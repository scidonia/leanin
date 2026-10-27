module

public meta import Lean
public meta import Lean.Parser.Term
public meta import LeanIn.Async.Attr
public import LeanIn.Runtime.Net
public import LeanIn.Runtime.Io
public import LeanIn.Runtime.VM


public section
/-!
# `async` — split-at-`await`, liveness-driven state machines, with control flow

`async name (c : Conn) (x : T) … := do …` compiles a connection-loop body into a per-function state
machine. The body is lowered **recursively**: pure code is inlined into the current state's step, each `await`
suspends the current state, and `if`/`match`/`while`/`recurse` become transitions between states. A **liveness
analysis** decides which variables each state carries as fields (those bound before and used after a
suspension). The first parameter `(c : Conn)` is the connection — a constant step parameter; **every further
parameter is a threaded field**: state 0 carries it, and `recurse` passes its current value back to state 0, so
a value the body never rebinds (a config, a handler, a clock) keeps its value across iterations, and one the
body rebinds (a protocol machine) advances — there is no split to get silently wrong.

Grammar:
- `let x := await (e)` / `await (e)` — a suspension.
- `let x := e` / `let x : T := e` — pure code, inlined (an ascription is what pins a state field's type;
  destructuring `let (a, b) := e` is not supported — bind components separately).
- a bare `e` — an action, sequenced with `>>=` exactly as `do` would (a term-level `let _ :=` would bind the
  action as a value and never run it).
- `if c then A else B` (the `else` is optional), `match s with …` — control flow; each branch is a nested
  body. A control-flow item in the middle of a sequence hoists the rest into a *shared* continuation state, so
  converging paths are compiled once.
- `while c do B` (desugared through the same transitions), `for x in xs do B`, `break`, `continue`.
- `recurse` — jump back to state 0 (must end a path). A close ends a path too; only pure statements may
  follow it, and they run after the socket goes (a completion signal is the use). `halt` ends a path as a
  return — the machine stops; a result-bearing machine delivers its `Completion.done` (or `fail` for a
  `throw`) and then halts.

Effects this cut resumes: `Io.recvRaw` (the byte payload continues on `.ok (some …)`; an end of stream or a
failure closes), `Io.recvTimeoutRaw` (the full race outcome is delivered: `none` stalled, `some (.ok …)` read,
`some (.error …)` failed), `Io.sendAllRaw`/`Io.sendRaw` (the `Except` is delivered to a bound result; an
unbound result discards it and the continuation still runs), `Io.closeRaw`, `VM.runAsync` (a sub-computation's result is delivered to the
bind), and **machine calls**: any `*.run` application suspends on the callee, whose `run` must declare its
completion last — a `Completion` the callee invokes with its result or failure; the generator fills that
slot with the caller's continuation, so a machine awaiting a machine is a raw resume and **no cell**, exactly
as `LeanIn.Http.Server.drive`'s `onClose` works. Field types are inferred without a general elaboration pass: a
threaded parameter keeps its signature
type, a `recvRaw`-bound variable is `ByteArray`, a `recvTimeoutRaw`-bound one is
`Option (Except IO.Error (Option ByteArray))`, a `sendRaw`/`sendAllRaw`-bound one is `Except IO.Error Unit`,
an ascribed binding keeps its type, and any other pure-bound field is read off its use —
`sendAllRaw`/`sendRaw` argument ⇒ `Array ByteArray`, `if`-condition ⇒ `Bool`, argument of a parameter's
arrow ⇒ its domain — and anything else is a **compile error naming the field** and its remedy, never a silent
`Unit` placeholder.
-/

namespace LeanIn.Async

/-- The two terminal channels of a compiled machine: a successful result and an ordinary failure. The
callback syntax exposes this continuation directly; `async def` hides it behind `Task.EAsync`. -/
structure Completion (α : Type) where
  done : α → IO Unit
  fail : IO.Error → IO Unit

open Lean Lean.Macro Lean.Parser.Term

/-- A parsed do-item: a node in the body's tree. `contStmt` is internal — a hoisted continuation marker. -/
private inductive Item where
  | pureBind (pat : Syntax) (ty? : Option Term) (term : Syntax)  -- `let <pat> := e` / `let <pat> : T := e`
  | pureStmt (term : Syntax)                     -- a bare `e`
  | await (bound? : Option Name) (ty? : Option Term) (term : Syntax) -- `let x := await e` / `let x : T := await e` / `await e`
  | if_ (cond : Syntax) (then_ else_ : List Item)
  | match_ (scrut : Syntax) (arms : List (Syntax × List Item))
  | while_ (cond : Syntax) (body : List Item)    -- `while c do body`
  | for_ (x : Ident) (xs : Syntax) (body : List Item)  -- `for x in xs do body`
  | break_                                       -- `break` (innermost `while`)
  | continue_                                    -- `continue` (innermost `while`)
  | recurse
  | halt                                         -- `halt` (the machine returns, must end a path)
  | return_ (value : Syntax)                     -- `return e` in a result-bearing declaration
  | throw_ (error : Syntax)                      -- `throw e`, delivered as `.error` in a result-bearing declaration
  | goto (idx : Nat) (args : List Name)          -- internal: jump to a specific state
  | contStmt (term : Term)                       -- internal: a hoisted continuation
  deriving Inhabited

/-- The name a declaration written as `n` was declared under: `n` itself, or — in a module, outside a
`public section` — its private form. -/
private meta def declaredName (env : Environment) (n : Name) : Name :=
  if env.contains n then n else mkPrivateName env n

/-- Recursively unwrap `doSeqIndent`/`doSeq`/`doSeqItem`/`doNested`/`null` down to the doElems. -/
private meta partial def doElemsOf (s : Syntax) : List Syntax :=
  match s.getKind with
  | `Lean.Parser.Term.doSeqIndent => s.getArgs.toList.flatMap doElemsOf
  | `Lean.Parser.Term.doSeq => s.getArgs.toList.flatMap doElemsOf
  | `Lean.Parser.Term.doSeqItem => s.getArgs.toList.flatMap doElemsOf
  | `Lean.Parser.Term.doNested => s.getArgs.toList.flatMap doElemsOf
  | `null => s.getArgs.toList.flatMap doElemsOf
  | _ => if s.isAtom then [] else [s]

/-- Collect the `matchAlt` nodes from a `matchAlts` node. -/
private meta partial def matchAltNodesOf (s : Syntax) : List Syntax :=
  if s.isOfKind `Lean.Parser.Term.matchAlt then [s]
  else
    match s with
    | .node _ _ args => args.toList.flatMap matchAltNodesOf
    | _ => []

mutual
private meta partial def parseItems (stx : Syntax) : MacroM (List Item) :=
  (doElemsOf stx).mapM parseItem

/-- Parse one do-item, recursing into `if` branches. -/
private meta partial def parseItem (d : Syntax) : MacroM Item := do
  match d with
  | `(doElem| let $x:ident : $ty:term := await $e) => return .await (some x.getId) (some ⟨ty⟩) e
  | `(doElem| let $x:ident := await $e) => return .await (some x.getId) none e
  | `(doElem| await $e) => return .await none none e
  | `(doElem| let $x:ident : $ty:term := $e) => return .pureBind x (some ⟨ty⟩) e
  | `(doElem| let $x:ident := $e) => return .pureBind x none e
  | `(doElem| let $p:term := $e) => return .pureBind p none e   -- destructuring `let (a, b) := e`
  | `(doElem| if $c:term then $t:doSeq else $e:doSeq) =>
    return .if_ c (← parseItems t) (← parseItems e)
  | `(doElem| if $c:term then $t:doSeq) =>
    return .if_ c (← parseItems t) []
  | `(doElem| match $s:term with $alts:matchAlts) =>
    -- Keep each `matchAlt` node whole; its body (arg 3) is parsed into items, its pattern (arg 1) is reused verbatim.
    let arms ← (matchAltNodesOf alts.raw).mapM (fun nd => do pure (nd, ← parseItems (nd.getArg 3)))
    return .match_ s arms
  | `(doElem| while $c:term do $b:doSeq) =>
    return .while_ c (← parseItems b)
  | `(doElem| for $x:ident in $xs:term do $b:doSeq) =>
    return .for_ x xs (← parseItems b)
  | `(doElem| break) => return .break_
  | `(doElem| continue) => return .continue_
  | `(doElem| recurse) => return .recurse
  | `(doElem| halt) => return .halt
  | `(doElem| return $e:term) => return .return_ e
  | `(doElem| throw $e:term) => return .throw_ e
  | `(doElem| $e:term) => return .pureStmt e
  | _ => Macro.throwError s!"async: unsupported do-item: {d}"
end

/-- The names used anywhere in a term (free variables a state might need). Dot-notation like `m.feed` is a
single compound identifier, so we collect each identifier's **root** as well as its full form — the root is the
local variable a state must carry, the full form never matches one. -/
private meta partial def usedNames (stx : Syntax) (acc : List Name := []) : List Name :=
  match stx with
  | .ident _ _ n _ => n :: n.getRoot :: acc
  -- A receiver-less dot head (`.ok`, `.error`, `.2`) is a constructor or projection, never a variable a
  -- state could carry — skip the node whole. (A dotted name like `m.feed` is a plain compound ident and
  -- still carries its root `m`.)
  | .node _ `Lean.Parser.Term.dotIdent _ => acc
  | .node _ _ args => args.foldl (fun a s => usedNames s a) acc
  | _ => acc

/-- The names bound by a pattern (for scope and liveness). Pattern semantics, from the syntax alone: an
identifier **applied to sub-patterns** is a constructor head, never a binding (`some (.ok …)`, `.ok …`), so
the head of an application is skipped and only its arguments are searched; a bare identifier may be a variable
or a nullary constructor — the syntax cannot tell those apart (`none` and `true` resolve only against the
expected type), so they are taken as bindings, which is inert unless the same name is also used as a bare term
after a suspension, where the field-type inference then fails loudly with the name. A preresolved identifier
is a constructor and is skipped as well, where the caller's syntax carries resolution. -/
private meta partial def patBoundNames (stx : Syntax) (acc : List Name := []) : List Name :=
  match stx with
  | .ident _ _ n pre => if n.isAnonymous || n == `_ || !pre.isEmpty then acc else n :: acc
  -- The head of an application is the constructor (`some x`, `.ok x`); only the arguments bind.
  | .node _ `Lean.Parser.Term.app args =>
    (args[1:].foldl (fun a s => patBoundNames s a) acc)
  -- A receiver-less dot head (`.ok`, `.none`) is a constructor wherever it appears, bare or applied.
  | .node _ `Lean.Parser.Term.dotIdent _ => acc
  | .node _ _ args => args.foldl (fun a s => patBoundNames s a) acc
  | _ => acc

/-- All names used in a list of items (for liveness). -/
private meta partial def usedInItems (items : List Item) : List Name :=
  items.flatMap go
where
  go : Item → List Name
  | .pureBind _ _ e => usedNames e
  | .pureStmt e => usedNames e
  | .await _ _ e => usedNames e
  | .if_ c t e => usedNames c ++ usedInItems t ++ usedInItems e
  | .match_ s arms => usedNames s ++ arms.flatMap (fun (_, b) => usedInItems b)
  | .while_ c b => usedNames c ++ usedInItems b
  | .for_ _ xs b => usedNames xs ++ usedInItems b
  | .break_ => []
  | .continue_ => []
  | .recurse => []
  | .halt => []
  | .return_ e => usedNames e
  | .throw_ e => usedNames e
  | .goto _ args => args
  -- A hoisted continuation is a jump term: the fields it passes are used exactly here.
  | .contStmt t => usedNames t

/-- Whether a list of items suspends anywhere (decides inline-vs-new-state for a continuation). -/
private meta partial def hasAwait (items : List Item) : Bool :=
  items.any fun
    | .await .. => true
    | .if_ _ t e => hasAwait t || hasAwait e
    | .match_ _ arms => arms.any (fun (_, b) => hasAwait b)
    | .while_ _ b => hasAwait b
    | .for_ _ _ b => hasAwait b
    | _ => false

/-- A variable's binding, for field-type inference. -/
private inductive Bind where
  | conn                          -- the connection (a step parameter, never a field)
  | threaded (ty : Term)          -- a threaded parameter (its signature type)
  | recvRes                       -- `recvRaw` result ⇒ `ByteArray`
  | recvTimeoutRes                -- `recvTimeoutRaw` result ⇒ `Option (Except IO.Error (Option ByteArray))`
  | sendRes                       -- `sendRaw`/`sendAllRaw` result ⇒ `Except IO.Error Unit`
  | typed (ty : Term)             -- a pure binding with an ascription ⇒ its type
  | pureB                         -- pure-bound ⇒ inferred from use

/-- A generated state: its index, its (typed) fields, and its body. -/
private structure GenState where
  idx : Nat
  fields : List (Name × Term)
  body : Term

/-- The innermost loop's jump targets, for `break`/`continue`: the head state (with the fields to pass back
into it) and the exit state (with its fields). -/
private structure LoopCtx where
  head : Nat
  headFields : List Name
  exit : Nat
  exitFields : List Name

private structure Ctx where
  name : Name
  conn : Name
  done : Option Name := none       -- the generated completion parameter, when the declaration has a result
  threaded : List Name          -- the threaded field names (state 0's fields: every parameter)
  paramTys : List (Name × Term) -- every parameter with its signature type (for use-inference)
  env : Lean.Environment        -- the environment at elaboration (machine-runner checks: `.St` lookup)
  ns : Name                     -- the current namespace (relative machine names resolve against it)
  loops : List LoopCtx := []    -- the enclosing `while` loops, innermost first
/-- The leading parameter count of a `run`'s type, and whether its last parameter is a function. -/
private meta partial def piShape (e : Lean.Expr) : Nat × Bool :=
  go e 0 where
  go : Lean.Expr → Nat → Nat × Bool
    | .forallE _ t b _, n =>
      if b.isForall then go b (n + 1) else (n + 1, t.isArrow || t.isForall)
    | _, n => (n, false)

/-- The type of the last parameter of a function type, if there is one. -/
private meta partial def lastParamType : Lean.Expr → Option Lean.Expr
  | .forallE _ t b _ => if b.isForall then lastParamType b else some t
  | _ => none

/-- Whether a type is `LeanIn.Async.Completion _`. -/
private meta def isCompletionType (t : Lean.Expr) : Bool :=
  match t.getAppFn.constName? with
  | some n => n == ``LeanIn.Async.Completion
  | none => false

/-- The effect an `await` runs, classified so the generator knows its resume shape and result type. -/
private inductive Eff where
  | recv (conn : Term) (size : Option Term)  -- `Io.recvRaw c [sz]` → `some` ByteArray continues / `none` closes
  | stallRead (conn : Term) (deadline : Term) (size : Term)  -- `Io.recvStallRaw c d sz` → the same race, swept
  | recvTimeout (conn : Term) (sched : Term) (deadline : Term) (size : Term)  -- `Io.recvTimeoutRaw c sched d sz` → `Option (Option ByteArray)`
  | sleep (sched : Term) (deadline : Term)  -- `Io.sleepRaw sched d` → `Unit`
  | runVM (m : Term)            -- `VM.runAsync m` → the machine's result (spawn + await a sub-computation)
  | runMachine (fn : Term) (args : List Term)  -- `Foo.run a b …` → the callee's callback payload
  | runMachineResult (fn : Term) (args : List Term)  -- a result machine's `run` → its `Completion` payload
  | spawn (push : Term) (fn : Term) (args : List Term)  -- `Foo.spawn push a …` → the machine's completion cell
  | join (h : Term)             -- `RawCell.await h` → the cell's value
  | newCell                     -- `RawCell.new` → a fresh completion cell
  | resolve (cell : Term) (v : Term)  -- `RawCell.resolve cell v` → first-wins resolution
  | select (h0 : Term) (h1 : Term)  -- `VM.selectRaw h0 h1` → the winning index and value
  | accept (l : Term) (push : Term)  -- `Io.acceptRaw l push` → the accepted connection (or an error)
  | sendAll (conn : Term) (data : Term)
  | send (conn : Term) (data : Term)
  | close (conn : Term)
  | unknown

/-- Strip a `Term.paren` wrapper: `(e)` becomes `e`. -/
private meta partial def unparen (s : Syntax) : Syntax :=
  if s.getKind == `Lean.Parser.Term.paren && s.getArgs.size ≥ 2 then unparen s[1]! else s

private meta def classify (ctx : Ctx) (e : Syntax) : MacroM Eff :=
  match unparen e with
  | `(LeanIn.Runtime.Io.recvStallRaw $c $d $z) => pure (.stallRead ⟨c⟩ ⟨d⟩ ⟨z⟩)
  | `(LeanIn.Runtime.Io.recvTimeoutRaw $c $s $d $z) => pure (.recvTimeout ⟨c⟩ ⟨s⟩ ⟨d⟩ ⟨z⟩)
  | `(LeanIn.Runtime.Io.sleepRaw $s $d) => pure (.sleep ⟨s⟩ ⟨d⟩)
  | `(LeanIn.Runtime.VM.runAsync $m) => pure (.runVM ⟨m⟩)
  | `(LeanIn.Runtime.selectRaw $a $b) => pure (.select ⟨a⟩ ⟨b⟩)
  | `(LeanIn.Runtime.Io.acceptRaw $l $push) => pure (.accept ⟨l⟩ ⟨push⟩)
  | `(LeanIn.Runtime.RawCell.await $h) => pure (.join ⟨h⟩)
  | `(LeanIn.Runtime.RawCell.new) => pure .newCell
  | `(LeanIn.Runtime.RawCell.resolve $cell $v) => pure (.resolve ⟨cell⟩ ⟨v⟩)
  | `(LeanIn.Runtime.Io.recvRaw $c $z) => pure (.recv ⟨c⟩ (some ⟨z⟩))
  | `(LeanIn.Runtime.Io.recvRaw $c) => pure (.recv ⟨c⟩ none)
  | `(LeanIn.Runtime.Io.sendAllRaw $c $d) => pure (.sendAll ⟨c⟩ ⟨d⟩)
  | `(LeanIn.Runtime.Io.sendRaw $c $d) => pure (.send ⟨c⟩ ⟨d⟩)
  | `(LeanIn.Runtime.Io.closeRaw $c) => pure (.close ⟨c⟩)
  -- A machine call: any `*.run` application — but only a machine's: the name must resolve to a declaration
  -- beside a generated `.St`, its ordinary arguments must be complete (the continuation is the one
  -- parameter the generator fills, last), and that last parameter must be a function.
  | `($fn:ident $args*) =>
    if fn.getId.getString! == "run" then do
      let candidates := [ctx.ns ++ fn.getId, fn.getId]
      match (candidates.map (declaredName ctx.env)).find? ctx.env.contains with
      | none =>
        Macro.throwError s!"async: unknown machine run `{fn.getId}` — neither `{candidates[0]!}` nor `{candidates[1]!}` exists"
      | some resolved =>
        -- Provenance, not shape: the tag `async` itself marks every `run` it generates. A
        -- hand-written `Foo.run` beside any `Foo.St` is rejected; `VM.run` is rejected.
        unless LeanIn.Async.machineAttr.hasTag ctx.env resolved do
          Macro.throwError s!"async: `{resolved}` is not the `run` of a compiled machine (it is not tagged with `machineAttr`) — a machine call awaits the `run` of a machine compiled by `async`"
        let some info := ctx.env.find? resolved
          | Macro.throwError s!"async: internal: `{resolved}` exists and does not"
        let (pis, lastIsFn) := piShape info.type
        if lastIsFn then
          unless args.size + 1 == pis do
            Macro.throwError s!"async: the machine call `{resolved}` takes {pis - 1} ordinary arguments before its continuation, but {args.size} were supplied"
          pure (.runMachine fn args.toList)
        else
          match lastParamType info.type with
          | some t =>
            if isCompletionType t then
              unless args.size + 1 == pis do
                Macro.throwError s!"async: the machine call `{resolved}` takes {pis - 1} ordinary arguments before its completion, but {args.size} were supplied"
              pure (.runMachineResult fn args.toList)
            else
              Macro.throwError s!"async: the machine call `{resolved}` does not end in a continuation or completion parameter — a callable machine declares one last"
          | none => Macro.throwError s!"async: the machine call `{resolved}` has no parameters"
    else if fn.getId.getString! == "spawn" then do
      -- A spawned machine: the generator emits `Foo.spawn` beside every callable `Foo.run`, so the surface
      -- exists exactly where the sibling `run` is tagged. The first argument is the executor's push.
      let candidates := [ctx.ns ++ fn.getId, fn.getId]
      match (candidates.map (declaredName ctx.env)).find? ctx.env.contains with
      | none =>
        Macro.throwError s!"async: unknown spawn `{fn.getId}` — a machine's spawn is generated beside its tagged `run`, and nothing named either candidate exists"
      | some resolved =>
        -- Provenance only: the tag is written by the generator beside its own `run`, so a hand-written
        -- `Foo.spawn` is rejected even when a compiled `Foo.run` exists.
        unless LeanIn.Async.spawnAttr.hasTag ctx.env resolved do
          Macro.throwError s!"async: `{resolved}` is not the spawn of a compiled machine (it is not tagged with `spawnAttr`) — a spawn is generated by `async` beside the `run` it spawns"
        let some info := ctx.env.find? resolved
          | Macro.throwError s!"async: internal: `{resolved}` exists and does not"
        let (pis, _) := piShape info.type
        unless args.size == pis do
          Macro.throwError s!"async: the spawn `{resolved}` takes {pis} arguments (the push, the connection, then the machine's own), but {args.size} were supplied"
        pure (.spawn ⟨args[0]!⟩ ⟨fn⟩ (List.drop 1 args.toList))
    else pure .unknown
  | _ => pure .unknown


private abbrev CompileM := StateT (Nat × List GenState) MacroM

/-- Extend the scope with freshly bound names. A name already in scope (a shadowing pure bind) keeps its
existing binding — and its type; a genuinely new name is `.pureB` (its type inferred from use). -/
private meta def extendScope (scope : List (Name × Bind)) (names : List Name) : List (Name × Bind) :=
  names.foldl (fun sc x => if sc.any (fun (n, _) => n == x) then sc else sc ++ [(x, .pureB)]) scope

/-- As `extendScope`, but a genuinely new name takes binding `b` (an ascribed pure bind). -/
private meta def extendScopeB (scope : List (Name × Bind)) (names : List Name) (b : Bind) : List (Name × Bind) :=
  names.foldl (fun sc x => if sc.any (fun (n, _) => n == x) then sc else sc ++ [(x, b)]) scope

private meta def freshIdx : CompileM Nat := do
  let (n, ss) ← get
  set (n + 1, ss)
  pure n

private meta def addState (s : GenState) : CompileM Unit := do
  let (n, ss) ← get
  set (n, s :: ss)

/-- The *reference* name for state `i` (`name.St.s{i}`). -/
private meta def stIdent (name : Name) (i : Nat) : Ident :=
  mkIdent ((Name.mkStr (name ++ `St) s!"s{i}").eraseMacroScopes)

/-- The *declaration* name for state `i` (just `s{i}`). -/
private meta def stLocalName (i : Nat) : Ident :=
  mkIdent ((Name.mkSimple s!"s{i}").eraseMacroScopes)

/-- Whether a pure-bound variable is used as a `sendAllRaw`/`sendRaw` data argument in the items. -/
private meta partial def usesSendArg (ctx : Ctx) (f : Name) (items : List Item) : MacroM Bool :=
  items.anyM go
where
  go : Item → MacroM Bool := fun
  | .await _ _ e => do
    let eff ← classify ctx e
    pure (match eff with
     | .sendAll _ d | .send _ d => d.raw.isIdent && d.raw.getId == f
     | _ => false)
  | .if_ _ t e => do
    if (← usesSendArg ctx f t) then pure true else usesSendArg ctx f e
  | .match_ _ arms => arms.anyM (fun (_, b) => usesSendArg ctx f b)
  | .while_ _ b => usesSendArg ctx f b
  | .for_ _ _ b => usesSendArg ctx f b
  | _ => pure false

/-- Whether a pure-bound variable is used as an `if`-condition in the items. -/
private meta partial def usedAsCond (f : Name) (items : List Item) : Bool :=
  items.any go
where
  go : Item → Bool
  | .if_ c t e => (c.isIdent && c.getId == f) || usedAsCond f t || usedAsCond f e
  | .match_ _ arms => arms.any (fun (_, b) => usedAsCond f b)
  | .while_ _ b => usedAsCond f b
  | .for_ _ _ b => usedAsCond f b
  | _ => false

/-- Whether a syntax subtree contains a reference to `f`. Application arguments are nested syntax nodes in
Lean's parser, so a direct-identifier check misses `handler head`'s `head` operand. -/
private meta partial def containsName (f : Name) (s : Syntax) : Bool :=
  match s with
  | .ident _ _ n _ => n.eraseMacroScopes == f.eraseMacroScopes || n.getRoot.eraseMacroScopes == f.eraseMacroScopes
  | .node _ _ args => args.any (containsName f)
  | _ => false

/-- Whether a pure-bound variable appears inside an **array-literal** `sendAllRaw`/`sendRaw` argument
(`#[x]` ⇒ the element, a `ByteArray`). -/
private meta partial def usesSendElem (ctx : Ctx) (f : Name) (items : List Item) : MacroM Bool :=
  items.anyM go
where
  go : Item → MacroM Bool := fun
  | .await _ _ e => do
    let eff ← classify ctx e
    pure (match eff with
     | .sendAll _ d | .send _ d =>
       (match d.raw[0]? with
        | some a => a.isAtom && a.getAtomVal == "#[" && containsName f d.raw
        | none => false)
     | _ => false)
  | .if_ _ t e => do
    if (← usesSendElem ctx f t) then pure true else usesSendElem ctx f e
  | .match_ _ arms => arms.anyM (fun (_, b) => usesSendElem ctx f b)
  | .while_ _ b => usesSendElem ctx f b
  | .for_ _ _ b => usesSendElem ctx f b
  | _ => pure false

/-- A field's type when it is used as the argument of a parameter function: the function's domain. For
example `handler head` ⇒ `Request.Head`, the handler's argument type — a field whose only use is passing it to
a typed function, with no `sendAll`/`if` use to read its type off. -/
private meta partial def findFnArg (ctx : Ctx) (f : Name) (items : List Item) : Option Term :=
  items.foldl (fun acc it => acc.orElse (fun _ => goItem it)) none
where
  sameName (a b : Name) : Bool := a.eraseMacroScopes == b.eraseMacroScopes
  goItem : Item → Option Term
  | .pureBind _ _ e => goTerm e
  | .pureStmt e => goTerm e
  | .await _ _ e => goTerm e
  | .if_ c t e => (goTerm c).orElse (fun _ => findFnArg ctx f t |>.orElse (fun _ => findFnArg ctx f e))
  | .match_ s arms =>
    (goTerm s).orElse (fun _ => arms.foldl (fun a (_, b) => a.orElse (fun _ => findFnArg ctx f b)) none)
  | .while_ c b => (goTerm c).orElse (fun _ => findFnArg ctx f b)
  | .for_ _ xs b => (goTerm xs).orElse (fun _ => findFnArg ctx f b)
  | _ => none
  goTerm (s : Syntax) : Option Term :=
    match s with
    | .node _ _ args =>
      let direct :=
        if args.size ≥ 2 && args[0]!.isIdent then
          match ctx.paramTys.find? (fun p => sameName p.1 args[0]!.getId) with
          | some (_, ty) =>
            match unparen ty.raw with
            | .node _ kk a =>
              if kk == `Lean.Parser.Term.arrow && a.size ≥ 1 &&
                 args[1:].toList.any (containsName f) then some ⟨a[0]!⟩ else none
            | _ => none
          | none => none
        else none
      direct.orElse (fun _ => args.foldl (fun a x => a.orElse (fun _ => goTerm x)) none)
    | _ => none

/-- The type of one state field, from its binding and (for pure-bound) how the continuation uses it. -/
private meta def fieldTypeFor (ctx : Ctx) (f : Name) (b : Bind) (rest : List Item) : MacroM Term := do
  match b with
  | .threaded ty => pure ty
  | .recvRes => `($(mkIdent `ByteArray))
  | .recvTimeoutRes => `(Option (Except IO.Error (Option ByteArray)))
  | .sendRes => `(Except IO.Error Unit)
  | .typed ty => pure ty
  | .conn => Macro.throwError s!"async: the connection `{f}` cannot be a state field"
  | .pureB =>
    if (← usesSendArg ctx f rest) then `(Array ByteArray)
    else if (← usesSendElem ctx f rest) then `($(mkIdent `ByteArray))
    else if usedAsCond f rest then `($(mkIdent `Bool))
    else match findFnArg ctx f rest with
      | some ty => pure ty
      | none => Macro.throwError s!"async: cannot determine the type of state field `{f}` — bound \
        without an ascription and live across a suspension, and not used in a shape the compiler infers \
        (a `sendAllRaw`/`sendRaw` argument, an `if`-condition, or the argument of a parameter's arrow). \
        Ascribe it: `let {f} : T := …`"

/-- A jump `name.step c (name.St.s{idx} args…)`, passing the state's live fields `args`. -/
private meta def jumpTerm (ctx : Ctx) (idx : Nat) (args : List Name) : MacroM Term := do
  let step := mkIdent (ctx.name ++ `step)
  let cn := stIdent ctx.name idx
  let c := mkIdent ctx.conn
  let argTs := args.toArray.map (fun a => (mkIdent a : Term))
  if argTs.isEmpty then `($step $c $cn) else `($step $c ($cn $argTs*))

/-- The `recurse` jump: back to state 0 with the threaded parameters' current values. -/
private meta def recurseTerm (ctx : Ctx) : MacroM Term :=
  jumpTerm ctx 0 ctx.threaded

/-- The binding an effect's result variable gets. -/
private meta def resultBind (eff : Eff) : Bind :=
  match eff with
  | .recv .. => .recvRes
  | .recvTimeout .. => .recvTimeoutRes
  | .stallRead .. => .recvTimeoutRes
  | .sendAll .. | .send .. => .sendRes
  | .runMachine .. | .runMachineResult .. => .pureB
  | _ => .pureB

/-- The suspension for one effect, with continuation `cont`. A source ascription (`let x : T := await …`)
applies to the binder itself, so a mismatched ascription fails at elaboration whether the value is live into a
later state or not — the alternative is that a dead binding's ascription silently disappears. -/
private meta def suspendTerm (ctx : Ctx) (eff : Eff) (bnd : Option Name) (ty? : Option Term)
    (cont : Term) : MacroM Term := do
  -- A binder carrying the source ascription when there is one.
  let annot (bv : Name) : MacroM Term :=
    match ty? with
    | some t => `(fun ($(mkIdent bv) : $t) => $cont)
    | none => `(fun $(mkIdent bv) => $cont)
  match eff with
  | .recv conn size =>
    let bv := bnd.getD `bs
    -- Cleanup ownership is single on every failure path. A *completion* failure is closed by the loop
    -- (`readDone` and `opDone` close after the raw callback and raise if the shim refuses), and a *submission
    -- refusal* is closed by the primitive itself before it resumes — so the generated error arms do nothing;
    -- closing here too would submit a second close for one failure. The end-of-stream arm is the machine's
    -- own: nobody else closes a connection whose peer simply left, so it closes, and a refusal is raised
    -- (`closeAfterFailure`) because a refused cleanup leaves the connection open with a step that has ended.
    -- A pattern cannot carry the ascription, so it is checked in the branch body.
    let checked : MacroM Term :=
      match ty? with
      | some t => `(let _ : $t := $(mkIdent bv); $cont)
      | none => pure cont
    let body ← checked
    let read ← match size with
      | some z => `(LeanIn.Runtime.Io.recvRaw $conn $z)
      | none => `(LeanIn.Runtime.Io.recvRaw $conn)
    `($read (fun
        | .ok (some $(mkIdent bv)) => $body
        | .ok none => LeanIn.Runtime.Io.closeAfterFailure $conn
        | .error _ => pure ()))
  | .stallRead conn d z =>
    let bv := bnd.getD `r
    let k ← annot bv
    `(LeanIn.Runtime.Io.recvStallRaw $conn $d $z $k)
  | .recvTimeout conn sched d z =>
    let bv := bnd.getD `r
    let k ← annot bv
    `(LeanIn.Runtime.Io.recvTimeoutRaw $conn $sched $d $z $k)
  | .sleep sched d =>
    -- The resume takes no argument; a bound sleep result is `()`, bound in the continuation so a
    -- `let u := await (sleepRaw …)` has its name in scope (`u : Unit`; an ascription to another type is a
    -- loud elaboration mismatch on the binding itself).
    match bnd with
    | none => `(LeanIn.Runtime.Io.sleepRaw $sched $d ($cont))
    | some bv =>
      match ty? with
      | some t => `(LeanIn.Runtime.Io.sleepRaw $sched $d (let $(mkIdent bv) : $t := (); $cont))
      | none => `(LeanIn.Runtime.Io.sleepRaw $sched $d (let $(mkIdent bv) := (); $cont))
  | .runVM m =>
    let bv := bnd.getD `v
    let k ← annot bv
    `(LeanIn.Runtime.VM.runAsync $m $k)
  | .runMachine fn args =>
    let bv := bnd.getD `v
    let argTs := args.toArray
    let k ← annot bv
    `($fn $argTs* $k)
  | .runMachineResult fn args =>
    dbg_trace "async: result machine call lowered"
    let bv := bnd.getD `v
    let argTs := args.toArray
    let k ← annot bv
    let fail ← match ctx.done with
      | some c => `(fun e => ($(mkIdent c)).fail e)
      | none => `(fun e => throw e)
    `($fn $argTs* ({ done := $k, fail := $fail } : LeanIn.Async.Completion _))
  | .spawn push fn args =>
    -- A spawned machine: the spawner allocates the completion cell, pushes the machine's first step onto
    -- the executor through the app's own inject, and hands the cell back as the handle. Nothing suspends
    -- here — the handle is a value, and the join is the suspension.
    let argTs := args.toArray
    match bnd with
    | some bv =>
      let k ← annot bv
      `($fn $push $argTs* >>= $k)
    | none =>
      `($fn $push $argTs* >>= fun _ => $cont)
  | .join h =>
    let bv := bnd.getD `v
    let k ← annot bv
    `(LeanIn.Runtime.RawCell.await $h $k)
  | .newCell =>
    match bnd with
    | some bv =>
      let k ← annot bv
      `(LeanIn.Runtime.RawCell.new >>= $k)
    | none => `(LeanIn.Runtime.RawCell.new >>= fun _ => $cont)
  | .resolve cell v =>
    -- A bound resolution binds the `Unit` in the continuation, so a `let r := await (resolve …)` keeps its
    -- name (and its ascription) rather than silently dropping both.
    match bnd with
    | some bv => `(LeanIn.Runtime.RawCell.resolve $cell $v >>= $(← annot bv))
    | none => `(LeanIn.Runtime.RawCell.resolve $cell $v >>= fun _ => $cont)
  | .select h0 h1 =>
    let bv := bnd.getD `v
    let k ← annot bv
    `(LeanIn.Runtime.selectRaw $h0 $h1 $k)
  | .accept l push =>
    let bv := bnd.getD `c
    let k ← annot bv
    `(LeanIn.Runtime.Io.acceptRaw $l $push $k)
  -- A write's failure policy is the same whether its result is bound or discarded: the operation returns its
  -- `Except`, and an unbound result simply discards it. Binding the result is the only way to inspect the
  -- failure; it does not change whether the continuation runs. The receiver is the one the author named.
  | .sendAll conn d =>
    match bnd with
    | some bv =>
      let k ← annot bv
      `(LeanIn.Runtime.Io.sendAllRaw $conn $d $k)
    | none =>
      `(LeanIn.Runtime.Io.sendAllRaw $conn $d (fun _ => $cont))
  | .send conn d =>
    match bnd with
    | some bv =>
      let k ← annot bv
      `(LeanIn.Runtime.Io.sendRaw $conn $d $k)
    | none =>
      `(LeanIn.Runtime.Io.sendRaw $conn $d (fun _ => $cont))
  | _ => Macro.throwError "async: unsupported effect"

/-- Whether a path's last item is a terminal — `recurse`, `break`, `continue`, `halt`, or a close — so
appending a continuation after it (the code following an `if`/loop body) would be unreachable and must be
skipped. -/
private meta partial def endsTerminal (ctx : Ctx) (items : List Item) : MacroM Bool :=
  match items.getLast? with
  | some .recurse => pure true
  | some .break_ => pure true
  | some .continue_ => pure true
  | some .halt => pure true
  | some (.return_ _) => pure true
  | some (.throw_ _) => pure true
  | some (.await _ _ e) => do
    let eff ← classify ctx e
    pure (match eff with | .close _ => true | _ => false)
  -- A close may be followed by a pure tail, so the check looks past pure items for the terminal.
  | some (.pureStmt _) | some (.pureBind ..) => endsTerminal ctx items.dropLast
  | _ => pure false

/-- Rewrite `continue` items at a `for` body's own level to take the loop's increment first — a skipped
iteration owes the counter too, or the loop never advances. A `continue` inside a nested loop belongs to that
loop and is left alone (the recursion enters `if`/`match` but never `while`/`for`). -/
private meta partial def incContinues (i : Ident) (inc : Term) : List Item → List Item
  | [] => []
  | .continue_ :: rest => .pureBind i none inc :: .continue_ :: incContinues i inc rest
  | .if_ c t e :: rest => .if_ c (incContinues i inc t) (incContinues i inc e) :: incContinues i inc rest
  | .match_ s arms :: rest => .match_ s (arms.map (fun (nd, b) => (nd, incContinues i inc b))) :: incContinues i inc rest
  | item :: rest => item :: incContinues i inc rest

/-- The tail a close may be followed by: every statement runs after the socket goes, so nothing that
suspends is allowed. Pure statements and a completion (`return`/`throw`, or an `if` of them) are the uses. -/
private meta def closeTail (ctx : Ctx) : List Item → MacroM Term
  | [] => `(pure ())
  | [.return_ e] => do
    let some done := ctx.done
      | Macro.throwError "async: `return` after `closeRaw` needs a result-bearing declaration"
    `(($(mkIdent done)).done $(⟨e⟩) >>= fun _ => pure ())
  | [.throw_ e] => do
    match ctx.done with
    | some done => `(($(mkIdent done)).fail $(⟨e⟩) >>= fun _ => pure ())
    | none => `(throw $(⟨e⟩))
  | [.if_ c t e] => do
    let tt ← closeTail ctx t
    let ee ← closeTail ctx e
    `(if $(⟨c⟩) then $tt else $ee)
  | [.pureStmt s] => `($(⟨s⟩) >>= fun _ => pure ())
  | .pureStmt s :: rs => do
    let t ← closeTail ctx rs
    `($(⟨s⟩) >>= fun _ => $t)
  | .pureBind pat none s :: rs => do
    let t ← closeTail ctx rs
    `(let $(⟨pat⟩) := $(⟨s⟩); $t)
  | .pureBind pat (some ty) s :: rs => do
    let t ← closeTail ctx rs
    `(let $(⟨pat⟩) : $ty := $(⟨s⟩); $t)
  | _ => Macro.throwError "async: only pure statements or a completion may follow `closeRaw`"

mutual
/-- Compile a list of items into the body Term of a state (or an inline continuation). Generates any
continuation states as a side effect. `scope` is the in-scope variables with their bindings. -/
private meta partial def compileBody (ctx : Ctx) (items : List Item) (scope : List (Name × Bind)) : CompileM Term := do
  match items with
  | [] => Macro.throwError "async: a path does not end in `recurse`, a close, or `halt`"
  | .halt :: rest => do
    unless rest.isEmpty do Macro.throwError "async: `halt` must end a path"
    `(pure ())
  | .return_ e :: rest => do
    unless rest.isEmpty do Macro.throwError "async: `return` must end a path"
    let some done := ctx.done
      | Macro.throwError "async: `return` needs a result-bearing declaration (`async def … : T`)"
    `(($(mkIdent done)).done $(⟨e⟩) >>= fun _ => pure ())
  | .throw_ e :: rest => do
    unless rest.isEmpty do Macro.throwError "async: `throw` must end a path"
    match ctx.done with
    | some done => `(($(mkIdent done)).fail $(⟨e⟩) >>= fun _ => pure ())
    | none => `(throw $(⟨e⟩))
  | .contStmt t :: rest => do
    unless rest.isEmpty do Macro.throwError "async: internal continuation marker must end a path"
    pure t
  | .recurse :: rest => do
    unless rest.isEmpty do Macro.throwError "async: `recurse` must end a path"
    recurseTerm ctx
  | .pureBind pat ty? e :: rest => do
    unless pat.isIdent do
      Macro.throwError "async: destructuring `let` is not supported yet — bind components separately (e.g. `let out := t.2.1`)"
    let b := match ty? with | some t => Bind.typed t | none => Bind.pureB
    let inner ← compileBody ctx rest (extendScopeB scope (patBoundNames pat) b)
    match ty? with
    | some t => `(let $(⟨pat⟩) : $t := $(⟨e⟩); $inner)
    | none => `(let $(⟨pat⟩) := $(⟨e⟩); $inner)
  | .pureStmt e :: rest => do
    -- A bare statement is an action to perform, as `do` would sequence it — a term-level `let _ :=` would
    -- bind the action as a value and silently never run it.
    let inner ← compileBody ctx rest scope
    `($(⟨e⟩) >>= fun _ => $inner)
  | .await bnd ty? e :: rest => do
    match (← classify ctx e) with
    | .close conn => do
      let tail ← closeTail ctx rest
      match bnd, ty? with
      | some bv, some t =>
        `(LeanIn.Runtime.Io.closeRaw $conn >>= fun ($(mkIdent bv) : $t) => $tail)
      | some bv, none =>
        `(LeanIn.Runtime.Io.closeRaw $conn >>= fun $(mkIdent bv) => $tail)
      -- An unbound close has no outcome channel, so a refusal is loud instead of silently unclosed.
      | none, _ =>
        `(LeanIn.Runtime.Io.closeRaw $conn >>= fun accepted =>
          if accepted then $tail
          else throw (IO.userError "async: the loop refused the connection's close submission"))
    | .unknown => Macro.throwError "async: unsupported effect in await"
    | eff => do
      let scope' := scope ++ bnd.toList.map (fun n =>
        (n, match ty? with | some t => .typed t | none => resultBind eff))
      let cont ← genCont ctx rest scope'
      suspendTerm ctx eff bnd ty? cont
  | .if_ c t e :: rest => do
    let cont? ← hoistCont ctx rest scope
    let suffix := cont?.toList
    let thenT ← compileBody ctx (if (← endsTerminal ctx t) then t else t ++ suffix) scope
    let elseT ← compileBody ctx (if (← endsTerminal ctx e) then e else e ++ suffix) scope
    `(if $(⟨c⟩) then $thenT else $elseT)
  | .match_ s arms :: rest => do
    let cont? ← hoistCont ctx rest scope
    let suffix := cont?.toList
    let armTerms ← arms.toArray.mapM (fun (nd, body) => do
      let armScope := extendScope scope (patBoundNames (nd.getArg 1))
      let t ← compileBody ctx (if (← endsTerminal ctx body) then body else body ++ suffix) armScope
      -- Rebuild the alternative as a term-level `matchAlt`, reusing the pattern (arg 1) verbatim and
      -- replacing only the body (arg 3) with the compiled continuation (a term, where the do-body was).
      match nd with
      | .node info _ args =>
        if args.size ≥ 4 then
          let newAlt : Syntax := .node info `Lean.Parser.Term.matchAlt (args.set! 3 t.raw)
          pure (⟨newAlt⟩ : TSyntax `Lean.Parser.Term.matchAlt)
        else Macro.throwError "async: malformed match alternative"
      | _ => Macro.throwError "async: malformed match alternative")
    let scrut : Term := ⟨s⟩
    `(match $scrut:term with $armTerms:matchAlt*)
  | .while_ c body :: rest => do
    -- L is the loop head; R is the code after the loop, which is also `break`'s target. L's body is
    -- `if c then (body; goto L) else goto R`, so a false condition falls through to R and a `break` jumps there.
    let lIdx ← freshIdx
    let rIdx ← freshIdx
    let all : List Item := .while_ c body :: rest
    let used := (usedInItems all).map (·.eraseMacroScopes)
    let loopScope := scope.filter (fun (n, _) => ctx.threaded.contains n || used.contains n.eraseMacroScopes)
    let loopNames := loopScope.map (·.1)
    let loopFields ← loopScope.mapM (fun (n, b) => do pure (n, ← fieldTypeFor ctx n b all))
    let restUsed := (usedInItems rest).map (·.eraseMacroScopes)
    let restScope := scope.filter (fun (n, _) => ctx.threaded.contains n || restUsed.contains n.eraseMacroScopes)
    let restNames := restScope.map (·.1)
    let restFields ← restScope.mapM (fun (n, b) => do pure (n, ← fieldTypeFor ctx n b rest))
    let restBody ← compileBody ctx rest restScope
    addState { idx := rIdx, fields := restFields, body := restBody }
    let ctx' := { ctx with
      loops := { head := lIdx, headFields := loopNames, exit := rIdx, exitFields := restNames } :: ctx.loops }
    let thenT ← compileBody ctx' (if (← endsTerminal ctx body) then body else body ++ [.goto lIdx loopNames]) loopScope
    let elseT ← jumpTerm ctx rIdx restNames
    addState { idx := lIdx, fields := loopFields, body := ← `(if $(⟨c⟩) then $thenT else $elseT) }
    jumpTerm ctx lIdx loopNames
  | .for_ x xs body :: rest => do
    -- Desugar to a counted loop: `let i := 0; let n := xs.size; while i < n do { let x := xs[i]!; body; i := i+1 }`.
    let i := mkIdent `__for_i
    let n := mkIdent `__for_n
    let natT : Term := ⟨mkIdent `Nat⟩
    let elem ← `(($(⟨xs⟩))[$i]!)
    -- A `continue` at this body's own level still owes the increment, so it is rewritten to take it; a
    -- terminal body (`halt`, `break`, a close) takes no increment after it at all.
    let incT ← `($i + 1)
    let body := incContinues i incT body
    let update ← if (← endsTerminal ctx body) then pure [] else pure [.pureBind i none incT]
    let inner : List Item :=
      [.pureBind x none elem] ++ body ++ update
    let whileItem := .while_ (← `($i < $n)) inner
    let setup : List Item :=
      [ .pureBind i (some natT) (← `(0)),
        .pureBind n (some natT) (← `(($(⟨xs⟩)).size)) ]
    compileBody ctx (setup ++ [whileItem] ++ rest) scope
  | .break_ :: rest => do
    unless rest.isEmpty do Macro.throwError "async: `break` must end a path"
    match ctx.loops with
    | l :: _ => jumpTerm ctx l.exit l.exitFields
    | [] => Macro.throwError "async: `break` used outside a `while`"
  | .continue_ :: rest => do
    unless rest.isEmpty do Macro.throwError "async: `continue` must end a path"
    match ctx.loops with
    | l :: _ => jumpTerm ctx l.head l.headFields
    | [] => Macro.throwError "async: `continue` used outside a `while`"
  | .goto idx args :: rest => do
    unless rest.isEmpty do Macro.throwError "async: an internal `goto` must end a path"
    jumpTerm ctx idx args

/-- The continuation after an `await`: inline pures+`recurse`/a hoisted marker; otherwise a new state. -/
private meta partial def genCont (ctx : Ctx) (rest : List Item) (scope : List (Name × Bind)) : CompileM Term := do
  match rest with
  | [] => Macro.throwError "async: an `await` has no continuation"
  | [.contStmt t] => pure t
  | _ =>
    if hasAwait rest then
      let idx ← genState ctx rest scope
      jumpTerm ctx idx (liveNames ctx rest scope)
    else
      -- pures + `recurse` (or a lone terminal): inline them.
      compileBody ctx rest scope

/-- Hoist the items after a control-flow item into a shared continuation state (so converging paths compile
once). Returns a `.contStmt` marker naming it, or `none` when there is no rest. -/
private meta partial def hoistCont (ctx : Ctx) (rest : List Item) (scope : List (Name × Bind)) : CompileM (Option Item) := do
  match rest with
  | [] => pure none
  | _ =>
    if hasAwait rest then
      let idx ← genState ctx rest scope
      pure (some (.contStmt (← jumpTerm ctx idx (liveNames ctx rest scope))))
    else
      pure (some (.contStmt (← compileBody ctx rest scope)))

/-- Generate a new state for `rest` (a continuation that suspends), returning its index. The state's fields
are the in-scope variables used in `rest`. -/
private meta partial def genState (ctx : Ctx) (rest : List Item) (scope : List (Name × Bind)) : CompileM Nat := do
  let idx ← freshIdx
  let fieldTys ← liveNames ctx rest scope |>.mapM (fun f => do
    let b := scope.lookup f |>.getD .pureB
    pure (f, ← fieldTypeFor ctx f b rest))
  let body ← compileBody ctx rest (liveScope ctx rest scope)
  addState { idx := idx, fields := fieldTys, body := body }
  pure idx

/-- The in-scope variables used in `rest` (the live fields). Compared scope-free: the threaded parameter
declared in the signature and the same name used in the body can carry different macro scopes, which would
otherwise drop a genuinely live variable from a state's fields. -/
private meta partial def liveNames (ctx : Ctx) (rest : List Item) (scope : List (Name × Bind)) : List Name :=
  let used := (usedInItems rest).map (·.eraseMacroScopes)
  -- Threaded parameters are always live: a `recurse` from any state must be able to pass them all back to
  -- state 0, so every state carries them whether or not its own body uses them.
  scope.filter (fun (n, _) => ctx.threaded.contains n || used.contains n.eraseMacroScopes) |>.map (·.1)

/-- The scope restricted to the variables live into `rest`. -/
private meta partial def liveScope (ctx : Ctx) (rest : List Item) (scope : List (Name × Bind)) : List (Name × Bind) :=
  let live := liveNames ctx rest scope
  scope.filter (fun (n, _) => live.contains n)
end

/-- `async def name (c : C) (x : T) … : R := do …` — a result-bearing machine. The generated public
`name` returns `Task.EAsync IO.Error R`; its internal runner keeps the explicit completion parameter, and
`return e` delivers `.ok e`. -/
syntax (docComment)? "async " "def " ident " (" ident " : " term ")" bracketedBinder* " : " term " := " doSeq : command

elab_rules : command
  | `($[$doc?:docComment]? async def $n:ident ( $c:ident : $cty:term ) $params:bracketedBinder* : $res:term := $body:doSeq) => do
  let threadedInfo ← params.toList.mapM fun p =>
    match p.raw with
    | `(bracketedBinder| ( $x:ident : $ty:term )) => pure (x.getId.eraseMacroScopes, (ty : Term))
    | _ => throwError "async: parameters must be `(x : T)`"
  let authored := threadedInfo.map (·.1)
  let doneName := `__asyncDone
  let doneTy ← `(LeanIn.Async.Completion $res)
  let threadedInfo := threadedInfo ++ [(doneName, doneTy)]
  let threaded := threadedInfo.map (·.1)
  let items ← Lean.Elab.liftMacroM (parseItems body)
  let ctx : Ctx := { name := n.getId, conn := c.getId, done := some doneName, threaded := threaded,
                     paramTys := threadedInfo, env := ← Lean.getEnv, ns := ← Lean.getCurrNamespace }
  let initScope : List (Name × Bind) := threadedInfo.map (fun (x, ty) => (x, .threaded ty))
  let s0fields := threadedInfo.map (fun (x, ty) => (x, ty))
  let compileAct : CompileM Unit := do
    let bodyT ← compileBody ctx items initScope
    addState { idx := 0, fields := s0fields, body := bodyT }
  let ((), (_n, statesRev)) ← Lean.Elab.liftMacroM (compileAct.run (1, []))
  let allStates := statesRev.reverse
  let ctors ← allStates.toArray.mapM (fun st => do
    let binders ← st.fields.toArray.mapM (fun (f, ty) => `(bracketedBinder| ($(mkIdent f) : $ty)))
    `(Lean.Parser.Command.ctor| | $(stLocalName st.idx):ident $binders*))
  let sn := mkIdent ((n.getId ++ `St).eraseMacroScopes)
  let stepn := mkIdent ((n.getId ++ `step).eraseMacroScopes)
  let runn := mkIdent ((n.getId ++ `run).eraseMacroScopes)
  let indCmd ← `(inductive $sn:ident where
    $[$ctors]*)
  Lean.Elab.Command.elabCommand indCmd
  let matchAlts ← allStates.toArray.mapM (fun st => do
    let pats := st.fields.toArray.map (fun (f, _) => (mkIdent f : Term))
    let cn := stLocalName st.idx
    let patTerm ← if pats.isEmpty then `(.$cn) else `(.$cn $pats*)
    `(matchAltExpr| | $patTerm => $(st.body)))
  let stepCmd ← `(partial def $stepn:ident ($(mkIdent c.getId) : $cty) : $sn → IO Unit :=
    fun st => match st with
      $matchAlts:matchAlt*)
  Lean.Elab.Command.elabCommand stepCmd
  let tfArgs := threaded.toArray.map (fun x => (mkIdent x : Term))
  let s0app ← if tfArgs.isEmpty then `($(stIdent n.getId 0)) else `($(stIdent n.getId 0) $tfArgs*)
  let doneId := mkIdent doneName
  let runCmd ← `(def $runn:ident ($(mkIdent c.getId) : $cty) $params* ($doneId : $doneTy) : IO Unit :=
    $stepn $(mkIdent c.getId) $s0app)
  Lean.Elab.Command.elabCommand runCmd
  -- The public entry: ordinary parameters, a result, and compiler-owned completion.
  let authoredArgs := authored.toArray.map (fun x => (mkIdent x : Term))
  let publicCmd ← `(def $n:ident ($(mkIdent c.getId) : $cty) $params* : LeanIn.Task.EAsync IO.Error $res :=
    ⟨fun k ctx => $runn $(mkIdent c.getId) $authoredArgs*
      ({ done := fun v => k (.ok v) ctx, fail := fun e => k (.error e) ctx } : LeanIn.Async.Completion $res)⟩)
  Lean.Elab.Command.elabCommand publicCmd
  if let some d := doc? then
    let declared := declaredName (← Lean.getEnv) (ctx.ns ++ n.getId)
    Lean.Elab.Command.liftTermElabM <| Lean.addDocString declared Syntax.missing d
  -- The spawner: the completion cell holds the machine's `Except`, and both channels resolve it.
  let spawnn := mkIdent ((n.getId ++ `spawn).eraseMacroScopes)
  let others := threadedInfo.dropLast
  let binders ← others.toArray.mapM (fun (x, t) => `(bracketedBinder| ($(mkIdent x) : $t)))
  let ids := others.toArray.map (fun (x, _) => (mkIdent x : Term))
  let pushId := mkIdent `push
  let cellName := mkIdent `cell
  let body ← `(do
    let $cellName ← LeanIn.Runtime.RawCell.new
    ($pushId (LeanIn.Task.Item.ofAction
      ($runn $(mkIdent c.getId) $ids*
        ({ done := fun v => LeanIn.Runtime.RawCell.resolve $cellName (.ok v),
           fail := fun e => LeanIn.Runtime.RawCell.resolve $cellName (.error e) } :
          LeanIn.Async.Completion $res))))
    pure $cellName)
  let spawnCmd ← `(def $spawnn:ident
    ($pushId : LeanIn.Task.Item → BaseIO Unit)
    ($(mkIdent c.getId) : $cty) $binders* :
      IO (LeanIn.Runtime.RawCell (Except IO.Error $res)) := $body)
  Lean.Elab.Command.elabCommand spawnCmd
  modifyEnv fun env =>
    LeanIn.Async.spawnAttr.ext.addEntry env (declaredName env (ctx.ns ++ (n.getId ++ `spawn)))
  modifyEnv fun env =>
    LeanIn.Async.machineAttr.ext.addEntry env (declaredName env (ctx.ns ++ (n.getId ++ `run)))

end LeanIn.Async

end
