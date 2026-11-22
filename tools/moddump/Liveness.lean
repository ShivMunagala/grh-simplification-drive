/-
liveness: which inputs does a proof never use?

Reads compiled modules (.olean) one at a time, in dependency order, and looks for three kinds of dead
weight in every statement and body:

  1. a leading argument of a theorem that neither the rest of its statement nor its proof mentions;
  2. wherever such a theorem is applied, the argument passed in that place;
  3. a local `have` or `let` whose name is not mentioned after it.

Each feeds the others: a hypothesis that is only ever passed on in a dead place is dead itself, and so is
a `have` that is. So a theorem is analysed after everything it uses, and what is removed from its body is
taken into account when its own arguments are examined.

Input (stdin): one line per module, `<module name>\t<path to .olean>`, importers after what they import.
Output (stdout), tab separated:
  L  <id>  <kind>  <leading arguments>  <dead positions, comma separated>  <statement size>  <after>
     <body size>  <after>  <dead arguments removed>  <unused haves removed>  <uses with too few arguments>
     <statement deps after>  <extra body deps after>  <name>
        one line for every declaration in which something was found
  D  <id of the theorem>  <position>  <times an argument was removed there>  <nodes removed>  <name>
        at the end: how much is passed, over all uses, in each dead place
  X  <module>  <error>
  E  <module>
`id` and the dependency lists are 64-bit hashes of names, as in moddump. Sizes count term nodes as stored.

Nothing is changed and nothing is checked: this measures what a removal would save. The proof stays
valid only if the source is edited accordingly and compiled again.
-/
import Lean.Environment
import Lean.Util.FoldConsts
import Lean.Util.NumObjs

open Lean

namespace Liveness

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "ax"
  | .defnInfo _ => "def"
  | .thmInfo _ => "thm"
  | .opaqueInfo _ => "opq"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "ind"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

structure St where
  /-- theorem ↦ positions of its dead leading arguments. Kept over all modules, so it is keyed by the
  hash of the name: a name itself lives in its module's file, which is released after the module. -/
  dead : Std.HashMap UInt64 (Array Nat) := {}
  /-- (theorem, position) ↦ how often an argument was removed there, how many nodes, and the name -/
  passed : Std.HashMap (UInt64 × Nat) (Nat × Nat × String) := {}
  /-- per module: what a shared subterm became, by its address (terms of a module stay where they are
  until the module is released) -/
  memo : Std.HashMap USize Expr := {}
  /-- per module: declarations already analysed -/
  done : NameSet := {}
  /-- per declaration -/
  args : Nat := 0
  haves : Nat := 0
  short : Nat := 0

unsafe abbrev M := StateT St IO

/-- Stands where a dead argument was. -/
def gone : Expr := .const `_dead []

mutual

/-- The term without dead arguments and unused haves. Unchanged parts keep their identity. -/
unsafe def erase (e : Expr) : M Expr := do
  match e with
  | .bvar _ | .const .. | .sort _ | .lit _ | .fvar _ | .mvar _ => return e
  | _ =>
    if let some r := (← get).memo.get? (ptrAddrUnsafe e) then
      return r
    let r ← match e with
      | .app .. => eraseApp e
      | .lam _ t b _ => do
        let t' ← erase t
        let b' ← erase b
        pure (e.updateLambdaE! t' b')
      | .forallE _ t b _ => do
        let t' ← erase t
        let b' ← erase b
        pure (e.updateForallE! t' b')
      | .letE _ t v b nd => do
        let b' ← erase b
        if !b'.hasLooseBVar 0 then
          modify fun s => { s with haves := s.haves + 1 }
          pure (b'.lowerLooseBVars 1 1)
        else
          let t' ← erase t
          let v' ← erase v
          pure (e.updateLet! t' v' b' nd)
      | .mdata _ b => do
        let b' ← erase b
        pure (e.updateMData! b')
      | .proj _ _ b => do
        let b' ← erase b
        pure (e.updateProj! b')
      | _ => pure e
    modify fun s => { s with memo := s.memo.insert (ptrAddrUnsafe e) r }
    return r

unsafe def eraseArgs (as : Array Expr) (start : Nat) : M (Array Expr × Bool) := do
  let mut out : Array Expr := #[]
  let mut changed := false
  for i in [start:as.size] do
    let a := as[i]!
    let a' ← erase a
    if !ptrEq a a' then changed := true
    out := out.push a'
  return (out, changed)

unsafe def eraseApp (e : Expr) : M Expr := do
  let f := e.getAppFn
  let as := e.getAppArgs
  match f with
  | .const c _ =>
    -- `letFun α β v (fun x => b)`: an older way to store a `have`
    if c == `letFun && as.size ≥ 4 then
      if let .lam _ _ b _ := as[3]! then
        let b' ← erase b
        if !b'.hasLooseBVar 0 then
          modify fun s => { s with haves := s.haves + 1 }
          let (rest, _) ← eraseArgs as 4
          return mkAppN (b'.lowerLooseBVars 1 1) rest
    let dead := (← get).dead.getD c.hash #[]
    if dead.isEmpty then
      let (as', changed) ← eraseArgs as 0
      return if changed then mkAppN f as' else e
    else
      let mut as' : Array Expr := #[]
      let mut complete := true
      for p in dead do
        if p ≥ as.size then complete := false
      if !complete then
        modify fun s => { s with short := s.short + 1 }
      for i in [0:as.size] do
        let a := as[i]!
        if dead.contains i then
          let k ← a.numObjs
          modify fun s =>
            let (n, w, nm) := match s.passed.get? (c.hash, i) with
              | some x => x
              | none => (0, 0, String.mk (toString c).toList)      -- a copy that outlives the module's file
            { s with args := s.args + 1, passed := s.passed.insert (c.hash, i) (n + 1, w + k, nm) }
          as' := as'.push gone
        else
          as' := as'.push (← erase a)
      return mkAppN f as'
  | .lam _ t b _ =>
    -- `(fun x => b) a`: how a `have` made by a tactic is stored
    let b' ← erase b
    if as.size ≥ 1 && !b'.hasLooseBVar 0 then
      modify fun s => { s with haves := s.haves + 1 }
      let (rest, _) ← eraseArgs as 1
      return mkAppN (b'.lowerLooseBVars 1 1) rest
    else
      let t' ← erase t
      let f' := f.updateLambdaE! t' b'
      let (as', changed) ← eraseArgs as 0
      return if changed || !ptrEq f f' then mkAppN f' as' else e
  | _ =>
    let f' ← erase f
    let (as', changed) ← eraseArgs as 0
    return if changed || !ptrEq f f' then mkAppN f' as' else e

end

/-- Peel the leading arguments that statement and proof share, and rebuild both without the ones that
nothing after them mentions. Returns the new statement, the new proof, how many arguments were peeled
and the positions that went. -/
partial def dropDead (t v : Expr) (pos : Nat) : Expr × Expr × Nat × Array Nat :=
  match t, v.consumeMData with
  | .forallE n d tb bi, .lam n' d' vb bi' =>
    let (tb', vb', depth, dead) := dropDead tb vb (pos + 1)
    if !tb'.hasLooseBVar 0 && !vb'.hasLooseBVar 0 then
      (tb'.lowerLooseBVars 1 1, vb'.lowerLooseBVars 1 1, depth, dead.push pos)
    else
      (.forallE n d tb' bi, .lam n' d' vb' bi', depth, dead)
  | _, _ => (t, v, pos, #[])

def hashList (s : NameSet) (skip : NameSet := {}) : String :=
  let parts := s.foldl (init := (#[] : Array String)) fun acc n =>
    if skip.contains n || n == `_dead then acc else acc.push (toString n.hash)
  " ".intercalate parts.toList

unsafe def analyse (locals : Std.HashMap Name ConstantInfo) (out : IO.FS.Stream) (name : Name) : M Unit := do
  if (← get).done.contains name then
    return
  modify fun s => { s with done := s.done.insert name }
  let some ci := locals.get? name | return
  let used := ci.getUsedConstantsAsSet.foldl (init := (#[] : Array Name)) fun acc n => acc.push n
  for c in used do
    if locals.contains c then
      analyse locals out c
  let some v := ci.value? (allowOpaque := true) | return
  modify fun s => { s with args := 0, haves := 0, short := 0 }
  let t' ← erase ci.type
  let v' ← erase v
  let (t'', v'', depth, dead) :=
    match ci with
    | .thmInfo _ => dropDead t' v' 0
    | _ => (t', v', 0, #[])
  let s ← get
  if dead.isEmpty && s.args == 0 && s.haves == 0 then
    return
  let dead := dead.qsort (· < ·)
  if !dead.isEmpty then
    modify fun s => { s with dead := s.dead.insert name.hash dead }
  -- A compiled file stores identical subterms once. The rebuilt terms do not (lowering bound variables
  -- copies what it touches), so they are shared again before they are counted.
  let tb ← ci.type.numObjs
  let ta ← (ShareCommon.shareCommon' t'').numObjs
  let vb ← v.numObjs
  let va ← (ShareCommon.shareCommon' v'').numObjs
  let tdeps := t''.getUsedConstantsAsSet
  let vdeps := v''.getUsedConstantsAsSet
  let pos := ",".intercalate (dead.toList.map toString)
  out.putStrLn
    s!"L\t{name.hash}\t{kindOf ci}\t{depth}\t{pos}\t{tb}\t{ta}\t{vb}\t{va}\t{s.args}\t{s.haves}\t{s.short}\t{hashList tdeps}\t{hashList vdeps tdeps}\t{name}"

/-- Everything that touches the module's terms happens in here, so that nothing built from them is
still alive when the caller releases the module's file. -/
unsafe def processBody (mod : ModuleData) (out : IO.FS.Stream) : M Unit := do
  modify fun s => { s with memo := {}, done := {} }
  let mut locals : Std.HashMap Name ConstantInfo := {}
  for ci in mod.constants do
    locals := locals.insert ci.name ci
  for ci in mod.constants do
    analyse locals out ci.name
  modify fun s => { s with memo := {}, done := {} }

unsafe def processOne (modName : String) (path : System.FilePath) (out : IO.FS.Stream) : M Unit := do
  let (mod, region) ← readModuleData path
  processBody mod out
  out.putStrLn s!"E\t{modName}"
  region.free

unsafe def mainUnsafe (_args : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut st : St := {}
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    match ((line.splitOn "\n").headD "").splitOn "\t" with
    | [m, p] =>
      try
        let (_, st') ← (processOne m p stdout).run st
        st := st'
      catch e =>
        stdout.putStrLn s!"X\t{m}\t{e}"
        st := { st with memo := {}, done := {} }
    | _ => pure ()
  for ((c, i), (n, w, nm)) in st.passed.toList do
    stdout.putStrLn s!"D\t{c}\t{i}\t{n}\t{w}\t{nm}"
  stdout.flush
  return 0

end Liveness

def main (args : List String) : IO UInt32 := unsafe Liveness.mainUnsafe args
