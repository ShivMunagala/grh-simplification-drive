/-
GrhCompact: reprint a declaration that is written out with every argument explicit.

Some files of the archive hold machine-printed terms: every implicit argument and every instance is
spelled out, so a term of a few thousand nodes takes tens of thousands of tokens. Part of that is
needed (some instances cannot be found again automatically), most is not. The command

    #grh_compact "<text before the name>" <name> "<universe suffix>" "<output file>"
                 "<the statement as written>" "<the value as written>"

placed right after such a declaration looks for the applications that have to stay explicit. A term is
printed with Lean's ordinary printer (implicit arguments left out); if the text does not read back as
exactly the same term, its parts are treated the same way and the application at the top is printed
with all its arguments. Every reading-back is done at the place of the declaration, in the file's own
scope. The result is then checked as a whole: the new text is elaborated under a temporary name and
must give the same statement (binder names and kinds, universe parameters) and, for a definition, the
same value; a theorem's proof only has to be accepted. If the new statement or the new value fails
that check, the one as written is kept. One line of JSON is appended to the output file.
Nothing is added to the environment. tools/compact.py drives this.
-/
import Lean
open Lean Meta Elab Term Command

namespace GrhCompact

def baseOpts (o : Options) : Options :=
  let o := o.setBool `pp.proofs true
  let o := o.setBool `pp.deepTerms true
  let o := o.set `pp.maxSteps (2000000000 : Nat)
  -- types of `fun` and `let` variables are printed: reading back must not depend on guessing them
  (o.setBool `pp.funBinderTypes true).setBool `pp.letVarTypes true

def isAuxOf (decl : Name) (n : Name) : Bool :=
  match n with
  | .str p s => p == decl && s.startsWith "_proof_"
  | _ => false

/-- Put the values of the declaration's auxiliary proof lemmas back in place. -/
def inlineAux (decl : Name) (e : Expr) : CoreM Expr := do
  let env ← getEnv
  Core.transform e (pre := fun e => do
    if let .const n us := e.getAppFn then
      if isAuxOf decl n then
        if let some ci := env.find? n then
          if let some v := ci.value? (allowOpaque := true) then
            return .visit ((v.instantiateLevelParams ci.levelParams us).beta e.getAppArgs)
    return .continue)

/-- The form two terms are compared in: no annotations, binder names without hygiene suffixes. -/
def plain (e : Expr) : CoreM Expr :=
  Core.transform e
    (pre := fun e => match e with
      | .mdata _ b => return .visit b
      | _ => return .continue)
    (post := fun e => match e with
      | .lam n t b bi => return .done (.lam n.eraseMacroScopes t b bi)
      | .forallE n t b bi => return .done (.forallE n.eraseMacroScopes t b bi)
      | .letE n t v b nd => return .done (.letE n.eraseMacroScopes t v b nd)
      | _ => return .done e)

def normal (decl : Name) (e : Expr) : CoreM Expr := do
  plain (← inlineAux decl e)

/-- Where two terms first differ, for the notes. -/
partial def firstDiff (a b : Expr) : Option String :=
  if a.equal b then none else
  match a, b with
  | .app f x, .app g y => (firstDiff f g).orElse fun _ => firstDiff x y
  | .lam n t c bi, .lam m u d bj =>
    if n != m || bi != bj then some s!"binder {n} / {m}" else (firstDiff t u).orElse fun _ => firstDiff c d
  | .forallE n t c bi, .forallE m u d bj =>
    if n != m || bi != bj then some s!"binder {n} / {m}" else (firstDiff t u).orElse fun _ => firstDiff c d
  | .letE n t v c _, .letE m u w d _ =>
    if n != m then some s!"let {n} / {m}" else
      ((firstDiff t u).orElse fun _ => firstDiff v w).orElse fun _ => firstDiff c d
  | .proj _ i x, .proj _ j y => if i != j then some "projection index" else firstDiff x y
  | _, _ => some s!"{(toString a).take 160} / {(toString b).take 160}"

def roomy {α : Type} (x : CoreM α) : CoreM α :=
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 0, maxRecDepth := 100000 }) x

/-- One reading-back with its own, small budget. A part in ordinary form that reads back at all does so
quickly; one that does not often sends the search for instances off for as long as it is allowed, and
there are thousands of readings. A part that would have needed more simply stays explicit. The
declaration as a whole is read with the file's own limits at the end. -/
def budget {α : Type} (x : TermElabM α) : TermElabM α := do
  let now ← IO.getNumHeartbeats
  withTheReader Core.Context
    (fun c => { c with maxHeartbeats := 20000000, initHeartbeats := now, maxRecDepth := 100000 }) <|
    withOptions (fun o => o.set `synthInstance.maxHeartbeats (3000 : Nat)) x

/-- Progress trace (file to write to, tests done, milliseconds spent in tests), for finding slow spots. -/
initialize traceRef : IO.Ref (String × Nat × Nat) ← IO.mkRef ("", 0, 0)
initialize phaseRef : IO.Ref (Array (String × Nat)) ← IO.mkRef #[]

def phase (name : String) : IO Unit := do
  phaseRef.modify (·.push (name, ← IO.monoMsNow))

def explicitHere (e : Expr) : Expr :=
  .mdata (KVMap.empty.setBool `pp.explicit true) e

def show1 (e : Expr) : MetaM String := do
  let f ← withOptions baseOpts <| PrettyPrinter.ppExpr e
  return f.pretty 96

/-- Does the text printed for `shown` read back, in the current local context, as exactly `orig`? -/
def readsBack (shown orig : Expr) (maxLength : Nat := 0) : TermElabM Bool := do
  let saved ← saveState
  let t0 ← IO.monoMsNow
  let r ← tryCatchRuntimeEx
      (budget do
        phaseRef.set #[]
        phase "start"
        let ty ← inferType orig
        let s ← show1 shown
        phase s!"printed {s.length} chars"
        -- (a long text in ordinary form almost never reads back whole: its parts are tried first)
        if maxLength != 0 && s.length > maxLength then pure false else
        if s.contains '✝' || s.contains '⋯' then pure false else
        match Parser.runParserCategory (← getEnv) `term s with
        | .error _ => pure false
        | .ok stx =>
          phase "parsed"
          let e ← Term.withoutErrToSorry <| Term.elabTermEnsuringType stx (some ty)
          phase "elaborated"
          Term.synthesizeSyntheticMVarsNoPostponing
          phase "synthesized"
          let e ← instantiateMVars e
          if e.hasMVar then pure false else
          let a ← plain e
          let b ← plain orig
          phase "normalised"
          let r := a.equal b
          phase s!"compared {r}"
          pure r)
      (fun _ => pure false)
  saved.restore
  let dt := (← IO.monoMsNow) - t0
  let (file, n, ms) ← traceRef.get
  traceRef.set (file, n + 1, ms + dt)
  if file != "" && ((n + 1) % 100 == 0 || dt > 5000) then
    let h ← IO.FS.Handle.mk file .append
    let ph ← phaseRef.get
    let t00 := (ph[0]?.map (·.2)).getD 0
    h.putStrLn s!"{n + 1} tests, {ms + dt} ms in tests; last: {dt} ms, {if r then "ok" else "no"}; phases: {ph.map fun (nm, t) => s!"{nm} +{t - t00}"}"
  return r

structure St where
  /-- results for small terms: found by reading the whole term back -/
  small : Std.HashMap Expr Expr := {}
  /-- results for large terms: depend on `safe` -/
  big : Std.HashMap Expr Expr := {}
  sizes : Std.HashMap Expr Nat := {}
  /-- print every large application with all its arguments (the fallback) -/
  safe : Bool := false
  marks : Nat := 0

abbrev M := StateRefT St TermElabM

/-- Number of nodes of `e` written out as a tree (shared parts counted each time), cut off at a million. -/
partial def treeSize (e : Expr) : M Nat := do
  if let some n := (← get).sizes.get? e then
    return n
  let n ← match e with
    | .app f x => do pure ((← treeSize f) + (← treeSize x) + 1)
    | .lam _ t c _ => do pure ((← treeSize t) + (← treeSize c) + 1)
    | .forallE _ t c _ => do pure ((← treeSize t) + (← treeSize c) + 1)
    | .letE _ t v c _ => do pure ((← treeSize t) + (← treeSize v) + (← treeSize c) + 1)
    | .mdata _ c => do pure ((← treeSize c) + 1)
    | .proj _ _ c => do pure ((← treeSize c) + 1)
    | _ => pure 1
  let n := min n 1000000
  modify fun st => { st with sizes := st.sizes.insert e n }
  return n

def atomic (t : Expr) : Bool := t.isFVar || t.isConst || t.isSort || t.isLit

def substitute (subst : Array (Expr × Expr)) (t : Expr) : Expr :=
  if subst.isEmpty then t else t.replace fun u => (subst.find? (fun p => p.1 == u)).map (·.2)

partial def placeholderGo (args : Array Expr) (info : FunInfo) (i : Nat) (fn : Expr) (args' : Array Expr)
    (subst : Array (Expr × Expr)) : TermElabM Bool := do
  if h : i < args.size then
    let x := args[i]
    let explicit := match info.paramInfo[i]? with
      | some pi => pi.isExplicit
      | none => true
    if explicit && !atomic x then
      let ty := substitute subst (← inferType x)
      withLocalDeclD (Name.mkSimple s!"grhArg{i}") ty fun v =>
        placeholderGo args info (i + 1) fn (args'.push v) (subst.push (x, v))
    else
      placeholderGo args info (i + 1) fn (args'.push (substitute subst x)) subst
  else
    let e' := mkAppN fn args'
    readsBack e' e'

/-- The test for a large application: can it be written in ordinary form? Its explicit arguments are
replaced by variables of the same types, so that only the application itself and its implicit arguments
are read back, not everything below it. (Whether the implicit arguments are found again depends on the
types of the explicit ones, not on what they are.) The declaration as a whole is still checked at the
end; if that fails, the large applications are all printed in full instead. -/
def placeholderOK (e : Expr) : TermElabM Bool := do
  try
    let f := e.getAppFn
    let args := e.getAppArgs
    let info ← getFunInfoNArgs f args.size
    if atomic f then
      placeholderGo args info 0 f #[] #[]
    else
      withLocalDeclD `grhFn (← inferType f) fun g => placeholderGo args info 0 g #[] #[]
  catch _ => return false

/-- `e` with the applications marked that have to be printed with all their arguments. -/
partial def compact (e : Expr) : M Expr := do
  let isBig := (← treeSize e) > 1500
  let st ← get
  if let some r := (if isBig then st.big else st.small).get? e then
    return r
  let r ← match e with
    | .app .. => do
      let whole ← if isBig then pure false else readsBack e e
      if whole then pure e else
      let f := e.getAppFn
      let f' ← if atomic f || f.isBVar then pure f else compact f
      let args' ← e.getAppArgs.mapM compact
      let e1 := mkAppN f' args'
      let ok ← if isBig then (if (← get).safe then pure false else placeholderOK e) else readsBack e1 e
      if ok then pure e1 else
      modify fun st => { st with marks := st.marks + 1 }
      pure (explicitHere e1)
    | .lam n t b bi => do
      let t' ← compact t
      let b' ← withLocalDecl n bi t fun x => do
        return (← compact (b.instantiate1 x)).abstract #[x]
      pure (.lam n t' b' bi)
    | .forallE n t b bi => do
      let t' ← compact t
      let b' ← withLocalDecl n bi t fun x => do
        return (← compact (b.instantiate1 x)).abstract #[x]
      pure (.forallE n t' b' bi)
    | .letE n t v b nd => do
      let t' ← compact t
      let v' ← compact v
      let b' ← withLetDecl n t v fun x => do
        return (← compact (b.instantiate1 x)).abstract #[x]
      pure (.letE n t' v' b' nd)
    | .mdata d b => do pure (.mdata d (← compact b))
    | .proj sn i b => do pure (.proj sn i (← compact b))
    | _ => pure e
  if isBig then modify fun st => { st with big := st.big.insert e r }
  else modify fun st => { st with small := st.small.insert e r }
  return r

def bad (s : String) : Bool := s.contains '✝' || s.contains '⋯'

/-- A text both ways: large applications tested locally, and (the fallback) all printed in full. -/
def both (x : M String) : M (String × String) := do
  let fast ← x
  modify fun st => { st with safe := true, big := {} }
  let safe ← x
  modify fun st => { st with safe := false, big := {} }
  return (fast, safe)

def binderText (n : Name) (bi : BinderInfo) (tS : String) (named : Bool) : String :=
  let nm := toString n
  match bi with
  | .default => "(" ++ nm ++ " : " ++ tS ++ ")"
  | .implicit => "{" ++ nm ++ " : " ++ tS ++ "}"
  | .strictImplicit => "⦃" ++ nm ++ " : " ++ tS ++ "⦄"
  | .instImplicit => if named then "[" ++ nm ++ " : " ++ tS ++ "]" else "[" ++ tS ++ "]"

def isNamed (n : Name) : Bool := !n.hasMacroScopes && n.isAtomic && !n.isAnonymous

/-- A value with its leading `fun` binders written by hand, so that instance binders keep their names
(the printer writes `fun [C] ↦ …` when the body does not mention the instance by name). -/
partial def lams (val : Expr) (acc : Array String) : M (String × String) := do
  let finish : M (String × String) := do
    let (b1, b2) ← both (do show1 (← compact val))
    let wrap (body : String) : String :=
      if acc.isEmpty then body else
        "fun " ++ " ".intercalate acc.toList ++ " ↦\n" ++ "\n".intercalate ((body.splitOn "\n").map ("  " ++ ·))
    return (wrap b1, wrap b2)
  match val with
  | .lam n t b bi =>
    let named := isNamed n
    if !(named || bi == .instImplicit) then finish else
    let tS ← show1 (← compact t)
    if bad tS then finish else
    withLocalDecl n bi t fun x => lams (b.instantiate1 x) (acc.push (binderText n bi tS named))
  | _ => finish

/-- Statement and value with their common leading binders moved in front of the colon:
`def f : ∀ (x : A), B := fun (x : A) ↦ b` is written `def f (x : A) : B := b`. This keeps the names of
instance binders and says each binder once. Gives the binders, the rest of the statement and the rest
of the value (each both ways, see `both`). -/
partial def peel (ty val : Expr) (acc : Array String) : M (Array String × (String × String) × (String × String)) := do
  let finish : M (Array String × (String × String) × (String × String)) := do
    return (acc, ← both (do show1 (← compact ty)), ← lams val #[])
  match ty, val with
  | .forallE n t b bi, .lam n' t' b' bi' =>
    let named := isNamed n
    if !(named || bi == .instImplicit) || n.eraseMacroScopes != n'.eraseMacroScopes || bi != bi' || !(t == t') then
      finish
    else
      let tS ← show1 (← compact t)
      if bad tS then finish else
      withLocalDecl n bi t fun x => peel (b.instantiate1 x) (b'.instantiate1 x) (acc.push (binderText n bi tS named))
  | _, _ => finish

def inTerm {α : Type} (x : M α) : CommandElabM (Option (α × Nat)) := do
  try
    liftTermElabM <| withTheReader Core.Context (fun c => { c with maxHeartbeats := 0, maxRecDepth := 100000 }) do
      let (r, st) ← x.run {}
      return some (r, st.marks)
  catch _ => return none

def indent4 (s : String) : String :=
  "\n".intercalate ((s.splitOn "\n").map fun l => if l.isEmpty then l else "    " ++ l)

def mkText (header name univ : String) (binders : Array String) (ty val : String) : String :=
  let flat := " ".intercalate binders.toList
  let bs := if binders.isEmpty then "" else if flat.length + header.length + name.length ≤ 90 && !flat.contains '\n' then " " ++ flat
    else "\n" ++ indent4 ("\n".intercalate binders.toList)
  header ++ name ++ univ ++ bs ++ " :\n" ++ indent4 ty ++ " :=\n" ++ indent4 val ++ "\n"

def firstError (msgs : MessageLog) : IO String := do
  for m in msgs.toList do
    if m.severity == .error then
      return ((← m.data.toString).take 400).toString
  return "no error message"

/-- Elaborate one command given as text, in the current scope, and give back the constant `tmp` it
declares. The environment and the messages are put back as they were. -/
def tryCmd (text : String) (tmp : Name) : CommandElabM (Except String (List Name × Expr × Option Expr)) := do
  let saved ← get
  let scope ← getScope
  let ictx := Parser.mkInputContext text "<grh>"
  let pmctx : Parser.ParserModuleContext :=
    { env := saved.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
  let (stx, mps, msgs) := Parser.parseCommand ictx pmctx {} {}
  if msgs.hasErrors then
    return .error ("does not parse: " ++ (← firstError msgs))
  if !(ictx.atEnd mps.pos) then
    return .error "does not parse as one command"
  modify fun s => { s with messages := {} }
  let r ← try
      withScope (fun sc => { sc with opts := sc.opts.setBool `Elab.async false }) (elabCommand stx)
      if (← get).messages.hasErrors then
        pure (.error (← firstError (← get).messages))
      else match (← getEnv).find? tmp with
        | some ci =>
          -- (normal form now: the helper lemmas of `tmp` exist only until the state is put back)
          let ty ← liftCoreM <| roomy <| normal tmp ci.type
          let val ← match ci.value? (allowOpaque := true) with
            | some v => pure (some (← liftCoreM <| roomy <| normal tmp v))
            | none => pure none
          pure (.ok (ci.levelParams, ty, val))
        | none => pure (.error "nothing declared")
    catch e => pure (.error ("exception: " ++ ((← e.toMessageData.toString).take 400).toString))
  set saved
  return r

def report (out : String) (j : Json) : IO Unit := do
  let h ← IO.FS.Handle.mk out .append
  h.putStrLn j.compress

syntax (name := grhCompact) "#grh_compact " str ident str str str str : command

def run (header univ origTyText origValText : String) (id : Syntax) : CommandElabM Json := do
  let written := id.getId
  let name ← liftCoreM <| realizeGlobalConstNoOverload id
  let some info := (← getEnv).find? name | return Json.mkObj [("ok", false), ("why", "constant not found")]
  let some val := info.value? (allowOpaque := true) |
    return Json.mkObj [("name", toString name), ("ok", false), ("why", "no value")]
  let isThm := match info with | .thmInfo _ => true | _ => false
  let tmpWritten := toString (written.appendAfter "_grhTmp")
  let tmpName := name.appendAfter "_grhTmp"
  let origTy ← liftCoreM <| roomy <| normal name info.type
  let origVal ← liftCoreM <| roomy <| normal name val
  let valShown ← liftCoreM <| roomy <| inlineAux name val
  let mut notes : Array Json := #[]
  let origText := mkText header (toString written) univ #[] origTyText origValText
  -- candidates: binders in front of the colon; new statement with the value as written; the reverse
  let mut cands : Array (String × Array String × String × String × Nat) := #[]
  match ← inTerm (peel info.type valShown #[]) with
  | some ((bs, (t1, t2), (v1, v2)), k) =>
    if bad t1 || bad v1 then notes := notes.push "binders in front: not printable"
    else
      cands := cands.push ("binders in front", bs, t1, v1, k)
      if !(bad t2 || bad v2) && (t2 != t1 || v2 != v1) then
        cands := cands.push ("binders in front, large applications in full", bs, t2, v2, k)
  | none => notes := notes.push "binders in front: error"
  match ← inTerm (both (do show1 (← compact info.type))) with
  | some ((t1, t2), k) =>
    if !bad t1 then cands := cands.push ("new statement, value as written", #[], t1, origValText, k)
    if !bad t2 && t2 != t1 then
      cands := cands.push ("new statement (large applications in full), value as written", #[], t2, origValText, k)
  | none => pure ()
  match ← inTerm (lams valShown #[]) with
  | some ((v1, v2), k) =>
    if !bad v1 then cands := cands.push ("statement as written, new value", #[], origTyText, v1, k)
    if !bad v2 && v2 != v1 then
      cands := cands.push ("statement as written, new value (large applications in full)", #[], origTyText, v2, k)
  | none => pure ()
  let sized := cands.map fun c => ((mkText header (toString written) univ c.2.1 c.2.2.1 c.2.2.2.1).length, c)
  for (len, which, bs, t, v, k) in sized.qsort (fun a b => a.1 < b.1) do
    if len ≥ origText.length then
      notes := notes.push (Json.str s!"{which}: not shorter")
      continue
    match ← tryCmd (mkText header tmpWritten univ bs t v) tmpName with
    | .error err => notes := notes.push (Json.str s!"{which}: {err}")
    | .ok (lps, nty, nval?) =>
      if !(lps == info.levelParams && nty.equal origTy) then
        notes := notes.push (Json.str s!"{which}: another statement")
        continue
      let mut okVal := true
      let mut diff := ""
      if !isThm then
        match nval? with
        | some nv =>
          okVal := nv.equal origVal
          if !okVal then diff := (firstDiff origVal nv).getD "?"
        | none => okVal := false
      if !okVal then
        notes := notes.push (Json.str s!"{which}: another value; first difference (as written / new): {diff} ;; {(v.take 300).toString}")
        continue
      return Json.mkObj [("name", toString name), ("ok", true), ("form", which), ("explicit", k),
        ("notes", Json.arr notes), ("text", mkText header (toString written) univ bs t v)]
  return Json.mkObj [("name", toString name), ("ok", false), ("why", "no new text passes"), ("notes", Json.arr notes)]

@[command_elab grhCompact] def elabGrhCompact : CommandElab := fun stx => do
  let some header := stx[1].isStrLit? | throwUnsupportedSyntax
  let some univ := stx[3].isStrLit? | throwUnsupportedSyntax
  let some out := stx[4].isStrLit? | throwUnsupportedSyntax
  let some ty := stx[5].isStrLit? | throwUnsupportedSyntax
  let some val := stx[6].isStrLit? | throwUnsupportedSyntax
  traceRef.set (out ++ ".trace", 0, 0)
  (← IO.FS.Handle.mk (out ++ ".trace") .append).putStrLn s!"== {stx[2].getId}"
  let j ← try run header univ ty val stx[2] catch e => do
    pure (Json.mkObj [("name", toString stx[2].getId), ("ok", false), ("why", "error: " ++ (← e.toMessageData.toString))])
  report out j

end GrhCompact
