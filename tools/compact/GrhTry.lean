/-
GrhTry: can a theorem be proved again by one call of standard automation?

A large part of the archive is lemmas whose statements mention only Mathlib: facts at library level
that the archive proves for itself, often by a long hand-made derivation. The command

    #grh_try "<full name of the theorem>" "<output file>"

takes the statement of an existing theorem, tries a fixed list of closing tactics on it, each with a
small budget, and appends one line of JSON: which tactics close it, and the size of the proof each one
builds (to compare with the size of the proof it has). Nothing is added to the environment.
tools/try_auto.py drives this and turns the answers into edits; whether a new proof is used is decided
later, by compiling the file it belongs to and comparing sizes.
-/
import Lean
open Lean Meta Elab Term Command Tactic

namespace GrhTry

def toName (s : String) : Name :=
  (s.splitOn ".").foldl (fun n c => match c.toNat? with
    | some k => .num n k
    | none => .str n c) .anonymous

/-- The tactics tried, cheapest first, each with its budget (in the unit of `maxHeartbeats`, times 1000). -/
def battery : List (String × Nat) := [
  ("rfl", 2000), ("simp", 10000), ("norm_num", 10000), ("omega", 10000), ("linarith", 10000),
  ("positivity", 10000), ("ring", 10000), ("tauto", 10000), ("aesop", 15000), ("simp_all", 15000),
  ("field_simp", 10000), ("gcongr", 10000), ("fun_prop", 10000), ("bound", 10000), ("grind", 20000),
  ("nlinarith", 20000), ("norm_num [*]", 10000), ("exact?", 40000)]

/-- Libraries a new proof may draw on. The file of the theorem is imported to read its statement, so the
theorem itself, and everything else in the archive, is in scope: a search would simply find the theorem.
A proof counts only if it mentions nothing of the archive. -/
def libraryRoots : List Name := [`Mathlib, `Batteries, `Init, `Std, `Lean, `Aesop, `Qq, `ProofWidgets, `Plausible,
  `LeanSearchClient, `ImportGraph, `Cli]

def fromLibraryOnly (env : Environment) (pf : Expr) : Bool :=
  pf.getUsedConstants.all fun c =>
    match env.getModuleIdxFor? c with
    | some idx => libraryRoots.contains (env.header.moduleNames[idx.toNat]!).getRoot
    | none => true                                      -- made while trying (a helper lemma of the tactic)

def tryTactic (ty : Expr) (tac : String) (budget : Nat) : TermElabM (Option Nat) := do
  let saved ← saveState
  let r ← tryCatchRuntimeEx
    (do
      let now ← IO.getNumHeartbeats
      withTheReader Core.Context
          (fun c => { c with maxHeartbeats := budget * 1000, initHeartbeats := now, maxRecDepth := 10000 }) do
        match Parser.runParserCategory (← getEnv) `tactic tac with
        | .error _ => pure none
        | .ok stx =>
          let mvar ← mkFreshExprMVar ty
          let goals ← Tactic.run mvar.mvarId! (do
            evalTactic (← `(tactic| intros))
            evalTactic stx)
          if !goals.isEmpty then pure none else
          Term.synthesizeSyntheticMVarsNoPostponing
          let pf ← instantiateMVars mvar
          if pf.hasMVar || pf.hasSorry || !fromLibraryOnly (← getEnv) pf then pure none else
          pure (some (← (ShareCommon.shareCommon' pf).numObjs)))
    (fun _ => pure none)
  saved.restore
  return r

def report (out : String) (j : Json) : IO Unit := do
  let h ← IO.FS.Handle.mk out .append
  h.putStrLn j.compress

syntax (name := grhTry) "#grh_try " str str : command

@[command_elab grhTry] def elabGrhTry : CommandElab := fun stx => do
  let some nm := stx[1].isStrLit? | throwUnsupportedSyntax
  let some out := stx[2].isStrLit? | throwUnsupportedSyntax
  let name := toName nm
  let some info := (← getEnv).find? name |
    report out (Json.mkObj [("name", nm), ("found", false)])
  let orig ← match info.value? (allowOpaque := true) with
    | some v => (ShareCommon.shareCommon' v).numObjs
    | none => pure 0
  let saved ← get
  let mut wins : Array Json := #[]
  for (tac, budget) in battery do
    if wins.size < 2 then
      let r ← try liftTermElabM (tryTactic info.type tac budget) catch _ => pure none
      if let some n := r then
        wins := wins.push (Json.mkObj [("tac", tac), ("size", n)])
  set saved
  report out (Json.mkObj [("name", nm), ("found", true), ("proof", orig), ("wins", Json.arr wins)])

end GrhTry
