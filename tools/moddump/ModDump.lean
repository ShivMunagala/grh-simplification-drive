/-
moddump: read compiled Lean modules (.olean) one at a time and print, for every declaration,
its kind, the size of its statement and of its body, and which other declarations they mention.

Input  (stdin): one line per module, `<module name>\t<path to .olean>`.
Output (stdout): tab-separated records
  M  <module>  <number of declarations>  <imports, comma separated>
  C  <kind>  <id>  <typeSize>  <valueSize>  <typeHash>  <valueHash>  <type deps>  <extra value deps>  <name>
  S  <id>  <strict statement hash>  <strict body hash>  <universe parameters hash>      (with `--strict`)
  A  <module>  <extension>=<number of entries>,...                                       (with `--strict`)
  N  <module>  <namespace>,...           namespaces the module registers                 (with `--strict`)
  B  <id>  <argument name>:<kind>,...    leading arguments of the statement              (with `--binders`)
With `--nsonly` only `M`, `N` and `E` are printed, which is fast: nothing is traversed.
  X  <module>  <error>                  (the module could not be read)
  E  <module>                           (end of module)

`id` and the entries of the dependency lists are 64-bit hashes of declaration names.
Sizes count term nodes: as stored in the file by default (`--noshared`), or after maximal sharing.
On the archive the two agree, because compiled files already share identical subterms.
`typeHash` / `valueHash` are Lean's own structural hashes of the statement and the body. They are
32 bits wide and ignore the names of bound variables and whether an argument is explicit or
implicit, so they are enough to notice an edited proof but not to show that a statement is the
same for every user.

`--strict` adds what the equivalence check needs for that:
  * `S`: 64-bit hashes of the statement and (for anything that is not a theorem) the body that also
    cover bound-variable names (hygiene suffixes removed) and binder kinds, a hash of the ordered
    universe parameters, and for definitions the unfolding hint and safety.
  * `A`: how many entries the module adds to each environment extension (attributes, instances,
    simp lemmas, notation, ...). A change in these numbers means other modules may elaborate
    differently even though no statement changed.

Each file is loaded on its own and released before the next one, so memory use stays small.
With `--delete`, a file is removed once it has been processed.
-/
import Lean.Environment
import Lean.Util.FoldConsts
import Lean.Util.NumObjs

open Lean

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "ax"
  | .defnInfo _ => "def"
  | .thmInfo _ => "thm"
  | .opaqueInfo _ => "opq"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "ind"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

def hashList (s : NameSet) (skip : NameSet := {}) : String :=
  let parts := s.foldl (init := (#[] : Array String)) fun acc n =>
    if skip.contains n then acc else acc.push (toString n.hash)
  " ".intercalate parts.toList

/-- How much size information to compute. Sizes need memory proportional to the term. -/
inductive SizeMode where
  | both    -- stored size and size after maximal sharing
  | raw     -- stored size only; the shared column repeats it
  | none    -- no sizes (columns are 0); dependencies only
  deriving BEq

def sizes (mode : SizeMode) (e : Expr) : IO (Nat × Nat) := do
  match mode with
  | .none => return (0, 0)
  | .raw =>
    let raw ← e.numObjs
    return (raw, raw)
  | .both =>
    let raw ← e.numObjs
    let shared ← (ShareCommon.shareCommon' e).numObjs
    return (raw, shared)

/-! ### Strict hashes -/

namespace Strict

partial def levelHash : Level → UInt64
  | .zero => 7
  | .succ l => mixHash 11 (levelHash l)
  | .max a b => mixHash 13 (mixHash (levelHash a) (levelHash b))
  | .imax a b => mixHash 17 (mixHash (levelHash a) (levelHash b))
  | .param n => mixHash 19 (hash n)
  | .mvar m => mixHash 23 (hash m.name)

def binderCode : BinderInfo → UInt64
  | .default => 1
  | .implicit => 2
  | .strictImplicit => 3
  | .instImplicit => 4

/-- A term identified by its address, for memoising over shared subterms. -/
structure Ptr where
  e : Expr

unsafe instance : Hashable Ptr where
  hash p := hash64 (ptrAddrUnsafe p.e).toUInt64

unsafe instance : BEq Ptr where
  beq a b := ptrAddrUnsafe a.e == ptrAddrUnsafe b.e

unsafe abbrev M := StateM (Std.HashMap Ptr UInt64)

/-- 64-bit structural hash that also covers binder names (without hygiene suffixes) and binder kinds. -/
unsafe def exprHash (e : Expr) : M UInt64 := do
  match e with
  | .bvar i => return mixHash 3 (hash i)
  | .const n ls => return ls.foldl (fun h l => mixHash h (levelHash l)) (mixHash 5 (hash n))
  | .sort l => return mixHash 29 (levelHash l)
  | .lit l => return mixHash 31 (hash l)
  | .fvar id => return mixHash 37 (hash id.name)
  | .mvar id => return mixHash 41 (hash id.name)
  | _ =>
    if let some h := (← get).get? ⟨e⟩ then
      return h
    let h ← match e with
      | .app f a => do
        let hf ← exprHash f
        let ha ← exprHash a
        pure (mixHash 43 (mixHash hf ha))
      | .lam n t b bi => do
        let ht ← exprHash t
        let hb ← exprHash b
        pure (mixHash (mixHash 47 (hash n.eraseMacroScopes)) (mixHash (binderCode bi) (mixHash ht hb)))
      | .forallE n t b bi => do
        let ht ← exprHash t
        let hb ← exprHash b
        pure (mixHash (mixHash 53 (hash n.eraseMacroScopes)) (mixHash (binderCode bi) (mixHash ht hb)))
      | .letE n t v b _ => do
        let ht ← exprHash t
        let hv ← exprHash v
        let hb ← exprHash b
        pure (mixHash (mixHash 59 (hash n.eraseMacroScopes)) (mixHash ht (mixHash hv hb)))
      | .mdata _ b => do
        let hb ← exprHash b
        pure (mixHash 61 hb)
      | .proj s i b => do
        let hb ← exprHash b
        pure (mixHash (mixHash 67 (hash s)) (mixHash (hash i) hb))
      | _ => pure 0
    modify fun m => m.insert ⟨e⟩ h
    return h

def hintsCode : ReducibilityHints → UInt64
  | .opaque => 1
  | .abbrev => 2
  | .regular h => mixHash 3 h.toUInt64

def safetyCode : DefinitionSafety → UInt64
  | .safe => 1
  | .unsafe => 2
  | .partial => 3

/-- What else other modules can see of a declaration besides its statement and body. -/
def extraCode : ConstantInfo → UInt64
  | .defnInfo v => mixHash (hintsCode v.hints) (safetyCode v.safety)
  | .opaqueInfo v => if v.isUnsafe then 5 else 4
  | .inductInfo v =>
    v.ctors.foldl (fun h c => mixHash h (hash c))
      (mixHash (hash v.numParams) (mixHash (hash v.numIndices) (if v.isRec then 1 else 0)))
  | .ctorInfo v => mixHash (hash v.cidx) (mixHash (hash v.numParams) (hash v.numFields))
  | .recInfo v => mixHash (hash v.numParams) (mixHash (hash v.numMotives) (hash v.numMinors))
  | _ => 0

/-- `S` record for one declaration. Bodies of theorems are not hashed: nothing else can see them. -/
unsafe def record (ci : ConstantInfo) : M String := do
  let th ← exprHash ci.type
  let vh ← match ci with
    | .thmInfo _ => pure (0 : UInt64)
    | _ => match ci.value? (allowOpaque := true) with
      | some v => exprHash v
      | none => pure 0
  let lp := ci.levelParams.foldl (fun h n => mixHash h (hash n)) 71
  return s!"S\t{ci.name.hash}\t{th}\t{mixHash vh (extraCode ci)}\t{lp}"

/-- Names and kinds of the leading arguments of a statement (`--binders`, for looking at a difference). -/
partial def telescope (e : Expr) (acc : Array String := #[]) : Array String :=
  match e with
  | .forallE n _ b bi => telescope b (acc.push s!"{n.eraseMacroScopes}:{binderCode bi}")
  | .mdata _ b => telescope b acc
  | _ => acc

end Strict

/-- `N` record: the namespaces a module registers (entries of that extension are names). -/
unsafe def namespaceRecord (modName : String) (mod : ModuleData) (out : IO.FS.Stream) : IO Unit := do
  for (n, es) in mod.entries do
    if (toString n).endsWith "Lean.namespacesExt" then
      let names := es.map fun e => toString (unsafeCast e : Name)
      out.putStrLn s!"N\t{modName}\t{",".intercalate names.toList}"

unsafe def processOne (mode : SizeMode) (strict binders nsOnly : Bool) (modName : String) (path : System.FilePath)
    (out : IO.FS.Stream) : IO Unit := do
  let (mod, region) ← readModuleData path
  let imports := mod.imports.map fun i => toString i.module
  out.putStrLn s!"M\t{modName}\t{mod.constants.size}\t{",".intercalate imports.toList}"
  if nsOnly then
    namespaceRecord modName mod out
    out.putStrLn s!"E\t{modName}"
    region.free
    return
  let mut memo : Std.HashMap Strict.Ptr UInt64 := {}
  for ci in mod.constants do
    let tdeps := ci.type.getUsedConstantsAsSet
    let all := ci.getUsedConstantsAsSet
    let (_, tSize) ← sizes mode ci.type
    let (vSize, vHash) ← match ci.value? (allowOpaque := true) with
      | some v => do
        let (_, s) ← sizes mode v
        pure (s, v.hash)
      | none => pure (0, (0 : UInt64))
    out.putStrLn
      s!"C\t{kindOf ci}\t{ci.name.hash}\t{tSize}\t{vSize}\t{ci.type.hash}\t{vHash}\t{hashList tdeps}\t{hashList all tdeps}\t{ci.name}"
    if strict then
      let (line, memo') := (Strict.record ci).run memo
      memo := memo'
      out.putStrLn line
    if binders then
      out.putStrLn s!"B\t{ci.name.hash}\t{",".intercalate (Strict.telescope ci.type).toList}"
  if strict then
    let exts := mod.entries.foldl (init := (#[] : Array String)) fun acc (n, es) =>
      if es.size == 0 then acc else acc.push s!"{n}={es.size}"
    out.putStrLn s!"A\t{modName}\t{",".intercalate exts.toList}"
    namespaceRecord modName mod out
  out.putStrLn s!"E\t{modName}"
  out.flush
  region.free

/-- `--hashnames`: read declaration names from stdin, print `<id>\t<name>` for each. -/
def hashNames : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let s := (line.splitOn "\n").headD ""
    if s.isEmpty then continue
    stdout.putStrLn s!"{s.toName.hash}\t{s}"
  return 0

unsafe def mainUnsafe (args : List String) : IO UInt32 := do
  if args.contains "--hashnames" then
    return (← hashNames)
  let delete := args.contains "--delete"
  let strict := args.contains "--strict"
  let binders := args.contains "--binders"
  let nsOnly := args.contains "--nsonly"
  let mode : SizeMode :=
    if args.contains "--nosize" then .none else if args.contains "--noshared" then .raw else .both
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    match ((line.splitOn "\n").headD "").splitOn "\t" with
    | [m, p] =>
      try
        processOne mode strict binders nsOnly m p stdout
      catch e =>
        stdout.putStrLn s!"X\t{m}\t{e}"
      if delete then
        try IO.FS.removeFile p catch _ => pure ()
    | _ => pure ()
  stdout.flush
  return 0

def main (args : List String) : IO UInt32 := unsafe mainUnsafe args
