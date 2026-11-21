/-
moddump: read compiled Lean modules (.olean) one at a time and print, for every declaration,
its kind, the size of its statement and of its body, and which other declarations they mention.

Input  (stdin): one line per module, `<module name>\t<path to .olean>`.
Output (stdout): tab-separated records
  M  <module>  <number of declarations>  <imports, comma separated>
  C  <kind>  <id>  <typeSize>  <valueSize>  <typeHash>  <valueHash>  <type deps>  <extra value deps>  <name>
  X  <module>  <error>                  (the module could not be read)
  E  <module>                           (end of module)

`id` and the entries of the dependency lists are 64-bit hashes of declaration names.
Sizes count term nodes: as stored in the file by default (`--noshared`), or after maximal sharing.
On the archive the two agree, because compiled files already share identical subterms.
`typeHash` / `valueHash` are structural hashes of the statement and the body, used to tell whether
a recompiled module still exposes the same statements and definitions.

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

unsafe def processOne (mode : SizeMode) (modName : String) (path : System.FilePath)
    (out : IO.FS.Stream) : IO Unit := do
  let (mod, region) ← readModuleData path
  let imports := mod.imports.map fun i => toString i.module
  out.putStrLn s!"M\t{modName}\t{mod.constants.size}\t{",".intercalate imports.toList}"
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
        processOne mode m p stdout
      catch e =>
        stdout.putStrLn s!"X\t{m}\t{e}"
      if delete then
        try IO.FS.removeFile p catch _ => pure ()
    | _ => pure ()
  stdout.flush
  return 0

def main (args : List String) : IO UInt32 := unsafe mainUnsafe args
