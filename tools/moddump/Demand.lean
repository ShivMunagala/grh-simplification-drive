/-
demand: starting from the target theorems, what does the proof actually ask of each declaration?

A theorem often proves more than its users take: a conjunction of which only some parts are read, a
record of which only some fields are projected, an existential whose property is split and half dropped.
This tool follows the demand from the top down through the compiled proof terms. For every declaration it
records which components of its result are asked for by something that is itself needed, and inside each
proof it analyses a subterm only under the demand that reaches it:

  * a pair `⟨a, b⟩` (any constructor of a type with one constructor) asked only for its first component
    does not need `b`;
  * a projection `e.1`, and a `casesOn` whose branch uses only some of the fields, ask `e` only for those;
  * `have h := v; body` needs `v` only as far as `body` uses `h`;
  * an argument passed to a theorem is needed only as far as that theorem's proof uses the parameter
    (known from the previous sweep; everything is assumed needed in the first one).

Anything else (definitions, recursors of other types, rewriting, functions applied to unknown things) asks
for all of its arguments. So the result errs on the side of "needed".

Two modes.

  demand --tables < modules
      one line per module on stdin (`<module>\t<path to .olean>`), any order, can be run in parallel.
      Prints what the second mode has to know before it reaches a definition:
        T <id> <leading arguments> <name>                         theorems
        K <id> <type id> <parameters> <fields> <name>             the constructor of a one-constructor type
        J <id> <type id> <field> <parameters> <name>              projection functions
        R <id> <type id> <parameters> <fields> <0 rec | 1 casesOn, recOn> <name>   eliminators

  demand --sweep TABLES --roots a,b,c [--params FILE] [--threads N] < modules
      modules level by level, importers first: a line `-` ends a level, and no module of a level imports
      another module of the same level (so a level is done by N workers at once). Prints
        A <id>                                    the declaration is needed
        Q <id> <demand> <name>                    what is asked of a theorem, when that is not everything
        P <id> <demand per leading argument>      what a theorem's proof asks of its arguments (for the next sweep)
        V <id> <kind> <statement nodes> <body nodes> <body nodes not needed> <components not needed>
          <haves not needed> <arguments not needed> <name>      declarations where something is not needed
        H <id> <name:nodes ...>                   the local steps of that declaration whose result is not used
        G <id> <name>                             analysis given up (too many steps): everything in it counts as needed
        E <module>
        L <modules in the level>                  after each level
  A demand is written `T` (everything), `_` (nothing) or `(d d ...)` (per component).

Nothing is changed and nothing is proved here: this measures what could go. A removal is real only when the
source is edited and compiled and the judge accepts it.
-/
import Lean.Environment
import Lean.Util.FoldConsts
import Lean.Util.NumObjs

open Lean

namespace Demand

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "ax"
  | .defnInfo _ => "def"
  | .thmInfo _ => "thm"
  | .opaqueInfo _ => "opq"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "ind"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

/-! ### Demands -/

inductive Dem where
  | bot
  | top
  | tup (ds : Array Dem)
  deriving Inhabited

namespace Dem

partial def hash : Dem → UInt64
  | .bot => 11
  | .top => 13
  | .tup ds => ds.foldl (fun h d => mixHash h d.hash) 17

partial def isBot : Dem → Bool
  | .bot => true
  | .top => false
  | .tup ds => ds.all fun d => d.isBot

partial def isTop : Dem → Bool
  | .top => true
  | .bot => false
  | .tup ds => ds.size > 0 && ds.all fun d => d.isTop

def mk (ds : Array Dem) : Dem :=
  if ds.all (·.isBot) then .bot else if ds.size > 0 && ds.all (·.isTop) then .top else .tup ds

partial def join : Dem → Dem → Dem
  | .bot, d => d
  | d, .bot => d
  | .top, _ => .top
  | _, .top => .top
  | .tup a, .tup b =>
    if a.size != b.size then .top
    else mk ((a.zip b).map fun (x, y) => x.join y)

/-- Everything is asked of component `i` what `d` says, nothing of the others. -/
def only (n i : Nat) (d : Dem) : Dem :=
  if n == 0 || i ≥ n then .top
  else mk ((Array.range n).map fun j => if j == i then d else .bot)

/-- The demands on the `n` components. -/
def parts (n : Nat) : Dem → Array Dem
  | .bot => (Array.range n).map fun _ => .bot
  | .top => (Array.range n).map fun _ => .top
  | .tup ds => if ds.size == n then ds else (Array.range n).map fun _ => .top

partial def str : Dem → String
  | .bot => "_"
  | .top => "T"
  | .tup ds => "(" ++ " ".intercalate (ds.toList.map str) ++ ")"

/-- Reads one demand from a list of characters. -/
partial def parse : List Char → Dem × List Char
  | '_' :: r => (.bot, r)
  | 'T' :: r => (.top, r)
  | '(' :: r =>
    let rec go (r : List Char) (acc : Array Dem) : Dem × List Char :=
      match r with
      | ')' :: r => (.tup acc, r)
      | ' ' :: r => go r acc
      | [] => (.top, [])
      | r => let (d, r') := parse r; go r' (acc.push d)
    go r #[]
  | _ :: r => (.top, r)
  | [] => (.top, [])

/-- Reads demands separated by spaces. -/
partial def parseList (s : String) : Array Dem :=
  let rec go (r : List Char) (acc : Array Dem) : Array Dem :=
    match r with
    | [] => acc
    | ' ' :: r => go r acc
    | r => let (d, r') := parse r; go r' (acc.push d)
  go s.toList #[]

end Dem

/-! ### Tables -/

structure Tables where
  nlam : Std.HashMap UInt64 Nat := {}                          -- theorem ↦ leading arguments
  ctor : Std.HashMap UInt64 (Nat × Nat) := {}                  -- constructor ↦ parameters, fields
  proj : Std.HashMap UInt64 (UInt64 × Nat × Nat) := {}         -- projection function ↦ type, field, parameters
  elim : Std.HashMap UInt64 (Nat × Nat × Nat) := {}            -- eliminator ↦ parameters, fields, kind
  nfields : Std.HashMap UInt64 Nat := {}                       -- one-constructor type ↦ fields
  param : Std.HashMap UInt64 (Array Dem) := {}                 -- theorem ↦ demand on each leading argument

/-- The one-constructor types of Lean's core that proofs are built from. -/
def Tables.core : Tables := Id.run do
  let mut t : Tables := {}
  for (ty, c, np, nf, projs) in
      [(`And, `And.intro, 2, 2, [`And.left, `And.right]),
       (`Iff, `Iff.intro, 2, 2, [`Iff.mp, `Iff.mpr]),
       (`Exists, `Exists.intro, 2, 2, []),
       (`Subtype, `Subtype.mk, 2, 2, [`Subtype.val, `Subtype.property]),
       (`Prod, `Prod.mk, 2, 2, [`Prod.fst, `Prod.snd]),
       (`PProd, `PProd.mk, 2, 2, [`PProd.fst, `PProd.snd]),
       (`Sigma, `Sigma.mk, 2, 2, [`Sigma.fst, `Sigma.snd]),
       (`PSigma, `PSigma.mk, 2, 2, [`PSigma.fst, `PSigma.snd]),
       (`Nonempty, `Nonempty.intro, 1, 1, [])] do
    t := { t with
      nfields := t.nfields.insert ty.hash nf
      ctor := t.ctor.insert c.hash (np, nf)
      elim := ((t.elim.insert (ty ++ `rec).hash (np, nf, 0)).insert (ty ++ `casesOn).hash (np, nf, 1)).insert
        (ty ++ `recOn).hash (np, nf, 1) }
    let mut i := 0
    for p in projs do
      t := { t with proj := t.proj.insert p.hash (ty.hash, i, np) }
      i := i + 1
  return t

def num (s : String) : Nat := s.toNat?.getD 0

def Tables.addLine (t : Tables) (line : String) : Tables :=
  match line.splitOn "\t" with
  | "T" :: id :: n :: _ => { t with nlam := t.nlam.insert (num id).toUInt64 (num n) }
  | "K" :: id :: ty :: np :: nf :: _ =>
    { t with ctor := t.ctor.insert (num id).toUInt64 (num np, num nf)
             nfields := t.nfields.insert (num ty).toUInt64 (num nf) }
  | "J" :: id :: ty :: i :: np :: _ => { t with proj := t.proj.insert (num id).toUInt64 ((num ty).toUInt64, num i, num np) }
  | "R" :: id :: _ :: np :: nf :: k :: _ => { t with elim := t.elim.insert (num id).toUInt64 (num np, num nf, num k) }
  | "P" :: id :: ds :: _ => { t with param := t.param.insert (num id).toUInt64 (Dem.parseList ds) }
  | _ => t

def Tables.load (t : Tables) (path : System.FilePath) : IO Tables := do
  let h ← IO.FS.Handle.mk path .read
  let mut t := t
  repeat
    let line ← h.getLine
    if line.isEmpty then break
    t := t.addLine ((line.splitOn "\n").headD "")
  return t

/-! ### Mode 1: tables -/

/-- Leading arguments that statement and proof share. -/
partial def leading (t v : Expr) (n : Nat := 0) : Nat :=
  match t, v.consumeMData with
  | .forallE _ _ tb _, .lam _ _ vb _ => leading tb vb (n + 1)
  | _, _ => n

/-- `fun params self => self.i`: the body of a projection function. -/
partial def projBody (v : Expr) (n : Nat := 0) : Option (Name × Nat × Nat) :=
  match v with
  | .lam _ _ b _ => projBody b (n + 1)
  | .proj s i (.bvar 0) => if n ≥ 1 then some (s, i, n - 1) else none
  | .mdata _ b => projBody b n
  | _ => none

unsafe def tablesOne (modName : String) (path : System.FilePath) (out : IO.FS.Stream) : IO Unit := do
  let (mod, region) ← readModuleData path
  let mut single : Std.HashMap Name (Nat × Nat) := {}          -- one-constructor type ↦ parameters, fields
  for ci in mod.constants do
    if let .inductInfo v := ci then
      if v.ctors.length == 1 && !v.isRec && v.numIndices == 0 then
        for c in mod.constants do
          if let .ctorInfo cv := c then
            if cv.induct == ci.name then
              single := single.insert ci.name (cv.numParams, cv.numFields)
              out.putStrLn s!"K\t{c.name.hash}\t{ci.name.hash}\t{cv.numParams}\t{cv.numFields}\t{c.name}"
  for ci in mod.constants do
    match ci with
    | .thmInfo v =>
      out.putStrLn s!"T\t{ci.name.hash}\t{leading v.type v.value}\t{ci.name}"
      -- the projections of a record of propositions are theorems
      if let some (s, i, np) := projBody v.value then
        out.putStrLn s!"J\t{ci.name.hash}\t{s.hash}\t{i}\t{np}\t{ci.name}"
    | .defnInfo v =>
      if let some (s, i, np) := projBody v.value then
        out.putStrLn s!"J\t{ci.name.hash}\t{s.hash}\t{i}\t{np}\t{ci.name}"
      else if let .str p last := ci.name then
        if last == "casesOn" || last == "recOn" then
          if let some (np, nf) := single.get? p then
            out.putStrLn s!"R\t{ci.name.hash}\t{p.hash}\t{np}\t{nf}\t1\t{ci.name}"
    | .recInfo v =>
      if let .str p _ := ci.name then
        if let some (np, nf) := single.get? p then
          if v.numMotives == 1 && v.numMinors == 1 then
            out.putStrLn s!"R\t{ci.name.hash}\t{p.hash}\t{np}\t{nf}\t0\t{ci.name}"
    | _ => pure ()
  out.putStrLn s!"E\t{modName}"
  region.free

/-! ### Mode 2: the sweep -/

/-- What analysing a term asks of the bound variables around it. It depends only on the term and on
the demand, not on where the term occurs, so it is computed once per shared subterm.

Almost every variable that is used is used whole, so those are kept as a set of bits (bit `i` for the
variable with de Bruijn index `i` as seen at the term); the few that are asked for only in part are
listed with their demand, sorted by variable. -/
structure Eff where
  tops : Nat := 0
  parts : Array (Nat × Dem) := #[]
  deriving Inhabited

namespace Eff

def var (i : Nat) (d : Dem) : Eff :=
  if d.isTop then { tops := 1 <<< i } else { parts := #[(i, d)] }

def joinParts (a b : Array (Nat × Dem)) : Array (Nat × Dem) := Id.run do
  if a.isEmpty then
    return b
  if b.isEmpty then
    return a
  let mut out : Array (Nat × Dem) := Array.mkEmpty (a.size + b.size)
  let mut i := 0
  let mut j := 0
  while i < a.size || j < b.size do
    if j ≥ b.size then
      out := out.push a[i]!
      i := i + 1
    else if i ≥ a.size then
      out := out.push b[j]!
      j := j + 1
    else
      let (x, dx) := a[i]!
      let (y, dy) := b[j]!
      if x < y then
        out := out.push (x, dx)
        i := i + 1
      else if y < x then
        out := out.push (y, dy)
        j := j + 1
      else
        out := out.push (x, dx.join dy)
        i := i + 1
        j := j + 1
  return out

def join (a b : Eff) : Eff :=
  { tops := a.tops ||| b.tops, parts := joinParts a.parts b.parts }

/-- Leaving a binder: what was asked of its variable, and the effect on the variables outside. -/
def pop (a : Eff) : Dem × Eff :=
  let d0 : Dem :=
    if a.tops.testBit 0 then .top
    else if a.parts.isEmpty then .bot
    else if (a.parts[0]!).1 == 0 then (a.parts[0]!).2 else .bot
  let rest : Array (Nat × Dem) :=
    if a.parts.isEmpty then #[]
    else (a.parts.filter fun (i, _) => i != 0).map fun (i, d) => (i - 1, d)
  (d0, { tops := a.tops >>> 1, parts := rest })

end Eff

structure St where
  t : Tables := {}
  /-- what the levels above asked of each declaration (shared between the workers of a level, read only) -/
  need : Std.HashMap UInt64 Dem := {}
  /-- what this worker asks (handed back when it is done) -/
  asks : Std.HashMap UInt64 Dem := {}
  lines : Array String := #[]
  /-- per declaration -/
  memo : Std.HashMap (USize × UInt64) Eff := {}
  live : Std.HashSet USize := {}
  steps : Nat := 0
  budget : Nat := 0
  comps : Nat := 0
  haves : Nat := 0
  args : Nat := 0
  /-- names of the local steps whose result is not used, with the size of what they bind (the first forty) -/
  dropped : Array (String × Nat) := #[]

abbrev M := StateT St IO

/-- A local step whose result nothing uses: count it and remember its name. -/
def deadHave (n : Name) (v : Expr) : M Unit := do
  let k ← v.numObjs
  modify fun s => { s with haves := s.haves + 1,
                           -- (the name is copied: it lives in the module's file, which is released later)
                           dropped := if s.dropped.size < 40
                             then s.dropped.push (String.mk (toString n.eraseMacroScopes).toList, k) else s.dropped }

def ask (h : UInt64) (d : Dem) : M Unit :=
  modify fun s => { s with asks := s.asks.insert h ((s.asks.getD h .bot).join d) }

def emit (line : String) : M Unit :=
  modify fun s => { s with lines := s.lines.push line }

mutual

unsafe def ana (e : Expr) (d : Dem) : M Eff := do
  if d.isBot then
    return {}
  match e with
  | .bvar i =>
    modify fun s => { s with live := s.live.insert (ptrAddrUnsafe e) }
    return Eff.var i d
  | .const c _ =>
    modify fun s => { s with live := s.live.insert (ptrAddrUnsafe e) }
    match (← get).t.nlam.get? c.hash with
    | some n => ask c.hash (if n == 0 then d else .top)
    | none => ask c.hash .top
    return {}
  | .sort _ | .lit _ | .fvar _ | .mvar _ =>
    modify fun s => { s with live := s.live.insert (ptrAddrUnsafe e) }
    return {}
  | _ =>
    let key := (ptrAddrUnsafe e, d.hash)
    if let some r := (← get).memo.get? key then
      return r
    -- An application `f a b c` is stored as nested nodes; all of them belong to the visit.
    -- The set is taken out of the state before it is changed, so that it is changed in place:
    -- while the state still holds it, every insertion would copy it.
    modify fun s =>
      let live0 := s.live
      let s := { s with live := {} }
      let live := Id.run do
        let mut live := live0.insert (ptrAddrUnsafe e)
        let mut x := e
        while x.isApp do
          x := x.appFn!
          live := live.insert (ptrAddrUnsafe x)
        return live
      { s with live := live, steps := s.steps + 1 }
    if (← get).steps > (← get).budget then
      throw (IO.userError "budget")
    let r ← match e with
      | .app .. => anaApp e d
      | .lam _ t b _ => do
        let et ← ana t .top
        let eb ← ana b .top
        pure (et.join eb.pop.2)
      | .forallE _ t b _ => do
        let et ← ana t .top
        let eb ← ana b .top
        pure (et.join eb.pop.2)
      | .letE n t v b _ => do
        let (dx, eb) := (← ana b d).pop
        if dx.isBot then
          deadHave n v
          pure eb
        else
          let et ← ana t .top
          let ev ← ana v dx
          pure ((eb.join et).join ev)
      | .mdata _ b => ana b d
      | .proj sname i b => do
        let nf := (← get).t.nfields.getD sname.hash 0
        ana b (Dem.only nf i d)
      | _ => pure {}
    modify fun s => { s with memo := s.memo.insert key r }
    return r

/-- The branch of an eliminator, or the proof of a theorem: `fun x₁ … xₙ => body`, with the demand `d`
on the body. Returns what is asked of each `xᵢ`, and the effect on the variables outside. -/
unsafe def anaMinor (m : Expr) (k : Nat) (d : Dem) : M (Array Dem × Eff) := do
  if k == 0 then
    return (#[], ← ana m d)
  match m.consumeMData with
  | .lam _ t b _ =>
    modify fun s => { s with live := (s.live.insert (ptrAddrUnsafe m)).insert (ptrAddrUnsafe m.consumeMData) }
    let (rest, eb) ← anaMinor b (k - 1) d
    let (dx, eb) := eb.pop
    -- the type of a variable that is not used is not needed either
    let et ← if dx.isBot then pure {} else ana t .top
    return (#[dx] ++ rest, eb.join et)
  | _ =>
    -- not written as a function of the fields: it is applied to all of them
    let em ← ana m .top
    return ((Array.range k).map fun _ => .top, em)

unsafe def anaApp (e : Expr) (d : Dem) : M Eff := do
  let f := e.getAppFn
  let as := e.getAppArgs
  let top (lo hi : Nat) (eff : Eff) : M Eff := do
    let mut eff := eff
    for i in [lo:hi] do
      eff := eff.join (← ana as[i]! .top)
    return eff
  match f with
  | .const c _ =>
    let h := c.hash
    let t := (← get).t
    if let some (ty, idx, np) := t.proj.get? h then
      if as.size > np then
        ask h .top
        let mut eff ← top 0 np {}
        eff := eff.join (← ana as[np]! (Dem.only (t.nfields.getD ty 0) idx (if as.size == np + 1 then d else .top)))
        return (← top (np + 1) as.size eff)
    if let some (np, nf) := t.ctor.get? h then
      if as.size == np + nf then
        ask h .top
        let mut eff ← top 0 np {}
        let ds := d.parts nf
        for j in [0:nf] do
          if (ds[j]!).isBot then
            modify fun s => { s with comps := s.comps + 1 }
          else
            eff := eff.join (← ana as[np + j]! ds[j]!)
        return eff
    if let some (np, nf, kind) := t.elim.get? h then
      if as.size ≥ np + 3 then
        ask h .top
        let mut eff ← top 0 (np + 1) {}
        let (major, minor) := if kind == 0 then (as[np + 2]!, as[np + 1]!) else (as[np + 1]!, as[np + 2]!)
        let (ds, em) ← anaMinor minor nf (if as.size == np + 3 then d else .top)
        eff := eff.join em
        eff := eff.join (← ana major (Dem.mk ds))
        return (← top (np + 3) as.size eff)
    if let some n := t.nlam.get? h then
      ask h (if as.size == n then d else .top)
      let ps := t.param.getD h #[]
      let mut eff : Eff := {}
      for i in [0:as.size] do
        let di := if i < n then ps.getD i .top else .top
        if di.isBot then
          modify fun s => { s with args := s.args + 1 }
        else
          eff := eff.join (← ana as[i]! di)
      return eff
    ask h .top
    top 0 as.size {}
  | .lam n t b _ =>
    -- `(fun x => b) v`: how a `have` made by a tactic is stored
    modify fun s => { s with live := s.live.insert (ptrAddrUnsafe f) }
    let (dx, eb) := (← ana b (if as.size == 1 then d else .top)).pop
    let mut eff := eb
    if dx.isBot then
      deadHave n as[0]!
    else
      eff := eff.join (← ana t .top)
      eff := eff.join (← ana as[0]! dx)
    top 1 as.size eff
  | _ =>
    let ef ← ana f .top
    top 0 as.size ef

end

/-- Everything in the term counts as needed (used when the analysis of a declaration is given up). -/
def askAll (e : Expr) : M Unit := do
  for c in e.getUsedConstants do
    ask c.hash .top

/-- Nodes of `e` that no demand reached. -/
unsafe def notNeeded (live : Std.HashSet USize) (e : Expr) : StateM (Std.HashSet USize) Nat := do
  let p := ptrAddrUnsafe e
  if (← get).contains p then
    return 0
  modify fun s => s.insert p
  let own := if live.contains p then 0 else 1
  let rest ← match e with
    | .app f a => do pure ((← notNeeded live f) + (← notNeeded live a))
    | .lam _ t b _ => do pure ((← notNeeded live t) + (← notNeeded live b))
    | .forallE _ t b _ => do pure ((← notNeeded live t) + (← notNeeded live b))
    | .letE _ t v b _ => do pure ((← notNeeded live t) + (← notNeeded live v) + (← notNeeded live b))
    | .mdata _ b => notNeeded live b
    | .proj _ _ b => notNeeded live b
    | _ => pure 0
  return own + rest

unsafe def sweepDecl (ci : ConstantInfo) : M Unit := do
  let h := ci.name.hash
  let s ← get
  let d := (s.need.getD h .bot).join (s.asks.getD h .bot)
  if d.isBot then
    return
  emit s!"A\t{h}"
  let tSize ← ci.type.numObjs
  let some v := ci.value? (allowOpaque := true)
    | do
      askAll ci.type
      return
  let vSize ← v.numObjs
  modify fun s => { s with memo := {}, live := {}, steps := 0, budget := 20 * (tSize + vSize) + 100000,
                           comps := 0, haves := 0, args := 0, dropped := #[] }
  try
    -- A statement is needed whole, as it is written: everything it mentions is asked for in full,
    -- also a proof that sits inside it under a projection.
    askAll ci.type
    match ci with
    | .thmInfo _ =>
      let n := (← get).t.nlam.getD h 0
      let (ps, _) ← anaMinor v n d
      if ps.any fun p => !p.isTop then
        emit s!"P\t{h}\t{" ".intercalate (ps.toList.map Dem.str)}"
      if !d.isTop then
        emit s!"Q\t{h}\t{d.str}\t{ci.name}"
    | _ =>
      let _ ← ana v .top
    let s ← get
    if s.comps + s.haves + s.args > 0 then
      let (dead, _) := Id.run ((notNeeded s.live v).run {})
      emit s!"V\t{h}\t{kindOf ci}\t{tSize}\t{vSize}\t{dead}\t{s.comps}\t{s.haves}\t{s.args}\t{ci.name}"
      if !s.dropped.isEmpty then
        emit s!"H\t{h}\t{" ".intercalate (s.dropped.toList.map fun (n, k) => s!"{n}:{k}")}"
  catch _ =>
    -- given up: the state is as it was before the attempt; ask for everything the declaration mentions
    askAll ci.type
    askAll v
    emit s!"G\t{h}\t{ci.name}"
  modify fun s => { s with memo := {}, live := {}, dropped := #[] }

/-- Declarations of a module, each after everything in the module that uses it. -/
def usersFirst (mod : ModuleData) : Array ConstantInfo := Id.run do
  let mut locals : Std.HashMap Name ConstantInfo := {}
  for ci in mod.constants do
    locals := locals.insert ci.name ci
  -- order with every declaration after what it uses, then reversed
  let mut order : Array ConstantInfo := #[]
  let mut done : NameSet := {}
  for root in mod.constants do
    if done.contains root.name then
      continue
    let mut stack : Array (ConstantInfo × Array Name × Nat) := #[]
    done := done.insert root.name
    stack := stack.push (root, root.getUsedConstantsAsSet.foldl (init := #[]) fun acc n => acc.push n, 0)
    while !stack.isEmpty do
      let (ci, used, i) := stack.back!
      if i < used.size then
        stack := stack.set! (stack.size - 1) (ci, used, i + 1)
        let c := used[i]!
        if !done.contains c then
          if let some cc := locals.get? c then
            done := done.insert c
            stack := stack.push (cc, cc.getUsedConstantsAsSet.foldl (init := #[]) fun acc n => acc.push n, 0)
      else
        stack := stack.pop
        order := order.push ci
  return order.reverse

/-- Everything that touches the module's terms happens in here, so that nothing built from them is
still alive when the caller releases the module's file. -/
unsafe def sweepBody (mod : ModuleData) : M Unit := do
  for ci in usersFirst mod do
    sweepDecl ci

unsafe def sweepOne (modName : String) (path : System.FilePath) : M Unit := do
  let (mod, region) ← readModuleData path
  sweepBody mod
  emit s!"E\t{modName}"
  region.free

/-- One worker: takes modules of the level from a shared counter until none is left. Returns its
output lines and what it asked. -/
unsafe def runWorker (t : Tables) (need : Std.HashMap UInt64 Dem) (mods : Array (String × String))
    (next : IO.Ref Nat) : IO (Array String × Array (UInt64 × Dem)) := do
  let mut st : St := { t := t, need := need }
  repeat
    let i ← next.modifyGet fun n => (n, n + 1)
    if i ≥ mods.size then
      break
    let (m, p) := mods[i]!
    try
      let (_, st') ← (sweepOne m p).run st
      st := st'
    catch e =>
      st := { st with lines := st.lines.push s!"X\t{m}\t{e}", memo := {}, live := {} }
  return (st.lines, st.asks.toArray)

def argAfter (args : List String) (flag : String) : Option String :=
  match args with
  | a :: b :: rest => if a == flag then some b else argAfter (b :: rest) flag
  | _ => none

unsafe def mainUnsafe (args : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  if args.contains "--tables" then
    repeat
      let line ← stdin.getLine
      if line.isEmpty then break
      match ((line.splitOn "\n").headD "").splitOn "\t" with
      | [m, p] =>
        try
          tablesOne m p stdout
        catch e =>
          stdout.putStrLn s!"X\t{m}\t{e}"
      | _ => pure ()
    stdout.flush
    return 0
  let some tables := argAfter args "--sweep"
    | do
      IO.eprintln "usage: demand --tables | demand --sweep TABLES --roots a,b,c [--params FILE] [--threads N]"
      return 2
  let mut t ← Tables.core.load tables
  if let some p := argAfter args "--params" then
    t ← t.load p
  let threads := max 1 (num ((argAfter args "--threads").getD "1"))
  let mut need : Std.HashMap UInt64 Dem := {}
  for r in ((argAfter args "--roots").getD "").splitOn "," do
    if !r.isEmpty then
      need := need.insert r.toName.hash .top
  -- stdin: the modules level by level; a line `-` ends a level. No module of a level imports another
  -- module of the same level, so the modules of one level can be done at the same time.
  let mut level : Array (String × String) := #[]
  let mut more := true
  while more do
    let line ← stdin.getLine
    let fields := ((line.splitOn "\n").headD "").splitOn "\t"
    match fields with
    | [m, p] => level := level.push (m, p)
    | _ =>
      if !level.isEmpty then
        let k := min threads level.size
        let next ← IO.mkRef 0
        let mut tasks := #[]
        for _ in [0:k] do
          tasks := tasks.push (← IO.asTask (runWorker t need level next))
        let mut results := #[]
        for task in tasks do
          results := results.push (← IO.ofExcept task.get)
        tasks := #[]
        for (lines, asks) in results do
          for l in lines do
            stdout.putStrLn l
          for (h, d) in asks do
            need := need.insert h ((need.getD h .bot).join d)
        stdout.putStrLn s!"L\t{level.size}"
        stdout.flush
        level := #[]
      if line.isEmpty then
        more := false
  stdout.flush
  return 0

end Demand

def main (args : List String) : IO UInt32 := unsafe Demand.mainUnsafe args
