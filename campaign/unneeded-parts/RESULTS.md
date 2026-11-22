# What the five theorems do not need

A proof this large could be carrying mathematics that its conclusion never uses: a theorem that proves five
things of which one is read, a hypothesis that a proof ignores, a step whose result is thrown away. This
campaign measured how much there is, and removes it, largest first.

## The measurement

`tools/demand.py` (with `tools/moddump/Demand.lean`) starts from the five target theorems and follows the
demand down through the compiled proof terms. For every declaration it records which components of its
result are asked for by something that is itself needed, and inside each proof it looks at a subterm only
under the demand that reaches it:

- a pair `⟨a, b⟩` (any constructor of a type with one constructor: conjunctions, existentials, records)
  that is asked only for its first component does not need `b`;
- a projection `e.1`, or a case split whose branch uses only some of the fields, asks `e` only for those;
- `have h := v; body` needs `v` only as far as `body` uses `h`;
- an argument passed to a theorem is needed only as far as that theorem's proof uses the parameter. This
  is learned in one sweep and used in the next, so the sweeps are repeated until nothing changes.

Everything else (definitions, recursors of other types, rewriting, functions applied to unknown things)
asks for all of its arguments, and a statement is needed whole once its theorem is needed at all. So the
result errs on the side of "needed": what it calls unneeded really is, up to mistakes in the tool, and the
judge decides about each removal anyway.

A sweep over the 146,531 modules of the cone takes twelve minutes on a rented 60-core machine. The
modules are processed level by level over the import graph (202 levels), each shared subterm is analysed
once per demand, and the effect of a subterm on the variables around it is kept as a set of bits.

### Result (state of change 30; written-out size 2,705,323,909 nodes)

| Sweep | Not needed | Whole declarations nothing asks for | Inside declarations that stay |
|---|---:|---:|---:|
| 1: components and local steps | 23,201,741 (0.86%) | 4,163 declarations, 7,854,643 nodes | 15,347,098 nodes in 70,550 declarations |
| 2: with unused arguments | 28,244,488 (1.04%) | 5,541 declarations, 11,084,732 nodes | 17,159,756 nodes in 92,542 declarations |
| 3: again | 28,883,214 (1.07%) | 5,759 declarations, 11,391,842 nodes | 17,491,372 nodes in 98,227 declarations |

6,784 theorems are asked for only part of their result; about 1.1 million local steps and 328,000 arguments
are not needed.

**So the proof uses almost everything it proves: about 1% is not needed.** There is no large unused block.
What there is comes in two kinds:

- **Whole declarations that are reached only through an unneeded part** (11.4 million nodes). They hang on
  2,140 entry points, mentioned in 1,524 declarations that stay. One edit at such a place frees everything
  behind it. The distribution is steep: the largest place frees 2.6 million nodes, the next 0.6 million,
  the thirtieth 53,000.
- **Small unneeded pieces inside proofs that stay** (17.5 million nodes in 98,227 declarations, on average
  under 200 nodes each): mostly local steps whose result is not used.

A simpler pass from the bottom up (`tools/liveness.py`: arguments that neither statement nor proof of a
theorem mentions, what is passed for them, and unused local steps) had given 0.75% before: 68,747 theorems
with such an argument, 1.02 million unused local steps.

### Checks on the measurement

- No declaration the sweep calls needed lies outside the cone, except 73 private helpers of declarations
  whose name occurs in two modules. The cone tool counts such a name once and follows only the first
  copy's references, so it misses these helpers; a small undercount in the cone tool, not in the sweep.
- Every declaration mentioned by the statement of a needed declaration is needed (0 violations). A first
  version of the sweep let a proof that sits inside a statement under a projection count as unneeded;
  statements now count whole.
- The first finding was confirmed by reading the source before anything was changed (below), and each
  removal goes through the judge like any other change.

## Removals recorded

| Change | What | Left the cone |
|---|---|---|
| 33 | `GlobalTheory.Unf.unfoldings_of_chain` proves eight statements about period unfoldings as a tuple of eight citations. Its only user read the sixth and now cites that lemma directly | 152 declarations, −577,102 nodes, −27,474 tokens |
| 34 | `GlobalTheory.DownLift.Sat.saturated` had three hypotheses that its proof introduced as `_` and never used. Its only user built one of them from `GlobalTheory.RawLift.rawLift_main`, the main theorem of the raw theta lift (injectivity upward, positivity of the inner product, spanning by parts, surjectivity of theta), and used that theorem for nothing else. The hypotheses are gone from the statement and the step from the user | 861 declarations, −2,587,854 nodes, −159,625 tokens |
| 35 | Eight theorems that prove lists of statements (lengths of kernels and cokernels, bounds along ramified coefficient chains, lifting of points, facts about a host field, hypotheses on parameters): their users cite the lemma for the part they read. No statement changed | 672 declarations, −1,014,148 nodes, −61,839 tokens |
| 37 | Second list, 13 files. `UpperTheory.V.Af.cuspSpectrumGL` (a tuple of three; both users read the third) and `CrystallineSemistableComparison.cstSmooth_of_etSide` (its users read the first part; that part's proof is split off into two lemmas) are bypassed. Two statements are trimmed: `UpperTheory.V.Loc.isType_and_isLocallyCrystalline_rz` stated two facts and all four uses read the second; `PositivityTheory.PlacePermOperatorBicommutantSpan.ei_inv` likewise. Two proofs lose a step whose result was never mentioned again | 361 declarations, −931,745 nodes, −42,279 tokens |
| 38 | Third list (GlobalTheory), 22 files. Seven bundles bypassed (de Rham comparison, semicontinuity for a finite projective complex, Galois characters from Artin, and four others). For three more the needed part had no lemma of its own; one is split off next to the bundle (`stokes_dbar`, `rPointT_holds` and `genPointT_holds`, `recognition_of_uRecDvr`). `GlobalTheory.JetRoad.jetRoad` is trimmed from 14 conjuncts to the 9 its five users read | 319 declarations, −1,204,484 nodes, −58,102 tokens |

Together: 2,365 declarations, −6,315,333 nodes, −349,319 tokens.

Two points of the second list were not real (see below). In change 37 one file no longer makes two equation lemmas
of definitions, because nothing in it unfolds those definitions any more; the judge used to count such marks and now
compares them by name. In change 38 one user of the trimmed statement needed no change in its source; the judge now
also takes the compiled file of such a module, when it was compiled with the trimmed module in place.

## What the measurement got wrong

Two of the first 28 items were not real. In both, a theorem is proved twice under one name, in two modules
that are never imported together, with different proofs. The tables behind the cone keep one record per
name, so the sweep looked at one copy while the user sees the other. There are 144 such names (all with the
same statement in each copy; 72 with different proofs). The cone tool should treat the copies as separate
declarations; until it does, an item whose theorem has a second copy has to be checked by reading.

## How a removal is made

See [the brief](BRIEF.md). In short: go around a bundle whose users read one part, or trim the statement to
what is read, or delete a step whose result nothing uses. When a statement changes, every user is compiled
again with the changed file in place.
