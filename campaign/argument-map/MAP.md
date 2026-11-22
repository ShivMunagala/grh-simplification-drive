# A map of the argument

This is a plain-language map of the formal proof of the Riemann Hypothesis and of GRH for Dirichlet
L-functions. It says what the main steps state, how much of the proof hangs on each, and where a shorter
mathematical route might exist. It is a first step: it was made by reading statements and the first
lines of proofs, not whole proofs. Where I could not tell something, I say so.

It was written by an AI assistant (Claude) from the statements and the dependency data, and has not been
checked by a mathematician. It describes how the proof is built and what each part costs; it makes no
claim about whether the proof is correct. The candidates in section 4 are guesses to be tested, not
findings.

**How cost is measured.** All shares are shares of the *written-out size*: the size of all fully
expanded proofs that the five target theorems depend on (2,789,304,299 term nodes; Mathlib is free).
"What hangs on a declaration" means what the targets reach *only* through it (its subtree in the
dominator tree of the dependency graph, from `tools/ablation.py`). Removing a declaration and every
use of it would remove exactly that much.

**One caveat runs through the whole map.** Many steps take published theorems as *hypotheses*, and
these hypotheses are discharged far up, in one top-level assembly. The cost of those published inputs is
then charged to the assembly, not to the step that needs them. So the exclusive share of a block can
understate what it really costs. For the largest such case (the covolume bound, section 2.B) I measured
the cost including its inputs by cutting the graph; that number is given separately.

**Sources.** The author's short public remark (4 pages) was read; it gives a timeline of ideas, not an
outline, but several items in it match blocks found here. I quote nothing from it beyond single words.

---

## 1. The chain at the top

Six theorems form a "spine": everything the targets need below a spine theorem passes through it.

| # | Spine theorem (module) | Share | In plain words |
|---|---|---:|---|
| 1 | `allChi` (`Supplements.Kernels.MainTheorems`) | 100% | Same statement as 2; a rename. |
| 2 | `UpperTheory.FinalTheorems.everyCharacter` (`Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion`) | 100% | GRH in half-plane form: for every Dirichlet character χ, L(s, χ) ≠ 0 when Re s > 1/2 (except the pole at s = 1 for the trivial character). |
| 3 | `UpperTheory.FinalTheorems.everyCharacter_of_row` (same module) | 79.5% | GRH follows from the existence of Galois representations attached to polarized cuspidal automorphic representations (see below). |
| 4 | `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin` (`...ThirdPlaceSeries.EveryCharacterOfLiteratureOfVWin`) | 69.2% | GRH follows from three "open" inputs (the Galois representations, twice, and a local reciprocity map) plus a bound on Galois cohomology of Tate twists ("VWin"). |
| 5 | `UpperTheory.Lit.every_character_of_theta_integrals_local_matching` (`...ThirdPlaceSeries.SiegelEisensteinSecondTermHypotheses`) | 44.7% | GRH follows from a bundle of about sixty published results on unitary groups and theta lifts, two statements about theta integrals, a covolume bound, the local reciprocity map, and VWin. |
| 6 | `UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound` (same module) | 39.1% | From the same inputs, the full list of hypotheses needed for the "definite side" family of data can be met (the list is non-empty). |

(Modules under `Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries`
are abbreviated `...ThirdPlaceSeries`.)

### What each step adds

- **Targets ← 2.** Cheap. RH follows from GRH for the trivial character of modulus 1 and the
  functional equation of ζ (zeros with Re s < 1/2 are reflected). The critical-line statements for
  primitive characters are similar. Imprimitive characters reduce to primitive ones by removing finitely
  many Euler factors, which do not vanish for Re s > 0.
- **2 ← 3 (adds 20.5%).** The proof of the Galois-representation input (6.1%, section 2.D), the
  weak local reciprocity map (0.05%), and a pool of 14.4% that the Galois-representation proof shares
  with the rest of the argument.
- **3 ← 4 (adds 10.3%).** The proof of VWin (8.2%, section 2.C) and 2.1% shared between VWin and the rest.
- **4 ← 5 (adds 24.5%).** This step is the "literature layer": a single file proves about 190 small
  theorems, each restating a published result and pointing to its proof in the tree, and bundles them.
  It also proves the covolume bound (7.1% exclusive, 13.6% with its inputs; section 2.B) and the theta
  integral statements (1.4%). The rest (about 16%) is shared support for these.
- **5 ← 6 (adds 5.6%).** The closing step: Green's classification of the cuspidal characters of
  GL_d over a finite field (used to see that the needed characters are regular), a "shape" theorem that
  turns the hypothesis list into families of data, and the analytic endgame. Plus 4.3% shared support.
- **Below 6 (39.1%).** Building the families: section 2.A.

### The strategy at this level, as far as I can tell

1. **Analytic endgame (cheap, about 0.1%).** For a primitive character ψ, take the cyclic group of
   characters it generates. Form a weighted sum of explicit-formula quantities: the smoothed prime sum
   Σ_{n≤y} Λ(n)(y/n − 1) − y log y + (1+γ)y, plus weighted twisted analogues for the other characters
   in the group. A one-sided bound of this sum by y^{θ} for all large y rules out zeros with
   Re s > θ for every character in the group (a Landau-type positivity argument). The proof needs this
   with θ = 1/2 + O(ε) for every ε > 0. The classical analytic number theory used here (Landau's
   lemma, zero-free regions, Perron's formula, Siegel–Walfisz) is small: each piece is a few hundredths
   of a percent.
2. **The one-sided bound comes from families.** For each ε there must be a family of data
   (`FamP`, built on a structure `D7`) at every large scale x. A datum is, roughly, a CM field with its
   totally real subfield, hermitian spaces and lattices, Harish-Chandra parameters at the real places
   indexed by binary "words", and local data at a finite set of primes. The family has to be "tied" to
   the character sums, and then a counting (determinant) argument gives the bound. This matches the
   author's remark: a Stepanov-type auxiliary construction, where multiplicity is won by chaining theta
   lifts between totally definite unitary groups, with a chain of length about √x.
3. **Making the families exist** is the expensive part. It needs a list of about forty properties
   (the structure `GlobalTheory.Fc.Hyps`): rows of theta-series coefficients, divisibility and level
   properties, primitivity, multiplicity, a covolume bound, counts, and so on. Section 2.A builds them.
4. **Inputs from arithmetic.** Two inputs are of a different nature: (a) the existence of Galois
   representations for polarized regular algebraic cuspidal representations of GL_n over CM fields,
   with local–global compatibility (the results of Harris–Taylor, Shin, Chenevier–Harris, Caraiani
   in the literature; here proved in the tree by a different route); (b) VWin, a bound on the sizes of
   Tate–Shafarevich-type groups of Tate twists over certain abelian fields. The remark describes (b)
   as a much weaker relative of Vandiver's conjecture.

---

## 2. The largest blocks

The 25 largest blocks off the spine are listed below. They are heavily nested: one block often has a
single child that carries almost all of it (a statement restated under a new name, or with one
hypothesis discharged). The 25 entries form **four lines of argument**. Shares are not additive along
a nested chain: the outermost one counts.

| Rank | Block | Share | Line | Parent (what uses it) |
|---:|---|---:|---|---|
| 1 | `GlobalTheory.Fc.S0.StageU.hypotheses_nonempty_of_unramified_exponents_alt` | 15.3% | A | spine 6 |
| 2–6 | `UpperTheory.One.vwin_of_row` and four nested restatements down to `UpperTheory.V.HV.DescentVanishingReductions.v_window_of_automorphy_csd_ss_mono_odd` | 8.2% → 8.1% | C | spine 3 |
| 7 | `UpperTheory.V.HV.DescentVanishingReductions.vwin_of_hypotheses_H_E_alt` | 7.3% | C | rank 6 |
| 8 | `SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt` | 7.1% | B | spine 4 |
| 9 | `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter` | 6.1% | D | spine 2 |
| 10 | `UpperTheory.Gal.Int.galoisRepresentations_of_thetaLift` | 5.6% | D | rank 9 |
| 11–12 | `GlobalTheory.T.large_unramified_exponent_bundles_exist_alt` = `GlobalTheory.Fc.StageOneU.member_bundles_large_unramified_exponents_alt` | 5.4% | A | rank 1 |
| 13 | `UpperTheory.Gal.Int.Geo.geoOne_holds` | 4.9% | D | rank 10 |
| 14 | `UpperTheory.Gal.Int.Geo.geometric_realization_of_weight_one` | 4.7% | D | rank 13 |
| 15 | `GlobalTheory.Fc.AllAtMemberStage0.allRows_of_open0_alt` | 3.8% | A | rank 1 |
| 16–17 | `PositivityTheory.HtPt.Ah.deep_slim_use` = `GlobalTheory.CompanionTheory.Ar.Plug.deepStR_of_use` | 3.7% | B | rank 8 |
| 18–19 | `GlobalTheory.T.member_exists_baseLattice_alt` = `GlobalTheory.Mem.Top.Bl.exists_baseLattice_of_prime_alt` | 3.4% | A | rank 12 |
| 20–24 | `UpperTheory.GalC.final_alt_alt` and four nested steps down to `UpperTheory.GalC.linkN_of_twGood_galoisPreconditions` | 3.3% → 3.1% | A | rank 1 |
| 25 | `GlobalTheory.Fc.S0.ontoX_and_lamLow_of_unitaryGroupHypotheses'` | 2.9% | A | spine 6 |

Just below the top 25: `UpperTheory.Gal.Int.Geo.steps_holds` (2.9%, D), `GlobalTheory.BigOn.ontoX_of_hypotheses_alt_alt`
(2.8%, A), the good-tower volume chain (2.7%, B), and the open-orbit chain (2.65%, A).

### A. Building the definite-side families (39.1% in all, under spine 6)

Spine 6 itself proves that the hypothesis list for the "definite side" can be met. Its proof combines a
handful of sub-results; together they hang 20.9%, and another **18.3% is support shared among them**
(mostly in `Development.AbelianVarietyTheory`, and 4.2% in `Formalism`). The vocabulary in this part
("members", "bundles", "rows", "slots", "linked at") is internal, and I could only partly decode it.

- **`hypotheses_nonempty_of_unramified_exponents_alt` (15.3%).** States that, given the third-place
  hypothesis bundle, rationality of the rows, the local reciprocity map, a grid of evaluation points
  and three "linked" conditions on the parameters, the hypothesis list is non-empty. In plain terms: the
  family members exist, they satisfy all row conditions, and their parameters satisfy the norm,
  functional and covolume conditions. Its cost:
  - *Existence of members with large unramified exponents* (5.4%, ranks 11–12): suitable theta lattices
    exist at all places, with a "base lattice" at a prime (3.4%, ranks 18–19), a finite-level statement
    about rational cusp data (1.3%) and closing the membership conditions (0.7%); extending adelic data to
    larger fields (0.7%).
  - *All row properties at every member* (3.8%, rank 15): local row properties obtained from the
    Siegel–Weil formula (1.6%), a "service" property derived from the link condition (1.1%),
    period entries and level valuations (0.4%).
  - *Norm-link condition* (3.3%, ranks 20–24): a chain of five nested statements ending in
    `GlobalTheory.NLinkClose.main_alt_alt` (2.3%). It bounds certain local quantities at the primes
    2 and 3 along a family and links them to Galois-cohomology lengths (one sub-result is named after
    a bound of block cocycles by Sha). Parts: row bounds in a joint setting (0.95%), an eventual
    congruence bound (0.5%), polynomial bounds on embedding jumps (0.4%).
- **`ontoX_and_lamLow_of_unitaryGroupHypotheses'` (2.9%, rank 25).** A surjectivity statement for the
  family data ("onto"), from twelve published inputs (Clozel's cohomological purity, Green's theorem,
  ℓ-adic Hecke characters, Chebotarev, base change to definite unitary groups, Bhatt–Scholze lattices,
  rapid decay of cusp forms, Casselman–Wallach, ...). Parts: a threshold-run statement on index bounds
  (1.1%), passing from "page" to "geometric" statements (0.4%), an exponent bound from base change
  and crystalline lattices (0.4%).
- **`open0_of_unitary_group_hypotheses` (2.65%).** The twelve "open parameter" conditions (primitivity,
  divisor, decomposition point, multiplicity, defect, ...) hold for the chosen parameters. Almost all of
  it is a chain of **six nested restatements** (`main_theorem_published_inputs_third_alt_alt`,
  `miStarRow_alt_alt`, `..._variant_alt_alt`, `miStarRowClosing_alt_alt`,
  `main_theorem_published_results_final_alt_alt`, `miStar_row_alt_alt`), each with one child, ending in
  `main_theorem_from_published_results_alt_alt_alt_alt_alt` (2.0%). The statements carry fourteen
  published inputs on unitary groups (Harish-Chandra finiteness, Weil representation, Siegel–Weil,
  the doubling method, discrete series, strong approximation).
- Smaller pieces directly under spine 6: theta-lift row properties (0.8%), separation of functionals
  from Howe duality and Siegel–Weil (0.7%), a Fourier-coefficient fit (0.6%), twisted multiplicity one
  (0.4%), a tower of theta matchings (0.4%).

### B. The covolume bound (7.1% exclusive; 13.6% with its literature inputs)

- **`SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt` (7.1%, rank 8).** From fifteen
  published inputs (resolution of singularities and principalisation in characteristic zero, the
  Poincaré–Lelong formula, arithmetic Hilbert–Samuel, Moriwaki's bigness theorem, Fargues' exact
  sequence, Zarhin's trick, toroidal compactifications of Siegel and unitary Shimura varieties, Arakelov
  degrees, Grothendieck–Messing deformation, ...) it proves `CovolumeBoundOfX`: eventually, at every
  point of every family, a lattice in the construction has normalized log-covolume below a threshold.
  The threshold is a main term plus C·B0·log log x, required for all large C.
- Its cost: a uniform mean-height bound for "deep" sub-lattices (3.7%, ranks 16–17), which in turn is a
  chain of four restatements ending in a **volume theorem for towers of Shimura varieties**
  (`GlobalTheory.CompanionTheory.Ar.Top.goodTower_and_volume`, 2.2%: a good tower exists, volumes are
  proportional, slopes are bounded on average); and a height lower bound with Hodge-bundle estimates
  (`topCovolG_alt_alt`, 2.2%).
- **With inputs.** Cutting the edges from the top assembly to this block and to the fifteen inputs it
  receives removes **13.6%** of the whole (6.6% in `Development.AbelianVarietyTheory`, 2.6% in
  `Development.AutomorphicSpectrum`, 2.0% in `GroundTheory`, 1.5% in `Development.WeilBound`). The
  only consumer I found is a single step of spine 6 (the "L3" linked condition). This matches items 13
  and 18 of the author's timeline (a slope inequality of Bost; computation of covolumes).

### C. VWin: bounds on Galois cohomology of Tate twists (8.2%)

- **Statement.** For every primitive character ψ and small ε: for suitable pairs of primes q, d
  (q ≡ 3 mod 8, d ≡ 7 mod 16, q | d+1, every small odd prime divides d+1, log q and log d of size
  about Y^{ε/5}) and every abelian number field E cut out by ψ, a 2-power level and the quadratic
  symbols of q and d, the "Sha-lengths" of the twists Q_ℓ/Z_ℓ(−e), 1 ≤ e < x^{401}, are finite and
  Σ_ℓ log ℓ · Σ_e length ≤ (exp(x^ε))^{1/2}. In words: a strong vanishing statement for these
  Selmer-type groups, uniform over a large range of twists.
- **Structure.** Ranks 2–6 are five nested restatements; the work is in
  `vwin_of_hypotheses_H_E_alt` (7.3%, 1,021 sub-blocks). It splits the bound into several counts and
  proves them via automorphy: a dense-image statement for symplectic groups of rank 2
  (`sp4In0_alt`, 1.2%, with base-change units and Ferrero–Washington), an Euler-system style input named
  after Kato (`katoTwoW_of_printsH`, 1.1%), automorphy for unitary groups in three variables (0.6%),
  patching modules (0.4%), and hypotheses from patching (0.5%). The block uses the Galois
  representations of line D as an input (it is not charged for them).

### D. Galois representations for polarized cuspidal representations (6.1%)

- **Statement (`UpperTheory.GalStar.Row0b`).** For a CM field E, a prime ℓ and a regular algebraic
  cuspidal representation π of GL_a over E that is polarized (conjugate self-dual up to a character of
  the totally real subfield), there is a continuous semisimple ℓ-adic representation of the Galois group
  of E with the right Hodge–Tate weights, compatible at every place away from ℓ with the given local
  reciprocity map, and crystalline / de Rham / potentially semistable with the right Weil–Deligne
  representation at places above ℓ, as far as stated.
- **Proof route.** Not the route of the literature. Theta-lift the representation to a definite
  unitary group of large rank (`UpperTheory.TP.K.tLiftK`, 0.5%: lifts exist once the target rank is
  large), then realize it geometrically in weight one (`geometric_realization_of_weight_one`, 4.7%),
  which splits into crystalline and jump "steps" (2.9%; étale and crystalline comparison, Künneth and
  Lefschetz, a projective bundle formula) and Kodaira–Spencer statements (1.5%, including an integral
  model of Harris–Taylor type, 0.4%).
- The weak local reciprocity map used everywhere (`UpperTheory.Zero.LLC.recTExists`) is cheap
  (0.05%). Its laws (twisting, central character, duality, injectivity) are only required for "good"
  representations, so it is much weaker than the local Langlands correspondence for GL_n.

### Smaller lines under the spine

- Green's classification of cuspidal characters of GL_d(F_g), used in the closing step: 1.3%.
- The two theta-integral statements (seesaw equality of theta integrals and local matching of Fock
  models; the work is a "Theorem K" in the theta-lift reductions): 1.4%.
- The literature bundles themselves are cheap once their contents exist: cutting the bundle of about
  sixty published results on unitary groups frees only 0.3%, the theta local-input bundle 0.3%. The
  results inside them are referenced from many other places.

---

## 3. Known theorems proved inside

`known` lists proofs of statements named as published results. Nested entries (one proof inside
another) are merged below; the share is what hangs only on the outer proof.

| # | Statement name | What it is, as far as I can tell | Share |
|---:|---|---|---:|
| 1 | `ToroidalForFanKS` | Toroidal compactification of PEL-type unitary Shimura varieties over a CM field: smooth model, normal-crossings boundary, charts for a fan, ample polarization, logarithmic Kodaira–Spencer isomorphism (Faltings–Chai, Lan). | 1.07% |
| 2 | `SiegelToroidalIntegral` (contains `SiegelToroidalPolCharts`, 0.73%) | Toroidal compactification of the Siegel moduli space with level n over Z[ζ_n, 1/n], with semi-abelian extension and ampleness of the Hodge bundle twisted by the boundary (Faltings–Chai). | 0.75% |
| 3 | `WeilSiegelFormulaUnitary` (contains `WeilSiegelFormula`, 0.27%) | Weil's convergence criterion and the Siegel–Weil formula for unitary dual pairs in the convergent range. | 0.28% |
| 4 | `JacquetShalikaRigidity` | Jacquet–Shalika: isobaric sums with the same Satake parameters at almost all places agree (strong multiplicity one). | 0.22% |
| 5 | `DeRhamPotSemistable` | The p-adic monodromy theorem: de Rham implies potentially semistable (Berger; André, Kedlaya, Mebkhout). | 0.21% |
| 6 | `AbelianDeRham` (contains `AbelianHodgeDeRham`, 0.16%) | De Rham cohomology of an abelian scheme: locally free of rank 2g, Hodge filtration, base change, rigidity, duality. | 0.20% |
| 7 | `SiegelWeilUnitarySchrodinger` (contains its literature form, 0.18%) | Siegel–Weil formula for unitary groups in the Schrödinger model. | 0.18% |
| 8 | `PrismaticDieudonneHodge` | Classification of p-divisible groups over O_C by Breuil–Kisin–Fargues modules, compatible with the Hodge filtration (Scholze–Weinstein; Anschütz–Le Bras). | 0.18% |
| 9 | `HarishChandraFinite` | Harish-Chandra's finiteness theorem: automorphic forms of fixed level, K-type and infinitesimal character form a finite-dimensional space. | 0.18% |
| 10 | `KudlaSplittingSplitUnitary` | Kudla's splitting of the metaplectic cover over unitary dual pairs (local). | 0.13% |
| 11 | `BhattScholzeIntegral` | Integral p-adic Hodge theory of Bhatt–Scholze (lattices in crystalline representations via prismatic F-crystals). | 0.13% |
| 12 | `ClozelConjC` | Clozel's rationality: Aut(C)-conjugates of regular algebraic cuspidal representations are again such. | 0.13% |
| 13 | `GoodChernWeil` (contains `ChernWeilNumbers`, 0.08%) | Mumford's good metrics and Hirzebruch–Mumford proportionality on toroidal compactifications. | 0.12% |
| 14 | `CrystallineSmoothLift` | A comparison of de Rham cohomology with Čech/Hochschild cohomology in degrees 1 and 2, with cup products and functoriality (deformation theory of smooth lifts). I could not identify the exact reference. | 0.12% |
| 15 | `FormalAlgebraisation` | Grothendieck's formal existence (algebraization) theorem. | 0.09% |

Next in line: existence of the dual abelian scheme and biduality (0.09%), finiteness of automorphic
forms on GL (0.08%), de Rham property of ℓ-adic Hecke characters (0.08%), local Bloch–Kato (0.07%).

**What this says overall.** The archive proves a lot of literature, but literature is not where the
size is. Each known theorem hangs at most about 1% on its own, because the support it needs is shared
with other parts. I also measured all of them at once: if every one of the 350 proofs of named published
statements in the cone were replaced by an assumption, **8.4%** of the whole would drop (5.5% in
`Development.AbelianVarietyTheory`). Most of the remaining 90% is the new argument (the families of
section 2.A, VWin, the covolume bound, the Galois representations) and the support it shares. The heavy
known theorems cluster in two places: compactifications and heights of Shimura varieties (rows 1, 2, 6,
13, 15, which feed the covolume line), and the theta/Siegel–Weil theory of unitary groups (rows 3, 7,
10). The first cluster is part of the 13.6% of candidate 1 below.

---

## 4. Where a shorter route might exist

Ranked by expected gain times my confidence. "Cost" is the share that would leave the proof if the
step were replaced by a free proof; a real replacement costs something too.

### Candidate 1. The covolume bound through Arakelov geometry — 13.6% with inputs (7.1% exclusive)

- **What it is.** Line B: a bound on normalized log-covolumes of certain lattices in the construction,
  proved via toroidal compactifications, arithmetic Hilbert–Samuel, bigness, height lower bounds and a
  volume theorem for towers of Shimura varieties.
- **Why it looks cheaper than it is proved.** It is used once, as one of the forty-odd conditions on a
  family. The threshold it must meet is a main term plus C·B0·log log x for all large C. In the place
  where the threshold is spent (`Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement`)
  the error term only needs to be at most a constant times x^ε·(B0 + Nc). So the error allowed
  downstream appears to be far larger (a power x^ε against log log x) than what is proved. If the
  lattices can be written down (theta series with controlled Fourier coefficients), an elementary
  bound on a spanning set (Hadamard's inequality, Siegel's lemma, Minkowski's second theorem) might give
  "main term + O(x^ε)" directly.
- **What to check.** (a) What the main term `l3m` is and how sharp it must be: if the main term
  itself is an arithmetic volume that only Hilbert–Samuel can give, the shortcut fails. (b) Whether
  the downstream estimate I found is the only use of the threshold. (c) Whether the lattice has explicit
  generators of known height.
- **Risk.** Medium to high. The size is measured; the slack in the error term is read from statements
  only; the main term is not understood.
- **Tested 2026-11-22: not feasible as proposed.** The statements and the one place where the bound is
  spent (`IndefSide.boundsMu`, called by `divClausesR_of`) were read.
  - The slack in the error term is real: the unit `B0·log log x` is used in a single line, through
    log log x ≤ x^ε, so an error of C·x^ε·(B0 + Nc) would do.
  - The main term is needed exactly. It is a sum of CM periods (`logOm = γ + log(π/v) − Re L'/L(1,χ)`,
    with weights from the signature), and it cancels against the same sum on the other side of the
    final inequality. With the sizes of the family it is about x^4 times larger than the error that is
    allowed, so it must be right to that accuracy.
  - The lattice is defined by integrality (cusp forms that are integral at every point of the integral
    model), not by generators. The only spanning-set bound in the tree is off by a large power of x,
    and theta lifts are known to span it only up to an index of main-term size. So Hadamard's or
    Minkowski's bounds cannot give the main term.
  - In the tree the main term does not come from a volume computation but from twisting by a flat line
    bundle of degree `logOm`; the Arakelov inputs feed one statement, that integral forms of the
    remaining weight have slope at least −C·B0·log log x. The slack would relax only that statement,
    by a factor x^ε / log log x. No shorter proof of the relaxed form was found.
  - Left open: whether a two-sided inner-product formula for theta-lifted lattices could replace the
    pair of conditions (`L3` and `ON`) at once. The tree has only the lower bound.

### Candidate 2. Stage-by-stage transport inside the family construction — at least 3.5%, probably more

- **What it is.** Line A builds the family data for one choice of parameters and then moves it to
  "stronger extensions" of the parameters (named stages: origin, list, at-property, closing), proving
  monotonicity statements to carry each property along. Many large proofs are transport lemmas between
  copies of the same structure (names with copy, move, transfer, equality of dependent pairs). By name
  alone, such lemmas carry at least 3.5% of the whole on their own (a lower bound: only the 200,000
  largest units were scanned, and many transport proofs have other names). The earlier proof-shrinking
  work found the same pattern among the largest single proofs.
- **Why it looks cheaper.** If the strongest parameter choice can be fixed at the start, each property
  is proved once and nothing has to be moved. Mathematically the stages look like bookkeeping, not
  content.
- **What to check.** Whether the staging is forced (for example, a later stage depends on numbers
  produced by an earlier one, so it cannot be fixed in advance). Read `GlobalTheory.Glob.open_and_linked_of_stronger_extension_alt`
  and the definitions of the extension stages.
- **Risk.** Medium. Partly a proof-engineering question, but a redesign at this level changes the
  statements, so it is mathematical work on the interface.
- **Tested 2026-11-22: not feasible as proposed.** The description above merged two different things.
  - At the top level the proof already does what is proposed. Every parameter depends on one number
    that is obtained first; each named stage only adds a condition (a subfamily), and properties are
    inherited through one generic lemma. All of it weighs 24,234 nodes (0.001%).
  - The costly moves are inside the proof that members exist, and there the order is forced. A member
    is built in two passes: an untwisted one, then a twisted one over a larger coefficient field. The
    twist (auxiliary primes, an exponent, a character) is chosen from the Hecke forms of the first-pass
    member, and the new field must contain roots of unity fixed by that choice; so the data of the
    first pass has to be carried over to the second.
  - Measured by the shape of the statement (the conclusion repeats a hypothesis for a related object),
    transport is 1.9% of the cone now (3.1% at the baseline: the earlier proof-shrinking already took
    42% of its gains from this family), half of it in 70 theorems.
  - Why there are so many copies: types are indexed by a record of about 150 fields that includes the
    coefficient field, so enlarging the field gives a new type for the same object; two runs of a
    construction are related only by records of equations (up to 75 of them); and the hypothesis list
    speaks of arbitrary bundles tied to the constructed data by such records (`TwArgs`, with its
    equation between two 12-tuples).
  - What is left here is smaller: restating `TwArgs` so that its tuple is a definition and not a field
    with an equation (about 0.2%); the largest proofs of the family that have not been rewritten yet
    (`lam_copy`, 5.5 million nodes, is the largest declaration in the cone); and one open variant, a
    single coefficient field for both passes, which needs the numbers of the second pass to be bounded
    before the first (ceiling about 1.1%).

### Candidate 3. The Galois representations, in full generality — 6.1%

- **What it is.** Line D proves a general theorem (all polarized regular algebraic cuspidal
  representations of GL_a over CM fields, with local–global compatibility). It is used by VWin (for
  automorphy arguments) and by the definite side (through two fields of the open-literature bundle,
  which receive the same statement twice).
- **Why it might be cheaper.** If some users only apply it to representations built from Hecke
  characters (theta lifts of characters, CM-type), the needed representations are sums of induced
  representations of algebraic Hecke characters, which come from class field theory, already in the tree.
- **What to check.** Every use of the projections of `Row0b` and of its two copies in the
  open-literature bundle; for each, which π it is applied to.
- **Risk.** High. VWin's automorphy-lifting arguments very likely need the general theorem, and then
  line D stays. I could not tell how much a split would save.
- **Tested 2026-11-22: not feasible.** Every place where the theorem is applied was read. On the VWin
  side it is used for any CM field, any rank and any polarized regular algebraic cuspidal π (the
  lemmas of the automorphy-lifting framework are stated for all π), and for base changes of arbitrary
  Hilbert modular forms. On the definite side it is used for every cuspidal constituent of the base
  change of an arbitrary automorphic representation of a definite unitary group, in ranks up to about
  x^4.5. Only one call is a special case (rank 1, a Hecke character). All parts of the conclusion are
  used, including the statements at places above ℓ. No narrower statement covers the uses.

### Candidate 4. VWin — 8.2%

- **What it is.** Line C, the strong vanishing statement for Galois cohomology of Tate twists.
- **Why it might be cheaper.** The bound it proves is weak in absolute terms (exp(x^ε)^{1/2} on a
  weighted sum of lengths), and the remark says the author expected slack. A route through the
  Iwasawa main conjecture for abelian fields (Mazur–Wiles, Rubin) and bounds for special values is the
  obvious thing to look at.
- **Why I doubt it.** The fields have degree about x^2 and conductors with log d about Y^{ε/5}; the
  twists go up to x^{401}. The size of the full groups, as predicted by special values of zeta
  functions, would be far beyond exp(x^ε). So most of these groups must be trivial, which is a
  Vandiver-type statement and not a size bound. I found no shorter route.
- **What to check.** Which (ℓ, e, E) actually occur downstream (the supply step uses it only through
  `UpperTheory.Top.supplyChi` with a fixed constant 401); whether a smaller range of twists would do.
- **Risk.** High. Listed because of its size, not because I see a route.
- **Tested 2026-11-22: not feasible as a narrowing.** The bound is consumed in one place
  (`divinN_of_hypV`), through a bound on congruence modules: the lifted Galois representation contains
  t consecutive Tate twists of one character, and the congruence quotient is bounded by one
  cohomology group per difference of twists. So every twist 1 ≤ e < t is used, with t about x^399
  (the rank gap of the theta tower), at every prime including 2. The bound itself has room (the
  square root is thrown away), but the proof gives no more cheaply for a weaker bound, and it is
  uniform in t, so a smaller range would remove none of its parts. Shrinking t would mean redesigning
  the parameters of the family.

### Candidate 5. Restatement chains and doubled inputs — small, but certain

- **What it is.** Many blocks are towers of restatements with one child each: five levels in line C
  (ranks 2–6), six in the open-orbit chain, five in the norm-link chain, four in the covolume chain.
  The open-literature bundle has two fields with the same statement. There are two independent proofs of
  the segment representation theorem for real groups (in `CompanionTheory` and in `PositivityTheory`)
  and two different formulations of "theta integrals agree" and "local matching".
- **Gain.** Little written-out size (the restatements themselves are thin), but a large gain in
  readability: the four lines of section 2 would each read as one statement with one proof.
- **What to check.** That the restated forms are equal or one implies the other trivially.
- **Risk.** Low.

### Candidate 6. Replacing heavy literature by a citation of a smaller statement — up to 8.4% in all

- **What it is.** The 350 named published results. Each is at most about 1%; all together 8.4%.
- **Why it might be cheaper.** Some are proved in much more generality than used (for example,
  Harish-Chandra finiteness for all K-types, toroidal compactifications for all PEL data). A narrower
  statement may have a short proof.
- **What to check.** For each heavy entry of section 3, the consumers and the special case they need.
- **Risk.** Low risk of being wrong, low gain per item. Rows 1, 2, 6, 13 and 15 of section 3 are inside
  candidate 1; do not count them twice.

---

## 5. What I could not determine

- The precise mathematical meaning of most internal predicates on the definite side ("rows", "slots",
  "linked at", "members", the forty fields of the hypothesis list). I described them by role, not by
  content. A real map of section 2.A needs a reading of the definitions in
  `Development.AbelianVarietyTheory.Definitions.GlobalTwisting` and the `Formalism.L2` namespace.
- Whether every field of the hypothesis list (`GlobalTheory.Fc.Hyps`) is used by the shape theorem
  (`UpperTheory.Top.shapeWin`). An unused field would be pure cost.
- Where the 18.3% shared pool under spine 6 and the 16% shared pool under spine 4 go: they are spread
  over thousands of small pieces (the folder named for divisors alone has 4,433 entry points). Shares of
  a shared pool cannot be assigned to one line without choosing a rule.
- How strong the main term of the covolume bound must be (candidate 1), and whether VWin is needed in
  its full range of twists (candidate 4).
- Whether the counting (determinant) argument itself has slack: it lives in `Formalism` (13.6% of the
  whole), and I read only its interface, not its proof.
- The exact reference for a few known statements (row 14 of section 3).
