# Proof-shrink campaign: results

## Pilot, 2026-11-21

Three workers, one kind of heavy proof each, at most 8 compile runs per worker.

| Theorem | Written-out size | Source tokens (file) | Compile time (file) | Outcome |
|---|---|---|---|---|
| `GlobalTheory.TwistChoice.same_basic` | 2,135,624 → 15,402 | 3,884 → 3,675 | 96.1 s → 88.4 s | recorded |
| `…Mult1.PG_mul_PG` | 125,103 → 38,313 | 5,500 → 5,488 (both) | 16.6 s → 16.9 s | recorded |
| `…Mult1.PG_conjTranspose` | 101,799 → 48,455 | (same file) | (same file) | recorded |
| `GlobalTheory.HeightCounting.SideCopy.sigSpan_copy` | 4,598,742 → 18,458 | 1,709 → 2,325 (+616) | 79.6 s → 8.5 s | recorded 2026-11-22 under the trade rule agreed after the pilot |
| `GlobalTheory.TwistChoice.fullRk_basisOf_transfer` | 2,328,340, unchanged | unchanged | — | not finished: same method as `same_basic`, ran out of runs |
| `PositivityTheory.Rg.BcB.F.F0.wEx_of` | 801,744, unchanged | unchanged | — | no gain: size comes from definitions |
| `GlobalTheory.TwistChoice.goodTw_transfer` | 2,509,854, unchanged | unchanged | — | not attempted: goal uses most fields |
| `…SideCopy.LamCopy.lam_copy` | 5,538,772, unchanged | unchanged | — | not attempted |

Recorded so far, against the unmodified archive: source size −227 tokens, written-out size −2,260,356 nodes.

## Wave 2, 2026-11-22

Four workers on the same kind of proof (large structures taken apart), now allowed to add helper lemmas and
to use the trade rule (source may rise if the written-out size falls by at least 1,000 nodes per token).

| Theorem | Written-out size | Source tokens (file) | Compile time (file) | Outcome |
|---|---|---|---|---|
| nine transfer theorems in `…InertiaEigenvalues.IsClassSystem` | file 2,488,882 → 499,081 | +777 | 131 s → 79 s | recorded (one shared helper, `SameGeo.transfer`) |
| `…SymmetryOfAgreementRelations.move_xd` | 2,036,015 → 25,369 | 3,943 → 3,956 (both) | 45.8 s → 10.1 s | recorded |
| `…SymmetryOfAgreementRelations.move_pack` | 758,884 → 4,565 | (same file) | (same file) | recorded |
| `GlobalTheory.HeightCounting.Rigid.transfer` | 1,185,477 → 40,837 | 1,679 → 2,034 | 28.5 s → 7.8 s | recorded |
| `GlobalTheory.TwInputs.Move.heckeTie_of_same` | 2,307,263 → 732,218 | 1,738 → 1,762 | 57.9 s → 22.5 s | recorded |
| `…ListCarry.listPin_copy` | 1,456,568 → 839,370 | 2,886 → 2,819 | 48.6 s → 39.9 s | recorded |
| `GlobalTheory.TwistChoice.fullRk_basisOf_transfer` | 2,328,340 → 7,419, plus a helper of 16,959 | 3,675 → 4,221 | 194.9 s → 163.2 s | recorded |
| `GlobalTheory.TwistChoice.goodTw_transfer` | 2,509,854, unchanged | unchanged | — | not attempted: the size is in the statement once unfolded |

Judged in two groups. The nine `IsClassSystem` proofs with `sigSpan_copy`: source +1,389 tokens, written-out
size −6,570,085 nodes, time on the two files 244.7 s → 71.5 s. The other five files: source +871 tokens,
written-out size −8,405,810 nodes, time 375.6 s → 221.6 s.

Techniques added by this wave:

- When `generalize` cannot be used because the goal reaches the structure through a definition that takes
  the whole structure as an argument: state a local `key` that quantifies over one side only, with the
  definition written out and the equalities as hypotheses; `subst` then replaces fresh variables by concrete
  projections.
- A helper of the form "for every predicate Ψ over the fields, equalities → Ψ (one side) → Ψ (other side)",
  proved by one chain of `subst`. Because Ψ is a variable, each substitution rewrites only a small term.
  Apply it to `fun … => goal`, elaborating the application with `have k := …` before `exact k h`.
- Copy, do not take apart: `obtain ⟨D₁, hD⟩ : ∃ D₁, D' = D₁ := ⟨_, rfl⟩`, move the equalities onto the copy,
  take the copy apart, substitute, and carry the large hypotheses across with one final `subst hD`.
- Take hypotheses apart only just before the step that needs their parts, so earlier substitutions do not
  restate them.

## Wave 3, 2026-11-22

Four workers. Checks ran on a rented machine (one to five minutes each instead of a quarter of an hour), so a
worker finished in 15 to 25 minutes.

| Theorem | Written-out size | Source tokens | Compile time (file) | Outcome |
|---|---|---|---|---|
| `GlobalTheory.TwInputs.Move.Forms.record_heq` | 750,091 → 50,054 | 754 → 1,330 | 41.4 s → 11.6 s (file) | recorded |
| `GlobalTheory.TwInputs.Move.Forms.exists_sameVec` | 215,910 → 10,458 | 232 → 387 | (same file) | recorded |
| `GlobalTheory.simpleU_rev_and_sq` | 219,684 → 5,131 | 275 → 222 (file) | 9.3 s → 1.0 s | recorded |
| `Formalism.UG.P.fIwasawa_perm` | 252,521 → 15,874 | 2,241 → 2,289 (file) | 28.6 s → 5.9 s | recorded |
| `PositivityTheory.Rg.BcB.F.BC.limAtOf_holds` | 831,837 → 831,795 | −6 | unchanged within tolerance | recorded, but no real gain: 98% of the size is the statement of a six-deep `choose_spec` chain |
| `GlobalTheory.TwInputs.Move.exists_restX`, `exists_restY` | unchanged | −106 (file) | unchanged | recorded: source only (`subst a b c` in one call) |
| `GlobalTheory.T.geo_heq_geoHalf_of_same` | 235,821, unchanged | unchanged | — | no gain: one attempt hit the heartbeat limit, the other grew the proof; restored |
| `GlobalTheory.ColRows.rowsU_of_colPins_alt`, `GlobalTheory.Mem.KeepRef.exists_thPW_keep` | | | | worker still running at the time of writing |

The five recorded files together: source +614 tokens, written-out size −1,356,731 nodes, time 252.9 s → 196.8 s.

Techniques added by this wave:

- Word the equalities of a local `key` so that `subst` removes the fresh variable: put the fresh variable on
  the right (`HEq V' W`) and pass `h.symm`. Otherwise `subst` removes the outer variable and drags its
  dependents along.
- `intros; subst_vars` handles `HEq` hypotheses as well and replaces long `fun e1 … e23 => by subst e1 … e23`.
- For `split_ifs` on compositions of `Equiv.swap` proving `π (f i) = f (π i)` with `f` injective: use
  `Function.Injective.swap_apply` and commutation from `Equiv.Perm.disjoint_swap_swap`. No case split is
  needed. Prove fixed points with `rw [Equiv.swap_apply_of_ne_of_ne (x := i), …] <;> omega`.
- Inside a `subst` chain, do not `intro` dependent binders early: something a `subst` reverts costs about
  twice as much as a hypothesis than as a binder still in the goal.
- A way to find where the size is: copies of the theorem with `sorry` in place of all bullets but one. If the
  copy with every bullet replaced is already most of the size, the size is in the statement and the
  definitions it unfolds to, and no proof edit will help.

Open lever found by this wave: the six-deep `choose_spec` chain behind `limAtOf_holds` is rebuilt in at
least three other files (`ClsFin`, `AllLeavesMono`, `PreEquivSymm`). One helper stating the whole
conjunction once, next to the definitions, would let all four share it.

## Wave 4, 2026-11-22

Four workers, checks on the rented machine.

| Theorem | Written-out size | Source tokens (file) | Outcome |
|---|---|---|---|
| `rl_ktypes`, `rl_levels` (two identical copies each, in `PreEquivSymm` and `ClsFin`), `limAtOf_holds` | 797,334 / 796,980 / 831,795 → 9,002 / 9,192 / 45,406 | +1,206 over four files, of which +1,203 is the new shared statement | recorded: one shared statement `rl_spec` next to the definitions, proved through a generic `ex6_spec` |
| `Qj20.Hpk_sq` | 202,413 → 33,774 | +24 | recorded |
| `MatrixMultiplicationContinuity.hpk_sq_lemma` | 178,382 → 33,774 | +90 | recorded |
| `B2x2.hpk_unit` | 177,993 → 370 | −209 | recorded |
| `PI.MirrorSection₂.hpk_sq` | 163,761 → 33,774 | +116 | recorded |
| `PI.SwBig.BigCellGProof.Hpk_rhoB` | 162,416 → 29,957 | +91 | recorded |
| `GlobalTheory.Mem.R3.Ext.lawsJ_enl` | 198,135 → 104,408 | −151 | recorded |
| `…FwBase.coreBaseFrames_eq_modelFrames_enlargedCoefficientBase` | 183,461 → 130,175 | −925 | recorded |
| `hc_count` | 218,057 → 90,234 plus two helpers of 4,191 and 5,299 | +75 | recorded |
| `GlobalTheory.RootSumDual.rootSum_dual_edges` | 195,752 → 130,309 | −9 | recorded |
| `GlobalTheory.LayerMove.exists_nonempty_nMore_upL` | 477,164 → 357,527 | +57 | recorded |
| `UpperTheory.cusp_sections_over_coefficient_extension` | 299,398, unchanged | unchanged | no gain: the nine field substitutions are needed for the closing step; restored |
| `PositivityTheory.Rg.BcB.F.F0.wEx_of` | 808,132 → 22,687 | +199 over three files | recorded: `ex6_spec` moved to a file this one imports, used through a small companion `ex6_imp` |

The shared statement was judged on its own: source +1,203 tokens, written-out size −3,922,255 nodes. The nine
files of the matrix lemmas and the four mixed proofs together: source −898 tokens, written-out size −1,084,105 nodes, time 129.9 s → 75.1 s.

Techniques added by this wave:

- **A chain of `choose_spec` over a large statement.** `h.choose_spec.choose_spec.…` restates the whole
  statement at every level. Prove the chain once over an abstract predicate
  (`ex6_spec : (h : ∃ a b c d e f, p a b c d e f) → p h.choose h.choose_spec.choose …`), then apply it to the
  concrete `h`: the large statement appears once. A direct proof of the shared statement was 613,795 nodes;
  through the generic lemma it is 14,935.
- **A matrix with one nonzero entry per row.** Do not expand a product entry by entry with `split_ifs`. First
  prove the row form `M i j = if j = σ i then c i else 0` for an explicit involution `σ` (one small case
  split), then the product is `simp only [Matrix.mul_apply, …, Fintype.sum_ite_eq']` and a two-case finish.
- **Before `split_ifs`,** simplify with the hypothesis that makes many conditions false
  (`simp only [h, false_and, and_false, false_or, if_false]`); conditions written differently often become
  the same one. When a case analysis on a defined value feeds one large `omega`, move it into a small lemma
  stating the value as an `if`, and rewrite with it.
- **Before a chain of `subst`,** clear every hypothesis the goal does not need, and `generalize` projections
  early so that their parent structures can be cleared. When large hypotheses mention the structure being
  taken apart, `generalize ht : t' = t1 at <goal and the needed facts>`, take `t1` apart, and carry the large
  hypotheses across with one final `subst ht`.
- **Checker behaviour:** `simp only [D]` on a definition from another file creates the equation lemma
  `D.eq_1` in the current file, which other compiled files may refer to; `unfold D` does not. Keep whichever
  the original proof used, or the equivalence check will refuse the change.

## Wave 5, 2026-11-22

Four workers on the proofs whose expansion is most out of proportion to their source.

| Theorem | Written-out size | Source tokens (file) | Outcome |
|---|---|---|---|
| `Formalism.L2.SG.Pf.CarrierXAll.ac_le` | 1,407,238 → 11,849 | −288 | recorded |
| `GlobalTheory.MomNum.mom_num` | 574,846 → 14,082 | −38 | recorded |
| `…EtaleIntegralityFacts.Lim.ampLimit` | 2,167,843 → 18,471 | +84 for all three | recorded |
| `…EtaleIntegralityFacts.Lim.diff_key` | 1,526,913 → 14,934 | (same file) | recorded |
| `…EtaleIntegralityFacts.Lim.diff_bound` | 408,773 → 2,695 | (same file) | recorded |
| `GlobalTheory.ArcOfPoint.exists_arcIn_of_unif` | 500,408 → 92,251 | +12 | recorded |
| `PositivityTheory.RgHe.A.Pf.bigProjP_of` | 457,279 → 60,796 | +32 | recorded |
| `GlobalTheory.TopVal.TwSet.lev_twArgs` | 855,125 → 417,638 | −41 | recorded |
| `UpperTheory.V.Ws.X1.bor1` | 167,440 → 22,274 | +41 | recorded |
| `case1`, `case2` in `MixFlagExists` | 160,707 → 110,330 and 162,790 → 110,358 | +24 | recorded |

What these had in common: **an arithmetic tactic multiplying out a power.** `ring`, `linarith` and `nlinarith`
expand any power of a sum they can see, and they see through names introduced by `set`. One power of degree 19
cost over a million nodes.

- Keep the base as one symbol: `generalize 2 * r + k + 1 = n` at the natural-number level before casting, or
  `generalize x ^ (67 * (n + 1) ^ 2) = A` before `ring`. Do not `push_cast` the cast of a sum that is raised
  to a power.
- After `set x := e with hx`, add `clear_value x` when `e` contains a power, so that later `ring`/`linarith`
  calls treat `x` as a plain variable. Prove the few facts that need the value once, with `rw [hx]`.
  `set … with hx` also leaves `hx` in context for every `linarith`; `generalize` does not.
- A large structure value built inline in `refine ⟨{ … }, ?_⟩` is written out once for every later goal that
  mentions it. Bind it once: `refine let a : T := { … }; ⟨a, ?_⟩`.
- To find the heavy step in a long proof: scratch copies of the theorem cut after each block, one run.
- `fin_cases` is expensive written out. Splitting `Fin n` on the natural-number value with
  `rintro ⟨_ | _ | _ | i, hi⟩` and closing with `rfl`, `omega` or `absurd h (by simp)` was about three times
  smaller on a 4×4 matrix.
- A structure with an equation among its fields: `have pack := a.pack; generalize a.x = x at pack ⊢; cases x;
  cases pack` instead of `cases a`, so the other fields are never restated.

## Wave 6, 2026-11-22

Four workers: one lead on a family of 24 proofs that all run `cases pack` on the same structure, three on
ten more proofs whose expansion is out of proportion to their source. One older worker reported back.

| Theorem | Written-out size | Source tokens (file) | Outcome |
|---|---|---|---|
| `…Rw.EqvMove.equivAll_enl` | 967,767 → 254,658 | −113 | recorded |
| `…Move.SetupRel.good_of` | 964,736 → 2,166 | +311 for both | recorded |
| `…Move.exists_setupRel` | 771,276 → 879, plus shared `setupRel_move` 590,799 | (same file) | recorded |
| `UpperTheory.geometric_action_over_coefficient_extension` | 741,655 → 203,248 | +248 | recorded |
| `GlobalTheory.Reg.exists_scharts_of_covers` | 569,393 → 147,321 | +10 | recorded |
| `GlobalTheory.ksForm_moved` | 473,861 → 149,167 | +74 | recorded |
| `…Move.CopyTw.exists_rest` | 491,356 → 186,666 | −20 | recorded |
| `…T.referenceTuple_rationalForm_lifts_algebraic_enlarged` | 398,876 → 72,006 | −76 | recorded |
| `GlobalTheory.T.modW_of_rSideW` | 378,300 → 45,775 | −94 | recorded |
| `PositivityTheory.HtPt.Kftwo.exists_pairHost` | 461,774 → 38,668, plus four helpers | +204 | recorded |
| 16 of the 24 `cases pack` proofs | 12,548,424 → 179,597, plus shared `TwArgs.pack_elim` 384,142 | −667 | recorded |
| `row_of_pack` (same family; its file cannot see the shared lemma) | 210,224 → 195,883 | −27 | recorded |
| `GlobalTheory.ColRows.rowsU_of_colPins_alt` | 485,546 | | no version compiled in time |
| `GlobalTheory.Mem.KeepRef.exists_thPW_keep` | 269,326 | | no gain |

What these had in common: **long conjunctions and records taken apart one level at a time.**

- `obtain ⟨-, -, …, h, -⟩ := H` on a conjunction of 14 or 19 parts is written out as one case split per
  part, and every level restates what is left of the conjunction, one binder deeper, so nothing is shared.
  It cost 300,000–400,000 nodes each time it appeared. Read the parts instead: by projection, written where
  the part is used (`H.2.2.1`; all at one depth, so shared), or through a small generic lemma over
  propositions (`pick14 : a ∧ … ∧ n → (c → j → P) → P`). Pulling parts out with one `have` each also works
  but is larger than using them in place.
- Take parts out late. A hypothesis whose type is a folded definition (`RSide z W R`) costs almost nothing
  each time a `subst` restates it; its fifty unfolded parts do not. For the same reason keep a bundled
  hypothesis whole until the step that needs it.
- Two records related field by field (the macros `geo_cases`, `set_cases`, `copy_cases`): take only one of
  them apart and replace its fresh fields by the other's projections. Theorems that repeat the same
  destructuring can share one lemma that states all their conclusions as a conjunction.
- Many substitutions into a large context: do them in a sub-proof that begins with `clear * - needed` and
  proves `∃ fresh…, x = ⟨…⟩`, then substitute that one equation outside.
- A long tactic proof inside a field of a structure literal (a `RingHom`) is copied into the goals of the
  fields after it. Move it to a top-level lemma.
- A structure literal mentioned in later goals: `refine let S : T := { … }; ⟨S, ?_, ?_⟩` (as in wave 5).
- A structure field that is an equation between dependent tuples (`pack`): one eliminator over the tuple's
  components, proved without `cases` as `(congrArg (fun s => motive s.1 s.2.1 …) a.pack).mpr h`. A user then
  restates its goal once instead of once per component: sixteen proofs went from 12.5 million nodes to
  179,597, and their files compile in half the time (1,236 s → 604 s).
  The lemma needs Lean's `@[elab_as_elim]` tag so that users need not write the motive; that adds an entry to
  one of the registers the equivalence check watches, and that was the judge's only objection. A tag on a
  lemma that the change itself adds has been allowed since 2026-11-22, and the change is recorded.
- Using that eliminator: bring the goal to the fields of `a.x` first (`cases ax`, or `rw [← eq_of_heq w.ax]`),
  delete the destructuring, then `exact a.pack_elim <tail>` or `refine a.pack_elim ?_`. Any other field of
  `a.x` that the goal or the tail needs has to be generalized first, together with the `HEq` hypotheses that
  mention it (`have h := a.tup; revert h; generalize a.x.Y = Y; revert Y; refine a.pack_elim ?_; intro Y h`),
  or the motive is not type-correct. Seven of the 24 did not go through; the reasons are in `attempted.tsv`.
- A second eliminator of the same kind for another structure, with two users, bought 574 nodes per token and
  was left out: a helper has to pay for itself.

What did not work, and why:

- `rowsU_of_colPins_alt`: stating a compact goal first and substituting in one step is sound, but taking the
  structures apart afterwards took over 20 minutes of compiler time, because the context then holds fourteen
  equations whose types mention the structure literal. The other order (take apart first) was not tried.
- `exists_thPW_keep`: the size is in `choose … using key`, which splits off sixteen pieces and restates the
  remaining existence statement at each step with the new functions put in. Restating the goal costs
  nothing: the size is counted after identical subterms are merged, so only terms that are new count.

For every proof here the statement alone was under 25,000 nodes: the size was in the steps.

## Wave 7, 2026-11-22

Four workers on 22 proofs of 119,000 to 353,000 nodes. Seventeen got smaller, five did not.

| Theorem | Written-out size | Outcome |
|---|---|---|
| `…SelC.args_pinned_heq_zsOf_mem_eq` | 352,727 → 13,027 | recorded |
| `…T.referenceTuple_weilDatum_vector_polynomialMap_enlarged` | 330,830 → 46,330 | recorded |
| `…LiftExt.liftAt_of_rSide` | 321,388 → 52,287 | recorded |
| `…T.referenceTuple_hilbertModel_definiteForms_enlarged` | 281,143 → 46,679 | recorded |
| `GlobalTheory.FinGL.Mir.dm_perm` | 241,342 → 210,851 | recorded |
| `…Move.exists_restX`, `exists_restY` | 223,799 → 110,157; 156,029 → 77,558 | recorded |
| `…SerCopy.series_copy_embedding_alt` | 198,971 → 136,883 | recorded |
| `…JmtUp.jMt_rowsSame` | 198,626 → 135,120 | recorded |
| `UpperTheory.pointEquiv_family_transport_of_same_pre` | 193,948 → 176,889 | recorded |
| `…GeoTies.BarAtOne.congr` | 192,874 → 75,528 | recorded |
| `Formalism.L2.Th1.A.flowTranslation` | 147,012 → 26,975 | recorded |
| `…RowEx.Jet.jets_congr` | 143,254 → 99,197 | recorded |
| `…R2.exists_ratGL_dM`, `exists_ratGL_aE` | 138,328 → 2,446; 134,084 → 2,455 | recorded |
| `PI.OneCosetSharp.W.C2.ent_unit`, `ent_τ0` | 128,421 → 58,721; 118,893 → 53,982 | recorded |
| `…Rw.Up.rxs_up` | 320,472 → 160,970, but compile 33.0 s → 54.0 s | refused on time, restored |
| `GlobalTheory.ModelIndep.datIndep` | 207,115 → 74,126, but compile 6.9 s → 11.2 s | refused on time, restored |
| `…SelC.pack_heq` | 292,019 | no gain: the size is in the statement |
| `…LiftExt.thetaLift_of`, `postLift_of` | 146,005; 145,030 | no gain |

What was new:

- **Structure literals hiding in instance arguments.** After `obtain` on a structure with instance fields,
  `dsimp only at *` does not look inside instance arguments, so hypotheses keep the whole structure
  literal there and every `subst` restates it. `dsimp +instances only at *` halved two proofs with dozens
  of substitutions.
- **Projecting a lemma applied to large literals.** `(lemma …).1` writes the lemma's statement, with the
  literals put in and nothing reduced, into the arguments of the projection. Give the lemma once to
  something that already has the expected type (`refine And.imp_right … ?_` and then the lemma). One proof
  went from 352,727 to 13,027 nodes this way.
- **A large fact built too early.** A `have` built from a variable that is taken apart later is restated
  by each case split and substitution. Build it after them, from the fresh fields.
- **`omega` and case splits.** Drop unused facts that contain truncated subtraction before `omega` runs:
  each one doubles its case splits whether or not it matters. With two three-way facts, split on one and
  hand the other to `omega` whole.
- **2×2 matrices.** `Matrix.mul_fin_two`, `Matrix.one_fin_two`, `Matrix.eta_fin_two` and one `simp`
  instead of `fin_cases` on both indices with a `simp` in each case: about 55 times smaller.
- **A certificate by hand.** Where `linear_combination` would cube a polynomial value, name the value with
  an equation (`obtain ⟨N, hN⟩ : ∃ N, e = N := ⟨_, rfl⟩`) and add the term for `hN` to the certificate.

What stopped the rest:

- **Time.** Two proofs lost half or more of their size by reading fields in place instead of taking the
  record apart, and then compiled much slower, because Lean has to see through large literals to check
  the result. The time dial refused them. Size and time pull against each other in this family.
- **The statement.** `pack_heq` is 292,019 nodes, and a copy of it proved by `sorry` is already 247,650:
  a large dependent-tuple type appears at several binder depths in the statement itself.
- **A macro.** `thetaLift_of` and `postLift_of` spend their size in a macro that takes two related records
  apart; a shared eliminator does not typecheck there because the two records are equal only after every
  definition is unfolded.

## Wave 8, 2026-11-22

One proof, the largest declaration in the cone.

| Theorem | Written-out size | Source | Compile time | Outcome |
|---|---|---|---|---|
| `GlobalTheory.HeightCounting.SideCopy.LamCopy.lam_copy` | 5,538,772 → 29,829 | +1,240 tokens (4,443 nodes per token) | 108.0 s → 2.7 s | recorded |

It moves a statement from one family datum to a copy of it, and ran the macro `copy_cases`: two records
of about 150 fields taken apart, dozens of equations substituted one by one, each restating the whole
goal. The new proof follows `sigSpan_copy`: state the property once in terms of the 29 components it
really mentions, prove it for any components equal to those of the first datum (the substitutions happen
there, with nothing large in scope), and apply that to the components of the copy. `copy_cases` has no
users left.

What was new compared with `sigSpan_copy`:

- **Bind the generic statement with a local `let`.** Each substitution then restates only the name applied
  to the components. With the statement left in the goal the proof was 79,141 nodes, with the `let` 30,924.
- **State the conclusion as a continuation** (`∀ G, (∀ w c chi, A → … → E → G) → G`) and not as an
  existential with a conjunction: nothing has to be taken apart on one side and rebuilt on the other
  (43,367 → 34,934).
- **`And.imp_right (Exists.imp fun v => And.imp_left …)`** under binders in place of anonymous
  constructors (34,934 → 30,924).
- **Make the components implicit arguments of the local lemma**: the equality proofs determine them.
- Components that are tied by a relation and not by an equation become extra variables with the relation
  as a hypothesis; components that are proofs need no equation at all.

## Bulk sweeps, 2026-11-22

The hand-made waves work on the largest proofs. Those are not where most of the size is:

| Proofs with a written-out proof of | Proofs | Share of the cone |
|---|---:|---:|
| 300,000 nodes or more | 40 | 1.2% |
| 100,000 to 300,000 | 325 | 1.6% |
| 30,000 to 100,000 | 6,288 | 10.3% |
| 10,000 to 30,000 | 38,909 | 22.8% |
| 3,000 to 10,000 | 121,366 | 23.8% |
| 1,000 to 3,000 | 179,925 | 11.7% |
| under 1,000 | 348,798 | 4.7% |

(The rest is statements, 14%, and auxiliary declarations and definitions.) So what the waves found is now
applied by generator wherever it fits (`tools/proof_edits.py`). A least-squares fit of proof size against
how often each tactic is used, over 353,132 proofs, says where to look: `obtain` goes with about 1,270
nodes per use (455,454 uses), `subst` 4,130 (32,822), `cases` 5,100 (7,925), `fin_cases` 2,300 (10,279),
`omega` 660 (102,648); every other source token goes with about 19. Each `obtain` restates the goal once
per level of its pattern.

How a sweep runs: an edit is one line. A file's edits are compiled all together; where that fails, one at
a time, and then the ones that passed alone together. A file is kept only if it compiles to the same
interface, its written-out size does not grow, and one of its two sizes falls, with source counted the
strict way (every projection step a token; if it grows, at least 1,000 nodes per token added).

| Sweep | Files compiled | Files kept | Written-out size | Source tokens |
|---|---:|---:|---:|---:|
| Dropped parts of a pattern skipped by projection (`obtain ⟨-, -, h, -⟩ := H` → `obtain ⟨h, -⟩ := H.2.2`), three rounds down to proofs of 1,000 nodes and patterns of two parts | 10,166 | 6,966 | −14,598,000 | −25,900 |
| Kept parts between dropped ones read by their own projections (costs source on the strict count) | 3,113 | 260 | −3,250,000 | −600 on the dial, +540 strict |
| `clear_value x` after `set x := e with h` where `e` contains a power | 441 | 12 | −93,026 | +32 |
| Citations of a copy written in the one form their proof uses | 6,130 | 6,127 | 0 | −104,029 |
| Deleting `show T` / `change T` lines that only restate the goal (pilot) | 300 | 54 | −4,026 | −1,033 |

- The projection rewrite keeps named parts in a pattern, because a name may be the witness of an existence
  statement, which has no projections. Only a single name that looks like a hypothesis is read as `.1`.
- A hypothesis that `obtain` consumed is cleared after the rewrite, so later steps see the same context.
- One file was left out because a theorem in it grew past the per-declaration cap although its file got
  smaller: the file-level test does not see that; the judge does.
- `clear_value` only pays where an arithmetic tactic multiplies out a power; applied to every `set … with`
  it gained nothing.
- The cone has 81,658 `show`/`change`/bare `dsimp only` lines carrying 1.57 million source tokens, but only
  about one in ten can go: most are needed by the step after them. Not run at scale.

## What the size was made of

- **Taking large structures apart.** `cases` on structures with dozens of fields followed by dozens of
  `subst`s: every `subst` restates the types of everything still in context, so the expansion grows roughly
  with the square of the number of fields. This is what the largest proofs in the cone are. The macro
  `copy_cases` does it wholesale: a 7-token proof expanded to 4.6 million nodes while the statement needed
  14 of about 85 substitutions.
- **Case splits that repeat.** `split_ifs` splitting on the same condition written two ways round.
- **Definitions, not proofs.** Chains like `(h E).choose_spec.choose_spec.….choose` restate a large
  existence statement once per level. Several of the largest items are definitions of this kind
  (`rlΘ₂`: 9 tokens, 1.4 million nodes; 192 such lines in 130 files). Proofs that use them inherit the size.
  Changing them changes what other files see, so it is not a proof-only edit.

## What worked

- Do not destructure. Take the few facts needed with `have`, `generalize` exactly the projections the goal
  mentions (on both sides), `subst` in that small context, close with the original tail. Instances that are
  proofs need no substitution. (`same_basic`: smaller on both sizes.)
- When `generalize` reports "result is not type correct", state the abstract version as a local `have` with
  the equalities as hypotheses and apply it; this avoids syntactic matching. (`sigSpan_copy`: far smaller
  written out, but longer in source.)
- Put `eq_comm` in the `simp only` set before `split_ifs` so equal conditions are written one way round.
- `omega` already knows `i.isLt` for every `Fin.val` it sees; such `have`s can go.

## What this says about the rule

`sigSpan_copy` trades 616 source tokens for 4.58 million nodes and a compile eight times faster. The cone
averages about 15 nodes per token, so this is some 500 times better than the going rate, and it still fails
"no dial may go up". A shared helper lemma for moving facts across `CopyAll` would probably give the same
saving for far fewer tokens, shared by every proof that uses the macro; that needs new declarations, which
the pilot's brief did not allow.

## Cost on this machine

Each compile of a deep file is 10–130 seconds of compiler work but 5–15 minutes of wall time, because
loading its imports means paging in several gigabytes. The pilot's ~20 compiles took about an hour and a half.
