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
| `GlobalTheory.ColRows.rowsU_of_colPins_alt`, `GlobalTheory.Mem.KeepRef.exists_thPW_keep` | | | | worker still running |

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
