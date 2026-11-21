# Proof-shrink campaign: results

## Pilot, 2026-11-21

Three workers, one kind of heavy proof each, at most 8 compile runs per worker.

| Theorem | Written-out size | Source tokens (file) | Compile time (file) | Outcome |
|---|---|---|---|---|
| `GlobalTheory.TwistChoice.same_basic` | 2,135,624 → 15,402 | 3,884 → 3,675 | 96.1 s → 88.4 s | recorded |
| `…Mult1.PG_mul_PG` | 125,103 → 38,313 | 5,500 → 5,488 (both) | 16.6 s → 16.9 s | recorded |
| `…Mult1.PG_conjTranspose` | 101,799 → 48,455 | (same file) | (same file) | recorded |
| `GlobalTheory.HeightCounting.SideCopy.sigSpan_copy` | 4,598,742 → 18,458 | 1,709 → 2,325 (+616) | 79.6 s → 8.5 s | review: source went up; patch in `review/sigSpan_copy.diff` |
| `GlobalTheory.TwistChoice.fullRk_basisOf_transfer` | 2,328,340, unchanged | unchanged | — | not finished: same method as `same_basic`, ran out of runs |
| `PositivityTheory.Rg.BcB.F.F0.wEx_of` | 801,744, unchanged | unchanged | — | no gain: size comes from definitions |
| `GlobalTheory.TwistChoice.goodTw_transfer` | 2,509,854, unchanged | unchanged | — | not attempted: goal uses most fields |
| `…SideCopy.LamCopy.lam_copy` | 5,538,772, unchanged | unchanged | — | not attempted |

Recorded so far, against the unmodified archive: source size −227 tokens, written-out size −2,260,356 nodes.

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
