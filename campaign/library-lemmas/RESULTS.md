# Lemmas at library level

Measured 2026-11-22 on the accepted state of change 43 (cone: 1,255,860 declarations, 2,682,394,619 nodes,
175,770,081 tokens).

## What was measured

A theorem whose **statement mentions no declaration of the archive**, only Mathlib and Lean, is a lemma at
library level: it could be stated, proved and checked with Mathlib alone. The archive proves a great many of
these for itself.

| | Theorems | Proof size (nodes) | Source tokens |
|---|---:|---:|---:|
| Theorems in the cone | 1,066,151 | | |
| Statement in Mathlib terms only | 289,990 | 254,481,770 (9.49% of the cone) | |
| … of which helper lemmas made by tactics | 197,301 | 69,461,888 | |
| … of which written theorems | **92,689** | **185,019,882 (6.90%)** | **21,480,859 (12.2% of the source)** |

Written theorems by size of proof:

| Proof size | Theorems | Nodes | Tokens |
|---|---:|---:|---:|
| under 200 nodes | 12,927 | 1,020,900 | 728,322 |
| 200 to 1,000 | 34,439 | 18,639,335 | 3,591,686 |
| 1,000 to 5,000 | 36,564 | 83,939,618 | 10,115,921 |
| 5,000 to 25,000 | 8,564 | 73,600,843 | 6,707,969 |
| over 25,000 | 195 | 7,819,186 | 336,961 |

More than half of the nodes are in `Development.AbelianVarietyTheory` (95.7 million). The largest single ones
are explicit identities and estimates of 70,000 to 150,000 nodes; several of them exist twice under two names.

`python3 tools/try_auto.py find --out build/auto/targets.json --min-nodes 1000` lists the 46,099 with a proof of
1,000 nodes or more (167,986,697 nodes, in 26,120 files).

## Two cheap ways to shrink them, both tested, both negligible

1. **They are not copies of library theorems.** The statements of all 489,292 theorems in Mathlib, its
   dependencies and Lean's library were hashed the same way as the archive's (`tools/moddump`). Only 139 written
   theorems of the cone state, term for term, what a library theorem states (31,226 nodes, 6,286 tokens). So
   these lemmas are the archive's own results, in library vocabulary.
2. **One call of standard automation does not prove them.** `tools/try_auto.py run` takes the statement of an
   existing theorem and tries eighteen closing tactics on it (`simp`, `norm_num`, `omega`, `linarith`,
   `nlinarith`, `positivity`, `ring`, `aesop`, `grind`, `exact?`, …), each with a small budget, counting a proof
   only if it mentions nothing of the archive. On a random sample of 600 of the 46,099: four were closed (0.7%),
   three of them with a smaller proof, saving 3,737 of 2,316,498 nodes (0.16%).

   A first run of this test reported 78%. It was wrong: the file of the theorem is imported to read its
   statement, so the library search found the theorem itself. The rule "nothing of the archive in the new proof"
   was added after that.

## What this means

- One eighth of the source is self-contained mathematics over Mathlib. Each of these theorems is a closed
  problem: a statement in Mathlib terms, a known proof, and a measure of its size. Nothing about the rest of the
  archive has to be understood to work on one.
- They do not fall to search or to one tactic; shortening them means proving them again, better. A community
  challenge on five classical blocks of this archive (zero-free regions, an explicit formula, Siegel–Walfisz,
  Chebotarev over ℚ, resolution of singularities; see riemann.verifytask.cn) reports proofs 1.5 to 13 times
  shorter in tokens after such rewriting. Those texts are not licensed for reuse yet and are built on a newer Lean,
  so nothing of them is used here; they show what the margin is.
- For this drive the class is too large to rewrite by hand in one go (46,099 theorems with proofs over 1,000
  nodes). It is the natural place for many hands: the list is a ready-made set of independent tasks, and
  `tools/judge.py` scores any answer.
