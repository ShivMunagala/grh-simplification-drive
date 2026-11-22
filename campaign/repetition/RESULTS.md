# Repetition campaign: the same statement, written or proved more than once

## What was measured (2026-11-22, from the tables, about a minute)

The five theorems depend on 696,508 theorems outside Mathlib (not counting compiler-generated helpers).
Grouped by statement they are 597,915 distinct statements. So about 98,600 theorems restate something that
is already there. They fall into four tiers, by how much has to change to remove them.

| Tier | What it is | How many | Written-out size | What it takes |
|---|---|---:|---:|---|
| 1 | Restates another theorem and proves it by citing that theorem | 46,289 | 0.9 million nodes | Turn into an alias: the repeated statement text goes. One file each, no import touched. |
| 2 | Proved independently, and the file already imports a public copy | 10,995 | 15.2 million | Replace the proof by a citation. One file each, no import touched, statement untouched. |
| 3 | Proved independently in a file that cannot see a copy, but importing the copy's file would add nothing except plain theorems and definitions | 9,055 | 12.1 million | One added import per file. Needs a rule for when an added import is invisible to everything else. |
| 4 | Proved independently, and no single import would do | about 30,000 | about 44 million | A shared file that both import, holding one proof that uses only what both already import. |

Tiers 2 to 4 together are 80,617 copies of 28,313 statements; 28,659 of them are the earliest copy and
stay. The independent proofs beyond the earliest weigh about 71 million nodes, 2.6% of the written-out dial.
Tier 1 matters for the source dial: the restated statements are about 4% of all source tokens.

How the groups are found: Lean's own hash of the statement plus its size. That can collide and ignores
argument names, so it only proposes candidates. Every rewrite is compiled, and the equivalence check
compares the statement before and after strictly.

## Tier 1: restating theorems become aliases

`theorem T.x : <statement> := by first | exact @X | …` becomes `alias T.x := X`.

- 36,725 of the restating theorems have exactly the statement of the theorem they cite (hash and size).
  34,430 files were rewritten and compiled on rented machines.
- An alias takes the argument names of the theorem it points to. On a sample of 400, 23 differed from the
  original in argument names (mostly an unnamed hypothesis that gets a name; a few renamed). None differed
  in which arguments are explicit. Any difference is treated as a changed statement and the file is left
  as it was.
- An alias registers the namespaces `GlobalTheory` and `GlobalTheory.T`; the original theorems did not
  (their bodies are added in a separate branch of the compiler, where registrations are dropped). Lean
  reads its namespace list only to resolve `open` and `export`. Every rewritten file already imports a
  module that registers `GlobalTheory`, and no `open` or `export` anywhere in the 175,187 files names `T`
  on its own, so nothing can resolve differently. `tools/nscheck.py` makes this check.
- The index file of an alias has no source range, so the token count takes the range stored in the compiled
  module. Otherwise an alias would count as zero tokens.

- Spot check of the claim that nothing else needs rebuilding: 120 files that import rewritten ones were
  recompiled with the aliases swapped in. All 120 came out identical to their accepted compiled form,
  declaration by declaration, proofs included. A control run on 37 files with nothing swapped in was
  identical too, so a plain recompile is reproducible.

Result, recorded 2026-11-22: 32,172 of the 34,430 rewritten files pass the strict check and are now aliases;
2,258 are left as they were because the alias would rename an argument. Source size −6,501,454 tokens
(3.55% of the dial), written-out size −442 nodes. Time, measured on a random 3,000 of the files before and
after under the same load on the rented machine: 8,143 s → 6,305 s.

Seven of the files make `GlobalTheory` visible for the first time to what imports them (85 files, one of
which did not see it before). None of those 85 opens a namespace of that name, so nothing resolves differently.

Still open in this tier: the 2,258 files with renamed arguments (an alias is only safe there if no user
passes that argument by name; checking that needs their users recompiled), and about 3,000 restating
theorems whose statement is not literally the cited one.

## Tier 2: duplicate proofs become citations

`theorem d <statement> := <long proof>` becomes
`theorem d <statement> := by first | exact @c | exact c | (intros; apply c <;> assumption)`,
where `c` is the earliest public copy the file already imports. This is the form the archive itself uses
in tier 1. The statement is kept character for character.

Trial on the six files with the largest candidates (15 theorems): all six pass the pre-check, and every
dial falls. Four of them:

| File (last part of its name) | Source tokens | Written-out size | Compile time |
|---|---|---|---|
| `RankOneEmbeddings` | 1,970 → 1,677 | 188,807 → 11,739 | 39.8 s → 5.2 s |
| `WuBLReproPf` | 1,775 → 1,352 | 173,987 → 6,954 | 22.1 s → 3.2 s |
| `FrameInvMulVecNegativeVector` | 6,275 → 5,289 | 432,214 → 121,486 | 60.3 s → 16.6 s |
| `DetEqMulMinorOfColZero` | 16,557 → 16,258 | 257,037 → 87,619 | 366.7 s → 156.3 s |

Result of the full run, recorded 2026-11-22: 10,872 theorems in 6,608 files were rewritten and compiled.
6,137 files pass the strict check; 9,729 theorems in them now cite a copy. Source size −360,217 tokens,
written-out size −14,593,193 nodes (both figures include three hand-edited files judged in the same run,
about 685,000 nodes of it). Time, on 272 files timed with old and new version back to back: 2,197.5 s → 2,090.1 s.

What was left out, and why:

- 272 files register something different afterwards. Nearly all are theorems proved by `rfl`: Lean marks
  such a theorem as usable by `dsimp`, and a citation is not marked. The check on registered attributes
  caught this; it would not show in any statement.
- 155 files did not compile (the citation form did not go through for at least one theorem in the file).
- 44 files changed something another file can see.
- 4 files under a directory with a non-ASCII name were skipped by a path-quoting slip in the judge (fixed).

These are per file: one failing theorem keeps the whole file out. A second pass that tries each theorem on
its own is prepared (`tools/proof_edits.py`, `tools/batch_variants.py`).

About 4,700 of the citations replace a proof shorter than the citation itself (18 tokens). The sweep as a
whole still lowers the source size, but those should use the short form `@c` where it compiles, or keep
their original proof. Also prepared (`tools/proof_edits.py shorten`), not yet run.

A first timing of this sweep showed it 61% slower. That was an artifact: the two versions were timed in
separate passes while the machine was unevenly busy. Old and new must be timed back to back in the same job
(`tools/batch_compile.py --paired`).

### Tried and dropped: taking over the shortest proof

For duplicates that cannot cite a copy, replacing the proof text by the text of the shortest proof of the
same statement looked like 15.6 million nodes on paper. On a sample of 60 files only 5 passed. The shortest
proofs are short because they lean on helper lemmas in their own file, which the other file cannot see.

## Tiers 3 and 4

Not started. Tier 3 needs the judge to accept an added import when (a) the importing file already imports
everything the imported file imports, so exactly one module is added to what its users see, and (b) that
module registers nothing that acts globally: no instances, simp or grind lemmas, notation, macros, ext
lemmas, coercions or exported aliases. Both conditions can be read from the tables. Because this changes
what other files can see, it should be confirmed by recompiling a sample of the files that use the changed
ones (`tools/downstream_check.py`).
