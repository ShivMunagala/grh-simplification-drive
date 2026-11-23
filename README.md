# GRH simplification drive

Working repository for simplifying Levent Alpöge's Lean proof of the Riemann Hypothesis and of GRH for
Dirichlet L-functions, announced on 2026-11-20 ([remark](https://alpo.ge/remark.pdf)).

This repository does not contain his archive. It contains the tools, the measurements, and our changes to
the proof as differences from the archive (`patches/`). The archive is fetched and checked by sha256.

## Goal

Make the proof smaller and easier to follow without changing what it proves: delete what is not needed,
share what is repeated, find shorter arguments.

What is fixed is the task, not the route: the five target theorems and the axioms they may use. Everything
between them and Mathlib may change. An argument may be replaced by a different proof, and an intermediate
statement or definition may be changed or dropped, as long as the same five theorems come out.

## Where it stands

One point per recorded change, placed at the time of its commit.

<!-- dials:start -->
<picture>
  <source media="(prefers-color-scheme: dark)" srcset="metrics/dials-dark.svg">
  <img alt="The three dials over time, one point per recorded commit. Latest: source size 173.4M, written-out proof size 2.63B, time change -4.70K" src="metrics/dials-light.svg">
</picture>

| Dial | Baseline | Now | Change |
|---|---:|---:|---:|
| Source size (tokens) | 184,248,210 | 173,383,567 | −10,864,643 |
| Written-out proof size (term nodes) | 2,789,304,299 | 2,628,830,310 | −160,473,989 |
| Time (CPU seconds on recompiled files, running total) | 0.0 | -4,702.9 | −4,702.9 |

Cone: 1,213,160 declarations in 114,326 files. Recorded changes: 57. Latest row: Restatements: users cite the original theorem (109 files held back for a name check) (2026-11-23 02:21 UTC).
<!-- dials:end -->

## Milestones

By area: where the size is (shares are of the written-out size) and what has been done about it. Details are
in `campaign/`; every recorded change is a row of `metrics/history.csv`.

| Area | What is known | Done | Next |
|---|---|---|---|
| **Repetition** ([results](campaign/repetition/RESULTS.md)) | 7.6% of the proof is repeated in some form: the same statement more than once 6.4%, copies under other names 1.25% | duplicate proofs cite a copy their file imports, or can import by one added line (13,300 proofs); users of statements with two independent proofs cite one (−6.3 million nodes); restatements: their users cite the original (15,490 files: −35.9 million nodes, −1.9 million tokens) | a leftover batch for other theorems with one statement (8,400 files) is being compiled; what then remains needs shared files |
| **Known mathematics proved inside** ([results](campaign/library-lemmas/RESULTS.md)) | published theorems: 8.4% if they were free. Lemmas stated in Mathlib terms only: 6.9%, and 12.2% of the source; they are not copies of Mathlib and automation proves 0.7% of them | one proof replaced by a different argument (Smith normal form by a dual family); zero-free regions and Siegel–Walfisz with shared bounds (−120 thousand nodes); resolution of singularities without its compatibility with base change, which the five theorems never use (−303 thousand nodes, −64 thousand tokens) | toroidal compactifications: are they needed in the generality proved? |
| **The argument** ([map](campaign/argument-map/MAP.md)) | four lines under one chain: families 39%, covolume bound 13.6%, VWin 8.2%, Galois representations 6.1%. The counting argument is a slope inequality and costs 0.1% itself; all 46 conditions on the families are used at the strength proved; main terms cancel exactly | four large shortcuts tested and ruled out | seven candidates of at most 0.5% each |
| **What the five theorems need** ([results](campaign/unneeded-parts/RESULTS.md)) | 1.07% of what is proved is never read | 46 bundles bypassed or split, 8 statements trimmed: 3,051 declarations out; 6,343 unused local steps deleted | second round of unused steps; fresh measurement |
| **How proofs are written** ([notes](campaign/proof-shrink/RESULTS.md)) | sweeps over the whole proof, hand rewrites of the heaviest proofs | 32,172 restatements made aliases; projections in place of long patterns; explicit-argument files reprinted; about 120 heavy proofs rewritten (largest: 5.5 million nodes to 30 thousand); definitions taken out of a six-fold existential through generic helpers (−3.0 million nodes for 18 tokens) | returns falling: in most remaining heavy proofs the size is in the method (ring normalisation, long chains of witnesses), not in one fixable step |
| **Measurement and judge** | | cone of the five theorems, three dials, judge, strict token count, patches that hold no archive text, check against stale compiles | cone tool: 144 theorems whose name exists in two files; full rebuild from source at the end |

### Log

- **2026-11-21.** Archive measured (cone, dials). Judge working. First changes recorded.
- **2026-11-22.** Changes 3 to 54.
- **2026-11-23.** Changes 55 to 57: users of a restatement cite the original (15,490 files).
  Mathematics: the bound on Galois cohomology (8.4%) shown to imply an open conjecture on K-groups of ℤ, so no
  known theorem replaces it; the two covolume conditions reduced, on paper, to one inequality on theta lattices
  (not proved). Sweeps: restatements, citations of duplicates (two tiers), projections, unused steps,
  explicit-argument files. Hand rewrites: waves 2 to 8 on the heaviest proofs. Statements: five lists of unneeded parts.
  Mathematics: map of the argument; four large shortcuts ruled out; the conditions on the families and the counting
  argument read in full; library-level lemmas and repetition measured. Tools: strict token count, patch format,
  judge rules for added imports, stale compiles and registers.

## Fixed

- Lean v4.33.1 and Mathlib `0df444a` (tag v4.33.1). Mathlib is frozen and free; only what sits on top of it counts.
- The five theorems in `proof/src/Main.lean`: RH twice (Mathlib's statement and a written-out copy) and GRH
  for Dirichlet L-functions in three forms. A change is valid only if it still proves all five, using only the
  three standard axioms. In the archive RH is derived from the GRH statement, so the two targets need almost
  exactly the same material; the tools report the RH-only numbers alongside.

## How a change is judged

Everything is measured over the **cone**: the theorems and definitions outside Mathlib that the five theorems
actually depend on. Anything else in the tree does not count.

Three dials:

1. **Source size** of the cone, in tokens. A name is one token however long it is, and every numeric
   projection step after it is one more (`h.2.2.1` is four tokens); comments are not counted.
2. **Written-out proof size** of the cone: the size of the fully expanded proofs that Lean checks.
3. **Time** to build and check, compared on the files a change recompiles. Measured as the time Lean spends
   elaborating and checking those files, not counting the loading of what they import. Before and after are
   always measured on the same machine under the same load. Large batches are timed on a rented machine,
   sometimes on a random sample of their files (the history row then covers only the sample), so the running
   total adds seconds from different machines and is a rough indicator, not a benchmark.

A valid change is accepted if no dial goes up, and it is progress if one goes down. The two sizes are exact.
Time is noisier, so it has a tolerance, and a change that raises it beyond that is reviewed by a person.

One trade between dials is allowed without review: **source size may rise if the written-out size falls by
at least 1,000 nodes for every token added.** The cone averages about 15 nodes per token, so this only admits
changes that are far better than the going rate. Any other change that trades one dial for another needs a
written reason and a human decision.

Until 2026-11-22 a name counted as one token together with its projection steps, so a chain such as
`h.2.2.1` cost nothing more than `h`, and a change could lower the source dial just by writing such chains.
The dial now counts every step. The baseline and the history were recounted: the first and the last row
exactly, the rows between by what each change did to the number of steps. On the new count the baseline is
0.6% higher, and every recorded change still meets the rules above.

Changes made in bulk are judged file by file as well: a file is changed only if its written-out size does
not grow, one of the two sizes falls, and, if its source grows, the written-out size falls by at least 1,000
nodes per token added.

Two fences:

- A size cap on any single theorem or definition that is added, or that is changed and grows
  (`baseline/caps.json`, provisional). New helper lemmas are welcome as long as they stay under it.
  A new helper may be over the cap when it replaces more than it adds: the cone's written-out size must
  fall by at least what the helper weighs.
- No new macros or notation.

A change to a proof must also leave alone what other files see of its file: the statements, the
definitions, and what the file registers with Lean (instances, tagged lemmas, namespaces, its imports).
If that changes, the files that use it have to be recompiled and judged with it, or a person decides.
Two such changes are allowed outright (decided 2026-11-22), and the judge checks the conditions:

- The tag `@[elab_as_elim]` on a lemma that the change itself adds. It only tells Lean how to apply that
  new lemma, so no file that existed before can be read differently.
- An import added to a file, so that a proof in it can cite a copy of its statement in a file it could not
  see. Two conditions: the file already imported, directly or not, everything the newly imported file
  imports, so that nothing becomes visible to any file except files added in this way; and such a file
  registers nothing that can act on other files, only bookkeeping about its own declarations (the list is
  `PLAIN_REGISTERS` in `tools/iface.py`; instances, simp lemmas, notation, coercions and the like are not
  on it). What is left is names: a name in some other file could now resolve to a declaration of a newly
  visible file. So before such a change is judged, every file that gets to see more than before is
  searched for an identifier that could do that (`tools/import_visibility.py`), and each file where one
  is found is recompiled against the changed state (`tools/downstream_check.py --modules`). It has to
  compile and to come out with the same declarations and statements. One kind of difference is expected
  and allowed: Lean stores the lemmas it makes on the way (the equations of a definition, the helper
  lemmas of `simp`, `abel` and `ring`) in the file that first needs them, and a file that now sees a
  module which already holds one uses that and does not make its own. A random sample of the files that
  import a changed file is recompiled the same way.

  The check is not a formality. In the first batch (2,512 files gaining an import) 101,394 files got to
  see something new and 4,071 of them were flagged. Two no longer compiled: a short name in them now
  also matched a copy of the same lemma in a newly visible file. The two citations that caused it were
  taken out. Of the rest, 4,050 came out identical and 21 differed only in helper lemmas. A random
  sample of 300 was identical throughout, so a sample alone would not have found the two.

Reported to steer the work, not enforced: which declarations most of the cone hangs on
(`tools/ablation.py`), what each known theorem costs on its own, and how often each definition is used.

## Setup

Needs Linux, about 70 GB of free disk and 16 GB of memory, and: `git`, `curl`, `python3`, `zstd`,
`bubblewrap`, `systemd-run`, and [elan](https://github.com/leanprover/elan) (Lean v4.33.1 is picked up from
the toolchain files).

```bash
# 1. The proof: fetch the archive (240 MB), check it, apply our patches. Creates proof/, a local git repository.
tools/setup_proof.sh

# 2. Mathlib, compiled, at the pinned revision (about 5 GB).
(cd proof && lake exe cache get)

# 3. The compiled base: the published build of the unmodified archive (28.6 GB download).
tools/fetch_compiled.sh

# 4. Read every compiled module once (about 15 minutes); keep the compiled files for per-file compiles
#    (99 GB unpacked; about a third of that on a compressing filesystem).
lake -d tools/moddump build
python3 tools/dump_stream.py --archive upstream-dl/compiled/oleans.tar.zst --out data/base --keep compiled/lib/lean

# 5. Cone and size dials for the unmodified archive (a few minutes). Should match baseline/summary.json.
python3 tools/cone.py --out data/base
```

If a compiled Mathlib at that revision already exists elsewhere, skip step 2 and point to it instead:
put `{"packages": "/path/to/.lake/packages"}` in `grh.local.json` (not committed), or set `GRH_PACKAGES`.

After step 4 the 28.6 GB download can be deleted.

## Working on it

```bash
# edit files under proof/src, then:
python3 tools/judge.py                        # compiles what changed, checks it, prints verdict and dials
git -C proof commit -am "what changed"        # the change, in the proof repository
python3 tools/record.py --label "what changed"   # history row, patches/, chart and README block
git add -A && git commit -m "what changed"    # this repository
```

- `python3 tools/judge.py --propagate` also recompiles other modules that use what changed.
- `python3 tools/ablation.py` prints the spine, the largest blocks and the cost of each known theorem.
- `python3 tools/patches.py status` shows how far `proof/` is from the archive and whether `patches/` is current.

The judge compiles only the files that changed and checks that they still expose the same statements, so it
runs on an ordinary machine (about eight minutes for one file that imports all of Mathlib). It is a fast
pre-filter: a full rebuild with Comparator on a large machine remains the final word. See
[`tools/README.md`](tools/README.md) for what the local check does and does not cover.

## Layout

- `patches/` — our changes to the proof, with none of the archive's text in them: paths of deleted files,
  names of rewritten wrappers, and for every other changed file the character spans to replace plus the
  text that replaces them, pinned by the sha256 of the archive's file. Where a rewrite kept or moved a
  piece of the archive's file (24 characters or more), the patch names its position and length and does
  not repeat it. Also the hash of the archive they apply to.
- `tools/` — fetching, measuring, judging, recording.
- `campaign/` — briefs and results of organised efforts; `campaign/proof-shrink/RESULTS.md` has the first one.
- `baseline/` — dials, caps and dependency ranking for the unmodified archive.
- `metrics/` — recorded dials per change, and the images drawn from them.
- `.github/workflows/dials.yml` — checks that the README and images match `metrics/history.csv`.

Not in git: `proof/` (the archive with our patches applied, its own local repository), `upstream-dl/`
(downloads), `compiled/` (compiled base), `compiled-overlay/` (compiled modules of recorded changes),
`data/` (tables), `build/` (judge output), `grh.local.json`.

## Upstream

- Source: `https://alpo.ge/lean.tar.gz.part01` … `part14`; joined size 239,275,554 bytes;
  sha256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.
- Contents: 175,187 Lean files, 17,374,215 lines, plus `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`.
- Compiled base: [published build of the unmodified archive](https://huggingface.co/datasets/JackMcCarthy/riemann-hypothesis-build/tree/9036e64326acf4acfae159b96664e9708445c1d1),
  sha256 `953bab5386a7849527a11960f80a2fab427c49c637d6e94cc75788dd8f40196b`.
- Verification by others: [Lean and Mathlib community statement](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/),
  [Sutherland's verification page](https://math.mit.edu/~drew/grh/),
  [mirror with Comparator setup and build cache](https://github.com/leanprover-community/riemann-hypothesis).
- The archive was published without a licence, which is why it is fetched and not stored here.

## Licence

Apache License 2.0 (`LICENSE`), the same as Lean and Mathlib. It covers what is in this repository: the
tools, the measurements, the write-ups, and the replacement text in `patches/`.

It does not cover the proof archive. That is Levent Alpöge's work, it was published without a licence, and it
is not stored here. `patches/` holds only the spans that changed: positions, and the text we put there;
anything a rewrite reuses from the archive's file is given as a position, not as text. Applying it needs
the archive, fetched from its author's site. Earlier versions of the patch file, whose formats could
repeat lines of the archive, were removed from this repository's history on 2026-11-22.

## Not built yet

- Rebuilding the overlay from `patches/` on a fresh clone (recompiling every changed module in order).
- Measuring on CI. A hosted runner cannot hold the compiled base, so dials are measured locally and recorded.
- Comparator and the independent checkers on our version: they need a full build on a large machine.
- Removing everything outside the cone from `proof/`: needs that full build to confirm.
