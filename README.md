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
  <img alt="The three dials over time, one point per recorded commit. Latest: source size 175.8M, written-out proof size 2.68B, time change -3.98K" src="metrics/dials-light.svg">
</picture>

| Dial | Baseline | Now | Change |
|---|---:|---:|---:|
| Source size (tokens) | 184,248,210 | 175,766,516 | −8,481,694 |
| Written-out proof size (term nodes) | 2,789,304,299 | 2,682,353,662 | −106,950,637 |
| Time (CPU seconds on recompiled files, running total) | 0.0 | -3,980.1 | −3,980.1 |

Cone: 1,255,858 declarations in 146,191 files. Recorded changes: 44. Latest row: pb_abs by a dual family in place of Smith normal form (33k to 5k nodes); shorter classical estimates in two files (2026-11-22 20:06 UTC).
<!-- dials:end -->

## Milestones

| When | Milestone | Status |
|---|---|---|
| 2026-11-21 | Archive measured: what the five theorems depend on, and the three dials for it | done |
| 2026-11-21 | Judge working: a change is compiled, checked and measured before it is recorded | done |
| 2026-11-22 | First heavy proofs rewritten without taking large structures apart (waves 1 and 2) | done |
| 2026-11-22 | Restatements removed: 32,172 theorems that only repeated another theorem's statement and cited it are now aliases. Source size −3.5% | done |
| 2026-11-22 | Repetition measured: 28,313 statements are proved independently more than once ([details](campaign/repetition/RESULTS.md)) | done |
| 2026-11-22 | Repetition sweep, part 1: 10,064 duplicate proofs now cite a copy their file already imports (two passes), each citation in its shortest form. Written-out size −0.5%, source −0.2% | done |
| 2026-11-22 | Heaviest proofs, waves 2 to 6: 50 proofs rewritten by hand, each kind of cause written up with its fix ([notes](campaign/proof-shrink/RESULTS.md)) | done |
| 2026-11-22 | One shared lemma for 24 proofs that take the same record apart: 16 rewritten, written-out size −12.0 million nodes, their files compile in half the time | done |
| 2026-11-22 | Patterns that drop parts of a conjunction read the kept parts by projection instead of matching every part. 9,519 lines in 7,351 files, −18.7 million nodes, source down ([notes](campaign/proof-shrink/RESULTS.md)) | done |
| 2026-11-22 | Source dial made stricter: every projection step is a token (before, `h.2.2.1` counted as one). Baseline and history recounted; all 30 recorded changes still pass | done |
| 2026-11-22 | Patch file stores nothing of the archive: pieces a rewrite kept or moved are given as positions. Earlier versions, which repeated such pieces, removed from this repository's history | done |
| 2026-11-22 | Repetition sweep, part 2: 3,243 duplicate proofs in 2,502 files cite a copy through one added import. Written-out size −7.2 million nodes, source −402,000 tokens. Before judging, every file that could read a name differently because of the new imports (4,071 of the 101,394 that see something new) was compiled again; two citations whose import made another file stop compiling were taken out | done |
| | Duplicates that would need a shared new file | not started |
| | Heavy definitions built from chains of `choose` | next |
| 2026-11-22 | Wave 7 on the heaviest proofs: 17 more rewritten. Proofs over 100,000 nodes are now only 2.8% of the whole, so returns from this kind of work are falling | done |
| | Sweep of repetitions: the same argument written out in many proofs | next |
| 2026-11-22 | Largest declaration in the proof (`lam_copy`, 5.5 million nodes) rewritten: the property is stated once over the 29 components it mentions, and no record is taken apart. 30,000 nodes; its file compiles in 2.7 s, before 108 s ([notes](campaign/proof-shrink/RESULTS.md)) | done |
| 2026-11-22 | Plain-language map of the argument, first version: the chain at the top, the four lines of argument under it and what each costs, known theorems proved inside (8.4% in all), six places where a shorter route might exist ([map](campaign/argument-map/MAP.md)). Everything above is about how the proof is written; this is the first step on the mathematics | done |
| 2026-11-22 | All four large candidates for a shorter route tested by reading every statement and every use: the covolume bound (13.6%), the Galois representations (6.1%), the vanishing statement VWin (8.2%) and the staging of the family construction. None can be replaced or narrowed; the reasons are in the map | done |
| 2026-11-22 | What the five theorems actually ask of each intermediate statement, measured on the compiled proof (`tools/demand.py`): parts of conjunctions, fields of records, arguments, local steps and whole declarations that nothing needed reads come to 1.07% of the written-out size. The proof uses almost everything it proves ([results](campaign/unneeded-parts/RESULTS.md)) | done |
| | Removing those unneeded parts, largest first ([brief](campaign/unneeded-parts/BRIEF.md), [results](campaign/unneeded-parts/RESULTS.md)). Eight changes so far take 3,051 declarations out of what the five theorems need (−7.7 million nodes, −451,000 tokens): seven of eight statements about period unfoldings; the main theorem of the raw theta lift, which was built only to be passed to a theorem that ignored it; theorems that prove lists of statements of which a few are read (46 so far: users cite the part they read); eight statements trimmed to what their users read | in progress |
| 2026-11-22 | Local steps whose result nothing uses (`have h : P := proof`, and `h` is never read): the same measurement names them, and 6,343 are deleted in 2,099 files, each deletion kept only if its file still compiles to the same statements and is smaller. Written-out size −1.6 million nodes, source −126,000 tokens. This round took the 3,000 files that hold most of them; about 18,000 files with a few each remain | first round done |
| 2026-11-22 | Declarations written with every argument explicit (machine-printed terms, about fifty files, 0.37% of the source): 252 reprinted in ordinary form by `tools/compact.py`, each kept only if Lean reads it back at the same place as the same statement and, for a definition, the same value. Source −482,000 tokens; written-out size unchanged. Another project had reported the pattern for four of these files; no text was taken from it ([notes](campaign/proof-shrink/RESULTS.md)) | done |
| 2026-11-22 | The conditions on the families, read one by one: all 46 fields of the hypothesis list are used, and the costly ones are consumed at the strength in which they are proved. There is room only in error terms and in smallness parameters (two small new candidates: an off-diagonal spectral bound, 1.5%, and a dimension estimate, 0.3%); main terms cancel exactly ([map, section 6](campaign/argument-map/MAP.md)) | done |
| 2026-11-22 | Lemmas at library level measured: 92,689 theorems the five targets need have statements that mention only Mathlib. Their proofs are 6.9% of the written-out size and 12.2% of the source. They are not copies of library theorems (139 exact matches) and one call of automation proves 0.7% of a sample, so shortening them means proving them again; each is a self-contained task ([results](campaign/library-lemmas/RESULTS.md)) | measured; open |
| 2026-11-22 | First proof replaced by a different argument: a statement proved through Smith normal form is proved by a dual family (33,347 → 5,167 nodes; the idea is from another project's notes, the proof is written here) | done |

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
