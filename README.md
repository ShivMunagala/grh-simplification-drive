# GRH simplification drive

Working repository for simplifying Levent Alpöge's Lean proof of the Riemann Hypothesis and of GRH for
Dirichlet L-functions, announced on 2026-11-20 ([remark](https://alpo.ge/remark.pdf)).

This repository does not contain his archive. It contains the tools, the measurements, and our changes to
the proof as differences from the archive (`patches/`). The archive is fetched and checked by sha256.

## Goal

Make the proof smaller and easier to follow without changing what it proves: delete what is not needed,
share what is repeated, find shorter arguments.

## Where it stands

One point per recorded change, placed at the time of its commit.

<!-- dials:start -->
<picture>
  <source media="(prefers-color-scheme: dark)" srcset="metrics/dials-dark.svg">
  <img alt="The three dials over time, one point per recorded commit. Latest: source size 183.1M, written-out proof size 2.79B, time change -7.5" src="metrics/dials-light.svg">
</picture>

| Dial | Baseline | Now | Change |
|---|---:|---:|---:|
| Source size (tokens) | 183,118,239 | 183,118,012 | −227 |
| Written-out proof size (term nodes) | 2,789,304,299 | 2,787,043,943 | −2,260,356 |
| Time (CPU seconds on recompiled files, running total) | 0.0 | -7.5 | −7.5 |

Cone: 1,265,167 declarations in 146,536 files. Recorded changes: 4. Latest row: prove same_basic without taking the structures apart (2026-11-21 21:24 UTC).
<!-- dials:end -->

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

1. **Source size** of the cone, in tokens. A name of any length is one token; comments are not counted.
2. **Written-out proof size** of the cone: the size of the fully expanded proofs that Lean checks.
3. **Time** to build and check, compared on the files a change recompiles. Measured as the time Lean spends
   elaborating and checking those files, not counting the loading of what they import.

A valid change is accepted if no dial goes up, and it is progress if one goes down. The two sizes are exact.
Time is noisier, so it has a tolerance, and a change that raises it beyond that is reviewed by a person.

One trade between dials is allowed without review: **source size may rise if the written-out size falls by
at least 1,000 nodes for every token added.** The cone averages about 15 nodes per token, so this only admits
changes that are far better than the going rate. Any other change that trades one dial for another needs a
written reason and a human decision.

Two fences:

- A size cap on any single theorem or definition that is added, or that is changed and grows
  (`baseline/caps.json`, provisional). New helper lemmas are welcome as long as they stay under it.
- No new macros or notation.

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

- `patches/` — our changes to the proof: deleted paths, a diff of changed and added files, and the hash of the
  archive they apply to. Empty until the first change.
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

## Not built yet

- A steadier time measure. Compile time is taken per file and swings with machine load; Lean's own
  per-phase timing, excluding module loading, would be steadier.
- Rebuilding the overlay from `patches/` on a fresh clone (recompiling every changed module in order).
- Measuring on CI. A hosted runner cannot hold the compiled base, so dials are measured locally and recorded.
- Comparator and the independent checkers on our version: they need a full build on a large machine.
- Removing everything outside the cone from `proof/`: needs that full build to confirm.
