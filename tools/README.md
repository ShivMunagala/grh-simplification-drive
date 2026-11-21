# Tools

Everything here runs on an ordinary machine. Nothing rebuilds the whole proof.

## How the work is split

| Step | Tool | Needs |
|---|---|---|
| Get the source and apply our patches | `setup_proof.sh` | 240 MB download |
| Get the compiled base | `fetch_compiled.sh` | 28.6 GB download |
| Read every compiled module once | `dump_stream.py` + `moddump/` | about 15 minutes, little memory |
| Cone and the two size dials | `cone.py` | a few minutes |
| Compile one file | `compile_one.py` | the compiled base on disk |
| Small equivalence check | `iface.py` | seconds |
| Judge a change | `judge.py` | compiles only what changed |

The compiled base is the published build of the unmodified archive (175,187 modules, 99 GB unpacked,
about a third of that on a compressing filesystem). It is treated as read-only. A change is checked by
compiling only the files it touches against that base.

## Why compiling only the touched files is enough

Other modules never look inside a proof. They see each theorem's statement, and each definition's
statement and body. `iface.py` compares a recompiled module with its base version on exactly that:

- same statements and same definitions: every module that uses it is still valid, nothing else is rebuilt;
- something changed or disappeared: `judge.py` looks up which modules actually mention it and
  recompiles those (`--propagate`), then repeats.

This is a pre-filter. It checks that compiled proofs stay valid; it does not notice that some
untouched file would now *compile differently* (for example because a lemma it found by search is
gone). Only a full rebuild shows that, so milestones still need one on a large machine, together
with Comparator and the independent checkers.

## Safety

The archive is untrusted code, and compiling Lean runs code. `compile_one.py` runs the compiler under
bubblewrap with no network and a read-only filesystem, and under a memory cap. `moddump` never
executes anything from a compiled file; it maps the file and walks the data, also sandboxed.

## The tools

- `setup_proof.sh` — build `proof/` from nothing: fetch the archive, make it a git repository with the
  unmodified archive tagged `upstream`, apply `patches/`.
- `patches.py` — `export`, `apply`, `status`: our changes to the proof as differences from the archive.
- `fetch_upstream.sh` — download the 14 source parts, verify the sha256, extract into `proof/`.
- `fetch_compiled.sh` — download the published compiled archive and verify its sha256.
- `moddump/` — small Lean program. Reads `.olean` files one at a time and prints, per declaration:
  kind, size of statement and body (term nodes), structural hashes of both, and the declarations
  each of them mentions. Build with `lake -d tools/moddump build`.
- `dump_stream.py` — streams the compiled archive through `moddump` without unpacking it, writing
  `data/base/consts.tsv.zst` (declarations) and `data/base/decls.tsv.zst` (source ranges).
  With `--keep compiled/lib/lean` it also leaves the compiled files on disk for `compile_one.py`.
- `cone.py` — builds the dependency graph, takes everything the five theorems reach, and reports
  the written-out size and the source size in tokens, for all five theorems and for RH alone.
  Accepts patches so the judge can swap in recompiled modules.
- `compile_one.py` — compile one module against the base; reports CPU time and peak memory.
- `iface.py` — the equivalence check described above.
- `judge.py` — changed files → compile → equivalence check → dials → verdict
  (`accept`, `review`, `incomplete`, `invalid`).
- `ablation.py` — ranks declarations by how much of the cone depends only on them: the spine
  (single statements everything below passes through), the largest blocks, and what each known
  theorem costs on its own. About a minute.
- `record.py` — after a judged change is committed in `proof/`, append its dials to
  `metrics/history.csv` with that commit's time, then export patches and redraw the chart.
- `chart.py` — draw the three dials over time (`metrics/dials-light.svg` / `dials-dark.svg`, one point per
  recorded commit) and refresh the block in the top-level README; `--check` fails if they are out of date
  (run by CI).
- `common.py`, `timed_exec.py` — shared paths and helpers.

## A change, start to finish

```
edit files under proof/src
python3 tools/judge.py                  # verdict and dials; add --propagate if other modules use what changed
git -C proof commit -am "..."           # the change itself, in the proof repository (local only)
python3 tools/record.py --label "..."   # history row with that commit's time, patches/, chart, README block
git add -A && git commit                # this repository: the row, the patches and the images together
```

`proof/` is its own git repository and is ignored by this one. Its first commit, tagged `upstream`, is the
unmodified archive; the judge compares against that tag. `patches.py export` turns everything after the tag
into `patches/` (deleted paths, plus a diff of changed and added files), and `patches.py apply` rebuilds our
version from a fresh copy of the archive. The round trip was checked: archive plus exported patch gives the
same tree hash as the edited tree.

One judged change takes about eight minutes here for a single file that imports all of Mathlib: two
compiles (the new version and, for timing, the old one) and one pass over the tables.

## CI

`.github/workflows/dials.yml` runs on every push and pull request. It does not measure: a hosted runner
cannot hold the compiled base. It checks that the README block and the images match
`metrics/history.csv`, so the numbers shown are always the numbers recorded. Measuring on CI needs a
self-hosted runner with the compiled base; `judge.py` would run there unchanged.

## Not built yet

- Stacking changes. The judge compares the working tree with the unmodified archive and patches only
  the modules it just compiled into the tables. For a second change on top of a first, the compiled
  results and table rows of earlier accepted changes have to be kept and reused.
- Time as an absolute number for the whole cone (the judge compares only the files it recompiles).
- Statement comparison by Comparator and replay by independent checkers: needs a full build and
  roughly 100 GB of memory, so it belongs on a large machine.
- Measuring on CI: a runner needs about 120 GB of disk for the compiled base.
- Removing everything outside the cone from `proof/`.
