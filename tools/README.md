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
statement and body. `iface.py` compares a recompiled module with its accepted version on exactly that:

- same statements and same definitions: every module that uses it is still valid, nothing else is rebuilt;
- something changed or disappeared: `judge.py` looks up which modules actually mention it and
  recompiles those (`--propagate`), then repeats.

"Same statement" is checked strictly, because Lean's own hash of a statement is 32 bits wide and ignores
the names of its arguments and whether each is explicit or implicit. `moddump --strict` adds a 64-bit hash
that covers argument names and kinds and the order of universe parameters. A statement that is the same up
to those is reported as changed: another file could be passing an argument by name or by position.

Two things a module shows to others are not in any statement, so they are compared separately:

- What it registers with Lean: attributes, instances, simp lemmas, notation. The number of entries per
  extension must be the same before and after (source positions, documentation, linter messages and
  import bookkeeping are left out). Dropping `@[simp]` from a lemma would otherwise pass.
- Namespaces. Lean only reads its list of namespaces to resolve `open X` and `export X`. A removed
  namespace is a difference. An added one is harmless when a module that the changed file imports
  already registers it, or when no `open` or `export` anywhere in the tree names a proper suffix of
  it; `nscheck.py` decides that from a table of all base modules and a scan of the source.

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
- `nscheck.py` — `build` the table of which base module registers which namespace (under a minute);
  `check` whether namespaces added by recompiled modules can change what any `open` refers to.
- `judge.py` — changed files → compile → equivalence check → dials → verdict
  (`accept`, `review`, `incomplete`, `invalid`). Judges against the accepted state (the archive plus every
  recorded change), so changes stack. `--precompiled DIR` takes modules compiled on another machine and
  still checks interfaces and dials here.
- `try_change.py` — what a worker runs on one edited file before handing it in: compile, equivalence
  check, sizes and time before and after, and `PRECHECK: pass` or `fail`.
- `alias_wrappers.py` — find theorems that only restate another theorem and cite it, and rewrite them
  as `alias`.
- `batch_compile.py` — compile many edited files in parallel on a machine with room for it and run the
  equivalence check on each; `--recheck` runs the check again without compiling.
- `remote/` — `bootstrap.sh` sets a rented machine up from nothing; `compile_there.py` compiles single
  files on it and brings the results back for the judge.
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
unmodified archive. `patches.py export` turns everything after the tag into `patches/`, and
`patches.py apply` rebuilds our version from a fresh copy of the archive. `patches/` holds no line of the
archive: deleted files are paths, rewritten wrappers are names, and every other change is a list of line
ranges to replace together with the replacement lines. Each file is pinned by the sha256 of its archive
version and of the result, so the ranges are exact and a wrong base is refused.

One judged change takes about eight minutes here for a single file that imports all of Mathlib: two
compiles (the new version and, for timing, the old one) and one pass over the tables.

## CI

`.github/workflows/dials.yml` runs on every push and pull request. It does not measure: a hosted runner
cannot hold the compiled base. It checks that the README block and the images match
`metrics/history.csv`, so the numbers shown are always the numbers recorded. Measuring on CI needs a
self-hosted runner with the compiled base; `judge.py` would run there unchanged.

## Not built yet

- Rebuilding the accepted state from `patches/` alone: the compiled modules of recorded changes live in
  `compiled-overlay/`, which is not in git, so a fresh clone has to recompile them.
- Time as an absolute number for the whole cone (the judge compares only the files it recompiles).
- Statement comparison by Comparator and replay by independent checkers: needs a full build and
  roughly 100 GB of memory, so it belongs on a large machine.
- Measuring on CI: a runner needs about 120 GB of disk for the compiled base.
- Removing everything outside the cone from `proof/`.
