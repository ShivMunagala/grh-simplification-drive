# Brief: make proofs smaller, statements unchanged

You are given a short list of theorems in a very large Lean 4 project (a formal proof of the Riemann
Hypothesis, built on Mathlib). For each one, try to replace its proof with a smaller one.
The statement must not change. Work on one theorem at a time.

Read `RESULTS.md` in this folder first: it says what made earlier proofs large and which techniques
worked.

## What "smaller" means

Three numbers are measured for the file that contains the theorem:

1. **Source tokens**: length of the source text. A name of any length is one token, comments are free.
2. **Written-out size**: size of the fully expanded proof Lean produces and checks. A short tactic
   can expand into something enormous (bulk case splits on large structures, `nlinarith`, `ring`,
   `simp` with big lemma sets), so a shorter source is not automatically a smaller proof.
3. **Time** Lean spends elaborating and checking the file (loading imports is not counted).

A change is good if **neither size goes up, at least one goes down, and the file does not get slower**.

One trade is allowed: **source tokens may go up if the written-out size falls by at least 1,000 nodes
for every token added.** Nothing else may be traded. In particular, making the source shorter by
calling heavier automation is not wanted.

What is wanted is a genuinely more direct argument: a lemma that already says it, a cheaper tactic
that suffices, a case split that is not needed, a detour removed, a shared lemma replacing the same
work done in several proofs.

## Rules

- Do not change the statement of any existing theorem or the body of any existing definition.
- You may add helper lemmas. Put a helper in the file that defines the thing it is about, so that
  every file that could use it already imports it; do not add imports and do not create files.
  A helper must be worth it: it counts towards the size like everything else. Keep each one small.
- Do not add macros, notation, `sorry`, `native_decide` or axioms.
- Edit only the files on your list (plus the defining file of a helper, if you say so in your report).
- You may use anything from Mathlib or from files the file already imports.
- Do not run `git commit`, the judge, or the record tool. Do not build anything else.
- The project is far too big to build; never run `lake build`. The only way to compile is the tool below.

## How to check an attempt

From the repository root:

```
python3 tools/try_change.py <Module.Name>
```

It compiles that one file against the already-compiled rest of the project (sandboxed), and prints the
compile errors, or the before/after numbers for the file and for each changed declaration, ending with
`PRECHECK: pass` or `PRECHECK: fail (reasons)`.

If you add a helper in one file and use it in another, check the helper's file first, then the user:
the tool compiles a file against the accepted versions of other files, so the second check will only
see your helper once the first file's change has been judged and recorded. Say so in your report and
stop there; the coordinator will record the helper and hand the users back.

Each run compiles the file once (twice the first time it is touched). A run takes from a few minutes
to a quarter of an hour, and at most two compiles run at a time on this machine, so runs queue.
**Think before each run.** Start a run in the background, send its output to a log file under
`build/try_logs/`, and wait for it to finish; never start a second run of your own while one is going.

Source files are under `proof/src/`; module `A.B.C` is `A/B/C.lean`. Read the file and whatever it
imports to understand the definitions involved. Mathlib's source is in the packages directory the
tools use (`proof/.lake/packages/mathlib`, or the one named in `grh.local.json`).

## When you stop on a theorem

- If `PRECHECK: pass`: leave your edit in place and move on.
- Otherwise restore the file exactly:
  `git -C proof checkout -- src/<path>.lean`
  and move on. Never leave a file in a failing or unchanged-but-edited state.
- Other workers edit other files in the same tree at the same time. Never run `git stash`,
  `git reset`, `git commit`, or a `checkout` of anything but your own files.

## Report (your final message)

For each theorem, in a small table: module, theorem, result (`improved` / `no gain` / `could not compile`
/ `too heavy for this machine`), source tokens before → after, written-out size before → after, number
of runs used. Copy the numbers the tool printed. Then for each one, two or three sentences: what you
changed, or why it resisted. Say in particular whether the size comes from the proof steps or from the
definitions and statements involved (in which case no local edit will help). If you found a technique
that should work on other proofs, describe it in one or two lines. Report honestly; "no gain" with a
clear reason is a useful result.
