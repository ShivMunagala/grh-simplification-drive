# Brief: make one proof smaller, statement unchanged

You are given a short list of theorems in a very large Lean 4 project (a formal proof of the Riemann
Hypothesis, built on Mathlib). For each one, try to replace its proof with a smaller one.
The statement must not change. Work on one theorem at a time.

## What "smaller" means

Three numbers are measured for the file that contains the theorem:

1. **Source tokens**: length of the source text. A name of any length is one token, comments are free.
2. **Written-out size**: size of the fully expanded proof Lean produces and checks. A short tactic
   can expand into something enormous (`nlinarith`, `ring`, `linarith`, `simp` with big lemma sets,
   case splits on large structures), so a shorter source is not automatically a smaller proof.
3. **Compile time** of the file.

A change is good only if **neither size goes up, at least one goes down, and the file does not get
slower**. Making the source shorter by calling heavier automation is not wanted, and neither is
shrinking the expansion by spelling out more steps in the source. What is wanted is a genuinely more
direct argument: a lemma that already says it, a cheaper tactic that suffices, a case split that is not
needed, a detour removed.

## Rules

- Edit only the proof of the listed theorem, in the listed file, between the listed lines. Do not touch
  the statement, other declarations, imports, `open` lines or options. Do not edit any other file.
- Do not add new declarations, macros, notation, `sorry`, `native_decide` or axioms.
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

Each run compiles the file once (twice the first time). That takes from one to many minutes, and only
one compile runs at a time on this machine, so runs queue behind other workers. **Think before each
run.** You have at most **6 runs per theorem**. Use a generous timeout when you call it (30 minutes).

Source files are under `proof/src/`; module `A.B.C` is
`A/B/C.lean`. Read the file and whatever it imports to understand the definitions involved. Mathlib's
source is in the packages directory the tools use (`proof/.lake/packages/mathlib`, or the one named in
`grh.local.json`).

## When you stop on a theorem

- If `PRECHECK: pass`: leave your edit in place and move on.
- Otherwise restore the file exactly:
  `git -C proof checkout -- src/<path>.lean`
  and move on. Never leave a file in a failing or unchanged-but-edited state.

## Report (your final message)

For each theorem, in a small table: module, theorem, result (`improved` / `no gain` / `could not compile`
/ `too heavy for this machine`), source tokens before → after, written-out size before → after, number
of runs used. Then for each one, two or three sentences: what you changed, or why it resisted. Say in
particular whether the size comes from the proof steps or from the definitions and statements involved
(in which case no local edit will help). Report honestly; "no gain" with a clear reason is a useful
result.
