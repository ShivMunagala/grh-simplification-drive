# Brief: remove parts of statements that nothing needs

The five target theorems do not use everything the proof proves on the way. A measurement
(`tools/demand.py`) followed the demand from the targets down through the compiled proof terms and found,
for each intermediate theorem, which parts of its result are ever read by something that is itself needed.
You are given a short list of theorems where some parts are never read. For each one, make the smallest
edit after which the unneeded parts, and the lemmas that only they use, are no longer reachable from the
targets.

Unlike the proof-shrinking work, **here statements may change**: only the five target theorems and the
axioms are fixed. But every file must still compile, and nothing that is needed may be weakened.

## What you are given for each item

- The theorem `B`, its module, and what is asked of it, written as a nested list: `T` = this part is
  needed, `_` = it is not. For a conjunction `A ∧ B ∧ C ∧ D`, which Lean reads as `A ∧ (B ∧ (C ∧ D))`,
  `(_ (T (_ T)))` means that only `B` and `D` are needed. An existential `∃ x, P x ∧ Q x` is a pair of the
  witness and the property: `(T (T _))` means `x` and `P x` are needed, `Q x` is not. `all` means the
  whole result is needed and the unneeded mention sits inside the proof (a step whose result is not used).
- The lemmas that would leave the cone, with what leaves with each (in term nodes).

The measurement can be wrong in details (it reads compiled terms, you read source). Check by reading: find
every use of `B` (`grep -rl "<last part of the name>" proof/src/<top folder>`; restrict the search, the tree
has 175,000 files) and see which parts each use takes.

## How to do it, in order of preference

1. **Go around the bundle.** If `B`'s proof is a tuple of citations and it has few users, change each user
   to cite the lemma for the part it needs (`foo args` instead of `(B args).2.2.1`, or instead of
   destructuring `B`). `B` then has no needed user left. Leave `B` itself alone: files outside the cone may
   use it.
2. **Trim the statement.** Delete the unneeded conjuncts from `B`'s statement and their proofs from its
   body, then fix every user (projection chains get shorter, patterns lose an entry). All users must
   compile.
3. **Delete the dead step.** For `all`: find the step in the proof whose result is not used (a `have` that
   nothing mentions, an argument that the callee ignores) and remove it.

If none of these is safe, or it turns out the part is used after all, leave the item and say why.

## Rules

- Do not change the five target theorems (in `proof/src/Main.lean`), any definition, or the statement of
  any theorem other than the `B` of an item.
- No new files, no new imports, no macros, notation, `sorry`, `native_decide` or axioms.
- Do not commit, do not run the judge or the record tool; never run `lake build` or any other Lean process.
- Other workers edit other files in the same tree. Give up on a file only by restoring that one file
  from the proof repository (`checkout -- src/<path>.lean` in `proof/`); never stash, reset, or restore
  anything else.

## How to check

From the repository root, one run at a time, in the background with the output in a log file under
`build/try_logs/`:

```
python3 tools/remote/compile_there.py <Module.Name> --out build/pre/<your label>
```

It sends the file to a rented machine, compiles it against the accepted versions of all other files, and
prints the errors or the numbers, ending with `PRECHECK: pass` or `PRECHECK: fail (reasons)`. When you
changed a statement, the check of `B`'s file will say that its interface changed: that is expected. Then
check each user with the changed file in place:

```
python3 tools/remote/compile_there.py <User.Module> --with <B's.Module> --out build/pre/<your label>
```

A user passes when it compiles and its own statements are unchanged. Think before each run; a run takes
one to five minutes.

## Report (your final message)

A table: item, what you did (went around / trimmed / deleted a step / left alone), files edited, result of
the last check of each file. Then for each item two or three sentences: which parts were unneeded and why
you are sure that no needed use reads them, or why you left it. List every edited file by module name:
the coordinator judges them together.
