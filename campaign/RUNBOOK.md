# Runbook: how the work runs without supervision

The owner has asked for this project to run largely on its own. This file says what that means, so that
any session can pick the work up and so that the limits are written down.

## The loop for hand-made changes

1. **Pick.** Take candidates from the current worklist (`build/judge/worklist.tsv.zst`, largest first within
   the family being worked on), skipping anything listed in a campaign's `attempted.tsv`.
2. **Dispatch.** Give up to four workers a short list each (files grouped so one compile checks several
   theorems) and the campaign brief. Workers edit `proof/`, check with `tools/try_change.py`, and report.
3. **Judge.** For each file a worker left in a passing state: `tools/judge.py --only <Module>`.
4. **Record.** `accept`: commit that file in `proof/`, `tools/record.py`, commit and push this repository.
   `review`: save the diff outside this repository (`build/review/`, not in git), restore the file, and list
   it for the owner. `invalid` or `incomplete`: restore the file and note why.
5. **Write down.** Add the outcome to the campaign's `RESULTS.md` and `attempted.tsv`, including failures
   and the reason, so nothing is tried twice blindly and techniques carry over.
6. Repeat while the work is paying off.

## The loop for mechanical changes to many files

Used when one rewrite applies to thousands of files (restating theorems turned into aliases, duplicate
proofs turned into citations).

1. **Find** the candidates from the tables (`tools/alias_wrappers.py find`, `tools/cite_duplicates.py find`).
2. **Rewrite** the files on a rented machine and compile them there in parallel
   (`tools/remote/bootstrap.sh`, `tools/remote/sync_there.py`, `tools/batch_compile.py`). A file that
   fails is simply left out.
3. **Check again** with `tools/batch_compile.py --recheck`, and time the accepted versions under the same
   load with `--accepted`.
4. **Spot-check** files that use the changed ones: `tools/downstream_check.py` recompiles a sample and
   requires each to come out exactly as it was.
5. **Judge here**, not there: copy the compiled modules back, apply the same rewrite to `proof/`, and run
   `tools/judge.py --precompiled <dir> --only-file <list>`. Interfaces, namespaces and dials are checked on
   this machine; only the compiling was done elsewhere.
6. **Record** as one change.

## Limits that hold without asking

- Only changes the judge accepts under the rules in the top-level README are recorded. Rules are not bent
  case by case; a change that needs a decision waits for the owner.
- On this machine: at most two compiles at a time, the second only while 6.5 GB of memory is free.
- Pushes go only to this repository's `main`, never forced. Nothing is published, posted or sent anywhere
  else, and nobody outside is contacted.
- The repository is public. No line of the archive goes into it: not in patches, not in review notes, not in
  examples. No keys, addresses of rented machines, or local paths either.
- Money: the owner has released the balance of one rental account for this work (2026-11-22). Machines are
  rented only from that balance, are destroyed as soon as their job is copied back, and everything is
  destroyed before the balance runs out. Nothing else is paid for.

## When to stop and report

- A family is exhausted, or three waves in a row save less than 100,000 nodes in total.
- A tool misbehaves in a way that could have corrupted a recorded number.
- Free disk falls below 60 GB.
- Something needs one of the decisions below.

## Decisions that stay with the owner

- Any change the judge sends to review.
- Changing the rules, the dials, the caps or the targets.
- Spending beyond the released balance.
- Rewriting the public history of this repository, or contacting the author about a licence.

## Where things stand

See the top-level README for the dials and milestones, each campaign's `RESULTS.md` for what was tried, and
`metrics/history.csv` for every recorded change.
