# Runbook: how the work runs without supervision

The owner has asked for this project to run largely on its own. This file says what that means, so that
any session can pick the work up and so that the limits are written down.

## The loop

1. **Pick.** Take candidates from the current worklist (`build/judge/worklist.tsv.zst`, largest first within
   the family being worked on), skipping anything listed in a campaign's `attempted.tsv`.
2. **Dispatch.** Give up to four workers a short list each (files grouped so one compile checks several
   theorems) and the campaign brief. Workers edit `proof/`, check with `tools/try_change.py`, and report.
3. **Judge.** For each file a worker left in a passing state: `tools/judge.py --only <Module>`.
4. **Record.** `accept`: commit that file in `proof/`, `tools/record.py`, commit and push this repository.
   `review`: save the diff under the campaign's `review/` folder, restore the file, and list it for the owner.
   `invalid` or `incomplete`: restore the file and note why.
5. **Write down.** Add the outcome to the campaign's `RESULTS.md` and `attempted.tsv`, including failures
   and the reason, so nothing is tried twice blindly and techniques carry over.
6. Repeat while the work is paying off.

## Limits that hold without asking

- Only changes the judge accepts under the rules in the top-level README are recorded. Rules are not bent
  case by case; a change that needs a decision goes to `review/` and waits.
- At most two compiles at a time, the second only while 6.5 GB of memory is free. Never a full build.
- Pushes go only to this repository's `main`. Nothing is published, posted or sent anywhere else, and
  nobody outside is contacted.
- No money is spent: no rented machines, no paid services.
- The archive itself is never committed to this repository.

## When to stop and report

- A family is exhausted, or three waves in a row save less than 100,000 nodes in total.
- A tool misbehaves in a way that could have corrupted a recorded number.
- Free disk falls below 60 GB.
- Something needs one of the decisions below.

## Decisions that stay with the owner

- Anything in a `review/` folder.
- Changing the rules, the dials, the caps or the targets.
- Renting a large machine (needed for a full rebuild, Comparator on our version, pruning to the cone, and
  any campaign that touches thousands of files).
- Making the repository public, or contacting the author about a licence.

## Where things stand

See the top-level README for the dials, each campaign's `RESULTS.md` for what was tried, and
`metrics/history.csv` for every recorded change.
