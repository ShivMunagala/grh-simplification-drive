#!/usr/bin/env python3
"""Record a judged change: one row in metrics/history.csv, fresh patches, fresh chart.

  tools/record.py --label "what changed" [--work build/judge] [--allow-review]

Run after tools/judge.py and after committing the change inside proof/ (its own local repository).
The row carries the time and short hash of that proof commit, so the chart shows when each change
happened. Time (the third dial) is kept as a running total of the change in CPU seconds on the files
each change recompiled, because the whole cone is never timed on this machine.

Afterwards commit this repository: the row, the patches and the redrawn images belong together.
"""
import argparse, csv, json, os, subprocess, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C

HISTORY = os.path.join(C.ROOT, 'metrics', 'history.csv')


def proof_git(*args):
    return subprocess.run(['git', '-C', C.PROOF] + list(args), stdout=subprocess.PIPE, check=True).stdout.decode()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--label', required=True)
    ap.add_argument('--work', default=os.path.join(C.ROOT, 'build', 'judge'))
    ap.add_argument('--allow-review', action='store_true',
                    help='record a change the judge sent to review (a person has decided to accept it)')
    a = ap.parse_args()

    verdict = json.load(open(os.path.join(a.work, 'verdict.json')))
    summary = json.load(open(os.path.join(a.work, 'summary.json')))
    v = verdict.get('verdict')
    if v != 'accept' and not (v == 'review' and a.allow_review):
        sys.exit(f'verdict is {v!r}; only accepted changes are recorded (use --allow-review after a human decision)')
    if proof_git('status', '--porcelain').strip():
        sys.exit('proof/ has uncommitted changes; commit the judged change there first')
    commit, when = proof_git('show', '-s', '--format=%h %cI', 'HEAD').split()

    with open(HISTORY, newline='', encoding='utf-8') as fh:
        rows = list(csv.DictReader(fh))
    if rows and rows[-1]['proof_commit'] == commit:
        sys.exit(f'proof commit {commit} is already recorded')
    last_time = float(rows[-1]['time_cpu_s']) if rows else 0.0
    d = verdict['dials']
    row = {
        'time': when,
        'proof_commit': commit,
        'label': a.label.replace(',', ';') + (' [review]' if v == 'review' else ''),
        'source_tokens': d['source_tokens']['after'],
        'written_out_size': d['written_out_size']['after'],
        'time_cpu_s': round(last_time + d['time_cpu_s']['change'], 1),
        'cone_declarations': summary['cone']['declarations'],
        'cone_modules': summary['cone']['modules_touched'],
    }
    with open(HISTORY, 'a', newline='', encoding='utf-8') as fh:
        csv.DictWriter(fh, fieldnames=list(row)).writerow(row)
    print('recorded', row)
    tools = os.path.join(C.ROOT, 'tools')
    subprocess.run([sys.executable, os.path.join(tools, 'patches.py'), 'export'], check=True)
    subprocess.run([sys.executable, os.path.join(tools, 'chart.py')], check=True)
    print('now commit this repository (metrics/, patches/, README.md)')


if __name__ == '__main__':
    main()
