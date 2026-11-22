#!/usr/bin/env python3
"""Record a judged change: it becomes part of the accepted state, and gets a row in the history.

  tools/record.py --label "what changed" [--work build/judge] [--allow-review]

Run after tools/judge.py and after committing the judged files inside proof/ (its own local
repository). This:

  * checks that the committed files are exactly the ones that were judged;
  * moves the freshly compiled modules into the overlay and their rows into the overlay tables,
    so the next change is judged on top of this one;
  * appends a row to metrics/history.csv with the time and short hash of the proof commit;
  * exports patches/ and redraws the chart and the README block.

Time (the third dial) is kept as a running total of the change in CPU seconds on the files each
change recompiled, because the whole cone is never timed on this machine.

Afterwards commit this repository: the row, the patches and the redrawn images belong together.
"""
import argparse, csv, hashlib, json, os, shutil, subprocess, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C

HISTORY = os.path.join(C.ROOT, 'metrics', 'history.csv')


def proof_git(*args, binary=False, check=True):
    p = subprocess.run(['git', '-C', C.PROOF] + list(args), stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=check)
    return (p.stdout if binary else p.stdout.decode()), p.returncode


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
    plan = verdict['plan']

    # the commit must contain exactly the judged files, with the judged contents
    head = proof_git('rev-parse', 'HEAD')[0].strip()
    names = set(l for l in proof_git('diff', '--name-only', '--no-renames', plan['base_commit'], 'HEAD', '--', 'src')[0]
                .splitlines() if l)
    judged = verdict['changed_hashes']
    if names != set(judged):
        extra, missing = sorted(names - set(judged))[:5], sorted(set(judged) - names)[:5]
        sys.exit(f'the proof commit does not match what was judged. Committed but not judged: {extra}. '
                 f'Judged but not committed: {missing}.')
    # the judged files are committed (not dirty) and their contents are what was judged
    dirty = set(l[3:] for l in proof_git('status', '--porcelain')[0].splitlines())
    for path, h in judged.items():
        if path in dirty:
            sys.exit(f'{path} has uncommitted changes; commit the judged files first')
        full = os.path.join(C.PROOF, path)
        got = None
        if os.path.exists(full):
            with open(full, 'rb') as fh:
                got = hashlib.sha256(fh.read()).hexdigest()
        if got != h:
            sys.exit(f'{path} differs from what was judged; run the judge again')
    commit, when = proof_git('show', '-s', '--format=%h %cI', 'HEAD')[0].split()

    with open(HISTORY, newline='', encoding='utf-8') as fh:
        rows = list(csv.DictReader(fh))
    if rows and rows[-1]['proof_commit'] == commit:
        sys.exit(f'proof commit {commit} is already recorded')

    # accepted state: compiled modules into the overlay, rows into the overlay tables
    os.makedirs(C.DATA_OVERLAY, exist_ok=True)
    for m in plan['modules']:
        for src, ext in ((plan['oleans'][m], '.olean'), (plan['ileans'][m], '.ilean')):
            dst = C.module_path(m, C.OVERLAY, ext)
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            shutil.copyfile(src, dst)
    for m in plan['removed']:
        for ext in ('.olean', '.ilean'):
            p = C.module_path(m, C.OVERLAY, ext)
            if os.path.exists(p):
                os.remove(p)
    shutil.copyfile(plan['consts'], os.path.join(C.DATA_OVERLAY, 'consts.tsv'))
    shutil.copyfile(plan['decls'], os.path.join(C.DATA_OVERLAY, 'decls.tsv'))
    modules = []
    with open(os.path.join(C.DATA_OVERLAY, 'consts.tsv'), 'rb') as fh:
        for line in fh:
            if line[:1] == b'M':
                modules.append(line.split(b'\t')[1].decode())
    d = verdict['dials']
    last_time = float(rows[-1]['time_cpu_s']) if rows else 0.0
    total_time = round(last_time + d['time_cpu_s']['change'], 1)
    state = {'proof_commit': head,
             'dials': {'source_tokens': d['source_tokens']['after'], 'written_out_size': d['written_out_size']['after']},
             'time_cpu_s': total_time, 'modules': sorted(set(modules)), 'removed': plan['removed']}
    json.dump(state, open(C.STATE, 'w'), indent=1)

    row = {
        'time': when,
        'proof_commit': commit,
        'label': a.label.replace(',', ';') + (' [review]' if v == 'review' else ''),
        'source_tokens': d['source_tokens']['after'],
        'written_out_size': d['written_out_size']['after'],
        'time_cpu_s': total_time,
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
