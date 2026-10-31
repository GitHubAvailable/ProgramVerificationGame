#!/usr/bin/env python3
"""Check that every level's reference solution rests only on Lean's standard axioms.

`Statement <name> …` elaborates the reference proof into a real theorem, so the kernel's own
axiom tracking answers the question directly. Anything beyond `propext`, `Classical.choice`
and `Quot.sound` — in particular `sorryAx`, which is what a `sorry`, an `admit` or a failed
`Template` hole leaves behind — is a proof gap.

Run after `lake build`.
"""
import json, os, re, subprocess, sys, tempfile

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def level_names():
    out = subprocess.run([sys.executable, os.path.join(REPO, 'test', 'extract_proofs.py')],
                         capture_output=True, text=True, check=True)
    levels = json.loads(out.stdout)
    missing = [f"{d['world']}/{d['level']}" for d in levels if not d['name']]
    return [(f"{d['world']}/{d['level']}", d['name']) for d in levels if d['name']], missing


def main():
    names, unnamed = level_names()
    if unnamed:
        print('cannot check (the Statement is unnamed, so no theorem is created): ' + ', '.join(unnamed))
    src = ['import Game'] + [f'#print axioms {n}' for _, n in names]
    with tempfile.NamedTemporaryFile('w', suffix='.lean', dir=REPO, delete=False,
                                     encoding='utf-8') as f:
        f.write('\n'.join(src) + '\n')
        path = f.name
    try:
        r = subprocess.run(['lake', 'env', 'lean', path], cwd=REPO,
                           capture_output=True, text=True)
    finally:
        os.unlink(path)
    out = r.stdout + r.stderr
    failures = []
    seen = set()
    for line in out.splitlines():
        m = re.match(r"'(\S+)' depends on axioms: \[(.*)\]", line.strip())
        if m:
            name, axioms = m.group(1), {a.strip() for a in m.group(2).split(',') if a.strip()}
            seen.add(name)
            extra = axioms - STANDARD
            print(f'  {name}: {sorted(axioms) or "no axioms"}'
                  + (f'  <-- NOT STANDARD: {sorted(extra)}' if extra else ''))
            if extra:
                failures.append(f'{name} depends on {sorted(extra)}')
        elif re.match(r"'(\S+)' does not depend on any axioms", line.strip()):
            name = re.match(r"'(\S+)'", line.strip()).group(1)
            seen.add(name)
            print(f'  {name}: no axioms')
    for key, n in names:
        if n not in seen:
            failures.append(f'{key}: no axiom report for {n} (did the build succeed?)')
    if r.returncode != 0 and not seen:
        print(out[-2000:], file=sys.stderr)
    print()
    for f_ in failures:
        print('FAIL:', f_)
    print(f'{len(seen)} reference solution(s) checked, {len(failures)} failure(s)')
    return 1 if failures or unnamed else 0


if __name__ == '__main__':
    sys.exit(main())
