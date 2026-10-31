#!/usr/bin/env python3
"""Check that every name a reference proof mentions is unlocked in that level.

The Game Server rejects a proof that mentions a name the level has not unlocked, and the
rejection is easy to miss: the proof still elaborates, the info view reads *No goals*, and
the only sign is that the level never registers as completed. This reproduces the server's
rule offline, against the generated game data, so the whole game can be audited in seconds
instead of a browser run per level.

The rule, from `GameServer/Runner.lean:findForbiddenTactics`:

  * an **atom** starting with a letter is a tactic name unless it is one of a short list of
    keywords, and must appear unlocked in the level's `tactics`;
  * an **identifier** is checked only when it resolves to a theorem, and must then appear
    unlocked in the level's `lemmas`.

Identifier resolution is done by Lean itself (names can be ambiguous, and `open` matters),
so this needs `lake env lean` and a built game.

Run after `lake build`.
"""
import json, os, re, subprocess, sys, tempfile

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DATA = os.path.join(REPO, '.lake', 'gamedata')

# GameServer.ALLOWED_KEYWORDS — keywords the server does not treat as tactic names.
ALLOWED_KEYWORDS = {'with', 'fun', 'at', 'only', 'by', 'generalizing', 'using', 'skip',
                    'if', 'then', 'else', 'clear'}
# Syntax that reaches the parser as something other than a bare atom or identifier.
NOT_A_NAME = {'this', 'sorry'}


def proofs():
    out = subprocess.run([sys.executable, os.path.join(REPO, 'test', 'extract_proofs.py')],
                         capture_output=True, text=True, check=True)
    return json.loads(out.stdout)


NAME_RE = re.compile(r"(?<![\w.'])([A-Za-z][A-Za-z0-9_']*(?:\.[A-Za-z0-9_'?!]+)*)")
# What can stand immediately before a token that begins a tactic.
TACTIC_LEAD = re.compile(r"(?:^|<;>|·|;|\(|\||=>|\bby)\s*$")
# A field name in dot notation, after a closing bracket or after an identifier.
FIELD_RE = re.compile(r"(?:(?P<owner>[A-Za-z][A-Za-z0-9_'.]*)|[')\]])"
                      r"\.(?P<f>[A-Za-z][A-Za-z0-9_']*)")


def candidates(proof):
    """Every token in the proof that the server could read as a name, split by position.

    The server distinguishes a tactic from a term by syntax node kind, which a textual scan
    cannot see. What it can see is position: a token that begins a tactic is an atom, and
    anything else is an identifier. That separation matters because a name can be both —
    `trivial` is a tactic *and* the theorem `trivial : True`, and only its use as a term is
    checked against the theorem inventory.

    Returns (tactic_position, term_position, field_names). `field_names` maps a field to
    the dotted tokens it was taken from, so a suffix of a name that really resolves — the
    `le_add_right` in `Nat.le_add_right` — can be told from a genuine projection.
    """
    lead, term, fields = set(), set(), {}
    for line in proof.split('\n'):
        for m in NAME_RE.finditer(line):
            tok = m.group(1)
            if tok in ALLOWED_KEYWORDS or tok in NOT_A_NAME:
                continue
            (lead if TACTIC_LEAD.search(line[:m.start()]) else term).add(tok)
        # Dot notation. `(h).symm` and `ih.cons` are *projections*: Lean parses the field as
        # its own identifier, and the server resolves it on its own — which is how `symm`
        # gets rejected in a proof that never writes the name `Eq.symm`. A textual scan
        # cannot tell a projection from a qualified name, so every trailing component of a
        # dotted token is offered too; components that are not global constants resolve to
        # nothing and are ignored.
        for m in FIELD_RE.finditer(line):
            fields.setdefault(m.group('f'), set()).add(m.group('owner') or '')
    return sorted(lead), sorted(term), fields


def classify(names):
    """Ask Lean which of these names resolve to theorems, as the level files see them.

    The names are passed as a list of strings and resolved in a loop at run time. Splicing
    one `resolveGlobalConst` per name into the source instead makes a `do` block long enough
    to hit `maxRecDepth`, and names like `h.1` are parsed as projections rather than as the
    tokens the server would see.
    """
    lits = ', '.join('"' + n.replace('\\', '\\\\').replace('"', '\\"') + '"' for n in names)
    src = [
        'import Game',
        'open Cslib',
        'open Cslib.Algorithms.Lean (TimeM)',
        'open Lean Elab Command in',
        'run_cmd do',
        '  let env ← getEnv',
        f'  let names : List String := [{lits}]',
        '  for s in names do',
        '    let ns ← (try resolveGlobalConst (mkIdent s.toName) catch _ => pure [])',
        '    for m in ns do',
        '      if (env.find? m).any (·.isTheorem) then',
        '        logInfo s!"THEOREM {s} {m}"',
        '      else logInfo s!"OTHER {s} {m}"',
    ]
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
    theorems, resolvable = {}, set()
    for m in re.finditer(r'(THEOREM|OTHER) (\S+) (\S+)', out):
        resolvable.add(m.group(2))
        if m.group(1) == 'THEOREM':
            theorems.setdefault(m.group(2), set()).add(m.group(3))
    if not resolvable:
        print(out[-3000:], file=sys.stderr)
        sys.exit('name resolution produced nothing; the probe did not run')
    return theorems, resolvable


def main():
    levels = proofs()
    all_names = set()
    for d in levels:
        lead, term, fields = candidates(d['proof'])
        all_names |= set(lead) | set(term) | set(fields)
        for owners in fields.values():
            all_names |= {o for o in owners if o}
    theorems, resolvable = classify(sorted(all_names))

    failures = []
    for d in levels:
        where = f"{d['world']}/{d['level']}"
        path = os.path.join(DATA, f"level__{d['world']}__{d['level']}.json")
        if not os.path.isfile(path):
            failures.append(f'{where}: no generated level data; run `lake build`')
            continue
        data = json.load(open(path, encoding='utf-8'))
        tactics = {t['name']: t for t in (data.get('tactics') or [])}
        lemmas = {t['name']: t for t in (data.get('lemmas') or [])}

        def available(table, name):
            t = table.get(name)
            return bool(t) and not t.get('locked') and not t.get('disabled')

        lead, term, fields = candidates(d['proof'])
        # A field is a real projection unless every place it was written was a suffix of a
        # name that resolves on its own, in which case Lean parsed the whole thing as one
        # identifier and the suffix was never a name of its own.
        for f, owners in fields.items():
            if any(o == '' or o not in resolvable for o in owners):
                term.append(f)
        for name in lead:
            if '.' not in name and name in tactics and not available(tactics, name):
                failures.append(f'{where}: tactic "{name}" is not unlocked here')
        for name in term:
            resolved = theorems.get(name)
            if not resolved:
                continue
            # The server accepts the name if any resolution of it is unlocked.
            if not any(available(lemmas, m) for m in resolved):
                failures.append(
                    f'{where}: "{name}" is used as a term, resolves to the theorem '
                    f'{sorted(resolved)[0]}, and is not unlocked here')
        print(f'  {where:24} {len(lead):3d} tactic + {len(term):3d} term name(s)')

    print()
    for f in failures:
        print('FAIL:', f)
    print(f'{len(levels)} level(s) checked, {len(failures)} failure(s)')
    return 1 if failures else 0


if __name__ == '__main__':
    sys.exit(main())
