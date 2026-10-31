#!/usr/bin/env python3
"""Merge an existing translation into the regenerated template (like `msgmerge`).

When source text changes, `lake build` rewrites `.i18n/en/Game.pot` with new msgids. This
carries every translation whose source string is unchanged across to the new template and
leaves genuinely new or changed strings empty, so a translator sees exactly what needs work.

    python3 .i18n/tools/merge_po.py zh [--fill fills.json]

`--fill` is an optional {msgid: msgstr} JSON used to supply translations for strings that are
new in this round; it is the mechanism for keeping a changed paragraph translated in the same
commit that changes it.
"""
import json, os, sys

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


def parse(path):
    """Return (ordered entries, {msgid: msgstr}). An entry is (comment lines, msgid)."""
    blocks = open(path, encoding='utf-8').read().split('\n\n')
    entries, table = [], {}
    for b in blocks:
        if not b.strip():
            continue
        lines = b.split('\n')
        comments = [l for l in lines if l.startswith('#')]
        field, parts = None, {'msgid': [], 'msgstr': []}
        for l in lines:
            if l.startswith('msgid '):
                field = 'msgid'
                parts['msgid'].append(l[6:])
            elif l.startswith('msgstr '):
                field = 'msgstr'
                parts['msgstr'].append(l[7:])
            elif l.startswith('"') and field:
                parts[field].append(l)
        try:
            mid = ''.join(json.loads(p) for p in parts['msgid'] if p.startswith('"'))
            mstr = ''.join(json.loads(p) for p in parts['msgstr'] if p.startswith('"'))
        except json.JSONDecodeError:
            continue
        if not mid:
            continue
        entries.append((comments, mid))
        table[mid] = mstr
    return entries, table


def emit(s):
    if s == '':
        return '""'
    lines = s.split('\n')
    pieces = [l + '\n' for l in lines[:-1]] + ([lines[-1]] if lines[-1] else [])
    return '\n'.join(json.dumps(p, ensure_ascii=False) for p in pieces)


def main():
    lang = sys.argv[1]
    fills = {}
    if '--fill' in sys.argv:
        fills = json.load(open(sys.argv[sys.argv.index('--fill') + 1], encoding='utf-8'))
    pot = os.path.join(REPO, '.i18n', 'en', 'Game.pot')
    po = os.path.join(REPO, '.i18n', lang, 'Game.po')
    entries, _ = parse(pot)
    _, old = parse(po) if os.path.isfile(po) else ([], {})
    header = ('msgid ""\n'
              'msgstr "Project-Id-Version: Game v4.35.0\\n"\n'
              '"Report-Msgid-Bugs-To: \\n"\n'
              '"Last-Translator: \\n"\n'
              f'"Language-Team: {lang}\\n"\n'
              f'"Language: {lang}\\n"\n'
              '"Content-Type: text/plain; charset=UTF-8\\n"\n'
              '"Content-Transfer-Encoding: 8bit"\n')
    chunks, kept, filled, empty = [header], 0, 0, []
    for comments, mid in entries:
        tr = fills.get(mid) or old.get(mid, '')
        if mid in fills and fills[mid]:
            filled += 1
        elif tr:
            kept += 1
        else:
            empty.append(mid)
        chunks.append('\n'.join(comments + ['msgid ' + emit(mid), 'msgstr ' + emit(tr)]) + '\n')
    open(po, 'w', encoding='utf-8').write('\n'.join(chunks))
    print(f'{po}: {kept} carried over, {filled} newly filled, {len(empty)} untranslated')
    for m in empty:
        print('  untranslated:', repr(m[:70]))
    return 0


if __name__ == '__main__':
    sys.exit(main())
