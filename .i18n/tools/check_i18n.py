#!/usr/bin/env python3
"""Validate the game's translations against the English template.

Checks, for every locale under `.i18n/` that has a `Game.po`:

* coverage — how many of the template's strings carry a translation;
* placeholder integrity — every `§n` the Game Server substitutes reappears, exactly as
  often, in the translation;
* Markdown structure — the number of image references and code fences is preserved;
* asset existence — every image a translation points at is actually in the repository,
  which is what catches a localised figure whose `images/<lang>/` variant was never added;
* glossary consistency — terms listed in `.i18n/<lang>/glossary.csv` are rendered with the
  agreed wording wherever the English term appears in the source string.

Exit status is non-zero if any check fails, so this is usable from CI.
"""
import csv, json, os, re, sys

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def parse_po(path):
    """Return a list of (msgid, msgstr) with PO string literals decoded."""
    entries, cur, field = [], {'msgid': [], 'msgstr': []}, None
    for line in open(path, encoding='utf-8'):
        line = line.rstrip('\n')
        if line.startswith('msgid '):
            if cur['msgid'] or cur['msgstr']:
                entries.append(cur)
            cur, field = {'msgid': [line[6:]], 'msgstr': []}, 'msgid'
        elif line.startswith('msgstr '):
            field = 'msgstr'
            cur['msgstr'] = [line[7:]]
        elif line.startswith('"') and field:
            cur[field].append(line)
        elif not line.strip():
            field = None
    if cur['msgid'] or cur['msgstr']:
        entries.append(cur)
    out = []
    for e in entries:
        try:
            mid = ''.join(json.loads(p) for p in e['msgid'] if p.startswith('"'))
            mstr = ''.join(json.loads(p) for p in e['msgstr'] if p.startswith('"'))
        except json.JSONDecodeError:
            continue
        if mid:
            out.append((mid, mstr))
    return out


def placeholders(s):
    return sorted(re.findall(r'§\d+', s))


def images(s):
    return re.findall(r'!\[[^\]]*\]\(([^)]+)\)', s)


def load_glossary(path):
    if not os.path.isfile(path):
        return []
    with open(path, encoding='utf-8') as f:
        rows = list(csv.DictReader(f))
    # Terms flagged `polysemous` are ordinary English words elsewhere in the prose, so a
    # source string containing one says nothing about whether the term was used at all.
    return [(r['en'].strip(), r['zh'].strip()) for r in rows
            if r.get('en') and r.get('zh')
            and 'polysemous' not in (r.get('note') or '')]


def check_locale(lang, template_entries):
    po = os.path.join(REPO, '.i18n', lang, 'Game.po')
    table = dict(parse_po(po))
    glossary = load_glossary(os.path.join(REPO, '.i18n', lang, 'glossary.csv'))
    problems, translated = [], 0
    for src, _ in template_entries:
        tr = table.get(src, '')
        if not tr:
            problems.append(f'untranslated: {src[:60]!r}')
            continue
        translated += 1
        if placeholders(src) != placeholders(tr):
            problems.append(
                f'placeholder mismatch in {src[:40]!r}: {placeholders(src)} vs {placeholders(tr)}')
        if len(images(src)) != len(images(tr)):
            problems.append(f'image-reference count differs in {src[:40]!r}')
        for img in images(tr):
            if not os.path.isfile(os.path.join(REPO, img)):
                problems.append(f'translated image asset missing: {img}')
        if src.count('```') != tr.count('```'):
            problems.append(f'code-fence count differs in {src[:40]!r}')
        for en, zh in glossary:
            if re.search(r'\b' + re.escape(en) + r'\b', src, re.I) and zh not in tr:
                # Only a warning-level signal: a sentence may legitimately paraphrase.
                problems.append(f'glossary: {src[:40]!r} uses "{en}" but translation lacks "{zh}"')
    return translated, problems


def main():
    template = parse_po(os.path.join(REPO, '.i18n', 'en', 'Game.pot'))
    template = [e for e in template if e[0]]
    print(f'template: {len(template)} strings')
    strict = '--strict-glossary' in sys.argv
    failed = False
    for lang in sorted(os.listdir(os.path.join(REPO, '.i18n'))):
        if not os.path.isfile(os.path.join(REPO, '.i18n', lang, 'Game.po')):
            continue
        n, problems = check_locale(lang, template)
        hard = [p for p in problems if not p.startswith('glossary:')]
        soft = [p for p in problems if p.startswith('glossary:')]
        print(f'{lang}: {n}/{len(template)} translated, '
              f'{len(hard)} problem(s), {len(soft)} glossary note(s)')
        for p in hard:
            print('  FAIL', p)
        for p in soft:
            print('  note', p)
        if hard or (strict and soft):
            failed = True
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())
