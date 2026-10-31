#!/usr/bin/env python3
"""Extract each level's player-facing reference proof from its Lean source.

The `Statement` block of a level contains the reference proof interleaved with `Hint`
tactics, which the Game Server shows to the player but the player never types. Stripping the
hints leaves exactly the proof script a player has to produce, which is what the in-game test
harness types into the editor.

Prints JSON: a list of {world, level, name, proof} in world/level order.
"""
import json, os, re, sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEVELS = os.path.join(REPO, 'Game', 'Levels')


def strip_string_literal(src, i):
    """Given index i at an opening quote, return the index just past the closing quote."""
    i += 1
    while i < len(src):
        if src[i] == '\\':
            i += 2
            continue
        if src[i] == '"':
            return i + 1
        i += 1
    raise ValueError('unterminated string literal')


def strip_hints(proof):
    """Remove `Hint "..."` tactics (and their trailing newline) from a proof script."""
    out, i = [], 0
    while i < len(proof):
        m = re.compile(r'[ \t]*Hint(?:\s*\([^)]*\))?\s*"').match(proof, i)
        if m:
            j = strip_string_literal(proof, m.end() - 1)
            while j < len(proof) and proof[j] in ' \t':
                j += 1
            if j < len(proof) and proof[j] == '\n':
                j += 1
            i = j
            continue
        out.append(proof[i])
        i += 1
    return ''.join(out)


def rejoin_bullets(proof):
    """Repair focus dots whose body was a `Hint` on the same line.

    `· Hint "..."` followed by the real tactic one line down becomes a bare `·` once the hint
    is stripped. Re-attach the next line so the bullet body keeps the column it had in the
    source, which is what Lean's whitespace-sensitive block structure depends on.
    """
    proof = re.sub(r'(?m)^([ \t]*·)[ \t]*\n[ \t]*', r'\1 ', proof)
    return re.sub(r'(?m)^([ \t]*·)[ \t]{2,}', r'\1 ', proof)


def dedent(block):
    lines = [l for l in block.split('\n')]
    widths = [len(l) - len(l.lstrip()) for l in lines if l.strip()]
    if not widths:
        return block
    pad = min(widths)
    return '\n'.join(l[pad:] if l.strip() else '' for l in lines)


def parse_level(path):
    src = open(path, encoding='utf-8').read()
    world = re.search(r'^World "([^"]+)"', src, re.M).group(1)
    level = int(re.search(r'^Level (\d+)', src, re.M).group(1))
    m = re.search(r'^Statement\s+(\S+)?', src, re.M)
    name = m.group(1) if m and not m.group(1).startswith('(') else None
    start = src.index(':= by', m.start()) + len(':= by')
    # The proof runs until the next top-level command.
    end = len(src)
    for cmd in ('\nConclusion', '\nNewTactic', '\nNewTheorem', '\nNewDefinition',
                '\nTheoremTab', '\nNewHiddenTactic', '\nOnlyTactic', '\nDisabledTactic'):
        k = src.find(cmd, start)
        if k != -1:
            end = min(end, k)
    proof = rejoin_bullets(strip_hints(src[start:end])).strip('\n')
    return {'world': world, 'level': level, 'name': name,
            'proof': dedent(proof).strip('\n'), 'file': os.path.relpath(path, REPO)}


def main():
    levels = []
    for root, _, files in os.walk(LEVELS):
        for f in sorted(files):
            if f.endswith('.lean') and re.match(r'L\d+', f):
                levels.append(parse_level(os.path.join(root, f)))
    levels.sort(key=lambda d: (d['world'], d['level']))
    json.dump(levels, sys.stdout, ensure_ascii=False, indent=1)
    print()


if __name__ == '__main__':
    main()
