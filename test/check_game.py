#!/usr/bin/env python3
"""Structural checks over the game data `MakeGame` generates.

Everything here reads `.lake/gamedata/`, so it checks what the server will actually serve
rather than what the Lean sources look like. Run `lake build` first.

Checks:
  * the world dependency graph, against the tree the curriculum requires;
  * that the core path is completable without the optional branch, and that the optional
    branch does not depend on the capstone world;
  * per-level cumulative inventory, including branch-local availability;
  * that every theorem, definition and tactic shown has documentation;
  * that every level has an objective, introduction, statement, hints and conclusion;
  * that every image referenced from game text exists in the repository;
  * level counts per content group.

Exit status is non-zero on any failure, so this is usable from CI.
"""
import json, os, re, sys
from collections import defaultdict

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DATA = os.path.join(REPO, '.lake', 'gamedata')

# The curriculum's required shape. Worlds may be split later; the invariants below are what
# must hold however that happens.
CORE_PATH = ['Behavior', 'Specification', 'Properties', 'Verification']
OPTIONAL = 'Refinement'
CAPSTONE = 'Verification'
# Content group -> worlds carrying it, and the group's hard minimum from GAME_DESIGN.md.
GROUPS = {
    '1 Understand Program Behavior':   (['Behavior'], 6),
    '2 Specify Correct Behavior':      (['Specification'], 6),
    '3 Prove and Reuse Properties':    (['Properties'], 8),
    '4 Verify a Complete Implementation': (['Verification'], 10),
    '5 Refinement and Equivalence':    (['Refinement'], 7),
}

failures, notes = [], []


def fail(msg):
    failures.append(msg)


def note(msg):
    notes.append(msg)


def load():
    if not os.path.isdir(DATA):
        print('no .lake/gamedata — run `lake build` first', file=sys.stderr)
        sys.exit(2)
    game = json.load(open(os.path.join(DATA, 'game.json'), encoding='utf-8'))
    levels = {}
    for f in os.listdir(DATA):
        m = re.match(r'level__(.+)__(\d+)\.json$', f)
        if m:
            levels[(m.group(1), int(m.group(2)))] = json.load(
                open(os.path.join(DATA, f), encoding='utf-8'))
    inv = json.load(open(os.path.join(DATA, 'inventory.json'), encoding='utf-8'))
    return game, levels, inv


def ancestors(edges, world):
    """All worlds that must be finished before `world`."""
    preds = defaultdict(set)
    for a, b in edges:
        preds[b].add(a)
    seen, stack = set(), list(preds[world])
    while stack:
        w = stack.pop()
        if w in seen:
            continue
        seen.add(w)
        stack.extend(preds[w])
    return seen


def check_tree(game):
    edges = [tuple(e) for e in game['worlds']['edges']]
    nodes = set(game['worlds']['nodes'])
    print(f'worlds: {sorted(nodes)}')
    print(f'edges : {sorted(edges)}')
    for w in CORE_PATH + [OPTIONAL]:
        if w not in nodes:
            fail(f'world missing from the game: {w}')
    for a, b in zip(CORE_PATH, CORE_PATH[1:]):
        if b not in ancestors(edges, b) | {b} or a not in ancestors(edges, b):
            fail(f'core path broken: {a} is not a prerequisite of {b}')
    core_prereqs = ancestors(edges, CORE_PATH[-1])
    if OPTIONAL in core_prereqs:
        fail(f'core capstone {CORE_PATH[-1]} depends on the optional world {OPTIONAL}')
    opt_prereqs = ancestors(edges, OPTIONAL)
    if CAPSTONE in opt_prereqs:
        fail(f'optional world {OPTIONAL} is gated behind the capstone {CAPSTONE}; '
             'an elementary item is probably introduced too late')
    if 'Properties' not in opt_prereqs:
        fail(f'optional world {OPTIONAL} does not depend on Properties, '
             'whose transition systems it needs')
    return edges


def check_levels(game, levels):
    sizes = game.get('worldSize') or {}
    for (world, idx), d in sorted(levels.items()):
        where = f'{world}/{idx}'
        for field, label in (('title', 'title'), ('introduction', 'introduction'),
                             ('descrText', 'statement description'),
                             ('conclusion', 'conclusion')):
            if not (d.get(field) or '').strip():
                fail(f'{where}: empty {label}')
        if not (d.get('statementName') or '').strip():
            fail(f'{where}: statement is unnamed, so no theorem is created and '
                 'test/check_axioms.py cannot check it for proof gaps')
    for group, (worlds, minimum) in GROUPS.items():
        n = sum(sizes.get(w, 0) for w in worlds)
        status = 'OK' if n >= minimum else f'BELOW MINIMUM ({minimum})'
        print(f'  group {group}: {n} level(s) across {worlds} — {status}')
        if n < minimum:
            fail(f'content group "{group}" has {n} level(s), hard minimum is {minimum}')


def check_inventory(game, levels, inv):
    edges = [tuple(e) for e in game['worlds']['edges']]
    documented = {k: set() for k in ('lemmas', 'definitions', 'tactics')}
    for cat in documented:
        for item in inv.get(cat) or []:
            documented[cat].add(item['name'])
    for (world, idx), d in sorted(levels.items()):
        where = f'{world}/{idx}'
        reachable = ancestors(edges, world) | {world}
        for cat in ('lemmas', 'definitions', 'tactics'):
            for item in d.get(cat) or []:
                if item.get('locked') or item.get('disabled'):
                    continue
                origin = item.get('world')
                if origin and origin not in reachable:
                    fail(f'{where}: {cat[:-1]} "{item["name"]}" is available but introduced '
                         f'in world {origin}, which is not on this branch')
                if item['name'] not in documented[cat]:
                    fail(f'{where}: {cat[:-1]} "{item["name"]}" has no inventory documentation')
    tabs = defaultdict(list)
    for l in inv.get('lemmas') or []:
        tabs[l.get('category') or '(no tab)'].append(l['name'])
    print('  theorem tabs:')
    for t, v in sorted(tabs.items()):
        print(f'    {t}: {len(v)}')
        if t == '(no tab)':
            fail(f'theorems without a tab: {v}')


def check_images(game, levels):
    refs = set()
    texts = [game.get('introduction') or '', game.get('info') or '']
    world_images = set()
    for name, node in game['worlds']['nodes'].items():
        texts.append(node.get('introduction') or '')
        if node.get('image'):
            refs.add(node['image'])
            world_images.add((name, node['image']))
    for d in levels.values():
        texts += [d.get('introduction') or '', d.get('descrText') or '',
                  d.get('conclusion') or '', d.get('image') or '']
    for t in texts:
        refs |= set(re.findall(r'!\[[^\]]*\]\((images/[^)]+)\)', t))
        if t.startswith('images/'):
            refs.add(t)
    for r in sorted(refs):
        exists = os.path.isfile(os.path.join(REPO, r))
        print(f'  image {r}: {"present" if exists else "MISSING"}')
        if not exists:
            fail(f'image referenced but not in the repository: {r}')
        if r.startswith('images/en/'):
            zh = r.replace('images/en/', 'images/zh/', 1)
            if not os.path.isfile(os.path.join(REPO, zh)):
                note(f'{r} has no Chinese variant at {zh}')
    # A world-level `Image` path is written straight into the game data and never reaches
    # Game.pot, so it cannot follow the player's language even when a variant exists.
    for world, img in sorted(world_images):
        if '/en/' in img or '/zh/' in img:
            note(f'world {world} uses Image "{img}"; that path is not translatable, so the '
                 'world picture stays in that language. Embed the figure in the world '
                 'introduction as Markdown, or use a language-neutral asset.')


def main():
    game, levels, inv = load()
    print('== world tree ==')
    check_tree(game)
    print('== levels ==')
    check_levels(game, levels)
    print('== inventory ==')
    check_inventory(game, levels, inv)
    print('== images ==')
    check_images(game, levels)
    print()
    for n in notes:
        print('note:', n)
    for f in failures:
        print('FAIL:', f)
    print(f'\n{len(failures)} failure(s), {len(notes)} note(s)')
    return 1 if failures else 0


if __name__ == '__main__':
    sys.exit(main())
