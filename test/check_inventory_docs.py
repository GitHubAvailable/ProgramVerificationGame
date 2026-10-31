#!/usr/bin/env python3
"""Open an inventory entry in each locale and record the documentation that renders.

The inventory is a learning reference, so its entries have to be translated too — and a
`TheoremDoc`/`DefinitionDoc`/`TacticDoc` body only appears once the player clicks the item,
which neither the build nor the generated game data can show. This opens one entry per tab in
each language and saves what the panel displays.

Usage: python3 test/check_inventory_docs.py [--base URL] [--out DIR]

Requires the Game Server running locally (see README) and Playwright with Chromium.
"""
import argparse, asyncio, json, os, sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(REPO, 'test'))
DEFAULT_BASE = "http://localhost:3000/#/g/local/ProgramVerificationGame"

# One entry per tab, chosen so the body is unmistakably prose rather than a bare signature,
# with the sub-tab (category) it is filed under. Theorems and definitions are grouped, and the
# page opens on whichever sub-tab the level or the inventory order picks, so the category is
# clicked explicitly. Category names are not translated, so they are the same in every locale.
TARGETS = [('Tactics', None, 'induction'),
           ('Definitions', 'States & Transitions', 'mtr'),
           ('Theorems', 'Invariants', 'mtrInv_of_trInv')]
TAB_LABEL = {
    'en': {'Tactics': 'Tactics', 'Definitions': 'Definitions', 'Theorems': 'Theorems'},
    'zh': {'Tactics': '策略', 'Definitions': '定义', 'Theorems': '定理'},
}


def has_chinese(text):
    return any('一' <= c <= '鿿' for c in text)


async def main():
    from play_levels import seed_language
    from playwright.async_api import async_playwright

    ap = argparse.ArgumentParser()
    ap.add_argument('--base', default=DEFAULT_BASE)
    ap.add_argument('--out', default=os.path.join(REPO, 'test', 'results'))
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)

    results, failures = [], []
    async with async_playwright() as b_pw:
        b = await b_pw.chromium.launch()
        for lang in ('en', 'zh'):
            for tab, category, item in TARGETS:
                # Opening an entry replaces the item list with the documentation panel, so
                # each entry gets a fresh page rather than navigating back out of it.
                ctx = await b.new_context(viewport={'width': 1600, 'height': 1000})
                await seed_language(ctx, lang)
                pg = await ctx.new_page()
                # By World 3 all three tabs have entries. Wait on `domcontentloaded` plus a
                # fixed delay rather than `networkidle`: the level keeps a Lean session open,
                # so the network never goes quiet and `networkidle` can hang indefinitely.
                await pg.goto('about:blank')
                await pg.goto(f"{args.base}/world/Properties/level/1",
                              wait_until='domcontentloaded')
                await pg.wait_for_timeout(12000)
                label = TAB_LABEL[lang][tab]
                try:
                    await pg.get_by_text(label, exact=True).first.click(timeout=15000)
                    await pg.wait_for_timeout(800)
                    if category:
                        await pg.locator('.inventory-panel .tab-bar:not(.major)').get_by_text(
                            category, exact=True).first.click(timeout=15000)
                        await pg.wait_for_timeout(800)
                    await pg.locator('.inventory-list').get_by_text(
                        item, exact=True).first.click(timeout=15000)
                    await pg.wait_for_timeout(1200)
                    doc = await pg.locator('.documentation').first.inner_text()
                except Exception as e:  # noqa: BLE001 - report, do not abort the sweep
                    failures.append(f'{lang}/{tab}: could not open "{item}" ({type(e).__name__})')
                    await ctx.close()
                    continue
                await pg.screenshot(path=os.path.join(args.out, f'inventory-{lang}-{tab}.png'),
                                    full_page=True)
                cjk = has_chinese(doc)
                results.append({'lang': lang, 'tab': tab, 'item': item,
                                'contains_chinese': cjk, 'text': doc[:600]})
                print(f'{lang} {tab:12} {item:12} chinese={cjk} :: '
                      f'{doc[:70].replace(chr(10), " ")}', flush=True)
                if lang == 'zh' and not cjk:
                    failures.append(f'zh/{tab}: documentation for "{item}" rendered no Chinese')
                if lang == 'en' and cjk:
                    failures.append(f'en/{tab}: documentation for "{item}" rendered Chinese')
                await ctx.close()
        await b.close()

    json.dump(results, open(os.path.join(args.out, 'inventory_docs.json'), 'w'),
              ensure_ascii=False, indent=1)
    print()
    for f in failures:
        print('FAIL:', f)
    print(f'{len(results)} inventory entries rendered, {len(failures)} failure(s)')
    return 1 if failures else 0


if __name__ == '__main__':
    sys.exit(asyncio.run(main()))
