#!/usr/bin/env python3
"""Play every level in a real browser against a locally running Game Server.

This is the in-game test: it drives Chromium through the same UI a player uses, types each
level's reference proof into the editor, and records whether the server reports the level
completed. A `lake build` cannot establish this — the proof must succeed against the exact
statement the player sees, with only the inventory that level unlocks.

It also records which image assets each locale actually requests, which is the only reliable
way to tell whether a localised diagram really switches.

Usage:
    python3 test/play_levels.py [--base URL] [--out DIR] [--headed]

Requires the Game Server running locally (see README) and Playwright with Chromium.
"""
import argparse, asyncio, json, os, subprocess, sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEFAULT_BASE = "http://localhost:3000/#/g/local/ProgramVerificationGame"
LOAD_MS = 9000
POLL_MS = 2000
POLL_TRIES = 45


def reference_proofs():
    out = subprocess.run([sys.executable, os.path.join(REPO, 'test', 'extract_proofs.py')],
                         capture_output=True, text=True, check=True)
    return json.loads(out.stdout)


async def goto_level(pg, base, world, level):
    url = f"{base}/world/{world}/level/{level}"
    # Levels differ only in the URL fragment, and a hash-only navigation does not reload the
    # page: the single-page app swaps the route, but the Lean session attached to the editor
    # is not reinitialised and the level sits there with a dead editor. Go elsewhere first so
    # the next navigation is a real load.
    await pg.goto('about:blank')
    # Wait on `domcontentloaded` plus a fixed delay, never `networkidle`: a level keeps a Lean
    # session open, so the network never goes quiet and `networkidle` can hang until the
    # navigation timeout with nothing to show for it.
    await pg.goto(url, wait_until='domcontentloaded')
    await pg.wait_for_timeout(LOAD_MS)


PREFERENCES_KEY = 'preferences'


def preferences(lang, layout='auto'):
    """The client's `preferences` localStorage record, as the Preferences dialog writes it."""
    return json.dumps({
        'layout': layout,
        'isSavePreferences': True,
        'language': lang,
        'isSuggestionsMobileMode': True,
        'useFlags': False,
        'showLockedInventory': True,
    })


async def seed_language(ctx, lang, layout='auto'):
    """Choose the language the way the Preferences dialog does, before the app boots.

    The client has no language detector and reads the choice from `localStorage`, so it has
    to be in place before the page scripts run; setting it afterwards would need a reload
    anyway. `add_init_script` runs on every navigation in the context.
    """
    await ctx.add_init_script(
        f"window.localStorage.setItem({PREFERENCES_KEY!r}, {preferences(lang, layout)!r})")


async def read_inventory(pg, timeout_ms=6000):
    """Read the inventory panel as the player sees it, tab by tab.

    Each entry is a `div.item` inside `div.inventory-list` whose class carries the state:
    `locked` for an item from a world this branch has not reached, `disabled` for one the
    level switches off, `new` for one this level introduces. Reading the classes is what
    turns the panel into evidence about cumulative and branch-local unlock, rather than a
    list of names that says nothing about availability.

    Everything is bounded and non-fatal. The panel is a secondary record — the level result
    must not be lost because a tab did not become clickable — and the whole tab is read in
    one `evaluate_all` rather than a round trip per item.
    """
    inventory = {}
    for tab in ('Theorems', 'Tactics', 'Definitions'):
        try:
            await pg.get_by_text(tab, exact=True).first.click(timeout=timeout_ms)
            await pg.wait_for_timeout(500)
            rows = await pg.locator('.inventory-list .item').evaluate_all(
                "els => els.map(e => [e.className, e.innerText.trim()])")
        except Exception as e:  # noqa: BLE001 - record the gap, keep the level result
            inventory[tab] = {'error': type(e).__name__}
            continue
        state = {'available': [], 'locked': [], 'disabled': []}
        for cls, name in rows:
            if not name:
                continue
            if 'locked' in cls:
                state['locked'].append(name)
            elif 'disabled' in cls:
                state['disabled'].append(name)
            else:
                state['available'].append(name)
        inventory[tab] = state
    return inventory


async def play_level(pg, base, world, level, proof, outdir):
    await goto_level(pg, base, world, level)
    if await pg.locator('button[title="Editor mode"]').count():
        await pg.locator('button[title="Editor mode"]').click()
        await pg.wait_for_timeout(3000)
    # Paste rather than type: Monaco re-indents inserted text, which compounds with the
    # proof's own indentation and silently changes the block structure Lean depends on.
    # A clipboard paste is inserted verbatim.
    await pg.evaluate("t => navigator.clipboard.writeText(t)", proof)
    await pg.locator('.monaco-editor').first.click()
    await pg.keyboard.press('Control+A')
    await pg.keyboard.press('Delete')
    await pg.keyboard.press('Control+V')
    completed = False
    for _ in range(POLL_TRIES):
        await pg.wait_for_timeout(POLL_MS)
        body = await pg.locator('body').inner_text()
        if 'level completed' in body.lower():
            completed = True
            break
    body = await pg.locator('body').inner_text()
    # Whether the paste landed is read off the screenshot rather than from the DOM: Monaco
    # renders a virtualised, token-split view whose `inner_text` does not reliably contain
    # the proof as written.
    await pg.screenshot(path=os.path.join(outdir, f'play-{world}-{level}.png'), full_page=True)
    diag = [l.strip() for l in body.split('\n')
            if 'error' in l.lower() or 'sorry' in l.lower()][:5]
    # Record the exercise exactly as the page showed it, so a later reader can match this
    # result against the level source instead of trusting that it was current.
    statement_shown = ''
    if await pg.locator('.exercise').count():
        statement_shown = (await pg.locator('.exercise').first.inner_text()).strip()
    inventory = await read_inventory(pg)
    return {'completed': completed, 'diagnostics': diag,
            'statement_shown': statement_shown, 'proof_pasted': proof,
            'inventory_visible': inventory}


async def locale_render(pg, base, world, level, lang, outdir, viewport_tag=''):
    """Load a level in `lang` and report the text and image assets actually rendered."""
    requested = []
    pg.on('request', lambda r: requested.append(r.url) if '/images/' in r.url else None)
    await goto_level(pg, base, world, level)
    await pg.wait_for_timeout(2500)
    body = await pg.locator('body').inner_text()
    imgs = await pg.locator('img').evaluate_all("els => els.map(e => e.getAttribute('src'))")
    name = f'locale-{lang}-{world}-{level}{viewport_tag}.png'
    await pg.screenshot(path=os.path.join(outdir, name), full_page=True)
    return {
        'lang': lang,
        'img_src_in_dom': [i for i in imgs if i],
        'image_requests': sorted(set(u.split('/images/')[-1] for u in requested)),
        'body_sample': body[:400],
        'screenshot': name,
    }


async def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--base', default=DEFAULT_BASE)
    ap.add_argument('--out', default=os.path.join(REPO, 'test', 'results'))
    ap.add_argument('--headed', action='store_true')
    ap.add_argument('--locales-only', action='store_true',
                    help='skip playing levels; only record per-locale rendering')
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)

    from playwright.async_api import async_playwright
    levels = reference_proofs()
    results = {'levels': {}, 'locales': [], 'mobile': []}
    out_name = 'locale_results.json' if args.locales_only else 'play_results.json'
    out_path = os.path.join(args.out, out_name)

    def save():
        json.dump(results, open(out_path, 'w'), ensure_ascii=False, indent=1)

    async with async_playwright() as p:
        b = await p.chromium.launch(headless=not args.headed)
        ctx = await b.new_context(viewport={'width': 1600, 'height': 1000},
                                  permissions=['clipboard-read', 'clipboard-write'])
        pg = await ctx.new_page()
        for d in ([] if args.locales_only else levels):
            key = f"{d['world']}/{d['level']}"
            r = await play_level(pg, args.base, d['world'], d['level'], d['proof'], args.out)
            results['levels'][key] = r
            print(f"{key:24} completed={r['completed']} diagnostics={r['diagnostics']}", flush=True)
            save()
        # Each level leaves a Lean session open on the server. Close the browser that played
        # them before opening any more pages: carrying a dozen live sessions into the locale
        # pass makes the next navigation hang with nothing to show for it.
        await pg.close()
        await ctx.close()
        await b.close()
        b = await p.chromium.launch(headless=not args.headed)
        # Localised rendering, desktop
        for world, level in (('Behavior', 1), ('Refinement', 1)):
            for lang in ('en', 'zh'):
                lctx = await b.new_context(viewport={'width': 1600, 'height': 1000})
                await seed_language(lctx, lang)
                pg2 = await lctx.new_page()
                r = await locale_render(pg2, args.base, world, level, lang, args.out)
                r['world'], r['level'] = world, level
                results['locales'].append(r)
                print(f"locale {lang} {world}/{level}: images={r['image_requests']}", flush=True)
                save()
                await pg2.close()
                await lctx.close()
        # Mobile viewport
        for lang in ('en', 'zh'):
            mctx = await b.new_context(viewport={'width': 390, 'height': 844},
                                       is_mobile=True, has_touch=True,
                                       device_scale_factor=3,
                                       user_agent=('Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X) '
                                                   'AppleWebKit/605.1.15 (KHTML, like Gecko) '
                                                   'Version/17.0 Mobile/15E148 Safari/604.1'))
            await seed_language(mctx, lang, layout='mobile')
            pgm = await mctx.new_page()
            r = await locale_render(pgm, args.base, 'Behavior', 1, lang, args.out, '-mobile')
            results['mobile'].append(r)
            print(f"mobile {lang}: images={r['image_requests']}", flush=True)
            save()
            await pgm.close()
            await mctx.close()
        await b.close()

    save()
    failed = [k for k, v in results['levels'].items() if not v['completed']]
    print(f"\n{len(results['levels']) - len(failed)}/{len(results['levels'])} levels completed in-game")
    if failed:
        print('NOT COMPLETED:', failed)
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(asyncio.run(main()))
