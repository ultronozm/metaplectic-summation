#!/usr/bin/env node
// Validate the built page the way a reader meets it: opened from disk in Chrome, with default security settings.
//
//   node portable/check/check.mjs [page.html] [--shots DIR]
//
// It checks that the file is self-contained and complete (every sketch, in the order of the paper, every reference
// target), that it makes no network request, that all formulas typeset, that every reference opens the right place
// in the paper and that Esc, Back, and the Sketch button return to the reader's place, that every Lean link opens its
// row of the appendix and that row links to the source, that every fold (figures and proofs) opens, that failures are
// shown on the page rather than swallowed, and that nothing overflows at laptop, narrow-window, and phone widths.
// Exit status 1 if anything fails.  Adapted from the check of ~/work/effective-nelson-venkatesh/portable.
import { readFileSync, mkdirSync, writeFileSync, rmSync } from 'node:fs';
import { execFileSync } from 'node:child_process';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { launch } from './browser.mjs';

const here = path.dirname(fileURLToPath(import.meta.url));
const root = path.resolve(here, '../..');
const args = process.argv.slice(2);
const shotsAt = args.includes('--shots') ? args[args.indexOf('--shots') + 1] : path.join(root, 'build/portable/check');
const target = path.resolve(args.find((a, i) => !a.startsWith('--') && args[i - 1] !== '--shots') || path.join(root, 'output/html/metaplectic-sketches.html'));
mkdirSync(shotsAt, { recursive: true });

const results = [];
function record(ok, name, detail = '') {
  results.push({ ok, name, detail });
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${name}${detail ? '  ' + detail : ''}`);
}
async function check(name, fn) {
  try {
    const detail = await fn();
    record(detail === false ? false : true, name, typeof detail === 'string' ? detail : '');
  } catch (error) {
    record(false, name, String(error.message || error).split('\n')[0]);
  }
}

const html = readFileSync(target, 'utf8');
const sketchesTex = readFileSync(path.join(root, 'sketches.tex'), 'utf8');
const wanted = [...sketchesTex.matchAll(/\\begin\{sketch\}\[([^\]]*)\]/g)].map((m) => m[1]);

// ---------------------------------------------------------------- the file itself

// The markup outside the scripts and the styles: what the browser would fetch from elsewhere is found here.
const markup = html.replace(/<script\b[^>]*>[\s\S]*?<\/script>/gi, '<script></script>').replace(/<style\b[^>]*>[\s\S]*?<\/style>/gi, '<style></style>');
const styles = [...html.matchAll(/<style\b[^>]*>([\s\S]*?)<\/style>/gi)].map((m) => m[1]).join('\n');
await check('self-contained: no external scripts, styles, images, or links', () => {
  const bad = [...markup.matchAll(/<(script|link|img|iframe|source|audio|video|embed|object)\b[^>]*\b(src|href|data)=["'](?!#|data:|blob:)[^"']*/gi)].map((m) => m[0].slice(0, 80));
  const css = [...styles.matchAll(/(@import|url\()\s*["']?(?!data:|#)[^)"']+/g)].map((m) => m[0].slice(0, 80));
  // Links that a reader follows to a web page (the Lean sources, URLs cited in the paper) are allowed; nothing else.
  const anchors = [...markup.matchAll(/<a\b[^>]*\bhref=["'](?!#|https:\/\/)[^"']*/gi)].map((m) => m[0].slice(0, 80));
  if (bad.length || css.length || anchors.length) throw new Error('external references: ' + [...bad, ...css, ...anchors].slice(0, 3).join(' | '));
  const hosts = [...new Set([...markup.matchAll(/href="https:\/\/([a-z0-9.-]+)/gi)].map((m) => m[1]))];
  return `${(html.length / 1e6).toFixed(1)} MB; outbound links to: ${hosts.join(', ') || 'none'}`;
});
await check('every sketch of sketches.tex is in the page, in the order of the paper', () => {
  const ids = [...html.matchAll(/<article class="sketch [^"]*" id="s:([^"]*)"/g)].map((m) => m[1]);
  const missing = wanted.filter((l) => !ids.includes(l)), extra = ids.filter((l) => !wanted.includes(l));
  if (missing.length || extra.length) throw new Error(`missing ${missing.join(',')} extra ${extra.join(',')}`);
  const positions = ids.map((l) => (l === 'document' ? -1 : html.indexOf(`id="p:${l}"`)));
  if (positions.some((p, i) => p < 0 && ids[i] !== 'document')) throw new Error('a sketch target is not in the paper');
  const sorted = positions.every((p, i) => i === 0 || p > positions[i - 1]);
  if (!sorted) throw new Error('order differs from the order of the targets in the page');
  return `${ids.length} sketches`;
});
await check('every reference and link has a target in the page', () => {
  const ids = new Set([...markup.matchAll(/\sid="([^"]+)"/g)].map((m) => m[1]));
  const links = [...markup.matchAll(/href="#([^"]+)"/g)].map((m) => m[1]).map((l) => l.replace(/&amp;/g, '&'));
  const broken = [...new Set(links.filter((l) => !ids.has(l)))];
  if (broken.length) throw new Error('no target for ' + broken.slice(0, 5).join(', '));
  return `${links.length} links`;
});
await check('no unfilled template slots; licenses present', () => {
  if (/\{\{[A-Z_]+\}\}/.test(html)) throw new Error('unfilled slot');
  for (const word of ['Khan Academy', 'SIL OPEN FONT LICENSE', 'Permission is hereby granted']) if (!html.includes(word)) throw new Error('license text missing: ' + word);
});

// ---------------------------------------------------------------- the page in a browser

const url = pathToFileURL(target).href;
const page = await launch({ width: 1440, height: 900 });
await page.send('Network.emulateNetworkConditions', { offline: true, latency: 0, downloadThroughput: 0, uploadThroughput: 0 });
await page.open(url);
await page.waitFor("document.documentElement.dataset.ready === '1'", { timeout: 30000 });
const quiet = () => page.log.exceptions.length === 0 && page.log.console.filter((c) => c.type === 'error' || c.type === 'log-error').length === 0;
const shot = (name) => page.screenshot(path.join(shotsAt, name + '.png'));

await check('offline: loads from disk with no script error and no network request', async () => {
  const remote = page.log.requests.filter((u) => !/^(file|data|blob):/.test(u));
  if (remote.length) throw new Error('requests: ' + remote.slice(0, 3).join(' '));
  if (!quiet()) throw new Error('errors: ' + JSON.stringify([...page.log.exceptions, ...page.log.console.filter((c) => c.type !== 'log')]).slice(0, 300));
  const status = await page.eval("document.getElementById('status').textContent");
  if (status) throw new Error('the page reports: ' + status);
});
await check('mathematics: every formula typeset, in the sketches and in the paper', async () => {
  const r = await page.eval(`({m: document.querySelectorAll('.m').length, rendered: document.querySelectorAll('.m.rendered').length,
    errors: document.querySelectorAll('.math-error').length, katex: document.querySelectorAll('.katex').length,
    fonts: Array.from(document.fonts).filter(f => f.status === 'loaded').length})`);
  if (r.errors || r.rendered !== r.m) throw new Error(`${r.errors} errors, ${r.rendered}/${r.m} typeset`);
  return `${r.m} formulas, ${r.fonts} embedded fonts in use`;
});

// References: every reference in a sketch opens the paper at its target; Esc returns to the place.
await check('references in the sketches open their target in the paper; Esc returns to the same place', async () => {
  const refs = await page.eval(`Array.from(document.querySelectorAll('#reading .sketch a.ref')).map((a, i) => ({i, label: a.dataset.label, card: a.closest('.sketch').dataset.label}))`);
  const failures = [];
  for (const ref of refs) {
    const r = await page.eval(`(async () => {
      const a = document.querySelectorAll('#reading .sketch a.ref')[${ref.i}];
      a.scrollIntoView({block: 'center'});
      const y0 = window.pageYOffset;
      a.click();
      await new Promise(r => setTimeout(r, 120));
      const target = document.getElementById('p:' + a.dataset.label), box = document.getElementById('paper-scroll').getBoundingClientRect();
      const t = target && target.getBoundingClientRect();
      const visible = !!t && t.top >= box.top - 2 && t.top < box.bottom - 20;
      const open = document.body.classList.contains('pane-open');
      document.getElementById('btn-close').click();
      await new Promise(r => setTimeout(r, 120));
      return {visible, open, closed: !document.body.classList.contains('pane-open'), dy: Math.abs(window.pageYOffset - y0)};
    })()`);
    if (!(r.visible && r.open && r.closed && r.dy <= 1)) failures.push(`${ref.card} -> ${ref.label} ${JSON.stringify(r)}`);
  }
  if (failures.length) throw new Error(failures.slice(0, 3).join(' | '));
  return `${refs.length} references`;
});
await check('references inside the paper scroll to their target', async () => {
  await page.eval("document.querySelector('#s\\\\:document .to-paper').click(); 0");
  await page.sleep(150);
  const refs = await page.eval(`Array.from(document.querySelectorAll('#paper-text a.ref')).map((a, i) => i).filter((i, k) => k % 6 === 0)`);
  const failures = [];
  for (const i of refs) {
    const r = await page.eval(`(async () => {
      const a = document.querySelectorAll('#paper-text a.ref')[${i}];
      const scroll = document.getElementById('paper-scroll');
      a.scrollIntoView({block: 'center'});
      a.click();
      await new Promise(r => setTimeout(r, 80));
      const target = document.getElementById('p:' + a.dataset.label), box = scroll.getBoundingClientRect(), t = target.getBoundingClientRect();
      return {ok: t.top >= box.top - 2 && t.top < box.bottom - 20, label: a.dataset.label};
    })()`);
    if (!r.ok) failures.push(r.label);
  }
  await page.eval("document.getElementById('btn-close').click(); 0");
  if (failures.length) throw new Error('did not reach ' + failures.slice(0, 5).join(', '));
  return `${refs.length} sampled`;
});

// Return navigation.
await check('return: Paper then Esc, Back, and Sketch all leave the reader where they were', async () => {
  const labels = ['sec:genuine', 'definition:fourier-transform', 'theorem:poisson', 'theorem:main', 'corollary:quadratic-dual', 'sec:strategy'];
  for (const label of labels) {
    await page.eval(`(() => { const el = document.getElementById('s:${label}'); el.scrollIntoView({block: 'start'}); window.scrollBy(0, -80); })()`);
    await page.sleep(100);
    const y0 = await page.eval('window.pageYOffset');
    const paperLink = `(document.getElementById('h:${label}') || document.getElementById('s:${label}')).querySelector('.to-paper')`;
    await page.eval(`${paperLink}.click(); 0`);
    await page.sleep(150);
    const opened = await page.eval(`(() => { const t = document.getElementById('p:${label}').getBoundingClientRect(), b = document.getElementById('paper-scroll').getBoundingClientRect(); return document.body.classList.contains('pane-open') && t.top >= b.top - 2 && t.top < b.top + 120; })()`);
    if (!opened) throw new Error(`${label}: paper did not open at the unit`);
    // Esc
    await page.key('Escape');
    await page.sleep(150);
    if (await page.eval("document.body.classList.contains('pane-open')")) throw new Error(`${label}: Esc did not close the paper`);
    if (Math.abs((await page.eval('window.pageYOffset')) - y0) > 1) throw new Error(`${label}: place changed after Esc`);
    // browser Back after opening
    await page.eval(`${paperLink}.click(); 0`);
    await page.sleep(100);
    await page.eval('history.back(); 0');
    await page.sleep(200);
    if (await page.eval("document.body.classList.contains('pane-open')")) throw new Error(`${label}: Back did not close the paper`);
    if (Math.abs((await page.eval('window.pageYOffset')) - y0) > 1) throw new Error(`${label}: place changed after Back`);
    await page.eval('history.forward(); 0');
    await page.sleep(200);
    if (!(await page.eval("document.body.classList.contains('pane-open')"))) throw new Error(`${label}: Forward did not reopen the paper`);
    // the Sketch button goes back to this sketch
    await page.eval("window.scrollTo(0, 0); 0");
    await page.eval("document.getElementById('btn-sketch').click(); 0");
    await page.sleep(200);
    const near = await page.eval(`(() => { const r = (document.getElementById('h:${label}') || document.getElementById('s:${label}')).getBoundingClientRect(); return !document.body.classList.contains('pane-open') && r.top >= 0 && r.top < 200; })()`);
    if (!near) throw new Error(`${label}: Sketch did not return to the sketch`);
  }
  return `${labels.length} sketches`;
});
await check('paper opens from the bar at the sketch in view, and every section is reachable from the list', async () => {
  await page.eval("document.getElementById('s:sec:germs').scrollIntoView(); 0");
  await page.sleep(100);
  await page.eval("document.getElementById('btn-paper').click(); 0");
  await page.sleep(200);
  const loc = await page.eval("document.getElementById('paper-loc').textContent");
  // The number and title of the subsection come from the page, not from this file: they change with the paper.
  const want = await page.eval("(() => { const h = document.getElementById('p:sec:germs').querySelector(':scope > .p-head'); return [h.querySelector('.num').textContent.trim(), h.querySelector('.p-title').textContent.replace(/\\s+/g, ' ').trim()]; })()");
  if (!want[0] || !loc.includes(want[0]) || !loc.includes(want[1])) throw new Error('opened at ' + loc + ', expected §' + want[0] + ' ' + want[1]);
  const options = await page.eval("Array.from(document.querySelectorAll('#paper-jump option')).map(o => o.value)");
  for (const value of options) {
    await page.eval(`(() => { const s = document.getElementById('paper-jump'); s.value = ${JSON.stringify(value)}; s.dispatchEvent(new Event('change')); })()`);
    await page.sleep(40);
    const ok = await page.eval(`(() => { const t = document.getElementById('p:' + ${JSON.stringify(value)}).getBoundingClientRect(), b = document.getElementById('paper-scroll').getBoundingClientRect(); return t.top >= b.top - 2 && t.top < b.bottom - 20; })()`);
    if (!ok) throw new Error('section ' + value + ' not reached');
  }
  await page.key('Escape');
  return `${options.length} entries`;
});

// Lean links: on the sketch cards and in the paper's text.
await check('Lean: every Lean link opens its row of the appendix on Lean, which links to the source', async () => {
  const links = await page.eval(`Array.from(document.querySelectorAll('#reading a.to-lean, #paper-text a.lean')).map((a, i) => ({i, href: a.getAttribute('href')}))`);
  if (!links.length) throw new Error('no Lean links');
  const failures = [];
  for (const link of links) {
    const r = await page.eval(`(async () => {
      const a = document.querySelectorAll('#reading a.to-lean, #paper-text a.lean')[${link.i}];
      const inPaper = !!a.closest('#paper-text');
      if (!inPaper) a.scrollIntoView({block: 'center'});
      else { if (!document.body.classList.contains('pane-open')) document.querySelector('#s\\\\:document .to-paper').click(); await new Promise(r => setTimeout(r, 60)); a.scrollIntoView({block: 'center'}); }
      a.click();
      await new Promise(r => setTimeout(r, 120));
      const id = a.getAttribute('href').slice(1), target = document.getElementById(id);
      const box = document.getElementById('paper-scroll').getBoundingClientRect(), t = target && target.getBoundingClientRect();
      const visible = !!t && t.top >= box.top - 2 && t.top < box.bottom - 20;
      const entry = target && target.nextElementSibling && target.nextElementSibling.matches('a.lean-entry') ? target.nextElementSibling : null;
      const source = entry ? entry.getAttribute('href') : '';
      const name = entry ? entry.textContent.trim() : '';
      document.getElementById('btn-close').click();
      await new Promise(r => setTimeout(r, 80));
      return {visible, source, name, decl: id.replace(/^p:lean:/, '')};
    })()`);
    if (!r.visible || r.name !== r.decl || !/^https:\/\/github\.com\/[^/]+\/[^/]+\/blob\/[0-9a-f]{40}\/lean\/.+#L\d+$/.test(r.source)) failures.push(`${link.href} ${JSON.stringify(r)}`);
  }
  if (failures.length) throw new Error(failures.slice(0, 3).join(' | '));
  const cards = await page.eval("document.querySelectorAll('#reading a.to-lean').length");
  return `${links.length} links (${cards} on sketch cards)`;
});
await check('Lean: every sketched statement marked \\lean in the paper has a Lean link on its card', async () => {
  const missing = await page.eval(`Array.from(document.querySelectorAll('#reading article.sketch.kind-statement')).filter(card => {
    const stmt = document.getElementById('p:' + card.dataset.label);
    const marked = stmt && Array.from(stmt.querySelectorAll('a.lean')).some(a => !a.closest('details.p-proof'));
    return marked !== !!card.querySelector('a.to-lean');
  }).map(card => card.dataset.label)`);
  if (missing.length) throw new Error('mismatch for ' + missing.join(', '));
});

// Folds: the figures under the sketches, and the proofs in the paper.
const figures = await page.eval("Array.from(document.querySelectorAll('details.explore[data-media]')).map(d => d.dataset.media)");
await check('folds: every figure starts closed, opens in place, and shows its drawing and typeset caption', async () => {
  if (!figures.length) throw new Error('no figures');
  const out = [];
  for (const id of figures) {
    const r = await page.eval(`(async () => {
      const d = document.querySelector('details.explore[data-media="${id}"]');
      const closed = !d.open;
      d.querySelector('summary').click();
      await new Promise(r => setTimeout(r, 150));
      d.scrollIntoView({block: 'start'}); window.scrollBy(0, -60);
      const svg = d.querySelector('.figure-art svg'), box = svg && svg.getBoundingClientRect();
      const caption = d.querySelector('.figure-caption');
      const math = caption.querySelectorAll('.m').length, typeset = caption.querySelectorAll('.m.rendered').length;
      const refs = Array.from(caption.querySelectorAll('a.ref')).filter(a => !document.getElementById('p:' + a.dataset.label)).length;
      return {closed, open: d.open, w: box ? box.width : 0, h: box ? box.height : 0, math, typeset, refs, shapes: svg ? svg.querySelectorAll('polyline, circle, line, text').length : 0};
    })()`);
    await page.sleep(150);
    await shot(`figure-${id}`);
    if (!r.closed || !r.open || r.w < 300 || r.h < 200 || r.shapes < 20 || r.typeset !== r.math || r.refs) throw new Error(`${id} ${JSON.stringify(r)}`);
    out.push(`${id} ${Math.round(r.w)}x${Math.round(r.h)}`);
    await page.eval(`document.querySelector('details.explore[data-media="${id}"] summary').click(); 0`);
  }
  return out.join(', ');
});
await check('folds: every proof in the paper folds and unfolds, and "fold proofs" folds them all', async () => {
  await page.eval("document.querySelector('#s\\\\:document .to-paper').click(); 0");
  await page.sleep(150);
  const r = await page.eval(`(async () => {
    const proofs = Array.from(document.querySelectorAll('#paper-text details.p-proof'));
    const openAtStart = proofs.filter(d => d.open).length;
    let toggled = 0;
    for (const d of proofs) { d.querySelector('summary').click(); if (!d.open) { d.querySelector('summary').click(); if (d.open) toggled++; } }
    const box = document.getElementById('fold-proofs');
    box.checked = true; box.dispatchEvent(new Event('change'));
    const folded = proofs.filter(d => !d.open).length;
    box.checked = false; box.dispatchEvent(new Event('change'));
    const reopened = proofs.filter(d => d.open).length;
    const bodies = proofs.filter(d => d.querySelector('.p-proof-body').textContent.trim().length > 20).length;
    return {n: proofs.length, openAtStart, toggled, folded, reopened, bodies};
  })()`);
  await page.eval("document.getElementById('btn-close').click(); 0");
  if (!r.n || r.openAtStart !== r.n || r.toggled !== r.n || r.folded !== r.n || r.reopened !== r.n || r.bodies !== r.n) throw new Error(JSON.stringify(r));
  return `${r.n} proofs`;
});
await check('audit: figures marked for re-check in this page', async () => {
  const n = await page.eval("document.querySelectorAll('details.explore > summary .mtag.recheck').length");
  return n ? `${n} marked; python3 portable/audit.py status says why` : 'none';
});
await check('after all of that: still no error, no request, nothing reported', async () => {
  const remote = page.log.requests.filter((u) => !/^(file|data|blob):/.test(u));
  const errors = page.log.console.filter((c) => c.type === 'error' || c.type === 'log-error');
  const status = await page.eval("document.getElementById('status').textContent");
  if (remote.length || page.log.exceptions.length || errors.length || status) throw new Error(JSON.stringify({ remote, exceptions: page.log.exceptions.slice(0, 2), errors: errors.slice(0, 2), status }));
});

// Viewports.
const viewports = [['laptop 1440x900', 1440, 900], ['laptop 1280x720', 1280, 720], ['narrow window 760x900', 760, 900], ['phone 390x844', 390, 844]];
for (const [name, w, h] of viewports) {
  await check(`layout at ${name}: no horizontal overflow, pane and contents fit`, async () => {
    await page.viewport(w, h, w < 500);
    await page.open(url);
    await page.waitFor("document.documentElement.dataset.ready === '1'", { timeout: 30000 });
    const slug = `${w}x${h}`;
    await page.eval("document.getElementById('s:theorem:main').scrollIntoView(); window.scrollBy(0, -70); 0");
    await page.sleep(250);
    await shot(`${slug}-reading`);
    const wide = await page.eval("document.documentElement.scrollWidth - window.innerWidth");
    if (wide > 1) throw new Error(`document ${wide}px wider than the window`);
    await page.eval("document.querySelector('#s\\\\:theorem\\\\:main .to-paper').click(); 0");
    await page.sleep(500);
    await shot(`${slug}-paper`);
    const fit = await page.eval(`(() => { const p = document.getElementById('paper').getBoundingClientRect(), s = document.getElementById('paper-scroll'); return {left: p.left, right: p.right, over: s.scrollWidth - s.clientWidth, w: window.innerWidth, sketchBtn: document.getElementById('btn-sketch').getBoundingClientRect().right <= window.innerWidth, closeBtn: document.getElementById('btn-close').getBoundingClientRect().right <= window.innerWidth}; })()`);
    if (fit.right > fit.w + 1 || !fit.sketchBtn || !fit.closeBtn) throw new Error('pane does not fit ' + JSON.stringify(fit));
    if (fit.over > 12) throw new Error(`paper text overflows its pane by ${fit.over}px`);
    await page.key('Escape');
    await page.eval("document.getElementById('btn-contents').click(); 0");
    await page.sleep(200);
    await shot(`${slug}-contents`);
    const toc = await page.eval("document.getElementById('contents').getBoundingClientRect().right <= window.innerWidth + 1");
    if (!toc) throw new Error('contents wider than the window');
    await page.key('Escape');
    // an open figure stays inside the window
    await page.eval("(() => { const d = document.querySelector('details.explore[data-media=lines]'); d.open = true; d.scrollIntoView(); })()");
    await page.sleep(300);
    const box = await page.eval("(() => { const r = document.querySelector('details.explore[data-media=lines]').getBoundingClientRect(); return [r.left, r.right, window.innerWidth]; })()");
    await shot(`${slug}-figure`);
    if (box[0] < -1 || box[1] > box[2] + 1) throw new Error('open figure leaves the window ' + box.join(','));
    const wide2 = await page.eval("document.documentElement.scrollWidth - window.innerWidth");
    if (wide2 > 1) throw new Error(`with a figure open, the document is ${wide2}px wider than the window`);
    await page.eval("document.querySelector('details.explore[data-media=lines]').open = false");
    return `screenshots in ${shotsAt}`;
  });
}
await page.viewport(1440, 900, false);

// ---------------------------------------------------------------- failures must be visible

async function variant(name, transform, test) {
  const copy = path.join(shotsAt, `variant-${name}.html`);
  writeFileSync(copy, transform(html));
  const browser = await launch({ width: 1440, height: 900 });
  try {
    await browser.open(pathToFileURL(copy).href);
    await browser.sleep(1500);
    return await test(browser);
  } finally { await browser.close(); rmSync(copy, { force: true }); }
}
// A build against an empty record of what the pictures were compared with marks every one of them.
await check('failure shown: figures that may be out of date carry a mark and a note that links to the statements', async () => {
  const marked = path.join(shotsAt, 'variant-recheck.html');
  execFileSync(process.env.PYTHON || 'python3', [path.join(root, 'portable/build.py'), '--output', marked, '--audit-lock', path.join(shotsAt, 'no-such-record.toml')], { cwd: root, stdio: 'pipe' });
  const b = await launch({ width: 390, height: 844, mobile: true });
  try {
    await b.open(pathToFileURL(marked).href);
    await b.waitFor("document.documentElement.dataset.ready === '1'", { timeout: 30000 });
    const r = await b.eval(`(() => {
      const figures = Array.from(document.querySelectorAll('details.explore[data-media]'));
      const links = Array.from(document.querySelectorAll('.recheck-note a.ref'));
      const first = figures[0]; first.open = true; first.scrollIntoView();
      const note = first.querySelector(':scope > .recheck-note');
      return { figures: figures.length, marked: figures.filter(d => d.querySelector('summary .mtag.recheck')).length,
        noted: figures.filter(d => d.querySelector(':scope > .recheck-note')).length,
        broken: links.filter(a => !document.getElementById('p:' + a.dataset.label)).length, links: links.length,
        visible: !!note && note.getBoundingClientRect().height > 10, wide: document.documentElement.scrollWidth - window.innerWidth };
    })()`);
    if (!r.figures || r.marked !== r.figures || r.noted !== r.figures) throw new Error(JSON.stringify(r));
    if (!r.links || r.broken || !r.visible || r.wide > 1) throw new Error(JSON.stringify(r));
    await b.screenshot(path.join(shotsAt, 'recheck-narrow.png'));
    return `${r.figures} figures marked, ${r.links} links`;
  } finally { await b.close(); rmSync(marked, { force: true }); }
});
await check('failure shown: a formula that cannot be typeset appears in red and is reported', () => variant('badmath',
  (h) => h.replace('<div class="sketch-body">', '<div class="sketch-body"><div class="paper-paragraph"><span class="m">\\undefinedmacro{x}</span></div>'),
  async (b) => {
    const r = await b.eval("({red: document.querySelectorAll('.math-error').length, status: document.getElementById('status').textContent})");
    if (r.red < 1 || !/formula/.test(r.status)) throw new Error(JSON.stringify(r));
  }));
await check('failure shown: without the math renderer, formulas stay readable and the page says so', () => variant('nokatex',
  (h) => h.replace(':e.katex=t()}', ':e.katexGone=t()}'),
  async (b) => {
    const r = await b.eval("({status: document.getElementById('status').textContent, raw: document.querySelectorAll('.m:not(.rendered)').length})");
    if (!/math renderer/.test(r.status) || r.raw < 10) throw new Error(JSON.stringify(r));
  }));

await page.close();
const failed = results.filter((r) => !r.ok);
console.log(`\n${results.length - failed.length} of ${results.length} checks passed.`);
if (failed.length) { console.log('Failed: ' + failed.map((f) => f.name).join('; ')); process.exit(1); }
