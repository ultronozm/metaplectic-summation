// Check a served build of the site in headless Chrome.
//
// Usage: node scripts/check-site/check.mjs URL [SCREENSHOT_DIR]
//   URL             where _site is served, e.g. http://127.0.0.1:8000/
//   SCREENSHOT_DIR  default _site/screenshots
//
// Starting from index.html, it opens every page of the site linked from
// there and checks that the page loads without script errors, that
// MathJax typesets it without errors, that no "??" remains, and that
// every link within the site resolves, anchors included.  Links leaving
// the site are counted, not fetched.  It saves a screenshot of the top
// of each page, and of the Lean table and of Appendix C.  Exit status 1
// on any failure.
import { mkdirSync } from 'node:fs';
import path from 'node:path';
import { launch } from './browser.mjs';

const base = new URL(process.argv[2] || 'http://127.0.0.1:8000/');
const shots = process.argv[3] || '_site/screenshots';
mkdirSync(shots, { recursive: true });

const problems = [];
const fail = (where, what) => problems.push(`${where}: ${what}`);
const idsCache = new Map();

// The ids of a page of the site, from its HTML.
async function idsOf(url) {
  if (!idsCache.has(url)) {
    const response = await fetch(url);
    const html = response.ok ? await response.text() : null;
    idsCache.set(url, html && new Set([...html.matchAll(/\sid="([^"]*)"/g)].map((m) => m[1])));
  }
  return idsCache.get(url);
}

const page = await launch({ width: 1280, height: 900 });
const typeset = `(async () => {
  if (!window.MathJax?.startup?.promise) return { mathjax: false };
  await MathJax.startup.promise;
  return {
    mathjax: true,
    math: document.querySelectorAll('mjx-container').length,
    errors: [...document.querySelectorAll('mjx-merror, [data-mjx-error]')].map((e) => e.getAttribute('data-mjx-error') || e.textContent).slice(0, 5),
  };
})()`;

async function visit(url, name) {
  page.log.exceptions.length = 0;
  page.log.console.length = 0;
  await page.open(url);
  const state = await page.waitFor(typeset, { timeout: 60000 });
  if (!state.mathjax) fail(name, 'MathJax did not load');
  else if (state.errors.length) fail(name, `MathJax errors: ${state.errors.join('; ')}`);
  if (await page.eval(`document.body.innerText.includes('??')`)) fail(name, '?? in the text');
  for (const e of page.log.exceptions) fail(name, `exception: ${e}`);
  for (const c of page.log.console) if ((c.type === 'error' || c.type === 'log-error') && !c.text.includes('favicon.ico')) fail(name, `console: ${c.text}`);
  await page.screenshot(path.join(shots, `${name}.png`));
  const links = await page.eval(`[...document.querySelectorAll('a[href]')].map((a) => a.href)`);
  return { math: state.math ?? 0, links };
}

async function shoot(selector, name) {
  const y = await page.eval(`(() => { const e = document.querySelector(${JSON.stringify(selector)}); if (!e) return null; e.scrollIntoView(); return window.scrollY; })()`);
  if (y === null) return fail(name, `no element ${selector}`);
  await page.sleep(300);
  await page.screenshot(path.join(shots, `${name}.png`));
}

const index = new URL('index.html', base).href;
const { math, links } = await visit(index, 'index');
await shoot('table', 'index-lean-table');
const pages = [...new Set(links.filter((l) => l.startsWith(base.origin) && /\.html(#|$)/.test(l)).map((l) => l.split('#')[0]))];
const report = [`index.html: ${math} formulas, ${links.length} links`];
const allLinks = new Map([[index, links]]);
for (const url of pages) {
  if (url === index) continue;
  const name = path.basename(new URL(url).pathname, '.html');
  const result = await visit(url, name);
  report.push(`${name}.html: ${result.math} formulas, ${result.links.length} links`);
  allLinks.set(url, result.links);
  if (name === 'schwartz-space-n-fold-cover-sl2') await shoot('[id="sec:lean"]', 'paper-appendix-c');
}
await page.close();

let internal = 0, external = 0;
for (const [from, list] of allLinks) {
  const where = path.basename(new URL(from).pathname);
  for (const link of new Set(list)) {
    if (!link.startsWith(base.origin)) { external++; continue; }
    internal++;
    const [target, anchor] = link.split('#');
    const response = await fetch(target, { method: 'HEAD' });
    if (!response.ok) { fail(where, `broken link ${link} (${response.status})`); continue; }
    if (anchor && target.endsWith('.html')) {
      const ids = await idsOf(target);
      if (!ids?.has(decodeURIComponent(anchor))) fail(where, `missing anchor ${link}`);
    }
  }
}
console.log(report.join('\n'));
console.log(`${internal} links within the site checked; ${external} links leaving it not fetched`);
console.log(`Screenshots in ${shots}`);
if (problems.length) {
  console.log(`\n${problems.length} problems:\n` + problems.join('\n'));
  process.exit(1);
}
console.log('No problems found.');
