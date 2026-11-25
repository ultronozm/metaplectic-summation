// A minimal Chrome driver over the DevTools protocol, with no dependencies.
// It opens the page the way a reader does, from disk, with Chrome's default security settings.
import { spawn } from 'node:child_process';
import { mkdtempSync, readFileSync, writeFileSync, existsSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';

const CANDIDATES = [
  process.env.CHROME,
  '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome',
  '/Applications/Chromium.app/Contents/MacOS/Chromium',
  '/usr/bin/google-chrome',
  '/usr/bin/chromium',
  'C:\\Program Files\\Google\\Chrome\\Application\\chrome.exe',
].filter(Boolean);

const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms));

export async function launch({ width = 1440, height = 900, mobile = false } = {}) {
  const binary = CANDIDATES.find((candidate) => existsSync(candidate));
  if (!binary) throw new Error('No Chrome found; set CHROME to its path');
  const profile = mkdtempSync(path.join(tmpdir(), 'site-check-'));
  const child = spawn(binary, [
    '--headless=new', '--remote-debugging-port=0', `--user-data-dir=${profile}`,
    '--no-first-run', '--no-default-browser-check', '--use-angle=swiftshader', '--enable-unsafe-swiftshader',
    '--mute-audio', '--autoplay-policy=no-user-gesture-required', `--window-size=${width},${height}`, 'about:blank',
  ], { stdio: 'ignore' });
  const portFile = path.join(profile, 'DevToolsActivePort');
  for (let i = 0; i < 100 && !existsSync(portFile); i++) await sleep(100);
  if (!existsSync(portFile)) throw new Error('Chrome did not start');
  const port = readFileSync(portFile, 'utf8').split('\n')[0];
  let targets = [];
  for (let i = 0; i < 50 && !targets.some((t) => t.type === 'page'); i++) {
    targets = await (await fetch(`http://127.0.0.1:${port}/json/list`)).json();
    if (!targets.some((t) => t.type === 'page')) await sleep(100);
  }
  const target = targets.find((t) => t.type === 'page');
  const socket = new WebSocket(target.webSocketDebuggerUrl);
  await new Promise((resolve, reject) => { socket.onopen = resolve; socket.onerror = reject; });

  let counter = 0;
  const pending = new Map(), listeners = new Map();
  const log = { console: [], exceptions: [], requests: [], failures: [] };
  socket.onmessage = (message) => {
    const data = JSON.parse(message.data);
    if (data.id && pending.has(data.id)) {
      const { resolve, reject } = pending.get(data.id);
      pending.delete(data.id);
      data.error ? reject(new Error(data.error.message)) : resolve(data.result);
    } else if (data.method) {
      for (const callback of listeners.get(data.method) || []) callback(data.params);
    }
  };
  const send = (method, params = {}) => new Promise((resolve, reject) => {
    const id = ++counter;
    pending.set(id, { resolve, reject });
    socket.send(JSON.stringify({ id, method, params }));
  });
  const on = (method, callback) => listeners.set(method, [...(listeners.get(method) || []), callback]);

  on('Runtime.consoleAPICalled', (p) => log.console.push({ type: p.type, text: p.args.map((a) => a.value ?? a.description ?? '').join(' ') }));
  on('Runtime.exceptionThrown', (p) => log.exceptions.push(p.exceptionDetails.exception?.description || p.exceptionDetails.text));
  on('Log.entryAdded', (p) => { if (p.entry.level === 'error') log.console.push({ type: 'log-error', text: p.entry.text + ' ' + (p.entry.url || '') }); });
  on('Network.requestWillBeSent', (p) => log.requests.push(p.request.url));
  on('Network.loadingFailed', (p) => log.failures.push(`${p.errorText} ${p.canceled ? '(canceled)' : ''}`));
  for (const domain of ['Page', 'Runtime', 'Log', 'Network']) await send(`${domain}.enable`);

  const page = {
    log, send, on,
    async viewport(w, h, isMobile = mobile) {
      await send('Emulation.setDeviceMetricsOverride', { width: w, height: h, deviceScaleFactor: 1, mobile: isMobile });
    },
    async open(url) {
      const loaded = new Promise((resolve) => on('Page.loadEventFired', resolve));
      await send('Page.navigate', { url });
      await loaded;
    },
    async eval(expression) {
      const result = await send('Runtime.evaluate', { expression, awaitPromise: true, returnByValue: true });
      if (result.exceptionDetails) throw new Error(result.exceptionDetails.exception?.description || result.exceptionDetails.text);
      return result.result.value;
    },
    async waitFor(expression, { timeout = 15000, interval = 100 } = {}) {
      const start = Date.now();
      for (;;) {
        let value;
        try { value = await page.eval(expression); } catch (error) { value = false; }
        if (value) return value;
        if (Date.now() - start > timeout) throw new Error('Timed out waiting for: ' + expression);
        await sleep(interval);
      }
    },
    async screenshot(file, { fullPage = false } = {}) {
      const { data } = await send('Page.captureScreenshot', { format: 'png', captureBeyondViewport: fullPage });
      writeFileSync(file, Buffer.from(data, 'base64'));
    },
    async key(key) {
      const code = key === 'Escape' ? 27 : 0;
      for (const type of ['keyDown', 'keyUp']) await send('Input.dispatchKeyEvent', { type, key, code: key, windowsVirtualKeyCode: code });
    },
    async click(x, y) {
      for (const type of ['mousePressed', 'mouseReleased']) await send('Input.dispatchMouseEvent', { type, x, y, button: 'left', clickCount: 1 });
    },
    async close() {
      try { socket.close(); } catch (error) { /* closed */ }
      child.kill();
      await sleep(200);
      try { rmSync(profile, { recursive: true, force: true }); } catch (error) { /* in use */ }
    },
    sleep,
  };
  await page.viewport(width, height, mobile);
  return page;
}
