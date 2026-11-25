/* The reader.  A plain script, with no modules and no network: it must work when the page is opened from disk.

   The sketches and the paper are already in the page as HTML, generated from sketches.tex and main.tex.
   This script typesets the formulas and moves between a sketch and the paper's text.  The pictures are static SVG.
   Whatever fails is reported on the page. */
(function () {
  'use strict';

  var $ = function (id) { return document.getElementById(id); };
  var D = window.EDITION;

  function escape(text) {
    return String(text).replace(/[&<>"]/g, function (c) { return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]; });
  }

  // ---------------------------------------------------------------- failures are shown on the page

  var statusBox = $('status');
  var reports = {};
  function problem(key, message) {
    var box = reports[key];
    if (!box) {
      box = reports[key] = document.createElement('div');
      statusBox.appendChild(box);
    }
    box.textContent = message;
  }
  window.addEventListener('error', function (event) {
    if (/ResizeObserver loop/.test(event.message || '')) return;
    problem('script:' + event.message, 'Script error: ' + (event.message || 'unknown') + (event.filename ? ' (' + event.filename.split('/').pop() + ':' + event.lineno + ')' : ''));
  });
  window.addEventListener('unhandledrejection', function (event) {
    var reason = event.reason, text = reason && reason.message ? reason.message : String(reason);
    problem('rejection:' + text, 'Unexpected error: ' + text);
  });

  // ---------------------------------------------------------------- mathematics

  var katex = window.katex;
  var mathErrors = 0;
  if (!katex) problem('katex', 'The math renderer did not load, so formulas appear as TeX source.');

  function typesetOne(el) {
    el.setAttribute('data-done', '1');
    if (!katex) return;
    var source = el.textContent;
    try {
      katex.render(source, el, { displayMode: el.classList.contains('display'), throwOnError: true, strict: false, macros: D.macros });
      el.classList.add('rendered');
    } catch (error) {
      el.classList.add('math-error');
      el.title = String(error && error.message || error);
      el.textContent = source;
      mathErrors++;
      problem('math', mathErrors + ' formula' + (mathErrors > 1 ? 's' : '') + ' could not be typeset; each is shown as TeX source in red.');
    }
  }
  function typeset(root) {
    var nodes = root.querySelectorAll('.m:not([data-done])');
    for (var i = 0; i < nodes.length; i++) typesetOne(nodes[i]);
  }

  var paperTypeset = false;
  function typesetPaperInSlices(done) {
    var pending = Array.prototype.slice.call(paperText.querySelectorAll('.m:not([data-done])')), index = 0;
    (function slice() {
      var started = Date.now();
      while (index < pending.length && Date.now() - started < 20) {
        if (!pending[index].getAttribute('data-done')) typesetOne(pending[index]);
        index++;
      }
      if (index < pending.length) setTimeout(slice, 0);
      else { paperTypeset = true; if (done) done(); }
    })();
  }
  function ensurePaperTypeset() {
    if (paperTypeset) return;
    typeset(paperText);
    paperTypeset = true;
  }

  // ---------------------------------------------------------------- elements

  var reading = $('reading'), paperScroll = $('paper-scroll'), paperText = $('paper-text');
  var contents = $('contents'), about = $('about'), bar = $('bar');

  function barHeight() { return bar.getBoundingClientRect().height; }
  function sketchTarget(label) { return $('h:' + label) || $('s:' + label); }

  function flash(el) {
    if (!el) return;
    el.classList.remove('flash');
    void el.offsetWidth;
    el.classList.add('flash');
    setTimeout(function () { el.classList.remove('flash'); }, 2000);
  }

  // The topmost block of the reading column still in view, with its offset, so that a change of layout
  // (the paper opening beside the sketches, a narrower column) does not move the reader's place.
  function keepPlace(change) {
    var line = barHeight() + 4, anchor = null, offset = 0, blocks = reading.children;
    for (var i = 0; i < blocks.length; i++) {
      var box = blocks[i].getBoundingClientRect();
      if (box.height && box.bottom > line) { anchor = blocks[i]; offset = box.top; break; }
    }
    change();
    if (anchor) {
      var shift = anchor.getBoundingClientRect().top - offset;
      if (Math.abs(shift) > 1) window.scrollBy(0, shift);
    }
  }

  // ---------------------------------------------------------------- the paper pane

  var paneOpen = false, invoker = null;

  function setPane(open) {
    if (open === paneOpen) return;
    paneOpen = open;
    if (open) ensurePaperTypeset();
    keepPlace(function () { document.body.classList.toggle('pane-open', open); });
    $('btn-paper').setAttribute('aria-pressed', String(open));
  }

  function revealProofs(el) {
    for (var node = el.parentNode; node && node !== paperText; node = node.parentNode) {
      if (node.tagName === 'DETAILS' && !node.open) node.open = true;
    }
  }

  // The block to flash: a heading or statement as a whole, an equation or paragraph for an anchor inside one.
  function blockOf(el) {
    if (el.classList.contains('p-sec')) return el.querySelector('.p-head') || el;
    // A row of the appendix on Lean: the declaration's link, not the whole paragraph or table.
    if (el.classList.contains('paper-anchor') && el.nextElementSibling && el.nextElementSibling.classList.contains('lean-entry')) return el.nextElementSibling;
    if (el.classList.contains('paper-anchor')) return el.closest('.display, .paper-paragraph, li, .bibliography-entry') || el;
    return el;
  }

  function showInPaper(label) {
    var target = $('p:' + label);
    if (!target) { problem('missing:' + label, 'The paper has no passage ' + label + '.'); return false; }
    revealProofs(target);
    var block = blockOf(target);
    paperScroll.scrollTop += block.getBoundingClientRect().top - paperScroll.getBoundingClientRect().top - 14;
    flash(block);
    var previous = paperText.querySelector('.is-unit');
    if (previous) previous.classList.remove('is-unit');
    var unit = target.classList.contains('paper-anchor') ? target.closest('.p-stmt, .p-sec, .p-front') : target;
    if (unit && /\b(p-sec|p-stmt|p-front)\b/.test(unit.className)) unit.classList.add('is-unit');
    return true;
  }

  function plainText(el) {
    var copy = el.cloneNode(true), extra = copy.querySelectorAll('.to-sketch');
    for (var i = 0; i < extra.length; i++) extra[i].parentNode.removeChild(extra[i]);
    return copy.textContent.replace(/\.\s*$/, '').replace(/\s+/g, ' ').trim();
  }

  // What the pane shows now: the innermost unit under its top edge, and the sketch to return to.
  function paneWhere() {
    var box = paperScroll.getBoundingClientRect();
    var el = document.elementFromPoint(box.left + Math.min(60, box.width / 2), box.top + 36);
    var unit = el && el.closest ? el.closest('#paper-text .p-stmt, #paper-text .p-sec, #paper-text .p-front') : null;
    if (!unit) return { html: '', sketch: null };
    var owner = unit.closest('[data-sketch]');
    var section = unit.classList.contains('p-sec') ? unit : unit.closest('.p-sec');
    var number = section && section.querySelector(':scope > .p-head .num');
    var text;
    if (unit.classList.contains('p-stmt')) {
      var title = unit.querySelector('.paper-statement > h4');
      text = '<b>' + escape(title ? plainText(title) : 'Statement') + '</b>' + (number && number.textContent ? ' &middot; &sect;' + escape(number.textContent) : '');
    } else if (unit.classList.contains('p-sec')) {
      var head = unit.querySelector(':scope > .p-head'), num = head.querySelector('.num');
      // An unnumbered section, such as the references, is named by its title alone.
      text = num ? '<b>&sect;' + escape(num.textContent) + '</b> ' + escape(plainText(head.querySelector('.p-title')))
        : '<b>' + escape(plainText(head.querySelector('.p-title'))) + '</b>';
    } else text = '<b>Title and abstract</b>';
    return { html: text, sketch: owner ? owner.getAttribute('data-sketch') : null };
  }

  function updatePane() {
    if (!paneOpen) return;
    var state = paneWhere();
    $('paper-loc').innerHTML = state.html;
    var button = $('btn-sketch');
    button.disabled = !state.sketch;
    button.setAttribute('data-label', state.sketch || '');
    button.title = state.sketch ? 'Back to the sketch of this unit' : 'This part of the paper has no sketch';
    $('btn-back').disabled = !(haveHistory && current.n > 0);
    var select = $('paper-jump'), section = state.sketch && D.sectionOf[state.sketch];
    if (section && select.value !== section) select.value = section;
  }

  // ---------------------------------------------------------------- the reading column

  function where() {
    var line = barHeight() + 40, heading = null, card = null, blocks = reading.children;
    for (var i = 0; i < blocks.length; i++) {
      if (blocks[i].getBoundingClientRect().top > line) break;
      if (blocks[i].classList.contains('r-head')) { heading = blocks[i]; card = null; }
      else if (blocks[i].classList.contains('sketch')) card = blocks[i];
    }
    var text = '';
    if (heading) {
      var number = heading.querySelector('.num').textContent;
      text = '<b>' + (number ? '&sect;' + escape(number) : '') + '</b> ' + escape(plainText(heading.querySelector('.ttl')));
    }
    var kind = card && card.querySelector('.unit-kind');
    if (kind && card.getBoundingClientRect().bottom > line) text += ' &middot; ' + escape(kind.textContent);
    $('where').innerHTML = text;
    var key = heading ? heading.getAttribute('data-label') : null, items = contents.querySelectorAll('li');
    for (var j = 0; j < items.length; j++) {
      items[j].classList.toggle('current', !!key && items[j].firstChild.getAttribute('data-target') === key);
    }
  }

  // ---------------------------------------------------------------- moving between the two

  // Every move is a history entry, so that the browser's Back and Forward move between sketch and paper.
  // The state is {pane: label or null, sketch: label or null, n: entries since the page opened, y: scroll of the reading column}.
  var current = { pane: null, sketch: null, n: 0 };
  var haveHistory = true;
  try { history.scrollRestoration = 'manual'; } catch (error) { /* an older browser */ }

  function remember() {
    if (!haveHistory) return;
    try { history.replaceState(Object.assign({}, current, { y: window.pageYOffset }), '', location.href); }
    catch (error) { haveHistory = false; }
  }

  function go(state) {
    remember();
    state.n = (current.n || 0) + 1;
    var url = state.pane ? '#p:' + state.pane : state.sketch ? '#s:' + state.sketch : location.href.split('#')[0];
    if (haveHistory) {
      try { history.pushState(state, '', url); } catch (error) { haveHistory = false; }
    }
    apply(state, false);
  }

  function apply(state, restore) {
    current = state;
    closeContents();
    if (state.pane) {
      var wasOpen = paneOpen;
      setPane(true);
      if (!showInPaper(state.pane) && !wasOpen) setPane(false);
      else if (!wasOpen && !restore) paperScroll.focus({ preventScroll: true });
    } else {
      var wasPane = paneOpen;
      setPane(false);
      if (state.sketch) {
        var target = sketchTarget(state.sketch);
        if (target) { target.scrollIntoView({ block: 'start' }); flash(target); }
        else problem('nosketch:' + state.sketch, 'There is no sketch ' + state.sketch + '.');
      }
      if (wasPane && invoker && document.body.contains(invoker)) {
        try { invoker.focus({ preventScroll: true }); } catch (error) { /* detached */ }
      }
    }
    if (restore && typeof state.y === 'number') window.scrollTo(0, state.y);
    where();
    updatePane();
  }

  window.addEventListener('popstate', function (event) {
    apply(event.state || fromHash(location.hash), true);
  });

  function fromHash(hash) {
    var match = /^#([ps]):(.+)$/.exec(hash || '');
    if (!match) return { pane: null, sketch: null, n: 0 };
    var label = decodeURIComponent(match[2]);
    return { pane: match[1] === 'p' ? label : null, sketch: match[1] === 's' ? label : null, n: 0 };
  }

  document.addEventListener('click', function (event) {
    var link = event.target.closest ? event.target.closest('a[href^="#"]') : null;
    if (!link || event.defaultPrevented || event.metaKey || event.ctrlKey || event.shiftKey) return;
    var href = link.getAttribute('href'), kind = href.slice(0, 3);
    if (kind === '#p:') {
      event.preventDefault();
      if (!paneOpen) invoker = link;
      go({ pane: href.slice(3), sketch: null });
    } else if (kind === '#s:' || kind === '#h:') {
      event.preventDefault();
      go({ pane: null, sketch: href.slice(3) });
    }
  });

  // ---------------------------------------------------------------- controls

  function closeContents() {
    contents.hidden = true;
    $('btn-contents').setAttribute('aria-expanded', 'false');
  }

  $('btn-contents').addEventListener('click', function () {
    var open = contents.hidden;
    contents.hidden = !open;
    this.setAttribute('aria-expanded', String(open));
  });
  document.addEventListener('click', function (event) {
    if (!contents.hidden && !event.target.closest('#contents, #btn-contents')) closeContents();
  });
  $('btn-paper').addEventListener('click', function () {
    invoker = this;
    if (paneOpen) { go({ pane: null, sketch: null }); return; }
    // Open the paper where the reader is: at the unit in view, or at the beginning.
    var line = barHeight() + 40, label = 'document', blocks = reading.children;
    for (var i = 0; i < blocks.length; i++) {
      if (blocks[i].getBoundingClientRect().top > line) break;
      var id = blocks[i].getAttribute('data-label');
      if (id && $('p:' + id)) label = id;
    }
    go({ pane: label, sketch: null });
  });
  $('btn-close').addEventListener('click', function () { go({ pane: null, sketch: null }); });
  $('btn-back').addEventListener('click', function () { if (haveHistory && current.n > 0) history.back(); });
  $('btn-sketch').addEventListener('click', function () {
    var label = this.getAttribute('data-label');
    if (label) go({ pane: null, sketch: label });
  });
  $('paper-jump').addEventListener('change', function () {
    if (this.value) go({ pane: this.value, sketch: null });
  });
  $('fold-proofs').addEventListener('change', function () {
    var all = paperText.querySelectorAll('details.p-proof');
    for (var i = 0; i < all.length; i++) all[i].open = !this.checked;
  });
  $('btn-about').addEventListener('click', function () { about.hidden = false; $('about-close').focus(); });
  $('about-close').addEventListener('click', function () { about.hidden = true; $('btn-about').focus(); });
  about.addEventListener('click', function (event) { if (event.target === about) about.hidden = true; });

  document.addEventListener('keydown', function (event) {
    if (event.key !== 'Escape') return;
    if (!about.hidden) about.hidden = true;
    else if (!contents.hidden) closeContents();
    else if (paneOpen) go({ pane: null, sketch: null });
  });

  var tick = 0, paneTick = 0;
  window.addEventListener('scroll', function () {
    if (!tick) tick = requestAnimationFrame(function () { tick = 0; where(); });
  }, { passive: true });
  paperScroll.addEventListener('scroll', function () {
    if (!paneTick) paneTick = requestAnimationFrame(function () { paneTick = 0; updatePane(); });
  }, { passive: true });
  window.addEventListener('resize', function () { where(); updatePane(); });

  // ---------------------------------------------------------------- start

  typeset(reading);
  typeset(contents);
  typeset(about);
  where();

  var start = fromHash(location.hash);
  try { history.replaceState(start, '', location.href); } catch (error) { haveHistory = false; }
  current = start;
  if (start.pane || start.sketch) {
    var begin = function () {
      // A link into the paper also puts the sketches at that unit, so that closing the paper lands there.
      var own = start.pane && (sketchTarget(start.pane));
      if (own) own.scrollIntoView({ block: 'start' });
      apply(start, false);
    };
    if (document.fonts && document.fonts.ready) document.fonts.ready.then(begin); else begin();
  }
  typesetPaperInSlices(function () {
    document.documentElement.setAttribute('data-ready', '1');
    updatePane();
  });
})();
