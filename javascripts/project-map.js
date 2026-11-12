/* A formula's TeX as plain text, for places that cannot typeset one: a tab title, an accessible name, a tooltip, an
 * SVG label. The explorer and the map share this reducer. Render's port, autoform_cli/tex_plain.py, gives the same
 * text for each case in tests/fixtures/tex-plain-cases.json and each entry of these tables. Unknown commands read as
 * their names.
 */
(function () {
  "use strict";
  if (window.AutoformTexPlain) return;

  // Tables hold only their own names, so a command named like an Object method, \toString say, reads as its name.
  function own(entries) { return Object.assign(Object.create(null), entries); }
  function table(keys, values) {
    var out = Object.create(null), chars = Array.from(values || "");
    keys.split(" ").forEach(function (key, index) { out[key] = values ? chars[index] : true; });
    return out;
  }
  var DOUBLE = table("A B C D E F G H I J K L M N O P Q R S T U V W X Y Z", "𝔸𝔹ℂ𝔻𝔼𝔽𝔾ℍ𝕀𝕁𝕂𝕃𝕄ℕ𝕆ℙℚℝ𝕊𝕋𝕌𝕍𝕎𝕏𝕐ℤ");
  var SUP = table("0 1 2 3 4 5 6 7 8 9 + - = ( ) a b c d e f g h i j k l m n o p r s t u v w x y z ′",
    "⁰¹²³⁴⁵⁶⁷⁸⁹⁺⁻⁼⁽⁾ᵃᵇᶜᵈᵉᶠᵍʰⁱʲᵏˡᵐⁿᵒᵖʳˢᵗᵘᵛʷˣʸᶻ′");
  var SUB = table("0 1 2 3 4 5 6 7 8 9 + - = ( ) a e h i j k l m n o p r s t u v x", "₀₁₂₃₄₅₆₇₈₉₊₋₌₍₎ₐₑₕᵢⱼₖₗₘₙₒₚᵣₛₜᵤᵥₓ");
  var SYMBOLS = own({
    alpha: "α", beta: "β", gamma: "γ", delta: "δ", epsilon: "ε", varepsilon: "ε", zeta: "ζ", eta: "η", theta: "θ",
    vartheta: "ϑ", iota: "ι", kappa: "κ", lambda: "λ", mu: "μ", nu: "ν", xi: "ξ", pi: "π", varpi: "ϖ", rho: "ρ",
    varrho: "ϱ", sigma: "σ", varsigma: "ς", tau: "τ", upsilon: "υ", phi: "φ", varphi: "φ", chi: "χ", psi: "ψ",
    omega: "ω", Gamma: "Γ", Delta: "Δ", Theta: "Θ", Lambda: "Λ", Xi: "Ξ", Pi: "Π", Sigma: "Σ", Upsilon: "Υ",
    Phi: "Φ", Psi: "Ψ", Omega: "Ω", ell: "ℓ", hbar: "ℏ", aleph: "ℵ", wp: "℘", Re: "ℜ", Im: "ℑ", infty: "∞",
    emptyset: "∅", varnothing: "∅", partial: "∂", nabla: "∇", forall: "∀", exists: "∃", neg: "¬", lnot: "¬",
    sum: "∑", prod: "∏", coprod: "∐", int: "∫", oint: "∮", bigcup: "⋃", bigcap: "⋂", bigoplus: "⨁",
    bigotimes: "⨂", circ: "∘", pm: "±", mp: "∓", prime: "′", ast: "∗", star: "⋆", bullet: "•",
    langle: "⟨", rangle: "⟩", lfloor: "⌊", rfloor: "⌋", lceil: "⌈", rceil: "⌉", vert: "|", lvert: "|", rvert: "|",
    Vert: "‖", lVert: "‖", rVert: "‖", dots: "…", ldots: "…", cdots: "⋯", dotsc: "…", dotsb: "⋯", vdots: "⋮",
    top: "⊤", bot: "⊥", triangle: "△",
    quad: " ", qquad: " ", colon: ": ", bmod: " mod ", mod: " mod ",
    // Relations, arrows and binary operators keep a space each side; runs of spaces collapse.
    to: " → ", rightarrow: " → ", leftarrow: " ← ", longrightarrow: " → ", Rightarrow: " ⇒ ", Leftarrow: " ⇐ ",
    implies: " ⇒ ", Leftrightarrow: " ⇔ ", iff: " ⇔ ", leftrightarrow: " ↔ ", mapsto: " ↦ ", hookrightarrow: " ↪ ",
    uparrow: " ↑ ", downarrow: " ↓ ",
    twoheadrightarrow: " ↠ ", le: " ≤ ", leq: " ≤ ", ge: " ≥ ", geq: " ≥ ", ne: " ≠ ", neq: " ≠ ", ll: " ≪ ",
    gg: " ≫ ", approx: " ≈ ", sim: " ∼ ", simeq: " ≃ ", cong: " ≅ ", equiv: " ≡ ", propto: " ∝ ", in: " ∈ ",
    notin: " ∉ ", ni: " ∋ ", subset: " ⊂ ", subseteq: " ⊆ ", subsetneq: " ⊊ ", supset: " ⊃ ", supseteq: " ⊇ ",
    cup: " ∪ ", cap: " ∩ ", setminus: " ∖ ", times: " × ", cdot: " · ", otimes: " ⊗ ", oplus: " ⊕ ", wedge: " ∧ ",
    land: " ∧ ", vee: " ∨ ", lor: " ∨ ", mid: " ∣ ", nmid: " ∤ ", parallel: " ∥ ", perp: " ⊥ ", vdash: " ⊢ ",
    models: " ⊨ ", lhd: " ◁ ", unlhd: " ⊴ ", trianglelefteq: " ⊴ ", triangleleft: " ◁ "
  });
  // After \not, a relation's negated sign.
  var NEGATED = own({"∈": "∉", "∋": "∌", "=": "≠", "≤": "≰", "≥": "≱", "⊂": "⊄", "⊆": "⊈", "⊃": "⊅", "⊇": "⊉", "∣": "∤",
    "∥": "∦", "≡": "≢", "∼": "≁", "≃": "≄", "≅": "≇", "≈": "≉", "⊢": "⊬", "⊨": "⊭"});
  var ESCAPES = own({",": " ", ";": " ", ":": " ", " ": " ", "!": "", "|": "‖", "\\": " "});
  var OPERATORS = table("arccos arcsin arctan arg cos cosh cot coth csc deg det dim exp gcd hom inf ker lcm lg lim liminf " +
    "limsup ln log max min Pr sec sin sinh sup tan tanh");
  var FONTS = table("mathrm mathit mathbf mathsf mathtt mathcal mathscr mathfrak text textrm textit textbf " +
    "textsf boldsymbol bm");
  var ACCENTS = own({bar: "\u0304", overline: "\u0305", hat: "\u0302", widehat: "\u0302", tilde: "\u0303",
    widetilde: "\u0303", vec: "\u20d7", dot: "\u0307", ddot: "\u0308"});
  var SIZES = table("left right middle big Big bigg Bigg bigl bigr Bigl Bigr biggl biggr Biggl Biggr");
  var STYLES = table("limits nolimits displaystyle textstyle scriptstyle scriptscriptstyle");

  // Whether s needs no parentheses beside a "/" or a script: one character, letters and digits, or one parenthesis.
  function atomic(s) {
    if (Array.from(s).length <= 1 || /^[A-Za-z0-9]+$/.test(s)) return true;
    if (s.charAt(0) !== "(" || s.charAt(s.length - 1) !== ")") return false;
    for (var depth = 0, index = 0; index < s.length; index++) {
      depth += s.charAt(index) === "(" ? 1 : s.charAt(index) === ")" ? -1 : 0;
      if (!depth && index < s.length - 1) return false;
    }
    return true;
  }
  function paren(s) { return atomic(s) ? s : "(" + s + ")"; }
  // A script in Unicode's raised or lowered characters when it has one for each, else after its ^ or _.
  function script(s, mark) {
    var chars = Array.from(s.replace(/ /g, "")), lifted = mark === "^" ? SUP : SUB;
    if (!chars.length) return "";
    var up = chars.map(function (c) { return lifted[c]; });
    return up.every(Boolean) ? up.join("") : mark + paren(chars.join(""));
  }

  function math(tex) {
    tex = String(tex || "");
    var at = 0;
    // An operator name, with a space when a letter or a command follows it.
    function spaced(word) { return word + (/[A-Za-z\\]/.test(tex.charAt(at)) ? " " : ""); }
    // One argument: a braced group, a command or a character.
    function argument() {
      while (tex.charAt(at) === " ") at++;
      if (tex.charAt(at) === "{") { at++; return group(true); }
      if (tex.charAt(at) === "\\") return command();
      return character();
    }
    // The character at at, whole even above U+FFFF, where charAt would split it.
    function character() {
      if (at >= tex.length) { at++; return ""; }
      var c = String.fromCodePoint(tex.codePointAt(at)); at += c.length;
      return c;
    }
    // Text up to the brace that closes the group, or to the end.
    function group(braced) {
      var out = "";
      while (at < tex.length) {
        var c = tex.charAt(at++);
        if (c === "}") { if (braced) return out; }
        else if (c === "{") out += group(true);
        else if (c === "\\") { at--; out += command(); }
        else if (c === "^" || c === "_") out = out.replace(/ $/, "") + script(argument(), c);
        else out += c === "~" || c === "&" ? " " : c;
      }
      return out;
    }
    function command() {
      var name = /^[A-Za-z]+/.exec(tex.slice(++at));
      if (!name) { var c = character(); return ESCAPES[c] !== undefined ? ESCAPES[c] : c; }
      name = name[0]; at += name.length;
      if (tex.charAt(at) === "*") at++;
      if (/^[dt]?frac$/.test(name)) { var top = argument(); return paren(top) + "/" + paren(argument()); }
      if (name === "binom") { var n = argument(); return "(" + n + " choose " + argument() + ")"; }
      if (name === "sqrt") {
        var index = "";
        if (tex.charAt(at) === "[") {
          var end = tex.indexOf("]", at); if (end < 0) end = tex.length;
          index = script(math(tex.slice(at + 1, end)), "^"); at = end + 1;
        }
        return index + "√" + paren(argument());
      }
      if (name === "mathbb") return Array.from(argument()).map(function (c) { return DOUBLE[c] || c; }).join("");
      if (name === "operatorname") return spaced(argument());
      if (FONTS[name]) return argument();
      if (ACCENTS[name]) return Array.from(argument()).map(function (c) { return c + ACCENTS[name]; }).join("");
      if (name === "pmod") return " (mod " + argument() + ")";
      if (name === "begin" || name === "end") { argument(); return " "; }
      if (name === "not") {
        var sign = argument(), bare = sign.trim();
        return sign.replace(bare, function () { return NEGATED[bare] || bare + "\u0338"; });
      }
      if (SIZES[name]) { if (tex.charAt(at) === ".") at++; return ""; }
      if (STYLES[name]) return "";
      if (OPERATORS[name]) return spaced(name);
      return SYMBOLS[name] !== undefined ? SYMBOLS[name] : name;
    }
    // Runs of spaces collapse, and none stays inside a bracket or before a comma.
    return group(false).replace(/\s+/g, " ").replace(/([(\[{⟨]) /g, "$1").replace(/ ([)\]}⟩,])/g, "$1").trim();
  }

  window.AutoformTexPlain = {math: math};
})();

/* Multiscale map layout: pure, synchronous functions over the autoform-project-map/v1 payload.
 * World units are stage pixels at the opening pose. A part's children are packed as if the part
 * were fitted to the stage, so every level reads the same at its own zoom; a parent's box never
 * changes once placed, so zooming in reveals its children inside it, whatever loads first. Pack
 * once per load and refit the camera on resize; re-pack only when the stage turns between portrait
 * and landscape. Edges are [user, used, statement, proof]; routes run from the used part to its
 * user, only through the gaps between boxes, so no route crosses a box or its label.
 */
(function () {
  "use strict";

  // Screen pixels at the zoom where a part is fitted to the stage. A header band holds a 15 px
  // title and a 12 px status line, and a box keeps room below it for what zooming in reveals; a
  // box narrower or shorter than MIN_W by MIN_H gets its label deeper in. GAP is wide enough for
  // a few lanes of routes between neighbouring boxes.
  var BAND = 52, BAND2 = 72, PAD = 12, GAP = 16, MIN_W = 150, MIN_H = 120, ASPECT = 1.6, LANE = 5, RADIUS = 6;
  // Mean advance of a 15 px semibold title character, for choosing one or two title lines.
  var TITLE_EM = 8.4;
  // The band height a lone title line needs, and a compact one: a 13 px title in a box at
  // least COMPACT_W wide, so narrow parts are still named.
  var LABEL_BAND = 36, COMPACT_BAND = 20, COMPACT_W = 60;
  // The advance between wrapped title lines, and the extra rows the progress and API details take.
  var LINE = 20, COMPACT_LINE = 16, DETAIL_LINE = 18;
  // The most routes a sibling set shows at rest; the rest appear with their parts.
  var MAX_REST = 18;

  function byKey(a, b) { return a < b ? -1 : a > b ? 1 : 0; }
  function inset(rect, d) {
    return {x: rect.x + d, y: rect.y + d, w: Math.max(0, rect.w - 2 * d), h: Math.max(0, rect.h - 2 * d)};
  }
  // World units per screen pixel at the zoom that fits this content box to the stage.
  function unitsPerPixel(content, stage) { return Math.max(content.w / stage.w, content.h / stage.h); }
  // A box's content area; its margin is the padding beside and below it, where routes may run.
  function contentOf(box) {
    var unit = box.unit, band = box.band === undefined ? BAND : box.band, pad = box.pad === undefined ? PAD : box.pad;
    return {x: box.x + pad * unit, y: box.y + band * unit, w: Math.max(0, box.w - 2 * pad * unit),
      h: Math.max(0, box.h - (band + pad) * unit), margin: pad * unit};
  }
  // A title too long for one line at this width takes two, when the box is tall enough for both.
  function bandFor(title, box) {
    var width = box.w / box.unit - 2 * PAD, height = box.h / box.unit;
    return (title || "").length * TITLE_EM > width && height >= BAND2 + PAD ? BAND2 : BAND;
  }

  // Prerequisites first: a weighted greedy feedback-arc order (Eades, Lin and Smyth), so most link
  // weight runs forward. Ties keep the payload's order, which is the book's reading order.
  function dependencyOrder(items, edges) {
    var rank = items.map(function (item) { return item.id; });
    var alive = new Set(rank), before = new Map(), after = new Map();
    rank.forEach(function (id) { before.set(id, new Map()); after.set(id, new Map()); });
    edges.forEach(function (edge) {
      var user = edge[0], used = edge[1], weight = (edge[2] || 0) + (edge[3] || 0);
      if (user === used || !weight || !alive.has(user) || !alive.has(used)) return;
      after.get(used).set(user, (after.get(used).get(user) || 0) + weight);
      before.get(user).set(used, (before.get(user).get(used) || 0) + weight);
    });
    function live(map) {
      var total = 0;
      map.forEach(function (weight, id) { if (alive.has(id)) total += weight; });
      return total;
    }
    var head = [], tail = [];
    while (alive.size) {
      var picked = null, i;
      for (i = 0; i < rank.length && !picked; i++) {
        if (alive.has(rank[i]) && !live(before.get(rank[i]))) { picked = rank[i]; head.push(picked); }
      }
      if (!picked) {
        for (i = rank.length - 1; i >= 0 && !picked; i--) {
          if (alive.has(rank[i]) && !live(after.get(rank[i]))) { picked = rank[i]; tail.push(picked); }
        }
      }
      if (!picked) {
        var best = -Infinity;
        for (i = 0; i < rank.length; i++) {
          if (!alive.has(rank[i])) continue;
          var delta = live(after.get(rank[i])) - live(before.get(rank[i]));
          if (delta > best) { best = delta; picked = rank[i]; }
        }
        head.push(picked);
      }
      alive.delete(picked);
    }
    return head.concat(tail.reverse());
  }

  // Scale values to fill total, none below floor (water-filling); with no room for every floor,
  // the shares even out instead.
  function fill(values, total, floor) {
    var n = values.length, clamped = new Array(n).fill(false), out = values.slice();
    floor = Math.min(floor, total / n);
    for (var round = 0; round <= n; round++) {
      var free = total, weight = 0, i;
      for (i = 0; i < n; i++) { if (clamped[i]) free -= floor; else weight += values[i]; }
      var scale = weight ? free / weight : 0, changed = false;
      for (i = 0; i < n; i++) {
        if (clamped[i]) { out[i] = floor; continue; }
        out[i] = values[i] * scale;
        if (out[i] < floor) { clamped[i] = true; changed = true; }
      }
      if (!changed) break;
    }
    return out;
  }

  // Ordered strip treemap: rows top to bottom, items left to right in the given order. A row closes
  // when the next item would worsen its worst aspect ratio (against ASPECT, since labels run across)
  // or would leave an item narrower than minW. Areas follow the weights where the minimums allow;
  // when the box cannot give every item a readable size, the minimums go and every item keeps a
  // good shape instead, so zooming in makes it readable.
  function strips(order, weightOf, box, minW, minH, aspect) {
    var total = 0;
    order.forEach(function (id) { total += weightOf(id); });
    var scale = total ? box.w * box.h / total : 0;
    function worst(items, area) {
      var height = area / box.w, ratio = 1;
      items.forEach(function (id) {
        var r = weightOf(id) * scale / height / height / aspect;
        ratio = Math.max(ratio, r, 1 / r);
      });
      return ratio;
    }
    function group(perRow) {
      var rows = [], row = [], rowArea = 0;
      order.forEach(function (id) {
        var area = weightOf(id) * scale;
        if (row.length && (row.length >= perRow || worst(row.concat([id]), rowArea + area) > worst(row, rowArea))) {
          rows.push({ids: row, area: rowArea}); row = []; rowArea = 0;
        }
        row.push(id); rowArea += area;
      });
      if (row.length) rows.push({ids: row, area: rowArea});
      // A last row flatter than the merged one joins the row above.
      if (rows.length > 1) {
        var last = rows[rows.length - 1], prev = rows[rows.length - 2], merged = prev.ids.concat(last.ids);
        if (merged.length <= perRow &&
            worst(merged, prev.area + last.area) < Math.max(worst(prev.ids, prev.area), worst(last.ids, last.area))) {
          rows.splice(rows.length - 2, 2, {ids: merged, area: prev.area + last.area});
        }
      }
      return rows;
    }
    var perRow = Math.max(1, Math.floor(box.w / minW)), rows = group(perRow);
    // Too many rows to give each a readable height: merge the neighbours that suffer least.
    var maxRows = Math.max(1, Math.floor(box.h / minH));
    while (rows.length > maxRows) {
      var best = -1, bestCost = Infinity;
      for (var i = 0; i + 1 < rows.length; i++) {
        if (rows[i].ids.length + rows[i + 1].ids.length > perRow) continue;
        var cost = worst(rows[i].ids.concat(rows[i + 1].ids), rows[i].area + rows[i + 1].area);
        if (cost < bestCost) { bestCost = cost; best = i; }
      }
      if (best < 0) break;
      rows.splice(best, 2, {ids: rows[best].ids.concat(rows[best + 1].ids), area: rows[best].area + rows[best + 1].area});
    }
    function place(rows, floorW, floorH) {
      var heights = fill(rows.map(function (r) { return r.area; }), box.h, floorH);
      var rects = {}, y = box.y;
      rows.forEach(function (r, index) {
        var widths = fill(r.ids.map(weightOf), box.w, floorW), x = box.x;
        r.ids.forEach(function (id, k) {
          rects[id] = {x: x, y: y, w: widths[k], h: heights[index], row: index};
          x += widths[k];
        });
        y += heights[index];
      });
      // Each item's zoom, against this level's, at which its box is big enough for its label; a
      // sliver needs a lot. Their geometric mean weighs every item alike, large or small.
      var worst = 0, logs = 0, count = 0;
      for (var id in rects) {
        var r = rects[id], zoom = Math.max(minW / Math.max(r.w, 1e-9), minH / Math.max(r.h, 1e-9));
        worst = Math.max(worst, zoom); logs += Math.log(zoom); count++;
      }
      return {rects: rects, readable: worst <= 1 / 0.99, zoom: Math.exp(logs / count)};
    }
    var kept = place(rows, minW, minH);
    return kept.readable ? [kept] : [kept, place(group(Infinity), 0, 0)];
  }

  // Strips run across a box, or down it as columns. A layout where every item is readable wins,
  // rows first, since they read like text. Otherwise the one whose items become readable soonest
  // as the camera closes in wins: a wide box with one dominant item would otherwise give it a flat
  // full-width row, and a flat box would give its children slivers.
  function transpose(rect) { return {x: rect.y, y: rect.x, w: rect.h, h: rect.w, row: rect.row}; }
  // Area grows with the square root of a part's statements, so a small part stays a usable box
  // beside a large one; the label carries the count.
  function packOrdered(order, weights, titles, content, unit) {
    var gap = GAP * unit, weightOf = function (id) { return Math.sqrt(Math.max(weights.get(id), 1)); };
    var minW = MIN_W * unit + gap, minH = MIN_H * unit + gap;
    var candidates = strips(order, weightOf, content, minW, minH, ASPECT).map(function (layout) {
      return Object.assign(layout, {columns: false});
    });
    strips(order, weightOf, transpose(content), minH, minW, 1 / ASPECT).forEach(function (layout) {
      var rects = {};
      for (var key in layout.rects) rects[key] = transpose(layout.rects[key]);
      candidates.push(Object.assign(layout, {rects: rects, columns: true}));
    });
    var packed = candidates.filter(function (layout) { return layout.readable; })[0] ||
      candidates.reduce(function (best, layout) { return layout.zoom < best.zoom * 0.98 ? layout : best; });
    var rects = packed.rects, columns = packed.columns;
    // Gaps shrink in a row of small items, so a small box keeps its shape instead of vanishing.
    var margin = new Map();
    order.forEach(function (id) {
      var r = rects[id], d = Math.min(gap, 0.25 * r.w, 0.25 * r.h);
      margin.set(r.row, Math.min(margin.has(r.row) ? margin.get(r.row) : gap, d));
    });
    var boxes = {};
    order.forEach(function (id, index) {
      var r = inset(rects[id], margin.get(rects[id].row) / 2), box = {x: r.x, y: r.y, w: r.w, h: r.h, unit: unit,
        row: rects[id].row, axis: columns ? "columns" : "rows"};
      // A box too small for a whole band keeps most of its height for its content, so what it
      // holds still opens as the camera closes in; its label waits until the band is tall enough.
      box.band = Math.min(bandFor(titles.get(id), box), 0.4 * r.h / unit);
      box.pad = Math.min(PAD, 0.1 * Math.min(r.w, r.h) / unit);
      boxes[id] = box;
    });
    Object.defineProperty(boxes, "$readable", {value: packed.readable});
    return boxes;
  }

  function summaries(list) {
    return list.map(function (part) { return {id: part.id, title: part.title, weight: part.results}; });
  }
  function weightsOf(items) { return new Map(items.map(function (item) { return [item.id, item.weight]; })); }
  function titlesOf(items) { return new Map(items.map(function (item) { return [item.id, item.title]; })); }

  // The regions, from index.json, at their native size: the opening pose is zoom 1, top-aligned.
  // When the stage is too short for every region at a readable size (a phone with many regions),
  // the world grows downward and the map scrolls. The returned content box is the area the regions
  // are packed in.
  function packLevels(index, stage) {
    var regions = summaries(index.regions), order = dependencyOrder(regions, index.region_edges || []);
    var height = stage.h, root, content, packed;
    for (var attempt = 0; attempt <= regions.length; attempt++) {
      root = {x: 0, y: 0, w: stage.w, h: height, unit: 1, depth: 0}; content = Object.assign(inset(root, PAD), {margin: PAD});
      packed = packOrdered(order, weightsOf(regions), titlesOf(regions), content, 1);
      if (packed.$readable) break;
      height += MIN_H + GAP;
    }
    var boxes = {};
    for (var id in packed) boxes[id] = Object.assign({depth: 1, parent: null}, packed[id]);
    return {root: root, content: content, boxes: boxes};
  }

  // A part's children inside its box, when its file loads. A part that also holds results of its
  // own opens with an "own results" box, keyed by the part id with "#results" appended; beside
  // other children it has a band for the page's title for it, and alone it is the part's whole
  // content.
  function packPart(partData, box, stage) {
    var items = summaries(partData.children || []), own = (partData.results || []).length;
    var id = partData.part.id, ownId = id + "#results", content = contentOf(box), boxes = {};
    var unit = unitsPerPixel(content, stage);
    if (!items.length) {
      if (own) boxes[ownId] = Object.assign({depth: box.depth + 1, parent: id, own: true, unit: unit, row: 0, band: 0, pad: 0}, content);
      return boxes;
    }
    var order = dependencyOrder(items, partData.edges || []), weights = weightsOf(items), titles = titlesOf(items);
    if (own) { order.unshift(ownId); weights.set(ownId, own); }
    var packed = packOrdered(order, weights, titles, content, unit);
    for (var child in packed) {
      boxes[child] = Object.assign({depth: box.depth + 1, parent: id}, packed[child]);
      if (child === ownId) boxes[child].own = true;
    }
    return boxes;
  }

  // One route per linked sibling pair, from the used part to its user; a pair linked both ways is
  // one route with a head at each end, its source the heavier side's used part. Unless everyRoute
  // is set, only the central routes are marked `rest`, at most four for every five boxes and never
  // more than MAX_REST: heaviest first, preferring routes that reach boxes no such route reaches
  // yet. Every route has an orthogonal path through the gaps of area, never in a band.
  function bundleEdges(boxes, edges, area, everyRoute) {
    var pairs = new Map();
    edges.forEach(function (edge) {
      var user = edge[0], used = edge[1];
      if (!boxes[user] || !boxes[used] || user === used) return;
      var a = used < user ? used : user, b = used < user ? user : used, key = a + "\u0000" + b;
      if (!pairs.has(key)) pairs.set(key, {a: a, b: b, ab: [0, 0], ba: [0, 0]});
      var pair = pairs.get(key), side = used === a ? pair.ab : pair.ba;
      side[0] += edge[2] || 0; side[1] += edge[3] || 0;
    });
    var routes = Array.from(pairs.keys()).sort(byKey).map(function (key) {
      var pair = pairs.get(key), forward = pair.ab[0] + pair.ab[1], backward = pair.ba[0] + pair.ba[1];
      var flip = backward > forward, main = flip ? pair.ba : pair.ab, other = flip ? pair.ab : pair.ba;
      var weight = forward + backward;
      return {from: flip ? pair.b : pair.a, to: flip ? pair.a : pair.b, both: forward > 0 && backward > 0,
        weights: [main[0], main[1], other[0], other[1]], kind: main[0] + other[0] > 0 ? "statement" : "proof",
        weight: weight, rest: false};
    });
    var byWeight = routes.slice().sort(function (p, q) { return q.weight - p.weight || byKey(p.from + p.to, q.from + q.to); });
    var budget = everyRoute ? Infinity : Math.min(MAX_REST, Math.max(1, Math.round(Object.keys(boxes).length * 0.8))), shown = 0;
    var reached = new Set();
    // Routes between two unreached boxes first, then routes reaching one, then the heaviest others.
    [2, 1, 0].forEach(function (fresh) {
      byWeight.forEach(function (route) {
        var count = (reached.has(route.from) ? 0 : 1) + (reached.has(route.to) ? 0 : 1);
        if (route.rest || shown >= budget || count < fresh) return;
        route.rest = true; shown++; reached.add(route.from); reached.add(route.to);
      });
    });
    if (routes.length) {
      var first = boxes[routes[0].from];
      if (first.axis === "columns") {
        // Route in the transposed picture, where the columns are rows, then turn it back.
        var flipped = {};
        for (var id in boxes) flipped[id] = Object.assign({}, boxes[id], transpose(boxes[id]));
        // Transposed, the left margin is the top one, which is the parent's band: never route there.
        routeThroughGaps(routes, flipped, Object.assign(transpose(area), {margin: area.margin}), true);
        routes.forEach(function (route) {
          for (var k = 0; k < route.points.length; k += 2) {
            var t = route.points[k]; route.points[k] = route.points[k + 1]; route.points[k + 1] = t;
          }
        });
      } else routeThroughGaps(routes, boxes, area);
    }
    return routes;
  }

  // The gaps of a strip layout: a corridor between each pair of rows and below the last, and in
  // each row the gaps between neighbours plus the side margins. A route leaves its source through
  // the side facing its target, runs along corridors and down or up through row gaps, and enters
  // its target the same way. Routes sharing a corridor or gap take separate lanes.
  function routeThroughGaps(routes, boxes, area, noLeftMargin) {
    var ids = Object.keys(boxes), unit = boxes[ids[0]].unit, rows = [];
    ids.forEach(function (id) {
      var box = boxes[id], r = box.row || 0;
      if (!rows[r]) rows[r] = {top: Infinity, bottom: -Infinity, ids: []};
      rows[r].top = Math.min(rows[r].top, box.y); rows[r].bottom = Math.max(rows[r].bottom, box.y + box.h);
      rows[r].ids.push(id);
    });
    rows = rows.filter(Boolean);
    var rowOf = new Map();
    rows.forEach(function (row, r) {
      row.ids.sort(function (p, q) { return boxes[p].x - boxes[q].x; });
      row.ids.forEach(function (id) { rowOf.set(id, r); });
    });
    var margin = area.margin === undefined ? PAD * unit : area.margin;
    var left = area.x - margin / 2, right = area.x + area.w + margin / 2, floor = area.y + area.h + margin / 2;
    // corridor[c] lies above row c (c = 1 .. rows.length - 1) or below the last row (c = rows.length).
    function corridorY(c) { return c < rows.length ? (rows[c - 1].bottom + rows[c].top) / 2 : (rows[c - 1].bottom + floor) / 2; }
    function corridorWidth(c) { return c < rows.length ? rows[c].top - rows[c - 1].bottom : floor - rows[c - 1].bottom; }
    // The passages through row r: the margins and the gaps between neighbours.
    function passages(r) {
      var list = [{x: right, width: margin, key: "R"}];
      if (!noLeftMargin) list.push({x: left, width: margin, key: "L"});
      var row = rows[r].ids;
      for (var k = 0; k + 1 < row.length; k++) {
        var a = boxes[row[k]], b = boxes[row[k + 1]];
        list.push({x: (a.x + a.w + b.x) / 2, width: b.x - a.x - a.w, key: String(k)});
      }
      return list;
    }
    var hSegments = new Map(), vSegments = new Map();
    // A route's leg along a corridor or through a passage, in the lane list of its gap; lanes() sets its offset.
    function leg(route, map, key, a, b, width, step) {
      if (!map.has(key)) map.set(key, {width: width, list: []});
      var entry = map.get(key);
      entry.width = Math.min(entry.width, width);
      Object.assign(step, {lo: Math.min(a, b), hi: Math.max(a, b), route: route, offset: 0});
      entry.list.push(step); route.legs.push(step);
    }
    routes.forEach(function (route) {
      var a = boxes[route.from], b = boxes[route.to], ra = rowOf.get(route.from), rb = rowOf.get(route.to);
      var ax = a.x + a.w / 2, bx = b.x + b.w / 2;
      route.legs = [];
      if (ra === rb) {
        var row = rows[ra].ids, ia = row.indexOf(route.from), ib = row.indexOf(route.to);
        if (Math.abs(ia - ib) === 1) {
          route.direct = ia < ib ? ["right", "left"] : ["left", "right"];
          return;
        }
        // Same row, not neighbours: along the corridor below the row.
        route.sides = ["bottom", "bottom"];
        leg(route, hSegments, ra + 1, ax, bx, corridorWidth(ra + 1), {h: ra + 1, from: ax, to: bx});
        return;
      }
      var down = rb > ra;
      route.sides = down ? ["bottom", "top"] : ["top", "bottom"];
      var c = down ? ra + 1 : ra, x = ax;
      // Walk through the rows between source and target, one corridor and one passage at a time.
      for (var r = down ? ra + 1 : ra - 1; down ? r < rb : r > rb; r += down ? 1 : -1) {
        var options = passages(r), pick = null, cost = Infinity;
        options.forEach(function (p) {
          var d = Math.abs(p.x - x) + Math.abs(p.x - bx);
          if (d < cost - 1e-9) { cost = d; pick = p; }
        });
        leg(route, hSegments, c, x, pick.x, corridorWidth(c), {h: c, from: x, to: pick.x});
        var next = down ? c + 1 : c - 1;
        // A leg reaches halfway into the corridors on either side, so its lane is shared with every leg in the same
        // column, whatever the row: the side margins line up across all rows.
        leg(route, vSegments, pick.x.toFixed(3), corridorY(c), corridorY(next), pick.width, {x: pick.x, from: c, to: next});
        x = pick.x; c = next;
      }
      leg(route, hSegments, c, x, bx, corridorWidth(c), {h: c, from: x, to: bx});
    });
    // Lanes: greedy interval colouring per corridor, centred in it. A crowded corridor can't keep every lane a few
    // pixels apart, so the `rest` routes take their lanes first and get slots spread across the corridor; the others
    // fill the slots between.
    function lanes(map) {
      map.forEach(function (entry) {
        var tracks = [], resting = 0;
        [true, false].forEach(function (rest) {
          entry.list.filter(function (item) { return !!item.route.rest === rest; })
            .sort(function (p, q) { return p.lo - q.lo || q.route.weight - p.route.weight; })
            .forEach(function (item) {
              var track = tracks.find(function (t) {
                return t.every(function (o) { return o.hi <= item.lo - LANE * unit || o.lo >= item.hi + LANE * unit; });
              });
              if (!track) { track = []; tracks.push(track); }
              track.push(item); item.track = tracks.indexOf(track);
            });
          if (rest) resting = tracks.length;
        });
        var count = tracks.length, spacing = Math.min(LANE * unit, entry.width * 0.85 / Math.max(count, 1)), slots = [], taken = [];
        // Resting tracks at evenly spread slots, the rest in the free slots left to right.
        for (var t = 0; t < resting; t++) { slots[t] = Math.round((t + 0.5) * count / resting - 0.5); taken[slots[t]] = true; }
        for (var free = 0; t < count; t++) { while (taken[free]) free++; slots[t] = free; taken[free] = true; }
        entry.list.forEach(function (item) { item.offset = (slots[item.track] - (count - 1) / 2) * spacing; });
      });
    }
    lanes(hSegments); lanes(vSegments);
    // Ports: spread over the middle of each side, ordered by where each route goes next.
    var ports = new Map();
    routes.forEach(function (route) {
      var a = boxes[route.from], b = boxes[route.to];
      var s = route.direct || route.sides, legs = route.legs;
      var nextA = route.direct ? b.y + b.h / 2 : legs.length ? legs[0].to : 0;
      var nextB = route.direct ? a.y + a.h / 2 : legs.length ? legs[legs.length - 1].from : 0;
      [[route.from, s[0], nextA, 0], [route.to, s[1], nextB, 1]].forEach(function (end) {
        var key = end[0] + "\u0000" + end[1];
        if (!ports.has(key)) ports.set(key, []);
        ports.get(key).push({route: route, end: end[3], toward: end[2]});
      });
    });
    ports.forEach(function (list, key) {
      var parts = key.split("\u0000"), box = boxes[parts[0]], side = parts[1];
      list.sort(function (p, q) { return p.toward - q.toward || byKey(p.route.from + p.route.to, q.route.from + q.route.to); });
      list.forEach(function (slot, i) {
        var t = 0.15 + 0.7 * (i + 1) / (list.length + 1);
        var point = side === "top" ? [box.x + box.w * t, box.y] : side === "bottom" ? [box.x + box.w * t, box.y + box.h] :
          side === "left" ? [box.x, box.y + box.h * t] : [box.x + box.w, box.y + box.h * t];
        slot.route[slot.end ? "endPort" : "startPort"] = point;
      });
    });
    // Boxes above and below a corridor spread their ports independently, so a port on one could meet a port on the
    // other across it, and the two stubs would read as one line. Each corridor's ports keep a lane apart, inside their
    // own faces: one sweep pushes right, a second pulls back from the faces' ends.
    var facing = new Map();
    ports.forEach(function (list, key) {
      var parts = key.split("\u0000"), box = boxes[parts[0]], side = parts[1];
      if (side !== "top" && side !== "bottom") return;
      var corridor = rowOf.get(parts[0]) + (side === "bottom" ? 1 : 0);
      if (!facing.has(corridor)) facing.set(corridor, []);
      list.forEach(function (slot) {
        facing.get(corridor).push({point: slot.route[slot.end ? "endPort" : "startPort"], lo: box.x + box.w * 0.1, hi: box.x + box.w * 0.9});
      });
    });
    facing.forEach(function (items) {
      items.sort(function (p, q) { return p.point[0] - q.point[0]; });
      for (var i = 1; i < items.length; i++) items[i].point[0] = Math.min(items[i].hi, Math.max(items[i].point[0], items[i - 1].point[0] + LANE * unit));
      for (i = items.length - 2; i >= 0; i--) items[i].point[0] = Math.max(items[i].lo, Math.min(items[i].point[0], items[i + 1].point[0] - LANE * unit));
    });
    routes.forEach(function (route) {
      var s = route.startPort, e = route.endPort, points = [s[0], s[1]];
      if (route.direct) {
        var y = (s[1] + e[1]) / 2;
        points.push(s[0], y, e[0], y);
      } else {
        var x = s[0], y0 = null;
        route.legs.forEach(function (leg) {
          if (leg.h !== undefined) {
            y0 = corridorY(leg.h) + leg.offset;
            points.push(x, y0);
          } else {
            x = leg.x + leg.offset;
            points.push(x, y0);
          }
        });
        points.push(e[0], y0);
      }
      points.push(e[0], e[1]);
      route.points = simplify(points);
      route.radius = RADIUS * unit;
      delete route.startPort; delete route.endPort; delete route.legs; delete route.sides; delete route.direct;
    });
  }

  // Drop repeated and collinear points from an orthogonal polyline.
  function simplify(points) {
    var out = [];
    for (var i = 0; i < points.length; i += 2) {
      var n = out.length;
      if (n >= 2 && Math.abs(out[n - 2] - points[i]) < 1e-6 && Math.abs(out[n - 1] - points[i + 1]) < 1e-6) continue;
      if (n >= 4) {
        var ax = out[n - 4], ay = out[n - 3], bx = out[n - 2], by = out[n - 1];
        if ((Math.abs(ax - bx) < 1e-6 && Math.abs(bx - points[i]) < 1e-6) ||
            (Math.abs(ay - by) < 1e-6 && Math.abs(by - points[i + 1]) < 1e-6)) { out[n - 2] = points[i]; out[n - 1] = points[i + 1]; continue; }
      }
      out.push(points[i], points[i + 1]);
    }
    return out;
  }

  // A view's links implied by others show only around a selected result, so they are routed the
  // first time `implied` is read. Out here, the getter keeps alive only what routing them needs,
  // not the scratch state of the layout that made the view.
  function routeImpliedWhenRead(view, cards, implied, area) {
    var routes = null;
    Object.defineProperty(view, "implied", {enumerable: true, get: function () {
      return routes || (routes = bundleEdges(cards, implied, area, true));
    }});
    return view;
  }

  // The result view inside a part, in the explorer's style: prerequisites above their users, each
  // cycle condensed into one layer, links implied by others hidden at rest and kept for selection.
  // Cards keep one size (CARD_W by CARD_H at the zoom where the part is fitted, or smaller when
  // many share the box) and sit in rows of at most `cols`, chosen to fill the box best. Links to
  // results outside the part become per-card stub counts. Returns {cards, routes, implied, stubs}.
  var CARD_W = 200, CARD_H = 64, COL_GAP = 24, ROW_GAP = 40;
  function layoutCommunity(results, resultEdges, boundaryEdges, ownBox) {
    // An own box beside other children keeps its band for its title.
    var box = ownBox.band ? Object.assign(contentOf(ownBox), {unit: ownBox.unit}) : ownBox;
    var ids = results.map(function (result) { return result.id; }), at = new Map();
    ids.forEach(function (id, index) { at.set(id, index); });
    var n = ids.length, after = ids.map(function () { return []; });
    var links = [];
    (resultEdges || []).forEach(function (edge) {
      var user = at.get(edge[0]), used = at.get(edge[1]);
      if (user === undefined || used === undefined || user === used) return;
      after[used].push(user); links.push(edge);
    });
    // Strongly connected components (Tarjan, iterative), numbered in reverse topological order.
    var index = 0, stack = [], onStack = new Array(n).fill(false), low = new Array(n), num = new Array(n).fill(-1);
    var component = new Array(n).fill(-1), components = [];
    for (var root = 0; root < n; root++) {
      if (num[root] >= 0) continue;
      var work = [[root, 0]];
      num[root] = low[root] = index++; stack.push(root); onStack[root] = true;
      while (work.length) {
        var frame = work[work.length - 1], v = frame[0];
        if (frame[1] < after[v].length) {
          var w = after[v][frame[1]++];
          if (num[w] < 0) { num[w] = low[w] = index++; stack.push(w); onStack[w] = true; work.push([w, 0]); }
          else if (onStack[w]) low[v] = Math.min(low[v], num[w]);
          continue;
        }
        work.pop();
        if (work.length) low[work[work.length - 1][0]] = Math.min(low[work[work.length - 1][0]], low[v]);
        if (low[v] === num[v]) {
          var members = [], x;
          do { x = stack.pop(); onStack[x] = false; component[x] = components.length; members.push(x); } while (x !== v);
          components.push(members.sort(function (a, b) { return a - b; }));
        }
      }
    }
    // Layers by longest path from the prerequisites; Tarjan's numbering is reverse topological.
    var count = components.length, layer = new Array(count).fill(0), next = components.map(function () { return new Set(); });
    for (v = 0; v < n; v++) after[v].forEach(function (u) { if (component[u] !== component[v]) next[component[v]].add(component[u]); });
    for (var c = count - 1; c >= 0; c--) next[c].forEach(function (d) { layer[d] = Math.max(layer[d], layer[c] + 1); });
    // Transitive reduction between components: keep c -> d unless d is reached another way.
    var reach = components.map(function () { return new Set(); }), kept = components.map(function () { return new Set(); });
    for (c = 0; c < count; c++) {
      var targets = Array.from(next[c]).sort(function (a, b) { return layer[a] - layer[b] || b - a; });
      targets.forEach(function (d) {
        if (!reach[c].has(d)) kept[c].add(d);
        reach[c].add(d); reach[d].forEach(function (e) { reach[c].add(e); });
      });
    }
    // Rows: each layer's components in payload order, a cycle's members side by side, wrapped at
    // cols without splitting a cycle that fits one row; then barycentre sweeps.
    var byLayer = [];
    for (c = count - 1; c >= 0; c--) {
      if (!byLayer[layer[c]]) byLayer[layer[c]] = [];
      byLayer[layer[c]].push(components[c]);
    }
    byLayer = byLayer.filter(Boolean).map(function (list) { return list.sort(function (a, b) { return a[0] - b[0]; }); });
    // Layered rows keep every layer on rows of its own; folded rows flow the same reading order
    // into rows like text, for a deep map in a wide box. Layered wins unless folding fits a
    // quarter better.
    function layered(cols) {
      var rows = [];
      byLayer.forEach(function (list) {
        var row = [];
        list.forEach(function (members) {
          if (row.length && row.length + members.length > cols && members.length <= cols) { rows.push(row); row = []; }
          members.forEach(function (member) {
            if (row.length === cols) { rows.push(row); row = []; }
            row.push(member);
          });
        });
        if (row.length) rows.push(row);
      });
      return rows;
    }
    var reading = [].concat.apply([], byLayer.map(function (list) { return [].concat.apply([], list); }));
    function folded(cols) {
      var rows = [];
      for (var k = 0; k < reading.length; k += cols) rows.push(reading.slice(k, k + cols));
      return rows;
    }
    var best = null;
    for (var cols = 1; cols <= Math.max(1, Math.min(n, 12)); cols++) {
      [[layered(cols), 1.25, false], [folded(cols), 1, true]].forEach(function (candidate) {
        var rows = candidate[0], width = cols * CARD_W + (cols - 1) * COL_GAP;
        var height = rows.length * CARD_H + (rows.length - 1) * ROW_GAP + 2 * PAD;
        var fit = Math.min(box.w / (width + 2 * PAD), box.h / height), score = fit * candidate[1];
        if (!best || score > best.score + 1e-9) best = {cols: cols, rows: rows, width: width, height: height, fit: fit, score: score, fold: candidate[2]};
      });
    }
    var rowsOf = best.rows, rowOf = new Array(n), slot = new Array(n);
    rowsOf.forEach(function (row, r) { row.forEach(function (member, k) { rowOf[member] = r; slot[member] = k; }); });
    // Direct links run inside a cycle or survive the reduction; the others are implied by them.
    var direct = [], implied = [];
    links.forEach(function (edge) {
      var cu = component[at.get(edge[0])], cv = component[at.get(edge[1])];
      (cu === cv || kept[cv].has(cu) ? direct : implied).push(edge);
    });
    var shown = direct.map(function (edge) { return [at.get(edge[1]), at.get(edge[0])]; });
    for (var sweep = 0; sweep < (best.fold ? 0 : 4); sweep++) {
      var downward = sweep % 2 === 0;
      for (var r = downward ? 1 : rowsOf.length - 2; downward ? r < rowsOf.length : r >= 0; r += downward ? 1 : -1) {
        var row = rowsOf[r], centre = new Map();
        row.forEach(function (member) {
          var near = shown.filter(function (pair) { return downward ? pair[1] === member && rowOf[pair[0]] < r : pair[0] === member && rowOf[pair[1]] > r; })
            .map(function (pair) { return slot[downward ? pair[0] : pair[1]]; });
          centre.set(member, near.length ? near.reduce(function (a, b) { return a + b; }, 0) / near.length : slot[member]);
        });
        row.sort(function (a, b) { return centre.get(a) - centre.get(b) || a - b; });
        row.forEach(function (member, k) { slot[member] = k; });
      }
    }
    // Scale to the box, never past the size cards have when the part is fitted to the stage.
    var scale = Math.min(best.fit, box.unit);
    var x0 = box.x + (box.w - (best.width + 2 * PAD) * scale) / 2 + PAD * scale, y0 = box.y + PAD * scale;
    var cards = {};
    rowsOf.forEach(function (row, r) {
      var indent = (best.cols - row.length) * (CARD_W + COL_GAP) / 2;
      row.forEach(function (member, k) {
        cards[ids[member]] = {x: x0 + (indent + k * (CARD_W + COL_GAP)) * scale, y: y0 + r * (CARD_H + ROW_GAP) * scale,
          w: CARD_W * scale, h: CARD_H * scale, unit: scale, row: r};
      });
    });
    var area = {x: x0, y: y0, w: best.width * scale, h: (rowsOf.length * CARD_H + (rowsOf.length - 1) * ROW_GAP) * scale};
    // Every result route shows: the reduction already chose them.
    var routes = bundleEdges(cards, direct, area, true);
    var stubs = {};
    (boundaryEdges || []).forEach(function (edge) {
      var inside = at.has(edge[0]) ? edge[0] : at.has(edge[1]) ? edge[1] : null;
      if (inside === null || (at.has(edge[0]) && at.has(edge[1]))) return;
      var entry = stubs[inside] || (stubs[inside] = {uses: 0, usedBy: 0});
      if (inside === edge[0]) entry.uses++; else entry.usedBy++;
    });
    return routeImpliedWhenRead({cards: cards, routes: routes, stubs: stubs, fold: best.fold}, cards, implied, area);
  }

  // Labels for the boxes on screen at this camera. A box at least MIN_W wide whose band holds a title
  // line gets a full label; one at least COMPACT_W wide gets a compact one (13 px lines);
  // deeper boxes gain theirs as the camera closes in. A box whose band is still too thin, but whose
  // height has room for the line, gets it as an overlay over its top. An overlay covers the top of
  // its box's content, so a descendant's label under it moves just below it, or goes when its box
  // has no room there. A box running above the stage's top (`stage.top`, below whatever the page
  // pins there) keeps its title in view there, as an overlay, while the box has room for it, unless
  // it holds the stage's centre or is the pinned part (`stage.pinned`) or around it. Labels come shallowest first. A box in `closed` (an object keyed by id) shows nothing inside, so its
  // title may wrap down the whole box: `lines` is the most it can take.
  function placeLabels(boxes, camera, stage, closed) {
    var labels = [], placed = {}, top = stage.top || 0, pinned = {};
    for (var at = stage.pinned; at && boxes[at]; at = boxes[at].parent) pinned[at] = true;
    Object.keys(boxes).sort(function (a, b) { return (boxes[a].depth || 0) - (boxes[b].depth || 0) || byKey(a, b); }).forEach(function (id) {
      var box = boxes[id];
      var x = (box.x - camera.x) * camera.z, y = (box.y - camera.y) * camera.z;
      var w = box.w * camera.z, h = box.h * camera.z, band = box.band * box.unit * camera.z, pad = box.pad * box.unit * camera.z;
      if (x >= stage.w || y >= stage.h || x + w <= 0 || y + h <= top || !box.band) return;
      var compact = w < 0.9 * MIN_W, need = compact ? COMPACT_BAND : 0.9 * LABEL_BAND;
      if (w < COMPACT_W) return;
      var inBand = band >= need;
      if (!inBand && h < (compact ? COMPACT_BAND : LABEL_BAND)) return;
      // How many lines the title takes in a band `b` tall, and whether the results line shows under it.
      function fill(b) {
        return {lines: !compact && box.band === BAND2 && b >= 0.9 * BAND2 ? 2 : 1,
          detail: !compact && inBand && Math.min(b, h) >= 0.9 * BAND ? "meta" : "title"};
      }
      var label = Object.assign({id: id, x: x + pad, y: y, w: w - 2 * pad, band: inBand ? band : need, overlay: !inBand, compact: compact}, fill(band));
      // The title as an overlay at `at`, when the box has room for it there.
      function moveTo(at) {
        if (at + need > y + h) return false;
        Object.assign(label, {y: at, band: need, overlay: true, lines: 1, detail: "title", held: false});
        return true;
      }
      // A title held at the stage's top keeps its band's height, up to BAND2, and its lines and results line, while the
      // box has room, and gives them up as the box leaves, so the page draws it as in its band until the box is going.
      function hold(at) {
        if (!moveTo(at)) return false;
        if (inBand && !compact) Object.assign(label, fill(label.band = Math.max(need, Math.min(band, BAND2, y + h - at))));
        label.held = true;
        return true;
      }
      // The pinned part, the parts around it and the box around the stage's centre hold the view, which the page's trail
      // and pinned title name, so only the boxes beside it keep their titles at the top.
      var around = pinned[id] || x <= stage.w / 2 && x + w >= stage.w / 2 && y <= stage.h / 2 && y + h >= stage.h / 2;
      if (y < top && !around && !hold(top)) return;
      // Outermost first, so a title moved below one cover is then checked against the covers inside it.
      var chain = [];
      for (var up = box.parent; up && boxes[up]; up = boxes[up].parent) chain.unshift(up);
      for (var i = 0; i < chain.length; i++) {
        var cover = placed[chain[i]];
        // An in-band label sits above its box's content, so only an overlay can cover a descendant.
        if (!cover || !cover.overlay) continue;
        var bottom = cover.y + cover.band;
        if (label.y >= bottom || label.y + label.band <= cover.y || label.x >= cover.x + cover.w || label.x + label.w <= cover.x) continue;
        if (!moveTo(bottom)) return;
      }
      // The first title line's baseline, where the page draws it.
      label.baseline = label.y + Math.min(30, label.band / 2 + (compact ? 5 : 6));
      if (closed && closed[id]) {
        // The details follow the last line, and a line's descent stays inside the box.
        var first = label.baseline - label.y + (compact ? 4 : 5);
        var room = y + h - pad - label.y - (label.detail === "meta" ? DETAIL_LINE : 0);
        label.lines = Math.max(label.lines, 1 + Math.floor((room - first) / (compact ? COMPACT_LINE : LINE)));
      }
      labels.push(label); placed[id] = label;
    });
    return labels;
  }

  // The camera that fits a box to the stage, centred.
  function fitCamera(box, stage) {
    var z = Math.min(stage.w / box.w, stage.h / box.h);
    return {x: box.x + box.w / 2 - stage.w / 2 / z, y: box.y + box.h / 2 - stage.h / 2 / z, z: z};
  }

  // The camera for opening a part: its content fitted to the stage, or up to twice as close when
  // most of its children would be too small to label there. Closer in, the view starts at the
  // content's top-left, where reading starts, leaving TITLE_ROOM pixels above it for the page to
  // pin the part's title, since the band itself has scrolled off.
  var TITLE_ROOM = 44;
  function focusCamera(box, children, stage) {
    var content = contentOf(box), fit = fitCamera(content, stage), needs = [];
    for (var id in children) {
      var child = children[id];
      if (child.band) needs.push(Math.max(0.9 * MIN_W / child.w, 0.9 * LABEL_BAND / (child.band * child.unit)));
    }
    needs.sort(function (a, b) { return a - b; });
    var z = Math.min(needs.length ? needs[Math.floor(needs.length / 2)] : 0, 2 * fit.z);
    if (z <= fit.z) return fit;
    return {x: content.x - PAD / z, y: content.y - TITLE_ROOM / z, z: z};
  }

  var api = {packLevels: packLevels, packPart: packPart, bundleEdges: bundleEdges, layoutCommunity: layoutCommunity,
    placeLabels: placeLabels, fitCamera: fitCamera, focusCamera: focusCamera, contentOf: contentOf, dependencyOrder: dependencyOrder,
    constants: {BAND: BAND, GAP: GAP, MIN_W: MIN_W, MIN_H: MIN_H, LINE: LINE, COMPACT_LINE: COMPACT_LINE, TITLE_EM: TITLE_EM,
      TITLE_ROOM: TITLE_ROOM}};
  window.AutoformMapLayout = api;
})();

/* Whole-project map (prototype).
 *
 * One continuous map of the whole project. Regions hold the mathematical parts inside them, and parts hold their
 * results; zooming in opens a part in place, so its boundary and its neighbours stay on screen. Data arrives one level
 * at a time from map/data/: index.json (regions), parts/<shard>.json (a part's children, and its results when
 * it holds them) and search.json (titles and Lean names, loaded on first search).
 *
 * Geometry comes from window.AutoformMapLayout (project-map-layout.js, shipped ahead of this file): world units are
 * stage pixels at the opening pose, a part's children are packed when its file loads, prerequisites come first, and
 * routes run only through the gaps between boxes. This file is the controller: camera, drawing, search, selection,
 * history and the reading pane.
 */
(function () {
  "use strict";

  var host = document.querySelector("[data-project-map]");
  // A book page loads this script and names the search index beside the map's data in data-whole-map: the map makes
  // its own host in the book's stage.
  var bookHost = !host && document.querySelector("[data-whole-map]"), bookStage = bookHost && bookHost.querySelector(".bp-dag-stage");
  if (bookStage) {
    host = document.createElement("div"); host.className = "bp-whole-map";
    host.setAttribute("data-project-map", ""); host.setAttribute("data-embedded", ""); host.setAttribute("data-routes", bookHost.dataset.wholeMap);
    bookStage.appendChild(host);
  }
  if (!host || host.dataset.pmMounted) return;
  host.dataset.pmMounted = "1";
  var L = window.AutoformMapLayout;
  // Inside a book page the map draws in the book's stage. The book has the outline, search, trail and reading pane and
  // owns the address and history: the map tells it which result or part was picked, with an "autoform-map-select" event
  // from the host, and follows the book's host (`book`): data-map-start names the page's node or scope, and
  // data-map-statuses the statuses its filter shows. The map's data and style sit beside the search index (data-routes).
  var embedded = host.hasAttribute("data-embedded"), fromBook = null;
  var book = embedded && host.parentNode && host.parentNode.closest("[data-catalog-src]") || host;

  var routeBase = new URL(host.getAttribute("data-routes") || "dependencies/index.json", location.href);
  var mapBase = new URL(host.getAttribute("data-map") || (embedded ? new URL("map/data/", routeBase).href : "data/"), location.href);
  // Embedded, the map waits for its stylesheet, so the book never shows it unstyled and it packs for the styled stage.
  var styled = Promise.resolve();
  if (embedded) {
    var style = document.createElement("link"); style.rel = "stylesheet"; style.href = new URL("../stylesheets/project-map.css", routeBase).href;
    host.style.visibility = "hidden";
    styled = new Promise(function (resolve) { style.onload = style.onerror = function () { host.style.visibility = ""; resolve(); }; });
    document.head.appendChild(style);
  }
  var reduceMotion = window.matchMedia && matchMedia("(prefers-reduced-motion: reduce)").matches;
  var SVGNS = "http://www.w3.org/2000/svg";
  var ROOT = "#root";
  var RETRY_MS = 5000;              // a part whose file failed to load is asked for again on its own after this long
  var OPEN_W = 140, OPEN_H = 90;   // a part shows its children (as tiles at first) once its box is this big on screen (px)
  var LABEL_MIN_W = 60;            // boxes narrower than this on screen never get a label
  var KID_LABEL_W = 90;            // a part with parts inside opens once its median child is this wide on screen (px)
  var CARD_TEXT_W = 120;           // result cards carry their titles, and their links, once this wide on screen (px)
  var COMPACT_EM = 7.3, META_EM = 6.6, CARD_EM = 7.2, CARD_META_EM = 6.2;  // mean character advances of the label fonts (px)

  // ---------------------------------------------------------------- small helpers
  function el(tag, cls, text) {
    var node = document.createElement(tag);
    if (cls) node.className = cls;
    if (text != null) node.textContent = text;
    return node;
  }
  function svg(tag, attrs) {
    var node = document.createElementNS(SVGNS, tag);
    if (attrs) for (var key in attrs) node.setAttribute(key, attrs[key]);
    return node;
  }
  function num(value) { return Number(value || 0).toLocaleString("en-US"); }
  function clamp(value, low, high) { return Math.max(low, Math.min(high, value)); }
  // A label for places that cannot typeset (map text): split by withMath's MARKUP tokens, code as typed and each
  // formula as tex-plain.js reduces it, never shown with its dollar signs.
  function plain(text) {
    text = String(text || "");
    var out = "", last = 0, match;
    MARKUP.lastIndex = 0;
    while ((match = MARKUP.exec(text))) {
      out += text.slice(last, match.index) + (match[1] !== undefined ? match[1] : match[2] !== undefined ? match[3].trim() :
        window.AutoformTexPlain.math(match[4] !== undefined ? match[4] : match[5]));
      last = MARKUP.lastIndex;
    }
    return out + text.slice(last);
  }
  var DONE = {fully_proved: 1, proved: 1, defined: 1, mathlib: 1};
  var PROGRESS = {can_prove: 1, stated: 1, can_state: 1, conditional: 1, statement_formalized: 1};
  // A project that tracks no Lean says so in its index: every result then looks alike, and the map shows no progress.
  function tracked() { return !model.index || model.index.tracks_lean !== false; }
  function group(status) { return !tracked() ? "planned" : DONE[status] ? "done" : PROGRESS[status] ? "progress" : "planned"; }
  var STATUS_WORDS = {fully_proved: "fully proved", proved: "proved", defined: "defined", mathlib: "in Mathlib",
    can_prove: "ready to prove", stated: "stated", can_state: "ready to state", conditional: "conditional",
    not_ready: "not ready", planned: "planned"};
  function statusWords(status) { return STATUS_WORDS[status] || String(status || "").replace(/_/g, " "); }
  // What a card says of its result: its status, or where the project tracks no Lean, its kind if it has one.
  function standing(row) { return tracked() ? statusWords(row.status) : row.caption || ""; }
  function mix(status) {
    var out = {done: 0, progress: 0, planned: 0};
    for (var key in status || {}) out[group(key)] += status[key];
    return out;
  }
  function progressText(summary) {
    return num(mix(summary.status).done) + " of " + num(summary.results) + " finished";
  }
  // A closed part's tile is tinted by what most of it is.
  function tileKind(status) {
    var counts = mix(status), total = counts.done + counts.progress + counts.planned;
    if (!total) return "planned";
    return counts.done / total >= 0.9 ? "done" : (counts.done + counts.progress) / total >= 0.5 ? "progress" : "planned";
  }
  function color(kind) {
    return getComputedStyle(document.documentElement).getPropertyValue(kind === "done" ? "--pm-proved" : kind === "progress" ? "--pm-progress" : "--pm-planned").trim() || "#999";
  }
  function wrap(text, width, maxLines) {
    // Lines break at ordinary spaces only: a no-break space holds its neighbours together.
    var words = text.split(/[ \t\n]+/), lines = [], line = "";
    words.forEach(function (word) {
      if (!line) line = word;
      else if ((line + " " + word).length <= width) line += " " + word;
      else { lines.push(line); line = word; }
    });
    if (line) lines.push(line);
    if (lines.length > maxLines) { lines = lines.slice(0, maxLines); lines[maxLines - 1] = clip(lines[maxLines - 1] + "…", width); }
    return lines.map(function (l) { return clip(l, width); });
  }
  function clip(text, width) { return text.length > width ? text.slice(0, Math.max(1, width - 1)) + "…" : text; }

  // ---------------------------------------------------------------- data
  // One request per file (at most the index, search and 256 part files); a request that fails or times out is
  // forgotten, so the next use of the file asks again. In the book, the book's router reads the files
  // (blueprint-navigation.js fetchJSON) under its stall timeout and keeps no copy; the standalone page has no router
  // and fetches them itself, giving each request FETCH_MS in all.
  var cache = new Map(), FETCH_MS = 30000;
  function request(url, name, read) {
    var controller = window.AbortController ? new AbortController() : null;
    var timer = setTimeout(function () { if (controller) controller.abort(); }, FETCH_MS);
    return fetch(url, controller ? {signal: controller.signal} : undefined).then(function (response) {
      if (!response.ok) throw new Error("HTTP " + response.status + " for " + name);
      return read(response);
    }).then(function (data) { clearTimeout(timer); return data; }, function (error) {
      clearTimeout(timer);
      throw controller && controller.signal.aborted ? new Error("loading " + name + " timed out") : error;
    });
  }
  var routed = embedded && typeof book.autoformFetchJSON === "function" ? book.autoformFetchJSON : null;
  function fetchJSON(relative) {
    if (!cache.has(relative)) {
      var url = new URL(relative, mapBase);
      // The router's messages name no file, so the map adds it.
      cache.set(relative, (routed ? routed(url.href).catch(function (error) { throw new Error((error && error.message || error) + " for " + relative); })
        : request(url, relative, function (response) { return response.json(); }))
        .catch(function (error) { cache.delete(relative); throw error; }));
    }
    return cache.get(relative);
  }

  var model = {index: null, parts: new Map(), results: new Map(), search: null, searchLoading: null};
  function part(id) { return model.parts.get(id); }
  function register(summary, parentId) {
    var known = model.parts.get(summary.id);
    if (known) { known.summary = summary; return known; }
    var record = {id: summary.id, summary: summary, parent: parentId, data: null, loading: null, box: null, ownBox: null, view: null, kids: [], results: []};
    model.parts.set(summary.id, record);
    var parent = model.parts.get(parentId);
    if (parent && parent.kids.indexOf(summary.id) < 0) parent.kids.push(summary.id);
    return record;
  }
  function chainOf(id) {
    var out = [];
    for (var at = part(id); at && at.id !== ROOT; at = part(at.parent)) out.unshift(at.id);
    return out;
  }
  function load(id) {
    var record = part(id);
    if (!record || record.id === ROOT) return Promise.resolve(record);
    if (record.data) return Promise.resolve(record);
    if (!record.loading) {
      // Parts share files: each holds the parts whose ids hash to it.
      record.retryAt = 0;
      record.loading = fetchJSON("parts/" + record.summary.file).then(function (shard) {
        var data = shard.parts && shard.parts[record.id];
        if (!data) throw new Error("Part " + record.id + " is missing from parts/" + record.summary.file);
        record.data = data;
        (data.children || []).forEach(function (child) { register(child, record.id); });
        (data.results || []).forEach(function (row) {
          model.results.set(row.id, {row: row, home: record.id, box: null});
          if (record.results.indexOf(row.id) < 0) record.results.push(row.id);
        });
        packChildren(record);
        if (record.parent === ROOT) outlineSoon();
        schedule();
        return record;
      }, function (error) {
        record.loading = null; record.retryAt = performance.now() + RETRY_MS;
        throw error;
      });
    }
    return record.loading;
  }

  // ---------------------------------------------------------------- layout (from the layout module)
  var stageSize = null;      // the stage the world was packed for
  function packRoot() {
    var root = part(ROOT), top = L.packLevels(model.index, stageSize);
    // For the browser tests: the shape the world was last packed for.
    host.dataset.pmPacked = stageSize.w >= stageSize.h ? "landscape" : "portrait";
    root.box = top.root;
    root.kids.forEach(function (id) { part(id).box = top.boxes[id] || null; });
    root.kids.forEach(function (id) { packChildren(part(id)); });
  }
  // A part's children and its own results, once both its box and its file are known.
  function packChildren(record) {
    if (!record || !record.box || !record.data) return;
    var boxes = L.packPart(record.data, record.box, stageSize);
    record.kids.forEach(function (id) { part(id).box = boxes[id] || null; });
    record.ownBox = boxes[record.id + "#results"] || null;
    var widths = record.kids.map(function (id) { return part(id).box ? part(id).box.w : 0; }).sort(function (a, b) { return a - b; });
    record.kidW = widths.length ? widths[widths.length >> 1] : null;
    var results = record.data.results || [];
    record.view = record.ownBox && results.length ?
      L.layoutCommunity(results, record.data.result_edges || [], record.data.boundary_edges || [], record.ownBox) : null;
    record.results.forEach(function (id) { var entry = model.results.get(id); if (entry) entry.box = record.view ? record.view.cards[id] || null : null; });
    record.kids.forEach(function (id) { if (part(id).data) packChildren(part(id)); });
  }

  // ---------------------------------------------------------------- page shell
  host.textContent = "";
  var app = el("div", "pm-app");
  var top = el("header", "pm-top");
  var home = el("a", "pm-home", "Home"); home.href = host.getAttribute("data-home") || "../";
  var trail = el("ol", "pm-trail"); trail.setAttribute("aria-label", "Where you are on the map");
  var searchBox = el("div", "pm-search");
  var search = el("input"); search.type = "search"; search.placeholder = "Search theorems by name or Lean name"; search.setAttribute("aria-label", "Search theorems by name or Lean name");
  search.setAttribute("autocomplete", "off");
  var hits = el("ul", "pm-hits"); hits.hidden = true; hits.id = "pm-hits"; hits.setAttribute("role", "listbox");
  search.setAttribute("aria-controls", "pm-hits");
  searchBox.append(search, hits);
  var tools = el("div", "pm-tools");
  var zoomOut = el("button", "", "−"), zoomIn = el("button", "", "+"), upLevel = el("button", "", "↑ Up"), fitAll = el("button", "", "Whole project");
  zoomOut.setAttribute("aria-label", "Zoom out"); zoomIn.setAttribute("aria-label", "Zoom in");
  upLevel.setAttribute("aria-label", "Up one level"); upLevel.title = "Up one level (Escape)";
  tools.append(zoomOut, zoomIn, upLevel, fitAll);
  top.append(home, trail, searchBox, tools);

  var side = el("aside", "pm-side"); side.setAttribute("aria-label", "Project outline");
  var sideInner = el("div", "pm-side-inner"); side.append(sideInner);
  var stage = el("main", "pm-stage");
  var canvas = svg("svg", {role: "application", "aria-label": "Map of the whole project. Drag, scroll or use the arrow keys to move; Control or Command with scroll, or plus and minus, to zoom."});
  canvas.setAttribute("tabindex", "0");
  var defs = svg("defs");
  // Markers do not inherit the colour of the line that uses them, so a highlighted route has its own.
  defs.innerHTML = ["pm-arrow", "pm-arrow-on"].map(function (id) {
    return '<marker id="' + id + '" class="' + id + '" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="8" markerHeight="8" markerUnits="userSpaceOnUse" orient="auto-start-reverse"><path d="M0,1 L10,5 L0,9 z"/></marker>';
  }).join("");
  // Labels draw last. A picked part's arrows to its neighbours cross other boxes, so they draw above everything but
  // the labels. A title over its box sits on a backdrop; backdrops have a layer of their own below every label, since
  // keep() appends a node only when it first creates it.
  var partLayer = svg("g"), miniLayer = svg("g"), resultLayer = svg("g"), cardRouteLayer = svg("g"), linkLayer = svg("g"),
    backdropLayer = svg("g"), labelLayer = svg("g");
  canvas.append(defs, partLayer, miniLayer, resultLayer, cardRouteLayer, linkLayer, backdropLayer, labelLayer);
  // Titles with formulas, which SVG text cannot typeset. The layer is inert: each part's and card's own label already
  // names them, and MathJax would make every formula a tab stop.
  var mathLayer = el("div", "pm-tex-layer"); mathLayer.inert = true;
  var pin = el("div", "pm-pin"); pin.hidden = true;
  var hint = el("div", "pm-hint", "");
  stage.append(canvas, mathLayer, pin, hint);
  var reader = el("aside", "pm-reader"); reader.setAttribute("aria-label", "Reading pane");
  var readerInner = el("div", "pm-reader-inner"); reader.append(readerInner);
  // Embedded, the book announces where the reader is.
  var live = el("p", "pm-sr"); if (!embedded) live.setAttribute("aria-live", "polite");
  app.append(top, side, stage, reader, live);
  if (embedded) {
    app.classList.add("pm-embedded");
    // The book's own drawing under the map listens on its stage: the map's pointer, wheel and keys stop at the map.
    ["pointerdown", "pointermove", "pointerup", "pointercancel", "wheel"].forEach(function (type) {
      host.addEventListener(type, function (event) { event.stopPropagation(); });
    });
    host.addEventListener("keydown", function (event) {
      if (!/^(Escape|Arrow|[-+=0]$)/.test(event.key)) return;
      event.stopPropagation();
      if (event.key === "Escape" && !event.defaultPrevented) { event.preventDefault(); escape(); }
    });
  }
  host.append(app);

  // ---------------------------------------------------------------- camera
  // The camera is the world point at the centre of the stage and the zoom k (screen px per world unit).
  var camera = {x: 0, y: 0, k: 1};
  var size = {w: 1, h: 1}, centre = null;
  // While the book's panes are dragged, what the map shows stays where it is on the page: whichever edge moves, and
  // whatever measures the stage first, the camera follows the stage's centre, up to the size the drag settles at.
  function measure() {
    var box = canvas.getBoundingClientRect();
    size.w = Math.max(1, box.width); size.h = Math.max(1, box.height);
    if (box.width <= 1 || box.height <= 1) return;
    var now = {x: box.left + box.width / 2, y: box.top + box.height / 2};
    if (centre && embedded && (settling || book.classList.contains("bp-dag-resizing"))) {
      camera = {x: camera.x + (now.x - centre.x) / camera.k, y: camera.y + (now.y - centre.y) / camera.k, k: camera.k};
    }
    centre = now;
  }
  function fitK(box, share) { return Math.min(size.w / box.w, size.h / box.h) * (share || 0.96); }
  function centerOf(box) { return [box.x + box.w / 2, box.y + box.h / 2]; }
  function toScreen(x, y) { return [(x - camera.x) * camera.k + size.w / 2, (y - camera.y) * camera.k + size.h / 2]; }
  function toWorld(sx, sy) { return [(sx - size.w / 2) / camera.k + camera.x, (sy - size.h / 2) / camera.k + camera.y]; }
  function screenBox(box) {
    var a = toScreen(box.x, box.y);
    return {x: a[0], y: a[1], w: box.w * camera.k, h: box.h * camera.k};
  }
  // The layout module's camera: the world point at the stage's top-left corner and the zoom.
  function cornerCamera() { return {x: camera.x - size.w / 2 / camera.k, y: camera.y - size.h / 2 / camera.k, z: camera.k}; }
  function limits() {
    var box = part(ROOT).box;
    return {low: Math.min(size.w / box.w, size.h / box.h) * 0.5, high: 60000};
  }
  var flight = null;
  function flyTo(target, done) {
    var range = limits();
    target = {x: target.x, y: target.y, k: clamp(target.k, range.low, range.high)};
    if (flight) cancelAnimationFrame(flight.frame);
    // The current entry takes the flight's end at once, so Back and Forward straight after a jump keep each place.
    clearTimeout(cameraTimer);
    try { if (history.state && history.state.pm) history.replaceState(Object.assign({}, history.state, {camera: target}), ""); } catch (_e) { /* ignore */ }
    // Drawn at once, so `done` sees the parts at the target, as at a flight's last frame. Nothing flies to where a drag of
    // the book's panes sent the map either (land, below).
    var sent = landing || navEpoch === landingEpoch;
    if (sent) landingEpoch = -1;
    if (reduceMotion || sent) { camera = target; render(); rememberCamera(); if (done) done(); return; }
    var start = {x: camera.x, y: camera.y, k: camera.k}, began = performance.now(), duration = 560;
    flight = {frame: 0, target: target};
    var step = function (now) {
      var t = Math.min(1, (now - began) / duration), e = t < 0.5 ? 2 * t * t : 1 - Math.pow(-2 * t + 2, 2) / 2;
      // Interpolate the scale geometrically, so a deep zoom does not rush its last screens.
      camera = {x: start.x + (target.x - start.x) * e, y: start.y + (target.y - start.y) * e,
        k: Math.exp(Math.log(start.k) + (Math.log(target.k) - Math.log(start.k)) * e)};
      render();
      if (t < 1) flight.frame = requestAnimationFrame(step); else { flight = null; rememberCamera(); if (done) done(); }
    };
    flight.frame = requestAnimationFrame(step);
  }
  // Opening a part fits its content, not its whole box, or comes closer when most of its children would be too small
  // to label (the layout module decides); the layout module's camera holds the stage's top-left corner.
  function flyToContent(record, done) {
    var children = {};
    record.kids.forEach(function (id) { var child = part(id); if (child && child.box) children[id] = child.box; });
    var corner = L.focusCamera(record.box, children, size);
    flyTo({x: corner.x + size.w / 2 / corner.z, y: corner.y + size.h / 2 / corner.z, k: corner.z}, done);
  }
  function zoomAt(factor, sx, sy) {
    var range = limits(), k = clamp(camera.k * factor, range.low, range.high);
    var world = factor > 1 ? towardContent(toWorld(sx, sy)) : toWorld(sx, sy);
    camera = {x: world[0] - (sx - size.w / 2) / k, y: world[1] - (sy - size.h / 2) / k, k: k};
    schedule();
  }
  // Zooming in over a gap or a title heads for what is inside, so a drill lands on content, not between parts: the
  // point that stays under the pointer moves just inside the nearest child or card of the deepest part around it.
  function towardContent(at) {
    var record = part(ROOT);
    if (!record.box || !inBox(record.box, at)) return at;
    for (;;) {
      var targets = [];
      record.kids.forEach(function (id) { if (part(id).box) targets.push({box: part(id).box, part: part(id)}); });
      record.results.forEach(function (id) { var entry = model.results.get(id); if (entry && entry.box) targets.push({box: entry.box}); });
      if (!targets.length) return at;
      var hit = targets.find(function (target) { return inBox(target.box, at); });
      if (hit && !hit.part) return at;
      if (hit) { record = hit.part; continue; }
      var near = targets.reduce(function (best, target) { return distance(target.box, at) < distance(best.box, at) ? target : best; });
      var b = near.box, ix = Math.min(12 / camera.k, b.w / 2), iy = Math.min(12 / camera.k, b.h / 2);
      return [clamp(at[0], b.x + ix, b.x + b.w - ix), clamp(at[1], b.y + iy, b.y + b.h - iy)];
    }
  }
  function inBox(b, at) { return at[0] >= b.x && at[0] <= b.x + b.w && at[1] >= b.y && at[1] <= b.y + b.h; }
  function distance(b, at) { return Math.hypot(Math.max(b.x - at[0], 0, at[0] - b.x - b.w), Math.max(b.y - at[1], 0, at[1] - b.y - b.h)); }
  function fitProject(instant) {
    var box = part(ROOT).box, k = Math.min(size.w / box.w, size.h / box.h), target = {x: box.x + box.w / 2, y: box.y + box.h / 2, k: k};
    // A world packed taller than its stage (many regions on a narrow screen) opens at full width, top-aligned, and pans
    // down. One packed for a stage of another shape, as after a pane drag, fits whole.
    if (box.h > stageSize.h && box.h / box.w > size.h / size.w * 1.05) { k = size.w / box.w; target = {x: box.x + box.w / 2, y: box.y + size.h / 2 / k, k: k}; }
    // An instant fit replaces a flight under way, whose end was worked out for the stage as it was.
    if (instant) { if (flight) { cancelAnimationFrame(flight.frame); flight = null; } camera = target; schedule(); }
    else flyTo(target);
  }

  // ---------------------------------------------------------------- state
  // focusPart pins the reading pane and trail to a part the reader asked for (ROOT for the whole project) until they
  // move the map themselves; then both follow the part that fills the view.
  // picked: a part chosen with one click, shown where it is with its neighbours (a second click goes inside).
  // links: the shown part's neighbours by role (uses, used-by, both); linkHover: the neighbour under the pointer in the panel.
  var state = {selected: null, related: null, focusPart: null, facets: null, picked: null, links: null, linkHover: null, error: null};
  var pending = false;
  function schedule() {
    if (pending) return;
    pending = true;
    requestAnimationFrame(function () { pending = false; render(); });
  }
  function release() { if (state.focusPart && !state.selected) state.focusPart = null; }

  // ---------------------------------------------------------------- render
  var keyed = new Map(), used = new Set();
  // Each key always gets the same attributes, so a node reused across frames never keeps a stale one.
  function keep(layer, key, tag, attrs) {
    var node = keyed.get(key);
    if (!node) { node = svg(tag); node.dataset.key = key; keyed.set(key, node); }
    if (node.parentNode !== layer) layer.appendChild(node);
    for (var name in attrs) if (node.getAttribute(name) !== String(attrs[name])) node.setAttribute(name, attrs[name]);
    used.add(key);
    return node;
  }
  function setText(node, text) { if (node.textContent !== text) node.textContent = text; return node; }
  // A title with a formula is HTML over the canvas, set by the site's MathJax; other titles stay SVG text. Its node
  // outlives the frames it is off screen, so a typeset title comes back without typesetting again.
  var mathNodes = new Map(), mathUsed = new Set(), mathPending = false;
  function hasMath(text) {
    if (!window.AutoformMath) return false;
    // A formula as withMath reads one: a lone dollar sign keeps the title SVG text.
    MARKUP.lastIndex = 0;
    for (var match; (match = MARKUP.exec(text));) if (match[4] !== undefined || match[5] !== undefined) return true;
    return false;
  }
  // New formulas wait hidden while MathJax sets them, until every pass started on the node has settled; one MathJax
  // could not set then shows as typed, as in the book.
  function typesetHidden(node) {
    node.texPasses = (node.texPasses || 0) + 1;
    node.classList.add("pm-tex-waiting");
    var settled = function () { if (!--node.texPasses) node.classList.remove("pm-tex-waiting"); };
    typeset(node).then(settled, settled);
  }
  function mathTitle(key, text, cls, x, baseline, width, size, step, lines) {
    var node = mathNodes.get(key);
    if (!node) { node = withMath(el("div"), text); mathNodes.set(key, node); }
    // The first line's baseline lands where the SVG text's would: half a line down, plus about a third of the font size.
    var style = "left:" + Math.round(x) + "px;top:" + Math.round(baseline - step / 2 - size * 0.35) + "px;width:" + Math.max(0, Math.round(width)) +
      "px;font-size:" + size + "px;line-height:" + step + "px;-webkit-line-clamp:" + lines;
    if (node.className !== "pm-tex " + cls) node.className = "pm-tex " + cls;
    if (node.getAttribute("style") !== style) node.setAttribute("style", style);
    if (node.parentNode !== mathLayer) { mathLayer.appendChild(node); if (!node.querySelector("mjx-container")) mathPending = true; }
    mathUsed.add(key);
  }
  // Deep zooms put ancestors' edges tens of millions of pixels away, where the compositor's float32 loses whole pixels;
  // geometry is cut to a margin around the stage first. Clamping each coordinate keeps an orthogonal route's visible
  // part exactly and folds the rest onto the margin, out of sight.
  var MARGIN = 2000;
  function cx(x) { return clamp(x, -MARGIN, size.w + MARGIN); }
  function cy(y) { return clamp(y, -MARGIN, size.h + MARGIN); }
  function placeRect(rect, b) {
    var x = cx(b.x), y = cy(b.y);
    rect.setAttribute("x", x); rect.setAttribute("y", y);
    rect.setAttribute("width", Math.max(1, cx(b.x + b.w) - x)); rect.setAttribute("height", Math.max(1, cy(b.y + b.h) - y));
  }
  function onScreen(b) { return b.x + b.w > -40 && b.x < size.w + 40 && b.y + b.h > -40 && b.y < size.h + 40; }
  // A part with parts inside stays one named tile until most of them could carry a name of their own, so the map
  // reveals the next level at the scale where it can be read, not wherever a parent happens to be large.
  function isOpen(record, b) {
    return record.id === ROOT || (!!record.data && b.w >= OPEN_W && b.h >= OPEN_H && (!record.kidW || record.kidW * camera.k >= KID_LABEL_W));
  }
  // The part the view is in: the deepest open part under the centre that fills most of the stage.
  function covers(b) {
    return b.x <= size.w / 2 && b.x + b.w >= size.w / 2 && b.y <= size.h / 2 && b.y + b.h >= size.h / 2 &&
      Math.min(b.w, size.w) * Math.min(b.h, size.h) >= size.w * size.h * 0.45;
  }
  var deepestAtCenter = null;
  // The part the view is in: the pinned title and the empty-stage hint follow it. The panel and trail follow a picked part.
  function viewPart() { return state.focusPart ? part(state.focusPart) || part(ROOT) : deepestAtCenter; }
  function currentPart() { return state.picked && part(state.picked) ? part(state.picked) : viewPart(); }
  function render() {
    // A world packed for no stage, as when the book hid the map from the start, is not drawn.
    if (!part(ROOT) || !part(ROOT).box || stageSize.w <= 1) return;
    measure();
    used = new Set(); mathUsed = new Set();
    deepestAtCenter = part(ROOT);
    var onPath = state.selected && model.results.get(state.selected) ? new Set(chainOf(model.results.get(state.selected).home)) : null;
    var labelBoxes = {}, closed = {}, communities = [], drawn = new Set();
    (function visit(record) {
      if (!record.box) return;
      var b = screenBox(record.box);
      if (record.id !== ROOT && !onScreen(b)) return;
      if (record.id !== ROOT && !record.data && b.w >= OPEN_W && b.h >= OPEN_H && !(record.retryAt > performance.now())) load(record.id).catch(report);
      var open = isOpen(record, b);
      if (record.id !== ROOT) {
        if (open && covers(b)) deepestAtCenter = record;
        drawPart(record, b, open, onPath);
        drawn.add(record.id);
        if (b.w >= LABEL_MIN_W) labelBoxes[record.id] = record.box;
        if (!open) closed[record.id] = true;
      }
      if (!open) return;
      record.kids.forEach(function (id) { visit(part(id)); });
      if (record.view) communities.push(record);
      // Beside other children, a part's own results have a band of their own to name them.
      if (record.ownBox && record.ownBox.band && record.kids.length && screenBox(record.ownBox).w >= LABEL_MIN_W) labelBoxes[record.id + "#results"] = record.ownBox;
    })(part(ROOT));
    // Titles keep below the pinned title, in the room the layout module leaves for it.
    var pinnedPart = pinned(), slots = L.placeLabels(labelBoxes, cornerCamera(),
      pinnedPart ? {w: size.w, h: size.h, top: L.constants.TITLE_ROOM, pinned: pinnedPart.id} : size, closed);
    communities.forEach(function (record) { if (drawCommunity(record)) drawn.add(record.id + "#results"); });
    drawLinks();
    drawLabels(slots);
    drawPin(pinnedPart);
    explainEmpty(drawn);
    keyed.forEach(function (node, key) { if (!used.has(key)) { node.remove(); keyed.delete(key); } });
    mathNodes.forEach(function (node, key) { if (!mathUsed.has(key)) node.remove(); });
    if (mathPending) { mathPending = false; typesetHidden(mathLayer); }
    updateTrail();
    if (!state.selected) showPart(currentPart());
  }
  function drawPart(record, b, open, onPath) {
    // A part as wide as the stage fills the view across: an outline on it would read as a rule across the stage.
    var dim = state.related && !state.related.parts.has(record.id), wide = b.x <= 0 && b.x + b.w >= size.w;
    var holder = keep(partLayer, "part:" + record.id, "g", {
      class: "pm-part " + (open ? "pm-open" : "pm-tile pm-tile-" + tileKind(record.summary.status)) + (dim ? " pm-dimmed" : "") +
        (state.focusPart === record.id ? " pm-focus" : "") + (onPath && onPath.has(record.id) ? " pm-on-path" : "") +
        (!state.selected && state.links && state.links.has(record.id) ? " pm-" + state.links.get(record.id) : "") +
        (state.linkHover === record.id ? " pm-link-hover" : "") + (state.picked === record.id ? " pm-picked" : "") +
        (wide ? " pm-stage-wide" : ""),
      tabindex: open ? -1 : 0, role: "button", "data-part": record.id,
      "aria-label": plain(record.summary.title) + ", " + num(record.summary.results) + " results" +
        (record.summary.api_total ? ", " + num(record.summary.api_total) + " used elsewhere" : "")});
    var shape = holder.firstChild || holder.appendChild(svg("rect"));
    placeRect(shape, b);
    shape.setAttribute("rx", clamp(Math.min(b.w, b.h) * 0.05, 1.5, 10));
    if (!holder.querySelector("title")) holder.appendChild(svg("title")).textContent = plain(record.summary.title);
    // Closed, a part shows its parts faintly, sized by their results and tinted by their status, where they will sit
    // once it opens; the names come then.
    if (!open && b.w >= 120 && b.h >= 80) record.kids.forEach(function (id) {
      var kid = part(id);
      if (!kid.box) return;
      var mini = keep(miniLayer, "mini:" + id, "rect", {class: "pm-mini pm-mini-" + tileKind(kid.summary.status), rx: 2});
      placeRect(mini, screenBox(kid.box));
    });
  }
  // An orthogonal route as a screen path, its corners rounded to radius.
  function routePath(points, radius) {
    var pts = [];
    for (var i = 0; i < points.length; i += 2) { var at = toScreen(points[i], points[i + 1]); pts.push([cx(at[0]), cy(at[1])]); }
    // Corners stay tight when the camera is far closer than the route's own level.
    var r = Math.min(radius * camera.k, 14), d = "M" + pts[0][0].toFixed(1) + "," + pts[0][1].toFixed(1);
    for (i = 1; i < pts.length - 1; i++) {
      var p0 = pts[i - 1], p1 = pts[i], p2 = pts[i + 1];
      var l1 = Math.hypot(p1[0] - p0[0], p1[1] - p0[1]), l2 = Math.hypot(p2[0] - p1[0], p2[1] - p1[1]);
      // A leg that clamping folded to nothing keeps its corner, so the path never cuts a diagonal.
      if (!l1 || !l2) { d += "L" + p1[0].toFixed(1) + "," + p1[1].toFixed(1); continue; }
      var rr = Math.min(r, l1 / 2, l2 / 2);
      d += "L" + (p1[0] - (p1[0] - p0[0]) / l1 * rr).toFixed(1) + "," + (p1[1] - (p1[1] - p0[1]) / l1 * rr).toFixed(1) +
        "Q" + p1[0].toFixed(1) + "," + p1[1].toFixed(1) + " " +
        (p1[0] + (p2[0] - p1[0]) / l2 * rr).toFixed(1) + "," + (p1[1] + (p2[1] - p1[1]) / l2 * rr).toFixed(1);
    }
    var last = pts[pts.length - 1];
    return d + "L" + last[0].toFixed(1) + "," + last[1].toFixed(1);
  }
  function routeVisible(points) {
    var x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
    for (var i = 0; i < points.length; i += 2) { x0 = Math.min(x0, points[i]); x1 = Math.max(x1, points[i]); y0 = Math.min(y0, points[i + 1]); y1 = Math.max(y1, points[i + 1]); }
    var a = toScreen(x0, y0), b = toScreen(x1, y1);
    return onScreen({x: a[0], y: a[1], w: b[0] - a[0], h: b[1] - a[1]});
  }
  function arrow(on) { return on ? "url(#pm-arrow-on)" : "url(#pm-arrow)"; }
  function linkWords(route, titleOf) {
    var main = route.weights[0] + route.weights[1], back = route.weights[2] + route.weights[3];
    return titleOf(route.to) + " uses " + titleOf(route.from) + ": " + num(main) + (main === 1 ? " link" : " links") +
      (route.both ? "; " + titleOf(route.from) + " uses " + titleOf(route.to) + ": " + num(back) + (back === 1 ? " link" : " links") : "");
  }
  // The picked part's arrows, the only links the map draws between parts, so the overview stays quiet until a reader
  // asks: straight to each neighbour the map has a box for, in from what it builds on, out to what uses it, thicker for
  // more results. Dots flow along each from what is used to what uses it. A pair linked both ways gets two arrows,
  // bowed apart.
  function drawLinks() {
    var record = !state.selected && state.picked ? part(state.picked) : null, links = record && record.data && record.data.links;
    if (!links || !record.box) return;
    var here = screenBox(record.box), rows = links.uses.concat(links.used_by);
    var most = Math.max.apply(null, rows.map(function (row) { return row[3]; }).concat([1]));
    [["uses", links.uses], ["used-by", links.used_by]].forEach(function (pair) {
      pair[1].forEach(function (row) {
        var other = part(row[0]);
        if (!other || !other.box) return;
        var there = screenBox(other.box), ends = pair[0] === "uses" ? [there, here] : [here, there];
        var away = there.x > size.w || there.y > size.h || there.x + there.w < 0 || there.y + there.h < 0;
        var d = bow(ends[0], ends[1]), width = (1.5 + 3 * Math.sqrt(row[3] / most)).toFixed(2);
        var path = keep(linkLayer, "link:" + pair[0] + ":" + row[0], "path", {
          d: d, class: "pm-link" + (state.linkHover === row[0] ? " pm-link-hover" : "") + (away ? " pm-link-away" : ""),
          "stroke-width": width, "marker-end": arrow(true)});
        keep(linkLayer, "flow:" + pair[0] + ":" + row[0], "path", {d: d, class: "pm-link pm-flowing" + (away ? " pm-link-away" : ""), "stroke-width": width});
        var title = plain(record.summary.title), name = plain(row[1]), count = num(row[3]) + (row[3] === 1 ? " result" : " results");
        setText(path.firstChild || path.appendChild(svg("title")),
          pair[0] === "uses" ? title + " uses " + count + " in " + name : count + " in " + name + " use " + title);
      });
    });
  }
  // A gentle curve from one box's edge to the other's, bowed to its left, so a reverse arrow bows the other way. Boxes
  // side by side would leave only a stub in the gap between them, so then the arrow runs between their middles.
  function bow(a, b) {
    var p = edgeToward(a, [b.x + b.w / 2, b.y + b.h / 2]), q = edgeToward(b, [a.x + a.w / 2, a.y + a.h / 2]);
    if (Math.hypot(q[0] - p[0], q[1] - p[1]) < 60) {
      p = edgeToward(inset(a), [b.x + b.w / 2, b.y + b.h / 2]); q = edgeToward(inset(b), [a.x + a.w / 2, a.y + a.h / 2]);
    }
    var dx = q[0] - p[0], dy = q[1] - p[1], length = Math.hypot(dx, dy) || 1, bend = Math.min(90, length * 0.18);
    var m = [(p[0] + q[0]) / 2 + dy / length * bend, (p[1] + q[1]) / 2 - dx / length * bend];
    return "M" + cx(p[0]).toFixed(1) + "," + cy(p[1]).toFixed(1) + " Q" + cx(m[0]).toFixed(1) + "," + cy(m[1]).toFixed(1) +
      " " + cx(q[0]).toFixed(1) + "," + cy(q[1]).toFixed(1);
  }
  function inset(box) { return {x: box.x + box.w * 0.3, y: box.y + box.h * 0.3, w: box.w * 0.4, h: box.h * 0.4}; }
  function edgeToward(box, point) {
    var c = [box.x + box.w / 2, box.y + box.h / 2], dx = point[0] - c[0], dy = point[1] - c[1];
    var s = Math.min(dx ? box.w / 2 / Math.abs(dx) : Infinity, dy ? box.h / 2 / Math.abs(dy) : Infinity, 1);
    return [c[0] + dx * s, c[1] + dy * s];
  }
  // A part's own results: status tiles while small, then cards with their titles and the links between them.
  function drawCommunity(record) {
    var view = record.view, first = view.cards[record.results[0]], shown = 0;
    var text = !!first && first.w * camera.k >= CARD_TEXT_W;
    record.results.forEach(function (id) { if (drawCard(model.results.get(id), view, text)) shown++; });
    if (!text) return shown > 0;
    var selected = state.selected && model.results.get(state.selected) && model.results.get(state.selected).home === record.id ? state.selected : null;
    function titleOf(id) { var entry = model.results.get(id); return plain(entry ? entry.row.title : id); }
    view.routes.concat(selected ? view.implied.filter(function (route) { return route.from === selected || route.to === selected; }) : [])
      .forEach(function (route) {
        if (!route.points || !routeVisible(route.points)) return;
        var involved = selected && (route.from === selected || route.to === selected);
        var path = keep(cardRouteLayer, "croute:" + route.from + ">" + route.to, "path", {
          d: routePath(route.points, route.radius),
          class: "pm-route pm-card-route" + (route.kind === "proof" ? " pm-proof" : "") + (involved ? " pm-involved" : "") + (selected && !involved ? " pm-dimmed" : ""),
          "stroke-width": involved ? 2 : 1.25, "marker-end": arrow(involved), "marker-start": route.both ? arrow(involved) : "none"});
        setText(path.firstChild || path.appendChild(svg("title")), linkWords(route, titleOf));
        if (involved && !route.both) keep(cardRouteLayer, "cflow:" + route.from + ">" + route.to, "path", {d: path.getAttribute("d"), class: "pm-route pm-involved pm-flowing"});
      });
    return shown > 0;
  }
  function drawCard(entry, view, text) {
    if (!entry || !entry.box) return false;
    var b = screenBox(entry.box);
    if (!onScreen(b) || b.w < 1) return false;
    var row = entry.row, isSelected = row.id === state.selected;
    var dim = (state.related ? !state.related.results.has(row.id) : state.facets && row.facet && !state.facets.has(row.facet)) ||
      Boolean(statuses && tracked() && !statuses.has(row.status));
    var holder = keep(resultLayer, "result:" + row.id, "g", {
      class: "pm-result pm-" + group(row.status) + (text ? " pm-card" : "") + (isSelected ? " pm-selected" : "") +
        (row.id === reading && !isSelected ? " pm-reading" : "") + (dim ? " pm-dimmed" : ""),
      tabindex: 0, role: "button", "aria-label": [plain(row.title), standing(row)].filter(Boolean).join(", "), "data-result": row.id});
    var card = holder.firstChild || holder.appendChild(svg("rect"));
    placeRect(card, b);
    card.setAttribute("rx", clamp(b.w * 0.04, 1, 8));
    if (!holder.querySelector("title")) holder.appendChild(svg("title")).textContent = plain(row.title);
    if (!text) return true;
    var pad = 10, width = b.w - 2 * pad, cls = dim ? " pm-dimmed" : "";
    var lines = wrap(plain(row.title), Math.max(4, Math.floor(width / CARD_EM)), b.h >= 58 ? 2 : 1);
    if (hasMath(row.title)) mathTitle("ct:" + row.id, row.title, "pm-card-title" + cls, b.x + pad, b.y + pad + 13, width, 13, 17, b.h >= 58 ? 2 : 1);
    else lines.forEach(function (line, index) {
      setText(keep(labelLayer, "ct:" + row.id + ":" + index, "text", {x: b.x + pad, y: b.y + pad + 13 + index * 17, class: "pm-card-title" + cls}), line);
    });
    if (b.h >= 52) {
      // The card's fill says it is finished, the common case; the line names any other status, or where the project
      // tracks no Lean, the result's kind.
      var stub = view.stubs[row.id], meta = [group(row.status) === "done" ? "" : standing(row),
        stub && stub.usedBy ? "used " + num(stub.usedBy) + "× elsewhere" : ""].filter(Boolean).join(" · ");
      if (meta) setText(keep(labelLayer, "cm:" + row.id, "text", {x: b.x + pad, y: b.y + b.h - pad, class: "pm-card-meta" + cls}), clip(meta, Math.max(4, Math.floor(width / CARD_META_EM))));
    }
    return true;
  }
  // Titles and progress in each box's header band, where the layout module finds room for them. A closed tile's title
  // wraps down the tile, up to the lines the module allows. A title the module puts over a box's content (its band still
  // too thin, the box running above the stage, or the title moved below another) sits on a backdrop in the box's fill.
  function drawLabels(slots) {
    slots.forEach(function (slot) {
      var own = /#results$/.test(slot.id), record = part(own ? slot.id.slice(0, -"#results".length) : slot.id);
      if (!record) return;
      var cls = state.related && !state.related.parts.has(record.id) ? " pm-dimmed" : "";
      var count = own ? record.results.length : 0, short = num(count) + (count === 1 ? " result" : " results");
      // A part's own results say whose they are when the line has room, and just how many when it does not.
      var long = short + " directly in " + plain(record.summary.title);
      var title = own ? (!slot.compact && long.length * L.constants.TITLE_EM <= slot.w ? long : short) : plain(record.summary.title);
      if (slot.overlay) {
        var b = screenBox(own ? record.ownBox : record.box), backdrop = keep(backdropLayer, "lb:" + slot.id, "rect", {
          class: "pm-backdrop pm-backdrop-" + (own ? "open" : isOpen(record, b) ? "open" : tileKind(record.summary.status)) + cls, rx: 6});
        placeRect(backdrop, {x: b.x + 1, y: slot.y + 1, w: b.w - 2, h: slot.band});
      }
      var tex = !own && hasMath(record.summary.title);
      if (slot.compact) {
        if (tex) mathTitle("lc:" + slot.id, record.summary.title, "pm-title pm-compact" + cls, slot.x, slot.baseline, slot.w, 13, L.constants.COMPACT_LINE, slot.lines);
        else wrap(title, Math.max(3, Math.floor(slot.w / COMPACT_EM)), slot.lines).forEach(function (line, index) {
          setText(keep(labelLayer, "lc:" + slot.id + ":" + index, "text", {x: slot.x, y: slot.baseline + index * L.constants.COMPACT_LINE,
            class: "pm-title pm-compact" + cls}), line);
        });
        return;
      }
      // The title as large as its room allows, from 15 to 30 px: the band of an open part, the top half of a closed
      // tile, or the band a held title keeps. At 15 px it keeps the layout module's lines and baseline.
      var box = screenBox(own ? record.ownBox : record.box), shut = !own && !isOpen(record, box);
      var room = shut && !slot.overlay ? box.h / 2 : slot.band, meta = slot.detail !== "title" && !own;
      // A box running off the left of the stage keeps its title on screen, inside the box.
      var x = slot.x, width = slot.w;
      if (slot.x < 12 && slot.x + slot.w - 12 >= 80) { x = 12; width = slot.x + slot.w - 12; }
      function perLine(size) { return Math.max(4, Math.floor(width / (L.constants.TITLE_EM * size / 15))); }
      function stepOf(size) { return size === 15 ? L.constants.LINE : Math.round(size * 1.2); }
      // The last line's descenders stay inside the room, clear of the parts below an open band.
      function mostOf(size) { return size === 15 ? slot.lines : Math.max(1, Math.floor((room - (meta ? 22 : Math.ceil(size / 4))) / stepOf(size))); }
      function fits(size) {
        var n = perLine(size);
        return title.split(/[ \t\n]+/).every(function (word) { return word.length <= n; }) && wrap(title, n, 99).length <= mostOf(size);
      }
      // As large as the room allows, then smaller until the whole title fits; at 15 px a long one is clipped.
      var size = slot.overlay && !slot.held ? 15 : Math.round(clamp(Math.min(room * 0.4, width / 7), 15, 30));
      while (size > 15 && !fits(size)) size--;
      var step = stepOf(size), most = mostOf(size);
      var lines = most > 1 ? wrap(title, perLine(size), most) : [clip(title, perLine(size))];
      var y = size === 15 ? slot.baseline : slot.y + Math.round(size * 1.2);
      if (tex) mathTitle("lt:" + slot.id, record.summary.title, "pm-title" + (shut ? " pm-halo" : "") + cls, x, y, width, size, step, lines.length);
      else lines.forEach(function (line, index) {
        setText(keep(labelLayer, "lt:" + slot.id + ":" + index, "text", {x: x, y: y + index * step,
          class: "pm-title" + (shut ? " pm-halo" : "") + cls, style: size === 15 ? "" : "font-size:" + size + "px"}), line);
      });
      if (!meta) return;
      // How many results, and a bar for how far along they are.
      var metaY = y + (lines.length - 1) * step + 18, words = num(record.summary.results) + (record.summary.results === 1 ? " result" : " results");
      setText(keep(labelLayer, "lm:" + slot.id, "text", {x: x, y: metaY, class: "pm-meta" + (shut ? " pm-halo" : "") + cls}), clip(words, Math.floor(width / META_EM)));
      var barX = x + words.length * META_EM + 8, barW = Math.min(90, x + width - barX);
      if (barW >= 24 && tracked()) progressBar("lp:" + slot.id, barX, metaY - 6, barW, record.summary.status, cls);
    });
  }
  function progressBar(key, x, y, width, status, cls) {
    var counts = mix(status), total = counts.done + counts.progress + counts.planned || 1, at = x;
    ["done", "progress", "planned"].forEach(function (kind) {
      var w = width * counts[kind] / total;
      keep(labelLayer, key + ":" + kind, "rect", {x: at.toFixed(1), y: y.toFixed(1), width: Math.max(0, w).toFixed(1), height: 5, class: "pm-seg pm-seg-" + kind + cls});
      at += w;
    });
  }
  // Zoomed into a gap, the stage would be blank under the pinned title: say where the reader is and how to get out.
  var HINT = "Click a part to see its links, again to go inside; Escape goes back up. Pinch or Control-scroll to zoom.";
  function explainEmpty(drawn) {
    var record = viewPart(), text = state.error || HINT;
    if (!state.error && record && record.id !== ROOT && record.data && !state.selected) {
      var inside = record.kids.some(function (id) { return drawn.has(id); }) || drawn.has(record.id + "#results");
      if (!inside && (record.kids.length || record.results.length)) text = "You are between the parts of " + plain(record.summary.title) + ". Zoom out" + (embedded ? "." : ", or choose a part in the reading pane.");
    }
    if (hint.textContent !== text) hint.textContent = text;
    hint.classList.toggle("pm-hint-strong", text !== HINT);
    // In the book the general hint is for the whole project; inside a part or beside a result it would sit on the cards.
    hint.hidden = embedded && text === HINT && (Boolean(state.selected) || Boolean(record && record.id !== ROOT));
  }
  // Once the part the view is in has its header band scrolled off, its title stays pinned to the top of the stage.
  function pinned() {
    var record = viewPart();
    if (!record || record.id === ROOT || !record.box) return null;
    var b = screenBox(record.box), band = (record.box.band || L.constants.BAND) * (record.box.unit || 1) * camera.k;
    // The title line sits at the top of the band, however tall the band has grown: pin once that line is off the stage.
    return b.y + Math.min(30, band / 2 + 6) >= 12 || b.y + b.h < 60 ? null : record;
  }
  // A list entry's title: its formulas for the site's MathJax where that runs, else plain text. The list typesets them.
  function titled(node, text) {
    if (!hasMath(text)) { node.textContent = plain(text); return node; }
    return withMath(node, text);
  }
  function drawPin(record) {
    pin.hidden = !record;
    if (!record) return;
    if (pin.dataset.part !== record.id) {
      pin.dataset.part = record.id;
      pin.replaceChildren(titled(el("strong"), record.summary.title));
      if (tracked()) pin.append(el("span", "", progressText(record.summary)));
      if (hasMath(record.summary.title)) typesetHidden(pin);
    }
  }

  // ---------------------------------------------------------------- selection and relationships
  function relationsOf(id) {
    var entry = model.results.get(id), owner = entry && part(entry.home);
    var uses = [], usedBy = [], outside = new Map();
    if (!owner || !owner.data) return {uses: uses, usedBy: usedBy, outside: outside};
    (owner.data.outside || []).forEach(function (row) { outside.set(row[0], row); });
    (owner.data.result_edges || []).concat(owner.data.boundary_edges || []).forEach(function (edge) {
      if (edge[0] === id) uses.push({id: edge[1], weight: edge[2] + edge[3], statement: edge[2] > 0});
      else if (edge[1] === id) usedBy.push({id: edge[0], weight: edge[2] + edge[3], statement: edge[2] > 0});
    });
    return {uses: uses, usedBy: usedBy, outside: outside};
  }
  // A selection keeps its relatives and every part they live in at full strength; the rest of the map dims.
  function relatedSets(id) {
    var rel = relationsOf(id), results = new Set([id]), parts = new Set();
    function addChain(chain) { chain.forEach(function (p) { parts.add(p); }); }
    var entry = model.results.get(id);
    if (entry) addChain(chainOf(entry.home));
    rel.uses.concat(rel.usedBy).forEach(function (item) {
      results.add(item.id);
      var other = model.results.get(item.id), outside = rel.outside.get(item.id);
      if (other) addChain(chainOf(other.home)); else if (outside) addChain(outside[2]);
    });
    return {results: results, parts: parts};
  }
  function select(id, options) {
    options = options || {};
    var leaving = viewState();
    if (id) state.picked = null;
    state.selected = id;
    state.related = id ? relatedSets(id) : null;
    // Embedded, the book's reading pane opens the result's page; a result the book sent is not sent back.
    if (embedded) {
      if (id && id !== fromBook) { fromBook = id; host.dispatchEvent(new CustomEvent("autoform-map-select", {bubbles: true, detail: {id: id, history: "push", focus: "reading"}})); }
    }
    else if (id) showResult(id);
    if (!id) showPart(currentPart());
    if (options.history !== false) remember(options.replace, leaving);
    schedule();
  }

  // ---------------------------------------------------------------- arriving somewhere
  // Each navigation takes a number; one whose files arrive after a newer navigation began gives way to it.
  var navEpoch = 0;
  function navigation() { state.error = null; return ++navEpoch; }
  function ensureChain(chain) {
    return chain.reduce(function (promise, id, index) {
      return promise.then(function () {
        if (!part(id)) {
          var row = model.search && model.search.partById.get(id);
          if (!row) throw new Error("Unknown part " + id);
          register({id: id, title: row[1], results: 0, status: {}, parts: 0, api: [], api_total: 0, imports_total: 0, file: row[2]},
            index ? chain[index - 1] : ROOT);
        }
        return load(id);
      });
    }, Promise.resolve());
  }
  function partChainFromSearch(position) {
    var rows = model.search.data.parts, chain = [];
    for (var at = position; at >= 0; at = rows[at][3]) chain.unshift(rows[at][0]);
    return chain;
  }
  // Any part, loaded or not, with its chain loaded: search knows every part's chain.
  function ensurePart(id) {
    if (part(id)) return ensureChain(chainOf(id));
    return loadSearch().then(function () {
      var row = model.search.partById.get(id);
      if (!row) throw new Error("Unknown part " + id);
      return ensureChain(partChainFromSearch(model.search.data.parts.indexOf(row)));
    });
  }
  function goToPart(id, options) {
    var epoch = navigation();
    return ensurePart(id).then(function () { if (epoch === navEpoch) return flyToPart(id, Object.assign({}, options, {epoch: epoch})); });
  }
  // One click picks a part where it is: the reading pane and the map show what it builds on and what uses it. The
  // neighbours' parts load too, so the map can draw an arrow to each.
  function pick(id) {
    navigation();
    state.picked = id; shownPart = null;
    select(null, {history: false});
    return load(id).then(function () {
      shownPart = null; schedule();
      var links = part(id) && part(id).data && part(id).data.links;
      if (!links) return;
      return Promise.all(links.uses.concat(links.used_by).map(function (row) {
        return part(row[0]) && part(row[0]).box ? null : ensurePart(row[0]).then(schedule, function () { /* the pane still lists it */ });
      }));
    });
  }
  function unpick() { if (state.picked) { state.picked = null; shownPart = null; schedule(); } }
  // From a list: the part where it sits among its siblings, picked, with the view widened to take in its neighbours.
  function showInContext(id) {
    var epoch = navigation();
    return ensurePart(id).then(function () {
      if (epoch !== navEpoch) return;
      var record = part(id), parent = part(record.parent);
      state.focusPart = parent ? parent.id : ROOT;
      var leaving = viewState(), picking = pick(id);
      epoch = navEpoch;
      remember(false, leaving);
      return picking.then(function () { if (epoch === navEpoch) flyToNeighbourhood(record, parent); });
    });
  }
  // Never so far out that the picked part is narrower than this on screen (px): far neighbours' arrows run off the stage.
  var PICKED_MIN_W = 100;
  function flyToNeighbourhood(record, parent) {
    var area = parent && parent.id !== ROOT ? L.contentOf(parent.box) : part(ROOT).box, links = record.data && record.data.links;
    var x0 = area.x, y0 = area.y, x1 = area.x + area.w, y1 = area.y + area.h;
    (links ? links.uses.concat(links.used_by) : []).forEach(function (row) {
      var box = part(row[0]) && part(row[0]).box;
      if (!box) return;
      x0 = Math.min(x0, box.x); y0 = Math.min(y0, box.y); x1 = Math.max(x1, box.x + box.w); y1 = Math.max(y1, box.y + box.h);
    });
    var wide = {x: x0, y: y0, w: x1 - x0, h: y1 - y0}, k = Math.max(fitK(wide, 0.92), Math.min(fitK(area), PICKED_MIN_W / record.box.w));
    // Aim at the middle of the neighbourhood, moved only as far as keeps the picked part on the stage.
    var at = centerOf(wide), b = record.box, halfW = size.w / 2 / k, halfH = size.h / 2 / k, margin = 40 / k;
    flyTo({x: clamp(at[0], b.x + b.w + margin - halfW, b.x - margin + halfW), y: clamp(at[1], b.y + b.h + margin - halfH, b.y - margin + halfH), k: k});
  }
  // Back from a part opened this way returns to the reading pane as it was, though the pane changes before the part loads.
  function leaveFor(id) {
    var leaving = viewState();
    select(null, {history: false});
    return flyToPart(id, {leaving: leaving});
  }
  function flyToPart(id, options) {
    options = options || {};
    var epoch = options.epoch || navigation();
    if (state.picked) { state.picked = null; shownPart = null; }
    return ensureChain(chainOf(id)).then(function () {
      if (epoch !== navEpoch) return;
      var record = part(id);
      state.focusPart = id;
      if (options.history !== false) remember(options.replace, options.leaving);
      flyToContent(record);
      showPart(record);
    });
  }
  function arrive(resultId, chain, options) {
    options = options || {};
    var epoch = options.epoch || navigation();
    return ensureChain(chain).then(function () {
      if (epoch !== navEpoch) return;
      var homeId = chain[chain.length - 1], record = part(homeId), entry = model.results.get(resultId);
      if (!entry || !entry.box) throw new Error("Result not found in its part: " + resultId);
      state.focusPart = homeId;
      var leaving = viewState();
      select(resultId, {history: false});
      if (options.history !== false) remember(options.replace, leaving);
      // Close enough that the result's card carries its title, with as much of its part around it as fits. The card
      // sits in the upper third, under the pinned title, so its part's band scrolls off and more of its neighbours
      // show below it. A card the layout left without area gets its part's view instead of an endless zoom.
      if (entry.box.w > 0 && entry.box.h > 0) {
        var at = centerOf(entry.box), k = Math.max(fitK(L.contentOf(record.box)), (CARD_TEXT_W * 1.9) / entry.box.w);
        flyTo({x: at[0], y: at[1] + size.h * 0.2 / k, k: k});
      } else flyToContent(record);
      live.textContent = "Showing " + plain(entry.row.title);
    });
  }
  // A result the map has not loaded yet (from a list in the reading pane): find its path through search.
  function arriveById(resultId, options) {
    var entry = model.results.get(resultId), epoch = navigation();
    options = Object.assign({}, options, {epoch: epoch});
    if (entry) return arrive(resultId, chainOf(entry.home), options);
    return loadSearch().then(function () {
      if (epoch !== navEpoch) return;
      var hit = model.search.byId.get(resultId);
      if (!hit) throw new Error("Unknown result " + resultId);
      return arrive(resultId, partChainFromSearch(hit[2]), options);
    });
  }

  // ---------------------------------------------------------------- search
  function loadSearch() {
    if (model.search) return Promise.resolve(model.search);
    if (!model.searchLoading) {
      model.searchLoading = fetchJSON("search.json").then(function (data) {
        var partById = new Map(), byId = new Map();
        data.parts.forEach(function (row) { partById.set(row[0], row); });
        var rows = data.rows.map(function (row) {
          var id = typeof row[3] === "string" ? data.parts[row[2]][0] + "/" + row[3] : row[3][0];
          var entry = [row[0], row[1], row[2], id, String(row[0]).toLowerCase(), String(row[1]).toLowerCase()];
          byId.set(id, entry);
          return entry;
        });
        model.search = {data: data, rows: rows, partById: partById, byId: byId};
        return model.search;
      });
    }
    return model.searchLoading;
  }
  var activeHit = -1, hitRows = [];
  function runSearch() {
    var query = search.value.trim().toLowerCase();
    if (!query) { hits.hidden = true; return; }
    if (!model.search) {
      hits.hidden = false; hits.replaceChildren(el("li", "pm-note", "Loading every theorem's name…"));
      loadSearch().then(runSearch, function () { hits.replaceChildren(el("li", "pm-note", "Search is unavailable.")); });
      return;
    }
    var scored = [];
    for (var i = 0; i < model.search.rows.length && scored.length < 4000; i++) {
      var row = model.search.rows[i], title = row[4], lean = row[5], rank = 0;
      if (title === query || lean === query) rank = 1;
      else if (title.indexOf(query) === 0 || lean.indexOf(query) === 0 || lean.endsWith("." + query)) rank = 2;
      else if (title.indexOf(query) > 0) rank = 3;
      else if (lean.indexOf(query) > 0) rank = 4;
      if (rank) scored.push([rank, row]);
    }
    scored.sort(function (a, b) { return a[0] - b[0] || a[1][0].length - b[1][0].length; });
    hitRows = scored.slice(0, 20).map(function (pair) { return pair[1]; });
    activeHit = hitRows.length ? 0 : -1;
    hits.replaceChildren();
    if (!hitRows.length) hits.append(el("li", "pm-note", tracked() ? "No theorem or Lean name matches." : "No theorem matches."));
    hitRows.forEach(function (row, index) {
      var item = el("li"), button = el("button", "pm-hit");
      button.type = "button"; button.setAttribute("role", "option"); button.setAttribute("aria-selected", String(index === activeHit));
      button.append(titled(el("span", "pm-hit-title"), row[0]));
      var meta = el("span", "pm-hit-meta"), chain = partChainFromSearch(row[2]);
      meta.append(document.createTextNode(chain.map(function (id) { return plain(model.search.partById.get(id)[1]); }).join(" / ")));
      if (row[1]) { meta.append(document.createTextNode(" · ")); meta.append(el("code", "", row[1])); }
      button.append(meta);
      button.addEventListener("click", function () { choose(row); });
      item.append(button); hits.append(item);
    });
    typesetHidden(hits);
    hits.hidden = false;
  }
  function choose(row) {
    hits.hidden = true;
    arrive(row[3], partChainFromSearch(row[2])).catch(report);
  }
  search.addEventListener("focus", function () { loadSearch().catch(function () {}); });
  search.addEventListener("input", runSearch);
  search.addEventListener("keydown", function (event) {
    if (event.key === "ArrowDown" || event.key === "ArrowUp") {
      if (!hitRows.length) return;
      event.preventDefault();
      activeHit = (activeHit + (event.key === "ArrowDown" ? 1 : hitRows.length - 1)) % hitRows.length;
      hits.querySelectorAll(".pm-hit").forEach(function (button, index) { button.setAttribute("aria-selected", String(index === activeHit)); });
    } else if (event.key === "Enter" && activeHit >= 0) {
      event.preventDefault(); choose(hitRows[activeHit]);
    } else if (event.key === "Escape") { hits.hidden = true; }
  });
  document.addEventListener("pointerdown", function (event) { if (!searchBox.contains(event.target)) hits.hidden = true; });

  // ---------------------------------------------------------------- side panel and reading pane
  // A project that tracks no Lean has no progress to draw: the empty string appends nothing visible.
  function bar(status) {
    if (!tracked()) return "";
    var counts = mix(status), total = counts.done + counts.progress + counts.planned || 1, node = el("div", "pm-bar");
    ["done", "progress", "planned"].forEach(function (kind) {
      var span = el("span"); span.style.width = (100 * counts[kind] / total) + "%"; span.style.background = color(kind); node.append(span);
    });
    node.setAttribute("aria-label", num(counts.done) + " finished, " + num(counts.progress) + " in progress, " + num(counts.planned) + " planned");
    node.setAttribute("role", "img");
    return node;
  }
  function renderSide() {
    var index = model.index, active = document.activeElement, focused = active && sideInner.contains(active) ? active.dataset.part : null;
    var scroll = side.scrollTop;
    sideInner.replaceChildren();
    sideInner.append(el("h1", "pm-project", plain(index.title)));
    var stats = el("div", "pm-stats"), counts = mix(index.status);
    [[num(index.results), "results"], [num(index.regions.length), index.regions.length === 1 ? "section" : "sections"]].concat(tracked() ? [[num(counts.done), "finished"]] : []).forEach(function (pair) {
      var stat = el("div", "pm-stat"); stat.append(el("strong", "", pair[0]), el("span", "", pair[1])); stats.append(stat);
    });
    sideInner.append(stats, bar(index.status));
    if (tracked()) {
      var legend = el("div", "pm-legend");
      [["done", "finished"], ["progress", "in progress"], ["planned", "planned"]].forEach(function (pair) {
        var item = el("span"), swatch = el("i"); swatch.style.background = color(pair[0]); item.append(swatch, document.createTextNode(pair[1])); legend.append(item);
      });
      sideInner.append(legend);
    }
    // The links the map draws: a picked part's arrows to its neighbours, and the routes between a part's results.
    var key = el("div", "pm-edge-key");
    [["pm-key-link", 2.5, "a picked part, to what uses it"], ["pm-route", 1.25, "a result, to what uses it"], ["pm-route pm-proof", 1.25, "used only in proofs"]].forEach(function (row) {
      var item = el("span"), sample = svg("svg", {width: 30, height: 10, "aria-hidden": "true"});
      sample.appendChild(svg("path", {d: "M2,5H24", class: row[0], "stroke-width": row[1], "marker-end": arrow(row[0] === "pm-key-link")}));
      item.append(sample, document.createTextNode(row[2])); key.append(item);
    });
    sideInner.append(key);
    var outline = el("ul", "pm-outline");
    index.regions.forEach(function (summary) {
      var item = el("li"), button = el("button");
      button.type = "button"; button.dataset.part = summary.id;
      button.append(el("span", "", plain(summary.title)), el("span", "pm-count", num(summary.results)));
      button.addEventListener("click", function () { showInContext(summary.id).catch(report); });
      item.append(button);
      var record = part(summary.id);
      if (record && record.data && record.kids.length) {
        var sub = el("ul");
        record.kids.slice(0, 40).forEach(function (id) {
          var child = part(id), li = el("li"), b = el("button");
          b.type = "button"; b.dataset.part = id;
          b.append(el("span", "", plain(child.summary.title)), el("span", "pm-count", num(child.summary.results)));
          b.addEventListener("click", function () { showInContext(id).catch(report); });
          li.append(b); sub.append(li);
        });
        item.append(sub);
      }
      outline.append(item);
    });
    sideInner.append(outline);
    if (index.facets && index.facets.length) {
      var facets = el("fieldset", "pm-facets");
      facets.append(el("legend", "", "Show results from"));
      index.facets.forEach(function (name) {
        var label = el("label"), box = el("input"); box.type = "checkbox"; box.checked = !state.facets || state.facets.has(name);
        box.addEventListener("change", function () {
          var checked = new Set(Array.from(facets.querySelectorAll("input")).filter(function (b) { return b.checked; }).map(function (b) { return b.value; }));
          state.facets = checked.size === index.facets.length ? null : checked;
          schedule(); rememberCamera();
        });
        box.value = name; label.append(box, document.createTextNode(" " + name)); facets.append(label);
      });
      sideInner.append(facets);
    }
    side.scrollTop = scroll;
    var again = focused && Array.from(sideInner.querySelectorAll("button")).find(function (button) { return button.dataset.part === focused; });
    if (again) again.focus();
  }
  // The outline lists each region's parts once they arrive.
  var outlineTimer = 0;
  function outlineSoon() { clearTimeout(outlineTimer); outlineTimer = setTimeout(renderSide, 400); }
  var shownPart = null;
  function pathLine(chain) {
    var line = el("p", "pm-path");
    chain.forEach(function (id, index) {
      if (index) line.append(document.createTextNode(" / "));
      var button = el("button", "", plain(part(id) ? part(id).summary.title : id)); button.type = "button";
      button.addEventListener("click", function () { leaveFor(id).catch(report); });
      line.append(button);
    });
    return line;
  }
  function showPart(record) {
    if (!record || state.selected || shownPart === record.id) return;
    shownPart = record.id;
    reader.scrollTop = 0;
    var links = record.id !== ROOT && record.data && record.data.links;
    state.links = links ? new Map() : null;
    if (links) {
      links.uses.forEach(function (row) { state.links.set(row[0], "uses"); });
      links.used_by.forEach(function (row) { state.links.set(row[0], state.links.has(row[0]) ? "both" : "used-by"); });
    }
    schedule();
    readerInner.replaceChildren();
    if (record.id === ROOT) {
      var index = model.index;
      readerInner.append(el("p", "pm-kicker", "Whole project"), el("h2", "", plain(index.title)));
      readerInner.append(el("p", "", num(index.results) + " results in " + num(index.regions.length) + (index.regions.length === 1 ? " section." : " sections.")), bar(index.status));
      var flows = (index.region_edges || []).slice().sort(function (a, b) { return b[2] + b[3] - a[2] - a[3]; });
      if (flows.length) {
        readerInner.append(el("h3", "", "How the sections build on each other"));
        readerInner.append(paged(flows, 8, function (edge) {
          var li = el("li", "pm-flow"), user = part(edge[0]), used = part(edge[1]);
          li.append(el("span", "", plain(user ? user.summary.title : edge[0]) + " uses " + plain(used ? used.summary.title : edge[1])),
            el("small", "", num(edge[2] + edge[3]) + (edge[2] + edge[3] === 1 ? " link" : " links")));
          return li;
        }));
      }
      return;
    }
    var summary = record.summary;
    readerInner.append(el("p", "pm-kicker", "Part"), el("h2", "", plain(summary.title)));
    readerInner.append(pathLine(chainOf(record.id).slice(0, -1)));
    readerInner.append(el("p", "", num(summary.results) + " results" + (summary.parts ? " in " + num(summary.parts) + " parts" : "") + "."), bar(summary.status));
    if (links) {
      var most = Math.max.apply(null, links.uses.concat(links.used_by).map(function (row) { return row[3]; }).concat([1]));
      var home = part(record.parent) && record.parent !== ROOT ? part(record.parent).summary.title : null;
      readerInner.append(linkList("Builds on", "uses", links.uses, links.uses_total, most, home, function (row) {
        return "Uses " + num(row[3]) + (row[3] === 1 ? " result" : " results") + " in " + plain(row[1]);
      }));
      readerInner.append(linkList("Used by", "used-by", links.used_by, links.used_by_total, most, home, function (row) {
        return num(row[3]) + (row[3] === 1 ? " result" : " results") + " in " + plain(row[1]) + (row[3] === 1 ? " uses it" : " use it");
      }));
      if (links.uses.length || links.used_by.length) readerInner.append(el("p", "pm-empty pm-link-note", "On the map, the parts in view are outlined, and while this part is picked, arrows run to them with dots flowing from what is used to what uses it. Bars count the results involved."));
    }
    if (record.kids.length) { readerInner.append(el("h3", "", "Parts (" + num(record.kids.length) + ")")); readerInner.append(listOfParts(record.kids)); }
    if (summary.api && summary.api.length) {
      // Single results come last, folded: the parts above say more about how this one fits.
      var more = el("details", "pm-more"), list = el("ul", "pm-list");
      more.append(el("summary", "", "Most-used results (" + num(summary.api_total) + ")"));
      summary.api.forEach(function (row) {
        var item = el("li"), button = el("button"); button.type = "button";
        button.append(titled(el("span"), row[1]), el("small", "", "used " + num(row[2]) + (row[2] === 1 ? " time" : " times")));
        button.addEventListener("click", function () { arriveById(row[0]).catch(report); });
        item.append(button); list.append(item);
      });
      more.append(list);
      if (summary.api_total > summary.api.length) more.append(el("p", "pm-empty", "The " + num(summary.api.length) + " most used are listed."));
      readerInner.append(more);
      typesetHidden(list);
    }
  }
  // Neighbouring parts for the panel, biggest first, each with a bar for how many results the link involves.
  function linkList(heading, role, rows, total, most, home, describe) {
    var section = el("section", "pm-links pm-" + role), title = el("h3");
    title.append(document.createTextNode(heading + (total ? " · " + num(total) + (total === 1 ? " part" : " parts") : "")));
    section.append(title);
    if (!rows.length) { section.append(el("p", "pm-empty", role === "uses" ? "Nothing outside it." : "Nothing outside uses it.")); return section; }
    var list = el("ul", "pm-list pm-link-list");
    rows.forEach(function (row) {
      var item = el("li"), button = el("button"), name = el("span", "pm-link-name"), meter = el("span", "pm-meter"), fill = el("i");
      button.type = "button"; button.title = describe(row);
      name.append(el("span", "", plain(row[1])));
      // Where a neighbour sits, when that is not beside this part.
      if (row[2] && row[2] !== home) name.append(el("small", "", plain(row[2])));
      fill.style.width = Math.max(4, Math.round(100 * row[3] / most)) + "%"; meter.append(fill);
      button.append(name, meter, el("small", "", num(row[3])));
      button.addEventListener("click", function () { state.linkHover = null; showInContext(row[0]).catch(report); });
      button.addEventListener("mouseenter", function () { state.linkHover = row[0]; schedule(); });
      button.addEventListener("mouseleave", function () { state.linkHover = null; schedule(); });
      item.append(button); list.append(item);
    });
    section.append(list);
    if (total > rows.length) section.append(el("p", "pm-empty", "The " + num(rows.length) + " with the most links are listed."));
    return section;
  }
  function listOfParts(ids) {
    return paged(ids.filter(part), 60, function (id) {
      var record = part(id), item = el("li"), button = el("button"); button.type = "button";
      button.append(el("span", "", plain(record.summary.title)), el("small", "", num(record.summary.results)));
      button.addEventListener("click", function () { showInContext(id).catch(report); });
      item.append(button);
      return item;
    });
  }
  // A list that shows its first items and pages through the rest, so every entry stays reachable.
  function paged(items, step, render) {
    var box = el("div", "pm-paged"), list = el("ul", "pm-list"), more = el("button", "pm-show-more"), shown = 0;
    more.type = "button";
    function page() {
      items.slice(shown, shown + step).forEach(function (item) { list.append(render(item)); });
      shown = Math.min(items.length, shown + step);
      more.textContent = "Show more (" + num(items.length - shown) + " left)";
      more.hidden = shown >= items.length;
      typesetHidden(list);
    }
    more.addEventListener("click", page);
    page();
    box.append(list, more);
    return box;
  }
  // Formulas go to the site's MathJax runtime (javascripts/mathjax.js), which reads only the spans marked for it.
  function typeset(node) {
    return Promise.resolve(window.AutoformMath && typeof window.AutoformMath.refresh === "function" ? window.AutoformMath.refresh(node) : null);
  }
  // The explorer's reading of a summary: closed code spans and unambiguous inline formulas; anything else stays literal.
  var MARKUP = /\\([\\`$])|(?<![\\`])(`+)(?!`)([^\n]*?)(?<!`)\2(?!`)|(?<![\\$])\$(?![\s$])((?:\\.|[^\\$\n])+?)(?<!\s)\$(?![$\d])|(?<!\\)\\\(((?:\\[^)]|[^\\\n])+?)\\\)/g;
  function withMath(node, text) {
    text = String(text || "");
    var last = 0, match, parts = [];
    MARKUP.lastIndex = 0;
    while ((match = MARKUP.exec(text))) {
      // An unmatched backtick may own later dollars: keep the whole text literal instead of guessing where code ends.
      if (text.slice(last, match.index).indexOf("`") >= 0) { node.append(document.createTextNode(text)); return node; }
      if (match.index > last) parts.push(document.createTextNode(text.slice(last, match.index)));
      parts.push(match[1] !== undefined ? document.createTextNode(match[1]) : match[2] !== undefined ? el("code", "", match[3].trim()) :
        el("span", "arithmatex", "\\(" + (match[4] !== undefined ? match[4] : match[5]) + "\\)"));
      last = MARKUP.lastIndex;
    }
    if (text.slice(last).indexOf("`") >= 0) { node.append(document.createTextNode(text)); return node; }
    if (last < text.length) parts.push(document.createTextNode(text.slice(last)));
    parts.forEach(function (piece) { node.append(piece); });
    return node;
  }
  function statement(text, title) {
    text = String(text || "");
    // Summaries open with the title as their first sentence; the heading already says it.
    if (title && text.indexOf(title) === 0 && /^[.:]\s/.test(text.slice(title.length))) text = text.slice(title.length + 1).trim();
    return withMath(el("p", "pm-statement"), text);
  }
  // A link from published data: http(s) only, no credentials; anything else is dropped.
  function safeLink(value, base) {
    if (typeof value !== "string" || !value || /[\u0000-\u001f\u007f]/.test(value)) return null;
    try { var url = new URL(value, base); return /^https?:$/.test(url.protocol) && !url.username && !url.password ? url.href : null; }
    catch (_error) { return null; }
  }
  // The book's page for a result holds its complete statement, proof and sources; the reading pane shows that block
  // instead of the index's summary. The last PAGES pages stay parsed.
  var pages = new Map(), PAGES = 6, shownResult = 0;
  function pageAt(url) {
    var key = url.split("#")[0];
    if (!pages.has(key)) {
      if (pages.size >= PAGES) pages.delete(pages.keys().next().value);
      pages.set(key, request(key, "the result's page", function (response) { return response.text(); })
        .then(function (text) { return new DOMParser().parseFromString(text, "text/html"); })
        .catch(function (error) { pages.delete(key); throw error; }));
    }
    return pages.get(key);
  }
  // The result's block, cleaned as the explorer cleans what it borrows: no scripts or embeds, no handlers or inline
  // styles, links rebased to the page and kept only when safe, and no ids to clash with this page's. Its heading and
  // dependency list go, since the pane has its own.
  function borrowed(page, id, base) {
    var block = Array.from(page.querySelectorAll(".bp-thmwrapper")).find(function (node) { return node.getAttribute("data-autoform-node-id") === id; });
    if (!block) return null;
    var copy = document.importNode(block, true), source = copy.querySelector(".bp-code-link");
    source = source && safeLink(source.getAttribute("href"), base);
    copy.querySelectorAll(".bp-thmheading, .bp-dependencies, script, iframe, object, embed, base, link, style, form").forEach(function (node) { node.remove(); });
    [copy].concat(Array.from(copy.querySelectorAll("*"))).forEach(function (node) {
      Array.from(node.attributes).forEach(function (attribute) {
        var name = attribute.name.toLowerCase();
        if (/^on/.test(name) || name === "srcdoc" || name === "style" || name === "id") node.removeAttribute(attribute.name);
      });
      ["href", "src"].forEach(function (name) {
        var value = node.getAttribute(name);
        if (value == null) return;
        var safe = safeLink(value, base);
        if (safe) node.setAttribute(name, safe); else node.removeAttribute(name);
      });
    });
    return {block: copy, source: source};
  }
  // Settles once the shown result's statement from its book page and its formulas are in the reading pane.
  var readerReady = Promise.resolve();
  function showResult(id) {
    var entry = model.results.get(id);
    if (!entry) return;
    shownPart = null;
    reader.scrollTop = 0;
    var row = entry.row, rel = relationsOf(id), shown = ++shownResult;
    readerInner.replaceChildren();
    readerInner.append(el("p", "pm-kicker", row.caption || "Result"));
    readerInner.append(withMath(el("h2"), row.title));
    readerInner.append(pathLine(chainOf(entry.home)));
    var chip = [tracked() ? statusWords(row.status) : "", row.facet].filter(Boolean).join(" · ");
    if (chip) readerInner.append(el("span", "pm-chip", chip));
    var summary = row.summary ? statement(row.summary, row.title) : null;
    if (summary) readerInner.append(summary);
    var lean = el("div", "pm-lean");
    if (row.lean) { lean.append(el("code", "", row.lean)); readerInner.append(lean); }
    var actions = el("div", "pm-actions"), page = row.route && safeLink(row.route, routeBase);
    if (page) { var read = el("a", "", "Open in the book"); read.href = page; actions.append(read); }
    readerInner.append(actions);
    var book = page && window.DOMParser ? pageAt(page).then(function (parsed) {
      var math = shown === shownResult && state.selected === id && borrowed(parsed, id, page);
      if (!math) return;
      var holder = el("div", "pm-math"); holder.append(math.block);
      if (summary) summary.replaceWith(holder); else (lean.parentNode ? lean : actions).before(holder);
      if (math.source && row.lean) { var link = el("a", "", "Lean source"); link.href = math.source; lean.append(link); }
      return typeset(holder);
    }).catch(function () { /* the summary and the link to the book stay */ }) : null;
    [["Uses", rel.uses], ["Used by", rel.usedBy]].forEach(function (pair) {
      readerInner.append(el("h3", "", pair[0] + " (" + num(pair[1].length) + ")"));
      if (!pair[1].length) { readerInner.append(el("p", "pm-empty", pair[0] === "Uses" ? "No prerequisites recorded." : "Nothing uses it yet.")); return; }
      readerInner.append(paged(pair[1], 12, function (item) {
        var other = model.results.get(item.id), outside = rel.outside.get(item.id);
        var titleText = other ? other.row.title : outside ? outside[1] : item.id;
        var where = other ? part(other.home).summary.title : outside && outside[2].length ? (part(outside[2][outside[2].length - 1]) || {summary: {title: ""}}).summary.title || "" : "";
        var li = el("li"), button = el("button"); button.type = "button";
        button.append(titled(el("span"), titleText), el("small", "", plain(where) + (item.statement ? "" : " · proof")));
        button.addEventListener("click", function () { arriveById(item.id).catch(report); });
        li.append(button);
        return li;
      }));
    });
    readerReady = Promise.all([book, typeset(readerInner)]);
  }

  // ---------------------------------------------------------------- trail
  function updateTrail() {
    var here = currentPart();
    var chain = state.selected && model.results.get(state.selected) ? chainOf(model.results.get(state.selected).home)
      : here && here.id !== ROOT ? chainOf(here.id) : [];
    var signature = chain.join("|") + "#" + (state.selected || "");
    if (trail.dataset.signature === signature) return;
    trail.dataset.signature = signature;
    trail.replaceChildren();
    function step(text, go, current) {
      var item = el("li"), node = current ? el("span", "", text) : el("button", "", text);
      if (current) item.setAttribute("aria-current", "location");
      else { node.type = "button"; node.title = text; node.addEventListener("click", go); }
      item.append(node); trail.append(item);
    }
    step(plain(model.index.title), wholeProject, !chain.length && !state.selected);
    chain.forEach(function (id, index) {
      step(plain(part(id).summary.title), function () { leaveFor(id).catch(report); }, index === chain.length - 1 && !state.selected);
    });
    if (state.selected) step(plain(model.results.get(state.selected).row.title), null, true);
  }

  // ---------------------------------------------------------------- history
  // Where the camera is, or where it is going during a flight: history never records a pose halfway along one.
  function settled() { var at = flight ? flight.target : camera; return {x: at.x, y: at.y, k: at.k}; }
  function snapshot() {
    return {pm: 1, camera: settled(), selected: state.selected, focusPart: state.focusPart, picked: state.picked,
      chain: state.selected && model.results.get(state.selected) ? chainOf(model.results.get(state.selected).home) :
        state.focusPart && state.focusPart !== ROOT ? chainOf(state.focusPart) : []};
  }
  // What Back restores besides the camera and the selection.
  function viewState() {
    return {query: search.value, facets: state.facets ? Array.from(state.facets) : null, readerScroll: reader.scrollTop, sideScroll: side.scrollTop};
  }
  // `leaving` is the view state of the entry being left, when the reading pane has already changed under it.
  function remember(replace, leaving) {
    if (embedded) return;
    var snap = snapshot();
    var hash = snap.selected ? "#result=" + encodeURIComponent(snap.selected) :
      snap.focusPart && snap.focusPart !== ROOT ? "#part=" + encodeURIComponent(snap.focusPart) : location.pathname + location.search;
    // The current entry keeps its camera, so Back returns to exactly where the reader was.
    try { history.replaceState(Object.assign({}, history.state || {}, {pm: 1, camera: settled(), selected: history.state && history.state.selected, focusPart: history.state && history.state.focusPart, chain: history.state && history.state.chain}, leaving || viewState()), ""); } catch (_e) { /* ignore */ }
    // Going nowhere new (Whole project from the whole project, Escape with nothing chosen) is not a new entry.
    var current = history.state, same = current && current.pm && current.selected === snap.selected &&
      current.focusPart === snap.focusPart && current.picked === snap.picked;
    if (replace || same) history.replaceState(Object.assign(snap, viewState()), "", hash); else history.pushState(snap, "", hash);
  }
  window.addEventListener("popstate", function (event) {
    if (embedded) return;
    var snap = event.state;
    clearTimeout(cameraTimer);  // a camera write still pending belongs to the entry just left
    var epoch = navigation();
    if (!snap || !snap.pm) { state.picked = null; select(null, {history: false}); state.focusPart = ROOT; fitProject(true); live.textContent = "Whole project"; return; }
    ensureChain(snap.chain || []).then(function () {
      if (epoch !== navEpoch) return;
      state.focusPart = snap.focusPart || null;
      state.picked = snap.picked && part(snap.picked) ? snap.picked : null;
      search.value = snap.query || "";
      var facets = snap.facets ? new Set(snap.facets) : null;
      if (String(facets && Array.from(facets)) !== String(state.facets && Array.from(state.facets))) { state.facets = facets; renderSide(); }
      select(snap.selected || null, {history: false});
      side.scrollTop = snap.sideScroll || 0;
      // The reading pane may change again as the view arrives, and a result's statement and formulas land after it
      // opens. Its scroll comes back once both have, or a shorter pane would cut it short.
      var scrolled = function () {
        var restore = function () { if (epoch === navEpoch) reader.scrollTop = snap.readerScroll || 0; };
        readerReady.then(restore, restore);
      };
      var here = snap.selected && model.results.get(snap.selected);
      live.textContent = here ? "Showing " + plain(here.row.title) : state.focusPart && state.focusPart !== ROOT && part(state.focusPart) ?
        "Showing " + plain(part(state.focusPart).summary.title) : "Whole project";
      if (snap.camera) flyTo(snap.camera, scrolled); else scrolled();
    }).catch(report);
  });
  // Keep the camera of the current entry up to date as the reader moves around.
  var cameraTimer = 0;
  function rememberCamera() {
    if (embedded) return;
    clearTimeout(cameraTimer);
    cameraTimer = setTimeout(function () {
      var current = history.state && history.state.pm ? history.state : snapshot();
      try { history.replaceState(Object.assign({}, current, {camera: settled(), focusPart: state.focusPart}, viewState()), ""); } catch (_e) { /* ignore */ }
    }, 250);
  }
  reader.addEventListener("scroll", rememberCamera);
  side.addEventListener("scroll", rememberCamera);

  // ---------------------------------------------------------------- input
  var drag = null;
  // Zoom per pixel of Control scroll or pinch: a wheel notch (100 px) zooms 2.2 times and a full trackpad pinch about
  // 5, so a reader crosses the library's levels in a few gestures. A key or button press zooms twice.
  var ZOOM_PER_PIXEL = 0.008, ZOOM_STEP = 2;
  // As in the explorer: scrolling (a two-finger swipe) pans, and Control or Command with scroll zooms. Browsers send a
  // trackpad pinch as a Control scroll.
  canvas.addEventListener("wheel", function (event) {
    event.preventDefault();
    var box = canvas.getBoundingClientRect(), pixels = event.deltaMode === 1 ? 25 : 1;
    release();
    if (event.ctrlKey || event.metaKey) {
      zoomAt(clamp(Math.exp(-event.deltaY * pixels * ZOOM_PER_PIXEL), 0.25, 4), event.clientX - box.left, event.clientY - box.top);
    } else {
      camera = {x: camera.x + event.deltaX * pixels / camera.k, y: camera.y + event.deltaY * pixels / camera.k, k: camera.k};
      schedule();
    }
    rememberCamera();
  }, {passive: false});
  // A second finger turns a drag into a pinch, which zooms about the fingers' midpoint and pans with it; nothing is
  // activated when the fingers lift.
  var touches = new Map(), pinch = null;
  function spread() {
    var p = Array.from(touches.values()), box = canvas.getBoundingClientRect();
    return {d: Math.max(1, Math.hypot(p[0][0] - p[1][0], p[0][1] - p[1][1])), x: (p[0][0] + p[1][0]) / 2 - box.left, y: (p[0][1] + p[1][1]) / 2 - box.top};
  }
  function lift(event) {
    touches.delete(event.pointerId);
    if (pinch && touches.size < 2) { pinch = null; rememberCamera(); }
  }
  canvas.addEventListener("pointerdown", function (event) {
    if (event.button !== 0) return;
    if (event.pointerType === "touch") touches.set(event.pointerId, [event.clientX, event.clientY]);
    if (touches.size === 2) { drag = null; canvas.classList.remove("pm-dragging"); release(); pinch = spread(); return; }
    if (touches.size > 2) return;
    drag = {x: event.clientX, y: event.clientY, cx: camera.x, cy: camera.y, moved: false, id: event.pointerId};
  });
  canvas.addEventListener("pointermove", function (event) {
    if (touches.has(event.pointerId)) touches.set(event.pointerId, [event.clientX, event.clientY]);
    if (pinch) {
      var now = spread();
      camera = {x: camera.x - (now.x - pinch.x) / camera.k, y: camera.y - (now.y - pinch.y) / camera.k, k: camera.k};
      zoomAt(now.d / pinch.d, now.x, now.y);
      pinch = now;
      return;
    }
    if (!drag || event.pointerId !== drag.id) return;
    // A press released off the map sent no pointerup here, so the drag ends at the next move with no button down.
    if (!event.buttons) { drag = null; canvas.classList.remove("pm-dragging"); return; }
    var dx = event.clientX - drag.x, dy = event.clientY - drag.y;
    if (!drag.moved && Math.hypot(dx, dy) < 4) return;
    if (!drag.moved) { drag.moved = true; canvas.setPointerCapture(drag.id); canvas.classList.add("pm-dragging"); release(); }
    camera = {x: drag.cx - dx / camera.k, y: drag.cy - dy / camera.k, k: camera.k};
    schedule();
  });
  function endDrag(event) {
    lift(event);
    if (!drag || event.pointerId !== drag.id) return;
    var moved = drag.moved; drag = null; canvas.classList.remove("pm-dragging");
    if (moved) { rememberCamera(); return; }
    activate(event.target);
  }
  canvas.addEventListener("pointerup", endDrag);
  canvas.addEventListener("pointercancel", function (event) { lift(event); drag = null; canvas.classList.remove("pm-dragging"); });
  function activate(target) {
    var resultNode = target.closest && target.closest("[data-result]");
    if (resultNode) { navigation(); select(resultNode.getAttribute("data-result")); return; }
    var partNode = target.closest && target.closest("[data-part]");
    if (partNode) {
      var id = partNode.getAttribute("data-part"), inside = state.focusPart === id;
      if (state.picked === id) flyToPart(id).catch(report); else pick(id).catch(report);
      // A click in the part the view is already in, between its cards, leaves the reader on its page.
      if (!inside) tell(id);
      return;
    }
    if (state.selected) select(null); else unpick();
  }
  canvas.addEventListener("keydown", function (event) {
    // With a modifier the keys are the browser's: Command-Left goes Back, Command-0 resets its zoom.
    if (event.altKey || event.metaKey || event.ctrlKey) return;
    var target = event.target, step = 80;
    if (event.key === "Enter" || event.key === " ") {
      if (target !== canvas) { event.preventDefault(); activate(target); }
      return;
    }
    if (target !== canvas && !/^Arrow/.test(event.key) && "+-=0".indexOf(event.key) < 0 && event.key !== "Escape") return;
    if (event.key === "ArrowLeft") camera.x -= step / camera.k;
    else if (event.key === "ArrowRight") camera.x += step / camera.k;
    else if (event.key === "ArrowUp") camera.y -= step / camera.k;
    else if (event.key === "ArrowDown") camera.y += step / camera.k;
    else if (event.key === "+" || event.key === "=") zoomAt(ZOOM_STEP, size.w / 2, size.h / 2);
    else if (event.key === "-") zoomAt(1 / ZOOM_STEP, size.w / 2, size.h / 2);
    else if (event.key === "0") wholeProject();
    else if (event.key === "Escape") escape();
    else return;
    if (event.key !== "0" && event.key !== "Escape") release();
    event.preventDefault(); schedule();
    if (event.key !== "0") rememberCamera();
  });
  zoomIn.addEventListener("click", function () { release(); zoomAt(ZOOM_STEP, size.w / 2, size.h / 2); rememberCamera(); });
  zoomOut.addEventListener("click", function () { release(); zoomAt(1 / ZOOM_STEP, size.w / 2, size.h / 2); rememberCamera(); });
  function wholeProject() {
    var leaving = viewState();
    navigation(); state.focusPart = ROOT; state.picked = null; select(null, {history: false}); remember(false, leaving); fitProject(); live.textContent = "Whole project";
  }
  fitAll.addEventListener("click", wholeProject);
  // One level up from where the reader is: from a result to its part, from a part to the part around it.
  function upOneLevel() {
    if (state.selected) {
      var home = model.results.get(state.selected) && model.results.get(state.selected).home;
      if (home) { tell(home); leaveFor(home).catch(report); } else select(null, {history: false});
      return;
    }
    var here = state.focusPart && state.focusPart !== ROOT && part(state.focusPart) || viewPart();
    if (!here || here.id === ROOT) return;
    // Embedded, the reader turns to the part the view is in before the view leaves it, as Up from a result does.
    if (embedded && fromBook !== here.id && hasPage(here.id)) { tell(here.id); return; }
    if (here.parent === ROOT || !part(here.parent)) wholeProject(); else { tell(here.parent); flyToPart(here.parent).catch(report); }
  }
  // Escape lets go of what is chosen first, then goes up a level.
  function escape() { if (state.selected) select(null); else if (state.picked) unpick(); else upOneLevel(); }
  upLevel.addEventListener("click", function () { unpick(); upOneLevel(); });
  document.addEventListener("keydown", function (event) {
    var active = document.activeElement, typing = !!active && /^(INPUT|TEXTAREA|SELECT)$/.test(active.tagName);
    // Embedded, "/" is the book's search, and the map's host handles its own Escape.
    if (embedded) return;
    if (event.key === "/" && active !== search && !typing) {
      event.preventDefault(); search.focus(); search.select();
    } else if (event.key === "Escape" && !typing && !event.defaultPrevented) { event.preventDefault(); escape(); }
  });
  // The world is packed for the stage's shape: a resize refits the camera, and turning between portrait and landscape repacks.
  // A drag of the book's panes does neither: what the map shows stays where it is on the page (measure keeps it there), or
  // the whole project, when that is the view, stays fitted, and nothing flies when the drag ends. Only a stage that was
  // never packed for, or that the book hid, goes to the page's place then, and a stage the drag shut goes there when it
  // shows again, at once if a drag opens it. One never packed for stays blank while a drag opens it, and is packed for
  // the stage the drag leaves, not the 160px it opens at.
  var dragged = false, settling = false, settledSize = null, landing = false, landingEpoch = -1;
  function wholeView() { return state.focusPart === ROOT && !state.selected && !state.picked; }
  // A drag sends the map to the page's place at once, however late the place's part loads, unless the reader goes
  // elsewhere first: the flight show() starts now, or the one its navigation starts later, lands where it is headed.
  function land() {
    fromBook = null; landing = true;
    show(book.getAttribute("data-map-start") || "");
    landing = false; landingEpoch = navEpoch;
  }
  function resized() {
    if (!stageSize) return;
    measure();
    if (embedded && book.classList.contains("bp-dag-resizing")) {
      dragged = true; settledSize = null;
      if (size.w > 1 && stageSize.w > 1) {
        if (missed) land();
        else if (wholeView()) fitProject(true);
      }
      // Drawn before the frame is painted, so the map never lags its stage by a frame as the edges move.
      render();
      return;
    }
    // The drag's last step can reach the stage after the drag settled, in the same frame; it settled with the rest.
    var late = settledSize && settledSize.w === size.w && settledSize.h === size.h;
    settledSize = null;
    if (late) return;
    // The book hides its stage while it lists statements, or the reader takes its room; the map waits until it shows again.
    if (size.w <= 1) { if (settling) missed = true; return; }
    var repack = stageSize.w <= 1 || (!settling && (size.w >= size.h) !== (stageSize.w >= stageSize.h));
    if (repack) {
      stageSize = {w: size.w, h: size.h};
      packRoot();
      if (!embedded) fitProject(true);
    }
    // In the book, a stage that was hidden or repacked goes back to the page's place, and the reading pane opening or
    // closing refits the whole project when that is the view.
    if (embedded && settling && (repack || missed)) land();
    else if (embedded && (repack || missed)) { fromBook = null; show(book.getAttribute("data-map-start") || ""); }
    else if (embedded && wholeView()) fitProject(settling);
    schedule();
  }
  if (window.ResizeObserver) new ResizeObserver(resized).observe(stage);
  function report(error) {
    state.error = "Something went wrong: " + (error && error.message ? error.message : error) + ". Try again, or reload the page.";
    live.textContent = state.error;
    schedule();
    if (window.console) console.error(error);
  }

  // Where the book sends the map: the roadmap's own id for the whole project, a part, a result, or else (an article
  // that states nothing) the part whose folder holds it. What the map itself just picked is already in view.
  var missed = false;
  function show(id) {
    measure();
    // An empty roadmap draws nothing, and a hidden stage (the book's list) waits until it shows again.
    if (!part(ROOT)) return;
    missed = size.w <= 1;
    if (missed) return;
    if (id && id === fromBook && (state.selected === id || state.picked === id || state.focusPart === id)) return;
    fromBook = id || null; reading = null;
    if (!id || id === "roadmap") return wholeProject();
    if (knownPart(id)) {
      if (state.selected) select(null, {history: false});
      return goToPart(id, {history: false}).catch(report);
    }
    return arriveById(id, {history: false}).catch(function () {
      var home = nearestPart(id);
      if (state.selected) select(null, {history: false});
      return home ? goToPart(home, {history: false}) : wholeProject();
    }).catch(wholeProject);
  }
  // project_map.py names the parts it makes up "region:..." or ".../~n": they, and the map's own root, have no page.
  function hasPage(id) { return id !== ROOT && !/^region:|\/~/.test(id); }
  // Search lists every part, loaded or not.
  function knownPart(id) { return Boolean(part(id) || model.search && model.search.partById.has(id)); }
  // A page the map has no card for, such as an article that states nothing, opens the part whose folder holds it.
  function nearestPart(id) {
    for (var at = id; at; at = at.slice(0, Math.max(0, at.lastIndexOf("/")))) if (knownPart(at)) return at;
    return null;
  }
  // Embedded, a part the reader picks, opens or goes up to on the map opens its page in the book, as a picked result
  // does.
  function tell(id) {
    if (!embedded || !id || id === fromBook || !hasPage(id)) return;
    fromBook = id;
    // Focus stays on the map, so the part can be opened there next.
    host.dispatchEvent(new CustomEvent("autoform-map-select", {bubbles: true, detail: {id: id, history: "push", focus: false}}));
  }
  // The book's status filter, as the statuses it shows (space-separated; absent for all of them): the map dims the rest,
  // unless the project tracks no Lean.
  var statuses = null;
  function readStatuses() {
    var shown = book.getAttribute("data-map-statuses");
    statuses = shown === null ? null : new Set(shown.split(" ").filter(Boolean));
  }
  // The book also marks on its host whether it has a result selected. When it lets go of the page's result (Escape in
  // its reader) the map does too, and Back to the selection selects it again.
  var bookSelects = embedded && book.classList.contains("bp-dag-has-selection");
  if (embedded && window.MutationObserver) new MutationObserver(function (records) {
    var changed = function (name) { return records.some(function (record) { return record.attributeName === name; }); };
    var start = book.getAttribute("data-map-start") || "", selects = book.classList.contains("bp-dag-has-selection");
    var letGo = bookSelects && !selects, regained = !bookSelects && selects;
    bookSelects = selects;
    if (dragged && !book.classList.contains("bp-dag-resizing")) {
      dragged = false; settling = true; resized(); settling = false; settledSize = {w: size.w, h: size.h};
    }
    if (changed("data-map-statuses")) { readStatuses(); schedule(); }
    if (!model.parts.has(ROOT)) return;
    if (changed("data-map-start")) show(start);
    else if (letGo && state.selected === start) { fromBook = null; select(null, {history: false}); }
    else if (regained && state.selected !== start) show(start);
  }).observe(book, {attributes: true, attributeFilter: ["data-map-start", "data-map-statuses", "class"]});
  if (embedded) readStatuses();
  // Embedded, the statement being read lights up on the map: the first one in the book's reading pane that reaches below
  // the pane's top, as the reader scrolls a chapter. One the map has drawn off the stage comes into view. A scroll that
  // comes with a new width is the text reflowing as a pane moves, which the browser scrolls to keep the reader's place: it
  // moves the light, not the camera.
  var reading = null, readingFrame = 0;
  function followReading() {
    var body = document.querySelector(".bp-reading-body");
    if (!body || body.pmFollowed) return;
    body.pmFollowed = true;
    var width = body.clientWidth;
    body.addEventListener("scroll", function () {
      cancelAnimationFrame(readingFrame);
      readingFrame = requestAnimationFrame(function () {
        var reflowed = body.clientWidth !== width, top = body.getBoundingClientRect().top + 40, id = null;
        width = body.clientWidth;
        Array.prototype.some.call(body.querySelectorAll(".bp-thmwrapper[data-autoform-node-id]"), function (card) {
          if (card.getBoundingClientRect().bottom < top) return false;
          id = card.getAttribute("data-autoform-node-id");
          return true;
        });
        if (id === reading) return;
        reading = id; schedule();
        var entry = id && model.results.get(id), b = !reflowed && size.w > 1 && entry && entry.box && screenBox(entry.box);
        if (b && !flight && (b.x < 0 || b.y < 0 || b.x + b.w > size.w || b.y + b.h > size.h)) {
          var at = centerOf(entry.box); flyTo({x: at[0], y: at[1], k: camera.k});
        }
      });
    }, {passive: true});
  }

  // ---------------------------------------------------------------- start
  styled.then(function () { return fetchJSON("index.json"); }).then(function (index) {
    if (!L) throw new Error("the map's layout script did not load");
    model.index = index;
    // A project that tracks no Lean has no Lean names to search for.
    if (!tracked()) { search.placeholder = "Search theorems by name"; search.setAttribute("aria-label", search.placeholder); }
    if (!index.regions.length) {
      var nothing = "Nothing is on the map yet: the roadmap has no results.";
      readerInner.replaceChildren(el("p", "pm-kicker", "Whole project"), el("h2", "", plain(index.title)), el("p", "pm-empty", nothing));
      // The stage says so too, for the book, which hides the map's reading pane; there is nothing to move.
      hint.textContent = nothing; hint.classList.add("pm-hint-strong"); top.hidden = true;
      return;
    }
    var root = {id: ROOT, summary: {id: ROOT, title: index.title, results: index.results, status: index.status, parts: index.regions.length, api: [], api_total: 0, imports_total: 0},
      parent: null, data: {children: index.regions, edges: index.region_edges}, loading: null, box: null, ownBox: null, view: null, kids: [], results: []};
    model.parts.set(ROOT, root);
    index.regions.forEach(function (summary) { register(summary, ROOT); });
    measure();
    stageSize = {w: size.w, h: size.h};
    packRoot();
    // The map opens on the whole project, which the reading pane describes until the reader goes somewhere.
    state.focusPart = ROOT;
    fitProject(true);
    renderSide();
    var hash = location.hash.slice(1), params = new URLSearchParams(hash);
    if (embedded) { show(book.getAttribute("data-map-start") || ""); followReading(); schedule(); return; }
    var start = params.get("result") ? arriveById(params.get("result"), {replace: true})
      : params.get("part") ? goToPart(params.get("part"), {replace: true})
      : Promise.resolve(remember(true));
    start.catch(report);
    schedule();
  }).catch(function (error) {
    readerInner.replaceChildren(el("p", "pm-empty", "The map could not load: " + error.message));
    hint.textContent = "The map could not load: " + error.message; hint.classList.add("pm-hint-strong");
  });
  // Set up: a book whose map script ends without this mark, as when it throws before here, shows a notice of its own.
  host.dataset.pmReady = "1";
})();
