#!/usr/bin/env python3
"""Deterministically typeset the frozen 214 proof packet and current foundation.

No symbolic expansion, network access, builds, or acceptance records are made.
The Markdown renderer changes presentation only.  Each source line is bound to
the generated TeX lines in SOURCE_SPANS.json, including retained blank lines.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys
import unicodedata
from urllib.parse import urljoin

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
FROZEN = "110cf72565be326fd567cd1a64a3b2e00213dcd1"
WEB = f"https://github.com/elliotglazer/diophantine-z-q/blob/{FROZEN}/"
V15 = ROOT / "research/version15/snapshots/v15-222-004/manuscript/quartic_v15.tex"
V15_SHA = "44ba3a8ec8521c29b81b26cfb9981cd6d5f3c76d54e7782438614842edb52c74"
FOUNDATION_PROFILE = ROOT / "docs/current-manuscript.json"
FOUNDATION = ROOT / json.loads(FOUNDATION_PROFILE.read_text())["tex"]["path"]
FOUNDATION_SHA = "aeb2b6a42a03943d7f8c46682389c8da693d2903ba92ccc164bbbd236451de74"
PACKET = ROOT / "research/quartic214"
OUT: list[str] = []
SPANS: list[dict] = []
SOURCES: dict[str, dict] = {}
CORRECTIONS = HERE / "SOURCE_CORRECTIONS_V1.json"
ACTIVE_CORRECTIONS: dict[tuple[str, int], dict] = {}


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def emit(s: str = "") -> None:
    OUT.extend(s.splitlines() or [""])


def register(p: Path) -> str:
    rel = p.relative_to(ROOT).as_posix()
    data = p.read_bytes()
    SOURCES[rel] = {"sha256": digest(data), "bytes": len(data),
                    "line_count": len(data.splitlines())}
    return rel


def bound(p: Path, start: int, end: int, tex: str, method: str) -> None:
    rel = register(p)
    first = len(OUT) + 1
    if method=="exact-retained-body-LF":
        # A trailing empty source line is an actual mapped line, distinct
        # from a file's terminal newline.  splitlines() would discard it.
        OUT.extend(tex.split("\n"))
    else:emit(tex)
    span = {"source": rel, "source_lines": [start, end],
            "tex_lines": [first, len(OUT)], "method": method}
    corrections = [ACTIVE_CORRECTIONS[(rel, n)] for n in range(start, end + 1)
                   if (rel, n) in ACTIVE_CORRECTIONS]
    if corrections:
        span["source_corrections"] = corrections
    SPANS.append(span)


TEXT_UNICODE = {
    "–": "--", "—": "---", "−": "-", "’": "'", "‘": "`",
    "“": "``", "”": "''", "…": r"\ldots{}", "§": r"\S{}",
    "²": r"\ensuremath{{}^2}", "³": r"\ensuremath{{}^3}",
    "¹": r"\ensuremath{{}^1}",
}
GREEK = {
    "alpha": "alpha", "beta": "beta", "gamma": "gamma", "delta": "delta",
    "epsilon": "epsilon", "zeta": "zeta", "eta": "eta", "theta": "theta",
    "iota": "iota", "kappa": "kappa", "lambda": "lambda", "mu": "mu",
    "nu": "nu", "pi": "pi", "rho": "rho", "sigma": "sigma", "tau": "tau",
    "phi": "phi", "chi": "chi", "omega": "omega", "ell": "ell",
    "Delta": "Delta", "Gamma": "Gamma", "Theta": "Theta", "Sigma": "Sigma",
    "Omega": "Omega",
}
GREEK_PATTERN = "(?:" + "|".join(sorted(GREEK,key=len,reverse=True)) + ")"
SYMBOLS = {
    "α": r"\alpha ", "β": r"\beta ", "γ": r"\gamma ", "δ": r"\delta ",
    "ε": r"\epsilon ", "η": r"\eta ", "θ": r"\theta ", "κ": r"\kappa ",
    "λ": r"\lambda ", "μ": r"\mu ", "ν": r"\nu ", "π": r"\pi ",
    "ρ": r"\rho ", "σ": r"\sigma ", "τ": r"\tau ", "φ": r"\phi ",
    "χ": r"\chi ", "ω": r"\omega ", "Γ": r"\Gamma ", "Δ": r"\Delta ",
    "Θ": r"\Theta ", "Σ": r"\Sigma ", "Ω": r"\Omega ", "ℓ": r"\ell ",
    "𝒳": r"{\mathcal X}", "→": r"\to ", "↦": r"\mapsto ", "↑": r"\uparrow ",
    "∈": r"\in ", "≠": r"\ne ", "≤": r"\le ", "≥": r"\ge ",
    "⊂": r"\subset ", "⊃": r"\supset ", "⊗": r"\otimes ",
    "⊕": r"\oplus ", "∩": r"\cap ", "∪": r"\cup ", "∞": r"\infty ",
    "≅": r"\cong ", "±": r"\pm ", "×": r"\times ", "∏": r"\prod ",
    "∑": r"\sum ", "∧": r"\wedge ", "∫": r"\int ",
    "∖": r"\setminus ", "⇔": r"\Longleftrightarrow ",
    "ĥ": r"\widehat{h}",
    "∣": r"\mid ", "·": r"\cdot ", "′": "'",
    "∀": r"\forall ", "∃": r"\exists ", "⇒": r"\Longrightarrow ",
    "⁴": "^{4}", "⌊": r"\lfloor ", "⌋": r"\rfloor ",
    "−": "-", "²": "^{2}", "³": "^{3}", "¹": "^{1}", "…": r"\ldots ",
}


def escape(s: str) -> str:
    """Text escape, retaining readable accents and mathematical Unicode."""
    result = []
    for c in s:
        if c in TEXT_UNICODE:
            result.append(TEXT_UNICODE[c])
        elif c in SYMBOLS:
            result.append(r"\ensuremath{" + SYMBOLS[c] + "}")
        elif c in "\\{}$&#%_^~":
            result.append({"\\": r"\textbackslash{}", "~": r"\textasciitilde{}",
                           "^": r"\textasciicircum{}"}.get(c, "\\" + c))
        else:
            result.append(c)
    return "".join(result)


OPS = {"log", "exp", "max", "min", "dim", "det", "deg", "rad", "ord",
       "ker", "Hom", "End", "Jac", "Tr", "Norm", "Spec", "Sel", "Sha",
       "ht", "depth", "disc", "tr", "supp", "nrd", "rank", "Aut", "GL"}
MATH_WORDS = {"in": r"\in", "iff": r"\Longleftrightarrow", "exists": r"\exists",
              "union": r"\cup", "subset": r"\subset", "divides": r"\mid",
              "product": r"\prod", "sum": r"\sum", "integral": r"\int",
              "infinity": r"\infty", "direct-sum": r"\oplus",
              "composed": r"\circ", "with": r"\text{ with }",
              "over": r"\text{ over }", "for": r"\text{ for }", "every": r"\text{ every }",
              "and": r"\text{ and }", "where": r"\text{ where }",
              "not": r"\text{ not }", "dividing": r"\text{ dividing }", "integer": r"\text{ integer }",
              "is": r"\text{ is }", "to": r"\text{ to }", "each": r"\text{ each }",
              "squarefree": r"\text{ squarefree }", "modulo": r"\text{ modulo }",
              "respectively": r"\text{ respectively }", "there": r"\text{ there }",
              "reduction": r"\operatorname{reduction}", "relative": r"\text{ relative }",
              "implies": r"\Longrightarrow"}


def math(s: str) -> str:
    """Translate source ASCII math to TeX without altering any operands."""
    s = s.strip().strip("`")
    s = re.sub(r"\s{2,}", " ", s).replace("−", "-")
    # These root operands are explicit in the source and its pointed
    # isomorphisms.  Never introduce an empty radicand or absorb the final Y.
    s = s.replace("√dY", r"\sqrt{d}Y")
    s = re.sub(r"√(pi|[A-Za-z]'?|[0-9]+|π)", lambda m:r"\sqrt{"+m[1]+"}",s)
    if "√" in s: raise ValueError("Unresolved radical operand: "+s)
    s = re.sub(r"(?<![A-Za-z\\])sqrt\(([^()]*)\)",lambda m:r"\sqrt{"+(r"\pi" if m[1]=="pi" else m[1])+"}",s)
    s = re.sub(r"2\^v2\(([^()]*)\)",r"2^{v_2(\1)}",s)
    s = re.sub(r"\bH0\(","H^0(",s)
    # Protect already-authored TeX control sequences and their arguments by
    # handling ASCII words only when not introduced by a backslash.
    s = s.replace("direct-sum", "⊕")
    s = s.replace("<=>", "⇔").replace("<->", "⇔").replace("->", "→")
    s = s.replace("<=", "≤").replace(">=", "≥").replace("!=", "≠")
    s = s.replace("=>", "⇒")
    s = s.replace("⇔", r"\Longleftrightarrow ").replace("⇒", r"\Longrightarrow ")
    # Parse complete script operands, including a following script.  Thus
    # 149^-L_N means 149^{-(L_N)}, not (149^-L)_N.  Literal set braces
    # outside script operands remain visible delimiters.
    def scripts(text):
        def atom(i):
            if i>=len(text): return "",i
            if text[i] in "+-":
                v,j=atom(i+1); return text[i]+v,j
            if text[i] in "({":
                opening=text[i]; closing=")" if opening=="(" else "}"; j=i+1; level=1
                while j<len(text) and level:
                    if text[j]==opening:level+=1
                    elif text[j]==closing:level-=1
                    j+=1
                if level: return text[i],i+1
                return scripts(text[i+1:j-1]),j
            m=re.match(r"(?:\\[A-Za-z]+|[A-Za-z]+[0-9]*|[0-9]+)",text[i:])
            if m: value=m.group(); j=i+len(value)
            else: value=text[i]; j=i+1
            # L' is the explicitly named base field.  Other primes, e.g.
            # L_i', remain primes on the indexed object, not on its index.
            if value=="L" and text[j:j+1]=="'": value+="'";j+=1
            while j<len(text) and text[j] == "_" and value!="vee":
                mark=text[j]; rest,j=atom(j+1); value="{"+value+"}"+mark+"{"+rest+"}"
            return value,j
        result=[]; i=0
        while i<len(text):
            if text[i] in "_^":
                mark=text[i]; value,i=atom(i+1); result.append(mark+"{"+value+"}")
            elif text[i]=="{" and (not i or text[i-1]!="\\"):
                result.append(r"\{");i+=1
            elif text[i]=="}" and (not i or text[i-1]!="\\"):
                result.append(r"\}");i+=1
            elif text[i]=="\\":
                # Keep already-authored control sequences and their explicit
                # brace arguments intact (not interpreted as literal sets).
                m=re.match(r"\\[A-Za-z]+(?:\{[^{}]*\})?",text[i:])
                if m:result.append(m.group());i+=len(m.group())
                else:result.append(text[i:i+2]);i+=2
            else:result.append(text[i]);i+=1
        return "".join(result)
    s=scripts(s)
    # Common source shorthands keep their stated notation.
    s = re.sub(r"(?<![A-Za-z\\])sqrt(\d+)", r"\\sqrt{\1}", s)
    s = re.sub(r"(?<![A-Za-z\\])log(?=[A-Z]|ell\b|d\b|p\b|\d)",r"\\log ",s)
    s = re.sub(r"(?<![A-Za-z\\])([A-Za-z])([0-9]+)\b", r"\1_{\2}", s)
    s = re.sub(r"(?<![A-Za-z\\])("+GREEK_PATTERN+r")([0-9]+)\b",r"\1_{\2}",s)
    s = re.sub(r"\bhF\b", r"\\hF", s)
    s = re.sub(r"\bhhat\b", r"\\widehat{h}", s)
    s = re.sub(r"\bQbar\b", r"\\overline{Q}", s)
    def word(m):
        w = m.group()
        if w in GREEK: return "\\" + GREEK[w] + " "
        if w in OPS: return r"\operatorname{" + w + "}"
        if w in MATH_WORDS: return MATH_WORDS[w] + " "
        if w in {"vee", "circ"}:return "\\"+w+" "
        # A bare Q can be a point; a bare Z can be a regular model.  Preserve
        # these ASCII source letters rather than guessing a blackboard font.
        if len(w) > 2: return r"\text{" + escape(w) + "}"
        return w
    # Existing control-sequence names, including text/operatorname arguments,
    # must not be reinterpreted.  Process each original ASCII word once.
    pieces = []; pos = 0
    for m in re.finditer(r"\\[A-Za-z]+(?:\{[^{}]*\})?|[A-Za-z]+", s):
        pieces.append(s[pos:m.start()]); w = m.group()
        pieces.append(w if w.startswith("\\") else word(m)); pos = m.end()
    pieces.append(s[pos:]); s = "".join(pieces)
    s = "".join(SYMBOLS.get(c, c) for c in s)
    s = s.replace("#", r"\#").replace("%", r"\%").replace("&", r"\&")
    # A literal TeX tilde in the source denotes isogeny, not a space.
    s = s.replace("~", r"\sim ")
    return s


def is_math(s: str) -> bool:
    core = s.strip(".,;:()[]")
    if not core: return False
    if re.match(r"\\(?:mathcal|mathfrak|mathbb|mathrm|mathbf|bar|overline|widehat|sqrt)\b",core):return True
    if re.fullmatch(r"[A-Za-z]'?", core) and core not in {"a","A"}: return True
    if core in GREEK or core in {"hF", "Qbar", "GL2", "P1", "P2", "A1"}: return True
    # Select explicit mathematical uses of spelled-out Greek names without
    # treating arbitrary Greek-prefixed prose or identifiers as mathematics.
    if re.match(r"^[+-]?"+GREEK_PATTERN+r"(?=[0-9(*/+]|$)",core):return True
    atom=r"(?:[A-Za-z][0-9]*|"+GREEK_PATTERN+r"[0-9]*)"
    if re.fullmatch(r"[+-]?"+atom+r"(?:\*"+atom+r")+",core):return True
    if any(c in SYMBOLS for c in core):return True
    if any(c in core for c in "=^_<>±²³¹αβγδϵηθκλμνπρστωΓΔΘΣΩℓ𝒳∈⊂⊃⊗∧∫∞≅≤≥≠×→↦∩∏−√"):
        return True
    if re.match(r"^(?:[A-Za-z]|hF|hhat|exp|sqrt|rad|log|max|min|Tr|Hom|End|Jac|ord|dim|ker|Spec|Sel|Sha)\(", core):
        return True
    if re.fullmatch(r"[A-Za-z][0-9]+", core): return True
    return False


def literal(s: str) -> str:
    return r"\nolinkurl{" + s.replace("%",r"\%") + "}"


def code(s: str) -> str:
    if re.search(r"\.(?:md|tex|json|py)\b",s) or s.startswith(("/root/","research/","sources/","proofs/","height/","different/","evaluation/")):
        return literal(s)
    if len(s) < 125 and is_math(s) and not re.search(r"\.(?:md|tex|json|py)\b", s):
        return r"\(" + math(s) + r"\)"
    return literal(s)


def prose(s: str, source: Path) -> str:
    # Exact already-TeX math, code, links and emphasis are recursively rendered.
    pattern = r"(<https?://[^>]+>|\\\(.*?\\\)|\\(?:ref|eqref)\{[^}]+\}|\$[^$]+\$|`[^`]+`|\[[^\]]+\]\([^\s]+\)|\*\*.*?\*\*|(?<!\w)\*[^*]+\*)"
    parts = []; last = 0
    for m in re.finditer(pattern, s):
        parts.append(plain(s[last:m.start()])); item = m.group()
        if item.startswith("<http"):
            parts.append(r"\url{"+item[1:-1].replace("%",r"\%")+"}")
        elif item.startswith(r"\(") or item.startswith("$"):
            parts.append("".join(SYMBOLS.get(c, c) for c in item))
        elif item.startswith((r"\ref{",r"\eqref{")):parts.append(item)
        elif item.startswith("`"): parts.append(code(item[1:-1]))
        elif item.startswith("["):
            lm = re.fullmatch(r"\[([^\]]+)\]\(([^\s]+)\)", item)
            assert lm
            title, url = lm.groups()
            if not re.match(r"https?://", url):
                url = urljoin(WEB + source.relative_to(ROOT).as_posix(), url)
            parts.append(r"\href{" + url.replace("#", r"\#").replace("%", r"\%") + "}{" + prose(title, source) + "}")
        elif item.startswith("**"): parts.append(r"\textbf{" + prose(item[2:-2], source) + "}")
        else: parts.append(r"\emph{" + prose(item[1:-1], source) + "}")
        last = m.end()
    parts.append(plain(s[last:])); return "".join(parts)


def plain(s: str) -> str:
    result = []
    # Mathematical subscripts such as product_(p in S10) are one balanced
    # span even though their conditions contain spaces.  Never split at an
    # interior space and silently discard the rest of the quantified domain.
    tokens=[]; start=0; stack=[]
    for i,c in enumerate(s):
        if c in "([{":stack.append(c)
        elif c in ")]}":
            if stack:stack.pop()
        elif c.isspace() and not stack:
            if re.search(r"\\(?:mathcal|mathfrak|mathbb|mathrm|mathbf|bar|overline|widehat|sqrt)$",s[start:i]):
                continue
            if i>start:tokens.append(s[start:i])
            tokens.append(c);start=i+1
    if start<len(s):tokens.append(s[start:])
    for token in tokens:
        if not token or token.isspace(): result.append(token); continue
        if re.match(r"https?://", token):
            tail = "." if token.endswith(".") else ""
            result.append(r"\url{" + token[:-1] + "}." if tail else r"\url{" + token + "}"); continue
        if re.fullmatch(r"[0-9a-f]{32,}", token.strip(".,;")):
            result.append(code(token)); continue
        hm=re.fullmatch(r"(SHA256|sha256|hashes|hash|commit|HEAD|head|and)([0-9a-f]{40,64})([.,;]?)",token)
        if hm:
            result.append(escape(hm[1])+code(hm[2])+escape(hm[3]));continue
        if re.search(r"\.(?:md|tex|json|py)(?=$|[.,;:]|\d)",token):
            result.append(code(token));continue
        if is_math(token):
            core = token.rstrip(".,;")
            result.append(r"\(" + math(core) + r"\)" + escape(token[len(core):]))
        else: result.append(escape(token))
    return "".join(result)


def markdown(p: Path, label: str, notice: str = "") -> None:
    lines = p.read_text().splitlines(); rel = register(p)
    register(CORRECTIONS)
    for correction in json.loads(CORRECTIONS.read_text())["corrections"]:
        if correction["source"] != rel:
            continue
        n = correction["source_line"]
        if (SOURCES[rel]["sha256"] != correction["source_sha256"]
                or lines[n - 1] != correction["original_line"]):
            raise ValueError("Stale source correction: " + correction["id"])
        lines[n - 1] = correction["corrected_line"]
        ACTIVE_CORRECTIONS[(rel, n)] = {
            "sidecar": CORRECTIONS.relative_to(ROOT).as_posix(),
            "id": correction["id"],
            "corrected_source_line": correction["corrected_line"]}
        if "finding_ids" in correction:
            ACTIVE_CORRECTIONS[(rel, n)]["finding_ids"] = correction["finding_ids"]

    # Explicit source-local notation resolutions.  Sigma denotes sums in
    # exactly these two sources; in the other sources it remains the named
    # exceptional prime set.  These adapters never change that global set.
    if p.name in {"aggregate-bridge.md","height-metric.md","height-different.md"}:
        lines=[l.replace("Σ","∑") for l in lines]
    if p.name in {"aggregate-bridge.md","uniform-existence.md"}:
        lines=[l.replace("F+","F_{+}") for l in lines]
    if p.name=="uniform-existence.md":
        lines=[l.replace("mathfrak_b",r"\mathfrak{b}") for l in lines]
    if p.name=="height-averaging.md":
        lines=[l.replace(" x "," × ") if "J_0 = C_1 x ... x C_r x E" in l else l for l in lines]
    if p.name=="height-metric.md":
        lines=[l.replace("p*ω","p_*ω").replace("barη",r"\overline{η}")
                 .replace("dbar t",r"d\overline{t}").replace("P1_t","P^1_t") for l in lines]
    if p.name in {"height-evaluation.md","height-different.md"}:
        lines=[re.sub(r"\bP1\b","P^1",l) for l in lines]
    emit(r"\clearpage")
    emit("% Source: " + p.relative_to(ROOT).as_posix())
    i = 0; in_display = False; in_fence = False
    while i < len(lines):
        line = lines[i]; n = i+1
        if line.startswith("```"):
            in_fence = not in_fence
            bound(p, n, n, "% fenced source marker", "fence-marker"); i += 1; continue
        if line.lstrip().startswith("`") and line.count("`")==1:
            # The bounded source inventory contains two multi-line code-math
            # spans.  Keep each entire expression and its source tag together.
            formulas=[line.lstrip()[1:]];j=i+1;suffix=None
            while j<len(lines):
                if "`" in lines[j]:
                    last,suffix=lines[j].split("`",1);formulas.append(last.strip());break
                formulas.append(lines[j].strip());j+=1
            if suffix is None:raise ValueError(f"Unterminated source code-math at {p}:{n}")
            display=[r"\begin{gather*}"]
            tag=re.fullmatch(r"\s*([.,;]?)\s*\(([^)]+)\)\s*",suffix)
            for k,formula in enumerate(formulas):
                end=(r"\\" if k<len(formulas)-1 else (tag[1]+r"\tag{"+escape(tag[2])+"}" if tag else math(suffix.strip())))
                display.append(math(formula)+end)
            display.append(r"\end{gather*}")
            bound(p,n,j+1,"\n".join(display),"complete-multiline-code-math-display")
            i=j+1;continue
        if line.strip() in {r"\[", r"\]"}:
            in_display = line.strip() == r"\["
            bound(p, n, n, line, "authored-tex-math"); i += 1; continue
        if in_display:
            bound(p, n, n, "".join(SYMBOLS.get(c,c) for c in line), "authored-tex-math-unicode"); i += 1; continue
        if not line.strip():
            bound(p, n, n, "", "paragraph-break"); i += 1; continue
        if line.startswith("#"):
            m = re.match(r"(#+)\s+(.*)", line); assert m
            level = len(m.group(1)); command = {1:"section", 2:"subsection", 3:"subsubsection"}.get(level,"paragraph")
            text = "\\" + command + "{" + prose(m.group(2),p) + "}"
            if level == 1: text += r"\label{q214:" + label + "}"
            bound(p,n,n,text,"markdown-heading")
            if level == 1:
                emit(r"\noindent\textit{Source: }\nolinkurl{" + p.relative_to(ROOT).as_posix() + r"}.\par")
                if notice: emit(r"\begin{quote}\small " + notice + r"\end{quote}")
            i += 1; continue
        if line.startswith("|"):
            rows=[]; j=i
            while j<len(lines) and lines[j].startswith("|"):
                cells=lines[j].strip().strip("|").split("|")
                # Pipe characters in inline mathematical expressions occur in
                # these source tables only as actual delimiters after backticks.
                if not all(re.fullmatch(r"\s*:?-+:?\s*",c) for c in cells): rows.append(cells)
                j+=1
            width = max(len(r) for r in rows)
            # Keep the first source field, and join any literal math pipes back
            # into the right-hand field in these two-column proof tables.
            table=[r"\begin{longtable}{@{}p{0.23\linewidth}p{0.73\linewidth}@{}}",r"\toprule"]
            for idx,row in enumerate(rows):
                cells=[row[0], "|".join(row[1:])]
                table.append(" & ".join(prose(c.strip(),p) for c in cells)+r"\\")
                if idx==0: table.extend([r"\midrule",r"\endhead"])
            table.extend([r"\bottomrule",r"\end{longtable}"])
            bound(p,n,j,"\n".join(table),"markdown-proof-table"); i=j; continue
        if line.startswith(" ") or in_fence:
            # Source-indented mathematical statements are real display math.
            j=i+1
            while j<len(lines) and lines[j].strip() and (lines[j].startswith(" ") or in_fence and not lines[j].startswith("```")):
                j+=1
            display=[r"\begin{gather*}"]
            for k in range(i,j):
                formula=lines[k].strip().rstrip(".")
                display.append(math(formula)+(r"\\" if k<j-1 else ""))
            display.append(r"\end{gather*}")
            bound(p,n,j,"\n".join(display),"ascii-display-math"); i=j; continue
        listmatch = re.match(r"(?:[-*]|\d+\.)\s+(.*)",line)
        if listmatch:
            j=i+1
            while j<len(lines) and re.match(r"(?:[-*]|\d+\.)\s+",lines[j]): j+=1
            entries=[r"\begin{itemize}"]
            for k in range(i,j):
                mm=re.match(r"([-*]|\d+\.)\s+(.*)",lines[k]); assert mm
                prefix = mm.group(1)+" " if mm.group(1)[0].isdigit() else ""
                entries.append(r"\item " + prose(prefix+mm.group(2),p))
            entries.append(r"\end{itemize}")
            bound(p,n,j,"\n".join(entries),"markdown-list"); i=j; continue
        formatted=prose(line,p)
        if line.startswith(("Author:","Author/integrator:","Final author revision")):
            formatted=r"\begin{quote}\footnotesize " + formatted + r"\end{quote}"
        bound(p,n,n,formatted,"prose-with-math-typesetting"); i+=1


def row_specification() -> None:
    p=PACKET/"construction/artifacts/candidate214-brox/candidate214-ir.json"
    data=json.loads(p.read_text()); register(p)
    emit(r"\clearpage\section{Complete coordinate and row specification}\label{q214:rows}")
    emit(r"Put $X_1=x$.  The following dictionary lists every coordinate, in the exact IR order.  Its names describe gates; the equations below, rather than a choice of field-component interpretation, define the polynomial.  The last column is the retained raw-$224$ coordinate identifier.  No coordinate is reserved for $A_N$.")
    first=len(OUT)+1
    emit(r"{\small\begin{longtable}{@{}r p{0.77\linewidth} r@{}}\toprule")
    emit(r"$i$ & Coordinate name & Parent\\\midrule\endhead")
    for c in data["coordinates"]:
        emit(str(c["id"])+" & "+literal(c["name"])+" & "+str(c["parent224Id"])+r"\\")
    emit(r"\bottomrule\end{longtable}}")
    SPANS.append({"source":p.relative_to(ROOT).as_posix(),"source_json_pointer":"/coordinates",
                  "tex_lines":[first,len(OUT)],"method":"complete-coordinate-dictionary"})
    emit(r"For $1\le i\le188$, the row below is $r_{i,N}$.  Each term is an exact integer coefficient times a power of $A_N$ and a coordinate monomial.  Long integer coefficients are grouped on separate display lines without abbreviation.  The definition is $P_N=\sum_i r_{i,N}^2$, with weight one on each of these primitive integral rows.  In particular the historical $222$-variable row weights are not imported.")
    for idx,row in enumerate(data["residuals"]):
        first=len(OUT)+1
        emit(r"\paragraph{Row " +str(row["id"])+".} "+literal(row["name"])+r"\nopagebreak")
        emit(r"\begin{equation*}\begin{aligned}r_{"+str(row["id"])+r",N}={}&")
        chunks=[]
        for t in row["terms"]:
            c=int(t["coefficient"]); mag=abs(c); factors=[]
            if mag!=1 or not (t["parameterPower"] or t["monomial"]):
                ds=str(mag)
                if len(ds)>65:
                    # A decimal integer is printed vertically inside one
                    # parenthesized integer via an explicit base-10 block sum.
                    groups=[ds[max(0,len(ds)-50*(j+1)):len(ds)-50*j] for j in range((len(ds)+49)//50)]
                    blocks=[]
                    for k,g in reversed(list(enumerate(groups))):
                        if int(g): blocks.append(str(int(g))+(r"\cdot10^{"+str(50*k)+"}" if k else ""))
                    factors.append(r"\left(\begin{gathered}"+r"\\{}+{}".join(blocks)+r"\end{gathered}\right)")
                else: factors.append(ds)
            if t["parameterPower"]: factors.append("A_N"+("^{"+str(t["parameterPower"])+"}" if t["parameterPower"]!=1 else ""))
            for v,power in sorted(Counter(t["monomial"]).items()):
                factors.append("X_{"+str(v)+"}"+("^{"+str(power)+"}" if power!=1 else ""))
            chunks.append(("-" if c<0 else "+")+" "+r"\,".join(factors))
        # One term per line is readable and keeps the 230-digit source
        # coefficients below the measure.  This does not expand a polynomial.
        for k,term in enumerate(chunks):
            if k==0 and term.startswith("+"): term=term[1:]
            emit(term+(r"\\ &" if k<len(chunks)-1 else ""))
        emit(r"\end{aligned}\end{equation*}")
        SPANS.append({"source":p.relative_to(ROOT).as_posix(),"source_json_pointer":f"/residuals/{idx}",
                      "tex_lines":[first,len(OUT)],"method":"exact-unexpanded-quadratic-row"})
    emit(r"The rows are independently reconstructible from \nolinkurl{research/quartic214/construction/build.py}.  The separate Laurent implementation \nolinkurl{construction/check_exact.py} compares all twenty changed factor components, six inverse-weight relations and $162$ untouched rows, and checks degree, content, coordinate occurrence, coefficient profiles and the complete quartic table.  These are finite algebraic conclusions.  They do not certify the retained arithmetic theorems.")
    for p in [PACKET/"construction/build.py",PACKET/"construction/check_exact.py",
              PACKET/"construction/artifacts/candidate214-brox/STATISTICS.json",
              PACKET/"construction/artifacts/candidate214-brox/candidate214-polynomial.json"]:
        register(p)


def tex_source(p: Path, prefix: str) -> None:
    text=p.read_text(); lines=text.splitlines()
    text=re.sub(r"\\(label|ref|eqref)\{([^}]+)\}",lambda m:"\\"+m[1]+"{"+prefix+m[2]+"}",text)
    text=text.replace(r"\section{",r"\subsection{")
    citations={"Javanpeykar":"v15-height-Javanpeykar","vonKaenel":"v15-height-vonKaenel",
               "Stacks":"v15-height-Stacks","Serre":"v15-height-Serre"}
    for a,b in citations.items(): text=text.replace("{"+a+"}","{"+b+"}")
    text=text.replace(r"~\cite{Logs}",r"~Section~\ref{v15:logs}")
    # These fragments supplement, and are read with, the later exact source
    # application bridges rather than replacing their normalization checks.
    bound(p,1,len(lines),text,"retained-tex; local-label-prefix; headings-demoted; bibliography-key-aliases; Logs-to-v15:logs")


def metadata_catalogue(p: Path) -> None:
    """Render primary-source metadata completely, retaining URLs/hashes/limits."""
    data=json.loads(p.read_text()); first=len(OUT)+1; register(p)
    emit(r"\clearpage\section{Primary-source editions and inspection catalogue}\label{q214:catalogue}")
    emit(r"\begingroup\raggedright")
    emit(r"This catalogue retains the complete primary-source metadata accompanying the author packet.  An inspection statement describes its original named author and date.  It is not an assertion that the typesetter repeated that inspection, nor an independent acceptance of the present manuscript.  External books and PDFs are identified by their editions, locators, URLs and byte hashes; their complete contents are not republished here.")
    def walk(obj, depth=0, name=""):
        if isinstance(obj,dict):
            for k,v in obj.items():
                if isinstance(v,(dict,list)):
                    emit(r"\paragraph{"+escape(k.replace("_"," "))+"}"); walk(v,depth+1,k)
                else:
                    emit(r"\noindent\textbf{"+escape(k)+"}: "+value(v)+r"\par")
        elif isinstance(obj,list):
            for i,v in enumerate(obj):
                if isinstance(v,(dict,list)):
                    emit(r"\medskip\noindent\textbf{"+escape(name)+" entry "+str(i+1)+r".}\par"); walk(v,depth+1,name)
                else: emit(r"\noindent $\bullet$ "+value(v)+r"\par")
    def value(v):
        if isinstance(v,bool): return "true" if v else "false"
        if v is None:return "null"
        s=str(v)
        if re.match(r"https?://",s):return r"\url{"+s.replace("%",r"\%")+"}"
        if re.fullmatch(r"[0-9a-f]{40,64}",s):return code(s)
        # Preserve dense original metadata strings verbatim, but permit line
        # breaks without inserting spaces or visible hyphens into their data.
        chunks=[]; run=0
        for c in s:
            chunks.append(escape(c));run=run+1 if c.isalnum() else 0
            if run==16:chunks.append(r"\allowbreak{}");run=0
        return "".join(chunks)
    walk(data)
    emit(r"\endgroup")
    SPANS.append({"source":p.relative_to(ROOT).as_posix(),"source_lines":[1,len(p.read_text().splitlines())],
                  "tex_lines":[first,len(OUT)],"method":"complete-recursive-primary-source-catalogue"})


def certificate_catalogue() -> None:
    emit(r"\clearpage\section{Finite certificates and exact computational sources}\label{q214:certificates}")
    emit(r"The following files identify finite inputs, methods and conclusions used in Part~I.  Their byte hashes bind the exact public objects.  The links provide the full recoverable certificates or implementations.  Their finite conclusions are distinct from the arithmetic theorem and from review acceptance.")
    records=[
        ("sources/contact-line-certificate.json", "The ten primitive contact lines and their exact determinant support; the geometric proof, rather than these determinants, constructs the cover and its tame charts."),
        ("sources/small-support-certificate.json", "The small exceptional support and exact finite support computations used by the full-family height argument."),
        ("sources/public-provider-scopes.json", "The exact public provider/source scopes used by the geometric and conductor carry arguments; this is source identification, not a fresh approval."),
        ("height/NUMERIC_CERTIFICATE_H4.json", "The rational logarithmic enclosures and strict H4 inequalities, including the exponent 2103/1024 and the bound on C2."),
        ("height/numeric_certificate.py", "The atanh-series rational enclosure method with its proved geometric tail and negative controls for the isolated H4 calculation."),
        ("construction/EXACT-CHECKS.json", "Recorded finite Laurent identities, row occurrence and polynomial-profile checks for the 214 construction."),
        ("construction/check_exact.py", "The separate implementation reconstructing deleted coordinates and comparing every changed and untouched row; it also verifies the full quartic and coefficient profiles."),
        ("construction/build.py", "The deterministic raw224-to214 generator.  It fixes the parameter coefficient, prints the IR and expands the finite sum of squares; the manuscript assembler itself does not run this expansion."),
        ("construction/artifacts/candidate214-brox/candidate214-ir.json", r"The exact 214-coordinate dictionary and 188 primitive integral rows printed in Section \ref{q214:rows}."),
        ("construction/artifacts/candidate214-brox/candidate214-polynomial.json", r"The complete symbolic quartic coefficient table: a term is \(c A_N^a\) times its coordinate multiset monomial, with \(A_N\) a coefficient and no additional coordinate."),
        ("construction/artifacts/candidate214-brox/STATISTICS.json", "The declared finite totals 214,188,2919,2920, degree four, content one and coefficient-only threshold53."),
    ]
    for rel,purpose in records:
        p=PACKET/rel; source=register(p); first=len(OUT)+1
        emit(r"\medskip\noindent\textbf{"+literal(rel)+r"}\par\noindent")
        emit(prose(purpose,p))
        emit(r"\par\noindent SHA-256: "+code(SOURCES[source]["sha256"])+r".\par")
        emit(r"\href{"+WEB+source+r"}{Read the exact public source}.\par")
        SPANS.append({"source":source,"source_json_pointer":"" if p.suffix==".json" else None,
                      "tex_lines":[first,len(OUT)],"method":"linked-certificate-scope-and-whole-file-hash"})


def assemble() -> tuple[bytes,bytes]:
    if digest(V15.read_bytes())!=V15_SHA:raise SystemExit("Frozen V15 provenance source differs")
    register(V15);register(FOUNDATION_PROFILE)
    profile=json.loads(FOUNDATION_PROFILE.read_text())
    if profile["tex"]["sha256"]!=FOUNDATION_SHA or profile["version"]!=16:
        raise SystemExit("Current foundation profile changed; source transition needs review")
    raw=FOUNDATION.read_bytes()
    if digest(raw)!=FOUNDATION_SHA: raise SystemExit("Current foundation source hash differs; refusing reconstruction")
    source=raw.decode(); vlines=source.splitlines()
    docline=next(i for i,l in enumerate(vlines) if l==r"\begin{document}")
    # Keep the complete package/macro preamble, replacing only publication
    # metadata.  The raw source hash is bound independently above.
    preamble="\n".join(vlines[:docline])
    preamble=re.sub(r"\\title\{.*?\}\n\\author\{\}\n\\date\{[^}]*\}",
        lambda m:r"\title{A 214-variable quartic family defining the integers over the rationals\\[4pt]\large Complete proposed proof with the current Version 16 foundation}"+"\n"+r"\author{Public author manuscript under the direction of Elliot Glazer}"+"\n"+r"\date{12 November 2026; frozen 214 source \texttt{110cf72565be}}",preamble,flags=re.S)
    emit(r"\PassOptionsToPackage{hypertexnames=false}{hyperref}")
    bound(FOUNDATION,1,docline,preamble,"exact-preamble-except-title-author-date; line-endings-LF")
    emit(r"\ifdefined\pdftrailerid\pdftrailerid{}\fi")
    emit(r"\usepackage{graphicx}")
    emit(r"\hypersetup{pdftitle={The proposed 214-variable quartic family: complete proof and retained foundation},pdfauthor={Elliot Glazer and attributed contributors},bookmarksnumbered=true}")
    emit(r"\setcounter{tocdepth}{2}\setcounter{secnumdepth}{3}")
    emit(r"\allowdisplaybreaks[1]")
    emit(r"\makeatletter\g@addto@macro\UrlBreaks{\do\a\do\b\do\c\do\d\do\e\do\f\do\0\do\1\do\2\do\3\do\4\do\5\do\6\do\7\do\8\do\9}\makeatother")
    emit(r"\begin{document}")
    emit(r"\renewcommand{\thesection}{I.\arabic{section}}")
    emit(r"\renewcommand{\theHsection}{q214.\arabic{section}}")
    intro=HERE/"introduction.tex"
    bound(intro,1,len(intro.read_text().splitlines()),intro.read_text(),"authored-introduction-verbatim")
    row_specification()
    markdown(ROOT/"research/quartic214-manuscript-review/FOUNDATION_TRANSITION.md","foundation-transition")
    markdown(PACKET/"PROOF.md","assembly")
    order=["existence","uniform-existence","geometry-carry","provider-scope-carry","modularity",
           "height-evaluation","height-different","height-metric","height-assembly",
           "height-supplier","height-averaging","primary-source-bridges","source-carry"]
    for stem in order:
        notice=""
        if stem=="height-supplier":
            notice=r"\textbf{Current application:} H0--H2 and H4 are consumed with the product averaging proof in Section~\ref{q214:height-averaging}.  The historical H3 quotient-filtration route is retained only as superseded evidence and is not used in this edition's 214 argument."
        if stem in {"uniform-existence","source-carry"}:
            notice=r"\textbf{Current foundation overlay:} The Version~15 byte-identity and no-new-repair statements in this dated source describe its historical freeze.  This edition instead incorporates the complete current Version~16 foundation and the explicit source-to-consumer transition in Section~\ref{q214:foundation-transition}.  The historical text is retained as evidence; it does not negate or independently accept that changed application."
        markdown(PACKET/"proofs"/(stem+".md"),stem,notice)
    emit(r"\clearpage\section{Retained selected source proofs}\label{q214:selected}")
    emit(r"These mathematical fragments are reproduced in full at the selected public ranges.  Their original coarse character/conductor route is retained as historical source evidence; M1 and M5 in Section~\ref{q214:modularity} supply the current character and conductor comparison.  The evaluation fragments are read together with the exact lattice, different and metric bridges above.  Historical source qualifications remain visible; no new acceptance is inferred from their inclusion.")
    for stem in ["support-section1","conductor-sections1-3","aggregate-bridge"]:
        markdown(PACKET/"sources"/(stem+".md"),"source-"+stem)
    emit(r"\section{Retained differential-evaluation proof}\label{q214:eval-source}")
    tex_source(PACKET/"sources/evaluation-sections1-4.tex","q214src:eval:")
    emit(r"\section{Retained changed-factor extraction proof}\label{q214:factor-source}")
    tex_source(PACKET/"sources/factor-extraction.tex","q214src:factor:")
    markdown(ROOT/"research/version15/quartics/quartic-222/provenance/shared-T-redundancy224-006/PROOF.md","raw224-source")
    certificate_catalogue()
    metadata_catalogue(PACKET/"PRIMARY_SOURCES.json")
    emit(r"\clearpage\section{Public-source resolution and reproducibility}\label{q214:resolution}")
    emit(r"The historical path names in the retained author proofs are provenance locators.  The complete mathematical foundation they identify is present in Part~II, and the selected later proofs are present in Part~I.  The public reading aliases below resolve the retained historical locators; none requires private-repository access.  Exact file and passage bindings for the source packet remain in \nolinkurl{research/quartic214/SOURCE_PATH_MAP.json} and the application contracts.  They are not rewritten into current acceptance for this new manuscript.")
    aliases_path=PACKET/"SOURCE_PATH_MAP.json"; register(aliases_path)
    mapping=json.loads(aliases_path.read_text())
    aliases=mapping.get("reading_aliases",{})
    first=len(OUT)+1
    emit(r"\begin{description}[style=nextline]")
    if isinstance(aliases,dict):
        for k,v in aliases.items(): emit(r"\item["+code(k)+"] "+code(v) if isinstance(v,str) else r"\item["+code(k)+"] "+escape(json.dumps(v,ensure_ascii=False)))
    else:
        for v in aliases: emit(r"\item "+escape(json.dumps(v,ensure_ascii=False)))
    emit(r"\end{description}")
    SPANS.append({"source":aliases_path.relative_to(ROOT).as_posix(),"source_json_pointer":"/reading_aliases","tex_lines":[first,len(OUT)],"method":"public-reading-alias-catalogue"})
    emit(r"\paragraph{Rebuilding this edition.} Run \nolinkurl{python3 -B research/quartic214-manuscript/assemble.py} from the repository root.  It reads bounded source files, emits this single TeX source and \nolinkurl{SOURCE_SPANS.json}, and performs no polynomial expansion or TeX build.  Its \nolinkurl{--check} mode verifies byte-for-byte deterministic output.  The separate PDF build and release metadata record the exact generated-source hash, toolchain and PDF hash.  Source mapping and successful compilation concern serialization, not arithmetic acceptance.")
    emit(r"\clearpage\part{The complete current Version 16 mathematical foundation}")
    emit(r"\begin{quote}\small\textbf{Scope of retained foundation.} The following is the entire mathematical body of the current upstream Version~16 source (SHA-256 \nolinkurl{"+FOUNDATION_SHA+r"}), selected by \nolinkurl{docs/current-manuscript.json}.  Its original abstract, theorem statements, proofs, bibliography and historical provenance are retained, including the GI, Gaudron--R\'emond citation and Tao--Ziegler corrections identified in Section~\ref{q214:foundation-transition}.  Assertions about $222$, $314$ and earlier variable counts refer to those constructions.  They do not replace the $214$ row specification in Part~I.  Historical review and incorporation statements belong to that upstream edition; they do not accept the newly assembled 214 manuscript.  Section, theorem, equation and cross-reference numbering in this part is restored to its original convention.\end{quote}")
    emit(r"\setcounter{section}{0}\setcounter{subsection}{0}\setcounter{equation}{0}\setcounter{theorem}{0}")
    emit(r"\renewcommand{\thesection}{\arabic{section}}\renewcommand{\theHsection}{foundation.\arabic{section}}")
    emit(r"\renewcommand{\theHequation}{foundation.\arabic{equation}}")
    # The original maketitle and toc are publication wrappers.  Retain the
    # complete original abstract and every body line through enddocument.
    body_start=docline+2
    assert vlines[docline+1]==r"\maketitle"
    toc=next(i for i in range(body_start,len(vlines)) if vlines[i]==r"\tableofcontents")
    bound(FOUNDATION,body_start+1,toc,"\n".join(vlines[body_start:toc]),"exact-retained-body-LF")
    emit("% Original second table of contents omitted; unified navigation precedes Part I.")
    end=next(i for i in range(toc+1,len(vlines)) if vlines[i]==r"\end{document}")
    anchors={
        r"\subsection{Removing rational and small coordinates without losing unit norm}":"q214foundation:gi-normalization",
        "The map from the remaining universal group must now land in the covering":"q214foundation:gi-cover",
        "We now adapt the arbitrary-function dense-model argument of":"q214foundation:tz-adaptation",
        r"\subsection{An abelian surface occurring as an isogeny factor}":"q214foundation:cmh-surface",
    }
    cursor=toc+1
    for index,line in enumerate(vlines):
        if line not in anchors or not (toc<index<end):continue
        if cursor<index:
            bound(FOUNDATION,cursor+1,index,"\n".join(vlines[cursor:index]),"exact-retained-body-LF")
        emit(r"\phantomsection\label{"+anchors[line]+"}")
        cursor=index
    if cursor<end:
        bound(FOUNDATION,cursor+1,end,"\n".join(vlines[cursor:end]),"exact-retained-body-LF")
    for line in anchors:
        if vlines.count(line)!=1:raise SystemExit("Current foundation anchor absent/ambiguous: "+line)
    emit(r"\end{document}")
    tex=("\n".join(OUT)+"\n").encode()
    manifest={"schema":"quartic214-manuscript-source-spans-v1","frozen_packet_commit":FROZEN,
              "review_status":"author serialization; no independent manuscript or Protocol D approval generated",
              "output":"research/quartic214-manuscript/quartic214.tex","output_sha256":digest(tex),
              "sources":SOURCES,"spans":SPANS,
              "foundation":{"profile":FOUNDATION_PROFILE.relative_to(ROOT).as_posix(),"source":FOUNDATION.relative_to(ROOT).as_posix(),"sha256":FOUNDATION_SHA,"version":16,"role":"current upstream foundation, not a new numbered 214 release"},
              "presentation_rules":["Exact current V16 body retained with LF line endings; old maketitle and duplicate toc replaced by unified front matter. V15 remains provenance; current transition is explicit.",
                "Part I ASCII formulas typeset as TeX; all Markdown source lines mapped, including metadata and blank lines.",
                "Selected TeX labels/references namespaced, headings demoted and bibliography keys matched to retained bibliography.",
                "Historical Logs citation resolves to retained V15 section v15:logs; no source theorem is substituted.",
                "Bare ASCII Q/Z and stars retain source notation; no global field-font or multiplication inference is made.",
                "Source-local Sigma means summation only in height-different.md,height-metric.md,aggregate-bridge.md; elsewhere it remains Sigma.",
                "The aggregate F+ is typeset F_{+} in uniform-existence.md and aggregate-bridge.md.",
                "Metric-source p*omega,bar-eta,dbar-t denote p_*omega,overline eta,d overline t as fixed by the stated model/metric.",
                "P1 denotes the target projective line in height-evaluation.md,height-different.md and metric P1_t; cohomology H0(...) is typeset H^0(...).",
                "hypertexnames=false supplies unique generated PDF destinations without changing printed numbers or the retained mathematical body; pdfTeX trailer ID is suppressed for deterministic builds.",
                "Four separate phantomsection labels locate current GI normalization, GI cover lifts, TZ adaptation and CMH surface passages; exact source blocks concatenate to the complete original mathematical body.",
                "All 214 coordinates and188 unexpanded residual rows printed directly from exact IR.",
                "All coordinate and residual metadata names are literal code identifiers; the source-local H3 product uses times and mathematical prose connectors retain visible word spaces.",
                "The two multi-line code-math spans in height-supplier.md are complete displays, retaining the H1.3 tag and the superseded H3 context; explicit Greek function/index/signed-atom notation is selected as math.",
                "Long decimal row coefficients expressed as exact base10 block sums without approximation.",
                "Historical H3 is explicitly superseded by operative product averaging; historical coarse conductor is superseded by M1/M5."]}
    return tex,(json.dumps(manifest,indent=2,ensure_ascii=False,sort_keys=True)+"\n").encode()


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument("--check",action="store_true")
    args=parser.parse_args(); tex,mapping=assemble()
    outputs={HERE/"quartic214.tex":tex,HERE/"SOURCE_SPANS.json":mapping}
    for p,data in outputs.items():
        if args.check:
            if not p.exists() or p.read_bytes()!=data: raise SystemExit("stale generated file: "+str(p))
        else: p.write_bytes(data)
    print("PASS: deterministic manuscript serialization" if args.check else "Wrote quartic214.tex and SOURCE_SPANS.json")


if __name__=="__main__": main()
