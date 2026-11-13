#!/usr/bin/env python3
"""For a Tau Ceti module X vendored at oct16, write Backport/X.lean = main version of X with every
declaration whose name already occurs in the vendored file removed (structure lines kept).
usage: extras.py MODULE [BPLIST]"""
import os, re, subprocess, sys
src = os.path.expanduser('~/tc-main')
sha = subprocess.run(['git','-C',src,'rev-parse','HEAD'],capture_output=True,text=True).stdout.strip()
m = sys.argv[1]
bp = set(l.strip() for l in open(sys.argv[2])) if len(sys.argv) > 2 else set()
parts = m.split('.')
main = open(os.path.join(src, *parts) + '.lean', encoding='utf-8').read()
vend_path = os.path.join('ZInQKernel/Contrib', *parts) + '.lean'
vend = open(vend_path, encoding='utf-8').read()
declre = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|scoped|local)\s+)*(theorem|lemma|def|abbrev|instance|structure|class|alias|irreducible_def|inductive)\s+([^\s:({\[]+)?', re.M)
def names(txt):
    return set(mm.group(2) for mm in declre.finditer(txt) if mm.group(2))
vn = names(vend)
lines = main.split('\n')
# header: up to and including the module docstring end; we rebuild imports
starts = re.compile(r'^(@\[|/--|theorem |lemma |def |abbrev |instance |structure |class |alias |private |protected |noncomputable |nonrec |scoped |irreducible_def |inductive |attribute |set_option .* in$|open .* in$|variable .* in$|omit .* in$|include .* in$)')
struct = re.compile(r'^(section|namespace|end|variable|open|universe|/-!|set_option|noncomputable section|public section|@\[expose\] public section|include|omit|#|local notation|notation|scoped notation|suppress_compilation|module$|public import|import)')
out = []; chunk = []; kind = None
def flush():
    global chunk
    if chunk:
        txt = '\n'.join(chunk)
        mm = declre.search(txt)
        nm = mm.group(2) if mm else None
        drop = False
        if mm and nm and nm in vn: drop = True
        if mm and not nm and txt.strip() in vend: drop = True
        if not drop: out.append(txt)
        else: out.append(f'-- (omitted: `{nm}`, already in the vendored module)')
    chunk = []
pending_prefix = []
i = 0
in_block_comment = False
while i < len(lines):
    l = lines[i]
    if chunk and (starts.match(l) or struct.match(l)) and not (chunk and chunk[-1].rstrip().endswith(' in') ) and not (chunk and all(c.startswith(('/--','@[')) or c.startswith(' ') for c in chunk) and not declre.search('\n'.join(chunk))):
        flush()
    if not chunk and struct.match(l) and not starts.match(l):
        # structural line (may be a multi-line /-! comment)
        if l.startswith('/-!'):
            while '-/' not in lines[i]:
                out.append(lines[i]); i += 1
            out.append(lines[i]); i += 1; continue
        out.append(l); i += 1; continue
    if not chunk and not starts.match(l):
        out.append(l); i += 1; continue
    chunk.append(l); i += 1
flush()
txt = '\n'.join(out)
for _ in range(3):
    txt = re.sub(r'/--(?:(?!-/).)*?-/\n(?:--(?! \(omitted)[^\n]*\n)*(?=-- \(omitted)', '', txt, flags=re.S)
    txt = re.sub(r'(?:@\[[^\]\n]*\]\n)?(?:variable [^\n]* in|omit [^\n]* in|include [^\n]* in|set_option [^\n]* in)\n(?=-- \(omitted)', '', txt)
# imports: add vendored module as public import
imp = re.compile(r'^(\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?)(TauCeti\.\S+)', re.M)
def rw(mm):
    x = mm.group(2)
    if x in bp: return mm.group(1) + 'ZInQKernel.Contrib.TauCeti.Backport.' + x[len('TauCeti.'):]
    return mm.group(1) + 'ZInQKernel.Contrib.' + x
txt = imp.sub(rw, txt)
txt = txt.replace('\nmodule\n', '\nmodule\n\npublic import ZInQKernel.Contrib.' + m + '\n', 1)
note = (f'-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit {sha[:12]}, module\n'
        f'-- {m}), Apache-2.0: declarations of that module absent from its commit-5a01f5fe version, which\n'
        f'-- is vendored as `ZInQKernel.Contrib.{m}` (task t40-tate).\n'
        f'-- Modified for the Z-in-Q kernel: declarations already in the vendored module removed; imports rewritten.\n')
k = txt.find('-/\n'); txt = txt[:k+3] + note + txt[k+3:]
d = os.path.join('ZInQKernel/Contrib/TauCeti/Backport', *parts[1:]) + '.lean'
os.makedirs(os.path.dirname(d), exist_ok=True)
open(d, 'w', encoding='utf-8').write(txt)
print(d, 'kept', len([1 for o in out if not o.startswith('-- (omitted')]), 'omitted', sum(1 for o in out if o.startswith('-- (omitted')))
