"""Compare each vendored module of the c5-deligne-serre branch with the vendored copies already in the tree.
A pair is 'identical' when the texts agree after (a) stripping the leading /- ... -/ provenance header and
(b) replacing every 'ZInQKernel.Contrib.<...>.Vendor.AnthropicFLT.' prefix with 'V.'.
Usage: python3 dupscan.py REF  (run from the repo root; reads the branch via git, the tree from the worktree)."""
import subprocess, sys, re, os, glob, json
ref = sys.argv[1]
PFX = re.compile(r'ZInQKernel\.Contrib\.[A-Za-z0-9_.]*?\.Vendor\.AnthropicFLT\.')
def norm(s):
    s = re.sub(r'\A\s*/-.*?-/\s*', '', s, count=1, flags=re.S)
    s = PFX.sub('V.', s)
    return '\n'.join(l.rstrip() for l in s.strip().split('\n'))
existing = {}
for f in glob.glob('ZInQKernel/**/Vendor/AnthropicFLT/**/*.lean', recursive=True):
    up = f.split('/Vendor/AnthropicFLT/')[1][:-5].replace('/', '.')
    existing.setdefault(up, []).append((f, norm(open(f).read())))
files = [l for l in subprocess.run(['git', 'ls-tree', '-r', '--name-only', ref, 'ZInQKernel/Contrib/CloudB3SC5DeligneSerre/Vendor'], capture_output=True, text=True).stdout.split('\n') if l.endswith('.lean')]
# batch read
p = subprocess.run(['git', 'cat-file', '--batch'], input='\n'.join(f'{ref}:{f}' for f in files).encode() + b'\n', capture_output=True)
data = p.stdout; pos = 0; texts = {}
for f in files:
    nl = data.index(b'\n', pos); hdr = data[pos:nl].split(); size = int(hdr[2])
    texts[f] = data[nl+1:nl+1+size].decode(); pos = nl + 1 + size + 1
same, differ, new = {}, {}, []
for f in files:
    up = f.split('/Vendor/AnthropicFLT/')[1][:-5].replace('/', '.')
    if up not in existing: new.append(up); continue
    n = norm(texts[f]); hits = [e for e, t in existing[up] if t == n]
    if hits: same[up] = hits
    else: differ[up] = [e for e, _ in existing[up]]
print('branch vendored modules', len(files)); print('upstream name not in tree', len(new))
print('identical to an existing copy', len(same)); print('same upstream name, text differs', len(differ))
json.dump({'same': same, 'differ': differ, 'new': new}, open('/tmp/fds-dupscan.json', 'w'), indent=1)
