import sys, re
log = open(sys.argv[1], encoding='utf-8', errors='replace').read().split('\n')
cur = None; errs = {}
for l in log:
    m = re.match(r'^✖ \[\d+/\d+\] Building (\S+)', l)
    if m: cur = m.group(1).split('.')[-1]; errs.setdefault(cur, []); continue
    m = re.match(r'^error: (\S+?\.lean):(\d+):(\d+): (.*)', l)
    if m: errs.setdefault(m.group(1).split('/')[-1][:-5], []).append(m.group(2) + ': ' + m.group(4)[:160])
    elif l.startswith('error:') and cur: errs[cur].append(l[:200])
for k, v in errs.items():
    print('==', k, len(v))
    for e in v[:int(sys.argv[2]) if len(sys.argv) > 2 else 4]: print('   ', e)
