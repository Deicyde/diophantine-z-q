"""Tiny driver for the Lean REPL: python repl.py header.lean cmd1.lean [cmd2.lean ...]
header is sent once (env 0); each cmd file is run in env 0. At most 9 cmds per session."""
import json, subprocess, sys, os
args = sys.argv[1:]
assert 1 <= len(args) <= 10
p = subprocess.Popen(['lake', 'env', 'repl'], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                     text=True, cwd='.')
def send(obj):
    p.stdin.write(json.dumps(obj) + '\n\n'); p.stdin.flush()
    lines = []
    while True:
        l = p.stdout.readline()
        if l == '' : break
        if l.strip() == '' and lines: break
        lines.append(l)
    return json.loads(''.join(lines)) if lines else None
r = send({'cmd': open(args[0]).read()})
msgs = [m for m in (r or {}).get('messages', []) if m['severity'] == 'error']
print('HEADER env', (r or {}).get('env'), 'errors:', msgs[:3])
for f in args[1:]:
    r = send({'cmd': open(f).read(), 'env': 0})
    print('=====', f)
    for m in (r or {}).get('messages', []):
        if m['severity'] in ('error',) or 'sorry' in m['data']:
            print(m['severity'], m['pos'], m['data'][:1500])
    if r and not any(m['severity']=='error' for m in r.get('messages', [])):
        print('OK')
p.stdin.close(); p.wait()
