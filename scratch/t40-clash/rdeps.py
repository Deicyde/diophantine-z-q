# Reverse transitive import closure of a module over the git-tracked ZInQKernel/*.lean files.
import subprocess, re, sys
files = subprocess.run(['git','ls-files','ZInQKernel/*.lean','ZInQKernel.lean'],capture_output=True,text=True).stdout.split()
imp = {}
for f in files:
    m = f[:-5].replace('/','.')
    imp[m] = set(re.findall(r'^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)', open(f).read(), re.M))
targets = set(sys.argv[1:]); changed = True
while changed:
    changed = False
    for m, s in imp.items():
        if m not in targets and s & targets:
            targets.add(m); changed = True
for t in sorted(targets): print(t)
