import subprocess, re, sys, json, os
os.chdir(sys.argv[1])
files = subprocess.check_output(['git','ls-files','ZInQKernel','ZInQKernel.lean']).decode().split()
files = [f for f in files if f.endswith('.lean')]
mod = {f: f[:-5].replace('/','.') for f in files}
imp = {}
for f in files:
    ims=[]
    with open(f, encoding='utf-8') as h:
        for line in h:
            s=line.strip()
            m=re.match(r'^(?:public\s+)?(?:meta\s+)?import\s+(.*)$', s)
            if m:
                ims += m.group(1).split()
            elif s and not s.startswith('--') and not s.startswith('module') and not s.startswith('prelude') and not s.startswith('/-') and not s.startswith('import'):
                # stop at first non-import content (crude)
                if not s.startswith('public') : break
    imp[mod[f]] = [i for i in ims if i.startswith('ZInQKernel')]
json.dump({'mod':mod,'imp':imp}, open(sys.argv[2],'w'))
print(len(imp))
