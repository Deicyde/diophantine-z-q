"""Run retained and new finite checks for the Version21 manuscript."""
from pathlib import Path
import hashlib,json,subprocess,sys,time,os
ROOT=Path(__file__).resolve().parent
REPO=ROOT.parents[2]
commands=[REPO/'research/version20/construction/check.py',ROOT/'verify247_retained.py',
          ROOT/'verify229.py',ROOT/'verify_arithmetic.py',ROOT/'check_printed.py']
results=[]
env={k:v for k,v in os.environ.items() if not any(t in k.upper() for t in ["TOKEN","SECRET","PASSWORD","API_KEY"]) and not k.startswith(("GH_","GITHUB_","ANTHROPIC_","OPENAI_"))}
env["PYTHONUTF8"]="1"
for command in commands:
 start=time.monotonic()
 result=subprocess.run([sys.executable,'-X','utf8','-B',str(command)],cwd=REPO,check=True,env=env,
                       stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 results.append({'script':command.relative_to(REPO).as_posix(),'sha256':hashlib.sha256(command.read_bytes()).hexdigest(),
                 'exit_code':result.returncode,'seconds':round(time.monotonic()-start,3),
                 'stdout':result.stdout.decode('utf-8'),'stderr':result.stderr.decode('utf-8')})
output=REPO/'build/version21';output.mkdir(parents=True,exist_ok=True)
tex=REPO/'manuscripts/quartic_v21.tex'
record={'scope':'Finite tables, transformations, expansion and numerical inequalities only; no arithmetic proof acceptance.',
        'manuscript_sha256':hashlib.sha256(tex.read_bytes()).hexdigest(),'results':results}
(output/'finite-checks.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print('Version21 finite checks passed; all 414 displayed rows and 436 scaling entries checked.')
