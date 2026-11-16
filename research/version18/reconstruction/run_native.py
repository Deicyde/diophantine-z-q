"""Run inspected deterministic package code only, in the private copied package.

The sole platform adaptation fixes Path.write_text's newline to LF, so a
Windows reproduction has the same bytes as the supplied Linux JSON artifacts.
No mathematical source or input file is edited.
"""
from pathlib import Path
from contextlib import redirect_stdout,redirect_stderr
from hashlib import sha256
import json,runpy,sys,traceback

HERE=Path(__file__).resolve().parent
PACKAGE=HERE/'native-package'
FROZEN=HERE.parents[1]/'v18-198-dependency-inventory-20261114/package/H10-quartic198'
# HERE.parents[1] is work; all reads/writes below are task-local.
assert PACKAGE.is_dir() and FROZEN.is_dir()
original_write=Path.write_text
def lf_write(self,data,encoding=None,errors=None,newline=None):
    return original_write(self,data,encoding=encoding or 'utf-8',errors=errors,newline='\n')
Path.write_text=lf_write
scripts=['build_affine200.py','check_affine200.py','build_inverse198.py',
         'check_inverse198.py','balance_inverse198.py','check_balanced198.py']
report={'python':sys.version,'newline_adaptation':'Path.write_text forced LF only', 'scripts':[]}
for script in scripts:
    path=PACKAGE/'circuits'/script
    log=HERE/(script+'.log')
    entry={'script':script,'script_sha256':sha256(path.read_bytes()).hexdigest()}
    try:
        with log.open('w',encoding='utf-8',newline='\n') as out,redirect_stdout(out),redirect_stderr(out):
            runpy.run_path(str(path),run_name='__main__')
        entry['status']='PASS'
    except Exception:
        entry['status']='FAIL';entry['traceback']=traceback.format_exc()
        report['scripts'].append(entry)
        (HERE/'native-reproduction.json').write_text(json.dumps(report,indent=2)+'\n')
        raise
    report['scripts'].append(entry)
for directory in ['affine200','inverse198']:
    names=['quadratic.json','polynomial.json']
    if directory=='inverse198':names+=['balanced-quadratic.json','balanced-polynomial.json']
    for name in names:
        rel=Path('circuits')/directory/name
        before,after=(FROZEN/rel).read_bytes(),(PACKAGE/rel).read_bytes()
        assert before==after,rel
        report.setdefault('identical_rebuilt_artifacts',[]).append({'path':str(rel),'sha256':sha256(after).hexdigest()})
report['status']='PASS'
(HERE/'native-reproduction.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
