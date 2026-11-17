import json,subprocess,sys,shutil
from pathlib import Path
HERE=Path(__file__).resolve().parent
def measure(name, src):
    d=HERE/'runs'/name
    if d.exists(): shutil.rmtree(d)
    d.mkdir(parents=True)
    (d/'builder.cjs').write_text(src)
    with (d/'run.log').open('w') as log:
        subprocess.run(['node',str(d/'builder.cjs')],check=True,stdout=log,stderr=subprocess.STDOUT)
        subprocess.run([sys.executable,'-B',str(HERE/'construction/tools/compile_ir.py'),str(d/'raw-translated-ir.json'),str(d/'compiled')],check=True,stdout=log,stderr=subprocess.STDOUT)
    rep=json.loads((d/'compiled/compiler-report.json').read_text())
    raw=json.loads((d/'raw-translated-ir.json').read_text())['counts']
    return raw['coordinates'], rep['final']['coordinates'], rep['final']['residuals'], rep['reduction']['eliminations'], rep.get('omittedFreeCoordinateIds')
if __name__=='__main__':
    print(measure(sys.argv[1], Path(sys.argv[2]).read_text()))
