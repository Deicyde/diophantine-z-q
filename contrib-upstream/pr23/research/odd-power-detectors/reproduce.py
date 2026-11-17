"""Reproduce uniform odd-power detectors: 376 variables, 425 digits."""
from pathlib import Path
import argparse, importlib.util, json, sys

HERE=Path(__file__).resolve().parent
ROW=HERE.parent/'scalar-row-reduction'
sys.path.insert(0,str(ROW))
spec=importlib.util.spec_from_file_location('row_replay',ROW/'reproduce.py')
lib=importlib.util.module_from_spec(spec);spec.loader.exec_module(lib)
from power_patch import transform as power


def builder():return power(lib.rows(lib.parent_builder()))


def main():
    if not __debug__:raise RuntimeError('Verification requires Python assertions')
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    lib.check_bindings(HERE);out=a.output.resolve()
    assert not out.exists() or not any(out.iterdir())
    assert lib.REPO/'research' not in out.parents
    lib.write_builder(out/'baseline',lib.rows(lib.parent_builder()))
    lib.write_builder(out,builder())
    lib.run(out,sys.executable,'-B',HERE/'check_power.py',out/'baseline/raw-translated-ir.json',out/'raw-translated-ir.json','--report',out/'power-check.json')
    expected=json.loads((HERE/'EXPECTED.json').read_text())
    result=lib.finish(out,HERE/'DIAGONAL_WEIGHTS.json',expected)
    assert json.loads((out/'power-check.json').read_text())['status']=='PASS'
    result['files']['power-check.json']=lib.digest(out/'power-check.json')
    lib.check_bindings(HERE)
    (out/'MEASURED.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result['summary'],indent=2),flush=True)


if __name__=='__main__':main()
