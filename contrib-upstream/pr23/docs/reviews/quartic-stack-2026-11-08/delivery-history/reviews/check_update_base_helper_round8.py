"""Focused independent behavioral review of the exact-old-overlay helper.

Runs a valid control and four targeted rejection cases on private copies of the
frozen prior112-file overlay. The supplied helper and delivered sources are read
only; every tested checkout is checked for mutation by the helper.
"""
from pathlib import Path
import argparse
import ast
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def snapshot(root):
    result={}
    for p in sorted(root.rglob('*')):
        name=p.relative_to(root).as_posix()
        if p.is_symlink():
            result[name]={'type':'symlink','target':str(p.readlink())}
        elif p.is_file():
            result[name]={'type':'file','sha256':digest(p),'bytes':p.stat().st_size}
        elif p.is_dir():
            result[name]={'type':'directory'}
        else:
            raise AssertionError('Unexpected probe filesystem object '+str(p))
    return result


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--helper',type=Path,required=True)
    parser.add_argument('--baseline',type=Path,required=True)
    parser.add_argument('--work-root',type=Path,required=True)
    parser.add_argument('--report',type=Path,required=True)
    args=parser.parse_args()
    helper=args.helper.resolve();baseline=args.baseline.resolve()
    manifest=baseline/'SOURCE_MANIFEST.json'
    expected='f2d74ebd40b61a48b1b3d1ecdb55d2fda53f372a090fce8ec1fcd347e333bbd5'
    assert digest(manifest)==expected
    model=json.loads(manifest.read_text())
    assert len(model['files'])==111
    assert len([p for p in baseline.rglob('*') if p.is_file()])==112
    for item in model['files']:
        p=baseline/item['path']
        assert p.stat().st_size==item['bytes'] and digest(p)==item['sha256']
    constants={}
    for node in ast.parse(helper.read_text()).body:
        if isinstance(node,ast.Assign):
            for target in node.targets:
                if isinstance(target,ast.Name):
                    try:constants[target.id]=ast.literal_eval(node.value)
                    except (ValueError,TypeError):pass
    assert constants['EXPECTED']==expected
    helper_sha=digest(helper)
    original_snapshot=snapshot(baseline)
    args.work_root.mkdir(parents=True,exist_ok=True)
    root=Path(tempfile.mkdtemp(prefix='update-base-review-',dir=args.work_root.resolve()))
    results=[]
    cases=[
      ('valid',None,'PASS: exact previous392-variable overlay'),
      ('wrong_manifest','manifest','FAIL: This is not the exact previous392-variable manifest'),
      ('changed_source','source','FAIL: Changed previous file: construction/builder.cjs'),
      ('extra_file','extra','FAIL: The previous overlay has missing or extra files'),
      ('symlink_source','symlink','FAIL: Unexpected symbolic link: construction/builder.cjs'),
    ]
    for name,mutation,expected_message in cases:
        checkout=root/name
        overlay=checkout/'research/conditional-quartic-reduction'
        shutil.copytree(baseline,overlay)
        sentinel=checkout/'UNRELATED_SENTINEL.txt'
        sentinel.write_text('Independent outside-overlay preservation sentinel.\n')
        if mutation=='manifest':
            p=overlay/'SOURCE_MANIFEST.json';p.write_bytes(p.read_bytes()+b'\n')
        elif mutation=='source':
            p=overlay/'construction/builder.cjs';p.write_bytes(p.read_bytes()+b'\n// controlled review mutation\n')
        elif mutation=='extra':
            (overlay/'review-extra-file.txt').write_text('A deliberately unlisted file.\n')
        elif mutation=='symlink':
            p=overlay/'construction/builder.cjs'
            target=checkout/'outside-builder-copy.cjs'
            target.write_bytes(p.read_bytes());p.unlink();p.symlink_to(target)
        before=snapshot(checkout)
        completed=subprocess.run([sys.executable,'-B',str(helper),str(checkout)],text=True,capture_output=True,timeout=20)
        combined=completed.stdout+completed.stderr
        # Ignore spacing differences only in the expected diagnostic text.
        assert expected_message.replace(' ','') in combined.replace(' ',''),(name,combined)
        assert (completed.returncode==0)==(mutation is None),(name,completed.returncode)
        after=snapshot(checkout)
        assert before==after,'Helper modified its input during '+name
        results.append({'case':name,'exitCode':completed.returncode,'stdout':completed.stdout,'stderr':completed.stderr,'checkoutUnchanged':True,'unrelatedSentinelSha256':digest(sentinel)})
    assert snapshot(baseline)==original_snapshot
    assert digest(helper)==helper_sha
    report={'status':'PASS','helperPath':str(helper),'helperSha256':helper_sha,'baselineManifestSha256':expected,'baselineFiles':112,'baselineManifestEntries':111,'cases':results,'allFiveCheckoutsUnchanged':True,'frozenBaselineUnchanged':True,'probeDirectory':str(root),'checkerSha256':digest(Path(__file__)),'scope':'One valid control and four focused rejection cases. Read-only helper review; no patch application or global arithmetic verification is claimed here.'}
    args.report.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ['cases']},indent=2))
    for r in results:print(r['case'],r['exitCode'],(r['stdout']+r['stderr']).splitlines()[0])


if __name__=='__main__':
    main()
