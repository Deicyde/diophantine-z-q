"""Focused tests of the shipped pipeline journal and stage-completion contract.

Only imports, assignments and function definitions before the first stage are
loaded from the reviewed pipeline. No mathematical construction is executed.
"""
from pathlib import Path
import argparse
import ast
import hashlib
import json
import subprocess
import sys
import tempfile


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('pipeline', type=Path)
    parser.add_argument('--expected', type=Path)
    parser.add_argument('--workdir', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    args.workdir.mkdir(parents=True, exist_ok=True)
    session = Path(tempfile.mkdtemp(prefix='helpers-', dir=args.workdir.resolve()))
    tree = ast.parse(args.pipeline.read_text(), filename=str(args.pipeline))
    checks = []

    def check(name, condition):
        checks.append({'check':name,'passed':bool(condition)})
        if not condition:
            raise AssertionError(name)

    def call_named(node, name):
        return (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and
                isinstance(node.value.func, ast.Name) and node.value.func.id == name)

    first_stage = next(i for i,n in enumerate(tree.body) if call_named(n,'run'))
    prefix = ast.Module(body=tree.body[:first_stage], type_ignores=[])
    namespace = {'__file__':str(args.pipeline.resolve()),'__name__':'reviewed_pipeline_prefix'}
    exec(compile(prefix,str(args.pipeline),'exec'),namespace)
    here = session/'construction'
    here.mkdir()
    namespace['HERE'] = here
    namespace['PACKAGE'] = session
    namespace['completed_stages'] = []
    run = namespace['run']
    atomic_json = namespace['atomic_json']

    run('first',sys.executable,'-c','raise SystemExit(0)')
    progress = json.loads((session/'pipeline-progress.json').read_text())
    check('successful stage appended exactly once',namespace['completed_stages']==['first'])
    check('success journal order',progress['completedStages']==['first'])
    check('success journal identifies stage',progress['currentStage']=='first' and progress['returnCode']==0)
    check('success journal remains in progress until completion',progress['status']=='IN_PROGRESS')
    check('atomic write leaves no temporary file',not (session/'pipeline-progress.json.tmp').exists())
    before = (session/'pipeline-progress.json').read_bytes()
    marker = session/'duplicate-ran'
    duplicate_rejected = False
    try:
        run('first',sys.executable,'-c',f'from pathlib import Path;Path({str(marker)!r}).touch()')
    except ValueError:
        duplicate_rejected = True
    check('duplicate stage rejected before subprocess',duplicate_rejected and not marker.exists())
    check('duplicate stage leaves journal unchanged',(session/'pipeline-progress.json').read_bytes()==before)
    failure_code = None
    try:
        run('failed',sys.executable,'-c','raise SystemExit(7)')
    except subprocess.CalledProcessError as error:
        failure_code = error.returncode
    progress = json.loads((session/'pipeline-progress.json').read_text())
    check('nonzero stage raises exact exit code',failure_code==7)
    check('failed stage excluded from completion sequence',namespace['completed_stages']==['first'])
    check('failure journal preserves successful prefix',progress['completedStages']==['first'])
    check('failure journal records failed stage and code',progress['currentStage']=='failed' and progress['returnCode']==7)
    check('failure journal has explicit FAIL status',progress['status']=='FAIL')
    check('stage failure does not write completion',(session/'pipeline-completion.json').exists() is False)
    target = session/'atomic-fixture.json'
    atomic_json(target,{'fixture':1})
    atomic_json(target,{'fixture':2})
    check('atomic writer replaces existing JSON exactly',json.loads(target.read_text())=={'fixture':2})

    stage_nodes = [(i,n) for i,n in enumerate(tree.body) if call_named(n,'run')]
    stages = [ast.literal_eval(n.value.args[0]) for _,n in stage_nodes]
    check('all actual stage identifiers are unique',len(stages)==len(set(stages)))
    completion_nodes = [(i,n) for i,n in enumerate(tree.body) if call_named(n,'atomic_json')]
    check('exactly one final structured completion write',len(completion_nodes)==1)
    check('completion write follows all actual stages',completion_nodes[0][0]>stage_nodes[-1][0])
    completion_fields = completion_nodes[0][1].value.args[1]
    check('completion is built as an explicit dictionary',isinstance(completion_fields,ast.Dict))
    fields = {ast.literal_eval(k):v for k,v in zip(completion_fields.keys,completion_fields.values)}
    check('completion status and format are explicit',
          ast.literal_eval(fields['status'])=='PASS' and
          ast.literal_eval(fields['format'])=='conditional-quartic-pipeline-completion-v1')
    check('completion uses live completed stage list',isinstance(fields['completedStages'],ast.Name) and
          fields['completedStages'].id=='completed_stages')
    if args.expected:
        expected = json.loads(args.expected.read_text())
        check('actual ordered pipeline stages match output manifest',
              expected['completionRecord']['stages']==stages)
    report = {'status':'PASS','pipelineSha256':digest(args.pipeline),'checkerSha256':digest(Path(__file__)),
              'expectedManifestSha256':digest(args.expected) if args.expected else None,
              'checks':checks,'assertions':len(checks),'orderedActualStages':stages,
              'scope':'Independent focused journal/helper execution and static completion-order checks; no mathematical construction executed.'}
    args.report.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ['checks','orderedActualStages']},indent=2))


if __name__=='__main__':
    main()
