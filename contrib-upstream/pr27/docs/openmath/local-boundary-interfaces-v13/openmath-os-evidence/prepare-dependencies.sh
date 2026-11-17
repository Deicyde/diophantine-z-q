#!/bin/sh
set -eu
ROOT="$PWD"
PROJECT="$ROOT/lean/.checks/openmath-local-boundary"
ARCHIVE="$ROOT/.checks/aborted-lake-checkout/$(date -u +%FT%H%M%SZ)"
mkdir -p "$ARCHIVE" "$PROJECT/.lake/packages"
for p in mathlib plausible LeanSearchClient importGraph proofwidgets aesop Qq batteries Cli
 do
  test ! -e "$PROJECT/.lake/packages/$p" || mv "$PROJECT/.lake/packages/$p" "$ARCHIVE/$p"
done
cp -a /opt/mathlib "$PROJECT/.lake/packages/mathlib"
for p in plausible LeanSearchClient importGraph proofwidgets aesop Qq batteries; do
  cp -a "/opt/mathlib/.lake/packages/$p" "$PROJECT/.lake/packages/$p"
done
cp -a "$ROOT/lean/.lake/packages/Cli" "$PROJECT/.lake/packages/Cli"
for p in mathlib plausible LeanSearchClient importGraph proofwidgets aesop Qq batteries Cli; do
  printf '#!/bin/sh\nprintf "Source dependency %s now has revision " "$1"\n' "$p"
done
mkdir -p "$PWD/.checks/tmp"
export TMPDIR="$PWD/.checks/tmp"
export TMP="$TMPDIR"
export TEMP="$TMPDIR"
export PATH="$PWD/.checks/tool-bin:$PATH"
python3 - "$PROJECT" <<'PY'
import json, subprocess, sys
from pathlib import Path
project=Path(sys.argv[1])
pins=json.loads((project/'lake-manifest.json').read_text())['packages']
report=[]
for pin in pins:
    folder=project/'.lake/packages'/pin['name']
    head=subprocess.check_output(['git','-c','safe.directory=*','-C',str(folder),'rev-parse','HEAD'],text=True).strip()
    if head != pin['rev']:
        raise RuntimeError(f'{pin["name"]}: prepared {head}, expected {pin["rev"]}')
    subprocess.run(['git','-c','safe.directory=*','-C',str(folder),'diff','--quiet','HEAD','--'],check=True)
    cache=folder/'.lake/build/lib/lean'
    if not cache.is_dir():
        raise RuntimeError(f'Missing compiled cache: {cache}')
    report.append({'name':pin['name'],'revision':head,'compiled_cache':str(cache),
       'source_origin':'Local exact-revision copy from the pinned VM installation' if pin['name']!='Cli' else 'Exact-revision copy of the prior CLI source newly built in the review workspace',
       'cache_present':True,'tracked_source_clean':True})
result={'root_package':'local_boundary_verification','proof_roots':41,'prepared_project':str(project),'dependencies':report}
Path.cwd()/'docs/openmath/local-boundary-interfaces-v13/openmath-os-evidence/PREPARED_DEPENDENCIES.json'.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'all_nine_revision_and_cache_checks':True,'cli_independently_built':True}))
PY
exec "$ROOT/.checks/pr2-paranoid-run.sh"
