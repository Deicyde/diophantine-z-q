import json
import os
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import kernel_build_resolution as resolve


class ResolutionTests(unittest.TestCase):
    def setUp(self):
        temporary=tempfile.TemporaryDirectory(); self.addCleanup(temporary.cleanup)
        self.root=Path(temporary.name)/'project'; self.root.mkdir()
        self.prefix=Path(temporary.name)/'toolchain'; self.prefix.mkdir()
        self.env={k:None for k in resolve.SEARCH_KEYS}
        binary=self.prefix/'bin'; binary.mkdir()
        ar=binary/'llvm-ar'; ar.write_bytes(b'fixture')
        self.env.update({'LEAN_SYSROOT':str(self.prefix.resolve()),'LAKE_HOME':str(self.prefix.resolve()),
            'LEAN':str(binary/('lean.exe' if os.name=='nt' else 'lean')),
            'LAKE':str(binary/('lake.exe' if os.name=='nt' else 'lake')),'LEAN_AR':str(ar)})
        self.packages={'packages':{}}

    def test_dependency_config_is_not_evaluated_until_all_expected_inputs_match(self):
        for mismatch in ('package','dependencies','compiler'):
            with self.subTest(mismatch=mismatch), \
                    patch.object(resolve,'project_layout'), \
                    patch.object(resolve,'package_environment',return_value={'different':1} if mismatch=='package' else self.packages), \
                    patch.object(resolve,'dependency_inputs',return_value=({'different':1} if mismatch=='dependencies' else {},{})), \
                    patch.object(resolve,'toolchain_inputs',return_value={'summary':'different' if mismatch=='compiler' else 'expected'}), \
                    patch.object(resolve.subprocess,'run') as run:
                with self.assertRaises(ValueError):
                    resolve.capture_lake_environment(self.root,self.prefix,self.packages,{},'expected')
                run.assert_not_called()

    def test_observer_uses_isolated_python_and_rechecks_dependency_bytes(self):
        with patch.object(resolve,'project_layout'), \
                patch.object(resolve,'checked_packages') as check, \
                patch.object(resolve,'toolchain_inputs',return_value={'summary':'expected'}), \
                patch.object(resolve.subprocess,'run',return_value=SimpleNamespace(returncode=0,stdout=json.dumps(self.env).encode())) as run:
            self.assertEqual(resolve.capture_lake_environment(self.root,self.prefix,self.packages,{},'expected'),self.env)
            self.assertEqual(check.call_count,2)
            self.assertIn('-I',run.call_args.args[0]); self.assertIn('-S',run.call_args.args[0])
            self.assertEqual(run.call_args.args[0][1],'env')

    def test_import_paths_are_from_actual_lean_output_and_confined_to_verified_roots(self):
        compiled=self.prefix/'Init.olean'; compiled.write_bytes(b'compiled')
        source=self.prefix/'Init.lean'; source.write_text('prelude')
        processes=[SimpleNamespace(returncode=0,stdout=(str(p)+'\n').encode()) for p in (compiled,source)]
        with patch.object(resolve.subprocess,'run',side_effect=processes) as run:
            result=resolve.resolve_imports(self.root,self.prefix,['Init'],self.env)
            self.assertEqual([c.args[0][1] for c in run.call_args_list],['--deps','--src-deps'])
            self.assertEqual(result['Init']['compiled']['owner'],'toolchain')
            self.assertEqual(result['Init']['compiled']['path'],'Init.olean')
        outside=self.root.parent/'outside.olean'; outside.write_bytes(b'unknown')
        with self.assertRaisesRegex(ValueError,'outside'):
            resolve.observed_file(self.root,self.prefix,str(outside))

    def test_malformed_names_cannot_inject_a_lean_command(self):
        for names in (['Init\n#eval 1'],['Init','Init'],['Init','init'],[],['../Init']):
            with self.subTest(names=names),patch.object(resolve.subprocess,'run') as run:
                with self.assertRaises(ValueError):resolve.resolve_imports(self.root,self.prefix,names,self.env)
                run.assert_not_called()

    def test_source_lookup_does_not_require_existing_project_objects(self):
        source=self.root/'Project.lean'; source.write_text('prelude')
        with patch.object(resolve.subprocess,'run',return_value=SimpleNamespace(
                returncode=0,stdout=(str(source)+'\n').encode())) as run:
            result=resolve.resolve_imports(self.root,self.prefix,['Project'],self.env,kinds=('source',))
            self.assertEqual(set(result['Project']),{'source'})
            self.assertEqual(run.call_count,1)
            self.assertEqual(run.call_args.args[0][1],'--src-deps')

    def test_two_module_names_cannot_share_a_resolved_input(self):
        source=self.root/'Project.lean'; source.write_text('prelude')
        with patch.object(resolve.subprocess,'run',return_value=SimpleNamespace(
                returncode=0,stdout=((str(source)+'\n')*2).encode())):
            with self.assertRaisesRegex(ValueError,'same input'):
                resolve.resolve_imports(self.root,self.prefix,['Project','Shadow'],self.env,kinds=('source',))

    def test_partial_lookup_and_credentials_stop_without_elaboration(self):
        with patch.object(resolve.subprocess,'run',return_value=SimpleNamespace(returncode=0,stdout=b'')):
            with self.assertRaisesRegex(ValueError,'incomplete'):
                resolve.resolve_imports(self.root,self.prefix,['Init'],self.env)
        with patch.dict(os.environ,{'GH_TOKEN':'fixture-not-a-token'}),patch.object(resolve.subprocess,'run') as run:
            with self.assertRaisesRegex(ValueError,'credentials'):
                resolve.resolve_imports(self.root,self.prefix,['Init'],self.env)
            run.assert_not_called()

    def test_fixed_lake_cannot_report_an_unverified_compiler_or_native_tool(self):
        for key in ('LEAN_SYSROOT','LAKE_HOME','LEAN','LAKE','LEAN_AR','LEAN_CC'):
            with self.subTest(key=key):
                foreign={**self.env,key:str(self.root/'unverified')}
                with self.assertRaisesRegex(ValueError,'unverified'):
                    resolve.validate_toolchain_selection(self.prefix,foreign)

    def test_runtime_and_trace_overrides_are_refused_before_lake_runs(self):
        for key,value in (('LAKE_OVERRIDE_LEAN','true'),('LEAN_GITHASH','forged'),
                          ('LD_PRELOAD','unverified.so'),('LAKE_CACHE_KEY','fixture-not-a-key')):
            with self.subTest(key=key),patch.dict(os.environ,{key:value}), \
                    patch.object(resolve.subprocess,'run') as run:
                with self.assertRaises(ValueError):
                    resolve.capture_lake_environment(self.root,self.prefix,self.packages,{},'expected')
                run.assert_not_called()


if __name__=='__main__':unittest.main()
