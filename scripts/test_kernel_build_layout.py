import json
from pathlib import Path
import tempfile
import unittest

from kernel_build_layout import bind_project_paths, project_layout


class LayoutTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        (self.root/'lake-manifest.json').write_text(json.dumps({'packages':[
            {'type':'path','dir':'./local','configFile':'lakefile.toml'},
            {'type':'git','name':'external'}]}))
        self.config = 'name="project"\n[[lean_lib]]\nname="Project"\n'
        (self.root/'lakefile.toml').write_text(self.config)
        (self.root/'local').mkdir()
        (self.root/'local/lakefile.toml').write_text('name="local"\n[[lean_lib]]\nname="Other"\n')
        self.paths = {'Project':'Project.lean', 'Project.Sub':'Project/Sub.lean',
                      'Other':'local/Other.lean'}
        for path in self.paths.values():
            source=self.root/path; source.parent.mkdir(exist_ok=True, parents=True)
            source.write_text('def value := 1')

    def bind(self):
        return bind_project_paths(self.root,self.paths,project_layout(self.root))

    def test_root_local_and_submodule_paths_and_outputs(self):
        result=self.bind()
        self.assertEqual(result['Project.Sub']['source_path'],'Project/Sub.lean')
        self.assertEqual(result['Project.Sub']['lean_output_prefix'],'.lake/build/lib/lean/Project/Sub')
        self.assertEqual(result['Other']['lean_output_prefix'],'local/.lake/build/lib/lean/Other')

    def test_package_and_library_source_directories_are_composed(self):
        (self.root/'lakefile.toml').write_text('name="project"\nsrcDir="src"\n'
            '[[lean_lib]]\nname="Vendor"\nsrcDir="vendor"\nroots=["Project"]\n')
        for name in ('Project','Project.Sub'):
            old=self.root/self.paths[name]
            self.paths[name]='src/vendor/'+self.paths[name]
            new=self.root/self.paths[name]; new.parent.mkdir(parents=True,exist_ok=True); old.rename(new)
        self.assertEqual(self.bind()['Project']['library'],'Vendor')

    def test_declared_contract_path_cannot_override_lake_lookup(self):
        self.paths['Project']='local/Other.lean'
        with self.assertRaisesRegex(ValueError,'differs from Lake'):self.bind()

    def test_ambiguous_roots_are_rejected_instead_of_guessing_priority(self):
        (self.root/'lakefile.toml').write_text(self.config+'\n[[lean_lib]]\nname="Overlap"\nroots=["Project"]\n')
        with self.assertRaisesRegex(ValueError,'ambiguous'):self.bind()

    def test_unknown_configs_and_custom_globs_do_not_qualify(self):
        for extra in ('globs=["Project.*"]','moreLeanArgs=["-R", "elsewhere"]','custom="yes"'):
            (self.root/'lakefile.toml').write_text(self.config+extra+'\n')
            with self.assertRaisesRegex(ValueError,'Unsupported library'):self.bind()
        (self.root/'lakefile.lean').write_text('import Lake')
        with self.assertRaisesRegex(ValueError,'Executable'):self.bind()

    def test_escaping_roots_and_changed_layout_are_rejected(self):
        layout=project_layout(self.root)
        (self.root/'lakefile.toml').write_text(self.config+'srcDir="new"\n')
        with self.assertRaisesRegex(ValueError,'changed'):bind_project_paths(self.root,self.paths,layout)
        (self.root/'lakefile.toml').write_text(self.config+'srcDir="../outside"\n')
        with self.assertRaisesRegex(ValueError,'Unsafe'):self.bind()


if __name__=='__main__':unittest.main()
