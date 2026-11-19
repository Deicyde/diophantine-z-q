"""Base audit discovery remains complete beside many periodic artifacts."""
import hashlib
import io
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from urllib.parse import parse_qs, urlsplit
import zipfile

import kernel_base_report as loader


class BaseReportDiscovery(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.addCleanup(self.tmp.cleanup)
        self.base = 'a'*40
        self.contract = b'bound source contract'
        report = {'status': 'passed', 'head_sha': self.base,
                  'contract_sha256': hashlib.sha256(self.contract).hexdigest(),
                  'targets': [{'name': 'Example', 'status': 'checked'}]}
        stream = io.BytesIO()
        with zipfile.ZipFile(stream, 'w') as archive:
            archive.writestr('audit.json', json.dumps(report))
        self.archive = stream.getvalue()
        self.audit = {'id': 999, 'name': 'kernel-audit', 'expired': False,
                      'digest': 'sha256:'+hashlib.sha256(self.archive).hexdigest()}
        self.artifacts = [{'id': i+1, 'name': f'kernel-progress-1-{i:03}',
                           'expired': False} for i in range(200)] + [self.audit]
        self.calls = []
        self.response_change = lambda value: value
        event = self.root/'event.json'
        event.write_text(json.dumps({'before': self.base}))
        self.addCleanup(patch.stopall)
        patch.object(loader, 'ROOT', self.root).start()
        patch.dict(os.environ, {'GITHUB_REPOSITORY': 'owner/repo',
                               'GITHUB_EVENT_PATH': str(event)}).start()
        patch.object(loader, 'git', side_effect=lambda root, command, *args:
                     self.contract if command == 'show' else b'').start()
        patch.object(loader, 'request', side_effect=self.request).start()

    def request(self, path, raw=False):
        self.calls.append((path, raw))
        parsed = urlsplit(path)
        query = parse_qs(parsed.query)
        if parsed.path.endswith('/kernel-lean.yml/runs'):
            return {'workflow_runs': [{'id': 42, 'head_sha': self.base,
                'head_branch': 'main', 'head_repository': {'full_name': 'owner/repo'},
                'event': 'push', 'conclusion': 'success'}]}
        if parsed.path.endswith('/runs/42/artifacts'):
            # Model the API's name filter and 100-item first page. Without the
            # filter, the genuine audit is after all 200 resource chunks.
            rows = self.artifacts
            if 'name' in query:
                rows = [a for a in rows if a['name'] == query['name'][0]]
            return self.response_change({'total_count': len(rows), 'artifacts': rows[:100]})
        if parsed.path.endswith('/artifacts/999/zip'):
            self.assertTrue(raw)
            return self.archive
        self.fail('Unexpected API read: '+path)

    def run_loader(self):
        loader.main()
        return json.loads((self.root/'build/kernel-ci/base-evidence.json').read_bytes())

    def test_audit_after_two_hundred_resource_chunks_is_found(self):
        result = self.run_loader()
        self.assertEqual(result['status'], 'authenticated_main_ci')
        self.assertEqual(result['artifact_id'], 999)
        loaded = json.loads((self.root/'build/kernel-ci/base-audit.json').read_bytes())
        self.assertEqual(loaded['targets'], [{'name': 'Example', 'status': 'checked'}])

    def test_missing_expired_and_ambiguous_audits_remain_unmeasured(self):
        for audits in ([], [{**self.audit, 'expired': True}],
                       [self.audit, {**self.audit, 'id': 1000}]):
            with self.subTest(audits=audits):
                self.artifacts = audits
                self.calls.clear()
                self.assertEqual(self.run_loader()['status'], 'not_measured')
                self.assertFalse(any(raw for _, raw in self.calls))

    def test_truncated_filtered_response_is_not_unique_evidence(self):
        self.response_change = lambda value: {**value, 'total_count': 2}
        self.assertEqual(self.run_loader()['status'], 'not_measured')
        self.assertFalse(any(raw for _, raw in self.calls))

    def test_missing_or_invalid_count_is_not_complete_evidence(self):
        for count in (None, True, '1', -1):
            with self.subTest(count=count):
                self.response_change = lambda value: {**value, 'total_count': count}
                self.assertEqual(self.run_loader()['status'], 'not_measured')

    def test_wrong_archive_digest_still_refuses_the_report(self):
        self.audit['digest'] = 'sha256:'+'0'*64
        with self.assertRaisesRegex(RuntimeError, 'digest'):
            self.run_loader()


if __name__ == '__main__':
    unittest.main()
