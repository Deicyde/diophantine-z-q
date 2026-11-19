import hashlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import urllib.error
import urllib.request

import kernel_build_download as download


class DownloadTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.data = b'archive bytes; the next boundary checks the ZIP members'
        self.selection = {'status': 'selected', 'artifact_id': 91,
                          'archive_sha256': hashlib.sha256(self.data).hexdigest(),
                          'producer': {'repository': 'owner/repo', 'run_id': 12}}
        self.location = 'https://production.example.blob.core.windows.net/artifact?signature=private'
        self.requests = []
        self.status = 302

    def opener(self, handler):
        outer = self

        class Fake:
            def open(self, request, timeout):
                outer.requests.append(request)
                if isinstance(handler, download.NoAPIRedirect):
                    raise urllib.error.HTTPError(request.full_url, outer.status, 'redirect',
                                                 {'Location': outer.location}, None)
                return io.BytesIO(outer.data)

        return Fake()

    def run_download(self):
        return download.download_archive(self.selection, 'example-secret', self.temp.name,
                                         opener_factory=self.opener)

    def test_signed_redirect_receives_no_api_credentials(self):
        result = self.run_download()
        self.assertEqual(Path(result['path']).read_bytes(), self.data)
        self.assertEqual(self.requests[0].get_header('Authorization'), 'Bearer example-secret')
        self.assertIsNone(self.requests[1].get_header('Authorization'))
        self.assertNotIn('signature', str(result))
        self.assertNotIn('example-secret', str(result))

    def test_bad_digest_removes_only_this_partial_download(self):
        existing = Path(self.temp.name)/'unrelated'
        existing.write_bytes(b'keep')
        self.selection['archive_sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'digest mismatch'):
            self.run_download()
        self.assertEqual(list(Path(self.temp.name).iterdir()), [existing])
        self.assertEqual(existing.read_bytes(), b'keep')

    def test_unknown_storage_hosts_http_and_embedded_credentials_are_refused(self):
        for location in ('https://example.org/a', 'http://a.blob.core.windows.net/a',
                         'https://a.blob.core.windows.net.evil.test/a',
                         'https://user:pass@a.blob.core.windows.net/a',
                         'https://a.blob.core.windows.net:80/a',
                         'https://a.blob.core.windows.net/a#fragment'):
            self.location = location
            self.requests.clear()
            with self.subTest(location=location), self.assertRaises(ValueError):
                self.run_download()
            self.assertEqual(len(self.requests), 1)
            self.assertEqual(list(Path(self.temp.name).iterdir()), [])

    def test_second_redirect_also_checks_host_and_drops_authorization(self):
        handler = download.StorageRedirect()
        req = urllib.request.Request(self.location, headers={'Authorization': 'must-not-leak'})
        redirected = handler.redirect_request(req, None, 302, '', {},
                                               'https://a.actions.githubusercontent.com/next')
        self.assertIsNone(redirected.get_header('Authorization'))
        with self.assertRaises(ValueError):
            handler.redirect_request(req, None, 302, '', {}, 'https://example.org/next')

    def test_failed_api_and_limits_leave_no_partial_download(self):
        self.status = 403
        with self.assertRaisesRegex(ValueError, 'storage redirect'):
            self.run_download()
        self.assertEqual(list(Path(self.temp.name).iterdir()), [])
        self.status = 302
        with patch.object(download, 'MAX_DOWNLOAD_BYTES', 2):
            with self.assertRaisesRegex(ValueError, 'size limit'):
                self.run_download()
        self.assertEqual(list(Path(self.temp.name).iterdir()), [])
        with patch.object(download.time, 'monotonic', side_effect=[0, 1000]):
            with self.assertRaisesRegex(ValueError, 'time limit'):
                self.run_download()
        self.assertEqual(list(Path(self.temp.name).iterdir()), [])


if __name__ == '__main__':
    unittest.main()
