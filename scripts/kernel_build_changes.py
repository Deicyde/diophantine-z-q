"""Bounded diagnostics for a rejected input context; never authorizes reuse."""
import hashlib
import json


def fingerprint(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':'),
                                    ensure_ascii=True).encode()).hexdigest()


class InputContextMismatch(ValueError):
    def __init__(self, message, expected, observed, installed_detail):
        self.expected = expected
        self.observed = observed
        self.installed_detail = installed_detail
        self.changed = sorted(k for k in observed if expected.get(k) != observed[k])
        # Only category names enter the log, never environment values.
        super().__init__(message + ': ' + ', '.join(self.changed))

    def report(self, previous_detail=None, limit=100):
        previous = (previous_detail or {}).get('installed_inputs', {})
        files = []
        counts = {}
        groups = [('toolchain', previous.get('toolchain_files', {}),
                   self.installed_detail.get('toolchain_files', {}))]
        before_deps = previous.get('dependency_files', {})
        after_deps = self.installed_detail.get('dependency_files', {})
        groups += [('dependency/' + name, before_deps.get(name, {}), after_deps.get(name, {}))
                   for name in sorted(set(before_deps) | set(after_deps))]
        if previous_detail is None:
            groups = []  # Missing old evidence cannot identify added/removed files.
        # Detailed rows contain hashes, size, mode and relative link targets,
        # never source contents. Count all differences even if examples truncate.
        for group, before, after in groups:
            count = 0
            for path in sorted(set(before) | set(after)):
                if before.get(path) == after.get(path):
                    continue
                count += 1
                if len(files) < limit:
                    files.append({'group': group, 'path': path,
                                  'before': before.get(path), 'after': after.get(path)})
            if count:
                counts[group] = count
        return {'schema': 'kernel-input-mismatch/v1', 'acceptance': False,
                'decision': 'rejected', 'changed_categories': self.changed,
                'categories': {k: {'expected_sha256': fingerprint(self.expected.get(k)),
                                   'observed_sha256': fingerprint(self.observed[k])}
                               for k in self.changed},
                'previous_file_inventory_available': previous_detail is not None,
                'changed_file_counts': counts, 'file_examples': files,
                'file_examples_truncated': sum(counts.values()) > len(files)}
