#!/usr/bin/env python3
"""Check that ZInQ.FrozenTarget states upstream's frozen main theorem token for token."""
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]


def statement(text, start, end):
    i = text.index(start)
    j = text.index(end, i)
    return re.sub(r'\s+', ' ', text[i:j]).strip()


frozen = (ROOT / 'lean/Frozen/BoundedIntegerPolynomial.lean').read_text(encoding='utf-8')
target = (ROOT / 'ZInQKernel/Target.lean').read_text(encoding='utf-8')
a = statement(frozen, '∃ P : MvPolynomial', ':= by')
b = statement(target, '∃ P : MvPolynomial', '\nend ZInQ')
if a != b:
    print('FrozenTarget differs from the frozen statement:\n  frozen: ' + a + '\n  target: ' + b)
    sys.exit(1)
print('FrozenTarget matches lean/Frozen/BoundedIntegerPolynomial.lean')
