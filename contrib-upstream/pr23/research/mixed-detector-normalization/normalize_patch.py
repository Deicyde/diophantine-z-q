"""Use the older delta^-3 normalization only for the six high tests.

Input is the actual order-45 builder after inherited substitutions.
"""
import re


def transform(source):
    old = "let q45=rquot('detector'+r+'.q45',sq(mixedHigh),q1cube,'positive_order_one_weight');"
    new = "let q45=rquot('detector'+r+'.q45',sq(mixedHigh),q1,'positive_order_one_weight');"
    assert source.count(old) == 1
    result = source.replace(old, new)
    comments = {
        '// R=1/E, q1=e/delta, q12=q1*e^22, q45=q1*e^88; E=q1*delta^2.':
            '// R=1/E, q1=e/delta, q12=e^23/delta, q46=e^91/delta^3; E=q1*delta^2.',
        '// Contact-unit normalization: use delta*D as the semantic one-place test.':
            '// One-place inputs: D/delta^m for low tests; D/delta^47 for high order46.',
        '// q_m=e^(2m-1)/delta=E^(m-1)*q1^m, where E=1/R; e need not be stored.':
            '// Low q_m=e^(2m-1)/delta; high q46=e^91/delta^3. E=1/R; e is not stored.',
    }
    for before, after in comments.items():
        assert result.count(before) == 1
        result = result.replace(before, after)
    result = re.sub(r'\b45\b', '46', result)
    return result.replace('q45', 'q46').replace('E45', 'E46')
