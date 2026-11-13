import sys; sys.path.insert(0, '.')
from poly import *
J = load_J()
j10 = J[3]
print('all have a5 or a6:', all(k[5] or k[6] for k in j10), 'all have a0 or a1:', all(k[0] or k[1] for k in j10))
print('terms without a0,a6:', sum(1 for k in j10 if not k[0] and not k[6]))
