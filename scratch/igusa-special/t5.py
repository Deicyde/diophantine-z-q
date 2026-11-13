import sys, itertools, time, pickle; sys.path.insert(0, '.')
from poly import *
J = load_J()
a, b = var(0, 2), var(1, 2); one = const(1, 2)
Ev = [one, {}, b, {}, a, {}, one]
JE = [subst(j, Ev, 2) for j in J]
for j in JE: print(len(j), fmt(j, 'ab')[:300])
pickle.dump(JE, open('/tmp/igs_JE.pkl', 'wb'))
