import sys, pickle; sys.path.insert(0, '.')
from poly import *
G = pickle.load(open('/tmp/igs_G.pkl', 'rb'))
for e in range(3):
    co = {k[2]: v for k, v in G.items() if k[0] == e}
    print('u^%d:' % e, [co.get(i, 0) for i in range(10)])
