import sys; sys.path.insert(0, '.')
from poly import *
y = load_y(); J = load_J()
print([[len(c) for c in r] for r in y], [len(j) for j in J])
