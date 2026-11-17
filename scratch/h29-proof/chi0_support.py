"""h29-proof: is the test vector f_n supported on one class of chi0(nrd)?  (n = 1, 3 mod 8)"""
import sys
sys.path.insert(0, __import__('os').path.dirname(__file__))
from brandt import chi0
from brandt2 import tau_choices, test_vector, int_generator
print("chi0 on the 8 classes:", chi0)
for n in [3, 11, 17, 33, 41, 57, 73, 89, 97, 105, 113]:
    for abc in tau_choices(n)[:2]:
        f = int_generator(test_vector(n, abc))
        sup = set(chi0[i] for i in range(8) if f[i] != 0)
        print(n, abc, "f =", f, "chi0 on supp f:", sup)
