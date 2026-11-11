import sys; sys.path.insert(0, 'scratch/rv-prop-n')
from tyzlib import *
for n in [5, 13, 21, 29, 205, 26565]:
    print(n, primes_of(n), genus_sums(n), genus_sums(n, True))
