"""ESTIMATE/exact-integer check of the OTHER session's sharpened consumers (NEXT_PR.md) at order 46.
Not owned here; only to show whether order 46 combines with E=2010."""
import sys
H = 3*2**106*(2**32*3**9)**6*46410**18+128
def lucas(E, m):
    c = 2*3**(E//2-1); b = c-1
    P = 2*b**4+6*b**3+5*b**2+1
    return (2*(b*b-6))**(32*m) > (3*H+14)**(32*m) * P**577
def scalar(E):
    c = 2*3**(E//2-1)
    return 8**992 * c**415 > (25*H)**992
for E in (1998, 2004, 2010, 2016):
    print(E, 'scalar(8c/25 target)', scalar(E), {m: lucas(E, m) for m in (45, 46, 47)})
