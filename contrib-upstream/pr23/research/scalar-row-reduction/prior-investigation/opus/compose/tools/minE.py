"""Minimal anchor exponent E (multiple of 6) per (detector order k, scalar order s), exact integers.
package margins = frontier/anchor_frontier.py (bc51100 Lucas, scalar c*^(32s-577)>(4H)^(32s));
sharpened = other session's NEXT_PR.md forms (unreviewed), s-generalized the same way."""
import sys
sys.path.insert(0, __file__.rsplit('/',1)[0])
from anchor_frontier import H0 as H, scalar_ok, lucas_ok, min_E, digits
def lucas_sh(E,m):
    c=2*3**(E//2-1); b=c-1; P=2*b**4+6*b**3+5*b**2+1
    return (2*(b*b-6))**(32*m) > (3*H+14)**(32*m)*P**577
def scalar_sh(E,s):
    c=2*3**(E//2-1); return 8**(32*s)*c**(32*s-577) > (25*H)**(32*s)
for s in (31,47):
    Es=min_E(lambda E: scalar_ok(E,H,577,s,4)); Ess=min_E(lambda E: scalar_sh(E,s))
    for k in (45,46,47,48,50):
        El=min_E(lambda E: lucas_ok(E,k,H)); Els=min_E(lambda E: lucas_sh(E,k))
        print(f's={s} k={k}: package scalar {Es} lucas {El} -> E={max(Es,El)} | sharpened scalar {Ess} lucas {Els} -> E={max(Ess,Els)}')
