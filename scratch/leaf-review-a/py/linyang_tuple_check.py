# leaf-review-a: test Lin-Yang's J-tuple (Leaves3.lean l.21306) against the Hashimoto-Murabayashi
# disc-6 QM family (recalled from memory: Tohoku Math. J. 47 (1995); UNVERIFIED):
#   y^2 = x(x^4 - P x^3 + Q x^2 - R x + 1), P=2(s+t), R=2(s-t),
#   Q=(1+2t^2)(11-28t^2+8t^4)/(3(1-t^2)(1-4t^2)),  4s^2t^2 - s^2 + t^2 + 2 = 0.
import itertools, mpmath as mp
mp.mp.dps=50
def dsq(r,i,j): return (r[i]-r[j])**2
perms=list(itertools.permutations(range(6)))
def IC(a,r):
    I2=a**2*sum(dsq(r,s[0],s[1])*dsq(r,s[2],s[3])*dsq(r,s[4],s[5]) for s in perms)/48
    I4=a**4*sum(dsq(r,s[0],s[1])*dsq(r,s[1],s[2])*dsq(r,s[2],s[0])*dsq(r,s[3],s[4])*dsq(r,s[4],s[5])*dsq(r,s[5],s[3]) for s in perms)/72
    I6=a**6*sum(dsq(r,s[0],s[1])*dsq(r,s[1],s[2])*dsq(r,s[2],s[0])*dsq(r,s[3],s[4])*dsq(r,s[4],s[5])*dsq(r,s[5],s[3])*dsq(r,s[0],s[3])*dsq(r,s[1],s[4])*dsq(r,s[2],s[5]) for s in perms)/12
    I10=a**10
    for i in range(6):
        for j in range(i+1,6): I10*=dsq(r,i,j)
    return I2,I4,I6,I10
def J(a,r):
    I2,I4,I6,I10=IC(a,r); J2=I2/8; J4=(4*J2**2-I4)/96; J6=(8*J2**3-160*J2*J4-I6)/576; J10=I10/4096
    return J2,J4,J6,J10
for t in [mp.mpf('0.3'),mp.mpf('2.7'),mp.mpc('0.4','0.9')]:
    s=mp.sqrt(-(t**2+2)/(4*t**2-1))
    P=2*(s+t); R=2*(s-t); Q=(1+2*t**2)*(11-28*t**2+8*t**4)/(3*(1-t**2)*(1-4*t**2))
    # roots of x(x^4-Px^3+Qx^2-Rx+1) plus infinity; move by x -> 1/(x-c): roots r -> 1/(r-c), infinity -> 0
    fr=[0]+list(mp.polyroots([1,-P,Q,-R,1],maxsteps=200,extraprec=200))
    c=mp.mpf('0.123456')
    r=[1/(x-c) for x in fr]+[mp.mpf(0)]
    J2,J4,J6,J10=J(1,r)
    jv=3779136*(4096*J10)**2/((4*J2**2-96*J4)**5)   # j = 3779136 I10^2/I4^5
    # tuple ratios: J2^2/J4 = 144(j+1)^2/(6(j^2+j+1)), J2^3/J6 = 1728(j+1)^3/(4(j^3-2j^2+1)), J2^5/J10=12^5(j+1)^5/j^3
    print("t",t,"j",mp.nstr(jv,12))
    print("  J2^2/J4 data",mp.nstr(J2**2/J4,12)," tuple",mp.nstr(144*(jv+1)**2/(6*(jv**2+jv+1)),12))
    print("  J2^3/J6 data",mp.nstr(J2**3/J6,12)," tuple",mp.nstr(1728*(jv+1)**3/(4*(jv**3-2*jv**2+1)),12))
    print("  J2^5/J10 data",mp.nstr(J2**5/J10,12)," tuple",mp.nstr(12**5*(jv+1)**5/jv**3,12))
