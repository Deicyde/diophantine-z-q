"""Source patches on a copy of the #13 builder (builder380.cjs)."""
import sys

def rep(src, old, new):
    assert src.count(old) == 1, old
    return src.replace(old, new, 1)

def t_by_rinverse(src):
    # T = rho*W^2 = 42 r N^2 is defined by the quadratic quotient row  ri*T = 42 N^2  (r*ri=1).
    return rep(src, """const rho=save('scalar.correctedR',scale(rr,42)),W2=rsq('scalar.W2',nw);
save('scalar.Bsemantic',mul(rho,W2));
pole('scalar',rho,scalar,false,mul(rho,W2));""",
"""const rho=save('scalar.correctedR',scale(rr,42));
const Tq=rquot('scalar.preparationT',scale(sq(nw),42),ri,'rInverse_nonzero_since_r_times_rInverse_is_one');
save('scalar.Bsemantic',Tq);
pole('scalar',rho,scalar,false,Tq);""")

PATCHES = {'tri': [t_by_rinverse]}


def tau_chart(src):
    # Replace w=h_S*tau and f=w^2/x_S by tau itself: tau=(h_P j_S - h_S j_P)/(x_P x_S + D).
    src = rep(src, """function subtractRootConstant(name,Qp,Rp){""", """function subtractRootConstantTau(name,Qp,Rp){
 const F=fadd(rawFmul(Rp.x,Qp.x),D);
 // w=(h_R h_Q j_Q - x_Q j_R)/F and x_Q=h_Q^2, so tau=w/h_Q has a linear numerator.
 const tau=fquot(name+'.tau',fsub(rawFmul(Rp.h,Qp.j),rawFmul(Qp.h,Rp.j)),F,'totally_positive_xP_xU_plus_D');
 return {tau:saveF(name+'.tau',tau),f:saveF(name+'.f',rawFmul(tau,tau))};
}
function subtractRootConstant(name,Qp,Rp){""")
    src = rep(src, "const scalarPoint=subtractRootConstant('scalar.shiftedS',points.S,P);\nconst PS=parameters('Sscalar',scalarPoint);",
              "const scalarPoint=subtractRootConstantTau('scalar.shiftedS',points.S,P);\nconst PS={f:scalarPoint.tau};")
    src = rep(src, "const ratioProxyReal=assign('scalar.ratioProxyReal',add(mul(primaryRatio[0],scalarPoint.w[0]),scale(mul(primaryRatio[1],scalarPoint.w[1]),2)));",
              "const ratioProxyReal=assign('scalar.ratioProxyReal',add(mul(primaryRatio[0],scalarPoint.tau[0]),scale(mul(primaryRatio[1],scalarPoint.tau[1]),2)));\ninv('scalar.ratioProxyNonzero',ratioProxyReal);")
    src = rep(src, "const physicalExpression=add(sq(scalarPoint.w[0]),scale(sq(scalarPoint.w[1]),-2),",
              "const physicalExpression=add(sq(scalarPoint.tau[0]),scale(sq(scalarPoint.tau[1]),-2),")
    return src

PATCHES['tau'] = [t_by_rinverse, tau_chart]
PATCHES['tauonly'] = [tau_chart]

def ri31_leaf(src):
    # One extra Laurent step r*ri31=ri15^2; scalar proxy leaf y=t/r^32 (r*y=ri31*t).
    src = rep(src, "      ri15=rquot('scalar.rInverse15',sq(ri7),rr,'positive_scalar_contact_product');",
              "      ri15=rquot('scalar.rInverse15',sq(ri7),rr,'positive_scalar_contact_product'),\n      ri31=rquot('scalar.rInverse31',sq(ri15),rr,'positive_scalar_contact_product');")
    src = rep(src, "rquot('scalar.ratioProxyLeaf',mul(ratioProxyReal,ri15),rr,", "rquot('scalar.ratioProxyLeaf',mul(ratioProxyReal,ri31),rr,")
    return src

def set_exponent(E):
    def f(src):
        import re
        out, n = re.subn(r"value:'3\^[0-9]+'", "value:'3^%d'" % E, src)
        assert n == 1
        return out
    return f

PATCHES['tau31'] = [t_by_rinverse, tau_chart, ri31_leaf]
PATCHES['tri31'] = [t_by_rinverse, ri31_leaf]

def f0_guard(src):
    # Keep the old guard semantics f(Q)_0 != 0 with f(Q)=tau^2, instead of guarding the proxy.
    return rep(src, "inv('scalar.ratioProxyNonzero',ratioProxyReal);",
               "inv('scalar.shiftedS.nonzeroRealF',assign('scalar.shiftedS.f0',add(sq(scalarPoint.tau[0]),scale(sq(scalarPoint.tau[1]),2))));")

PATCHES['tauf0'] = [t_by_rinverse, tau_chart, f0_guard]

if __name__ == '__main__':
    name, src, dst = sys.argv[1], sys.argv[2], sys.argv[3]
    s = open(src).read()
    for f in PATCHES[name]:
        s = f(s)
    open(dst, 'w').write(s)
