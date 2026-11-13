exec(open('twist2.py').read().split("def dist")[0])
def dist(P,Q): return abs(P[0]-Q[0])+abs(P[1]-Q[1])
for n, (num, den) in [(5,(1089,1624)), (13,(1801,88*61))]:
    w = I*sqrt(n)
    tX = (num + w)/den
    tQ = (1+w)/(4*(n+1))
    tP = (2*n+15+w)/(4*(n+9))
    z,_ = reduce0(tX); zp,_ = reduce0(tP)
    PX, PQ, PP = phi(z), phi(tQ), phi(zp)
    print(n, "phi(tauX) vs phi(tauQ)", float(dist(PX,PQ)), " phi(tau_Q') vs phi(tauQ)+T00", float(dist(PP, add(PQ,T00))))
