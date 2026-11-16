# hcm-g1: which way does the arithmetic Frobenius at p | 2 move j(O_K) for K = Q(sqrt(-23))?
# ShimuraMainCM's normalization (Tau Ceti's arithmetic Artin map, lattice s^{-1}a) predicts
# j(a)^{Frob_p} = j(p^{-1} a). Here a = O_K, p0 = (2, omega), omega = (1+sqrt(-23))/2, p0^{-1} ~ p1 = (2, omega-1).
import cypari2
gp = cypari2.Pari(); gp.set_real_precision(60)
cmds = [
 "K = nfinit(y^2+23)",
 "R = rnfequation(K, polclass(-23), 1)",   # [pol, y as poly in X, k] with X = x + k*y
 "pol = R[1]; ay = lift(R[2]); k = R[3]",
 "L = nfinit(pol); G = galoisinit(L)",
 "j0 = ellj((1+I*sqrt(23))/2)",
 "rts = polroots(pol); r = 0",
 "for(i=1,#rts, t=rts[i]; if(abs(subst(ay,x,t)-I*sqrt(23))<1e-20 && abs(t-k*subst(ay,x,t)-j0)<1e-10, r=t))",
 "jP0 = ellj((1+I*sqrt(23))/4); jP1 = ellj((-1+I*sqrt(23))/4)",
 "om = (1+ay)/2; jx = x - k*ay",
 "dec = idealprimedec(L, 2); P = 0",
 "for(i=1,#dec, if(nfeltval(L, om, dec[i])>0, P=dec[i]))",
 "fr = idealfrobenius(L, G, P); s = galoispermtopol(G, fr)",
 "fj = subst(jx, x, s) % pol",
 "fjv = subst(fj, x, r)",
]
for c in cmds: gp(c)
print("embedding found:", gp("r != 0"))
print("check y fixed by Frob:", gp("(subst(ay,x,s) - ay) % pol == 0"))
print("f(P|2) =", gp("P.f"), " v_P(omega) =", gp("nfeltval(L, om, P)"), " v_P(omega-1) =", gp("nfeltval(L, om-1, P)"))
print("|Frob(j0) - j(p0)|      =", gp("abs(fjv - jP0)"))
print("|Frob(j0) - j(p0^{-1})| =", gp("abs(fjv - jP1)"))
print("j0, j(p0), j(p0^-1) =", gp("[j0, jP0, jP1]"))
# sanity: PARI's idealfrobenius is arithmetic: Frob(b) = b^2 mod P on the integral basis
print("Frob(b) - b^2 in P for every integral basis element b:",
      gp("vector(#L.zk, i, nfeltval(L, nfeltadd(L, nfgaloisapply(L, s, L.zk[i]), nfeltmul(L, -1, nfeltpow(L, L.zk[i], 2))), P) >= 1)"))
