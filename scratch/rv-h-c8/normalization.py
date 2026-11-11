# (1) E = 11a1, 37a1, 389a1 (k=2, trivial character): a_l(E) = l+1-#E(F_l) is the trace of the
#     Frobenius endomorphism on V_p(E), i.e. of ARITHMETIC Frobenius on the Tate module; compare
#     with the q-expansion of the weight-2 newform (mffromell). First 25 good primes each.
# (2) Weight 2, level 13, character chi of order 6 (znstar(13) generator exponent 2): check
#     conj(a_l) = conj(chi(l)) a_l for l < 100, l != 13, exactly in Q(zeta_6), the coefficient field, i.e.
#     fbar = f (x) chi^{-1} is a Galois conjugate of f (so the other normalization rho_f^vee (x) cyc
#     is again a constituent of V(A_f)).
import cypari2
pari = cypari2.Pari()
pari.allocatemem(2*10**8)
gp = r'''
check1(ai)=my(E=ellinit(ai),N=ellglobalred(E)[1],F=mffromell(E)[2],c=mfcoefs(F,120),bad=0,n=0);
  forprime(p=2,120, if(N%p, n++; if(n<=25, if(ellap(E,p)!=c[p+1] || ellap(E,p)!=p+1-ellcard(E,p), bad++))));
  [N,min(n,25),bad];
check2()=my(G=znstar(13,1),mf=mfinit([13,2,[G,[2]]],0),L=mfeigenbasis(mf),f=L[1],c=mfcoefs(f,100),o=charorder(G,[2]),T=t^2-t+1,out=[]);
  forprime(p=2,97, if(p!=13, my(a=Mod(lift(c[p+1]),T),e=chareval(G,[2],p,[Mod(t,T),o]),sg=x->Mod(subst(lift(x),t,1-t),T));
     out=concat(out,[[p, sg(a)==sg(e)*a]])));
  [#L, 2, o, out]
'''
for d in gp.strip().split(";\ncheck"):
    d = d if d.startswith("check") else "check" + d
    pari(d.replace("\n", " ").rstrip(";"))
for name, ai in [("11a1","[0,-1,1,-10,-20]"),("37a1","[0,0,1,-1,0]"),("389a1","[0,1,1,-2,0]")]:
    N, n, bad = pari("check1(%s)" % ai)
    print(name, "N =", N, "primes checked =", n, "mismatches (newform a_l vs ellap vs l+1-#E) =", bad)
nL, deg, o, out = pari("check2()")
print("level 13 weight 2 char order", o, ": #eigenforms(new) =", nL, "coeff field degree =", deg)
print("conj(a_l) = conj(chi(l)) a_l exactly (complex conj = t->1-t on Q(zeta_6)) for all", len(out), "primes:", all(int(x[1]) == 1 for x in out))
