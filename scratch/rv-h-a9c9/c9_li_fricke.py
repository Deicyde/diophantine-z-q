"""C9 check of Li's Fricke formula f|_2 W_N = lambda * fbar (fbar = sum conj(a_n) q^n), by direct
numerical evaluation of q-expansions (independent of PARI's Atkin-Lehner code), for weight-2
newforms with NONTRIVIAL even character, N = 11..60, first 30 (form, embedding) pairs.
W_N = [[0,-1],[N,0]], (f|_2 W_N)(z) = N (N z)^(-2) f(-1/(N z)).
Since fbar = c(f) (c = complex conjugation in Aut(C)) is a Galois conjugate, this shows the span
of conjugates of f is W_N-stable on samples. Also compare lambda with PARI's mfatkineigenvalues."""
import cypari2
pari = cypari2.Pari()
pari.allocatemem(2*10**9)
pari.default("realprecision", 80)
M = 500
done = 0
worst = 0
pari('M=%d' % M)
for N in range(11, 61):
    if done >= 30: break
    pari('G=znstar(%d,1); CH=chargalois(G)' % N)
    for ci in range(1, int(pari('#CH')) + 1):
        if done >= 30: break
        pari('chi=CH[%d]' % ci)
        if pari('zncharisodd(G,chi)') == 1 or pari('charorder(G,chi)') == 1:
            continue
        pari('mf=mfinit([%d,2,[G,chi]],0)' % N)
        if pari('mfdim(mf)') == 0: continue
        pari('L=mfeigenbasis(mf); AE=mfatkineigenvalues(mf,%d)' % N)
        for fi in range(1, int(pari('#L')) + 1):
            if done >= 30: break
            pari('f=L[%d]; V=mfembed(f, mfcoefs(f,M)); if(type(V[1])!="t_VEC", V=[V])' % fi)
            ne = int(pari('#V'))
            for e in range(1, ne + 1):
                if done >= 30: break
                pari('a=V[%d]' % e)  # a[1]=a_0,...,a[M+1]=a_M
                pari('F(z)=my(q=exp(2*Pi*I*z)); sum(n=1,M, a[n+1]*q^n)')
                pari('Fb(z)=my(q=exp(2*Pi*I*z)); sum(n=1,M, conj(a[n+1])*q^n)')
                pari('W(z)=%d*(%d*z)^(-2)*F(-1/(%d*z))' % (N, N, N))
                pari('y0=1/sqrt(%d); pts=[I*y0, 0.05+1.1*I*y0, -0.1+0.9*I*y0]' % N)
                pari('R=vector(3,j,W(pts[j])/Fb(pts[j]))')
                spread = float(pari('vecmax(vector(3,j,abs(R[j]-R[1])))'))
                absl = float(pari('abs(abs(R[1])-1)'))
                inpari = float(pari('vecmin(apply(x->abs(x-R[1]), concat(AE[%d])))' % fi))
                order = int(pari('charorder(G,chi)'))
                print(f"N={N} chi#{ci} (order {order}) form {fi} emb {e}: lambda={complex(pari('R[1]')):.12f} "
                      f"spread={spread:.2e} ||lambda|-1|={absl:.2e} dist to PARI pseudo-eig={inpari:.2e}")
                worst = max(worst, spread, absl)
                done += 1
print("checked", done, "pairs; worst spread/|lambda| defect:", worst)
