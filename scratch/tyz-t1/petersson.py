"""TYZ L975: Om^2 = 32 pi^2 (phi, phi)_{Gamma0(32)}, Om = Om_{1,inf} = 2 int_1^oo dx/sqrt(x^3-x)."""
import cypari2
pari = cypari2.Pari(); pari.allocatemem(10**9); pari('default(realprecision,40)')
print(pari('E=ellinit([0,0,0,4,0]); w=E.omega; cov=abs(imag(conj(w[1])*w[2])); '
           'Om1=2*intnum(x=[1,-1/2],[oo,-3/2],1/sqrt(x^3-x)); '
           'mf=mfinit([32,2],0); F=mfeigenbasis(mf)[1]; pp=48*mfpetersson(mfsymbol(mf,F)); '
           '[Om1, cov, Om1^2/cov, cov/(4*Pi^2*pp), Om1^2/(32*Pi^2*pp)]'))
