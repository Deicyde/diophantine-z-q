default(realprecision, 28);
phiv(an, M, tau) = {my(q = exp(2*Pi*I*tau), s = 0., qn = 1.); for(n = 1, M, qn *= q; s += an[n]/n*qn); s};
E = ellinit([0,0,0,-1,0]); w = E.omega;
an = ellan(E, 30000);
B = [real(w[1]), real(w[2]); imag(w[1]), imag(w[2])];
rho(a,c) = {my(e = lift(Mod(a, c)^-1), M = ceil(c*6.0)+60, p); p = phiv(an, M, (a + I)/c) - phiv(an, M, (-e + I)/c); my(x=matsolve(B,[real(p);imag(p)])[,1]); [round(x[1]+x[2]), round(x[1]-x[2]), abs(x[1]+x[2]-round(x[1]+x[2]))+abs(x[1]-x[2]-round(x[1]-x[2]))]};
f = fileopen("lev32b_out.txt","w");
for(k=1,24, c=32*k; for(a=1,c, if(gcd(a,c)!=1,next); r=rho(a,c); filewrite(f, Str(a," ",c," ",r[1]," ",r[2]," ",r[3]))));
fileclose(f);
