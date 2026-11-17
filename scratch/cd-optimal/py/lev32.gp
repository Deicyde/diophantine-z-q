default(realprecision, 30);
phiv(an, M, tau) = {my(q = exp(2*Pi*I*tau), s = 0., qn = 1.); for(n = 1, M, qn *= q; s += an[n]/n*qn); s};
E = ellinit([0,0,0,-1,0]); w = E.omega; print("omega C1 = ", w);
an = ellan(E, 4000);
rho(a,c) = {my(e = lift(Mod(a, c)^-1), M = ceil(c*6.5)+60); phiv(an, M, (a + I)/c) - phiv(an, M, (-e + I)/c)};
B = [real(w[1]), real(w[2]); imag(w[1]), imag(w[2])];
for(k=1,4, c=32*k; for(a=1,40, if(gcd(a,c)!=1,next); p=rho(a,c); x=matsolve(B,[real(p);imag(p)]); printf("a=%d c=%d coords=%s\n",a,c,x~)));
