\\ TwN via the mod-2 Hecke reduction (cd-optimal report section 4): for d = 5 mod 8 squarefree,
\\ TwN(d) holds if S(A) = sum_{e | d} rho(A / (32 d^2 / e^2)) is not in (1+i) L_1 for some A coprime to 2d,
\\ where rho(a/c) = Phi_1(gamma tau) - Phi_1(tau), gamma in Gamma0(32), gamma oo = a/c (level 32 only).
\\ Coordinates in the basis (w1, w2) = E.omega of C_1 (w1 = Omega, w2 = -i Omega): (1+i)L_1 = {x + y even}.
default(realprecision, 30);
E = ellinit([0,0,0,-1,0]); w = E.omega; B = [real(w[1]), real(w[2]); imag(w[1]), imag(w[2])];
phiv(an, M, tau) = {my(q = exp(2*Pi*I*tau), s = 0., qn = 1.); for(n = 1, M, qn *= q; s += an[n]/n*qn); s};
rho(an, a, c) = {my(e = lift(Mod(a, c)^-1), M = ceil(c*6.0)+60); phiv(an, M, (a + I)/c) - phiv(an, M, (-e + I)/c)};
run(dmax) = {
  my(an = ellan(E, ceil(32*dmax^2*6.0) + 100));
  forstep(d = 5, dmax, 8, if(!issquarefree(d), next);
    my(found = 0, tried = 0, S, x, err);
    forstep(A = 1, 60, 2, if(gcd(A, d) != 1, next); tried++;
      S = sumdiv(d, e, rho(an, A, 32*d^2/e^2));
      x = matsolve(B, [real(S); imag(S)])[,1]; err = vecmax(abs(x - round(x)));
      if((round(x[1]) + round(x[2])) % 2 != 0, found = A; break));
    printf("d=%d tried=%d found_A=%d coords=%s err=%.1e\n", d, tried, found, round(x)~, err));
}
run(301);
