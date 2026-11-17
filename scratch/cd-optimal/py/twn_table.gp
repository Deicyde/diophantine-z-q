\\ parity table: for primes p = 5 mod 8 and odd A <= 31 coprime to p, bit(p, A) = parity of x+y for
\\ S = rho(A/(32p^2)) + rho(A/32) in the basis E.omega of C_1 (1 = not in (1+i)L_1).
default(realprecision, 30);
E = ellinit([0,0,0,-1,0]); w = E.omega; B = [real(w[1]), real(w[2]); imag(w[1]), imag(w[2])];
phiv(an, M, tau) = {my(q = exp(2*Pi*I*tau), s = 0., qn = 1.); for(n = 1, M, qn *= q; s += an[n]/n*qn); s};
rho(an, a, c) = {my(e = lift(Mod(a, c)^-1), M = ceil(c*6.0)+60); phiv(an, M, (a + I)/c) - phiv(an, M, (-e + I)/c)};
run(pmax) = {
  my(an = ellan(E, ceil(32*pmax^2*6.0) + 100));
  forprime(p = 5, pmax, if(p % 8 != 5, next);
    my(bits = List(), S, x);
    forstep(A = 1, 31, 2, if(A % p == 0, listput(bits, "."); next);
      S = rho(an, A, 32*p^2) + rho(an, A, 32);
      x = matsolve(B, [real(S); imag(S)])[,1];
      listput(bits, Str((round(x[1]) + round(x[2])) % 2)));
    printf("p=%d bits(A=1,3,..,31)=%s\n", p, concat(Vec(bits))));
}
run(109);
