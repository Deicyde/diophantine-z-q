\\ Numerical period lattice Lambda_f of the newform f of C_d : y^2 = x^3 - d^2 x versus the period lattice
\\ L of C_d (PARI E.omega, differential dx/2y).  Psi(gamma) = phi_f(gamma tau) - phi_f(tau),
\\ phi_f = sum a_n/n q^n, gamma = [a,b;c,e] in Gamma0(N), tau = (-e+I)/c, gamma tau = (a+I)/c.
\\ Coordinates of Psi in the basis (w1,w2) of L; index of their span in Z^2 (1 means Lambda_f = L).
default(realprecision, 30);
phiv(an, M, tau) = {my(q = exp(2*Pi*I*tau), s = 0., qn = 1.); for(n = 1, M, qn *= q; s += an[n]/n*qn); s};
run(d, maxk, amax) = {
  my(E = ellinit([0,0,0,-d^2,0]), N = ellglobalred(E)[1], w = E.omega, w1 = w[1], w2 = w[2]);
  my(M = ceil(N*maxk*6.5) + 100, an = ellan(E, M), B = [real(w1), real(w2); imag(w1), imag(w2)]);
  my(vecs = List(), err = 0., g = 0);
  for(k = 1, maxk, my(c = N*k);
    for(a = 1, amax, if(gcd(a, c) != 1, next);
      my(e = lift(Mod(a, c)^-1), psi = phiv(an, M, (a + I)/c) - phiv(an, M, (-e + I)/c));
      my(x = matsolve(B, [real(psi); imag(psi)]), r = round(x));
      err = max(err, vecmax(abs(x - r))); listput(vecs, r)));
  for(i = 1, #vecs, for(j = i + 1, #vecs, g = gcd(g, matdet(matconcat([vecs[i], vecs[j]])))));
  printf("d=%d N=%d terms=%d max|coord-round|=%.2e index[L:span]=%d sample=%s\n", d, N, M, err, g,
    Vec(vecs)[1..min(4, #vecs)]);
}
