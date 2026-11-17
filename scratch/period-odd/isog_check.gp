\\ numeric check: lattice of C_d : y^2 = x^3 - d^2 x, L' = ((1+I)/2) L is a lattice of y^2 = x^3 + 4 d^2 x,
\\ and wp_{L'}(z) = wp_L(z) + wp_L(z+h), h = (1+I) w / 2, with wp_L(h) = 0.
d = 5; E = ellinit([0,0,0,-d^2,0]); om = E.omega; print(om);
w = om[1]; \\ real period
L = [w, I*w]; lam = (1+I)/2; Lp = [lam*w, lam*I*w];
Ep = ellinit([0,0,0,4*d^2,0]);
\\ g2 check: g2(L) = 4 d^2, so wp' ^2 = 4 wp^3 - g2 wp
z = 0.123 + 0.0456*I;
x = ellwp(L, z); dx = ellwp(L, z, 1)[2];
print("C_d eq: ", (dx/2)^2 - (x^3 - d^2*x));
h = (1+I)*w/2; print("wp(h) = ", ellwp(L, h + 1e-30));
X = ellwp(Lp, z); dX = ellwp(Lp, z, 1)[2];
print("E' eq: ", (dX/2)^2 - (X^3 + 4*d^2*X));
print("wp_L' - (x - d^2/x): ", X - (x - d^2/x));
y = dx/2;
print("wp'_L'/2 - y(x^2+d^2)/x^2: ", dX/2 - y*(x^2+d^2)/x^2);
print("wp(z+h) + d^2/x: ", ellwp(L, z+h) + d^2/x);
print("wp'(z+h)/2 - d^2 y / x^2: ", ellwp(L, z+h, 1)[2]/2 - d^2*y/x^2);
