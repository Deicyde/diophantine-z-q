default(seriesprecision, 140);
P = 140;
u = q^-2 * eta(q^2+O(q^P))^2*eta(q^16+O(q^P))/(eta(q^4+O(q^P))*eta(q^32+O(q^P))^2);
x = u + 2; s = sqrt(x^2+4);
S = s*q^2;
R = S; e = vector(130);
for(m=1,130, c = polcoeff(R, m); if(c != 0, e[m] = -c; R = R / (1 - q^m + O(q^P))^(-c)));
for(m=1,130, if(e[m], print1("k=",m," e=",e[m],"; ")));
print();
