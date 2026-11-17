default(seriesprecision, 200);
P = 200;
e(k) = eta(q^k+O(q^P));
x = q^-2*e(16)^6/(e(8)^2*e(32)^4);
s = q^-2*e(8)^5/(e(4)^2*e(16)*e(32)^2);
y = -q^-3*e(8)^4*e(16)^2/(e(4)^2*e(32)^4);
print("x^2+4-s^2 = ", x^2+4-s^2 + O(q^20));
print("y^2-x^3-4x = ", y^2-x^3-4*x + O(q^20));
x1 = (x+s)/2; x1b = (x-s)/2;
print("x1 = ", x1 + O(q^40));
print("x1b = ", x1b + O(q^40));
\\ product expansion of x1*q^2 (exponents of (1-q^m))
R = x1*q^2; ex = vector(190);
for(m=1,190, c = polcoeff(R, m); if(c != 0, ex[m] = -c; R = R / (1 - q^m + O(q^P))^(-c)));
print("x1 prod exps: ", vector(64,m,ex[m]));
R = -x1b/q^2; ex = vector(190);
print("x1b lead: ", -x1b/q^2 + O(q^10));
for(m=1,190, c = polcoeff(R, m); if(c != 0, ex[m] = -c; R = R / (1 - q^m + O(q^P))^(-c)));
print("x1b prod exps: ", vector(64,m,ex[m]));
