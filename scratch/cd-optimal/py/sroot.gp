default(seriesprecision, 60);
et(k) = eta(q^k + O(q^200)) * 1;  \\ eta without q^(k/24)
\\ u = eta(2)^2 eta(16)/(eta(4) eta(32)^2): q-power (2*2+16-4-64)/24 = -48/24 = -2
u = q^-2 * et(2)^2*et(16)/(et(4)*et(32)^2);
x = u + 2;
s2 = x^2 + 4;
print("x = ", x + O(q^12));
print("x^2+4 = ", s2 + O(q^12));
s = sqrt(s2);
print("s = ", s + O(q^20));
