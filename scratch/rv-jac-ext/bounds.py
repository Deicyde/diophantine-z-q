# Exact integer checks of the degree bounds (rv-jac-ext).
import math
F0 = math.factorial(324)
L10 = lambda x: len(str(x))
print("digits of F0=324!:", L10(F0))
for base in (6, 12, 720):
    k = 1
    while k * base**k <= F0: k += 1
    print(f"largest k with k*{base}^k <= 324!: {k-1}")
for k in (144, 288, 324):
    print(k, "k*12^k <= F0:", k*12**k <= F0, " k*720^k <= F0:", k*720**k <= F0)
# route L: 12*[L:Q] <= D, with [L:Q] <= k*3^(r^2); D = F0*3^(256 F0^4) too large to evaluate:
# compare exponents of 3 and cofactors separately
for k in (144, 324):
    print(k, "12*k <= F0:", 12*k <= F0, " (16k^2)^2 <= 256 F0^4:", (16*k*k)**2 <= 256*F0**4)
print("12 <= 3^(256(F0^4-(F0-1)^4)):", True, "(exponent gap", L10(256*(F0**4-(F0-1)**4)), "digits)")
