# Exact statistics for the frozen 198-variable result

These statements report finite polynomial facts only. Insert the independently reviewed arithmetic and Busy Beaver conclusions separately.

## A-based presentation matching the settled coefficient convention

Let `K0=31581660^28`, `H0=(5898050446009651968*K0)^2`, and `A=149^(2N+1)` for an integer N>=1. Conant's unbalanced table specifies a polynomial

```
P_A in Z[X,Y1,...,Y197]
```

which is a sum of 184 primitive integral quadratic squares. It has total degree four, integer content one, and exactly 2945 nonzero coordinate monomials. The coefficient of X^4 is one. Every coefficient is a polynomial in A of degree at most two; more precisely,

```
P_A = P_0 - 2*A*Y103 - 44402*A*Y103^2*Y115 + A^2*Y103^2,
```

where P_0 is the fixed integer polynomial obtained by setting A=0 in the complete coefficient table. Its coefficient height is

```
H(P_A)=max(H0,A^2)=max(H0,149^(4N+2)).
```

The second branch attains the maximum for exactly N>=53 among the allowed positive integers. This coefficient crossover does not certify a sufficient defining parameter. For the agreed notation `A=149^(2*BB(2^1000)+1)`, substitute `N=BB(2^1000)`; the legitimacy of that arithmetic specialization is a separate theorem.

## Balanced presentation, if explicitly stated with C

For `C=149^N`, the package's preferred balanced table is a polynomial in C with 198 total variables, 184 integral quadratic squares, degree four, content one, and exactly 2945 nonzero coordinate monomials for every N>=1. Its 2959 parameter-separated terms comprise 1697 constant profiles, 685 linear profiles, 549 quadratic profiles, and fourteen constant-plus-quadratic profiles. Its exact coefficient height is

```
max(H0,K0*C^2)=max(H0,31581660^28*149^(2N)),
```

with crossover N=57. It fixes the input and has the same rational input projection as the unbalanced table. Its coefficients are not polynomials in A=149*C^2 because some are nonzero linear polynomials in C. Its row 54 has content 149 after each allowed specialization, so "184 primitive quadratic squares" requires qualification for this presentation. The full quartic always has content one.

Both counts include the input X, leaving 197 existential rational variables. Neither fixed coefficient parameter is counted as a variable. These are two presentations of the frozen 198-variable construction; no further reduction or optimization is asserted.
