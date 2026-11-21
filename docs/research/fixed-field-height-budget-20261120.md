# Fixed-field height budget for the frozen theorem

Status (2026-11-20, AI-READ): mathematical comparison and an integer-arithmetic
replay, against the definitions on fork main
[19f23e1fa](https://github.com/Deicyde/diophantine-z-q/tree/19f23e1fa7f6d77b70d7d1799ed681f06d9ef63f).
This is a comparison for the alternative height construction; the manuscript's
height decomposition on main is unchanged.

This addresses the dimension and constants questions in
[#104](https://github.com/Deicyde/diophantine-z-q/issues/104). The fixed-field
construction in
[nasqret/z-in-q-lean's height argument](https://github.com/nasqret/z-in-q-lean/blob/de33a32dc47dfdb1efa6c70d0b837bc6a5c9a2c6/docs/qualitative-existence.md)
reduces the non-CM part of Section 4 to a rational abelian variety. A coarse
dimension cap of 128 suffices; the sharper cap of 16 is unnecessary for the
numerical bound. Use the printed Theorem 6.2 directly, without the sharper bound
inside its proof.

### A common field of degree at most 64

Work with the field from the nasqret note. Write
`L = ℚ(i,a,b)` with `a²=2`, `b²=3`; put
`K=L(x,y,z)` with `x²=a`, `y²=b`, and `z²=1+ia`.
It is Galois of degree at most 64: it is the composite of `L` and the
splitting fields of `X⁴−2`, `X⁴−3` and `X⁴−2X²+3`. For the last polynomial
the four roots are `±z, ±b/z`. The discriminants of the three monic quartics
have support in `{2,3}` (for the last it is `3072`). The cyclotomic field
`L=ℚ(ζ₂₄)` has the same support bound. Thus `K/ℚ` is unramified outside
`{2,3}`. This uses the field's ramification, so an arbitrary primitive element
and primes dividing its polynomial's index need not enter the local argument.

Here is an elementary check of why this one field splits every rational
multiplier on `G=Gal(L/ℚ)`, with the trivial action on the coefficient group.
The kernel `C=Gal(K/L)` acts by signs on `(x,y,z)` and is central: each lift of
a base sign sends each radical to a multiple of itself with multiplier in
`L`. Lifts of the independent sign changes of `i,a,b` act on the three
radicals, up to signs, by
`(x,y,b/z)`, `(ix,y,b/z)`, `(x,iy,z)`, respectively.
Hence the commutators for the pairs `(i,a),(i,b),(a,b)` act by the sign
vectors `(1,0,0),(0,1,1),(0,0,1)`, with 1 denoting a minus sign. These
vectors form a basis. The computation is independent of the lift since `C`
is central.

For a rational multiplier `c` on `G`, the commutator is an alternating
bicharacter with values in `{±1}`. Choose the character of `C` with these
three values using the basis just computed. The character applied to the
extension cocycle of `Gal(K/ℚ)` gives a rational cocycle with the same
commutators, which is a coboundary when inflated to `Gal(K/ℚ)`. Indeed, if
`s` is the chosen section, take the cochain given by this character on the
`C` component of `k s(g)`. Dividing by that cocycle leaves a symmetric
cocycle on `G`. With coefficients in `ℚ̄×` it is a coboundary: in the
commutative extension, rescale lifts of the three generators by algebraic
square roots to make them of order two, giving a section. This proves the
claimed splitting without a computation of square-class independence or a
search for a splitting field.

The span of the splitting cochain values is a finite-dimensional domain
containing 1, and is closed under multiplication by the cochain equation with
rational `c`. It is therefore the coefficient field `E`, and
`m=[E:ℚ]≤|Gal(K/ℚ)|≤64`. With the geometric hypotheses for Guitart's
Proposition 2.10 and Corollary 2.12 in place, `A^m` is isogenous over `K`
to `B_K` for the rational factor `B/ℚ` of dimension `g=2m≤128`, with
the required field action. This field calculation does not establish the
geometric endomorphism and compatibility hypotheses on the Jacobians.

### Comparison with the actual coefficient in `SixContactMin`

Set `D=heightD`, `M=contactSupport(Mult.S_mul,u)`, and
`T=Mult.S_mul ∪ {p outside Mult.S_mul with odd contact at u}`, so
`N=∏_{p∈T}p=(∏_{p∈Mult.S_mul}p)M`. To apply the comparison at a non-CM
parameter, the geometric argument must give the isogeny above and good
reduction of that same `B` outside `T`. This support is for the original
height parameter: the change `s=5+120/u` is in `PGL₂(ℤ_p)` for `p>5`,
sends the six contacts to `∞,0,±1,±3`, and preserves their local
intersection orders. The primes 2, 3 and 5 already lie in `Mult.S_mul`.
The local test and the common polarized period in the nasqret argument are
still required for this application. In particular we use its bound
`h(R)≤84 max(1,h_F(B))+42 log deg φ+289200` and its rational coordinate
inequality `12h(u)≤h(R)+450+log(1024)`, for the invariant `R` of the
actual sextic and an isogeny between `B_K` and `A^m`.

* **Published height bound.** Von Känel, *The effective Shafarevich
  conjecture for abelian varieties of GL₂-type*, [Forum Math. Sigma 9 (2021),
  e39](https://doi.org/10.1017/fms.2021.29), p. 15, Theorem 6.2, gives
  `h_F(B)≤(3g)^{144g}N^{24}`. It applies to an abelian scheme of
  product GL₂-type over `Spec ℤ[1/N]`. Good reduction gives the abelian
  scheme, and the generic endomorphisms extend by the Néron property (compare
  the proof of Corollary 6.4 on the same page). Its stable height is in the
  original Faltings convention (metric in `2.1, p. 5). Equation (3.1), p. 6,
  gives the half-log-degree change after passing to a common semistable field.
* **Explicit isogeny transfer.** Apply Gaudron–Rémond,
  [*Polarisations et isogénies*](https://lmbp.uca.fr/`gaudron/art13.pdf),
  Duke Math. J. 163 (2014), Theorem 1.4, p. 2060, with `B_K` as the source
  and `A^m` as the target. Both isogenies are bounded by the source's
  `κ` (pp. 2058–2059; stable height in the original convention). With
  `d=[K:ℚ]` and `H=max(1,h_F(B))` this gives
  `deg φ≤[(14g)^{64g²} d max(h_F(B),log d,1)²]^{1024g³}`.
  Because `d≤64`, the inner maximum is at most `64H`, and `log H≤H`.
  Therefore `log deg φ≤C H` for
  `C=(1024·128³)(64·128²·11+18+2)`.
  There is no need to estimate the degree of the chosen descent isogeny.
* **Absorption at the frozen coefficient.** The preceding comparisons give
  `h(u)≤(84+42C+289200+450+10)(3·128)^{144·128}N^{24}`. The coefficient
  is at most `2^{167000}` (integer replay below). The theorem
  `Mult.le_heightD_of_mem_S_mul` bounds each prime of `Mult.S_mul` by `D`,
  so their product is at most `D^D`. Also `D≥3^{256·8⁴}≥2^{167000}`,
  since `heightF0=324!≥8`. With `heightE0≥2`,
  `2^{167000}D^{24D}≤D^{24D+1}≤D^{17D·heightE0}≤heightH6(D)`.
  The last inequality uses the `heightQ(D)^{17}` term in `heightH6`.

Run `python3 -B scratch/fixed-field-height/check_budget.py` to
check the integer comparisons, without evaluating `D`. This proves the
*conditional comparison with the exact coefficient*, not `SixContactMin`.
The remaining jobs are to establish the geometric endomorphism/descent data
on the actual fibres, identify their local models and common polarized
period, and cover all CM or other exceptional parameters at the same
coefficient. In particular a theorem that omits an unspecified finite set
cannot yet be applied to `SixContactMin`.
