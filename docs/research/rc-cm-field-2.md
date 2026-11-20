# CM field descent on the normalized modular curve

**Result (verified in Lean).** Every proper ideal singular modulus is
integral over ℤ and has degree at most `Nat.card (Pic O)` over ℚ and over
the embedded quadratic field. All the singular moduli of the order lie in
one embedding of `ringClassField O` extending the given quadratic
embedding. For each eligible Heegner form, both plane coordinates descend
in that one embedding. The field-of-definition statement holds
unconditionally at level one. At general level the sole remaining
comparison is `BranchDescends N`: the specified branch of the normalization
must descend over that field. No new literature print is used.

**Scope correction (verified against the manuscript).** The Lean target quantifies over all imaginary quadratic orders and eligible forms, with a complex embedding chosen per form. Tex 2839–2844 and 2915–2916 concern a field split at $2N$, exclude the two fields with extra units, and choose compatible lattices and fixed orientations. The Lean target's discriminant is $f^2D_K$; the subscript in the manuscript denotes the conductor. For an eligible form, $d\equiv B^2\pmod{4N}$ already enforces splitting at the odd primes dividing $N$, and at 2 when $N$ is even; for odd $N$ there is no separate splitting assumption at 2. The broader Lean scope is not supported by that passage alone. No counterexample to the Lean target is known here.

**Correction to the proposed branch argument.** The nonvanishing denominator in `X0Branch.exists_analyticJN_ratio` expresses the second plane coordinate in terms of sections on the normalization. Going from the plane pair to the normalization needs expressions in the opposite direction, or a different descent argument.

The [results log](../../scratch/rc-cm-field-2/log.md) records the sizing done
before compilation. Root membership and the $\psi(N)$ count needed a
generic distinctness argument; Tau Ceti supplied `Pic O` and split-prime
comparison, but the lattice-to-ideal dictionary and Frobenius comparison
with singular moduli needed proofs. The fork's Fowler bridge supplied
a model for proper-to-invertible fractional ideals. The existing
`KroneckerCongruence` was just an identity of polynomials over
`ZMod p`; it was small enough to prove from the integral Laurent expansion.
There is no `CMFieldOfDefinition` row in `docs/one-proof/kinds.tsv` or
`docs/one-proof/OPEN.md` at the merged base. No autofold or dry run applies.

### Algebraic integrality

For an invertible fractional ideal, take its embedded period lattice and
a basis `[1,ω]` of the order. The element `n+ω` is primitive in the
multiplier order. Its multiplication image has cyclic quotient: Smith
normal form identifies cyclicity with the absence of any common divisor
of the entries of the multiplication matrix. Invertibility gives that
divisibility of the matrix would also divide the scalar in the order.
The index equals the squared complex norm. For large positive `n`, the
quadratic norm lies strictly between consecutive squares, after shifting
`n` by the integral part of half the trace. At such a level the modular
polynomial's diagonal has unit leading coefficient and kills the
unchanged j-value; dividing by that coefficient gives a monic equation
over ℤ. This argument is on the spot (c) and is fully verified in Lean.

### Exact order and multiplicities

Root membership and the degree count do not by themselves control multiplicities
when j-values collide. For a transcendental parameter, equality of two translate
values gives an `SL₂(ℤ)` equivalence. Clearing denominators gives a quadratic
over ℚ; all its coefficients must vanish. The lower-left matrix entry is then
zero, and the bounds on the upper-right entries of the triangular representatives
force equality of the representatives. Consequently the factors are distinct
there. Both polynomial evaluations are continuous in the parameter, so equality
extends to the whole upper half-plane.

The root support itself recovers the exact order. A cyclic self-sublattice
is the image of a primitive scalar of norm its index, and any such scalar
gives a diagonal root. Here primitive means the two coefficients have gcd
one in an integral basis of the multiplier order; both directions follow
from Smith normal form and the definition of the multiplier ring. A
nonsquare index supplies a nonreal multiplier. To construct a basis
`[1,ω]`, evaluate multipliers at the first period and take the second
coefficient in the lattice basis. The image is a principal ideal of ℤ
and the kernel consists of rational integers. The index of multiplication
by `ω` is its squared complex norm, and the same index for `1+ω`
also gives its integral trace. Translate `ω` by an integer to normalize
the trace `t` to 0 or 1.

For norm `u ≥ 2`, the least nontrivial primitive norm is `u`.
The norm of `a+bω` is `(a+bt/2)²+b²(u−t²/4)`. For `|b| ≥ 2`
this exceeds `u+1`; for `|b| = 1` the level `u+1` is present for
trace zero and absent for trace one. The orders with `u = 1` are
distinguished from those with `u ≥ 2` by levels 2 through 5 and
elementary congruences modulo 2, 3 and 4. Once the two parameters agree,
the generators coincide or are exchanged by `ω ↦ t−ω`, which gives
the very same subring of ℂ. This identifies the multiplier order of
every conjugate via the Galois invariance of diagonal roots.
The ideal dictionary then provides a proper invertible fractional ideal
in the specified order. Counting conjugates by its Picard group bounds
the degree. This argument does not use the degree or class-polynomial
formula as an input.

### Split-prime route to inclusion

The tree does contain the required split-prime test:
`ncard_primesOver_ringClassField_eq_finrank_iff` in
`ZInQKernel/Contrib/TauCeti/NumberTheory/ClassFieldTheory/ClassFields/RingClass/Field.lean`
(VERIFIED). A conductor-prime-to prime of the full ring of integers splits
completely in the ring class field exactly when it is generated by an element
of the order. Thus the following route to *inclusion* does not need to identify
the two oriented Frobenius factors or assume that conjugacy acts by translations
in the Picard group (on the spot (c), verified in Lean). These stronger
reciprocity statements are not needed for membership.

Take a finite Galois extension of ℚ containing the embedded ring class field
and the given integral j-value. For each automorphism fixing the ring class
field, use Chebotarev over ℚ to realize that element as Frobenius at a prime
outside the conductor, ramification and the primes dividing the norm of
the difference of that j-value from its conjugate if the difference is nonzero.
The rational prime splits in the quadratic field, since Frobenius fixes that
field. Its degree-one prime in the quadratic field splits completely in the
ring class field. Use the splitting criterion to produce a multiplier of norm
the rational prime. On every invertible fractional ideal, that multiplier gives
a cyclic self-isogeny of prime degree `p`, hence `Φₚ(j,j)=0`. On the
diagonal, Kronecker's congruence reduces this to
`−(jᵖ−j)²=0` in the residue field. Thus the Frobenius fixes the reduction
of the chosen j-value, and the choice of prime implies that it fixes the value
itself. The fixed-field theorem then puts the value in the ring class field.

The polynomial input needed here is only the **diagonal** congruence.
`Kronecker.lean` proves the entire vendored `KroneckerCongruence` (VERIFIED
in Lean). The integral Laurent-series equation reduces to a root at
`Y=Xᵖ` by Frobenius and transcendence of the Laurent series. Prime-level
symmetry gives the other factor. After removing the factor `Yᵖ−X`,
specialization at `Y=Xᵖ` is nonzero on that factor, so the remaining
polynomial is divisible by `Y−Xᵖ`. The degree and monicity then
determine the product. The same file proves the diagonal consequence
over any residue field of characteristic `p`.

### The remaining comparison

`BranchDescends N` fixes an imaginary quadratic order, a complex embedding
of its ring class field over the quadratic field, and an eligible form
`[A,B,C]`. Under simultaneous singular modulus membership in that
embedding, it asks that every regular function on the finite j-chart,
evaluated at `cmPoint A B d`, land in the same embedded ring class field.
`fieldPoint_iff_finitePointEval_range` proves this is exactly the test
for descent of the chosen point over a **fixed** embedding.
`finiteChart_finiteTest` reduces the check to a fixed finite set of module
generators at each level, since the functions from the j-line already
descend. At level one they are all the functions on the finite chart.

At a point where each of these sections can be written as a rational
function of the plane pair with a denominator nonzero at the point,
the two coordinates suffice; `fieldPoint_of_eval_rational_in_coordinates`
proves this for the regular sections, or one can apply its range argument
to the finite set of generators. There is such a test off a finite set
of first j-values: express the chosen generators in powers of the second
coordinate with coefficients in ℚ(j), then clear the finitely many
denominators in ℚ[j]. The germ comparison and regularity identify these
expressions with the chart evaluations wherever the denominators are
nonzero. This uses denominators for the **inverse** comparison. The
second coordinate itself is integral over ℚ[j] and is a regular function
on the normalized finite chart, so a forward ratio for it can even use
denominator one. In particular a simple root of the
specialized modular polynomial lies in the étale locus of the plane
model over the j-line: invert its derivative in the second variable.
The plane presentation uses the monic minimal polynomial of the second
generator. On that open the plane ring is normal, and its normalization
is an isomorphism there, so the plane pair specifies a point over the
embedded field. The finite exceptional set and simple-root arguments
are on the spot (c); the checked local Lean criterion starts with the
rational expressions. When plane values collide, a proof can instead
identify the normalized point with its oriented cyclic subgroup on a
CM elliptic curve. That specialized moduli comparison is missing here;
neither the single ratio for the second coordinate nor the arithmetic
comparison alone provides it.

### Known issues

- **Level two (VERIFIED in Lean).** The forms `[2,1,1]` and `[2,−1,1]`
  are eligible and −7 is prime to 2. Put
  `τ₊=(−1+i√7)/4` and `τ₋=(1+i√7)/4`. Translation relates the
  doubled parameters, and inversion sends `τ₊` to `2τ₋` and
  `τ₋` to `2τ₊`, so the two plane coordinates coincide. If a
  matrix with entries `a,b,c,e` carries `τ₊` to `τ₋`, substitute
  `τ₋=τ₊+1/2` and `τ₊²=−τ₊/2−1/2` into the equation. The
  imaginary and real parts give `a=e` and `2b=e−c`. If
  `c` is even, `e` is even too, which contradicts the determinant
  being one. The separate `middleCoefficient_mod_four` checks the
  transformation invariant: the transformed middle coefficient of a
  form with even leading coefficient is congruent to the old one
  modulo four for a change of variables in $\Gamma_0(2)$.
- The broader quantifier in the Lean field-of-definition statement is not
  literally supplied by the manuscript passage. The manuscript works with the
  split Heegner hypothesis and a compatible system of orientations, whereas
  the Lean conclusion for a single form allows its own embedding.
- **Reflection (checked on the spot (c)).** Lean verifies
  $-\bar\tau_+=\tau_-$. The existing
  `X0Model2.sectionExpansion` proves that regular functions on the finite
  chart pull back to meromorphic functions with rational Laurent expansions
  and gives their values at the complex points. Since
  $q(-\bar z)=\overline{q(z)}$, a pullback $g$ and
  $z\mapsto\overline{g(-\overline z)}$ agree near the cusp; the meromorphic
  identity theorem gives $g(-\bar z)=\overline{g(z)}$ at regular points.
  Hence the finite chart evaluations of the two points are complex
  conjugates and determine the exchanged scheme points. This compatibility
  with conjugation is an on-the-spot argument and was not compiled.
  The reduced form enumeration has $A\le\sqrt{7/3}<2$ and with the
  usual boundary sign convention gives just `[1,1,2]`; the class
  number is one (computed). The exchange is consistent with two distinct
  $\mathbf Q(\sqrt{-7})$-points because conjugation acts nontrivially on that
  field. It does not exhibit their coordinates over that field by itself.
- A different route to the branch comparison is to descend the elliptic curve
  with the given j and descend its cyclic subgroup as the common kernel of a
  CM ideal. In characteristic zero the scalar on invariant differentials
  detects a nonzero endomorphism, so an action fixing the embedded CM field
  fixes the CM endomorphisms. To exploit this here one still needs the moduli
  identification of the resulting oriented cyclic subgroup with the specified
  point on `X0Branch.model`. This is a proposed formal route, not a Lean
  proof of that identification.

### The oriented lattice product

For the form `[A,B,C]`, write `A=Na` and
`ω=(−B+i√(−d))/2`. Its scaled parameter is the root for `[a,B,NC]`.
The latter form is primitive: any common divisor of `a,B,NC`
is prime to `N` (a common divisor of `B,N` would divide `d`), hence
divides `a,B,C` and then `A,B,C`. The product of the lattices
`(N,ω)(a,ω)` is contained in `(A,ω)` because
`ω²=−Bω−AC`; conversely it contains `A`, `Nω`, and
`Bω=−ω²−AC`. Bézout for `N,B` supplies `ω`.
In the order generated by `1,ω`, the form ideal `(A,ω)` times its
conjugate is `(A)`: the four generators give multiples of `A`,
and (A^2,AB,AC) generate `A` by primitivity. The same argument
gives invertibility for the scaled and level ideals. Thus the
second lattice represents the inverse translate by the oriented level ideal.

### Lean statements

The declarations are in `ZInQ.Manuscript.RC.CMField2`. The
[statement check](../../scratch/rc-cm-field-2/Check.lean) prints the types
of the public theorems and the full definitions of the four comparisons,
including the three proved on the way to descent. See its
[Lean output](../../scratch/rc-cm-field-2/statements.txt) for the exact types.
All 29 new modules and the statement check passed `lake env lean`.
The [axiom audit](../../scratch/rc-cm-field-2/axioms.txt) records 153 checks,
covering every new theorem with only `propext`, `Classical.choice` and
`Quot.sound` or a subset. The import audit found no prohibited dependency.

| Statement | Conclusion |
| --- | --- |
| `singularModulus_isIntegral` | A singular modulus of a proper invertible ideal is integral over ℤ. |
| `singularModulus_finrank_le`, `singularModulus_finrank_over_base_le` | Adjoining a singular modulus over ℚ, or over the quadratic field via its specified embedding, gives degree at most `Nat.card (Pic O)`. |
| `singularModulus_finrank_le_of_primitive_equation` | The same bound over ℚ for `analyticJ τ`, when τ solves a positive-leading primitive equation of discriminant `O.discr`. |
| `ConjugateSingularModulus`, proved by `conjugateSingularModulus` | Every ℚ-embedding of the simple field generated by a singular modulus sends its generator to a singular modulus of another invertible proper fractional ideal of the same order in the same embedding. |
| `ExactMultiplierOrderOfDiagonalMultiplicities`, proved by `exactMultiplierOrderOfDiagonalMultiplicities` | A period lattice with the same specialized diagonal root multiplicities as an ideal lattice has exactly that ideal lattice's embedded multiplier order. The proof needs only equality of root support. |
| `SingularModulusMemRingClass`, proved by `singularModulusMemRingClass` | For each given quadratic embedding into ℂ there is one compatible complex embedding of the ring class field containing every proper ideal singular modulus of the order. |
| `heegner_coordinates_mem_ringClass` | The two plane coordinates of an eligible form lie in the image of a single complex embedding of the ring class field. |
| `BranchDescends N`, proved as `branchDescends_one` at level one | Over a compatible embedding containing all proper ideal singular moduli, every regular section on the finite j-chart evaluates in that embedding's image at the chosen branch. |
| `cmFieldOfDefinition_modelOne`, `cmFieldOfDefinition_one` | `PreparedParam.CMFieldOfDefinition` for the level-one model and for the normalized branch model at level one. |
| `cmFieldOfDefinition N` | `BranchDescends N → PreparedParam.CMFieldOfDefinition (X0Branch.model N)`. |
| `levelTwo_heegner`, `levelTwo_coordinates`, `levelTwo_distinct`, `levelTwo_reflection` | The two forms pass the Heegner and coprimality checks, give the same plane pair and distinct normalized points, and have reflected parameters. |

The specialized product is `modularPolynomial_eq_coset_product`: for every
upper half-plane parameter, the monic specialization at its j-value is the
product over primitive triangular coset representatives, including repeats.
`exists_cyclic_sublattice_of_modularPolynomial_root` supplies a lattice
for each root, and `diagonal_root_iff_primitive_norm` characterizes the
root support for self-isogenies. The path to inclusion uses
`kroneckerCongruence_of_prime`, `splitPrime_of_frob_fixes_ringClass`, and
`singularModulus_reduction_pow_eq_of_split`, respectively the prime-level
congruence, the splitting implication for Frobenius, and the fixed residue
of a singular modulus. The oriented-ideal comparison is
`formIdeal_scaled_eq_levelInverse_mul`, the fractional-ideal form of the
lattice product above.

### Manuscript check

| Lines | Verdict | Check |
| --- | --- | --- |
| 2836–2838 | OK | The field-of-definition step is on the modular curve; passage to the normalized modular parametrization is subsequent. |
| 2839–2844 | OK | These are the actual splitting, unit and conductor assumptions; the class field is indexed by conductor. |
| 2915–2916 | gap filled | Lean proves the lattice product, simultaneous ring class membership and descent of both plane coordinates; it closes the field-of-definition step at level one. |
| 2915–2916 | unverified | At general level, the normalized branch and compatibility of the chosen orientations across conductors still need comparison. A reference for the wider Lean scope was not read. |
| 2917–2919 | unverified | The image under the stated rational map is formal once a point descends; the Cai–Chen–Liu identification and reduction of their condition were not read. The manuscript's locator is Theorem 2.15; its cited §2 comparison is UNVERIFIED. |
| 8209–8212 | OK | The passage explicitly restricts to odd fundamental discriminants, splitting at $2N$, and no extra units. It does not assert the broader Lean quantifiers. |
| 8213–8217 | unverified | The conductor-one trace expression uses chosen ideal class points. This work does not formalize their compatible action or the sum. |

`CMjDegreePrint` on fork main asserts equality for the degree of a singular
modulus over ℚ and uses `FowlerBridges.properClassNumber`. The new
`singularModulus_finrank_le_of_primitive_equation` uses the same analytic
input (an upper half-plane root of a primitive integral quadratic) and proves
the upper bound in terms of `Nat.card (Pic O)`, the number of proper classes.
The degree proof uses neither the print nor the consumer giving the opposite
inequality for a field of definition. The separate inclusion proof uses
Frobenius and does not use a degree formula.
