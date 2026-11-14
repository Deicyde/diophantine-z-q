# leaf-review-a, fork notes A2: r3, qmClassNumberOne, qmDenZeroCM3, x6ConicModel, qmHauptmodul

Line numbers are those of `scratch/leaf-fold3/Leaves3.lean`. No Lean was run. Numerical checks use
mpmath 1.3.0 (`~/bin/uv run --offline --with mpmath==1.3.0 python -I …`; `~/pyenv` does not exist on
this host). The scripts are `scratch/leaf-review-a/py/hauptmodul_check.py` and `py/linyang_tuple_check.py`.
Marks: VERIFIED = read, computed or numerically checked here; STANDARD = published; SPECULATIVE = a
judgement; UNVERIFIED = a locator recalled from memory.

## 1. r3 : `ZInQ.LeafPush2.R03_LinYang` (l.21402)

**Statement.** For every abelian surface `A/ℂ` with an injective unital `ι : 𝒪 → End(A)`
(`QMStr`, l.21254; `𝒪 = ℤ⟨1, i, (1+j)/2, (i+ij)/2⟩ ⊂ (2,−3)_ℚ`, l.21238): either there are `j ≠ 0`,
`a`, `r` (six distinct roots, `a ≠ 0`) with `[J₂:J₄:J₆:J₁₀](a∏(x−rᵢ)) = [12(j+1) : 6(j²+j+1) :
4(j³−2j²+1) : j³]` in weighted-projective form (`LinYangTuple`, scaling `t ≠ 0`), and a smooth proper
geometrically connected integral curve `C/ℂ` with function field `ℂ(x, y)`, `y² = a∏(x−rᵢ)`, whose
Jacobian is isomorphic to `A` as a group scheme; or `A ≅ E₁ × E₂` as schemes, with `E₁`, `E₂` elliptic.

**Definitions checked (VERIFIED, read).** `IC2`, `IC4`, `IC6`, `IC10` (l.21267-21287) are the
Igusa–Clebsch invariants of a sextic with all roots finite: the sums over `S₆` count each of the 15
matchings 48 times, each of the 10 triangle splits 72 times, and each of the 60 `I₆` terms 12 times,
which are the divisors used. `IC10` is the discriminant `a¹⁰∏_{i<j}(rᵢ−rⱼ)²`. `IgJ2`…`IgJ10`
(l.21297-21304) are Igusa's `J`'s: `J₂ = I₂/8`, `J₄ = (4J₂²−I₄)/96`, `J₆ = (8J₂³−160J₂J₄−I₆)/576`,
`J₁₀ = I₁₀/4096`. These are Igusa's 1960 formulas (STANDARD).

**Normalization check (VERIFIED numerically, 3 samples).** I compared the tuple with the
Hashimoto–Murabayashi family of discriminant 6, recalled from memory (Tohoku Math. J. 47 (1995);
UNVERIFIED): `y² = x(x⁴ − Px³ + Qx² − Rx + 1)` with `P = 2(s+t)`, `R = 2(s−t)`,
`Q = (1+2t²)(11−28t²+8t⁴)/(3(1−t²)(1−4t²))`, and `4s²t² − s² + t² + 2 = 0`. The root at ∞ was moved by
a Möbius map. At `t = 0.3`, `2.7` and `0.4+0.9i` I took `j = 3779136·I₁₀²/I₄⁵` from the data. The
weighted ratios `J₂²/J₄`, `J₂³/J₆` and `J₂⁵/J₁₀` of the HM curve then equal the tuple's ratios at that
`j` to 12 digits. So the tuple is right in Igusa's `J` convention, `J₆` included, and it is **not** an
Igusa–Clebsch tuple. Read as an `I`-tuple, `I₄⁵/I₁₀²` would not be a degree-one function of `j`.

**Source.** Lin–Yang, Math. Z. 295 (2020), arXiv:1807.00466v1, Example 29, eqs. (13)-(14); or
Baba–Granath, Canad. J. Math. 60 (2008), Prop. 3.6 (both UNVERIFIED locators). Also used: Lemma QP
(a principal polarization of the fixed type exists on every `(A, ι)` in characteristic 0; Rotger 2003,
2004, UNVERIFIED) and Weil's dichotomy (a principally polarized abelian surface over an algebraically
closed field is a Jacobian of a smooth genus-2 curve or a product of elliptic curves with the product
polarization; Weil 1957, UNVERIFIED).

**Verdict: CONSEQUENCE.** Derivation:
1. Give `(A, ι)` a principal polarization `L` of the type whose image in `A₂` is the Lin–Yang/HM curve.
   rv-qm-polar: there is one polarization of each type `c`, `c² = −6`. So whichever type the family
   uses, such an `L` exists.
2. The image of `X₆/W ≅ P¹` in the coarse space is `j ↦ [12(j+1) : … : j³]`. If `J₁₀ ≠ 0`, i.e.
   `j ∉ {0, ∞}`, then `(A, L) ≅ (Jac C, Θ)` for the genus-2 curve `C` with these invariants. `C` has a
   sextic model with six finite roots, and its `J`'s equal the tuple up to weighted scaling. This gives
   the first disjunct; the isomorphism of polarized surfaces is in particular an isomorphism of group
   schemes.
3. If `j ∈ {0, ∞}`, then `J₁₀ = 0`, and Weil's dichotomy gives `A ≅ E₁ × E₂`, the second disjunct.

The statement is existential in `C` and mentions no polarization, so it is no stronger than the
source. No repair is needed.

## 2. qmClassNumberOne : `G0Split.FibreQM.QMClassNumberOne` (l.63070)

**Statement.** Every discrete `Λ ⊂ ℂ²` with `IsZLattice ℝ Λ` (a full lattice) that is stable under
`ι(𝒪)` (`qmMat`, l.62560: pkg-I1's real embedding `ι(i) = diag(√2, −√2)`, `ι(j) = [[0,−3],[1,0]]`) has
the form `Λ = ι(𝒪)w`. Here `qmOrbit w` is the ℤ-span of `ι(b_k)w` over the basis `b_k` of `𝒪`
(l.62293), and `w` is not a complex multiple of a real vector.

**Definitions checked (VERIFIED, read).** `qmOrbit` uses `oBasis`, the same ℤ-basis as `InO`/`ofInt`,
so `qmOrbit w = ι(𝒪)w`. `qmMat` and `BPAnalytic.QM.iota` (l.36501) agree with pkg-I1's `iota`.

**Source.** Eichler's class number theorem. The maximal order of the indefinite quaternion algebra of
discriminant 6 has one class of left ideals (Vignéras, *Arithmétique des algèbres de quaternions*,
Cor. III.5.7; Voight, *Quaternion algebras*, Cor. 28.5.17; UNVERIFIED numbers).

**Verdict: CONSEQUENCE.** Derivation:
1. `ℚΛ` is a 4-dimensional left `B`-module. For any `v ∈ Λ∖0`, `b ↦ ι(b)v` is injective, because a
   nonzero `b` is invertible. So `ℚΛ = ι(B)v`.
2. Then `Λ = ι(I)v` for a lattice `I ⊂ B` with `𝒪I ⊆ I`. Since `𝒪` is maximal, `I` is an invertible
   left `𝒪`-ideal.
3. Class number one gives `I = 𝒪α`, so `Λ = ι(𝒪)w` with `w = ι(α)v`.
4. If `w = c·r` with `r` real, then `ι(𝒪)w ⊆ cℝ²` has real rank 2, which contradicts `IsZLattice ℝ Λ`.

No repair is needed.

## 3. qmDenZeroCM3 : `G0Split.FibreQM.QMDenZeroCM3` (l.62628)

**Statement.** If `jDen(Ω(τ)) = (Σ_{m even} θ_m(Ω(τ))⁸)⁵ = 0` for some `τ ∈ ℍ`, then `τ` is fixed by
`ι(x)` for some `x ∈ 𝒪` with `x² − x + 1 = 0`, i.e. a CM point of discriminant −3.

**Definitions checked.** `PkgI1.Omega`, `jDen`, `thetaConst` (l.240-330). `det F₀(τ) = −√2(τ−3)(τ+1)/2`
(VERIFIED by hand), so `F₀(τ)P⁻¹` is invertible on all of `ℍ` and Mathlib's junk inverse never
occurs. `Ω(τ)` is symmetric with positive-definite imaginary part (VERIFIED numerically at two CM
points; the eigenvalues of `Im Ω(√2+i)` are `0.5` and `1`). The theta series converge on `𝔥₂`, so
`tsum` has no junk value.

**Numerical facts (VERIFIED).**
- `g(τ) := Σθ⁸(Ω(τ)) / ((τ−3)(τ+1))⁴` satisfies `g(γτ) = (cτ+d)⁸ g(τ)` exactly for `γ = ι((1+j)/2)`,
  at two points.
- At `τ₀ = i√3`, `|Σθ⁸(Ω(τ₀+ε))|` scales like `ε²`: a zero of order 2 in `τ`, so `jDen` has a zero of
  order **10**. The docstring's "zero of order 30 in `τ`" is wrong. This is a docstring error only.
- `∏θ²` also vanishes to order 2 at `τ₀`, so `j_θ` has a pole of order `10 − 4 = 6` there, consistent
  with pkg-I1.

**Source.** The docstring cites Lin–Yang's divisor of `ψ₄` on `X₆/W` and calls itself "SPECULATIVE as
a reading". Better: the valence formula for cocompact Fuchsian groups (Shimura 1971, *Introduction to
the arithmetic theory of automorphic functions*, §2.4-2.6, UNVERIFIED), with the signature
`(0; 2,2,3,3)` of `𝒪¹` for discriminant 6 (STANDARD; e.g. Alsina–Bayer, *Quaternion orders, quadratic
forms and Shimura curves*, UNVERIFIED), and R4 (`ThetaModularity`).

**Verdict: CONSEQUENCE**, by the following derivation (the steps marked computation are not
literature facts):
1. For `γ ∈ 𝒪¹`, `Λ_{γτ} = (cτ+d)⁻¹ι(𝒪γ)v_τ`, and right multiplication by `γ` preserves the Riemann
   form `Trd(μ⁻¹xȳ)` because `n(γ) = 1`. So `Ω(γτ) = M_γ·Ω(τ)` with `M_γ ∈ Sp₄(ℤ)` (computation).
   With R4, `g` is a holomorphic weight-8 automorphic form for `𝒪¹`. The factor `(τ−3)(τ+1)` has no
   zero on `ℍ`, so `g` and `jDen∘Ω` have the same zeros.
2. `g ≢ 0` (numerically).
3. Valence formula: `Σ ord_P(g)/e_P = 8·(1/3)/2 = 4/3`, since `vol/2π = 1/3` for `(0;2,2,3,3)`.
4. At an elliptic point of order 3, a weight-8 form has `ord ≡ 2 (mod 3)` (as `E₈` at `ρ`). So each of
   the two order-3 points contributes at least `2/3`, which exhausts `4/3`.
5. Hence there are no other zeros. The stabilizers of the order-3 points are generated by order-6
   units `x`, `x² − x + 1 = 0`.

The statement is true as written. No repair is needed.

## 4. x6ConicModel : `X6Kummer.X6ConicModel` (l.75647)

**Statement.** There is a witness `(Y, Φ, X, Ψ, fY, π₆)` of `R1R2fpFullProps` (l.56226: R1fp repaired,
R1hecke, X6Props, R2X6Props with the values `0, ∞, −16/27` at the CM points of discriminants −4, −3,
−24, CMExists, R1rec, X6Surj, R5pt). It comes with a `Gal(ℚ̄/ℚ)`-equivariant bijection
`X(ℚ̄) ≃ C(ℚ̄)` for the conic `C : Y² + 3X² + 3Z² = 0`, under which `π₆ = −16(X²+Z²)/(27Z²)`
(`ConicModel`, l.75625).

**Checks (VERIFIED by hand).**
- `Y² + 3X² + 3Z² = 0` corresponds to `(−3,−3)_ℚ = (−1,−3)_ℚ`, Kurihara's `x² + y² + 3 = 0`. It is
  ramified at `{3, ∞}`: no real points, and none over `ℚ₃`.
- With `t = −X²/Z²` the three sign-change involutions generate `W`, and `C → C/W = P¹_t` has degree 4.
- `j = 16(t−1)/27` takes the values `−16/27`, `0`, `∞` at `t = 0`, `1`, `∞`, matching R2X6Props.

**Derivation independent of Elkies' printed constants.** `X₆ → X₆/W` is a `(ℤ/2)²`-cover defined over
`ℚ`, branched over the three CM points, each with `e = 2` (Riemann–Hurwitz: `Σ(e−1) = 6`). So the
function field is `ℚ(t)(√(αt), √(β(t−1)))`. The fibre fields fix the constants:
- Over `t = 1`, the points with CM by `ℤ[i]` (`h = 1`, no real points) lie over `ℚ(i)`, so `α = −1`.
- Over `t = ∞`, the points with CM by `ℤ[ζ₃]` lie over `ℚ(√−3)`, so `β = 3`.
- Over `t = 0` the field is then `ℚ(√−3)`, which matches González–Rotger Thm 5.12 for `ℤ[√−6]`
  (UNVERIFIED locator; rv-nocm checked 24 CM points).

This is exactly `Y² + 3X² + 3 = 0`.

**Source.** Kurihara, J. Fac. Sci. Univ. Tokyo 25 (1979) (the conic); Elkies, ANTS-III, LNCS 1423
(1998), §3 (`X*(6)` with coordinate `t` and `X₆ = X*(6)(√−t, √(3(t−1)))`). Both UNVERIFIED locators.

**Verdict: CONSEQUENCE** (Elkies' model with the Möbius change of coordinates `j = 16(t−1)/27`).
It is stated on one witness, existentially. It is true when the genuine Shimura-curve data satisfy
`R1R2fpFullProps`, which is r1r2's content. If `R1R2fpFullProps` were unsatisfiable, this field would
be false, not vacuous, so it cannot hide a gap. No repair is needed.

## 5. qmHauptmodul : `PkgI1.QMHauptmodul` (l.336), second opinion

**Ω normalization: correct (VERIFIED numerically).**
- `Ω(τ)` is symmetric with `Im Ω ≻ 0` at the CM points.
- `j_θ = 3779136(∏θ)⁴/(Σθ⁸)⁵ ∘ Ω` is invariant at a generic `τ`, to about `10⁻³⁵`, under `ι(j)`
  (det 3), `ι(2j+ij)` (det 6) and `ι((1+j)/2)` (det 1). So `j_θ` is invariant under Atkin–Lehner
  elements as well as `𝒪¹`.
- `j_θ(√2+i) = 0` to about `10⁻¹⁶²`, and `j_θ(i√(9+6√2)) = −0.592592592592593 = −16/27`.

**CM clauses: one Γ*-orbit each (VERIFIED by counting).**
- Optimal embeddings modulo `𝒪¹`: `h(R)∏_{p|6}(1 − (R/p))` gives 2 for each of `ℤ[i]`, `ℤ[ζ₃]`,
  `ℤ[√−6]` (Eichler; STANDARD). Every embedding is optimal, since all three orders are maximal.
- `X₆ → X₆/W` has degree 4 with `e = 2` at each of the three branch points, so each fibre consists of
  exactly these 2 points. So each clause is about a single `Γ*`-orbit.
- `x` and `−x` give the same Möbius map, so "for every `x`, every fixed `τ`" adds nothing beyond that
  orbit.

**Degree one: derivable, not only cited.**
- By §3, `jDen∘Ω` vanishes only on the `P₋₃` orbit, to order 10 in `τ`.
- `jNum` vanishes there to order 4 (numerically: `∏θ²` has order 2).
- So `j_θ` has a single pole on the compact genus-0 curve `Γ*\ℍ`, of order `6/6 = 1` in the local
  coordinate `(τ−τ₀)⁶`. Hence `j_θ` has degree 1, its fibres are exactly the `Γ*`-orbits, and it is
  surjective onto `P¹(ℂ)`.
- The value `−16/27` is a computation, or Baba–Granath's CM value for the Hauptmodul normalized by
  `0` at `P₋₄` and `∞` at `P₋₃`.

**Verdict: CONSEQUENCE** (composite, as the docstring says). The inputs are R4, the period
computation, the valence formula, the signature `(0;2,4,6)` of `Γ*` (`vol/2π = 1/12`), and the
Baba–Granath / Lin–Yang CM values. Two steps are computations VERIFIED only numerically (by pkg-I1
and by this check): `ord_{P₋₃}∏θ² = 2` and the exact value `−16/27`. The statement is no stronger
than the facts. No repair is needed.
