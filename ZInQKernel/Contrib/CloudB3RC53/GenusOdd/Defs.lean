import ZInQKernel.Contrib.CloudB3RC53.Basic
import ZInQKernel.Contrib.CloudB3RC53.Prints.CST
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.BaseChange

/-!
# GenusOdd: the genuine objects of the genus lower bound (Section 7, tex L2403–2439)

Definitions only (and a few PROVED facts about them). They are the objects of Proposition
`ex:sec7-genus-lower` of `diophantine_zq.tex` (tex L2403–2458):

* `Lval E`: the value at `s = 1` of the entire continuation of `L(E, s)` (unique when it exists,
  `Lval_eq`), and `Lderiv E` its derivative at `s = 1`.
* `omegaMinus Lat`: the least positive `t` with `i t ∈ Lat` (the imaginary period `|Ω^-|` of the
  period lattice `Lat` of `E`, CST's `IsLatticeOf`).
* `Lstar E Lat d = √|d| L(E^{(d)}, 1) / |Ω^-|`: the normalized central value `L_*(d)` for `d < 0`
  (tex L1826–1830, L7176–7177: `L_*(h) = √|h| L(E^h,1)/|Ω_E^ε|`, `ε` the sign of `h`).
  `HasTwoAdicVal x v`: `x` is a nonzero rational number of 2-adic valuation `v`; this is how a
  valuation of `L_*` is stated (rationality is Manin–Drinfeld and is never assumed silently).
* `chiD d n = (n / |d|)` (Jacobi symbol): the Kronecker character `χ_d(n)` for a discriminant
  `d ≡ 1 (mod 4)`, the only case used here (all discriminants of (3.4) are odd).
* `IsQuadRingClassChar K c d χ`: `χ : Pic(O_c) → ℂ^×` is quadratic and equals `χ_d ∘ N_{K/ℚ}` on the
  primes of `K` prime to the conductor and to `d` (the genus character of (O.1), tex L8213–8217,
  with `d = h_*`, `c = 1`; the ring-class character "weighted by `χ_h`" of tex L2414, with `d = h`,
  `c = |h|`).
* `heegnerSum`: the unaveraged sum `P_χ = Σ_{t ∈ Pic(O_c)} χ(t) σ_t(y)` of tex L2411–2414 and (O.1),
  over the Artin images `σ_t ∈ Gal(H_c/K)` (`ringClassArtinEquiv`), for quadratic `χ`, as an
  honest point of `E(H_c)`.
* `eigenLattice`: the `χ`-eigen subgroup `{x ∈ E(H_c) : σ x = χ(σ) x for all σ ∈ Gal(H_c/K)}`, the
  "native rank-one lattice" of tex L2415, L2433–2434, L9426–9427.
* `twoDivIndex M x`: the largest `e` with `x ≡ 2^e G` modulo torsion for some `G ∈ M` (`⊤` if there
  is no largest), the "index valuation" of tex L2416 (`P = m G + T`, `j = v₂ m`, tex L9422–9425).

The Heegner point is the complex-analytic model of `Prints/CST.lean`: any `y ∈ E(H_c)` whose image
under an embedding `ι : H_c → ℂ` is `φ(τ)` for the CM point `τ` of a Heegner form. The algebraic
Heegner point `x_c ∈ X₀(N)(H_c)` is not available (see `Prints/CST.lean`).
-/

noncomputable section

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory IsDedekindDomain Complex

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open ZInQ.Contrib.CloudB3RC53.CST

/-! ### Central values -/

/-- Two entire continuations of `L(E, s)` coincide (identity theorem; PROVED). -/
theorem IsLContinuation.unique {E : WeierstrassCurve ℚ} {F G : ℂ → ℂ}
    (hF : IsLContinuation E F) (hG : IsLContinuation E G) : F = G := by
  have hFa : AnalyticOnNhd ℂ F Set.univ := analyticOnNhd_univ_iff_differentiable.mpr hF.1
  have hGa : AnalyticOnNhd ℂ G Set.univ := analyticOnNhd_univ_iff_differentiable.mpr hG.1
  refine AnalyticOnNhd.eq_of_eventuallyEq hFa hGa (z₀ := 2) ?_
  have hopen : IsOpen {s : ℂ | 3 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : (2 : ℂ) ∈ {s : ℂ | 3 / 2 < s.re} := by norm_num
  filter_upwards [hopen.mem_nhds hmem] with s hs
  rw [hF.2 s hs, hG.2 s hs]

open Classical in
/-- **`L(E, 1)`**: the value at `s = 1` of the entire continuation of Mathlib's `L(E, s)` (junk `0`
if there is none; the continuation is unique, `IsLContinuation.unique`). -/
def Lval (E : WeierstrassCurve ℚ) : ℂ :=
  if h : ∃ F, IsLContinuation E F then Classical.choose h 1 else 0

open Classical in
/-- **`L'(E, 1)`**: the derivative at `s = 1` of the entire continuation (junk `0` if none). -/
def Lderiv (E : WeierstrassCurve ℚ) : ℂ :=
  if h : ∃ F, IsLContinuation E F then deriv (Classical.choose h) 1 else 0

theorem Lval_eq {E : WeierstrassCurve ℚ} {F : ℂ → ℂ} (hF : IsLContinuation E F) :
    Lval E = F 1 := by
  have h : ∃ F, IsLContinuation E F := ⟨F, hF⟩
  rw [Lval, dite_eq_left_of_eq_true (eq_true h), IsLContinuation.unique (Classical.choose_spec h) hF]

theorem Lderiv_eq {E : WeierstrassCurve ℚ} {F : ℂ → ℂ} (hF : IsLContinuation E F) :
    Lderiv E = deriv F 1 := by
  have h : ∃ F, IsLContinuation E F := ⟨F, hF⟩
  rw [Lderiv, dite_eq_left_of_eq_true (eq_true h), IsLContinuation.unique (Classical.choose_spec h) hF]

/-! ### Periods and the normalized central value `L_*` -/

/-- **The imaginary period `|Ω^-|`** of a lattice: the least positive `t` with `i t ∈ Lat` (`0` if
there is none; for the period lattice of an elliptic curve over `ℚ`, which is stable under complex
conjugation, there is one). The manuscript fixes the periods "by `π` and the integral lattice"
(tex L1826–1827) "up to the fixed rational period comparison" (tex L7177); any fixed choice cancels
in (3.4), where both `L_*` values have negative argument. -/
def omegaMinus (Lat : PeriodPair) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ (t : ℂ) * I ∈ Lat.lattice}

/-- **The normalized central value** `L_*(d) = √|d| L(E^{(d)}, 1) / |Ω^-|` (tex L1826–1830,
L7176–7177, in the convention for `d < 0`, the only one used by (3.4): `hk' < 0`, `h_* < 0`).
Complex-valued as defined; it is rational by Manin–Drinfeld, which is not assumed: valuation
claims are stated through `HasTwoAdicVal`. -/
def Lstar (E : WeierstrassCurve ℚ) (Lat : PeriodPair) (d : ℤ) : ℂ :=
  ((Real.sqrt |(d : ℝ)| : ℝ) : ℂ) * Lval (qtwist E d) / ((omegaMinus Lat : ℝ) : ℂ)

/-- `x` is a nonzero rational number with 2-adic valuation `v`. -/
def HasTwoAdicVal (x : ℂ) (v : ℤ) : Prop :=
  ∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) = x ∧ padicValRat 2 q = v

open Classical in
/-- `L_*(d)` as a rational number when it is one (junk `0` otherwise): the `Lstar : ℤ → ℚ` of the
`RCData` interface (`RCData.Lstar`). -/
def LstarQ (E : WeierstrassCurve ℚ) (Lat : PeriodPair) (d : ℤ) : ℚ :=
  if h : ∃ q : ℚ, (q : ℂ) = Lstar E Lat d then Classical.choose h else 0

theorem LstarQ_spec {E : WeierstrassCurve ℚ} {Lat : PeriodPair} {d : ℤ}
    (h : LstarQ E Lat d ≠ 0) : (LstarQ E Lat d : ℂ) = Lstar E Lat d := by
  unfold LstarQ at h ⊢
  split_ifs with h'
  · exact Classical.choose_spec h'
  · exact absurd (dite_eq_right_of_eq_false (eq_false h')) h

theorem hasTwoAdicVal_LstarQ {E : WeierstrassCurve ℚ} {Lat : PeriodPair} {d : ℤ}
    (h : LstarQ E Lat d ≠ 0) :
    HasTwoAdicVal (Lstar E Lat d) (padicValRat 2 (LstarQ E Lat d)) :=
  ⟨_, h, LstarQ_spec h, rfl⟩

/-! ### Quadratic characters -/

/-- **`χ_d(n)`** for a discriminant `d ≡ 1 (mod 4)`: the Jacobi symbol `(n / |d|)` (for such `d`
the Kronecker symbol `(d / n)` equals `(n / |d|)` by quadratic reciprocity). -/
def chiD (d : ℤ) (n : ℕ) : ℤ := jacobiSym n d.natAbs

section RingClass

variable (K : Type) [Field K] [NumberField K] (c : ℕ) [NeZero c]

/-- **`χ = χ_d ∘ N_{K/ℚ}` on `Pic(O_c)`**: `χ` is quadratic, and `χ([𝔭]) = χ_d(N𝔭)` for every prime
`𝔭` of `K` prime to the conductor of `O_c` and to `d`. For `c = 1`, `d = h_*` and
`disc K = h h_*` this is the genus character of (O.1) (tex L8213–8217, `χ_{h_*}(N𝔞)`); for
`c = |h|`, `d = h` and `disc K = k'` it is the ring-class character "weighted by `χ_h`" of tex
L2414. The values at the remaining primes are forced by the group structure (every class contains
primes prime to any given integer). -/
def IsQuadRingClassChar (d : ℤ) (χ : Pic (conductorOrder K c) →* ℂˣ) : Prop :=
  (∀ t, χ t * χ t = 1) ∧
    ∀ (𝔭 : HeightOneSpectrum (𝓞 K))
      (h : 𝔭.asIdeal ∈ integralIdealsPrimeTo (conductorOrder K c).conductorModulus),
      (d : 𝓞 K) ∉ 𝔭.asIdeal →
        ((χ ((conductorOrder K c).picClass ⟨𝔭.asIdeal, h⟩) : ℂˣ) : ℂ) =
          (chiD d (Ideal.absNorm 𝔭.asIdeal) : ℂ)

variable {K c}

open Classical in
/-- The sign `χ(t) ∈ {±1}` of a quadratic character, as an integer. -/
def chiSign (χ : Pic (conductorOrder K c) →* ℂˣ) (t : Pic (conductorOrder K c)) : ℤ :=
  if ((χ t : ℂˣ) : ℂ) = 1 then 1 else -1

variable (E : WeierstrassCurve ℚ) [DecidableEq (ringClassField (conductorOrder K c))]

/-- The Galois action of `σ ∈ Gal(H_c/K)` on `E(H_c)`. -/
abbrev galPt (σ : ringClassField (conductorOrder K c) ≃ₐ[K] ringClassField (conductorOrder K c)) :
    (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point →+
      (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point :=
  WeierstrassCurve.Affine.Point.map (W' := E.toAffine) (σ.toAlgHom.restrictScalars ℚ)

/-- **The unaveraged Heegner sum** `P_χ = Σ_{t ∈ Pic(O_c)} χ(t) σ_t(y)` (tex L2411–2414, (O.1)
L8213–8217) for a quadratic `χ`, summed over `σ ∈ Gal(H_c/K)` with `t` its Artin preimage: no
`1/|Pic|`, no `1/u`. For the genus point `y` is the conductor-one Heegner point, for the ring-class
point the conductor-`c` one (the analytic model of `Prints/CST.lean`). -/
def heegnerSum (χ : Pic (conductorOrder K c) →* ℂˣ)
    (y : (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point) :
    (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point :=
  ∑ σ : ringClassField (conductorOrder K c) ≃ₐ[K] ringClassField (conductorOrder K c),
    chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) • galPt E σ y

/-- **The native lattice** (tex L2415, L2433–2434, L9422–9427): the `χ`-eigen subgroup of `E(H_c)`,
`{x : σ x = χ(σ) x for every σ ∈ Gal(H_c/K)}`. -/
def eigenLattice (χ : Pic (conductorOrder K c) →* ℂˣ) :
    AddSubgroup (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point where
  carrier := {x | ∀ σ, galPt E σ x = chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) • x}
  zero_mem' := fun σ => by simp
  add_mem' := fun {a b} ha hb σ => by rw [map_add, ha σ, hb σ, smul_add]
  neg_mem' := fun {a} ha σ => by rw [map_neg, ha σ, smul_neg]

end RingClass


/-! ### Local square classes -/

/-- `d` is a unit square at the prime `p`: `p ∤ d` and `d` is a square modulo `p` (`p` odd), or
`d ≡ 1 (mod 8)` (`p = 2`). For `p ∤ d` this is "`d` is a square in `ℚ_p`" (Hensel), the
"squareclass of one at `p`" of tex L2405–2406, L2350–2352. -/
def SquareAt (p : ℕ) (d : ℤ) : Prop :=
  ¬ (p : ℤ) ∣ d ∧ (p = 2 → d % 8 = 1) ∧ (p ≠ 2 → IsSquare (d : ZMod p))

/-! ### The twist embedding `E^{(d)}(ℚ) → E(H)` -/

section Twist

variable {H : Type*} [Field H] [Algebra ℚ H]

open Classical in
/-- The variable change `(x, y) ↦ (s² x, s³ y)` (`u = s⁻¹`), or `1` if `s = 0`. -/
def twistVC (s : H) : WeierstrassCurve.VariableChange H :=
  if hs : s = 0 then 1 else ⟨Units.mk0 s⁻¹ (inv_ne_zero hs), 0, 0, 0⟩

/-- **Over `H ∋ s` with `s² = d ≠ 0`, the twist `E^{(d)}` is the variable change `u = s⁻¹` of `E`**
(PROVED; for `a₁ = a₃ = 0`). -/
theorem twistVC_smul (E : WeierstrassCurve ℚ) (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0) {d : ℚ} {s : H}
    (hs : s ≠ 0) (hsd : s ^ 2 = algebraMap ℚ H d) :
    twistVC s • E.baseChange H = (qtwist E d).baseChange H := by
  have hq : qtwist E d = ⟨0, d * E.a₂, 0, d ^ 2 * E.a₄, d ^ 3 * E.a₆⟩ := by
    simp only [qtwist, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, h₁, h₃]
    congr 1 <;> ring
  rw [hq, twistVC, dif_neg hs]
  ext
  · simp [WeierstrassCurve.variableChange_a₁, h₁]
  · simp [WeierstrassCurve.variableChange_a₂, h₁]
    simp only [← eq_ratCast (algebraMap ℚ H), map_mul]
    field_simp
    linear_combination (algebraMap ℚ H E.a₂) * hsd
  · simp [WeierstrassCurve.variableChange_a₃, h₁, h₃]
  · simp [WeierstrassCurve.variableChange_a₄, h₁, h₃]
    simp only [← eq_ratCast (algebraMap ℚ H), map_mul, map_pow]
    field_simp
    linear_combination (algebraMap ℚ H E.a₄ * (s ^ 2 + algebraMap ℚ H d)) * hsd
  · simp [WeierstrassCurve.variableChange_a₆, h₁, h₃]
    simp only [← eq_ratCast (algebraMap ℚ H), map_mul, map_pow]
    field_simp
    linear_combination (algebraMap ℚ H E.a₆ * (s ^ 4 + s ^ 2 * algebraMap ℚ H d +
      algebraMap ℚ H d ^ 2)) * hsd

variable [DecidableEq H]

/-- **The twist embedding** `ψ_s : E^{(d)}(ℚ) → E(H)`, `(X, Y) ↦ (X/d, Y/(d s))`, for `s ∈ H` with
`s² = d` (the identification of `E^{(d)}(ℚ)` with the points of `E` over `ℚ(√d)` on which
`√d ↦ −√d` acts by `−1`, tex L8298–8299 "the standard twist identification"): base change to `H`
followed by the variable change `twistVC s`. A group homomorphism by construction. -/
def twistEmb (E : WeierstrassCurve ℚ) (d : ℚ) (s : H)
    (heq : twistVC s • E.baseChange H = (qtwist E d).baseChange H) :
    (qtwist E d).toAffine.Point →+ (E.baseChange H).toAffine.Point :=
  ((WeierstrassCurve.Affine.Point.addEquivVariableChange (E.baseChange H) (twistVC s)).toAddMonoidHom.comp
    (AddEquiv.cast (M := fun V : WeierstrassCurve H => V.toAffine.Point) heq.symm).toAddMonoidHom).comp
    ((WeierstrassCurve.Affine.Point.map (W' := (qtwist E d).toAffine) (Algebra.ofId ℚ H)).comp
      (WeierstrassCurve.Affine.Point.equivBaseChangeSelf (qtwist E d).toAffine).toAddMonoidHom)

end Twist

/-! ### Index valuations -/

/-- **The index valuation** of `x` in `M` (tex L2416; L9422: "write `P_D = m_D G + T` in its native
rank-one free lattice", `j = v₂(m_D)`): the supremum of the `e` such that `x - 2^e G` is torsion for
some `G ∈ M`. In a rank-one `M` containing the nontorsion point `x = m G₀ + T` it is `v₂ m`. -/
def twoDivIndex {A : Type*} [AddCommGroup A] (M : AddSubgroup A) (x : A) : ℕ∞ :=
  ⨆ (e : ℕ) (_ : ∃ G ∈ M, IsOfFinAddOrder (x - (2 ^ e : ℕ) • G)), (e : ℕ∞)

end ZInQ.Contrib.CloudB3RC53.GenusOdd
