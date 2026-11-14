import ZInQKernel.Contrib.CurvesG.GenusSplit
import ZInQKernel.Contrib.RLeaf.BelyiX1
import ZInQKernel.Contrib.RLeaf.T40

/-! # curve-split: row H-79 `ZInQ.Contrib.CurvesG.GenusX1Field`

`GenusX1Field` (imported from `ZInQKernel/Contrib/CurvesG/GenusSplit.lean`, unchanged) says that the
genus of `K_N = ℚ(j)(x(P))` *equals* the genus of `Γ₁(N)`. Its published sources (Shimura 1971,
§6.7 canonical model of `X₁(N)`, and Prop. 1.40, the genus of `Γ\ℍ*`) are statements about the
compact Riemann surface `Γ₁(N)\ℍ*`, which has no Lean definition today (Mathlib v4.35 has the upper
half plane and the action of `SL₂(ℤ)`, not the compactified quotient as a Riemann surface nor its
genus). So `GenusX1Field` cannot be split into published-form leaves over genuine definitions now.

Finding (VERIFIED by reading the consumers): the proof only uses `GenusX1Field` through
`LeafModCurves.dim_J1_le` (`dim J₁(N) ≤ N²`; consumers `javanpeykarJ1` and the E2 step of
`scratch/g0-assemble2/olean/TailD.lean`). The bound needs much less than the equality:

* `GenusX1Le` (new, weaker than the row): `g(K_N) ≤ N²`; `genusX1Le_of_genusX1Field` (proved).
* `dimJ1Le_of` (proved): `DimJacobianEqGenus → GenusX1Le → DimJ1Le`, where `DimJ1Le` is exactly the
  conclusion of `LeafModCurves.dim_J1_le`.
* `genusX1Le_of_belyi` (proved): `BelyiGenusBound → X0Transitive → GenusX1Le`, from the kernel
  theorems `ZInQ.RLeaf.belyiX1` (`j/1728` is a Belyi function on `K_N`, `[K_N : ℚ(j)] ≤ N²`) and
  `ZInQ.RLeaf.x1ConstantField_of_x0Transitive` (`ℚ` is algebraically closed in `K_N`).
* `BelyiGenusBound` (named GLUE, a two-line consequence of Riemann–Hurwitz): a function field
  `F/ℚ` with constant field `ℚ` and a Belyi function `t` of degree `d` has `2g(F) + 1 ≤ d`.

No `sorry`, no `axiom`. -/

noncomputable section

namespace CurveSplit

open AlgebraicGeometry CategoryTheory LeafModCurves X1Belyi ZInQ.Contrib.CurvesG

/-- **GLUE (lit-composite): the Riemann–Hurwitz bound for Belyi functions.** Let `F` be a finite
extension of `ℚ(j)` (`Qj = RatFunc ℚ`) in which `ℚ` is algebraically closed, and suppose
`t = j/1728` is a Belyi function on `F` over `ℚ` (`IsBelyiFunction`: unramified over every finite
place of `ℚ(t)` other than `t = 0, 1`). Then `2 g(F) + 1 ≤ [F : ℚ(j)]`, `g = fieldGenus`.

Why true (STANDARD): Riemann–Hurwitz (Stichtenoth, *Algebraic function fields and codes*, Thm
3.4.13, with Dedekind's different theorem Thm 3.5.1 in characteristic 0; Hartshorne IV.2.4
geometrically; numbers UNVERIFIED) gives `2g − 2 = −2d + Σ_P (e_P − 1) deg P`, the sum over the
places above `t = 0, 1, ∞` only; at each of these three degree-one places the fundamental
identity `Σ_{P|Q} e_P f_P = d` (Stichtenoth Thm 3.1.11) gives `Σ_{P|Q} (e_P − 1) f_P ≤ d − 1`; so
`2g − 2 ≤ d − 3`. Also needed: the places of `F/ℚ` are discrete valuation rings (Stichtenoth Thm
1.1.6) to read `IsBelyiFunction` as `e_P = 1`, and `fieldGenus` (holomorphic differentials) is the
Riemann–Roch genus (Stichtenoth Thm 1.5.15 / Chevalley; UNVERIFIED). A Lean proof needs Lean
statements of these four textbook results over Mathlib's `ValuationSubring` (places, `e_P` as the
index of `Uₚ·ℚ(t)ˣ` in `Fˣ`, `deg P` as the `ℚ`-dimension of the residue field) and about 400
lines of valuation-theoretic glue. -/
def BelyiGenusBound : Prop :=
  ∀ (F : Type) [Field F] [Algebra Qj F] [Algebra ℚ F] [FiniteDimensional Qj F],
    ConstantFieldIsQ F → IsBelyiFunction ℚ F (algebraMap Qj F (RatFunc.X / 1728)) →
      2 * fieldGenus F + 1 ≤ Module.finrank Qj F

/-- **The genus bound that the proof uses** (weaker than `GenusX1Field`): `g(K_N) ≤ N²`. -/
def GenusX1Le : Prop :=
  ∀ (N : ℕ) (P : EjBar.toAffine.Point), 0 < N → addOrderOf P = N →
    fieldGenus (fieldX1 P) ≤ N ^ 2

/-- **The conclusion of `LeafModCurves.dim_J1_le`** (`dim J₁(N) ≤ N²`), the only use of T34. -/
def DimJ1Le : Prop :=
  ∀ (N : ℕ) (J : PkgI3.AbVar ℚ), 0 < N → IsJ1 N J →
    ∃ g : ℕ, J.dim = (g : WithBot ℕ∞) ∧ g ≤ N ^ 2

/-- `GenusX1Field → GenusX1Le` (proved, from `genus_Gamma1_le`). -/
theorem genusX1Le_of_genusX1Field (h : GenusX1Field) : GenusX1Le := by
  intro N P hN hP
  have : NeZero N := ⟨hN.ne'⟩
  have h1 := h N P hN hP
  have h2 := genus_Gamma1_le N
  rw [← h1] at h2
  exact_mod_cast h2

/-- **`DimJ1Le` from the first half of T34 and the genus bound** (proved). -/
theorem dimJ1Le_of (h1 : DimJacobianEqGenus) (h2 : GenusX1Le) : DimJ1Le := by
  rintro N J hN ⟨X, P₀, aj, ⟨hC, hI, P, hP, he⟩, hJ⟩
  exact ⟨fieldGenus (fieldX1 P), h1 X hC P₀ J aj hJ hI (fieldX1 P) he, h2 N P hN hP⟩

/-- `K_N` is finite over `ℚ(j)`. -/
instance fieldX1_finiteDimensional (P : EjBar.toAffine.Point) :
    FiniteDimensional Qj (fieldX1 P) :=
  IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (xCoord P))

/-- **`GenusX1Le` from the Riemann–Hurwitz bound for Belyi functions and `X₀(N)`-transitivity**
(proved; `BelyiX1` and the constant field are kernel theorems). -/
theorem genusX1Le_of_belyi (hB : BelyiGenusBound) (h0 : ZInQ.RLeaf.X0Transitive) :
    GenusX1Le := by
  intro N P hN hP
  obtain ⟨hBel, hdeg⟩ := ZInQ.RLeaf.belyiX1 N P hN hP
  have hK := ZInQ.RLeaf.x1ConstantField_of_x0Transitive h0 N P hN hP
  have := hB (fieldX1 P) hK hBel
  omega

/-- **`DimJ1Le` (the use of T34) from `DimJacobianEqGenus`, `BelyiGenusBound` and
`X₀(N)`-transitivity** (proved). -/
theorem dimJ1Le_of_belyi (h1 : DimJacobianEqGenus) (hB : BelyiGenusBound)
    (h0 : ZInQ.RLeaf.X0Transitive) : DimJ1Le :=
  dimJ1Le_of h1 (genusX1Le_of_belyi hB h0)

/-! ## `BelyiGenusBound` from three textbook theorems

Places of a function field `F/ℚ` are Mathlib `ValuationSubring`s; the ramification index over
`ℚ(j)` is the index of `U_P · ℚ(j)ˣ` in `Fˣ` (`Fˣ/U_P` is the value group), the degree of a place
is the `ℚ`-dimension of its residue field. -/

section RH

variable (F : Type) [Field F] [Algebra Qj F] [Algebra ℚ F]

/-- A place of `F/ℚ`: a proper valuation subring containing `ℚ`. -/
structure Place where
  w : ValuationSubring F
  ne_top : w ≠ ⊤
  rat_mem : ∀ c : ℚ, algebraMap ℚ F c ∈ w

variable {F}

theorem Place.ext' {P Q : Place F} (h : P.w = Q.w) : P = Q := by
  cases P; cases Q; cases h; rfl

/-- `ℚ → κ(P)`. -/
def Place.ratHom (P : Place F) : ℚ →+* IsLocalRing.ResidueField P.w :=
  (IsLocalRing.residue P.w).comp ((algebraMap ℚ F).codRestrict P.w.toSubring P.rat_mem)

/-- The degree `[κ(P) : ℚ]` of a place. -/
def Place.deg (P : Place F) : ℕ :=
  @Module.finrank ℚ (IsLocalRing.ResidueField P.w) _ _ P.ratHom.toModule

/-- The ramification index `e(P | P ∩ ℚ(j))`: the index of `U_P · ℚ(j)ˣ` in `Fˣ`. -/
def Place.ramIdx (P : Place F) : ℕ :=
  (P.w.unitGroup ⊔ (Units.map (algebraMap Qj F : Qj →* F)).range).index

/-- The Belyi coordinate `t = j/1728` in `F`. -/
abbrev tF : F := algebraMap Qj F (RatFunc.X / 1728)

variable (F)

/-- **Leaf: Riemann–Hurwitz for `F/ℚ(j)`** (published). For `F` finite over `ℚ(j)` with
constant field `ℚ`: only finitely many places ramify, and
`2 g(F) − 2 = [F : ℚ(j)] · (2·0 − 2) + Σ_P (e_P − 1) deg P`.
Source: Stichtenoth, *Algebraic Function Fields and Codes* (2nd ed.), Thm 3.4.13 (Hurwitz genus
formula, `g(ℚ(j)) = 0`) with Thm 3.5.1 (Dedekind's different theorem: `d(P) = e_P − 1` in
characteristic 0); Hartshorne IV.2.4 geometrically (numbers UNVERIFIED). The genus is
`fieldGenus` (the dimension of the holomorphic differentials, which equals the Riemann–Roch genus:
Stichtenoth Thm 1.5.15 / Hartshorne II.8, UNVERIFIED): a composite of these printed statements. -/
def RiemannHurwitzQj : Prop :=
  ∀ (F : Type) [Field F] [Algebra Qj F] [Algebra ℚ F] [FiniteDimensional Qj F],
    ConstantFieldIsQ F →
      ∃ h : (Function.support fun P : Place F => ((P.ramIdx : ℤ) - 1) * P.deg).Finite,
        2 * (fieldGenus F : ℤ) - 2 =
          -2 * (Module.finrank Qj F : ℤ) + ∑ P ∈ h.toFinset, ((P.ramIdx : ℤ) - 1) * P.deg

/-- **Leaf: the fundamental identity at the places `j = 0`, `j = 1728`, `j = ∞` of `ℚ(j)`**
(published). For `F` finite over `ℚ(j)` and `Q` one of these three places of degree one, finitely
many places `P` of `F` lie over `Q` and `Σ_{P|Q} e_P deg P = [F : ℚ(j)]`.
Source: Stichtenoth Thm 3.1.11 (`Σ e(P|Q) f(P|Q) = [F : ℚ(j)]`) with `deg P = f(P|Q) deg Q` and
`deg Q = 1` (Stichtenoth §3.1; numbers UNVERIFIED). `P` lies over `j = 0` iff `t ∈ 𝔪_P`, over
`j = 1728` iff `t − 1 ∈ 𝔪_P`, over `j = ∞` iff `t ∉ 𝒪_P` (`t = j/1728`). -/
def FundamentalIdentityQj : Prop :=
  ∀ (F : Type) [Field F] [Algebra Qj F] [Algebra ℚ F] [FiniteDimensional Qj F],
    ∀ Z ∈ ({{P : Place F | tF ∈ P.w ∧ tF ∈ P.w.nonunits},
        {P : Place F | tF ∈ P.w ∧ tF - 1 ∈ P.w.nonunits},
        {P : Place F | tF ∉ P.w}} : Set (Set (Place F))),
      ∃ h : Z.Finite, ∑ P ∈ h.toFinset, P.ramIdx * P.deg = Module.finrank Qj F

/-- **Leaf: places of a function field are discrete valuation rings** (published). Every place
`P` of `F/ℚ` has a uniformizer `π`: `π ∈ 𝒪_P` is not a unit, and every `x ∈ Fˣ` is `π^n` times a
unit of `𝒪_P`. Source: Stichtenoth Thm 1.1.6 with Def. 1.1.4 / Thm 1.1.5 (numbers UNVERIFIED). -/
def PlacesAreDVR : Prop :=
  ∀ (F : Type) [Field F] [Algebra Qj F] [Algebra ℚ F] [FiniteDimensional Qj F],
    ∀ P : Place F, ∃ π : Fˣ, (π : F) ∈ P.w ∧ π ∉ P.w.unitGroup ∧
      ∀ x : Fˣ, ∃ n : ℤ, x * π ^ (-n) ∈ P.w.unitGroup

end RH

section Glue

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F]

/-- Valuation of a `ℤ`-power of a unit. -/
theorem val_zpow (A : ValuationSubring F) (x : Fˣ) (n : ℤ) :
    A.valuation ((x ^ n : Fˣ) : F) = A.valuation (x : F) ^ n := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀]

/-- **`e_P = 1` when a uniformizer comes from `ℚ(j)`** (proved). If `P` has a uniformizer `π` and
`s = r ∈ ℚ(j)ˣ` is a non-unit of `𝒪_P` dividing every element of `𝔪_P`, then `e_P = 1`. -/
theorem ramIdx_eq_one (P : Place F) (π : Fˣ) (hπ : (π : F) ∈ P.w) (hπu : π ∉ P.w.unitGroup)
    (hdvr : ∀ x : Fˣ, ∃ n : ℤ, x * π ^ (-n) ∈ P.w.unitGroup) (r : Qj) (hr0 : r ≠ 0)
    (hs : algebraMap Qj F r ∈ P.w.nonunits)
    (hgen : ∀ x ∈ P.w.nonunits, ∃ y ∈ P.w, x = algebraMap Qj F r * y) : P.ramIdx = 1 := by
  set v := P.w.valuation
  set s : Fˣ := Units.map (algebraMap Qj F : Qj →* F) (Units.mk0 r hr0) with hsdef
  have hsval : (s : F) = algebraMap Qj F r := rfl
  have hsrange : s ∈ (Units.map (algebraMap Qj F : Qj →* F)).range := ⟨_, rfl⟩
  -- `v π < 1`
  have hvπ1 : v π ≤ 1 := (P.w.valuation_le_one_iff _).mpr hπ
  have hvπne : v π ≠ 1 := fun h => hπu ((P.w.mem_unitGroup_iff π).mpr h)
  have hvπ : v π < 1 := lt_of_le_of_ne hvπ1 hvπne
  have hvπ0 : 0 < v π := (Valuation.pos_iff v).mpr π.ne_zero
  have hanti := zpow_right_strictAnti₀ hvπ0 hvπ
  -- `v(x) = v(π)^n` from the uniformizer
  have hval : ∀ x : Fˣ, ∃ n : ℤ, v x = v π ^ n := by
    intro x
    obtain ⟨n, hn⟩ := hdvr x
    refine ⟨n, ?_⟩
    have h1 : v ((x * π ^ (-n) : Fˣ) : F) = 1 := (P.w.mem_unitGroup_iff _).mp hn
    rw [Units.val_mul, map_mul, val_zpow, zpow_neg] at h1
    have hne : v π ^ n ≠ 0 := (zpow_pos hvπ0 n).ne'
    calc v x = v x * ((v π ^ n)⁻¹ * v π ^ n) := by rw [inv_mul_cancel₀ hne, mul_one]
      _ = v π ^ n := by rw [← mul_assoc, h1, one_mul]
  -- `v(s) = v(π)`
  obtain ⟨m, hm⟩ := hval s
  have hvs : v s < 1 := (P.w.mem_nonunits_iff).mp (hsval ▸ hs)
  have hπn : (π : F) ∈ P.w.nonunits := (P.w.mem_nonunits_iff).mpr hvπ
  obtain ⟨y, hy, hπy⟩ := hgen _ hπn
  have hvy : v y ≤ 1 := (P.w.valuation_le_one_iff _).mpr hy
  have hle : v π ≤ v s := by
    rw [hπy, map_mul, ← hsval]
    exact mul_le_of_le_one_right zero_le hvy
  have hm1 : m = 1 := by
    have h1 : v π ^ (1 : ℤ) ≤ v π ^ m := by rw [zpow_one, ← hm]; exact hle
    have h2 : v π ^ m < v π ^ (0 : ℤ) := by rw [zpow_zero, ← hm]; exact hvs
    have h3 : m ≤ 1 := hanti.le_iff_ge.mp h1
    have h4 : 0 < m := hanti.lt_iff_gt.mp h2
    omega
  rw [hm1, zpow_one] at hm
  -- every unit lies in `U_P · ℚ(j)ˣ`
  rw [Place.ramIdx, Subgroup.index_eq_one, eq_top_iff]
  intro x _
  obtain ⟨n, hn⟩ := hval x
  have hu : x * s ^ (-n) ∈ P.w.unitGroup := by
    rw [P.w.mem_unitGroup_iff, Units.val_mul, map_mul, val_zpow, hm, hn, zpow_neg,
      mul_inv_cancel₀ (zpow_pos hvπ0 n).ne']
  have : x = (x * s ^ (-n)) * s ^ n := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu)
    (Subgroup.mem_sup_right (Subgroup.zpow_mem _ hsrange n))

end Glue

section Glue2

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F]

theorem algebraMap_rat_comp : (algebraMap Qj F).comp (algebraMap ℚ Qj) = algebraMap ℚ F :=
  RingHom.ext_rat _ _

theorem mul_mem_nonunits (A : ValuationSubring F) {a b : F} (ha : a ∈ A) (hb : b ∈ A.nonunits) :
    a * b ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hb ⊢
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le ((A.valuation_le_one_iff a).mpr ha)) hb

/-- Polynomials over `ℚ` at an element of `𝒪_P` stay in `𝒪_P`. -/
theorem aeval_mem (P : Place F) {z : F} (hz : z ∈ P.w) (p : Polynomial ℚ) :
    Polynomial.aeval z p ∈ P.w := by
  rw [Polynomial.aeval_eq_sum_range]
  refine Subring.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def]
  exact Subring.mul_mem _ (P.rat_mem _) (Subring.pow_mem _ hz _)

/-- `ℚ(j)`-polynomials at an element of `𝒪_P`, when `ℚ(j) ⊆ 𝒪_P`. -/
theorem aeval_mem_Qj (P : Place F) (himg : ∀ r : Qj, algebraMap Qj F r ∈ P.w) {z : F}
    (hz : z ∈ P.w) (p : Polynomial Qj) : Polynomial.aeval z p ∈ P.w := by
  rw [Polynomial.aeval_eq_sum_range]
  refine Subring.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def]
  exact Subring.mul_mem _ (himg _) (Subring.pow_mem _ hz _)

/-- The polynomials over `ℚ` vanishing at the place `P` (when `t ∈ 𝒪_P`). -/
def polyIdeal (P : Place F) (ht : (tF : F) ∈ P.w) : Ideal (Polynomial ℚ) where
  carrier := {p | Polynomial.aeval (tF : F) p ∈ P.w.nonunits}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact P.w.nonunits.add_mem ha hb
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact P.w.nonunits.zero_mem
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at *
    exact mul_mem_nonunits P.w (aeval_mem P ht c) hx

theorem polyIdeal_isPrime (P : Place F) (ht : (tF : F) ∈ P.w) : (polyIdeal P ht).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one]
    show Polynomial.aeval (tF : F) 1 ∉ P.w.nonunits
    rw [map_one, ValuationSubring.mem_nonunits_iff, map_one]
    exact lt_irrefl _
  · intro a b hab
    have ha := (P.w.valuation_le_one_iff _).mpr (aeval_mem P ht a)
    have hb := (P.w.valuation_le_one_iff _).mpr (aeval_mem P ht b)
    change Polynomial.aeval (tF : F) (a * b) ∈ P.w.nonunits at hab
    change Polynomial.aeval (tF : F) a ∈ P.w.nonunits ∨ Polynomial.aeval (tF : F) b ∈ P.w.nonunits
    rw [map_mul, ValuationSubring.mem_nonunits_iff, map_mul] at hab
    rw [ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff]
    by_contra h
    push_neg at h
    have h1 := le_antisymm ha h.1
    have h2 := le_antisymm hb h.2
    rw [h1, h2, one_mul] at hab
    exact lt_irrefl _ hab

/-- `ℚ[j] → F`, through `ℚ(j)`, is evaluation at `1728 t`. -/
theorem algebraMap_poly (p : Polynomial ℚ) :
    algebraMap Qj F (algebraMap (Polynomial ℚ) Qj p) =
      Polynomial.aeval (tF : F) (p.comp (Polynomial.C 1728 * Polynomial.X)) := by
  have h1728 : Polynomial.aeval (tF : F) (Polynomial.C (1728 : ℚ) * Polynomial.X) =
      algebraMap Qj F RatFunc.X := by
    rw [map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    simp only [map_ofNat]
    rw [tF, ← map_ofNat (algebraMap Qj F) 1728, ← map_mul]
    congr 1
    field_simp
  have h2 : algebraMap Qj F (algebraMap (Polynomial ℚ) Qj p) =
      Polynomial.aeval (algebraMap Qj F RatFunc.X) p := by
    have : (algebraMap Qj F).comp (algebraMap (Polynomial ℚ) Qj) =
        (Polynomial.aeval (algebraMap Qj F RatFunc.X)).toRingHom := by
      refine Polynomial.ringHom_ext' (RingHom.ext_rat _ _) ?_
      simp [RatFunc.algebraMap_X]
    exact congrArg (fun φ : Polynomial ℚ →+* F => φ p) this
  rw [h2, Polynomial.aeval_comp]
  exact (congrArg (fun z => Polynomial.aeval z p) h1728).symm

theorem comp_ne_zero {p : Polynomial ℚ} (hp : p ≠ 0) :
    p.comp (Polynomial.C 1728 * Polynomial.X) ≠ 0 := by
  intro h
  have h2 := congrArg Polynomial.natDegree h
  rw [Polynomial.natDegree_comp, Polynomial.natDegree_C_mul_X _ (by norm_num), mul_one,
    Polynomial.natDegree_zero] at h2
  have h3 := congrArg Polynomial.leadingCoeff h
  rw [Polynomial.leadingCoeff_comp (by rw [Polynomial.natDegree_C_mul_X _ (by norm_num)]; norm_num),
    Polynomial.leadingCoeff_zero] at h3
  simp only [Polynomial.leadingCoeff_C_mul_X, mul_eq_zero, pow_eq_zero_iff', Polynomial.leadingCoeff_eq_zero] at h3
  tauto

/-- **The ideal of a place is nonzero** (proved): otherwise `ℚ(j) ⊆ 𝒪_P`, and then `𝒪_P = F`
since `F` is algebraic over `ℚ(j)` (an element outside `𝒪_P` has an inverse in `𝔪_P` whose minimal
polynomial has a nonzero constant term in `𝔪_P ∩ ℚ(j) = 0`). -/
theorem polyIdeal_ne_bot [FiniteDimensional Qj F] (P : Place F) (ht : (tF : F) ∈ P.w)
    (htr : Transcendental ℚ (tF : F)) : polyIdeal P ht ≠ ⊥ := by
  intro hbot
  have hunit : ∀ p : Polynomial ℚ, p ≠ 0 → (Polynomial.aeval (tF : F) p)⁻¹ ∈ P.w := by
    intro p hp
    have h2 : Polynomial.aeval (tF : F) p ∉ P.w.nonunits := fun h => by
      have : p ∈ polyIdeal P ht := h
      rw [hbot, Ideal.mem_bot] at this
      exact hp this
    have h0 : Polynomial.aeval (tF : F) p ≠ 0 := fun h0 => htr ⟨p, hp, h0⟩
    rw [ValuationSubring.mem_nonunits_iff_or] at h2
    push_neg at h2
    exact h2.2
  have himg : ∀ r : Qj, algebraMap Qj F r ∈ P.w := by
    intro r
    rw [← RatFunc.num_div_denom r, map_div₀, algebraMap_poly, algebraMap_poly, div_eq_mul_inv]
    exact Subring.mul_mem _ (aeval_mem P ht _) (hunit _ (comp_ne_zero (RatFunc.denom_ne_zero r)))
  obtain ⟨x, hx⟩ : ∃ x, x ∉ P.w := by
    by_contra h
    push_neg at h
    exact P.ne_top (eq_top_iff.mpr fun x _ => h x)
  have hx0 : x ≠ 0 := fun h => hx (h ▸ P.w.zero_mem)
  have hy : x⁻¹ ∈ P.w.nonunits := (P.w.inv_mem_nonunits_iff).mpr (Or.inr hx)
  have hyw : x⁻¹ ∈ P.w := P.w.nonunits_subset hy
  have hy0 : x⁻¹ ≠ 0 := inv_ne_zero hx0
  have hint : IsIntegral Qj x⁻¹ := IsIntegral.of_finite Qj _
  set p := minpoly Qj x⁻¹
  have hc0 := minpoly.coeff_zero_ne_zero hint hy0
  have hev : Polynomial.aeval x⁻¹ p = 0 := minpoly.aeval Qj _
  have hsplit := Polynomial.X_mul_divX_add p
  rw [← hsplit, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at hev
  have hc : algebraMap Qj F (p.coeff 0) = -(x⁻¹ * Polynomial.aeval x⁻¹ p.divX) := by
    linear_combination hev
  have hcn : algebraMap Qj F (p.coeff 0) ∈ P.w.nonunits := by
    rw [hc, mul_comm]
    exact P.w.nonunits.neg_mem (mul_mem_nonunits P.w (aeval_mem_Qj P himg hyw _) hy)
  have hcinv : (algebraMap Qj F (p.coeff 0))⁻¹ ∈ P.w := by
    rw [← map_inv₀]; exact himg _
  rw [ValuationSubring.mem_nonunits_iff_or] at hcn
  rcases hcn with h | h
  · exact hc0 ((map_eq_zero_iff _ (algebraMap Qj F).injective).mp h)
  · exact h hcinv

/-- A nonzero prime ideal of `ℚ[X]` contains a monic irreducible polynomial. -/
theorem exists_monic_irreducible_mem (I : Ideal (Polynomial ℚ)) [hI : I.IsPrime] (h0 : I ≠ ⊥) :
    ∃ q : Polynomial ℚ, q.Monic ∧ Irreducible q ∧ q ∈ I := by
  set g := Submodule.IsPrincipal.generator I
  have hg0 : g ≠ 0 := by
    intro h
    apply h0
    rw [← Submodule.IsPrincipal.span_singleton_generator I]
    simp [g, h]
  have hgp : Prime g := Submodule.IsPrincipal.prime_generator_of_isPrime I h0
  refine ⟨g * Polynomial.C g.leadingCoeff⁻¹, Polynomial.monic_mul_leadingCoeff_inv hg0, ?_, ?_⟩
  · refine (irreducible_mul_isUnit ?_).mpr hgp.irreducible
    exact Polynomial.isUnit_C.mpr (IsUnit.mk0 _ (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hg0)))
  · exact I.mul_mem_right _ (Submodule.IsPrincipal.generator_mem I)

end Glue2

section Glue3

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F]

/-- `ℚ(j) → F` commutes with evaluating `ℚ`-polynomials. -/
theorem algebraMap_aeval (z : Qj) (q : Polynomial ℚ) :
    algebraMap Qj F (Polynomial.aeval z q) = Polynomial.aeval (algebraMap Qj F z) q := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, algebraMap_rat_comp]

/-- **Every place lies over `j = 0`, `j = 1728`, `j = ∞`, or is unramified** (proved from the
Belyi property and the uniformizer leaf). -/
theorem place_cases [FiniteDimensional Qj F] (hB : IsBelyiFunction ℚ F (tF : F))
    (hD : PlacesAreDVR) (P : Place F) :
    ((tF : F) ∈ P.w ∧ (tF : F) ∈ P.w.nonunits) ∨ ((tF : F) ∈ P.w ∧ (tF : F) - 1 ∈ P.w.nonunits) ∨
      (tF : F) ∉ P.w ∨ P.ramIdx = 1 := by
  by_cases ht : (tF : F) ∈ P.w
  · have hpr := polyIdeal_isPrime P ht
    obtain ⟨q, hqm, hqi, hqI⟩ := exists_monic_irreducible_mem (polyIdeal P ht)
      (polyIdeal_ne_bot P ht hB.1)
    have hqI' : Polynomial.aeval (tF : F) q ∈ P.w.nonunits := hqI
    by_cases hX : q = Polynomial.X
    · left
      rw [hX, Polynomial.aeval_X] at hqI'
      exact ⟨ht, hqI'⟩
    by_cases hX1 : q = Polynomial.X - 1
    · right; left
      rw [hX1, map_sub, Polynomial.aeval_X, map_one] at hqI'
      exact ⟨ht, hqI'⟩
    right; right; right
    have hgen := hB.2 P.w P.rat_mem ht q hqm hqi hX hX1 hqI'
    obtain ⟨π, hπ, hπu, hdvr⟩ := hD F P
    set r : Qj := Polynomial.aeval (RatFunc.X / 1728 : Qj) q with hr
    have hrq : algebraMap Qj F r = Polynomial.aeval (tF : F) q := by
      rw [hr, algebraMap_aeval]
    have hr0 : r ≠ 0 := by
      intro h0
      have : Polynomial.aeval (tF : F) q = 0 := by rw [← hrq, h0, map_zero]
      exact hB.1 ⟨q, hqm.ne_zero, this⟩
    refine ramIdx_eq_one P π hπ hπu hdvr r hr0 (hrq ▸ hqI') ?_
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hgen x hx
    exact ⟨y, hy, hrq ▸ hxy⟩
  · right; right; left
    exact ht

/-- Variant of `place_cases` with uniformizers only at places containing `t`. -/
theorem place_cases' [FiniteDimensional Qj F] (hB : IsBelyiFunction ℚ F (tF : F))
    (hD : ∀ P : Place F, (tF : F) ∈ P.w → ∃ π : Fˣ, (π : F) ∈ P.w ∧ π ∉ P.w.unitGroup ∧
      ∀ x : Fˣ, ∃ n : ℤ, x * π ^ (-n) ∈ P.w.unitGroup) (P : Place F) :
    ((tF : F) ∈ P.w ∧ (tF : F) ∈ P.w.nonunits) ∨ ((tF : F) ∈ P.w ∧ (tF : F) - 1 ∈ P.w.nonunits) ∨
      (tF : F) ∉ P.w ∨ P.ramIdx = 1 := by
  by_cases ht : (tF : F) ∈ P.w
  · have hpr := polyIdeal_isPrime P ht
    obtain ⟨q, hqm, hqi, hqI⟩ := exists_monic_irreducible_mem (polyIdeal P ht)
      (polyIdeal_ne_bot P ht hB.1)
    have hqI' : Polynomial.aeval (tF : F) q ∈ P.w.nonunits := hqI
    by_cases hX : q = Polynomial.X
    · left
      rw [hX, Polynomial.aeval_X] at hqI'
      exact ⟨ht, hqI'⟩
    by_cases hX1 : q = Polynomial.X - 1
    · right; left
      rw [hX1, map_sub, Polynomial.aeval_X, map_one] at hqI'
      exact ⟨ht, hqI'⟩
    right; right; right
    have hgen := hB.2 P.w P.rat_mem ht q hqm hqi hX hX1 hqI'
    obtain ⟨π, hπ, hπu, hdvr⟩ := hD P ht
    set r : Qj := Polynomial.aeval (RatFunc.X / 1728 : Qj) q with hr
    have hrq : algebraMap Qj F r = Polynomial.aeval (tF : F) q := by
      rw [hr, algebraMap_aeval]
    have hr0 : r ≠ 0 := by
      intro h0
      have : Polynomial.aeval (tF : F) q = 0 := by rw [← hrq, h0, map_zero]
      exact hB.1 ⟨q, hqm.ne_zero, this⟩
    refine ramIdx_eq_one P π hπ hπu hdvr r hr0 (hrq ▸ hqI') ?_
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hgen x hx
    exact ⟨y, hy, hrq ▸ hxy⟩
  · right; right; left
    exact ht

/-- **`BelyiGenusBound` from Riemann–Hurwitz, the fundamental identity and the uniformizer leaf**
(proved). -/
theorem belyiGenusBound_of_leaves (hRH : RiemannHurwitzQj) (hFI : FundamentalIdentityQj)
    (hD : PlacesAreDVR) : BelyiGenusBound := by
  classical
  intro F _ _ _ _ hK hB
  obtain ⟨hsupp, hRHeq⟩ := hRH F hK
  set Z0 : Set (Place F) := {P | (tF : F) ∈ P.w ∧ (tF : F) ∈ P.w.nonunits} with hZ0
  set Z1 : Set (Place F) := {P | (tF : F) ∈ P.w ∧ (tF : F) - 1 ∈ P.w.nonunits} with hZ1
  set Zi : Set (Place F) := {P | (tF : F) ∉ P.w} with hZi
  obtain ⟨h0, hs0⟩ := hFI F Z0 (by simp [hZ0])
  obtain ⟨h1, hs1⟩ := hFI F Z1 (by simp [hZ1])
  obtain ⟨hi, hsi⟩ := hFI F Zi (by simp [hZi])
  set f : Place F → ℤ := fun P => ((P.ramIdx : ℤ) - 1) * P.deg with hf
  set A := h0.toFinset ∪ h1.toFinset ∪ hi.toFinset with hA
  have hsub : hsupp.toFinset ⊆ A := by
    intro P hP
    rw [Set.Finite.mem_toFinset, Function.mem_support] at hP
    rcases place_cases hB hD P with h | h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr h))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr h))
    · exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr h)
    · exfalso
      apply hP
      show ((P.ramIdx : ℤ) - 1) * P.deg = 0
      rw [h]
      simp
  have hsum : ∑ P ∈ hsupp.toFinset, f P = ∑ P ∈ A, f P :=
    Finset.sum_subset hsub fun P _ hP => by
      rwa [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hP
  have hd01 : Disjoint h0.toFinset h1.toFinset := by
    rw [Finset.disjoint_left]
    intro P hP0 hP1
    rw [Set.Finite.mem_toFinset] at hP0 hP1
    have h1n : (1 : F) ∈ P.w.nonunits := by
      have := P.w.nonunits.sub_mem hP0.2 hP1.2
      rwa [sub_sub_cancel] at this
    rw [ValuationSubring.mem_nonunits_iff, map_one] at h1n
    exact lt_irrefl _ h1n
  have hd : Disjoint (h0.toFinset ∪ h1.toFinset) hi.toFinset := by
    rw [Finset.disjoint_left]
    intro P hP hPi
    rw [Set.Finite.mem_toFinset] at hPi
    rcases Finset.mem_union.mp hP with hP | hP <;> rw [Set.Finite.mem_toFinset] at hP
    · exact hPi hP.1
    · exact hPi hP.1
  rw [hA, Finset.sum_union hd, Finset.sum_union hd01] at hsum
  have hdpos : 0 < Module.finrank Qj F := Module.finrank_pos
  have part : ∀ (Z : Set (Place F)) (hZ : Z.Finite),
      ∑ P ∈ hZ.toFinset, P.ramIdx * P.deg = Module.finrank Qj F →
        ∑ P ∈ hZ.toFinset, f P ≤ (Module.finrank Qj F : ℤ) - 1 := by
    intro Z hZ hs
    have e1 : ∑ P ∈ hZ.toFinset, f P =
        ((∑ P ∈ hZ.toFinset, P.ramIdx * P.deg : ℕ) : ℤ) - ∑ P ∈ hZ.toFinset, (P.deg : ℤ) := by
      push_cast
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun P _ => ?_
      simp only [hf]
      ring
    rw [e1, hs]
    obtain ⟨P, hP, hne⟩ : ∃ P ∈ hZ.toFinset, P.ramIdx * P.deg ≠ 0 := by
      by_contra hc
      push_neg at hc
      rw [Finset.sum_eq_zero hc] at hs
      omega
    have hdeg : 1 ≤ P.deg := Nat.pos_of_ne_zero fun h => hne (by rw [h, mul_zero])
    have : (1 : ℤ) ≤ ∑ P ∈ hZ.toFinset, (P.deg : ℤ) :=
      le_trans (by exact_mod_cast hdeg)
        (Finset.single_le_sum (f := fun P : Place F => (P.deg : ℤ)) (fun P _ => by positivity) hP)
    linarith
  have p0 := part Z0 h0 hs0
  have p1 := part Z1 h1 hs1
  have pi := part Zi hi hsi
  have key : 2 * (fieldGenus F : ℤ) + 1 ≤ Module.finrank Qj F := by
    have := hRHeq
    rw [hsum] at this
    linarith
  exact_mod_cast key

/-- **`DimJ1Le` (the use of T34) from textbook leaves and `X₀(N)`-transitivity** (proved). -/
theorem dimJ1Le_of_textbook (h1 : DimJacobianEqGenus) (hRH : RiemannHurwitzQj)
    (hFI : FundamentalIdentityQj) (hD : PlacesAreDVR) (h0 : ZInQ.RLeaf.X0Transitive) : DimJ1Le :=
  dimJ1Le_of_belyi h1 (belyiGenusBound_of_leaves hRH hFI hD) h0

end Glue3

section Glue4

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F]

/-- **Places containing `j` are discrete valuation rings** (proved; replaces `PlacesAreDVR` where it
is used). With `R` the integral closure of `ℚ[j]` in `F` (a Dedekind domain with fraction field
`F`), `R ⊆ 𝒪_P`, `𝔭 = R ∩ 𝔪_P` is a nonzero prime, and a uniformizer of the DVR `R_𝔭 ⊆ 𝒪_P` is a
uniformizer of `𝒪_P`. -/
theorem exists_uniformizer [FiniteDimensional Qj F] (P : Place F) (ht : (tF : F) ∈ P.w) :
    ∃ π : Fˣ, (π : F) ∈ P.w ∧ π ∉ P.w.unitGroup ∧
      ∀ x : Fˣ, ∃ n : ℤ, x * π ^ (-n) ∈ P.w.unitGroup := by
  classical
  set v := P.w.valuation
  -- `j ∈ 𝒪_P`
  have hs : algebraMap Qj F RatFunc.X ∈ P.w := by
    have : algebraMap Qj F RatFunc.X = algebraMap ℚ F 1728 * (tF : F) := by
      rw [tF, ← algebraMap_rat_comp, RingHom.comp_apply, ← map_mul]
      congr 1
      rw [map_ofNat]
      field_simp
    rw [this]
    exact Subring.mul_mem _ (P.rat_mem _) ht
  letI : Algebra (Polynomial ℚ) F := ((algebraMap Qj F).comp (algebraMap (Polynomial ℚ) Qj)).toAlgebra
  have : IsScalarTower (Polynomial ℚ) Qj F := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsSeparable Qj F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  set R := integralClosure (Polynomial ℚ) F
  have : IsDedekindDomain R := integralClosure.isDedekindDomain (Polynomial ℚ) Qj F
  have : IsFractionRing R F :=
    IsIntegralClosure.isFractionRing_of_finite_extension (Polynomial ℚ) Qj F R
  -- `ℚ[j] ⊆ 𝒪_P`
  have hpoly : ∀ p : Polynomial ℚ, algebraMap (Polynomial ℚ) F p ∈ P.w := by
    intro p
    have : algebraMap (Polynomial ℚ) F p = Polynomial.aeval (algebraMap Qj F RatFunc.X) p := by
      change (algebraMap Qj F) (algebraMap (Polynomial ℚ) Qj p) = _
      have h2 : (algebraMap Qj F).comp (algebraMap (Polynomial ℚ) Qj) =
          (Polynomial.aeval (algebraMap Qj F RatFunc.X)).toRingHom := by
        refine Polynomial.ringHom_ext' (RingHom.ext_rat _ _) ?_
        simp [RatFunc.algebraMap_X]
      exact congrArg (fun φ : Polynomial ℚ →+* F => φ p) h2
    rw [this]
    exact aeval_mem P hs p
  -- `R ⊆ 𝒪_P` (valuation rings are integrally closed)
  let φ : Polynomial ℚ →+* P.w := (algebraMap (Polynomial ℚ) F).codRestrict P.w.toSubring hpoly
  have hRw : ∀ r : R, (r : F) ∈ P.w := by
    rintro ⟨x, hx⟩
    obtain ⟨p, hpm, hp⟩ := hx
    have hint : IsIntegral P.w x := ⟨p.map φ, hpm.map φ, by
      rw [Polynomial.eval₂_map]; exact hp⟩
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    show x ∈ P.w
    rw [← hy]; exact y.2
  -- the prime `𝔭 = R ∩ 𝔪_P`
  let ψ : R →+* P.w := (R.val.toRingHom).codRestrict P.w.toSubring hRw
  set 𝔭 : Ideal R := (IsLocalRing.maximalIdeal P.w).comap ψ with h𝔭def
  have h𝔭prime : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  have hmem𝔭 : ∀ r : R, r ∈ 𝔭 ↔ (r : F) ∈ P.w.nonunits := by
    intro r
    rw [h𝔭def, Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
    rfl
  have hunit : ∀ r : R, r ∉ 𝔭 → ((r : F))⁻¹ ∈ P.w := by
    intro r hr
    rw [hmem𝔭, ValuationSubring.mem_nonunits_iff_or] at hr
    push_neg at hr
    exact hr.2
  have h𝔭ne : 𝔭 ≠ ⊥ := by
    intro hbot
    apply P.ne_top
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    have hb0 : b ∉ 𝔭 := by
      rw [hbot, Ideal.mem_bot]
      intro h; exact nonZeroDivisors.coe_ne_zero ⟨b, hb⟩ h
    rw [div_eq_mul_inv]
    exact Subring.mul_mem _ (hRw a) (hunit b hb0)
  -- the DVR `R_𝔭 ⊆ F`
  have hle : 𝔭.primeCompl ≤ nonZeroDivisors R := Ideal.primeCompl_le_nonZeroDivisors 𝔭
  set Rp := Localization.subalgebra.ofField F 𝔭.primeCompl hle with hRpdef
  have : IsLocalRing Rp := IsLocalization.AtPrime.isLocalRing Rp 𝔭
  have : IsDiscreteValuationRing Rp :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R h𝔭ne Rp
  have hRpw : ∀ y : Rp, (y : F) ∈ P.w := by
    rintro ⟨y, hy⟩
    obtain ⟨a, b, hb, rfl⟩ := hy
    exact Subring.mul_mem _ (hRw a) (hunit b hb)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Rp
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  -- units of `R_𝔭` are units of `𝒪_P`
  have hU : ∀ u : Rpˣ, v ((u : Rp) : F) = 1 := by
    intro u
    have h1 : v ((u : Rp) : F) ≤ 1 := (P.w.valuation_le_one_iff _).mpr (hRpw u)
    have h2 : v (((u⁻¹ : Rpˣ) : Rp) : F) ≤ 1 := (P.w.valuation_le_one_iff _).mpr (hRpw _)
    have h3 : ((u : Rp) : F) * (((u⁻¹ : Rpˣ) : Rp) : F) = 1 := by
      rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
    have h4 : v ((u : Rp) : F) * v (((u⁻¹ : Rpˣ) : Rp) : F) = 1 := by rw [← map_mul, h3, map_one]
    by_contra hne
    have hlt : v ((u : Rp) : F) < 1 := lt_of_le_of_ne h1 hne
    have : v ((u : Rp) : F) * v (((u⁻¹ : Rpˣ) : Rp) : F) < 1 :=
      lt_of_lt_of_le (mul_lt_one_of_lt_of_le hlt h2) le_rfl
    rw [h4] at this
    exact lt_irrefl _ this
  refine ⟨Units.mk0 (ϖ : F) hϖ0, hRpw ϖ, ?_, ?_⟩
  · -- `ϖ ∈ 𝔪_P`
    rw [ValuationSubring.mem_unitGroup_iff]
    obtain ⟨⟨a, s'⟩, hϖeq⟩ := IsLocalization.mk'_surjective (S := Rp) 𝔭.primeCompl ϖ
    have hϖmax : ϖ ∈ IsLocalRing.maximalIdeal Rp :=
      (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
    rw [← hϖeq, IsLocalization.AtPrime.mk'_mem_maximal_iff Rp 𝔭] at hϖmax
    have hϖeq' : IsLocalization.mk' Rp a s' = ϖ := hϖeq
    have hspec := IsLocalization.mk'_spec Rp a s'
    rw [hϖeq'] at hspec
    have hF : (ϖ : F) * ((s' : R) : F) = ((a : R) : F) := congrArg Subtype.val hspec
    have ha : v ((a : R) : F) < 1 := (P.w.mem_nonunits_iff).mp ((hmem𝔭 a).mp hϖmax)
    have hs1 : v ((s' : R) : F) = 1 := by
      have h1 : v ((s' : R) : F) ≤ 1 := (P.w.valuation_le_one_iff _).mpr (hRw s')
      have h2 : ((s' : R) : F) ∉ P.w.nonunits := (hmem𝔭 s').not.mp s'.2
      rw [ValuationSubring.mem_nonunits_iff, not_lt] at h2
      exact le_antisymm h1 h2
    intro hv
    have : v ((a : R) : F) = 1 := by
      rw [← hF, map_mul, hs1, mul_one]
      exact hv
    rw [this] at ha
    exact lt_irrefl _ ha
  · intro x
    obtain ⟨a, b, hb, hab0⟩ := IsFractionRing.div_surjective (A := Rp) (x : F)
    have hab : ((a : Rp) : F) / ((b : Rp) : F) = x := hab0
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [Subalgebra.coe_zero, zero_div] at hab
      exact x.ne_zero hab.symm
    obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
    obtain ⟨n, u', hu'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
    refine ⟨(m : ℤ) - n, ?_⟩
    rw [ValuationSubring.mem_unitGroup_iff]
    have hxe : ((x * Units.mk0 (ϖ : F) hϖ0 ^ (-((m : ℤ) - n)) : Fˣ) : F) =
        ((u : Rp) : F) * (((u' : Rp) : F))⁻¹ := by
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, ← hab, hu, hu']
      push_cast
      have hu0 : ((u' : Rp) : F) ≠ 0 := fun h => u'.ne_zero (Subtype.ext h)
      rw [neg_sub, zpow_sub₀ hϖ0, zpow_natCast, zpow_natCast]
      field_simp
    rw [hxe, map_mul, map_inv₀, hU, hU, inv_one, mul_one]

/-- **`BelyiGenusBound` from Riemann–Hurwitz and the fundamental identity** (proved; the uniformizers
at the places containing `t` are `exists_uniformizer`). -/
theorem belyiGenusBound_of_rh_fi (hRH : RiemannHurwitzQj) (hFI : FundamentalIdentityQj) :
    BelyiGenusBound := by
  classical
  intro F _ _ _ _ hK hB
  obtain ⟨hsupp, hRHeq⟩ := hRH F hK
  set Z0 : Set (Place F) := {P | (tF : F) ∈ P.w ∧ (tF : F) ∈ P.w.nonunits} with hZ0
  set Z1 : Set (Place F) := {P | (tF : F) ∈ P.w ∧ (tF : F) - 1 ∈ P.w.nonunits} with hZ1
  set Zi : Set (Place F) := {P | (tF : F) ∉ P.w} with hZi
  obtain ⟨h0, hs0⟩ := hFI F Z0 (by simp [hZ0])
  obtain ⟨h1, hs1⟩ := hFI F Z1 (by simp [hZ1])
  obtain ⟨hi, hsi⟩ := hFI F Zi (by simp [hZi])
  set f : Place F → ℤ := fun P => ((P.ramIdx : ℤ) - 1) * P.deg with hf
  set A := h0.toFinset ∪ h1.toFinset ∪ hi.toFinset with hA
  have hsub : hsupp.toFinset ⊆ A := by
    intro P hP
    rw [Set.Finite.mem_toFinset, Function.mem_support] at hP
    rcases place_cases' hB (fun P ht => exists_uniformizer P ht) P with h | h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr h))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr h))
    · exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr h)
    · exfalso
      apply hP
      show ((P.ramIdx : ℤ) - 1) * P.deg = 0
      rw [h]
      simp
  have hsum : ∑ P ∈ hsupp.toFinset, f P = ∑ P ∈ A, f P :=
    Finset.sum_subset hsub fun P _ hP => by
      rwa [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hP
  have hd01 : Disjoint h0.toFinset h1.toFinset := by
    rw [Finset.disjoint_left]
    intro P hP0 hP1
    rw [Set.Finite.mem_toFinset] at hP0 hP1
    have h1n : (1 : F) ∈ P.w.nonunits := by
      have := P.w.nonunits.sub_mem hP0.2 hP1.2
      rwa [sub_sub_cancel] at this
    rw [ValuationSubring.mem_nonunits_iff, map_one] at h1n
    exact lt_irrefl _ h1n
  have hd : Disjoint (h0.toFinset ∪ h1.toFinset) hi.toFinset := by
    rw [Finset.disjoint_left]
    intro P hP hPi
    rw [Set.Finite.mem_toFinset] at hPi
    rcases Finset.mem_union.mp hP with hP | hP <;> rw [Set.Finite.mem_toFinset] at hP
    · exact hPi hP.1
    · exact hPi hP.1
  rw [hA, Finset.sum_union hd, Finset.sum_union hd01] at hsum
  have hdpos : 0 < Module.finrank Qj F := Module.finrank_pos
  have part : ∀ (Z : Set (Place F)) (hZ : Z.Finite),
      ∑ P ∈ hZ.toFinset, P.ramIdx * P.deg = Module.finrank Qj F →
        ∑ P ∈ hZ.toFinset, f P ≤ (Module.finrank Qj F : ℤ) - 1 := by
    intro Z hZ hs
    have e1 : ∑ P ∈ hZ.toFinset, f P =
        ((∑ P ∈ hZ.toFinset, P.ramIdx * P.deg : ℕ) : ℤ) - ∑ P ∈ hZ.toFinset, (P.deg : ℤ) := by
      push_cast
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun P _ => ?_
      simp only [hf]
      ring
    rw [e1, hs]
    obtain ⟨P, hP, hne⟩ : ∃ P ∈ hZ.toFinset, P.ramIdx * P.deg ≠ 0 := by
      by_contra hc
      push_neg at hc
      rw [Finset.sum_eq_zero hc] at hs
      omega
    have hdeg : 1 ≤ P.deg := Nat.pos_of_ne_zero fun h => hne (by rw [h, mul_zero])
    have : (1 : ℤ) ≤ ∑ P ∈ hZ.toFinset, (P.deg : ℤ) :=
      le_trans (by exact_mod_cast hdeg)
        (Finset.single_le_sum (f := fun P : Place F => (P.deg : ℤ)) (fun P _ => by positivity) hP)
    linarith
  have p0 := part Z0 h0 hs0
  have p1 := part Z1 h1 hs1
  have pi := part Zi hi hsi
  have key : 2 * (fieldGenus F : ℤ) + 1 ≤ Module.finrank Qj F := by
    have := hRHeq
    rw [hsum] at this
    linarith
  exact_mod_cast key

/-- **`DimJ1Le` (the use of T34) from `DimJacobianEqGenus`, Riemann–Hurwitz, the fundamental
identity and `X₀(N)`-transitivity** (proved). -/
theorem dimJ1Le_of_rh_fi (h1 : DimJacobianEqGenus) (hRH : RiemannHurwitzQj)
    (hFI : FundamentalIdentityQj) (h0 : ZInQ.RLeaf.X0Transitive) : DimJ1Le :=
  dimJ1Le_of_belyi h1 (belyiGenusBound_of_rh_fi hRH hFI) h0

end Glue4

/-! ## `FundamentalIdentityQj` from Mathlib's fundamental identity for Dedekind domains -/

section Glue5

open IsDedekindDomain

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F] [Algebra (Polynomial ℚ) F]
  [IsScalarTower (Polynomial ℚ) Qj F]

/-- The coordinate `j` in `F`. -/
abbrev sF : F := algebraMap Qj F RatFunc.X

theorem algebraMap_poly_eq (p : Polynomial ℚ) :
    algebraMap (Polynomial ℚ) F p = Polynomial.aeval (sF : F) p := by
  rw [IsScalarTower.algebraMap_apply (Polynomial ℚ) Qj F]
  have h2 : (algebraMap Qj F).comp (algebraMap (Polynomial ℚ) Qj) =
      (Polynomial.aeval (sF : F)).toRingHom := by
    refine Polynomial.ringHom_ext' (RingHom.ext_rat _ _) ?_
    simp [RatFunc.algebraMap_X]
  exact congrArg (fun φ : Polynomial ℚ →+* F => φ p) h2

/-- The integral closure of `ℚ[j]` lies in every place containing `j`. -/
theorem intCl_mem (P : Place F) (hs : (sF : F) ∈ P.w) (r : integralClosure (Polynomial ℚ) F) :
    (r : F) ∈ P.w := by
  have hpoly : ∀ p : Polynomial ℚ, algebraMap (Polynomial ℚ) F p ∈ P.w := fun p => by
    rw [algebraMap_poly_eq]; exact aeval_mem P hs p
  let φ : Polynomial ℚ →+* P.w := (algebraMap (Polynomial ℚ) F).codRestrict P.w.toSubring hpoly
  obtain ⟨x, hx⟩ := r
  obtain ⟨p, hpm, hp⟩ := hx
  have hint : IsIntegral P.w x := ⟨p.map φ, hpm.map φ, by
    rw [Polynomial.eval₂_map]; exact hp⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  show x ∈ P.w
  rw [← hy]; exact y.2

theorem isSeparable_Qj [FiniteDimensional Qj F] : Algebra.IsSeparable Qj F :=
  Algebra.IsAlgebraic.isSeparable_of_perfectField

theorem isDedekind_intCl [FiniteDimensional Qj F] :
    IsDedekindDomain (integralClosure (Polynomial ℚ) F) :=
  haveI := isSeparable_Qj (F := F)
  integralClosure.isDedekindDomain (Polynomial ℚ) Qj F

theorem isFractionRing_intCl [FiniteDimensional Qj F] :
    IsFractionRing (integralClosure (Polynomial ℚ) F) F :=
  haveI := isSeparable_Qj (F := F)
  IsIntegralClosure.isFractionRing_of_finite_extension (Polynomial ℚ) Qj F _

attribute [local instance] isDedekind_intCl isFractionRing_intCl

variable [FiniteDimensional Qj F]

local notation "OF" => integralClosure (Polynomial ℚ) F

/-- The center on `OF` of a place containing `j`, a height-one prime. -/
noncomputable def centerHS (P : Place F) (hs : (sF : F) ∈ P.w) : HeightOneSpectrum OF where
  asIdeal := (IsLocalRing.maximalIdeal P.w).comap
    ((OF).val.toRingHom.codRestrict P.w.toSubring (intCl_mem P hs))
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro hbot
    apply P.ne_top
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OF) x
    have hb0 : (b : F) ∉ P.w.nonunits := by
      intro h
      have : b ∈ (IsLocalRing.maximalIdeal P.w).comap
          ((OF).val.toRingHom.codRestrict P.w.toSubring (intCl_mem P hs)) := by
        rw [Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]; exact h
      rw [hbot, Ideal.mem_bot] at this
      exact nonZeroDivisors.coe_ne_zero ⟨b, hb⟩ this
    rw [ValuationSubring.mem_nonunits_iff_or] at hb0
    push_neg at hb0
    rw [div_eq_mul_inv]
    exact Subring.mul_mem _ (intCl_mem P hs a) hb0.2

theorem mem_centerHS (P : Place F) (hs : (sF : F) ∈ P.w) (r : OF) :
    r ∈ (centerHS P hs).asIdeal ↔ (r : F) ∈ P.w.nonunits := by
  change r ∈ Ideal.comap _ _ ↔ _
  rw [Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

/-- A place containing `j` is the valuation ring of its center. -/
theorem w_eq_valuationSubring (P : Place F) (hs : (sF : F) ∈ P.w) :
    P.w = ((centerHS P hs).valuation F).valuationSubring := by
  rw [← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  symm
  refine ValuationSubring.eq_of_le_of_ne_top _ ?_ P.ne_top
  rintro x hx
  obtain ⟨a, b, hb, rfl⟩ := hx
  have hb0 : (b : F) ∉ P.w.nonunits := (mem_centerHS P hs b).not.mp hb
  rw [ValuationSubring.mem_nonunits_iff_or] at hb0
  push_neg at hb0
  exact Subring.mul_mem _ (intCl_mem P hs a) hb0.2

/-- The place of a height-one prime of `OF`. -/
noncomputable def placeOf (w : HeightOneSpectrum OF) : Place F where
  w := (w.valuation F).valuationSubring
  ne_top := by
    simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]; infer_instance
  rat_mem c := by
    have hr : ((Polynomial.C c : Polynomial ℚ) : Polynomial ℚ) ∈ (⊤ : Subalgebra (Polynomial ℚ) (Polynomial ℚ)) :=
      trivial
    let r : OF := algebraMap (Polynomial ℚ) OF (Polynomial.C c)
    have : algebraMap ℚ F c = algebraMap OF F r := by
      change _ = algebraMap (Polynomial ℚ) F (Polynomial.C c)
      rw [algebraMap_poly_eq, Polynomial.aeval_C]
    rw [this]
    exact (Valuation.mem_valuationSubring_iff _ _).mpr (HeightOneSpectrum.valuation_le_one _ _)

theorem sF_mem_placeOf (w : HeightOneSpectrum OF) : (sF : F) ∈ (placeOf w).w := by
  have : (sF : F) = algebraMap OF F (algebraMap (Polynomial ℚ) OF Polynomial.X) := by
    change _ = algebraMap (Polynomial ℚ) F Polynomial.X
    rw [algebraMap_poly_eq, Polynomial.aeval_X]
  rw [this]
  exact (Valuation.mem_valuationSubring_iff _ _).mpr (HeightOneSpectrum.valuation_le_one _ _)

theorem placeOf_centerHS (P : Place F) (hs : (sF : F) ∈ P.w) : placeOf (centerHS P hs) = P :=
  Place.ext' (w_eq_valuationSubring P hs).symm

theorem centerHS_placeOf (w : HeightOneSpectrum OF) :
    centerHS (placeOf w) (sF_mem_placeOf w) = w := by
  ext r
  rw [mem_centerHS, ValuationSubring.mem_nonunits_iff_or,
    ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F)]
  change (r : F) = 0 ∨ ((r : F))⁻¹ ∉ (w.valuation F).valuationSubring ↔ _
  rw [Valuation.mem_valuationSubring_iff, map_inv₀, not_le]
  by_cases hr : (r : F) = 0
  · have : algebraMap OF F r = 0 := hr
    simp [hr, this]
  · have h0 : w.valuation F (algebraMap OF F r) ≠ 0 := by
      rw [Valuation.ne_zero_iff]; exact hr
    change _ ↔ w.valuation F (r : F) < 1
    rw [one_lt_inv_iff₀]
    simp only [hr, false_or]
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨zero_lt_iff.mpr h0, h⟩

/-- The prime `(j − a)` of `ℚ[j]`. -/
noncomputable abbrev pa (a : ℚ) : Ideal (Polynomial ℚ) := Ideal.span {Polynomial.X - Polynomial.C a}

theorem pa_isMaximal (a : ℚ) : (pa a).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (Polynomial.irreducible_X_sub_C a)

theorem pa_ne_bot (a : ℚ) : pa a ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]; exact Polynomial.X_sub_C_ne_zero a

/-- The places over `j = a`. -/
def Zfin (F : Type) [Field F] [Algebra Qj F] [Algebra ℚ F] (a : ℚ) : Set (Place F) :=
  {P | (sF : F) ∈ P.w ∧ (sF : F) - algebraMap ℚ F a ∈ P.w.nonunits}

theorem algebraMap_X_sub_C (a : ℚ) :
    ((algebraMap (Polynomial ℚ) OF (Polynomial.X - Polynomial.C a) : OF) : F) =
      (sF : F) - algebraMap ℚ F a := by
  have : ((algebraMap (Polynomial ℚ) OF (Polynomial.X - Polynomial.C a) : OF) : F) =
      algebraMap (Polynomial ℚ) F (Polynomial.X - Polynomial.C a) := rfl
  rw [this, algebraMap_poly_eq, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]

theorem placeOf_mem_Zfin_iff (a : ℚ) (w : HeightOneSpectrum OF) :
    placeOf w ∈ Zfin F a ↔ w.asIdeal ∈ (pa a).primesOver OF := by
  have hpm := pa_isMaximal a
  have key : (sF : F) - algebraMap ℚ F a ∈ (placeOf w).w.nonunits ↔
      algebraMap (Polynomial ℚ) OF (Polynomial.X - Polynomial.C a) ∈ w.asIdeal := by
    conv_rhs => rw [← centerHS_placeOf w]
    rw [mem_centerHS, algebraMap_X_sub_C]
  constructor
  · rintro ⟨-, h⟩
    refine ⟨w.isPrime, ⟨?_⟩⟩
    have hle : pa a ≤ w.asIdeal.under (Polynomial ℚ) := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact key.mp h
    exact hpm.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle
  · rintro ⟨-, hlo⟩
    refine ⟨sF_mem_placeOf w, key.mpr ?_⟩
    have : Polynomial.X - Polynomial.C a ∈ w.asIdeal.under (Polynomial ℚ) := by
      rw [← hlo.over]; exact Ideal.subset_span rfl
    exact this

/-- `e_P` is Mathlib's ramification index (proved below). -/
theorem ramIdx_placeOf (a : ℚ) (w : HeightOneSpectrum OF) (hw : w.asIdeal ∈ (pa a).primesOver OF) :
    (placeOf w).ramIdx = Ideal.ramificationIdx' (pa a) w.asIdeal := by
  sorry

/-- `deg P` is Mathlib's inertia degree (proved below). -/
theorem deg_placeOf (a : ℚ) (w : HeightOneSpectrum OF) (hw : w.asIdeal ∈ (pa a).primesOver OF) :
    (placeOf w).deg = Ideal.inertiaDeg' (pa a) w.asIdeal := by
  sorry

theorem centerHS_congr {P Q : Place F} (h : P = Q) (hP : (sF : F) ∈ P.w) (hQ : (sF : F) ∈ Q.w) :
    centerHS P hP = centerHS Q hQ := by
  subst h; rfl

/-- **The fundamental identity at `j = a`** (proved from Mathlib's for Dedekind domains). -/
theorem fundamentalIdentity_fin (a : ℚ) :
    ∃ h : (Zfin F a).Finite, ∑ P ∈ h.toFinset, P.ramIdx * P.deg = Module.finrank Qj F := by
  classical
  have hpm := pa_isMaximal a
  have hp0 := pa_ne_bot a
  have hinjF : Function.Injective (algebraMap (Polynomial ℚ) F) := by
    rw [IsScalarTower.algebraMap_eq (Polynomial ℚ) Qj F]
    exact (algebraMap Qj F).injective.comp (IsFractionRing.injective (Polynomial ℚ) Qj)
  have : FaithfulSMul (Polynomial ℚ) OF := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro x y hxy
    apply hinjF
    have h1 := congrArg (fun z : OF => (z : F)) hxy
    exact h1
  have : Module.IsTorsionFree (Polynomial ℚ) OF := inferInstance
  have : Module.Finite (Polynomial ℚ) OF := by
    have := isSeparable_Qj (F := F)
    exact IsIntegralClosure.finite (Polynomial ℚ) Qj F OF
  set S := IsDedekindDomain.primesOverFinset (pa a) OF with hS
  have hmemS : ∀ 𝔓, 𝔓 ∈ S ↔ 𝔓 ∈ (pa a).primesOver OF := fun 𝔓 =>
    IsDedekindDomain.mem_primesOverFinset_iff hp0 OF
  let G : ∀ 𝔓 ∈ S, Place F := fun 𝔓 h𝔓 =>
    placeOf ⟨𝔓, ((hmemS 𝔓).mp h𝔓).1, by
      have := ((hmemS 𝔓).mp h𝔓).2
      exact Ideal.ne_bot_of_liesOver_of_ne_bot hp0 𝔓⟩
  have hG : ∀ 𝔓 h𝔓, G 𝔓 h𝔓 ∈ Zfin F a := fun 𝔓 h𝔓 =>
    (placeOf_mem_Zfin_iff a _).mpr ((hmemS 𝔓).mp h𝔓)
  have hZ : Zfin F a = Set.range (fun x : S => G x.1 x.2) := by
    ext P
    constructor
    · intro hP
      have hs := hP.1
      set w := centerHS P hs
      have hPw : placeOf w = P := placeOf_centerHS P hs
      have hw : w.asIdeal ∈ S := (hmemS _).mpr ((placeOf_mem_Zfin_iff a w).mp (hPw ▸ hP))
      refine ⟨⟨w.asIdeal, hw⟩, ?_⟩
      show placeOf _ = P
      convert hPw
    · rintro ⟨x, rfl⟩
      exact hG x.1 x.2
  have hfin : (Zfin F a).Finite := hZ ▸ Set.finite_range _
  refine ⟨hfin, ?_⟩
  rw [← Ideal.sum_ramification_inertia (S := OF) (p := pa a) Qj F hp0]
  symm
  refine Finset.sum_bij G (fun 𝔓 h𝔓 => (Set.Finite.mem_toFinset _).mpr (hG 𝔓 h𝔓)) ?_ ?_ ?_
  · intro 𝔓₁ h₁ 𝔓₂ h₂ he
    have := centerHS_congr he (sF_mem_placeOf _) (sF_mem_placeOf _)
    rw [centerHS_placeOf, centerHS_placeOf] at this
    exact congrArg HeightOneSpectrum.asIdeal this
  · intro P hP
    rw [Set.Finite.mem_toFinset, hZ] at hP
    obtain ⟨⟨𝔓, h𝔓⟩, rfl⟩ := hP
    exact ⟨𝔓, h𝔓, rfl⟩
  · intro 𝔓 h𝔓
    rw [ramIdx_placeOf a _ ((hmemS 𝔓).mp h𝔓), deg_placeOf a _ ((hmemS 𝔓).mp h𝔓)]

end Glue5

end CurveSplit

#print axioms CurveSplit.genusX1Le_of_genusX1Field
#print axioms CurveSplit.dimJ1Le_of
#print axioms CurveSplit.genusX1Le_of_belyi
#print axioms CurveSplit.dimJ1Le_of_belyi
#print axioms CurveSplit.belyiGenusBound_of_leaves
#print axioms CurveSplit.dimJ1Le_of_textbook
#print axioms CurveSplit.exists_uniformizer
#print axioms CurveSplit.belyiGenusBound_of_rh_fi
#print axioms CurveSplit.dimJ1Le_of_rh_fi
