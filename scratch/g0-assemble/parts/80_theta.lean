
/-! ## §3″. g0-thetapoint: `ThetaPointOfFibre` (missing piece 9) from smaller named Props

Task g0-thetapoint, 2026-11-13. `G0Split.ThetaPointOfFibre` (above, unchanged) is proved here
along two routes.

* Route E (`ThetaPt.thetaPointOfFibre_of_qm_ratios`): `ThetaPt.FibreQMPeriod` (GLUE: R1(b) and
  the Hauptmodul comparison on the actual fibre: some uniformization lattice of the fibre is a QM
  lattice `ι(𝒪)(τ, 1)ᵀ` with `j_θ(Ω(τ)) = J(u)`) and `ThetaPt.ThetaRatiosAlgebraic` (LEAF
  candidate: theta-constant ratios at a period matrix of an abelian surface over a number field
  are algebraic numbers). `ThetaRatiosAlgebraic` implies `ThetaPt.ThetaNullAlgebraic` (proved).
* Route A (`ThetaPt.thetaPointOfFibre_of_parts`): `DimBaseChange` (g0-split piece 2, unchanged;
  the model is a surface), `ThetaPt.UniformizationExistsNF` (TEXTBOOK leaf candidate: analytic
  uniformization at some complex place), `ThetaPt.FibreQMPeriodAll` (GLUE: the universal form of
  `FibreQMPeriod`) and `ThetaPt.ThetaNullAlgebraic` (LEAF-COMPOSITE).

Proved glue: the F1 value passes from `ℂ` to the number field (`f1_of_theta`, homogeneity of
degree 0 of `j_θ`), the height comparison (`height_even`, Mathlib's `logHeight_comp_le`; the odd
theta constants are not needed), `Ω(τ) ∈ 𝔥₂` and `Ω(τ)` is a period matrix of every lattice
linearly isomorphic to `ι(𝒪)(τ, 1)ᵀ` (bp-analytic's `ZInQKernel/HDecomp/Analytic/QMLattice.lean`),
the identification of the two copies of `θ_m` and of `Ω(τ)`, and, as a check of the docstring of
`ThetaPointOfFibre`, the vanishing of the six odd theta constants (`thetaConst_odd`). -/

noncomputable section

namespace HSyn

open scoped MatrixGroups ModularForm

namespace G0Split

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings

namespace ThetaPt

open Complex

/-! ### Definitions and connective lemmas -/

/-- F1's theta expression `j_θ(Ω) = 3779136 (∏_{m even} θ_m(0, Ω))⁴ / (Σ_{m even} θ_m(0, Ω)⁸)⁵`,
with leaf-push2's theta constants (`thetaConst`, as in R22). -/
def jTheta (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  3779136 * (∏ m ∈ PkgI1.evenChars, thetaConst Ω m) ^ 4 /
    (∑ m ∈ PkgI1.evenChars, thetaConst Ω m ^ 8) ^ 5

/-- An enumeration `Fin 10 ≃ {even characteristics}`. -/
def evenEnum : Fin 10 ≃ PkgI1.evenChars :=
  (PkgI1.evenChars.equivFin.trans (finCongr PkgI1.card_evenChars)).symm

theorem prod_evenEnum {R : Type*} [CommMonoid R] (g : Char2 → R) :
    ∏ i : Fin 10, g (evenEnum i) = ∏ m ∈ PkgI1.evenChars, g m := by
  rw [← Finset.prod_coe_sort]
  exact Equiv.prod_comp evenEnum (fun m : PkgI1.evenChars => g m)

theorem sum_evenEnum {R : Type*} [AddCommMonoid R] (g : Char2 → R) :
    ∑ i : Fin 10, g (evenEnum i) = ∑ m ∈ PkgI1.evenChars, g m := by
  rw [← Finset.sum_coe_sort]
  exact Equiv.sum_comp evenEnum (fun m : PkgI1.evenChars => g m)

/-- leaf-push2's theta constant is pkg-I1's (`2πi·vᵀ(b/2) = πi·vᵀb`); the proof of
`ZInQ.LeafPush2.thetaConst_eq` (ZInQKernel/HDecomp/LeafPush2/Bridge.lean), repeated. -/
theorem thetaConst_eq_pkgI1 (Ω : Matrix (Fin 2) (Fin 2) ℂ) (m : Char2) :
    thetaConst Ω m = PkgI1.thetaConst m Ω := by
  unfold thetaConst PkgI1.thetaConst
  congr 1
  funext n
  congr 2
  have : (fun i => ((m.2 i : ℕ) : ℂ) / 2) = (1 / 2 : ℂ) • fun i => ((m.2 i : ℕ) : ℂ) := by
    funext i; simp [div_eq_inv_mul]
  rw [this, dotProduct_smul, smul_eq_mul]
  ring

/-- `j_θ = jNum / jDen` in pkg-I1's notation (the function of `PkgI1.QMHauptmodul`). -/
theorem jTheta_eq (Ω : Matrix (Fin 2) (Fin 2) ℂ) :
    jTheta Ω = PkgI1.jNum Ω / PkgI1.jDen Ω := by
  unfold jTheta PkgI1.jNum PkgI1.jDen PkgI1.thetaProd2 PkgI1.thetaSum8
  simp only [thetaConst_eq_pkgI1]
  rw [Finset.prod_pow, ← pow_mul]

/-- pkg-I1's `Ω(τ)` (copied in `Leaves.lean`) is bp-analytic's (the same text). -/
theorem omega_eq (τ : ℂ) : PkgI1.Omega τ = BPAnalytic.QM.Omega τ := rfl

/-- **F1 passes to the number field (glue, proved).** If `emb(z_m) = c·θ_m(Ω)` with `c ≠ 0` and
`j_θ(Ω) = q ∈ ℚ`, then the ten even coordinates of `z` satisfy `Φ(z') = q` in `L` (`j_θ` is
homogeneous of degree `0`: `c⁴⁰` cancels; `emb` is injective). -/
theorem f1_of_theta {L : Type*} [Field L] [CharZero L] (emb : L →+* ℂ)
    (Ω : Matrix (Fin 2) (Fin 2) ℂ) (z : Char2 → L) (c : ℂ) (hc : c ≠ 0)
    (hz : ∀ m, emb (z m) = c * thetaConst Ω m) (q : ℚ) (hJ : jTheta Ω = (q : ℂ)) :
    3779136 * (∏ i, (fun i => z (evenEnum i)) i) ^ 4 /
      (∑ i, (fun i => z (evenEnum i)) i ^ 8) ^ 5 = algebraMap ℚ L q := by
  apply emb.injective
  rw [eq_ratCast (algebraMap ℚ L), map_ratCast, ← hJ]
  simp only [map_div₀, map_mul, map_pow, map_prod, map_sum, map_ofNat, hz]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [mul_pow]
  rw [← Finset.mul_sum, prod_evenEnum (fun m => thetaConst Ω m),
    sum_evenEnum (fun m => thetaConst Ω m ^ 8)]
  unfold jTheta
  set P := ∏ m ∈ PkgI1.evenChars, thetaConst Ω m
  set S := ∑ m ∈ PkgI1.evenChars, thetaConst Ω m ^ 8
  have h40 : c ^ 40 ≠ 0 := pow_ne_zero 40 hc
  calc 3779136 * ((c ^ 10) ^ 4 * P ^ 4) / (c ^ 8 * S) ^ 5
      = c ^ 40 * (3779136 * P ^ 4) / (c ^ 40 * S ^ 5) := by ring
    _ = 3779136 * P ^ 4 / S ^ 5 := mul_div_mul_left _ _ h40

/-- **The height comparison (glue, proved).** Dropping coordinates does not increase the height:
`h(z') ≤ h(z)` for the ten even coordinates `z'` of `z` (Mathlib's `logHeight_comp_le`). -/
theorem height_even {L : Type*} [Field L] [NumberField L] (z : Char2 → L) :
    Height.logHeight (fun i => z (evenEnum i)) / Module.finrank ℚ L ≤ absLogHeight z := by
  unfold absLogHeight
  exact div_le_div_of_nonneg_right (Height.logHeight_comp_le (fun i => (evenEnum i : Char2)) z)
    (Nat.cast_nonneg _)

/-- Transport of `IsPeriodMatrix` along a `ℂ`-linear isomorphism (the proof of
`ZInQ.LeafPush2.isPeriodMatrix_of_map`, repeated). -/
theorem isPeriodMatrix_of_map {Λ Λ' : Submodule ℤ (Fin 2 → ℂ)} {Ω : Matrix (Fin 2) (Fin 2) ℂ}
    (h : IsPeriodMatrix Λ Ω) (F : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ))
    (hF : Λ.map (F.toLinearMap.restrictScalars ℤ) = Λ') : IsPeriodMatrix Λ' Ω := by
  obtain ⟨T, hT⟩ := h
  refine ⟨F.symm.trans T, fun z => ?_⟩
  have hz : z ∈ Λ' ↔ F.symm z ∈ Λ := by
    rw [← hF, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hy
      exact ⟨F.symm z, hy, by simp⟩
  rw [hz, hT]
  rfl

/-- The converse transport: if `F` maps `Λ` onto `Λ'`, a period matrix of `Λ'` is one of `Λ`. -/
theorem isPeriodMatrix_of_comap {Λ Λ' : Submodule ℤ (Fin 2 → ℂ)} {Ω : Matrix (Fin 2) (Fin 2) ℂ}
    (h : IsPeriodMatrix Λ' Ω) (F : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ))
    (hF : Λ.map (F.toLinearMap.restrictScalars ℤ) = Λ') : IsPeriodMatrix Λ Ω := by
  refine isPeriodMatrix_of_map h F.symm ?_
  rw [← hF, ← Submodule.map_comp]
  convert Submodule.map_id Λ
  ext v
  simp

/-- `Ω(τ)` is a period matrix of the QM lattice `Λ_τ = ι(𝒪)(τ, 1)ᵀ` (bp-analytic; the proof of
`ZInQ.LeafPush2.isPeriodMatrix_qmLattice`, repeated). -/
theorem isPeriodMatrix_qmLattice {τ : ℂ} (hτ : τ.im ≠ 0) :
    IsPeriodMatrix (BPAnalytic.QM.qmLattice hτ) (BPAnalytic.QM.Omega τ) :=
  isPeriodMatrix_of_map
    (⟨LinearEquiv.refl ℂ _, fun z => by
      simpa using BPAnalytic.mem_periodLattice_iff _ (BPAnalytic.QM.det_im_Omega_ne_zero hτ) z⟩)
    (BPAnalytic.QM.FpEquiv hτ).toLinearEquiv (BPAnalytic.QM.map_periodLattice_Omega hτ)

/-- `Ω(τ) ∈ 𝔥₂` for `Im τ > 0` (bp-analytic's `Omega_mem_siegelSpace`). -/
theorem isSiegel_Omega {τ : ℂ} (hτ : 0 < τ.im) : IsSiegel (BPAnalytic.QM.Omega τ) :=
  BPAnalytic.QM.Omega_mem_siegelSpace hτ

/-- The odd characteristics: `aᵀb` odd. -/
def IsOddChar (m : Char2) : Prop :=
  ((m.1 0 : ℕ) * (m.2 0 : ℕ) + (m.1 1 : ℕ) * (m.2 1 : ℕ)) % 2 = 1

/-- **The six odd theta constants vanish (proved).** `n ↦ -n - a` maps the term at `n` to minus
itself when `aᵀb` is odd. This checks the docstring of `ThetaPointOfFibre` ("the six odd theta
nulls vanish"); the proof of the piece does not need it (`height_even`). -/
theorem thetaConst_odd (Ω : Matrix (Fin 2) (Fin 2) ℂ) (m : Char2) (hm : IsOddChar m) :
    thetaConst Ω m = 0 := by
  set a : Fin 2 → ℤ := fun i => ((m.1 i : ℕ) : ℤ)
  set f : (Fin 2 → ℤ) → ℂ := fun n => Complex.exp (Real.pi * I *
        ((fun i => (n i : ℂ) + ((m.1 i : ℕ) : ℂ) / 2) ⬝ᵥ
          Ω.mulVec (fun i => (n i : ℂ) + ((m.1 i : ℕ) : ℂ) / 2)) +
      2 * Real.pi * I *
        ((fun i => (n i : ℂ) + ((m.1 i : ℕ) : ℂ) / 2) ⬝ᵥ (fun i => ((m.2 i : ℕ) : ℂ) / 2))) with hf
  let e : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) :=
    { toFun := fun n => -n - a, invFun := fun n => -n - a,
      left_inv := fun n => by simp, right_inv := fun n => by simp }
  have hv : ∀ n : Fin 2 → ℤ, (fun i => ((e n i : ℤ) : ℂ) + ((m.1 i : ℕ) : ℂ) / 2) =
      -(fun i => (n i : ℂ) + ((m.1 i : ℕ) : ℂ) / 2) := by
    intro n; funext i
    simp only [e, Equiv.coe_fn_mk, Pi.sub_apply, Pi.neg_apply, a, Int.cast_sub, Int.cast_neg,
      Int.cast_natCast]
    ring
  -- the parity: `aᵀb = 2k + 1`
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (m.1 0 : ℕ) * (m.2 0 : ℕ) + (m.1 1 : ℕ) * (m.2 1 : ℕ) = 2 * k + 1 :=
    ⟨((m.1 0 : ℕ) * (m.2 0 : ℕ) + (m.1 1 : ℕ) * (m.2 1 : ℕ)) / 2, by unfold IsOddChar at hm; omega⟩
  have hfe : ∀ n, f (e n) = - f n := by
    intro n
    simp only [hf]
    rw [hv n, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg, neg_dotProduct]
    set Q := (fun i => (n i : ℂ) + ((m.1 i : ℕ) : ℂ) / 2) ⬝ᵥ
          Ω.mulVec (fun i => (n i : ℂ) + ((m.1 i : ℕ) : ℂ) / 2)
    set D := (fun i => (n i : ℂ) + ((m.1 i : ℕ) : ℂ) / 2) ⬝ᵥ (fun i => ((m.2 i : ℕ) : ℂ) / 2)
    -- `2·2πi·D = 2πi (nᵀb) + πi (aᵀb)`
    have hD : 2 * D = ((n 0 * (m.2 0 : ℕ) + n 1 * (m.2 1 : ℕ) + k : ℤ) : ℂ) + 1 / 2 := by
      have hk' : ((m.1 0 : ℕ) : ℂ) * ((m.2 0 : ℕ) : ℂ) + ((m.1 1 : ℕ) : ℂ) * ((m.2 1 : ℕ) : ℂ)
          = 2 * (k : ℂ) + 1 := by exact_mod_cast hk
      simp only [D, dotProduct, Fin.sum_univ_two]
      push_cast
      linear_combination (1 / 2 : ℂ) * hk'
    have hexp : Complex.exp (2 * Real.pi * I * D) =
        - Complex.exp (2 * Real.pi * I * (-D)) := by
      have h2 : 2 * Real.pi * I * D = 2 * Real.pi * I * (-D) +
          (((n 0 * (m.2 0 : ℕ) + n 1 * (m.2 1 : ℕ) + k : ℤ) : ℂ) * (2 * Real.pi * I) +
            Real.pi * I) := by
        linear_combination (2 * Real.pi * I) * hD
      rw [h2, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
        Complex.exp_pi_mul_I]
      ring
    rw [Complex.exp_add, Complex.exp_add, hexp]
    ring
  have h : thetaConst Ω m = - thetaConst Ω m := by
    change ∑' n, f n = - ∑' n, f n
    rw [← tsum_neg, ← Equiv.tsum_eq e f]
    exact tsum_congr hfe
  have h2 : (2 : ℂ) * thetaConst Ω m = 0 := by linear_combination h
  simpa using h2

/-! ### The smaller named Props -/

/-- **TEXTBOOK leaf candidate (analytic uniformization at a complex place).** An abelian surface
`A` over a number field `K` has, at some embedding `σ : K → ℂ`, an analytic uniformization
`Φ : ℂ² → A(ℂ)_σ` with kernel `Λ` (`IsUniformization`: surjective homomorphism, kernel `Λ`, open
preimages of affine charts, holomorphic regular functions). Mumford, *Abelian Varieties*, §1
(`X(ℂ)` is a complex torus `ℂ^g/Λ`) with Serre's GAGA for the holomorphy of regular functions
(locators UNVERIFIED). In the build: `ZInQKernel/HDecomp/LeafPush2/UnifBridge.lean`,
`exists_isUniformization_of_leaf`, gives it over `ℂ` from bp-analytic's `UniformizationLeafAll`;
here `σ` exists because `K` is a number field. -/
def UniformizationExistsNF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K), A.dim = (2 : WithBot ℕ∞) →
    ∃ (σ : K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ)) (Φu : (Fin 2 → ℂ) → CPts A σ),
      IsUniformization σ Λ Φu

/-- **GLUE (G19, F1 analytic on the actual fibre: R1(b) with the Hauptmodul comparison).** For
`u ∉ 𝒞`, every number-field model `A` of the fibre surface over `J(u)` (`FibreOver`), every
complex place `σ` and every analytic uniformization `Φ : ℂ² → A(ℂ)_σ` with kernel `Λ`: there are
`τ ∈ ℍ` and a `ℂ`-linear automorphism `F` of `ℂ²` carrying `Λ` onto the QM lattice
`Λ_τ = ι(𝒪)(τ, 1)ᵀ` (bp-analytic's `qmLattice`, N5's basis of `𝒪`), with F1's value
`jNum(Ω(τ)) / jDen(Ω(τ)) = J(u)` (pkg-I1's `Ω(τ)`, the period matrix of the principal
polarization `Trd(μ⁻¹xȳ)` of `ℂ²/Λ_τ`).

Why true (model argument, no human review). `σ` factors as `ℚ̄ → ℂ` after a Galois conjugate of
the embedding of `FibreOver`; `π` is defined over `ℚ` and `J(u) ∈ ℚ`, so the conjugate object of
`Y₃` again lies over `J(u)`. R1(b) (`R01b_ComplexUniformization`, a placeholder: Shimura 1967,
Main Thm I) gives `τ ∈ ℍ` with `A(ℂ)_σ ≅ ℂ²/Λ_τ`, and two uniformizations of one complex torus
differ by a linear automorphism of `ℂ²` (bp-analytic, `IsUniformization.continuous_comparison`
and its sequel). The value: `τ ↦ π(P_τ)` (R1(b)(c)) and the function `f` of
`PkgI1.QMHauptmodul` (a consequence of R2-R4) are Hauptmoduln of `Γ*\ℍ = X₆/W` with the same
values `0, ∞, -16/27` at the CM points of discriminants `-4, -3, -24` (`R2fpProps`), so they are
equal (a Möbius map fixing three points is the identity); `jDen(Ω(τ)) ≠ 0` because `J(u) ≠ ∞`
and `χ₁₀(Ω(τ)) ≠ 0` for the simple surface `A` (`FibreSimple`). The polarization of the QM
object plays no role (`f` and `π` are compared as functions of `τ`); like every leaf-qm-fp object
this inherits the SPECULATIVE premise bp-qmmoduli §2.2 through `R1fpProps`, `R2fpProps`. Size: large (it
needs the analytification of `Y₃` and of the universal family, rv-blueprints Q3). -/
def FibreQMPeriodAll : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K), FibreOver Y Φ π u K A →
    ∀ (σ : K.K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ))
      (Φu : (Fin 2 → ℂ) → CPts (LeafAdopt.abVarEquiv K.K A) σ), IsUniformization σ Λ Φu →
    ∃ (τ : ℂ) (hτ : 0 < τ.im) (F : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ)),
      Λ.map (F.toLinearMap.restrictScalars ℤ) = BPAnalytic.QM.qmLattice hτ.ne' ∧
      PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) = ((Jmap u : ℚ) : ℂ)

/-- **GLUE (G19, F1 analytic on the actual fibre; the existential form of `FibreQMPeriodAll`).**
For `u ∉ 𝒞` and every number-field model `A` of the fibre surface over `J(u)`: at some complex
place `σ`, some analytic uniformization `Φ : ℂ² → A(ℂ)_σ` has a kernel `Λ` carried onto a QM
lattice `Λ_τ = ι(𝒪)(τ, 1)ᵀ` (`τ ∈ ℍ`) by a `ℂ`-linear automorphism, with
`jNum(Ω(τ)) / jDen(Ω(τ)) = J(u)`. It follows from `DimBaseChange`, `UniformizationExistsNF` and
`FibreQMPeriodAll` (`fibreQMPeriod_of_all`), and with `ThetaNullAlgebraic` alone it gives
`ThetaPointOfFibre` (`thetaPointOfFibre_of_qm`). Why true: as for `FibreQMPeriodAll`, at the
place `σ` through which the embedding of `FibreOver` factors (no Galois conjugation needed). -/
def FibreQMPeriod : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K), FibreOver Y Φ π u K A →
    ∃ (σ : K.K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ))
      (Φu : (Fin 2 → ℂ) → CPts (LeafAdopt.abVarEquiv K.K A) σ), IsUniformization σ Λ Φu ∧
    ∃ (τ : ℂ) (hτ : 0 < τ.im) (F : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ)),
      Λ.map (F.toLinearMap.restrictScalars ℤ) = BPAnalytic.QM.qmLattice hτ.ne' ∧
      PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) = ((Jmap u : ℚ) : ℂ)

/-- **LEAF-COMPOSITE (algebraicity of theta constants).** For an abelian variety `A` over a
number field `K`, an analytic uniformization `Φ : ℂ² → A(ℂ)_σ` with kernel `Λ` and any
`Ω ∈ 𝔥₂` that is a period matrix of `Λ` (that is, any principal polarization of `ℂ²/Λ` with any
symplectic basis), the sixteen theta constants `θ_m(0, Ω)` are, up to one nonzero factor `c`, the
image of a point `z ∈ L¹⁶` of a number field `L` under an embedding `L → ℂ`.

Sources: the principal polarization of `A(ℂ)_σ` is algebraic (Lefschetz, Appell–Humbert with
GAGA) and defined over `ℚ̄` (`NS(A_ℚ̄) = NS(A_ℂ)`); theta-constant ratios of a principally
polarized abelian variety over `ℚ̄` are algebraic: for genus 2, Thomae's formula expresses
`θ_m⁴/θ_{m'}⁴` through the Rosenhain roots of the curve (Mumford, *Tata Lectures on Theta II*,
IIIa §8; for a product of elliptic curves, Jacobi's formulas), and in general Shimura's theorem
on special values of Siegel modular functions with algebraic Fourier coefficients (Shimura,
*Theta functions with complex multiplication*, Duke 43 (1976), and Faltings–Chai, Ch. V) (all
locators UNVERIFIED). Not one printed theorem: a composite of published results, so a leaf
candidate to be reviewed, not a leaf. -/
def ThetaNullAlgebraic : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (σ : K →+* ℂ)
    (Λ : Submodule ℤ (Fin 2 → ℂ)) (Φu : (Fin 2 → ℂ) → CPts A σ), IsUniformization σ Λ Φu →
    ∀ Ω : Matrix (Fin 2) (Fin 2) ℂ, IsSiegel Ω → IsPeriodMatrix Λ Ω →
    ∃ (L : GlueAssembly.NF) (emb : L.K →+* ℂ) (z : Char2 → L.K) (c : ℂ), c ≠ 0 ∧
      ∀ m, emb (z m) = c * thetaConst Ω m

/-- **LEAF candidate (theta-constant ratios are algebraic numbers).** For an abelian variety `A`
over a number field `K`, a uniformization `Φ : ℂ² → A(ℂ)_σ` with kernel `Λ` and any period matrix
`Ω ∈ 𝔥₂` of `Λ`: some theta constant `θ_{m₀}(0, Ω)` is nonzero and every ratio
`θ_m(0, Ω)/θ_{m₀}(0, Ω)` is an algebraic number. This is the form in which the literature states
it (values of Siegel modular functions with algebraic Fourier coefficients at a point whose
principally polarized abelian variety is defined over `ℚ̄` are algebraic: Shimura, Duke 43 (1976);
for genus 2 also Thomae's formula, Mumford, *Tata Lectures on Theta II*, IIIa §8; with
`NS(A_ℚ̄) = NS(A_ℂ)` for the polarization defined by `Ω`; all locators UNVERIFIED). Nonvanishing:
at most one of the ten even `θ_m(0, Ω)` vanishes in genus 2 (it vanishes exactly on products of
elliptic curves; UNVERIFIED locator: Igusa 1962/1967). `ThetaNullAlgebraic` follows
(`thetaNullAlgebraic_of_ratios`, proved). -/
def ThetaRatiosAlgebraic : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (σ : K →+* ℂ)
    (Λ : Submodule ℤ (Fin 2 → ℂ)) (Φu : (Fin 2 → ℂ) → CPts A σ), IsUniformization σ Λ Φu →
    ∀ Ω : Matrix (Fin 2) (Fin 2) ℂ, IsSiegel Ω → IsPeriodMatrix Λ Ω →
    ∃ m₀ : Char2, thetaConst Ω m₀ ≠ 0 ∧ ∀ m, IsAlgebraic ℚ (thetaConst Ω m / thetaConst Ω m₀)

/-- Finitely many algebraic complex numbers lie in the image of a number field (`ℚ(α_i) ⊆ ℂ`). -/
theorem exists_nf_of_isAlgebraic {Idx : Type} [Fintype Idx] (α : Idx → ℂ)
    (h : ∀ i, IsAlgebraic ℚ (α i)) :
    ∃ (L : GlueAssembly.NF) (emb : L.K →+* ℂ) (z : Idx → L.K), ∀ i, emb (z i) = α i := by
  set E : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (Set.range α)
  have hfd : FiniteDimensional ℚ E := by
    apply IntermediateField.finiteDimensional_adjoin
    rintro x ⟨i, rfl⟩
    exact (h i).isIntegral
  have : NumberField E := ⟨⟩
  exact ⟨⟨E⟩, E.val.toRingHom, fun i => ⟨α i, IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩⟩,
    fun i => rfl⟩

/-- **`ThetaNullAlgebraic` from `ThetaRatiosAlgebraic` (proved):** `L = ℚ(θ_m/θ_{m₀})`,
`c = θ_{m₀}⁻¹`. -/
theorem thetaNullAlgebraic_of_ratios (h : ThetaRatiosAlgebraic) : ThetaNullAlgebraic := by
  intro K _ _ A σ Λ Φu hU Ω hS hP
  obtain ⟨m₀, h0, halg⟩ := h K A σ Λ Φu hU Ω hS hP
  obtain ⟨L, emb, z, hz⟩ := exists_nf_of_isAlgebraic _ halg
  exact ⟨L, emb, z, (thetaConst Ω m₀)⁻¹, inv_ne_zero h0, fun m => by
    rw [hz m, div_eq_inv_mul]⟩

/-- **GLUE (G19, F1 analytic; proved below from `DimBaseChange`, `UniformizationExistsNF` and
`FibreQMPeriodAll`).** For `u ∉ 𝒞` and every model `A` of the fibre surface over `J(u)`: some
analytic uniformization of `A(ℂ)_σ` with a period matrix `Ω ∈ 𝔥₂` such that `j_θ(Ω) = J(u)`. -/
def FibreThetaF1 : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K), FibreOver Y Φ π u K A →
    ∃ (σ : K.K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ))
      (Φu : (Fin 2 → ℂ) → CPts (LeafAdopt.abVarEquiv K.K A) σ), IsUniformization σ Λ Φu ∧
    ∃ Ω : Matrix (Fin 2) (Fin 2) ℂ, IsSiegel Ω ∧ IsPeriodMatrix Λ Ω ∧
      jTheta Ω = ((Jmap u : ℚ) : ℂ)

/-! ### The proofs -/

/-- **`ThetaPointOfFibre` from F1-analytic and algebraicity (proved).** Take `K' = L` and `z'`
the ten even coordinates of the algebraic theta point `z`. -/
theorem thetaPointOfFibre_of (hF1 : FibreThetaF1) (hAlg : ThetaNullAlgebraic) :
    ThetaPointOfFibre := by
  intro Y Φ π h1 h2 u hu K A hFib
  obtain ⟨σ, Λ, Φu, hU, Ω, hS, hP, hJ⟩ := hF1 Y Φ π h1 h2 u hu K A hFib
  obtain ⟨L, emb, z, c, hc, hz⟩ := hAlg K.K (LeafAdopt.abVarEquiv K.K A) σ Λ Φu hU Ω hS hP
  exact ⟨σ, Λ, Φu, hU, Ω, hS, hP, L, emb, z, c, hc, hz, L, fun i => z (evenEnum i),
    f1_of_theta emb Ω z c hc hz (Jmap u) hJ, height_even z⟩

/-- **The existential form (proved)** from `DimBaseChange` (the model is a surface,
`model_dim`), `UniformizationExistsNF` and `FibreQMPeriodAll`. -/
theorem fibreQMPeriod_of_all (hDim : DimBaseChange) (hU : UniformizationExistsNF)
    (hQM : FibreQMPeriodAll) : FibreQMPeriod := by
  intro Y Φ π h1 h2 u hu K A hFib
  obtain ⟨emb, y, P, hP, hy, hiso⟩ := hFib
  have hA2 : A.dim = 2 := model_dim hDim emb A P.A hiso P.surface
  obtain ⟨σ, Λ, Φu, hΦu⟩ := hU K.K (LeafAdopt.abVarEquiv K.K A) hA2
  exact ⟨σ, Λ, Φu, hΦu, hQM Y Φ π h1 h2 u hu K A ⟨emb, y, P, hP, hy, hiso⟩ σ Λ Φu hΦu⟩

/-- **F1-analytic on the fibre (proved)** from `FibreQMPeriod`, with `Ω = Ω(τ)`
(bp-analytic: `Ω(τ) ∈ 𝔥₂`, and `Ω(τ)` is a period matrix of `Λ_τ`, hence of `Λ`). -/
theorem fibreThetaF1_of_qm (hQM : FibreQMPeriod) : FibreThetaF1 := by
  intro Y Φ π h1 h2 u hu K A hFib
  obtain ⟨σ, Λ, Φu, hΦu, τ, hτ, F, hF, hJ⟩ := hQM Y Φ π h1 h2 u hu K A hFib
  refine ⟨σ, Λ, Φu, hΦu, BPAnalytic.QM.Omega τ, isSiegel_Omega hτ,
    isPeriodMatrix_of_comap (isPeriodMatrix_qmLattice hτ.ne') F hF, ?_⟩
  rw [jTheta_eq, ← omega_eq]
  exact hJ

/-- F1-analytic on the fibre from `DimBaseChange`, `UniformizationExistsNF`, `FibreQMPeriodAll`. -/
theorem fibreThetaF1_of (hDim : DimBaseChange) (hU : UniformizationExistsNF)
    (hQM : FibreQMPeriodAll) : FibreThetaF1 :=
  fibreThetaF1_of_qm (fibreQMPeriod_of_all hDim hU hQM)

/-- **Missing piece 9, `ThetaPointOfFibre`, from two named Props (proved):** the existential
F1-analytic glue `FibreQMPeriod` and the algebraicity of theta constants. -/
theorem thetaPointOfFibre_of_qm (hQM : FibreQMPeriod) (hAlg : ThetaNullAlgebraic) :
    ThetaPointOfFibre :=
  thetaPointOfFibre_of (fibreThetaF1_of_qm hQM) hAlg

/-- **Missing piece 9 from the existential F1 glue and the ratio form of algebraicity (proved).** -/
theorem thetaPointOfFibre_of_qm_ratios (hQM : FibreQMPeriod) (hAlg : ThetaRatiosAlgebraic) :
    ThetaPointOfFibre :=
  thetaPointOfFibre_of_qm hQM (thetaNullAlgebraic_of_ratios hAlg)

/-- **Missing piece 9, `ThetaPointOfFibre`, from strictly smaller named Props (proved).** -/
theorem thetaPointOfFibre_of_parts (hDim : DimBaseChange) (hU : UniformizationExistsNF)
    (hQM : FibreQMPeriodAll) (hAlg : ThetaNullAlgebraic) : ThetaPointOfFibre :=
  thetaPointOfFibre_of (fibreThetaF1_of hDim hU hQM) hAlg

end ThetaPt

end G0Split

end HSyn

end
