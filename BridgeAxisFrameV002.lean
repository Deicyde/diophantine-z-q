import BridgeSeriesV002
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.CoefficientCoordinates

/-!
# A derived fixed-weight finite axis frame

The localized coefficient forms are actual level-one forms. Their proved
rational spans are transported into one Gamma-one target weight, and a
finite representation is then produced by span induction. All-row field
coordinate descent replaces the finitely many complex scalars by scalars
in the actual cyclotomic coefficient field, with no supplied basis.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm BigOperators

namespace BridgeAxisFrame

open ZInQ.Contrib.HeckePrimeRationality
open DirectTorsionOrbit DirectOrbitInterpolation DirectLevelOneInterpolation
open BridgeDenominator BridgeLambda BridgeSeries

/-- A finite family representing one element of an actual complex span. -/
theorem finite_span_representation {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {W : ℤ}
    (S : Set (ModularForm Γ W)) (f : ModularForm Γ W) (hf : f ∈ Submodule.span ℂ S) :
    ∃ J : Type, ∃ hJ : Fintype J,
      letI := hJ
      ∃ F : J → ModularForm Γ W, ∃ c : J → ℂ,
        (∀ i, F i ∈ S) ∧ f = ∑ i, c i • F i := by
  classical
  refine Submodule.span_induction (p := fun f _ =>
    ∃ J : Type, ∃ hJ : Fintype J, letI := hJ;
      ∃ F : J → ModularForm Γ W, ∃ c : J → ℂ,
        (∀ i, F i ∈ S) ∧ f = ∑ i, c i • F i) ?_ ?_ ?_ ?_ hf
  · intro g hg
    refine ⟨Unit, inferInstance, (fun _ => g), (fun _ => 1), (fun _ => hg), ?_⟩
    simp
  · refine ⟨Empty, inferInstance, Empty.elim, Empty.elim, (fun i => Empty.elim i), ?_⟩
    simp
  · intro f g _ _ hf hg
    obtain ⟨J, hJ, F, c, hF, hf⟩ := hf
    obtain ⟨L, hL, G, d, hG, hg⟩ := hg
    letI := hJ
    letI := hL
    refine ⟨Sum J L, inferInstance, Sum.elim F G, Sum.elim c d, ?_, ?_⟩
    · intro i
      cases i with
      | inl i => exact hF i
      | inr i => exact hG i
    · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hf, hg]
  · intro a f _ hf
    obtain ⟨J, hJ, F, c, hF, hf⟩ := hf
    letI := hJ
    refine ⟨J, hJ, F, (fun i => a * c i), hF, ?_⟩
    rw [hf, Finset.smul_sum]
    simp only [smul_smul]

/-- One actual fixed-weight term, with the level-one coefficient and the raw unit power. -/
def axisTerm (N : ℕ) [NeZero N] (hN : 3 ≤ N) (W : ℤ) (j : ℕ)
    (R : ModularForm 𝒮ℒ (W - (j : ℤ))) (u : (ZMod N)ˣ) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) W :=
  ModularForm.mcast (by ring)
    ((restrictLevelOne N _ R).mul (unitPower N hN u j))

/-- Its exact analytic value is the product of the actual forms, in the raw normalization. -/
theorem axisTerm_apply (N : ℕ) [NeZero N] (hN : 3 ≤ N) (W : ℤ) (j : ℕ)
    (R : ModularForm 𝒮ℒ (W - (j : ℤ))) (u : (ZMod N)ˣ) (τ : ℍ) :
    axisTerm N hN W j R u τ = R τ * lambdaForm N hN u τ ^ j := by
  simp only [axisTerm, ModularForm.mcast_apply, ModularForm.coe_mul, Pi.mul_apply,
    restrictLevelOne_coe, unitPower, ModularForm.coe_mcast, ModularForm.coe_pow, Pi.pow_apply]

/-- The actual series of a fixed-weight term is the corresponding formal product. -/
theorem axisTerm_qExpansion (N : ℕ) [NeZero N] (hN : 3 ≤ N) (W : ℤ) (j : ℕ)
    (R : ModularForm 𝒮ℒ (W - (j : ℤ))) (u : (ZMod N)ˣ) :
    qExpansion 1 (axisTerm N hN W j R u) =
      qExpansion 1 R * (qExpansion 1 (lambdaForm N hN u)) ^ j := by
  simp only [axisTerm, ModularForm.coe_mcast]
  rw [ModularForm.qExpansion_mul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N),
    unitPower_qExpansion]
  rfl

/-- Weight casts commute with the actual diamond endomorphism. -/
theorem diamond_mcast {N : ℕ} {a b : ℤ} (hab : a = b) (u : (ZMod N)ˣ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) a) :
    diamondOp b u (ModularForm.mcast hab f) = ModularForm.mcast hab (diamondOp a u f) := by
  cases hab
  rfl

/-- The actual diamond transport keeps the same one target weight. -/
theorem diamond_axisTerm (N : ℕ) [NeZero N] (hN : 3 ≤ N) (W : ℤ) (j : ℕ)
    (R : ModularForm 𝒮ℒ (W - (j : ℤ))) (u v : (ZMod N)ˣ) :
    diamondOp W u (axisTerm N hN W j R v) = axisTerm N hN W j R (u * v) := by
  rw [axisTerm, diamond_mcast, BridgeLambda.diamond_mul,
    diamond_restrictLevelOne, diamond_unitPower]
  rfl

/-- The term map is genuinely complex linear on the actual level-one coefficient space. -/
def axisTermMap (N : ℕ) [NeZero N] (hN : 3 ≤ N) (W : ℤ) (j : ℕ) (u : (ZMod N)ˣ) :
    ModularForm 𝒮ℒ (W - (j : ℤ)) →ₗ[ℂ] ModularForm ((Gamma1 N).map (mapGL ℝ)) W where
  toFun R := axisTerm N hN W j R u
  map_add' R S := by
    ext τ
    simp only [axisTerm_apply, _root_.add_apply]
    ring
  map_smul' a R := by
    ext τ
    simp only [axisTerm_apply, _root_.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The actual frame set, defined from rational level-one forms and bounded powers of the raw torsion form. -/
def frameSet (N : ℕ) [NeZero N] (hN : 3 ≤ N) (W : ℤ) :
    Set (ModularForm ((Gamma1 N).map (mapGL ℝ)) W) :=
  {f | ∃ j : Fin (orbitLength N), ∃ R : ModularForm 𝒮ℒ (W - (j : ℤ)),
    DirectLevelOneArithmetic.IsRat R ∧ f = axisTerm N hN W (j : ℕ) R 1}

/-- The proved rational span of an actual level-one space maps into this fixed-weight frame span. -/
theorem axisTermMap_mem_span (N : ℕ) [NeZero N] (hN : 3 ≤ N) (W : ℤ)
    (j : Fin (orbitLength N)) (R : ModularForm 𝒮ℒ (W - (j : ℤ))) :
    axisTermMap N hN W (j : ℕ) 1 R ∈ Submodule.span ℂ (frameSet N hN W) := by
  have hR : R ∈ DirectLevelOneArithmetic.rationalSpan (W - (j : ℤ)) := by
    rw [DirectLevelOneArithmetic.rationalSpan_all]
    exact Submodule.mem_top
  change R ∈ Submodule.span ℂ {R | DirectLevelOneArithmetic.IsRat R} at hR
  refine Submodule.span_induction (p := fun R _ =>
    axisTermMap N hN W (j : ℕ) 1 R ∈ Submodule.span ℂ (frameSet N hN W))
    (fun R hR => Submodule.subset_span ⟨j, R, hR, rfl⟩)
    (by rw [map_zero]; exact Submodule.zero_mem _) ?_ ?_ hR
  · intro A B _ _ hA hB
    rw [map_add]
    exact Submodule.add_mem _ hA hB
  · intro a A _ hA
    rw [map_smul]
    exact Submodule.smul_mem _ a hA

/-- The actual denominator product lives in one unchanged Gamma-one level and one target weight. -/
def denominatorProduct (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℤ)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) (k + 2 * orbitWeight N) :=
  ModularForm.mcast (by ring)
    ((restrictLevelOne N _ (DirectLocalizedTorsionGeneration.denominator N hN)).mul g)

/-- Its analytic product is the actual denominator times the original form. -/
theorem denominatorProduct_apply (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℤ)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (τ : ℍ) :
    denominatorProduct N hN k g τ = DirectLocalizedTorsionGeneration.denominator N hN τ * g τ := by
  simp only [denominatorProduct, ModularForm.mcast_apply, ModularForm.coe_mul,
    Pi.mul_apply, restrictLevelOne_coe]

/-- The actual width-one product identity, using the genuine Gamma-one fields. -/
theorem denominatorProduct_qExpansion (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℤ)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    qExpansion 1 (denominatorProduct N hN k g) =
      qExpansion 1 (DirectLocalizedTorsionGeneration.denominator N hN) * qExpansion 1 g := by
  simp only [denominatorProduct, ModularForm.coe_mcast]
  rw [ModularForm.qExpansion_mul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N)]
  rfl

/-- Localized generation and the derived level-one rational spans produce the frame membership. -/
theorem denominatorProduct_mem_span (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℤ)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    denominatorProduct N hN k g ∈ Submodule.span ℂ (frameSet N hN (k + 2 * orbitWeight N)) := by
  have he : denominatorProduct N hN k g =
      ∑ j : Fin (orbitLength N), axisTermMap N hN (k + 2 * orbitWeight N) (j : ℕ) 1
        (levelOneCoefficient N hN k g j) := by
    apply ModularForm.ext
    intro τ
    rw [denominatorProduct_apply]
    simpa only [axisTermMap, LinearMap.coe_mk, AddHom.coe_mk, axisTerm_apply,
      _root_.sum_apply, lambdaForm_one, baseLambda_coe] using
      DirectLocalizedTorsionGeneration.localized_generation N hN k g τ
  rw [he]
  exact Submodule.sum_mem _ (fun j _ => axisTermMap_mem_span N hN _ j _)

/-- Every rational level-one coefficient and actual unit power gives cyclotomic coefficients. -/
theorem axisTerm_coefficients_mem (N : ℕ) [NeZero N] (hN : 3 ≤ N) (W : ℤ) (j : ℕ)
    (R : ModularForm 𝒮ℒ (W - (j : ℤ))) (hR : DirectLevelOneArithmetic.IsRat R)
    (u : (ZMod N)ˣ) :
    ∀ n : ℕ, (qExpansion 1 (axisTerm N hN W j R u)).coeff n ∈ Torsion.coefficientField N := by
  have hRK : ∀ n, (qExpansion 1 R).coeff n ∈ Torsion.coefficientField N := by
    intro n
    obtain ⟨q, hq⟩ := hR n
    rw [hq]
    exact KnownFieldCoefficientCoordinates.rational_mem _ q
  rw [axisTerm_qExpansion]
  exact coefficients_mem_mul _ _ _ hRK
    (coefficients_mem_pow _ _ (lambdaForm_coefficients_mem N hN u) j)

/-- Every member of the derived fixed-weight frame has actual cyclotomic coefficients. -/
theorem frame_coefficients_mem (N : ℕ) [NeZero N] (hN : 3 ≤ N) (W : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) W) (hf : f ∈ frameSet N hN W) :
    ∀ n : ℕ, (qExpansion 1 f).coeff n ∈ Torsion.coefficientField N := by
  obtain ⟨j, R, hR, rfl⟩ := hf
  exact axisTerm_coefficients_mem N hN W (j : ℕ) R hR 1

/-- Rational input gives field coefficients for the actual denominator product, without Hecke or diamond closure. -/
theorem denominatorProduct_coefficients_mem (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℤ)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg : ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 g).coeff n = (q : ℂ)) :
    ∀ n : ℕ, (qExpansion 1 (denominatorProduct N hN k g)).coeff n ∈ Torsion.coefficientField N := by
  have hgK : ∀ n, (qExpansion 1 g).coeff n ∈ Torsion.coefficientField N := by
    intro n
    obtain ⟨q, hq⟩ := hg n
    rw [hq]
    exact KnownFieldCoefficientCoordinates.rational_mem _ q
  rw [denominatorProduct_qExpansion]
  exact coefficients_mem_mul _ _ _ (BridgeDenominator.denominator_coefficients_mem N hN) hgK

/-- The finitely many field scalars are produced by all-row descent from the derived frame. -/
theorem exists_field_frame_coordinates (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℤ)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg : ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 g).coeff n = (q : ℂ)) :
    ∃ J : Type, ∃ hJ : Fintype J,
      letI := hJ
      ∃ F : J → ModularForm ((Gamma1 N).map (mapGL ℝ)) (k + 2 * orbitWeight N),
      ∃ c : J → Torsion.coefficientField N,
        (∀ i, F i ∈ frameSet N hN (k + 2 * orbitWeight N)) ∧
          denominatorProduct N hN k g = ∑ i, (c i : ℂ) • F i := by
  classical
  obtain ⟨J, hJ, F, c, hF, hrep⟩ := finite_span_representation _ _
    (denominatorProduct_mem_span N hN k g)
  letI := hJ
  have hFK := fun i => frame_coefficients_mem N hN _ (F i) (hF i)
  obtain ⟨d, hd⟩ := ModularFormCoefficientCoordinates.exists_coordinates
    one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N) (Torsion.coefficientField N)
      F hFK (denominatorProduct N hN k g) (denominatorProduct_coefficients_mem N hN k g hg) c hrep
  exact ⟨J, hJ, F, d, hF, hd⟩

end BridgeAxisFrame
