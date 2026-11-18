import PrincipalDiamondComponent
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.HeckeSlash.Operators
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.HeckeSlash.Diamond
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Prime.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Rational translate orbits and actual Hecke stability

The orbit is the complex span of positive rational matrix slashes of the
original function. Its members have genuine finite representations. Restricting
the orbit to actual cusp forms preserves the actual finite Hecke coset sums.
No invariance or representation of the desired eigencomponent is assumed.
-/

noncomputable section
set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open HeckeRing.GL2
open scoped MatrixGroups ModularForm Pointwise

namespace ZInQ.Contrib.HeckePrimeRationality.ReverseHecke

/-- A rational invertible matrix with positive determinant. -/
abbrev PositiveMatrix := {α : GL (Fin 2) ℚ // 0 < (α : Matrix (Fin 2) (Fin 2) ℚ).det}

/-- The actual complex-linear positive-rational translate orbit of a function. -/
def functionOrbit (k : ℤ) (f : ℍ → ℂ) : Submodule ℂ (ℍ → ℂ) :=
  Submodule.span ℂ (Set.range fun α : PositiveMatrix ↦
    f ∣[k] GeneralLinearGroup.map (algebraMap ℚ ℝ) α.val)

/-- Positive rational matrices compose with positive determinant. -/
theorem positive_matrix_mul {α β : GL (Fin 2) ℚ}
    (hα : 0 < (α : Matrix (Fin 2) (Fin 2) ℚ).det)
    (hβ : 0 < (β : Matrix (Fin 2) (Fin 2) ℚ).det) :
    0 < (α * β : Matrix (Fin 2) (Fin 2) ℚ).det := by
  rw [Matrix.det_mul]
  exact mul_pos hα hβ

/-- Every orbit member has an actual finite positive-rational translate representation. -/
theorem functionOrbit_representation (k : ℤ) (f : ℍ → ℂ) {g : ℍ → ℂ}
    (hg : g ∈ functionOrbit k f) :
    ∃ m : ℕ, ∃ c : Fin m → ℂ, ∃ α : Fin m → GL (Fin 2) ℚ,
      (∀ i, 0 < (α i : Matrix (Fin 2) (Fin 2) ℚ).det) ∧
        g = ∑ i, c i • (f ∣[k] GeneralLinearGroup.map (algebraMap ℚ ℝ) (α i)) := by
  classical
  obtain ⟨m, c, h, heq⟩ := Submodule.mem_span_set'.mp hg
  choose α hα using (fun i : Fin m ↦ (h i).property)
  refine ⟨m, c, fun i ↦ (α i).val, fun i ↦ (α i).property, ?_⟩
  rw [← heq]
  exact Finset.sum_congr rfl fun i _ ↦ congrArg (c i • ·) (hα i).symm

/-- A finite sum of positive-rational translates belongs to the actual orbit. -/
theorem sum_mem_functionOrbit {J : Type*} [Fintype J] (k : ℤ) (f : ℍ → ℂ)
    (c : J → ℂ) (α : J → GL (Fin 2) ℚ)
    (hα : ∀ i, 0 < (α i : Matrix (Fin 2) (Fin 2) ℚ).det) :
    (∑ i, c i • (f ∣[k] GeneralLinearGroup.map (algebraMap ℚ ℝ) (α i))) ∈
      functionOrbit k f :=
  Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
    (Submodule.subset_span ⟨⟨α i, hα i⟩, rfl⟩)

/-- Slashing an orbit member by a positive rational matrix keeps it in the same orbit. -/
theorem slash_mem_functionOrbit (k : ℤ) (f : ℍ → ℂ) {g : ℍ → ℂ}
    (hg : g ∈ functionOrbit k f) (β : GL (Fin 2) ℚ)
    (hβ : 0 < (β : Matrix (Fin 2) (Fin 2) ℚ).det) :
    g ∣[k] GeneralLinearGroup.map (algebraMap ℚ ℝ) β ∈ functionOrbit k f := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨α, rfl⟩ := hg
    rw [← SlashAction.slash_mul, ← map_mul]
    exact Submodule.subset_span ⟨⟨α.val * β, positive_matrix_mul α.property hβ⟩, rfl⟩
  | zero => simpa only [SlashAction.zero_slash] using (functionOrbit k f).zero_mem
  | add g h _ _ ihg ihh =>
    simpa only [SlashAction.add_slash] using (functionOrbit k f).add_mem ihg ihh
  | smul c g _ ih =>
    rw [_root_.ModularForm.smul_slash_of_det_pos k
      (_root_.ModularForm.det_map_ratCast_pos hβ)]
    exact (functionOrbit k f).smul_mem c ih

/-- The actual finite coset slash sum preserves the orbit when its matrices are positive. -/
theorem heckeSlashSum_mem_functionOrbit (k : ℤ) (f : ℍ → ℂ)
    {Δ : Submonoid (GL (Fin 2) ℚ)} {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℚ)}
    (D : HeckeCoset Δ Γ₁ Γ₂)
    [Finite (DoubleCoset.DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹)]
    (hpos : ∀ v : DoubleCoset.DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹,
      0 < (↑(DoubleCoset.rightCosetRep D v) : Matrix (Fin 2) (Fin 2) ℚ).det)
    {g : ℍ → ℂ} (hg : g ∈ functionOrbit k f) :
    heckeSlashSum k D g ∈ functionOrbit k f := by
  classical
  let : Fintype (DoubleCoset.DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹) :=
    Fintype.ofFinite _
  rw [heckeSlashSum_def]
  exact Submodule.sum_mem _ fun v _ ↦ by
    rw [_root_.ModularForm.rat_slash]
    exact slash_mem_functionOrbit k f hg _ (hpos v)

/-- The submodule of actual Gamma-one cusp forms whose functions lie in the orbit. -/
def cuspOrbit (L : ℕ) (k : ℤ) (f : ℍ → ℂ) :
    Submodule ℂ (CuspForm ((Gamma1 L).map (mapGL ℝ)) k) where
  carrier := {g | ⇑g ∈ functionOrbit k f}
  zero_mem' := by
    change ⇑(0 : CuspForm ((Gamma1 L).map (mapGL ℝ)) k) ∈ functionOrbit k f
    rw [FunLike.coe_zero]
    exact (functionOrbit k f).zero_mem
  add_mem' := by
    intro g h hg hh
    change ⇑(g + h) ∈ functionOrbit k f
    rw [FunLike.coe_add]
    exact (functionOrbit k f).add_mem hg hh
  smul_mem' := by
    intro c g hg
    change ⇑(c • g) ∈ functionOrbit k f
    rw [FunLike.coe_smul]
    exact (functionOrbit k f).smul_mem c hg

/-- Every actual positive-index Hecke operator preserves the actual cusp orbit. -/
theorem heckeTCuspNat_mem_cuspOrbit (L : ℕ) [NeZero L] (k : ℤ) (f : ℍ → ℂ)
    (n : ℕ) [NeZero n] {g : CuspForm ((Gamma1 L).map (mapGL ℝ)) k}
    (hg : g ∈ cuspOrbit L k f) : heckeTCuspNat k n g ∈ cuspOrbit L k f := by
  change ⇑(heckeTCuspNat k n g) ∈ functionOrbit k f
  rw [coe_heckeTCuspNat]
  have hD : ((diagCosetGamma1 L n).out : GL (Fin 2) ℚ) ∈ Matrix.GLPos (Fin 2) ℚ := by
    obtain ⟨A, hA, hdet, hN, hunit⟩ :=
      (mem_Delta0_iff L).mp (diagCosetGamma1 L n).out.property
    exact hdet
  exact heckeSlashSum_mem_functionOrbit k f (diagCosetGamma1 L n)
    (fun v ↦ det_rightCosetRep_pos (diagCosetGamma1 L n)
      (_root_.ModularForm.map_mapGL_le_glpos (Gamma1 L)) hD v) hg

/-- Good Hecke operators preserve actual character membership by the diamond commutation law. -/
theorem good_hecke_mem_character (L : ℕ) [NeZero L] (k : ℤ)
    (χ : (ZMod L)ˣ →* ℂˣ) (p : ℕ) (hp : p.Prime) (hpL : p.Coprime L)
    {g : CuspForm ((Gamma1 L).map (mapGL ℝ)) k} (hg : g ∈ cuspFormCharSpace k χ) :
    heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) g ∈ cuspFormCharSpace k χ := by
  let : NeZero p := ⟨hp.ne_zero⟩
  rw [mem_cuspFormCharSpace_iff] at hg ⊢
  intro d
  have hcomm := congrArg (fun T : Module.End ℂ (CuspForm ((Gamma1 L).map (mapGL ℝ)) k) ↦ T g)
    (commute_heckeTCuspNat_diamondOpCusp k hpL d).eq
  simp only [Module.End.mul_apply] at hcomm
  rw [diamondOpCuspHom_apply, ← hcomm, ← diamondOpCuspHom_apply, hg d, map_smul]

/-- The actual part of the cusp orbit in one actual nebentypus character space. -/
def characterOrbit (L : ℕ) (k : ℤ) (χ : (ZMod L)ˣ →* ℂˣ) (f : ℍ → ℂ) :
    Submodule ℂ (cuspFormCharSpace k χ) :=
  (cuspOrbit L k f).comap (cuspFormCharSpace k χ).subtype

/-- An actual principal cusp form has a nonzero element in one actual character orbit. -/
theorem exists_nonzero_characterOrbit (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (hf : f ≠ 0) :
    ∃ χ : (ZMod (N ^ 2))ˣ →* ℂˣ,
      ∃ g : cuspFormCharSpace k χ,
        g ≠ 0 ∧ g ∈ characterOrbit (N ^ 2) k χ ⇑f := by
  classical
  obtain ⟨χ, g, hg0, hgχ, c, α, hα, hrep⟩ :=
    PrincipalCuspTransport.exists_nonzero_nebentypus_rational_translates N k f hf
  refine ⟨χ, ⟨g, hgχ⟩, fun h ↦ hg0 (congrArg Subtype.val h), ?_⟩
  change ⇑g ∈ functionOrbit k ⇑f
  rw [hrep]
  exact sum_mem_functionOrbit k ⇑f c α hα

end ZInQ.Contrib.HeckePrimeRationality.ReverseHecke
