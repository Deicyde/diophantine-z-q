import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.DivisionEisensteinPrimeFiberMoves
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Actual trace invariance along principal-congruence series orbits

Normality inside the mapped principal groups makes right multiplication a
permutation of the trace quotient. It therefore leaves the actual normalized
trace of an independently series-defined generator unchanged.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open UpperHalfPlane Matrix CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators Matrix MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.DivisionEisensteinLowerClosure

open EisensteinWeightTwo DivisionEisensteinLevelMaps

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

/-- Principal congruence normality holds inside any mapped principal group. -/
theorem mapped_principal_subgroup_normal (N M : ℕ) : ((ΓP M).subgroupOf (ΓP N)).Normal := by
  constructor
  intro δ hδ γ
  change (γ.val * δ.val * γ.val⁻¹) ∈ (ΓP M)
  obtain ⟨d, hd, he⟩ := Subgroup.mem_map.mp hδ
  change mapGL ℝ d = δ.val at he
  obtain ⟨g, hg, hge⟩ := Subgroup.mem_map.mp γ.property
  rw [← he, ← hge, ← map_mul, ← map_inv, ← map_mul]
  exact Subgroup.mem_map.mpr ⟨g * d * g⁻¹, (Gamma_normal M).conj_mem d hd g, rfl⟩

/-- Right quotient reindexing identifies actual trace summands of a translated generator. -/
theorem quotientFunc_generator_right_shift (N M : ℕ) (hM : 0 < M) (a : Fin 2 → ℤ)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma N)
    (q : (ΓP N) ⧸ (ΓP M).subgroupOf (ΓP N)) :
    let g : (ΓP N) := ⟨mapGL ℝ γ, Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩⟩
    let _ := mapped_principal_subgroup_normal N M
    SlashInvariantForm.quotientFunc (divisionEisensteinMF M hM (a ᵥ* γ.1)) q =
      SlashInvariantForm.quotientFunc (divisionEisensteinMF M hM a) (MulOpposite.op g⁻¹ • q) := by
  let g : (ΓP N) := ⟨mapGL ℝ γ, Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩⟩
  let _ := mapped_principal_subgroup_normal N M
  change SlashInvariantForm.quotientFunc (divisionEisensteinMF M hM (a ᵥ* γ.1)) q =
    SlashInvariantForm.quotientFunc (divisionEisensteinMF M hM a) (MulOpposite.op g⁻¹ • q)
  have hseries : ⇑(divisionEisensteinMF M hM (a ᵥ* γ.1)) =
      (⇑(divisionEisensteinMF M hM a) : ℍ → ℂ) ∣[(2 : ℤ)] (mapGL ℝ γ) :=
    (divisionEisenstein_slash M hM a γ).symm
  induction q using QuotientGroup.induction_on' with
  | H r =>
    rw [MulAction.Quotient.smul_coe, SlashInvariantForm.quotientFunc_mk,
      SlashInvariantForm.quotientFunc_mk, hseries, ← SlashAction.slash_mul]
    simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Subgroup.coe_mul,
      Subgroup.coe_inv, _root_.mul_inv_rev, inv_inv, g]

/-- The actual normalized trace is constant on an actual Γ(N) series-label orbit. -/
theorem normalizedTrace_generator_SL (N M : ℕ) (hM : 0 < M)
    (a : Fin 2 → ℤ) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma N) :
    normalizedTrace N M hM (divisionEisensteinMF M hM (a ᵥ* γ.1)) =
      normalizedTrace N M hM (divisionEisensteinMF M hM a) := by
  classical
  let : NeZero M := ⟨hM.ne'⟩
  let _ := mapped_principal_subgroup_normal N M
  let Q := (ΓP N) ⧸ (ΓP M).subgroupOf (ΓP N)
  let : Fintype Q := Fintype.ofFinite Q
  let g : (ΓP N) := ⟨mapGL ℝ γ, Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩⟩
  rw [normalizedTrace_apply, normalizedTrace_apply]
  apply congrArg (fun f : _root_.ModularForm (ΓP N) 2 => (traceIndex N M : ℂ)⁻¹ • f)
  apply DFunLike.coe_injective
  rw [_root_.ModularForm.coe_trace, _root_.ModularForm.coe_trace]
  have he : ∀ q : Q,
      SlashInvariantForm.quotientFunc (divisionEisensteinMF M hM (a ᵥ* γ.1)) q =
        SlashInvariantForm.quotientFunc (divisionEisensteinMF M hM a)
          (MulOpposite.op g⁻¹ • q) := fun q => quotientFunc_generator_right_shift N M hM a γ hγ q
  simp_rw [he]
  exact Equiv.sum_comp (MulAction.toPerm (MulOpposite.op g⁻¹))
    (SlashInvariantForm.quotientFunc (divisionEisensteinMF M hM a))

/-- Congruent integer labels define the same actual independently defined series form. -/
theorem divisionMF_eq_of_congr (M : ℕ) (hM : 0 < M) (a b c d : ℤ)
    (ha : (a : ZMod M) = c) (hb : (b : ZMod M) = d) :
    divisionEisensteinMF M hM ![a,b] = divisionEisensteinMF M hM ![c,d] := by
  have hd0 : (M : ℤ) ∣ a - c := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp
    simp only [Int.cast_sub, ha, sub_self]
  have hd1 : (M : ℤ) ∣ b - d := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp
    simp only [Int.cast_sub, hb, sub_self]
  obtain ⟨r, hr⟩ := hd0
  obtain ⟨s, hs⟩ := hd1
  have ha0 : a = c + M * r := by linarith
  have hb0 : b = d + M * s := by linarith
  apply _root_.ModularForm.ext
  intro τ
  change divisionEisenstein M a b τ = divisionEisenstein M c d τ
  rw [ha0, hb0, divisionEisenstein_add_level M hM c d r s τ]

end ZInQ.Contrib.HeckePrimeRationality.DivisionEisensteinLowerClosure
