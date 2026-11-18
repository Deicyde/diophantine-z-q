import DirectTorsionOrbitV001
import Mathlib.NumberTheory.ModularForms.NormTrace

/-!
# Actual coset translations and their finite permutation law

All translated entries retain genuine holomorphy and boundedness fields.
Integral slashing permutes the complete inverse coset orbit, with the
permutation derived from the quotient action rather than supplied as data.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm Pointwise BigOperators

namespace DirectOrbitAlgebra

open DirectTorsionOrbit
open ZInQ.Contrib.HeckePrimeRationality

/-- Normality of the actual principal subgroup supplies the required translated-level inclusion. -/
theorem principal_le_inv_conjugate (N : ℕ) (H : Subgroup SL(2, ℤ))
    (hH : Gamma N ≤ H) (γ : SL(2, ℤ)) :
    (Gamma N).map (mapGL ℝ) ≤
      ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • H.map (mapGL ℝ) := by
  rintro _ ⟨δ, hδ, rfl⟩
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, ConjAct.toConjAct_smul]
  have hconj : γ * δ * γ⁻¹ ∈ Gamma N := (Gamma_normal N).conj_mem δ hδ γ
  exact Subgroup.mem_map.mpr ⟨γ * δ * γ⁻¹, hH hconj, by simp only [map_mul, map_inv]⟩

/-- The actual principal group is contained in the actual Gamma-one group. -/
theorem principal_le_gamma_one (N : ℕ) : Gamma N ≤ Gamma1 N := by
  intro γ hγ
  rcases Gamma_mem.mp hγ with ⟨h00, _, h10, h11⟩
  exact (Gamma1_mem N γ).mpr ⟨h00, h11, h10⟩

/-- Integral slashing, bundled on the unchanged principal modular-form space. -/
def principalSlash (N : ℕ) (k : ℤ) (γ : SL(2, ℤ))
    (f : ModularForm ((Gamma N).map (mapGL ℝ)) k) :
    ModularForm ((Gamma N).map (mapGL ℝ)) k :=
  ModularForm.restrict (principal_le_inv_conjugate N (Gamma N) le_rfl γ)
    (ModularForm.translate f (mapGL ℝ γ))

/-- The bundled slash is exactly the original analytic slash action. -/
theorem principalSlash_coe (N : ℕ) (k : ℤ) (γ : SL(2, ℤ))
    (f : ModularForm ((Gamma N).map (mapGL ℝ)) k) :
    ⇑(principalSlash N k γ f) = ⇑f ∣[k] γ := by
  simp only [principalSlash, ModularForm.coe_restrict, ModularForm.coe_translate,
    ModularForm.SL_slash]
  rfl

/-- Each inverse coset translate of an arbitrary Gamma-one form is an actual principal form. -/
def formOrbit (N : ℕ) [NeZero N] (k : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (i : Fin (orbitLength N)) :
    ModularForm ((Gamma N).map (mapGL ℝ)) k :=
  ModularForm.restrict
    (principal_le_inv_conjugate N (Gamma1 N) (principal_le_gamma_one N) (representative N i)⁻¹)
    (ModularForm.translate f (mapGL ℝ (representative N i)⁻¹))

/-- Its underlying function is the actual inverse representative translate. -/
theorem formOrbit_coe (N : ℕ) [NeZero N] (k : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (i : Fin (orbitLength N)) :
    ⇑(formOrbit N k f i) = ⇑f ∣[k] (representative N i)⁻¹ := by
  simp only [formOrbit, ModularForm.coe_restrict, ModularForm.coe_translate,
    ModularForm.SL_slash]
  rfl

local instance : MulAction SL(2, ℤ) SL(2, ℤ) := Monoid.toMulAction ..
local instance (N : ℕ) : MulAction SL(2, ℤ) (SL(2, ℤ) ⧸ Gamma1 N) :=
  MulAction.quotient SL(2, ℤ) (Gamma1 N)

/-- The actual quotient action, transported to the proved finite enumeration. -/
def cosetPermutation (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) : Equiv.Perm (Fin (orbitLength N)) :=
  (orbitEquiv N).symm.trans ((MulAction.toPerm γ⁻¹).trans (orbitEquiv N))

/-- Its action on actual cosets is precisely left multiplication by the inverse matrix. -/
theorem cosetPermutation_coset (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) (i : Fin (orbitLength N)) :
    (orbitEquiv N).symm (cosetPermutation N γ i) = γ⁻¹ • (orbitEquiv N).symm i := by
  simp [cosetPermutation]

/-- The representative relation needed by the original Gamma-one slash invariance. -/
theorem cosetPermutation_relation (N : ℕ) [NeZero N] (γ : SL(2, ℤ))
    (i : Fin (orbitLength N)) :
    (representative N i)⁻¹ * γ * representative N (cosetPermutation N γ i) ∈ Gamma1 N := by
  have hq : (QuotientGroup.mk (γ⁻¹ * representative N i) : SL(2, ℤ) ⧸ Gamma1 N) =
      QuotientGroup.mk (representative N (cosetPermutation N γ i)) := by
    change γ⁻¹ • (QuotientGroup.mk (representative N i) : SL(2, ℤ) ⧸ Gamma1 N) =
      QuotientGroup.mk (representative N (cosetPermutation N γ i))
    simpa only [representative, Quotient.out_eq] using
      (cosetPermutation_coset N γ i).symm
  have hrel := Quotient.exact hq
  simpa only [QuotientGroup.leftRel_apply, mul_inv_rev, inv_inv, mul_assoc] using hrel

/-- Slashing permutes the actual complete coset orbit at every integer weight. -/
theorem formOrbit_slash (N : ℕ) [NeZero N] (k : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (γ : SL(2, ℤ))
    (i : Fin (orbitLength N)) :
    ⇑(formOrbit N k f i) ∣[k] γ = ⇑(formOrbit N k f (cosetPermutation N γ i)) := by
  rw [formOrbit_coe, formOrbit_coe, ← SlashAction.slash_mul]
  have he : (representative N i)⁻¹ * γ =
      ((representative N i)⁻¹ * γ * representative N (cosetPermutation N γ i)) *
        (representative N (cosetPermutation N γ i))⁻¹ := by group
  rw [he, SlashAction.slash_mul]
  have hmem : mapGL ℝ ((representative N i)⁻¹ * γ *
      representative N (cosetPermutation N γ i)) ∈ (Gamma1 N).map (mapGL ℝ) :=
    Subgroup.mem_map.mpr ⟨_, cosetPermutation_relation N γ i, rfl⟩
  have hs : ⇑f ∣[k] ((representative N i)⁻¹ * γ *
      representative N (cosetPermutation N γ i)) = ⇑f :=
    SlashInvariantFormClass.SL_slash_eq f _ (cosetPermutation_relation N γ i)
  rw [hs]

/-- The previously constructed torsion orbit is exactly this actual coset orbit. -/
theorem torsionOrbit_slash (N : ℕ) [NeZero N] (hN : 3 ≤ N) (γ : SL(2, ℤ))
    (i : Fin (orbitLength N)) :
    ⇑(torsionOrbit N hN i) ∣[(1 : ℤ)] γ =
      ⇑(torsionOrbit N hN (cosetPermutation N γ i)) := by
  have hdiv : ¬ (N : ℤ) ∣ 1 := fun h => base_good N hN ⟨dvd_zero _, h⟩
  let f := AllLevelForms.torsionForm N (NeZero.pos N) 1 hdiv
  have he (j : Fin (orbitLength N)) : formOrbit N 1 f j = torsionOrbit N hN j := by
    apply ModularForm.ext
    intro τ
    rw [formOrbit_coe, torsionOrbit_coe]
    rfl
  simpa only [he] using formOrbit_slash N 1 f γ i

end DirectOrbitAlgebra
