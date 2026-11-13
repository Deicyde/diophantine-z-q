/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.Ideles), Apache-2.0: a declaration added to that module after commit 5a01f5fe
-- and not already in `ZInQKernel.Contrib.TauCeti.Backport.NumberTheory.ClassFieldTheory.Global.Kummer.Ideles`
-- (task ring-class).
module

public import ZInQKernel.Contrib.TauCeti.Backport.NumberTheory.ClassFieldTheory.Global.Kummer.Ideles
public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.Subgroup

public noncomputable section

open IsDedekindDomain NumberField

namespace TauCeti.ClassFieldTheory

variable {K : Type*} [Field K] [NumberField K]

open GlobalNumberFields in
/-- **A subgroup containing the `n`-th powers and a ray subgroup contains a Kummer idele-class
subgroup.** Let `N ≤ C_K` contain the `n`-th powers and the ray subgroup of a modulus `𝔪` whose
finite part is supported in `S`. Then `N` contains the image in `C_K` of the Kummer idele subgroup
`E_S` of ideles that are `n`-th powers at `S` and at every infinite place and units elsewhere. -/
theorem auxiliaryKummerIdeleClassSubgroup_le_of_raySubgroup_le {n : ℕ}
    {N : Subgroup (IdeleClassGroup (𝓞 K) K)} (hpow : ∀ c, c ^ n ∈ N) {𝔪 : Modulus K}
    (h𝔪 : raySubgroup 𝔪 ≤ N) {S : Finset (HeightOneSpectrum (𝓞 K))}
    (hS : 𝔪.support ⊆ S) :
    auxiliaryKummerIdeleClassSubgroup S ∅ n ≤ N := by
  classical
  intro c hc
  obtain ⟨x, hx, rfl⟩ := (mem_auxiliaryKummerIdeleClassSubgroup_iff S ∅ n c).1 hc
  obtain ⟨hxS, hxinf, hxunit⟩ := (mem_auxiliaryKummerIdeleSubgroup_iff S ∅ n x).1 hx
  -- Write `x = z * yⁿ`, where `y` is supported on `S` and the infinite places and `z` is `1` there
  -- and a unit elsewhere, hence congruent to one modulo `𝔪`. First choose the `n`-th roots of the
  -- coordinates of `x` at `S` and at the infinite places.
  choose yS hyS using hxS
  choose yinf hyinf using hxinf
  let y : IdeleGroup (𝓞 K) K := ideleOfUnits yinf (fun v ↦ if hv : v ∈ S then yS v hv else 1)
    (Filter.eventually_cofinite.2 <| S.finite_toSet.subset fun v (hv : ¬ _) ↦
      by_contra fun (hvS : v ∉ S) ↦ hv (by simp only [hvS, dite_false]; exact one_mem _))
  -- The quotient `z = x / yⁿ` is `1` at `S` and at infinity, and agrees with `x` elsewhere.
  set z := x * (y ^ n)⁻¹ with hz
  have hzS (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) : v.ideleFiniteCoord z = 1 := by
    simp [hz, y, hv, ← hyS v hv]
  have hzS' (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
      v.ideleFiniteCoord z = v.ideleFiniteCoord x := by
    simp [hz, y, hv]
  have hzinf (w : InfinitePlace K) : w.ideleInfiniteCoord z = 1 := by
    simp [hz, y, ← hyinf w]
  have hzmem : z ∈ ideleCongruenceSubgroup 𝔪 := by
    refine mem_ideleCongruenceSubgroup_iff.2 ⟨fun v _ ↦ ?_, fun v hv ↦ ?_, fun w _ ↦ ?_⟩
    · by_cases hv : v ∈ S
      · simp [hzS v hv]
      · rw [hzS' v hv]
        exact hxunit v hv (Finset.notMem_empty v)
    · simp [hzS v (hS ((Modulus.mem_support_iff 𝔪 v).2 hv))]
    · simp [hzinf]
  -- Hence the class of `x = z * yⁿ` lies in `N`.
  have hxz : x = z * y ^ n := by rw [hz, inv_mul_cancel_right]
  rw [hxz, QuotientGroup.mk_mul, QuotientGroup.mk_pow]
  exact N.mul_mem (h𝔪 (mem_raySubgroup_iff.2 ⟨z, hzmem, rfl⟩)) (hpow _)

end TauCeti.ClassFieldTheory
