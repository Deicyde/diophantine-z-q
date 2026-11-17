/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

Properties of the ACTUAL stage-leg factor β, not assumptions about raw
étale stages or a fictitious ind-étale B_s → P map. The local property is
proved from the actual maximal-ideal contraction and factor equation;
injectivity is proved from the ORIGINAL O-uniformizer whose image is a
uniformizer of the actual local stage, and its nonzero image in P.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.LocalModel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open IsLocalRing

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective

/-- The actual factor through a prime localization is local: no locality
    of the raw stage B or ind-étaleness of B_s → P is assumed. -/
theorem away_factor_isLocalHom
    {O B P : Type u} [CommRing O] [CommRing B] [CommRing P] [IsLocalRing P]
    [Algebra O B] [Algebra O P] (ι : B →ₐ[O] P) (s : B)
    [IsLocalization.AtPrime (Localization.Away s) ((maximalIdeal P).comap ι.toRingHom)]
    (β : Localization.Away s →ₐ[O] P)
    (hβ : β.comp (IsScalarTower.toAlgHom O B (Localization.Away s)) = ι) :
    IsLocalHom β.toRingHom := by
  let C := Localization.Away s
  let q : Ideal B := (maximalIdeal P).comap ι.toRingHom
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  have hβι (b : B) : β (algebraMap B C b) = ι b :=
    congrArg (fun f : B →ₐ[O] P => f b) hβ
  refine IsLocalHom.mk ?_
  intro x hx
  obtain ⟨⟨a, t⟩, ht⟩ := IsLocalization.surj (Submonoid.powers s) x
  have hut : IsUnit (β (algebraMap B C t)) :=
    (IsLocalization.map_units C t).map β.toRingHom
  have haP : IsUnit (ι a) := by
    have he : β x * β (algebraMap B C t) = ι a := by
      rw [← map_mul, ht, hβι]
    exact he ▸ hx.mul hut
  have haq : a ∈ q.primeCompl := notMem_maximalIdeal.mpr haP
  have haC : IsUnit (algebraMap B C a) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff C q a).mpr haq
  have hprod : IsUnit (x * algebraMap B C t) := ht.symm ▸ haC
  exact isUnit_of_mul_isUnit_left hprod

/-- Injectivity of the actual O-algebra factor is DERIVED from the original
    uniformizer. The raw stage leg need not be injective; the only base
    injectivity is O → P, provided by the same-closure ordinary factory. -/
theorem factor_injective_of_original_uniformizer
    {O C P : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra O C]
    [CommRing P] [IsDomain P] [Algebra O P]
    (hOP : Function.Injective (algebraMap O P)) (β : C →ₐ[O] P)
    (π : O) (hπ : Irreducible π) (hπC : Irreducible (algebraMap O C π)) :
    Function.Injective β := by
  have hπP : algebraMap O P π ≠ 0 := by
    intro h
    exact hπ.ne_zero (hOP (h.trans (map_zero _).symm))
  have hzero (x : C) (hx : β x = 0) : x = 0 := by
    by_contra hx0
    obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hπC
    have hu : β (w : C) ≠ 0 := (w.isUnit.map β.toRingHom).ne_zero
    have hne : β x ≠ 0 := by
      rw [hw, map_mul, map_pow, β.commutes π]
      exact mul_ne_zero hu (pow_ne_zero n hπP)
    exact hne hx
  intro x y hxy
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, hxy, sub_self]

#print axioms away_factor_isLocalHom
#print axioms factor_injective_of_original_uniformizer

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
