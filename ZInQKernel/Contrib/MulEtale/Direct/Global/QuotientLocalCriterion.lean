/-
Multiplication-etale construction: QuotientLocalCriterion.
The mathematical declarations below are part of the checked H-101 contribution.
-/
import ZInQKernel.Contrib.MulEtale.Direct.Global.LocalPushoutCriterion
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Ideal.Over

noncomputable section
open scoped TensorProduct
namespace H101DirectGlobalDetection.QuotientLocal

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
  [IsLocalRing R] [IsLocalRing T] [IsLocalHom (algebraMap R T)]

abbrev sourceIdeal : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
abbrev targetIdeal : Ideal T := (IsLocalRing.maximalIdeal R).map (algebraMap R T)

theorem sourceIdeal_le_comap_targetIdeal :
    sourceIdeal R S ≤ (targetIdeal R T).comap (algebraMap S T) := by
  apply Ideal.map_le_iff_le_comap.mp
  rw [sourceIdeal, targetIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq R S T]

/-- The unchanged actual quotient map induced by the original algebra map. -/
def quotientMap : (S ⧸ sourceIdeal R S) →+* (T ⧸ targetIdeal R T) :=
  Ideal.quotientMap (targetIdeal R T) (algebraMap S T)
    (sourceIdeal_le_comap_targetIdeal R S T)

include R in
/-- Actual quotient formal etaleness and the two smooth structural algebras
imply formal etaleness of the investigated map. The literal base quotient
and every coefficient map/tower are constructed inside this proof. -/
theorem formallyEtale_of_quotientMap
    [Algebra.EssFiniteType R S] [Algebra.EssFiniteType R T]
    [Algebra.FormallySmooth R S] [Algebra.FormallySmooth R T]
    (H : (quotientMap R S T).FormallyEtale) : Algebra.FormallyEtale S T := by
  let I := IsLocalRing.maximalIdeal R
  let J := sourceIdeal R S
  let L := targetIdeal R T
  let S' := S ⧸ J
  let T' := T ⧸ L
  let R' := R ⧸ I
  letI : CommRing R' := Ideal.Quotient.commRing I
  let K := IsLocalRing.ResidueField T
  have hJL : J ≤ L.comap (algebraMap S T) := sourceIdeal_le_comap_targetIdeal R S T
  have hLm : L ≤ IsLocalRing.maximalIdeal T :=
    IsLocalRing.map_maximalIdeal_le (algebraMap R T)
  have hIm : I ≤ (IsLocalRing.maximalIdeal T).comap (algebraMap R T) :=
    Ideal.map_le_iff_le_comap.mp hLm
  have hJm : J ≤ (IsLocalRing.maximalIdeal T).comap (algebraMap S T) := by
    apply Ideal.map_le_iff_le_comap.mp
    rw [show J.map (algebraMap S T) = L by
      dsimp only [J, L, sourceIdeal, targetIdeal]
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R S T]]
    exact hLm
  let q : S' →+* T' := quotientMap R S T
  have killT : ∀ t : T, t ∈ L → algebraMap T K t = 0 := by
    intro t ht
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr (hLm ht)
  have killS : ∀ s : S, s ∈ J →
      ((algebraMap T K).comp (algebraMap S T)) s = 0 := by
    intro s hs
    have hm : algebraMap S T s ∈ IsLocalRing.maximalIdeal T :=
      (Ideal.mem_comap).mp (hJm hs)
    change algebraMap T K (algebraMap S T s) = 0
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hm
  have killR : ∀ r : R, r ∈ I →
      ((algebraMap T K).comp (algebraMap R T)) r = 0 := by
    intro r hr
    have hm : algebraMap R T r ∈ IsLocalRing.maximalIdeal T :=
      (Ideal.mem_comap).mp (hIm hr)
    change algebraMap T K (algebraMap R T r) = 0
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hm
  let cT : T' →+* K := Ideal.Quotient.lift L (algebraMap T K) killT
  let cS : S' →+* K := Ideal.Quotient.lift J
    ((algebraMap T K).comp (algebraMap S T)) killS
  let cR : R' →+* K := Ideal.Quotient.lift I
    ((algebraMap T K).comp (algebraMap R T)) killR
  have hq (s : S) : q (Ideal.Quotient.mk J s) =
      Ideal.Quotient.mk L (algebraMap S T s) := by
    dsimp only [q, quotientMap]
    exact Ideal.quotientMap_mk
  have hcT (t : T) : cT (Ideal.Quotient.mk L t) = algebraMap T K t := by
    exact Ideal.Quotient.lift_mk L (algebraMap T K) killT
  have hcS (s : S) : cS (Ideal.Quotient.mk J s) =
      algebraMap T K (algebraMap S T s) := by
    exact Ideal.Quotient.lift_mk J ((algebraMap T K).comp (algebraMap S T)) killS
  have hcR (r : R) : cR (Ideal.Quotient.mk I r) =
      algebraMap T K (algebraMap R T r) := by
    exact Ideal.Quotient.lift_mk I ((algebraMap T K).comp (algebraMap R T)) killR
  letI : Algebra S' T' := q.toAlgebra
  letI : Algebra T' K := cT.toAlgebra
  letI : Algebra S' K := cS.toAlgebra
  letI : Algebra R' K := cR.toAlgebra
  letI : Algebra R' S' :=
    (Ideal.Quotient.algebraQuotientMapQuotient :
      Algebra (R ⧸ I) (S ⧸ I.map (algebraMap R S)))
  letI : Algebra R' T' :=
    (Ideal.Quotient.algebraQuotientMapQuotient :
      Algebra (R ⧸ I) (T ⧸ I.map (algebraMap R T)))
  letI : IsScalarTower R R' S' := Ideal.Quotient.tower_quotient_map_quotient
  letI : IsScalarTower R R' T' := Ideal.Quotient.tower_quotient_map_quotient
  letI : IsScalarTower S S' T' := IsScalarTower.of_algebraMap_eq fun s => by
    change Ideal.Quotient.mk L (algebraMap S T s) = q (Ideal.Quotient.mk J s)
    exact (hq s).symm
  letI : IsScalarTower R' S' T' := IsScalarTower.of_algebraMap_eq fun r => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    change Ideal.Quotient.mk L (algebraMap R T a) =
      q (Ideal.Quotient.mk J (algebraMap R S a))
    rw [hq]
    exact congrArg (Ideal.Quotient.mk L) (IsScalarTower.algebraMap_apply R S T a)
  letI : IsScalarTower T T' K := IsScalarTower.of_algebraMap_eq fun t => by
    change algebraMap T K t = cT (Ideal.Quotient.mk L t)
    exact (hcT t).symm
  letI : IsScalarTower S S' K := IsScalarTower.of_algebraMap_eq fun s => by
    change algebraMap S K s = cS (Ideal.Quotient.mk J s)
    rw [hcS]
    exact IsScalarTower.algebraMap_apply S T K s
  letI : IsScalarTower S' T' K := IsScalarTower.of_algebraMap_eq fun s => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective s
    change cS (Ideal.Quotient.mk J a) = cT (q (Ideal.Quotient.mk J a))
    rw [hq, hcS, hcT]
  letI : IsScalarTower R' T' K := IsScalarTower.of_algebraMap_eq fun r => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    change cR (Ideal.Quotient.mk I a) = cT (Ideal.Quotient.mk L (algebraMap R T a))
    rw [hcR, hcT]
  letI : IsScalarTower R' S' K := IsScalarTower.of_algebraMap_eq fun r => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    change cR (Ideal.Quotient.mk I a) = cS (Ideal.Quotient.mk J (algebraMap R S a))
    rw [hcR, hcS]
    exact congrArg (algebraMap T K) (IsScalarTower.algebraMap_apply R S T a)
  letI : Algebra.IsPushout R R' S S' :=
    SourceReuse.isPushout_quotient (A := R) (B := S) I
  letI : Algebra.IsPushout R R' T T' :=
    SourceReuse.isPushout_quotient (A := R) (B := T) I
  letI : Algebra.FormallyEtale S' T' := by
    change Algebra.FormallyEtale S' T' at H
    exact H
  exact H101DirectGlobalDetection.formallyEtale_of_formallyEtale_baseChange R S T R' S' T'

end H101DirectGlobalDetection.QuotientLocal
