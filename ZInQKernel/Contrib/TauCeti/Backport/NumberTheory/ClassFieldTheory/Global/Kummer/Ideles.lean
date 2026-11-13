/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.Ideles), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.Ideles`.
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.Ideles
-- `auxiliaryKummerIdeleClassSubgroup_def` unfolds a definition whose body the oct16 module does not expose.
import all ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.Ideles
public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Ideles.FiniteIdeal
public import ZInQKernel.Contrib.TauCeti.Backport.NumberTheory.NumberField.Global.Ideles.FiniteIdeal
public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.Subgroup
public import Mathlib.GroupTheory.Index
import ZInQKernel.Contrib.TauCeti.GroupTheory.Index.Map

public noncomputable section

open IsDedekindDomain NumberField
namespace TauCeti.ClassFieldTheory

variable {K : Type*} [Field K] [NumberField K]

/-- At exponent one, membership in the auxiliary Kummer subgroup is the unit condition outside
the union `S ∪ T`. -/
theorem mem_auxiliaryKummerIdeleSubgroup_one_iff_union
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (x : IdeleGroup (𝓞 K) K) :
    x ∈ auxiliaryKummerIdeleSubgroup S T 1 ↔
      ∀ v ∉ ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T),
        Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) = 1 := by
  rw [mem_auxiliaryKummerIdeleSubgroup_one_iff]
  constructor
  · exact fun h v hv ↦ h v (fun hvS ↦ hv (Or.inl hvS)) fun hvT ↦ hv (Or.inr hvT)
  · exact fun h v hvS hvT ↦ h v fun hv ↦ hv.elim hvS hvT

end TauCeti.ClassFieldTheory

open IsDedekindDomain NumberField
namespace TauCeti.ClassFieldTheory

variable {K : Type*} [Field K] [NumberField K]

/-- The principal idele of `a` lies in the exponent-one auxiliary Kummer subgroup exactly when
`a` is an `(S ∪ T)`-unit. -/
theorem unitEmbedding_mem_auxiliaryKummerIdeleSubgroup_one_iff
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (a : Kˣ) :
    IdeleGroup.unitEmbedding (𝓞 K) K a ∈ auxiliaryKummerIdeleSubgroup S T 1 ↔
      a ∈ ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T).unit K := by
  rw [mem_auxiliaryKummerIdeleSubgroup_one_iff_union,
    IdeleGroup.forall_valued_ideleFiniteCoord_unitEmbedding_eq_one_iff]

end TauCeti.ClassFieldTheory

open IsDedekindDomain NumberField
namespace TauCeti.ClassFieldTheory

variable {K : Type*} [Field K] [NumberField K]

/-- The principal ideles lying in the `(S ∪ T)`-ideles are precisely the principal
`(S ∪ T)`-units. -/
@[simp]
theorem comap_unitEmbedding_auxiliaryKummerIdeleSubgroup_one
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    (auxiliaryKummerIdeleSubgroup S T 1).comap (IdeleGroup.unitEmbedding (𝓞 K) K) =
      ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T).unit K :=
  Subgroup.ext (unitEmbedding_mem_auxiliaryKummerIdeleSubgroup_one_iff S T)

end TauCeti.ClassFieldTheory

open IsDedekindDomain NumberField
namespace TauCeti.ClassFieldTheory

variable {K : Type*} [Field K] [NumberField K]

/-- The auxiliary Kummer idele class subgroup is the image under the quotient by
principal ideles. -/
theorem auxiliaryKummerIdeleClassSubgroup_def
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    auxiliaryKummerIdeleClassSubgroup S T n =
      (auxiliaryKummerIdeleSubgroup S T n).map
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)) :=
  (rfl)

end TauCeti.ClassFieldTheory

open IsDedekindDomain NumberField
namespace TauCeti.ClassFieldTheory

variable {K : Type*} [Field K] [NumberField K]

/-- If the classes of the primes in `S ∪ T` generate the ideal class group, every idele
class has an `(S ∪ T)`-idele representative. -/
@[simp]
theorem auxiliaryKummerIdeleClassSubgroup_one_eq_top
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hST : Subgroup.closure (HeightOneSpectrum.classGroupMk (R := 𝓞 K) ''
      ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ (T : Set (HeightOneSpectrum (𝓞 K))))) = ⊤) :
    auxiliaryKummerIdeleClassSubgroup S T 1 = ⊤ := by
  apply top_unique
  intro c _
  obtain ⟨x, hx, hc⟩ :=
    IdeleClassGroup.exists_valued_ideleFiniteCoord_eq_one_and_mk_eq hST c
  exact (mem_auxiliaryKummerIdeleClassSubgroup_iff S T 1 c).2
    ⟨x, (mem_auxiliaryKummerIdeleSubgroup_one_iff_union S T x).2 hx, hc⟩

end TauCeti.ClassFieldTheory

open IsDedekindDomain NumberField
namespace TauCeti.ClassFieldTheory

variable {K : Type*} [Field K] [NumberField K]

/-- If the classes of `S ∪ T` generate the ideal class group, the quotient map restricted
to the auxiliary Kummer subgroup of exponent one is surjective. -/
theorem auxiliaryKummerIdeleSubgroup_one_mk_surjective
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hST : Subgroup.closure (HeightOneSpectrum.classGroupMk (R := 𝓞 K) ''
      ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ (T : Set (HeightOneSpectrum (𝓞 K))))) = ⊤) :
    Function.Surjective
      ((QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)).comp
        (auxiliaryKummerIdeleSubgroup S T 1).subtype) := by
  rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
  exact (auxiliaryKummerIdeleClassSubgroup_def S T 1).symm.trans
    (auxiliaryKummerIdeleClassSubgroup_one_eq_top S T hST)

end TauCeti.ClassFieldTheory

open IsDedekindDomain NumberField
namespace TauCeti.ClassFieldTheory

variable {K : Type*} [Field K] [NumberField K]

/-- Restricting the auxiliary Kummer subgroup to the exponent-one subgroup before taking
its image in the idele class group gives the same auxiliary Kummer idele-class subgroup. -/
private theorem map_subgroupOf_auxiliaryKummerIdeleSubgroup
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    ((auxiliaryKummerIdeleSubgroup S T n).subgroupOf
      (auxiliaryKummerIdeleSubgroup S T 1)).map
        ((QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)).comp
          (auxiliaryKummerIdeleSubgroup S T 1).subtype) =
      auxiliaryKummerIdeleClassSubgroup S T n := by
  rw [auxiliaryKummerIdeleClassSubgroup_def, ← Subgroup.map_map,
    Subgroup.subgroupOf_map_subtype]
  exact congrArg (Subgroup.map _)
    (inf_eq_left.mpr (auxiliaryKummerIdeleSubgroup_le_one S T n))

end TauCeti.ClassFieldTheory

open IsDedekindDomain NumberField
namespace TauCeti.ClassFieldTheory

variable {K : Type*} [Field K] [NumberField K]

/-- **The index of the auxiliary Kummer idele classes.** If the classes of `S ∪ T` generate the
ideal class group, then
`[C_K : E_{S,T} Kˣ / Kˣ] · [U_{S∪T} : U_{S∪T} ∩ E_{S,T}] = [I_{S∪T} : E_{S,T}]`,
where `I_{S∪T}` is the group of `(S ∪ T)`-ideles, `U_{S∪T}` is the group of `(S ∪ T)`-units, and
an `(S ∪ T)`-unit lies in `E_{S,T}` when its principal idele does. -/
theorem index_auxiliaryKummerIdeleClassSubgroup_mul_relIndex
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ)
    (hST : Subgroup.closure (HeightOneSpectrum.classGroupMk (R := 𝓞 K) ''
      ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ (T : Set (HeightOneSpectrum (𝓞 K))))) = ⊤) :
    (auxiliaryKummerIdeleClassSubgroup S T n).index *
        ((auxiliaryKummerIdeleSubgroup S T n).comap (IdeleGroup.unitEmbedding (𝓞 K) K)).relIndex
          (((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T).unit K) =
      (auxiliaryKummerIdeleSubgroup S T n).relIndex (auxiliaryKummerIdeleSubgroup S T 1) := by
  let J := auxiliaryKummerIdeleSubgroup S T 1
  let E := (auxiliaryKummerIdeleSubgroup S T n).subgroupOf J
  let q := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)
  let f : J →* IdeleClassGroup (𝓞 K) K := q.comp J.subtype
  have hf : Function.Surjective f := auxiliaryKummerIdeleSubgroup_one_mk_surjective S T hST
  have hmap : E.map f = auxiliaryKummerIdeleClassSubgroup S T n :=
    map_subgroupOf_auxiliaryKummerIdeleSubgroup S T n
  have hker : f.ker.map J.subtype = IdeleGroup.principalSubgroup (𝓞 K) K ⊓ J := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', Subgroup.map_comap_eq,
      Subgroup.range_subtype, inf_comm]
  have hprincipal : E.relIndex f.ker =
      ((auxiliaryKummerIdeleSubgroup S T n).comap (IdeleGroup.unitEmbedding (𝓞 K) K)).relIndex
        (((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T).unit K) := by
    -- `E` is the pullback to the subtype of `(S ∪ T)`-ideles, as in `Subgroup.subgroupOf`.
    dsimp only [E, Subgroup.subgroupOf]
    rw [Subgroup.relIndex_comap, hker, ← comap_unitEmbedding_auxiliaryKummerIdeleSubgroup_one,
      Subgroup.relIndex_comap, Subgroup.map_comap_eq, inf_comm]
  have hmul := E.index_map_mul_relIndex_ker f hf
  rw [hmap, hprincipal] at hmul
  exact hmul

end TauCeti.ClassFieldTheory

end
