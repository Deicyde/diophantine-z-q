import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_HenselianLocalRing_exists_algHom_lift_of_etale.lean
Original Git blob: 253afcdc10f78890cf09bcdb93441f7ec6d94a0b
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_HenselianLocalRing_exists_algHom_lift_of_etale
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open Polynomial IsLocalRing

namespace W2Port
h77_bridge_namespace

section StandardEtalePairSections

variable {R : Type u} [CommRing R] [HenselianLocalRing R]

theorem standardEtalePair_residueSection_exists
    (P : StandardEtalePair R) (φ : P.Ring →ₐ[R] ResidueField R) :
    ∃ ret : P.Ring →ₐ[R] R,
      ∀ s : P.Ring, algebraMap R (ResidueField R) (ret s) = φ s := by
  have aeval_eq : ∀ (r : R) (p : R[X]), aeval r p = p.eval r :=
    fun r p => congrFun (coe_aeval_eq_eval r) p
  have hx₀ : P.HasMap (φ P.X) := StandardEtalePair.hasMap_X.map φ
  obtain ⟨a₀, ha₀⟩ := residue_surjective (R := R) (φ P.X)
  have ha₀' : algebraMap R (ResidueField R) a₀ = φ P.X := by
    rw [ResidueField.algebraMap_eq]; exact ha₀
  have hresAt : ∀ b : R, algebraMap R (ResidueField R) b = φ P.X →
      ∀ p : R[X], algebraMap R (ResidueField R) (p.eval b) = aeval (φ P.X) p := by
    intro b hb p
    rw [← aeval_algebraMap_apply_eq_algebraMap_eval, hb]
  have unitOfRes : ∀ b : R, IsUnit (algebraMap R (ResidueField R) b) → IsUnit b := by
    intro b hb
    rw [← notMem_maximalIdeal]
    intro hbm
    exact hb.ne_zero (by rw [ResidueField.algebraMap_eq]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hbm)
  have hmem : P.f.eval a₀ ∈ maximalIdeal R := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    show algebraMap R (ResidueField R) (P.f.eval a₀) = 0
    rw [hresAt a₀ ha₀']; exact hx₀.1
  have hud : IsUnit ((derivative P.f).eval a₀) :=
    unitOfRes _ (hresAt a₀ ha₀' _ ▸ hx₀.isUnit_derivative_f)
  obtain ⟨a, haroot, hadiff⟩ := HenselianLocalRing.is_henselian P.f P.monic_f a₀ hmem hud
  have hares : algebraMap R (ResidueField R) a = φ P.X := by
    rw [ResidueField.algebraMap_eq, ← ha₀]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem a a₀).mpr hadiff
  have hmap : P.HasMap a := ⟨aeval_eq a P.f ▸ haroot,
    aeval_eq a _ ▸ unitOfRes _ (hresAt a hares _ ▸ hx₀.2)⟩
  refine ⟨P.lift a hmap, fun s => ?_⟩
  have hcomp : (Algebra.ofId R (ResidueField R)).comp (P.lift a hmap) = φ :=
    StandardEtalePair.hom_ext (by
      rw [AlgHom.comp_apply, StandardEtalePair.lift_X, Algebra.ofId_apply]; exact hares)
  have hs := AlgHom.congr_fun hcomp s
  rw [AlgHom.comp_apply, Algebra.ofId_apply] at hs; exact hs

end StandardEtalePairSections

section IsStandardEtaleSections

variable {R : Type u} [CommRing R] [HenselianLocalRing R]

theorem isStandardEtale_residueSection_exists
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.IsStandardEtale R S]
    (φ : S →ₐ[R] ResidueField R) :
    ∃ ret : S →ₐ[R] R, ∀ s : S, algebraMap R (ResidueField R) (ret s) = φ s := by
  obtain ⟨Pres⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := R) (S := S)
  obtain ⟨ret, hret⟩ :=
    standardEtalePair_residueSection_exists Pres.P (φ.comp Pres.equivRing.symm.toAlgHom)
  refine ⟨ret.comp Pres.equivRing.toAlgHom, fun s => ?_⟩
  have := hret (Pres.equivRing s)
  simpa using this

end IsStandardEtaleSections

section Gluing

variable {R : Type u} [CommRing R] [HenselianLocalRing R]

theorem etale_residueSection_exists_of_henselianLocalRing
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (φ : S →ₐ[R] ResidueField R) :
    ∃ ret : S →ₐ[R] R, ∀ s : S, algebraMap R (ResidueField R) (ret s) = φ s := by
  haveI : (RingHom.ker φ.toRingHom).IsPrime := RingHom.ker_isPrime φ.toRingHom
  haveI : Algebra.IsEtaleAt R (RingHom.ker φ.toRingHom) := inferInstance
  obtain ⟨g, hg, hSE⟩ :=
    Algebra.IsEtaleAt.exists_isStandardEtale (R := R) (S := S) (RingHom.ker φ.toRingHom)
  letI := hSE
  have hu : IsUnit (φ.toRingHom g) :=
    isUnit_iff_ne_zero.mpr fun h0 => hg (RingHom.mem_ker.mpr h0)
  have hlift : ∀ s : S,
      IsLocalization.Away.lift (S := Localization.Away g) g hu
        (algebraMap S (Localization.Away g) s) = φ.toRingHom s :=
    fun s => IsLocalization.Away.lift_eq (S := Localization.Away g) g hu s
  let ψ : Localization.Away g →ₐ[R] ResidueField R :=
    { toRingHom := IsLocalization.Away.lift (S := Localization.Away g) g hu
      commutes' := fun r => by
        show IsLocalization.Away.lift (S := Localization.Away g) g hu
            (algebraMap R (Localization.Away g) r) = algebraMap R (ResidueField R) r
        rw [IsScalarTower.algebraMap_apply R S (Localization.Away g), hlift (algebraMap R S r)]
        exact φ.commutes r }
  obtain ⟨ret, hret⟩ := isStandardEtale_residueSection_exists (Localization.Away g) ψ
  refine ⟨ret.comp (IsScalarTower.toAlgHom R S (Localization.Away g)), fun s => ?_⟩
  rw [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply,
    hret (algebraMap S (Localization.Away g) s)]
  exact hlift s

end Gluing

end W2Port

theorem solution
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (φ : S →ₐ[R] IsLocalRing.ResidueField R) :
    ∃ ψ : S →ₐ[R] R, ∀ s : S, algebraMap R (IsLocalRing.ResidueField R) (ψ s) = φ s :=
  W2Port.etale_residueSection_exists_of_henselianLocalRing S φ


end P2MW.S_HenselianLocalRing_exists_algHom_lift_of_etale
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
