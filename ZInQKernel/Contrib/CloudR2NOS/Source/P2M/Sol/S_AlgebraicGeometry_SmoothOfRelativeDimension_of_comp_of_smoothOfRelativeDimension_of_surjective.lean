/-
NOS-CORE PROBE STAGING COPY (lane C4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_SmoothOfRelativeDimension_of_comp_of_smoothOfRelativeDimension_of_surjective.lean
  Source sha256  : 8623428a99913ec88c5efd009b69c3a7e7d3062f6c68266621f7da7ea754318b
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v1 (lane C4 drift rules v1), applied: R6×1; rule citations in the batch ledger.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_of_comp_of_smoothOfRelativeDimension_of_surjective
r2nos_namespace_dual

set_option autoImplicit false

universe u

open TensorProduct
r2nos_open_dual "TensorProduct"

namespace RelDimSub
r2nos_namespace_dual

theorem rank_baseChange_eq {A : Type u} (B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Nontrivial B] (N : Type u) [AddCommGroup N] [Module A N] [Module.Free A N] :
    Module.rank B (B ⊗[A] N) = Module.rank A N := by
  haveI : Nontrivial A := (algebraMap A B).domain_nontrivial
  let b := Module.Free.chooseBasis A N
  let b' := Algebra.TensorProduct.basis B b
  rw [← b.mk_eq_rank'', ← b'.mk_eq_rank'']

noncomputable def omegaLocEquiv {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
    (T' : Type u) [CommRing T'] [Algebra T T'] [Algebra R T'] [IsScalarTower R T T']
    (M : Submonoid T) [IsLocalization M T'] :
    Ω[T'⁄R] ≃ₗ[T'] T' ⊗[T] Ω[T⁄R] :=
  haveI : Algebra.FormallyEtale T T' := Algebra.FormallyEtale.of_isLocalization M
  (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R T T').symm

theorem exists_kaehler_equiv_prod (R S C : Type u) [CommRing R] [CommRing S] [CommRing C] [Algebra R S]
    [Algebra S C] [Algebra R C] [IsScalarTower R S C] [Algebra.FormallySmooth S C]
    [Module.Projective C Ω[C⁄S]] :
    Nonempty (Ω[C⁄R] ≃ₗ[C] (C ⊗[S] Ω[S⁄R]) × Ω[C⁄S]) := by
  have hex : Function.Exact (KaehlerDifferential.mapBaseChange R S C) (KaehlerDifferential.map R S C C) :=
    KaehlerDifferential.exact_mapBaseChange_map R S C
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange R S C) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R S C x).mp hx
    haveI : Subsingleton (Algebra.H1Cotangent S C) := Algebra.FormallySmooth.subsingleton_h1Cotangent
    rw [Subsingleton.elim y 0, map_zero]
  have hsurj : Function.Surjective (KaehlerDifferential.map R S C C) := KaehlerDifferential.map_surjective R S C
  obtain ⟨l, hl⟩ := Module.projective_lifting_property (KaehlerDifferential.map R S C C) LinearMap.id hsurj
  exact ⟨(hex.splitSurjectiveEquiv hinj ⟨l, hl⟩).1⟩

theorem rank_kaehler_eq_sub {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    [Algebra S T] [Algebra R T] [IsScalarTower R S T] [Algebra.IsStandardSmooth R S] [Nontrivial T]
    (a b : ℕ)
    (hb : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension b) (algebraMap S T))
    (ha : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension a) (algebraMap R T)) :
    Module.rank S Ω[S⁄R] = ((a - b : ℕ) : Cardinal) ∧ b ≤ a := by
  classical

  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal T
  obtain ⟨sb, hsb, hPb⟩ := hb
  obtain ⟨sa, hsa, hPa⟩ := ha
  obtain ⟨t, ht, ht𝔪⟩ : ∃ t ∈ sb, t ∉ 𝔪 := by
    by_contra hcon; push Not at hcon
    exact h𝔪.ne_top (top_le_iff.mp (hsb ▸ Ideal.span_le.mpr hcon))
  obtain ⟨t', ht', ht'𝔪⟩ : ∃ t' ∈ sa, t' ∉ 𝔪 := by
    by_contra hcon; push Not at hcon
    exact h𝔪.ne_top (top_le_iff.mp (hsa ▸ Ideal.span_le.mpr hcon))
  let Tb := Localization.Away t
  let Ta := Localization.Away t'
  let C := Localization.AtPrime 𝔪

  have hTb : Algebra.IsStandardSmoothOfRelativeDimension b S Tb := by
    have := hPb t ht
    rwa [← IsScalarTower.algebraMap_eq (R := S) (S := T) (A := Tb),
      RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at this
  have hTa : Algebra.IsStandardSmoothOfRelativeDimension a R Ta := by
    have := hPa t' ht'
    rwa [← IsScalarTower.algebraMap_eq (R := R) (S := T) (A := Ta),
      RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at this
  haveI : Algebra.IsStandardSmooth S Tb := hTb.isStandardSmooth
  haveI : Algebra.IsStandardSmooth R Ta := hTa.isStandardSmooth

  have hCt : IsUnit (algebraMap T C t) := IsLocalization.map_units C (⟨t, ht𝔪⟩ : 𝔪.primeCompl)
  have hCt' : IsUnit (algebraMap T C t') := IsLocalization.map_units C (⟨t', ht'𝔪⟩ : 𝔪.primeCompl)
  letI : Algebra Tb C := (IsLocalization.Away.lift t hCt).toAlgebra
  haveI : IsScalarTower T Tb C := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.Away.lift_eq t hCt x).symm
  letI : Algebra Ta C := (IsLocalization.Away.lift t' hCt').toAlgebra
  haveI : IsScalarTower T Ta C := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.Away.lift_eq t' hCt' x).symm
  haveI : Nontrivial Tb := (algebraMap Tb C).domain_nontrivial
  haveI : Nontrivial Ta := (algebraMap Ta C).domain_nontrivial

  have hTS : Algebra.Smooth S T := by
    rw [← RingHom.smooth_algebraMap, RingHom.smooth_iff_locally_isStandardSmooth]
    exact RingHom.locally_of_locally
      (fun {R' S' : Type u} [CommRing R'] [CommRing S'] (f : R' →+* S')
        (hf : RingHom.IsStandardSmoothOfRelativeDimension b f) =>
        RingHom.IsStandardSmoothOfRelativeDimension.isStandardSmooth b f hf) ⟨sb, hsb, hPb⟩
  haveI : Algebra.FormallySmooth S T := hTS.formallySmooth
  haveI : Algebra.FormallySmooth T C := Algebra.FormallySmooth.of_isLocalization 𝔪.primeCompl
  haveI : Algebra.FormallySmooth S C := Algebra.FormallySmooth.comp S T C

  have eb : Ω[C⁄S] ≃ₗ[C] C ⊗[Tb] Ω[Tb⁄S] :=
    omegaLocEquiv (R := S) C 𝔪.primeCompl
      ≪≫ₗ (TensorProduct.AlgebraTensorModule.cancelBaseChange T Tb C C Ω[T⁄S]).symm
      ≪≫ₗ TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C C)
            (omegaLocEquiv (R := S) Tb (Submonoid.powers t)).symm
  have ea : Ω[C⁄R] ≃ₗ[C] C ⊗[Ta] Ω[Ta⁄R] :=
    omegaLocEquiv (R := R) C 𝔪.primeCompl
      ≪≫ₗ (TensorProduct.AlgebraTensorModule.cancelBaseChange T Ta C C Ω[T⁄R]).symm
      ≪≫ₗ TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C C)
            (omegaLocEquiv (R := R) Ta (Submonoid.powers t')).symm
  haveI : Module.Free C Ω[C⁄S] := Module.Free.of_equiv eb.symm
  haveI : Module.Projective C Ω[C⁄S] := Module.Projective.of_free
  obtain ⟨e⟩ := exists_kaehler_equiv_prod R S C

  have hrb : Module.rank C Ω[C⁄S] = b := by
    rw [eb.rank_eq, rank_baseChange_eq C Ω[Tb⁄S]]
    exact Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential b
  have hra : Module.rank C Ω[C⁄R] = a := by
    rw [ea.rank_eq, rank_baseChange_eq C Ω[Ta⁄R]]
    exact Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential a
  have hsum : (a : Cardinal) = Module.rank S Ω[S⁄R] + b := by
    rw [← hra, e.rank_eq, rank_prod', rank_baseChange_eq C Ω[S⁄R], hrb]

  obtain ⟨r, hr⟩ : ∃ r : ℕ, Module.rank S Ω[S⁄R] = r := by
    refine Cardinal.lt_aleph0.mp ?_
    calc Module.rank S Ω[S⁄R] ≤ Module.rank S Ω[S⁄R] + b := self_le_add_right _ _
      _ = a := hsum.symm
      _ < Cardinal.aleph0 := Cardinal.natCast_lt_aleph0 (n := a)
  rw [hr] at hsum ⊢
  norm_cast at hsum
  refine ⟨?_, by omega⟩
  congr 1
  omega

end RelDimSub

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry"

theorem solution
    {X Y Z : Scheme.{u}} [Nonempty X] (f : X ⟶ Y) (g : Y ⟶ Z) (a b : ℕ)
    [SmoothOfRelativeDimension a (f ≫ g)] [SmoothOfRelativeDimension b f] [Surjective f] [Smooth g] :
    SmoothOfRelativeDimension (a - b) g ∧ b ≤ a := by

  have key : ∀ (y : Y) (U : Z.Opens) (hU : IsAffineOpen U) (V : Y.Opens) (hV : IsAffineOpen V)
      (hy : y ∈ V) (e : V ≤ g ⁻¹ᵁ U), (g.appLE U V e).hom.IsStandardSmooth →
      (g.appLE U V e).hom.IsStandardSmoothOfRelativeDimension (a - b) ∧ b ≤ a := by
    intro y U hU V hV hy e hstd
    obtain ⟨x, hx⟩ := f.surjective y
    obtain ⟨W, hW, hxW, hWV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ f ⁻¹ᵁ V by simpa [← hx] using hy)

    have hb : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension b) (f.appLE V W hWV).hom :=
      HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension b) f inferInstance ⟨V, hV⟩ ⟨W, hW⟩ hWV
    have ha : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension a)
        ((f.appLE V W hWV).hom.comp (g.appLE U V e).hom) := by
      rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
      exact HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension a) (f ≫ g) inferInstance ⟨U, hU⟩ ⟨W, hW⟩ _

    haveI : Nontrivial Γ(X, W) := (X.presheaf.germ W x hxW).hom.domain_nontrivial
    haveI : Nontrivial Γ(Y, V) := (Y.presheaf.germ V y hy).hom.domain_nontrivial

    letI algRS : Algebra Γ(Z, U) Γ(Y, V) := (g.appLE U V e).hom.toAlgebra
    letI algST : Algebra Γ(Y, V) Γ(X, W) := (f.appLE V W hWV).hom.toAlgebra
    letI algRT : Algebra Γ(Z, U) Γ(X, W) := ((f.appLE V W hWV).hom.comp (g.appLE U V e).hom).toAlgebra
    haveI : IsScalarTower Γ(Z, U) Γ(Y, V) Γ(X, W) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : Algebra.IsStandardSmooth Γ(Z, U) Γ(Y, V) := hstd
    obtain ⟨hr, hle⟩ := RelDimSub.rank_kaehler_eq_sub (R := Γ(Z, U)) (S := Γ(Y, V)) (T := Γ(X, W)) a b hb ha
    exact ⟨(Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth (a - b)).mpr hr, hle⟩
  obtain ⟨x₀⟩ := ‹Nonempty X›
  refine ⟨⟨fun y => ?_⟩, ?_⟩
  · obtain ⟨U, hU, V, hV, hy, e, hstd⟩ := Smooth.exists_isStandardSmooth g y
    exact ⟨U, hU, V, hV, hy, e, (key y U hU V hV hy e hstd).1⟩
  · obtain ⟨U, hU, V, hV, hy, e, hstd⟩ := Smooth.exists_isStandardSmooth g (f.base x₀)
    exact (key _ U hU V hV hy e hstd).2

#print axioms solution
end S_AlgebraicGeometry_SmoothOfRelativeDimension_of_comp_of_smoothOfRelativeDimension_of_surjective
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
