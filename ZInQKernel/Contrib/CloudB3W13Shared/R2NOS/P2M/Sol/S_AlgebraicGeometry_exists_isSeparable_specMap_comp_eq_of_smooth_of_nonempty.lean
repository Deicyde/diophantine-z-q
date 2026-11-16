/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_exists_isSeparable_specMap_comp_eq_of_smooth_of_nonempty.lean
  Retrieved      : 2026-11-16 (immutable raw blob at the revision above; bytes and sha256 in
                   `ZInQKernel/Contrib/CloudB3W13Shared/R2NOS/PORT_MANIFEST.md`)
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(Cloud Batch 3 Worker 13 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679,
2026-11-16). The changes are mechanical; no statement, hypothesis, definition or proof term was
weakened or omitted unless listed under "manual repairs":
  * the whole file is wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end`, so the
    source's root declarations become `ZInQ.Contrib.CloudW03NeronSurj.FLT.<name>`;
  * the source's `import P2M.Util` is dropped: this port contains no port commands, no local
    notation, no macro and no elaborator. The source's
    `p2m_open "Algebra CategoryTheory.Algebra"` is written as the ordinary `open` command it
    abbreviated, in the same scope (`P2mSepPt`);
  * file-level `set_option`s reproduce the source build environment (source lakefile.lean
    leanOptions: autoImplicit false, maxHeartbeats 4000000, synthInstance.maxHeartbeats 400000,
    backward.isDefEq.respectTransparency.types false) together with
    backward.isDefEq.respectTransparency.instanceSearchTypes false, a Lean 4.35 option absent from
    the source's Lean 4.33.1 whose `false` value restores the 4.33.1 behaviour;
  * scopes the source leaves open at end of file are closed explicitly (no-op).
  * every `open` of a Mathlib namespace is written `_root_.<Namespace>`: inside the port
    namespace a bare `open N` resolves to `ZInQ.Contrib.CloudW03NeronSurj.FLT.N` whenever that
    namespace exists in the environment and then shadows Mathlib's root `N`, which is what the
    source's `r2nos_open_dual` shim worked around. Naming the root explicitly is the ordinary-Lean
    equivalent and is stable however the import graph grows.
Manual repairs: none.
-/

import Mathlib

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_exists_isSeparable_specMap_comp_eq_of_smooth_of_nonempty

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

namespace P2mSepPt

open _root_.Algebra _root_.CategoryTheory.Algebra

lemma exists_algHom_of_perfectField (K : Type u) [Field K] [PerfectField K]
    (S : Type u) [CommRing S] [Algebra K S] [Algebra.FiniteType K S]
    (p : Ideal S) (hp : p ≠ ⊤) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
      (_ : Algebra.IsSeparable K K') (_ : S →ₐ[K] K'), True := by
  obtain ⟨M, hM, -⟩ := Ideal.exists_le_maximal p hp
  letI : Field (S ⧸ M) := Ideal.Quotient.field M
  haveI : Algebra.FiniteType K (S ⧸ M) := inferInstance
  haveI : Module.Finite K (S ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (S ⧸ M)
  haveI : Algebra.IsAlgebraic K (S ⧸ M) := Algebra.IsAlgebraic.of_finite K (S ⧸ M)
  haveI : Algebra.IsSeparable K (S ⧸ M) := Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact ⟨S ⧸ M, inferInstance, inferInstance, inferInstance, inferInstance,
    Ideal.Quotient.mkₐ K M, trivial⟩

lemma exists_eval_ne_zero {K : Type u} [Field K] [Infinite K] {n : ℕ}
    {h : MvPolynomial (Fin n) K} (hh : h ≠ 0) :
    ∃ a : Fin n → K, MvPolynomial.eval a h ≠ 0 := by
  by_contra! H
  exact hh (MvPolynomial.funext fun a => by simpa using H a)

lemma exists_isMaximal_isSeparable_of_etale (K : Type u) [Field K] [Infinite K] (n : ℕ)
    (Sf : Type u) [CommRing Sf] [Algebra K Sf]
    [Algebra (MvPolynomial (Fin n) K) Sf] [IsScalarTower K (MvPolynomial (Fin n) K) Sf]
    [Algebra.Etale (MvPolynomial (Fin n) K) Sf] (Q₀ : Ideal Sf) [Q₀.IsPrime] :
    ∃ (M : Ideal Sf) (_ : M.IsMaximal),
      FiniteDimensional K (Sf ⧸ M) ∧ Algebra.IsSeparable K (Sf ⧸ M) := by
  classical

  haveI : Module.Flat (MvPolynomial (Fin n) K) Sf := inferInstance
  haveI : Algebra.HasGoingDown (MvPolynomial (Fin n) K) Sf := Algebra.HasGoingDown.of_flat
  have hopen : IsOpenMap (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) K) Sf)) :=
    PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation

  have hU : IsOpen (Set.range (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) K) Sf))) :=
    hopen.isOpen_range
  let q₀ : PrimeSpectrum (MvPolynomial (Fin n) K) := PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) K) Sf) ⟨Q₀, ‹_›⟩
  have hq₀ : q₀ ∈ Set.range (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) K) Sf)) := ⟨_, rfl⟩
  obtain ⟨_, ⟨h, rfl⟩, hq₀h, hhU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hq₀ hU
  have hh0 : h ≠ 0 := by
    intro H
    rw [H] at hq₀h
    simp [PrimeSpectrum.basicOpen_zero] at hq₀h

  obtain ⟨a, ha⟩ := exists_eval_ne_zero hh0
  let ev : (MvPolynomial (Fin n) K) →ₐ[K] K := MvPolynomial.aeval a
  have hev : Function.Surjective ev := fun x =>
    ⟨MvPolynomial.C x, by simp [ev]⟩
  let m : Ideal (MvPolynomial (Fin n) K) := RingHom.ker ev
  haveI hm : m.IsMaximal := RingHom.ker_isMaximal_of_surjective ev hev
  have hhm : h ∉ m := by
    change ev h ≠ 0
    simpa [ev, MvPolynomial.aeval_eq_eval, MvPolynomial.coe_aeval_eq_eval] using ha
  have hmD : (⟨m, hm.isPrime⟩ : PrimeSpectrum (MvPolynomial (Fin n) K)) ∈ PrimeSpectrum.basicOpen h := hhm
  obtain ⟨Q, hQ⟩ := hhU hmD

  obtain ⟨M, hM, hQM⟩ := Ideal.exists_le_maximal Q.asIdeal Q.isPrime.ne_top
  have hmM : m ≤ M.comap (algebraMap (MvPolynomial (Fin n) K) Sf) := by
    have : Q.asIdeal.comap (algebraMap (MvPolynomial (Fin n) K) Sf) = m := by
      simpa [PrimeSpectrum.ext_iff] using hQ
    rw [← this]
    exact Ideal.comap_mono hQM
  letI : Field (Sf ⧸ M) := Ideal.Quotient.field M
  refine ⟨M, hM, ?_, ?_⟩
  ·
    haveI : Algebra.FiniteType K (MvPolynomial (Fin n) K) := inferInstance
    haveI : Algebra.FiniteType (MvPolynomial (Fin n) K) Sf := inferInstance
    haveI : Algebra.FiniteType K Sf := Algebra.FiniteType.trans (S := (MvPolynomial (Fin n) K)) inferInstance inferInstance
    haveI : Algebra.FiniteType K (Sf ⧸ M) := inferInstance
    exact finite_of_finite_type_of_isJacobsonRing K (Sf ⧸ M)
  ·
    let κ := (MvPolynomial (Fin n) K) ⧸ m
    letI : Field κ := Ideal.Quotient.field m
    letI : Algebra κ (Sf ⧸ M) := (Ideal.quotientMap M (algebraMap (MvPolynomial (Fin n) K) Sf) hmM).toAlgebra
    haveI : IsScalarTower (MvPolynomial (Fin n) K) κ (Sf ⧸ M) := IsScalarTower.of_algebraMap_eq fun x => by
      change Ideal.Quotient.mk M (algebraMap (MvPolynomial (Fin n) K) Sf x) =
        Ideal.quotientMap M (algebraMap (MvPolynomial (Fin n) K) Sf) hmM (Ideal.Quotient.mk m x)
      rw [Ideal.quotientMap_mk]
    haveI : IsScalarTower K κ (Sf ⧸ M) := IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap Sf (Sf ⧸ M) (algebraMap K Sf x) =
        Ideal.quotientMap M (algebraMap (MvPolynomial (Fin n) K) Sf) hmM (Ideal.Quotient.mk m (algebraMap K (MvPolynomial (Fin n) K) x))
      rw [Ideal.quotientMap_mk, IsScalarTower.algebraMap_apply K (MvPolynomial (Fin n) K) Sf]
      rfl
    haveI : Algebra.FormallyUnramified (MvPolynomial (Fin n) K) (Sf ⧸ M) :=
      Algebra.FormallyUnramified.comp (MvPolynomial (Fin n) K) Sf (Sf ⧸ M)
    haveI : Algebra.FormallyUnramified κ (Sf ⧸ M) :=
      Algebra.FormallyUnramified.of_restrictScalars (MvPolynomial (Fin n) K) κ (Sf ⧸ M)
    haveI : Algebra.FiniteType (MvPolynomial (Fin n) K) (Sf ⧸ M) := inferInstance
    haveI : Algebra.FiniteType κ (Sf ⧸ M) :=
      Algebra.FiniteType.of_restrictScalars_finiteType (MvPolynomial (Fin n) K) κ (Sf ⧸ M)
    haveI : Algebra.EssFiniteType κ (Sf ⧸ M) := inferInstance
    haveI : Algebra.IsSeparable κ (Sf ⧸ M) :=
      (Algebra.FormallyUnramified.iff_isSeparable κ (Sf ⧸ M)).mp inferInstance

    let e : κ ≃ₐ[K] K := Ideal.quotientKerAlgEquivOfSurjective hev
    haveI : Algebra.IsSeparable K κ :=
      Algebra.IsSeparable.of_algHom K K e.toAlgHom
    exact Algebra.IsSeparable.trans K κ (Sf ⧸ M)

lemma exists_algHom_of_smooth (K : Type u) [Field K]
    (S : Type u) [CommRing S] [Algebra K S] [Algebra.Smooth K S]
    (p : Ideal S) [p.IsPrime] :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
      (_ : Algebra.IsSeparable K K') (_ : S →ₐ[K] K'), True := by
  classical
  cases finite_or_infinite K with
  | inl hfin =>
    haveI : PerfectField K := inferInstance
    exact exists_algHom_of_perfectField K S p (Ideal.IsPrime.ne_top ‹_›)
  | inr hinf =>
    obtain ⟨f, hfp, n, _inst, htower, hstd⟩ :=
      Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K) (S := S) (p := p)
    haveI := htower
    haveI := hstd

    haveI hp' : (Ideal.map (algebraMap S (Localization.Away f)) p).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ _ ‹_›
        ((Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hfp)
    obtain ⟨M, hM, hfinM, hsepM⟩ := exists_isMaximal_isSeparable_of_etale K n
      (Localization.Away f) (Ideal.map (algebraMap S (Localization.Away f)) p)
    letI : Field (Localization.Away f ⧸ M) := Ideal.Quotient.field M
    exact ⟨Localization.Away f ⧸ M, inferInstance, inferInstance, hfinM, hsepM,
      (Ideal.Quotient.mkₐ K M).comp (IsScalarTower.toAlgHom K S (Localization.Away f)), trivial⟩

end P2mSepPt

theorem solution
    (K : Type u) [Field K] {V : Scheme.{u}} (g : V ⟶ Spec (CommRingCat.of K)) [Smooth g]
    [Nonempty V] :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
      (_ : Algebra.IsSeparable K K') (P : Spec (CommRingCat.of K') ⟶ V),
      P ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K K')) := by
  classical
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨_, ⟨U, hU, rfl⟩, hvU, -⟩ :=
    V.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ v) isOpen_univ
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (hU.fromSpec ≫ g)
  have hsm : Smooth (Spec.map ψ) := by rw [hψ]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)] at hsm
  algebraize [ψ.hom]

  obtain ⟨x, -⟩ : ∃ x : Spec Γ(V, U), hU.fromSpec.base x = v := by
    have : v ∈ Set.range hU.fromSpec.base := by rw [hU.range_fromSpec]; exact hvU
    exact this
  obtain ⟨K', _, _, _, _, χ, -⟩ :=
    P2mSepPt.exists_algHom_of_smooth K Γ(V, U) x.asIdeal
  refine ⟨K', inferInstance, inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ hU.fromSpec, ?_⟩
  rw [Category.assoc, ← hψ, ← Spec.map_comp]
  congr 1
  ext1
  change χ.toRingHom.comp ψ.hom = algebraMap K K'
  exact χ.comp_algebraMap

end P2MW.S_AlgebraicGeometry_exists_isSeparable_specMap_comp_eq_of_smooth_of_nonempty

end ZInQ.Contrib.CloudW03NeronSurj.FLT
