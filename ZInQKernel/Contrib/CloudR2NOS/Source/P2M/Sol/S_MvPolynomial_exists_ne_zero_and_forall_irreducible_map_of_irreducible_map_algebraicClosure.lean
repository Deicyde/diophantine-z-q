/-
NOS-CORE PROBE STAGING COPY (nos-core-probe-001, lane4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.lean
  Source sha256  : a474d37a81f0aa7f5ae75a6bab461683b766ecb9b42c2046a06440e8d67d0e04
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v1, applied: R1×5; rule citations in the batch ledger.
-/

/-
NEW DEFAULT-LIMIT EDITION, H4 L3 under H5 C4 assignment 2026-11-17.
Base is batch1 7885eb97524498f6a74798aca90dbdd4774636c1a16966ec5f6c6276ad3f8210,
including its already-applied coefficient drift repairs. These repairs,
all declarations/statements/imports and every nonnumeric base option are
preserved. The slow localization/Nullstellensatz argument is decomposed
and uses Mathlib's actual maximal-ideal/common-zero theorem, instead of
rebuilding its integral quotient and algebraic-closure lift locally.
SOURCE ONLY for the parent's probe; no native/type/default-heartbeat PASS.
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

namespace P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure
r2nos_namespace_dual

set_option autoImplicit false

open MvPolynomial
r2nos_open_dual "MvPolynomial"

namespace P2mBertiniNoether
r2nos_namespace_dual

universe u v w

variable {σ : Type v}

def BddExp (σ : Type v) (d : ℕ) : Type v := {α : σ →₀ ℕ // ∀ s, α s ≤ d}

scoped instance instFiniteBddExp [Finite σ] (d : ℕ) : Finite (BddExp σ d) := by
  classical
  refine Finite.of_injective (fun α : BddExp σ d => fun s : σ => (⟨α.1 s, Nat.lt_succ_of_le
    (α.2 s)⟩ : Fin (d + 1))) ?_
  intro α β h
  apply Subtype.ext
  ext s
  have := congrArg (fun f : σ → Fin (d + 1) => (f s : ℕ)) h
  simpa using this

noncomputable scoped instance instFintypeBddExp [Finite σ] (d : ℕ) : Fintype (BddExp σ d) :=
  Fintype.ofFinite _

abbrev Vars (σ : Type v) (d : ℕ) : Type v := BddExp σ d ⊕ BddExp σ d ⊕ Bool

scoped instance instFiniteVars [Finite σ] (d : ℕ) : Finite (Vars σ d) := by
  unfold Vars; infer_instance

section System

variable {R : Type u} [CommRing R] [Finite σ] (d : ℕ)

noncomputable def genG : MvPolynomial σ (MvPolynomial (Vars σ d) R) :=
  ∑ b : BddExp σ d, monomial b.1 (X (Sum.inl b))

noncomputable def genH : MvPolynomial σ (MvPolynomial (Vars σ d) R) :=
  ∑ b : BddExp σ d, monomial b.1 (X (Sum.inr (Sum.inl b)))

noncomputable def genRel (F : MvPolynomial σ R) : MvPolynomial σ (MvPolynomial (Vars σ d) R) :=
  genG d * genH d - map (C : R →+* MvPolynomial (Vars σ d) R) F

noncomputable def sysIdeal (F : MvPolynomial σ R) (a b : BddExp σ d) :
    Ideal (MvPolynomial (Vars σ d) R) :=
  Ideal.span (Set.range fun m : σ →₀ ℕ => (genRel d F).coeff m) ⊔
    Ideal.span {X (Sum.inr (Sum.inr false)) * X (Sum.inl a) - 1,
      X (Sum.inr (Sum.inr true)) * X (Sum.inr (Sum.inl b)) - 1}

variable {d}

noncomputable def readG {E : Type w} [CommRing E] (ψ : MvPolynomial (Vars σ d) R →+* E) :
    MvPolynomial σ E :=
  ∑ b : BddExp σ d, monomial b.1 (ψ (X (Sum.inl b)))

noncomputable def readH {E : Type w} [CommRing E] (ψ : MvPolynomial (Vars σ d) R →+* E) :
    MvPolynomial σ E :=
  ∑ b : BddExp σ d, monomial b.1 (ψ (X (Sum.inr (Sum.inl b))))

lemma map_genG {E : Type w} [CommRing E] (ψ : MvPolynomial (Vars σ d) R →+* E) :
    map ψ (genG (R := R) d) = readG ψ := by
  simp only [genG, readG, map_sum, map_monomial]

lemma map_genH {E : Type w} [CommRing E] (ψ : MvPolynomial (Vars σ d) R →+* E) :
    map ψ (genH (R := R) d) = readH ψ := by
  simp only [genH, readH, map_sum, map_monomial]

lemma map_genRel {E : Type w} [CommRing E] (ψ : MvPolynomial (Vars σ d) R →+* E)
    (F : MvPolynomial σ R) :
    map ψ (genRel d F) = readG ψ * readH ψ - map (ψ.comp C) F := by
  simp only [genRel, map_sub, map_mul, map_genG, map_genH, map_map]

lemma coeff_sum_monomial {E : Type w} [CommRing E] (c : BddExp σ d → E) (a : BddExp σ d) :
    (∑ b : BddExp σ d, monomial b.1 (c b) : MvPolynomial σ E).coeff a.1 = c a := by
  classical
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Subtype.ext h)
  · intro h; exact absurd (Finset.mem_univ a) h

lemma coeff_readG {E : Type w} [CommRing E] (ψ : MvPolynomial (Vars σ d) R →+* E)
    (a : BddExp σ d) : (readG ψ).coeff a.1 = ψ (X (Sum.inl a)) :=
  coeff_sum_monomial _ a

lemma coeff_readH {E : Type w} [CommRing E] (ψ : MvPolynomial (Vars σ d) R →+* E)
    (b : BddExp σ d) : (readH ψ).coeff b.1 = ψ (X (Sum.inr (Sum.inl b))) :=
  coeff_sum_monomial _ b

lemma factor_of_forall_mem_sysIdeal {E : Type w} [CommRing E]
    (ψ : MvPolynomial (Vars σ d) R →+* E) (F : MvPolynomial σ R) (a b : BddExp σ d)
    (hψ : ∀ p ∈ sysIdeal d F a b, ψ p = 0) :
    readG ψ * readH ψ = map (ψ.comp C) F ∧
      ψ (X (Sum.inr (Sum.inr false))) * (readG ψ).coeff a.1 = 1 ∧
      ψ (X (Sum.inr (Sum.inr true))) * (readH ψ).coeff b.1 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · have h0 : map ψ (genRel d F) = 0 := by
      ext m
      rw [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
      exact hψ _ (Ideal.mem_sup_left (Ideal.subset_span ⟨m, rfl⟩))
    rw [map_genRel] at h0
    exact sub_eq_zero.mp h0
  · rw [coeff_readG]
    have := hψ _ (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_insert _ _)))
    rw [map_sub, map_one, map_mul, sub_eq_zero] at this
    exact this
  · rw [coeff_readH]
    have := hψ _ (Ideal.mem_sup_right (Ideal.subset_span
      (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
    rw [map_sub, map_one, map_mul, sub_eq_zero] at this
    exact this

lemma eq_sum_monomial_of_bdd {E : Type w} [CommRing E] (g : MvPolynomial σ E)
    (hg : ∀ m ∈ g.support, ∀ s, m s ≤ d) :
    g = ∑ b : BddExp σ d, monomial b.1 (g.coeff b.1) := by
  classical
  ext m
  by_cases hm : ∀ s, m s ≤ d
  · rw [coeff_sum_monomial (fun b : BddExp σ d => g.coeff b.1) ⟨m, hm⟩]
  · rw [coeff_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_eq_zero]
    · by_contra h
      exact hm (hg m (mem_support_iff.mpr h))
    · intro b _
      rw [if_neg]
      intro h
      exact hm (h ▸ b.2)

lemma exists_hom_of_factor {E : Type w} [CommRing E] (φ : R →+* E) (F : MvPolynomial σ R)
    (g h : MvPolynomial σ E) (hg : ∀ m ∈ g.support, ∀ s, m s ≤ d)
    (hh : ∀ m ∈ h.support, ∀ s, m s ≤ d) (hgh : g * h = map φ F) (a b : BddExp σ d)
    (t t' : E) (ht : t * g.coeff a.1 = 1) (ht' : t' * h.coeff b.1 = 1) :
    ∃ ψ : MvPolynomial (Vars σ d) R →+* E, ψ.comp C = φ ∧ ∀ p ∈ sysIdeal d F a b, ψ p = 0 := by
  classical
  let x : Vars σ d → E := Sum.elim (fun b => g.coeff b.1)
    (Sum.elim (fun b => h.coeff b.1) (fun bb => cond bb t' t))
  refine ⟨eval₂Hom φ x, eval₂Hom_comp_C φ x, ?_⟩
  have hG : readG (eval₂Hom φ x) = g := by
    rw [readG, eq_sum_monomial_of_bdd g hg]
    simp only [coe_eval₂Hom, eval₂_X, x, Sum.elim_inl]
  have hH : readH (eval₂Hom φ x) = h := by
    rw [readH, eq_sum_monomial_of_bdd h hh]
    simp only [coe_eval₂Hom, eval₂_X, x, Sum.elim_inr, Sum.elim_inl]
  intro p hp
  rw [← RingHom.mem_ker]
  revert p
  change sysIdeal d F a b ≤ RingHom.ker (eval₂Hom φ x)
  rw [sysIdeal, sup_le_iff, Ideal.span_le, Ideal.span_le]
  constructor
  · rintro _ ⟨m, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, ← coeff_map, map_genRel, hG, hH, eval₂Hom_comp_C, hgh,
      sub_self, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  · intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rw [SetLike.mem_coe, RingHom.mem_ker]
    rcases hp with rfl | rfl
    · rw [map_sub, map_mul, map_one]
      simp only [coe_eval₂Hom, eval₂_X, x, Sum.elim_inr, Sum.elim_inl, cond_false]
      rw [ht, sub_self]
    · rw [map_sub, map_mul, map_one]
      simp only [coe_eval₂Hom, eval₂_X, x, Sum.elim_inr, Sum.elim_inl, cond_true]
      rw [ht', sub_self]

end System

/-- The constant multiplicative set remains disjoint from J. Isolate
    this localization argument from all algebraic-closure quotient data. -/
lemma fraction_map_ne_top_of_no_constants
    {R : Type u} [CommRing R] [IsDomain R] {ι : Type v}
    (J : Ideal (MvPolynomial ι R)) (hJ : ∀ c : R, c ≠ 0 → C c ∉ J) :
    J.map (MvPolynomial.map (algebraMap R (FractionRing R))) ≠ ⊤ := by
  letI : Algebra (MvPolynomial ι R) (MvPolynomial ι (FractionRing R)) :=
    MvPolynomial.algebraMvPolynomial
  haveI : IsLocalization ((nonZeroDivisors R).map (C : R →+* MvPolynomial ι R))
      (MvPolynomial ι (FractionRing R)) := MvPolynomial.isLocalization _ _
  have hdisj : Disjoint
      (((nonZeroDivisors R).map (C : R →+* MvPolynomial ι R) : Submonoid (MvPolynomial ι R)) :
        Set (MvPolynomial ι R)) (J : Set (MvPolynomial ι R)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨c, hc, rfl⟩ hcJ
    exact hJ c (nonZeroDivisors.ne_zero hc) hcJ
  have hne := (IsLocalization.map_algebraMap_ne_top_iff_disjoint
    ((nonZeroDivisors R).map (C : R →+* MvPolynomial ι R))
    (MvPolynomial ι (FractionRing R)) J).mpr hdisj
  exact hne

/-- Reuse Mathlib's actual weak Nullstellensatz on a proper finite-variable
    ideal over a field. No chosen quotient Field/Integral/lift instances
    are re-elaborated in the calling theorem. -/
lemma exists_common_zero_of_ne_top
    {k : Type u} [Field k] {K : Type w} [Field K] [Algebra k K] [IsAlgClosed K]
    {ι : Type v} [Finite ι] (I : Ideal (MvPolynomial ι k)) (hI : I ≠ ⊤) :
    ∃ x : ι → K, ∀ p ∈ I, aeval x p = 0 := by
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨x, hx⟩ := _root_.MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hm
  refine ⟨x, fun p hp => ?_⟩
  have hpm := hIm hp
  rw [hx] at hpm
  exact (_root_.MvPolynomial.mem_vanishingIdeal_singleton_iff x p).mp hpm

/-- Evaluation commutes with this genuine scalar tower. A short opaque
    equality replaces reconstruction of a composite quotient RingHom. -/
lemma aeval_map_through_tower
    {R : Type u} [CommRing R] {k : Type u} [CommRing k] {K : Type w} [CommRing K]
    [Algebra R k] [Algebra k K] [Algebra R K] [IsScalarTower R k K]
    {ι : Type v} (x : ι → K) (p : MvPolynomial ι R) :
    aeval (R := k) x (MvPolynomial.map (algebraMap R k) p) = aeval (R := R) x p := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, ← IsScalarTower.algebraMap_eq]
  rfl

set_option backward.isDefEq.respectTransparency false in

theorem exists_C_mem_of_forall_exists_aeval_ne_zero
    {R : Type u} [CommRing R] [IsDomain R] {ι : Type v} [Finite ι]
    (J : Ideal (MvPolynomial ι R))
    (hJ : ∀ x : ι → AlgebraicClosure (FractionRing R), ∃ p ∈ J, aeval x p ≠ 0) :
    ∃ c : R, c ≠ 0 ∧ C c ∈ J := by
  classical
  by_contra hcon
  push Not at hcon
  have hne := fraction_map_ne_top_of_no_constants J hcon
  obtain ⟨x, hx⟩ := exists_common_zero_of_ne_top
    (K := AlgebraicClosure (FractionRing R))
    (J.map (MvPolynomial.map (algebraMap R (FractionRing R)))) hne
  obtain ⟨p, hpJ, hp⟩ := hJ x
  apply hp
  have hzero := hx (MvPolynomial.map (algebraMap R (FractionRing R)) p)
    (Ideal.mem_map_of_mem (MvPolynomial.map (algebraMap R (FractionRing R))) hpJ)
  rw [aeval_map_through_tower] at hzero
  exact hzero

section Main

variable {R : Type u} [CommRing R]

lemma exists_coeff_ne_zero_of_not_isUnit {E : Type w} [Field E] {p : MvPolynomial σ E}
    (hp0 : p ≠ 0) (hp : ¬ IsUnit p) : ∃ m : σ →₀ ℕ, m ≠ 0 ∧ p.coeff m ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  apply hp
  rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced]
  refine ⟨p.coeff 0, ?_, ?_⟩
  · rw [isUnit_iff_ne_zero]
    intro h0
    apply hp0
    ext m
    by_cases hm : m = 0
    · rw [hm, h0, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    · rw [hcon m hm, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  · ext m
    rw [coeff_C]
    by_cases hm : m = 0
    · subst hm; simp
    · rw [if_neg (Ne.symm hm), hcon m hm]

lemma not_isUnit_of_coeff_ne_zero {E : Type w} [CommRing E] [IsReduced E] {p : MvPolynomial σ E}
    {m : σ →₀ ℕ} (hm : m ≠ 0) (h : p.coeff m ≠ 0) : ¬ IsUnit p := by
  classical
  intro hu
  rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced] at hu
  obtain ⟨r, -, rfl⟩ := hu
  rw [coeff_C, if_neg (Ne.symm hm)] at h
  exact h rfl

lemma totalDegree_map_le {E : Type w} [CommRing E] (φ : R →+* E) (F : MvPolynomial σ R) :
    (map φ F).totalDegree ≤ F.totalDegree :=
  Finset.sup_mono (support_map_subset φ F)

lemma bdd_of_dvd {E : Type w} [Field E] {φ : R →+* E} {F : MvPolynomial σ R}
    {g : MvPolynomial σ E} (hg : g ∣ map φ F) (hF : map φ F ≠ 0) :
    ∀ m ∈ g.support, ∀ s, m s ≤ F.totalDegree := by
  intro m hm s
  calc m s ≤ m.sum (fun _ e => e) := by
        have h__af := Finsupp.le_degree s m
        simp [Finsupp.degree] at h__af
        exact h__af
    _ ≤ g.totalDegree := le_totalDegree hm
    _ ≤ (map φ F).totalDegree := totalDegree_le_of_dvd_of_isDomain hg hF
    _ ≤ F.totalDegree := totalDegree_map_le φ F

end Main

section Final

set_option backward.isDefEq.respectTransparency false in

theorem bertiniNoether {R : Type u} [CommRing R] [IsDomain R] [Finite σ]
    (F : MvPolynomial σ R)
    (hF : Irreducible (map (algebraMap R (AlgebraicClosure (FractionRing R))) F)) :
    ∃ c : R, c ≠ 0 ∧ ∀ (E : Type w) [Field E] (φ : R →+* E), φ c ≠ 0 →
      Irreducible (map φ F) := by
  classical

  have hnopt : ∀ a b : BddExp σ F.totalDegree, a.1 ≠ 0 → b.1 ≠ 0 →
      ∀ x : Vars σ F.totalDegree → AlgebraicClosure (FractionRing R),
        ∃ p ∈ sysIdeal F.totalDegree F a b, aeval x p ≠ 0 := by
    intro a b ha hb x
    by_contra hcon
    push Not at hcon
    obtain ⟨hgh, ht, ht'⟩ := factor_of_forall_mem_sysIdeal
      ((aeval x : MvPolynomial (Vars σ F.totalDegree) R →ₐ[R]
        AlgebraicClosure (FractionRing R)) :
        MvPolynomial (Vars σ F.totalDegree) R →+* AlgebraicClosure (FractionRing R)) F a b hcon
    have hC : ((aeval x : MvPolynomial (Vars σ F.totalDegree) R →ₐ[R]
        AlgebraicClosure (FractionRing R)) :
        MvPolynomial (Vars σ F.totalDegree) R →+* AlgebraicClosure (FractionRing R)).comp C =
        algebraMap R (AlgebraicClosure (FractionRing R)) := by
      ext r
      simp
    rw [hC] at hgh
    have hg : ¬ IsUnit (readG ((aeval x : MvPolynomial (Vars σ F.totalDegree) R →ₐ[R]
        AlgebraicClosure (FractionRing R)) :
        MvPolynomial (Vars σ F.totalDegree) R →+* AlgebraicClosure (FractionRing R))) :=
      not_isUnit_of_coeff_ne_zero ha (fun h0 => by
        rw [h0, mul_zero] at ht; exact zero_ne_one ht)
    have hh : ¬ IsUnit (readH ((aeval x : MvPolynomial (Vars σ F.totalDegree) R →ₐ[R]
        AlgebraicClosure (FractionRing R)) :
        MvPolynomial (Vars σ F.totalDegree) R →+* AlgebraicClosure (FractionRing R))) :=
      not_isUnit_of_coeff_ne_zero hb (fun h0 => by
        rw [h0, mul_zero] at ht'; exact zero_ne_one ht')
    rcases hF.isUnit_or_isUnit hgh.symm with h | h
    exacts [hg h, hh h]

  have hc : ∀ a b : BddExp σ F.totalDegree, ∃ c : R, c ≠ 0 ∧
      (a.1 ≠ 0 → b.1 ≠ 0 → C c ∈ sysIdeal F.totalDegree F a b) := by
    intro a b
    by_cases hab : a.1 ≠ 0 ∧ b.1 ≠ 0
    · obtain ⟨c, hc0, hcJ⟩ :=
        exists_C_mem_of_forall_exists_aeval_ne_zero _ (hnopt a b hab.1 hab.2)
      exact ⟨c, hc0, fun _ _ => hcJ⟩
    · exact ⟨1, one_ne_zero, fun ha hb => (hab ⟨ha, hb⟩).elim⟩
  choose cf hcf0 hcfJ using hc

  obtain ⟨m₁, hm₁, hFm₁⟩ := exists_coeff_ne_zero_of_not_isUnit hF.ne_zero hF.not_isUnit
  rw [coeff_map] at hFm₁
  have hFm₁' : F.coeff m₁ ≠ 0 := fun h => hFm₁ (by rw [h, map_zero])
  refine ⟨F.coeff m₁ * ∏ ab : BddExp σ F.totalDegree × BddExp σ F.totalDegree, cf ab.1 ab.2,
    mul_ne_zero hFm₁' (Finset.prod_ne_zero_iff.mpr fun ab _ => hcf0 ab.1 ab.2), ?_⟩
  intro E _ φ hφ
  rw [map_mul, map_prod] at hφ
  have hφ₁ : φ (F.coeff m₁) ≠ 0 := left_ne_zero_of_mul hφ
  have hφ₂ : ∀ a b : BddExp σ F.totalDegree, φ (cf a b) ≠ 0 := fun a b =>
    (Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hφ)) (a, b) (Finset.mem_univ _)
  have hφF0 : map φ F ≠ 0 := fun h => hφ₁ (by rw [← coeff_map, h, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply])
  refine irreducible_iff.mpr ⟨not_isUnit_of_coeff_ne_zero hm₁ (by rwa [coeff_map]), ?_⟩
  intro g h hgh
  by_contra hu
  push Not at hu
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hφF0 (by rw [hgh, zero_mul])
  have hh0 : h ≠ 0 := by
    rintro rfl
    exact hφF0 (by rw [hgh, mul_zero])
  obtain ⟨ma, hma, hga⟩ := exists_coeff_ne_zero_of_not_isUnit hg0 hu.1
  obtain ⟨mb, hmb, hhb⟩ := exists_coeff_ne_zero_of_not_isUnit hh0 hu.2
  have hgbd := bdd_of_dvd (Dvd.intro _ hgh.symm) hφF0
  have hhbd := bdd_of_dvd (Dvd.intro_left _ hgh.symm) hφF0
  obtain ⟨ψ, hψC, hψ⟩ := exists_hom_of_factor φ F g h hgbd hhbd hgh.symm
    ⟨ma, hgbd ma (mem_support_iff.mpr hga)⟩ ⟨mb, hhbd mb (mem_support_iff.mpr hhb)⟩
    (g.coeff ma)⁻¹ (h.coeff mb)⁻¹ (inv_mul_cancel₀ hga) (inv_mul_cancel₀ hhb)
  have := hψ _ (hcfJ ⟨ma, hgbd ma (mem_support_iff.mpr hga)⟩
    ⟨mb, hhbd mb (mem_support_iff.mpr hhb)⟩ hma hmb)
  rw [← RingHom.comp_apply, hψC] at this
  exact hφ₂ _ _ this

end Final

end P2mBertiniNoether
w03_reactivate "P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.P2mBertiniNoether"

universe u v w

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] {σ : Type v} [Finite σ] (F : MvPolynomial σ R)
    (hF : Irreducible (MvPolynomial.map (algebraMap R (AlgebraicClosure (FractionRing R))) F)) :
    ∃ c : R, c ≠ 0 ∧ ∀ (E : Type w) [Field E] (φ : R →+* E), φ c ≠ 0 →
      Irreducible (MvPolynomial.map φ F) :=
  P2mBertiniNoether.bertiniNoether F hF
end S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
