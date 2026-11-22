/-
Copyright (c) 2026 Contributors. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.

Root-lifting and residue-section arguments are adapted from the public
Fermat's Last Theorem development, distributed under Apache 2.0:
https://github.com/anthropics/fermats-last-theorem
Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2.
Source files: S_ValuationSubring_henselianLocalRing_of_isAlgClosed.lean,
S_HenselianLocalRing_exists_algHom_lift_of_etale.lean, and
S_Algebra_Etale_algHom_ext_of_forall_sub_mem_map_maximalIdeal_of_henselianLocalRing.lean.
The integral-closure, standard-etale and tensor-separator primitives are
from Mathlib: https://github.com/leanprover-community/mathlib4
Source revision: 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2Raynaud.StrictHenselization.ValuationMaps
import ZInQKernel.Contrib.CloudR2Raynaud.StrictHenselization.Port.UnramifiedDVR

set_option autoImplicit false
noncomputable section
universe u

namespace ZInQ.Contrib.CloudR2Raynaud.StrictHenselization.Ordinary.Construction

open IsLocalRing Polynomial CategoryTheory
open scoped TensorProduct

/-- Integrality places every root of the original monic polynomial
    inside the original valuation subring. -/
private theorem root_mem_valuationSubring
    {Ω : Type u} [Field Ω] (w : ValuationSubring Ω)
    {p : w[X]} (hp : p.Monic) {x : Ω} (hx : (p.map w.subtype).IsRoot x) :
    x ∈ w := by
  have hint : IsIntegral w x := by
    refine ⟨p, hp, ?_⟩
    change p.eval₂ (algebraMap w Ω) x = 0
    change (p.map w.subtype).eval x = 0 at hx
    rw [Polynomial.eval_map] at hx
    exact hx
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := w) (K := Ω)).mp hint
  exact ha ▸ a.2

/-- A monic polynomial whose residue vanishes at the original point
    has a root reducing to that point in the original valuation subring. -/
private theorem ambient_root_lift
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (w : ValuationSubring Ω) :
    ∀ (n : ℕ) (p : w[X]), p.Monic → p.natDegree = n →
      ∀ a₀ : w, p.eval a₀ ∈ maximalIdeal w →
        ∃ a : w, p.IsRoot a ∧ a - a₀ ∈ maximalIdeal w := by
  intro n
  induction n with
  | zero =>
      intro p hp hdeg a₀ ha₀
      have hp1 : p = 1 := (Monic.natDegree_eq_zero hp).mp hdeg
      rw [hp1, eval_one] at ha₀
      exact absurd ((Ideal.eq_top_iff_one _).mpr ha₀) (maximalIdeal.isMaximal w).ne_top
  | succ n ih =>
      intro p hp hdeg a₀ ha₀
      have hdeg' : (p.map w.subtype).degree ≠ 0 := by
        rw [degree_map_eq_of_injective Subtype.val_injective,
          degree_eq_natDegree (Monic.ne_zero hp), hdeg]
        exact_mod_cast Nat.succ_ne_zero n
      obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (p.map w.subtype) hdeg'
      have hxw : x ∈ w := root_mem_valuationSubring w hp hx
      have hxroot : p.IsRoot (⟨x, hxw⟩ : w) := by
        have hval : w.subtype (p.eval (⟨x, hxw⟩ : w)) = 0 := by
          rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
          exact hx
        exact (map_eq_zero_iff _ Subtype.val_injective).mp hval
      let q := p /ₘ (X - C (⟨x, hxw⟩ : w))
      have hfac : (X - C (⟨x, hxw⟩ : w)) * q = p :=
        mul_divByMonic_eq_iff_isRoot.mpr hxroot
      by_cases hpoint : (⟨x, hxw⟩ : w) - a₀ ∈ maximalIdeal w
      · exact ⟨_, hxroot, hpoint⟩
      · have hqmon : q.Monic :=
          Monic.of_mul_monic_left (monic_X_sub_C _) (by rw [hfac]; exact hp)
        have hqdeg : q.natDegree = n := by
          have h := congrArg natDegree hfac
          rw [Monic.natDegree_mul (monic_X_sub_C _) hqmon, natDegree_X_sub_C, hdeg] at h
          omega
        have hqpoint : q.eval a₀ ∈ maximalIdeal w := by
          have h := congrArg (eval a₀) hfac
          rw [eval_mul, eval_sub, eval_X, eval_C] at h
          rw [← h] at ha₀
          rcases (maximalIdeal.isMaximal w).isPrime.mem_or_mem ha₀ with hbad | hgood
          · apply (hpoint ?_).elim
            have hneg := (Ideal.neg_mem_iff _).mpr hbad
            rwa [neg_sub] at hneg
          · exact hgood
        obtain ⟨a, ha, haa₀⟩ := ih q hqmon hqdeg a₀ hqpoint
        refine ⟨a, ?_, haa₀⟩
        show p.eval a = 0
        rw [← hfac, eval_mul, ha.eq_zero, mul_zero]

/-- Henselianity is constructed from roots in the original algebraically
    closed ambient field, not assumed for the original base DVR. -/
private theorem ambient_henselian
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (w : ValuationSubring Ω) :
    HenselianLocalRing w where
  toIsLocalRing := inferInstance
  is_henselian p hp a₀ h₀ _ := ambient_root_lift w p.natDegree p hp rfl a₀ h₀

/-- The simple residue root of a standard-etale algebra lifts to an
    actual section over the given henselian ring. -/
private theorem standard_pair_residue_section
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    (P : StandardEtalePair R) (φ : P.Ring →ₐ[R] ResidueField R) :
    ∃ ret : P.Ring →ₐ[R] R,
      ∀ s : P.Ring, algebraMap R (ResidueField R) (ret s) = φ s := by
  have hev : ∀ (r : R) (p : R[X]), aeval r p = p.eval r :=
    fun r p => congrFun (coe_aeval_eq_eval r) p
  have hx₀ : P.HasMap (φ P.X) := StandardEtalePair.hasMap_X.map φ
  obtain ⟨a₀, ha₀⟩ := residue_surjective (R := R) (φ P.X)
  have ha₀' : algebraMap R (ResidueField R) a₀ = φ P.X := by
    rw [ResidueField.algebraMap_eq]
    exact ha₀
  have hresAt : ∀ b : R, algebraMap R (ResidueField R) b = φ P.X →
      ∀ p : R[X], algebraMap R (ResidueField R) (p.eval b) = aeval (φ P.X) p := by
    intro b hb p
    rw [← aeval_algebraMap_apply_eq_algebraMap_eval, hb]
  have unitOfRes : ∀ b : R, IsUnit (algebraMap R (ResidueField R) b) → IsUnit b := by
    intro b hb
    rw [← notMem_maximalIdeal]
    intro hbm
    exact hb.ne_zero (by
      rw [ResidueField.algebraMap_eq]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hbm)
  have hmem : P.f.eval a₀ ∈ maximalIdeal R := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    show algebraMap R (ResidueField R) (P.f.eval a₀) = 0
    rw [hresAt a₀ ha₀']
    exact hx₀.1
  have hud : IsUnit ((derivative P.f).eval a₀) :=
    unitOfRes _ (hresAt a₀ ha₀' _ ▸ hx₀.isUnit_derivative_f)
  obtain ⟨a, haroot, hadiff⟩ := HenselianLocalRing.is_henselian P.f P.monic_f a₀ hmem hud
  have hares : algebraMap R (ResidueField R) a = φ P.X := by
    rw [ResidueField.algebraMap_eq, ← ha₀]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem a a₀).mpr hadiff
  have hmap : P.HasMap a := ⟨hev a P.f ▸ haroot,
    hev a _ ▸ unitOfRes _ (hresAt a hares _ ▸ hx₀.2)⟩
  refine ⟨P.lift a hmap, fun s => ?_⟩
  have hcomp : (Algebra.ofId R (ResidueField R)).comp (P.lift a hmap) = φ :=
    StandardEtalePair.hom_ext (by
      rw [AlgHom.comp_apply, StandardEtalePair.lift_X, Algebra.ofId_apply]
      exact hares)
  have hs := AlgHom.congr_fun hcomp s
  rw [AlgHom.comp_apply, Algebra.ofId_apply] at hs
  exact hs

private theorem standard_etale_residue_section
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.IsStandardEtale R S]
    (φ : S →ₐ[R] ResidueField R) :
    ∃ ret : S →ₐ[R] R, ∀ s : S, algebraMap R (ResidueField R) (ret s) = φ s := by
  obtain ⟨P⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := R) (S := S)
  obtain ⟨ret, hret⟩ := standard_pair_residue_section P.P (φ.comp P.equivRing.symm.toAlgHom)
  refine ⟨ret.comp P.equivRing.toAlgHom, fun s => ?_⟩
  simpa using hret (P.equivRing s)

/-- An arbitrary etale residue point lifts through a genuine standard-etale
    neighborhood of its kernel. No henselianity of a different ring is used. -/
private theorem etale_residue_section
    {R : Type u} [CommRing R] [HenselianLocalRing R]
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
        change (IsLocalization.Away.lift (S := Localization.Away g) g hu)
          (algebraMap R (Localization.Away g) r) = algebraMap R (ResidueField R) r
        exact (congrArg (IsLocalization.Away.lift (S := Localization.Away g) g hu)
          (IsScalarTower.algebraMap_apply R S (Localization.Away g) r)).trans
            ((hlift (algebraMap R S r)).trans (φ.commutes r)) }
  obtain ⟨ret, hret⟩ := standard_etale_residue_section (Localization.Away g) ψ
  refine ⟨ret.comp (IsScalarTower.toAlgHom R S (Localization.Away g)), fun s => ?_⟩
  rw [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply,
    hret (algebraMap S (Localization.Away g) s)]
  exact hlift s

/-- Etale maps to a local ring are equal when all their values have the
    same residue. The finite-type tensor separator is imported from Mathlib. -/
private theorem etale_maps_eq_of_same_residue
    {R E B : Type u} [CommRing R] [CommRing E] [CommRing B] [IsLocalRing B]
    [Algebra R E] [Algebra R B] [Algebra.Etale R E]
    (φ ψ : E →ₐ[R] B)
    (h : ∀ x : E, φ x - ψ x ∈ maximalIdeal B) : φ = ψ := by
  classical
  let e : E ⊗[R] E := Algebra.FormallyUnramified.elem R E
  let Φ : E ⊗[R] E →ₐ[R] B := Algebra.TensorProduct.productMap φ ψ
  have hΦμ : ∀ t : E ⊗[R] E, Φ t - φ (Algebra.TensorProduct.lmul' R t) ∈ maximalIdeal B := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
        rw [Algebra.TensorProduct.productMap_apply_tmul,
          Algebra.TensorProduct.lmul'_apply_tmul, map_mul, ← mul_sub]
        refine (maximalIdeal B).mul_mem_left _ ?_
        have hneg := (maximalIdeal B).neg_mem (h b)
        rwa [neg_sub] at hneg
    | add t₁ t₂ ht₁ ht₂ =>
        rw [map_add, map_add, map_add]
        convert (maximalIdeal B).add_mem ht₁ ht₂ using 1 <;> ring
  have hΦe : Φ e - 1 ∈ maximalIdeal B := by
    have he : Algebra.TensorProduct.lmul' R e = 1 :=
      Algebra.FormallyUnramified.lmul_elem (R := R) (S := E)
    have h := hΦμ e
    rw [he] at h
    have hφone : φ (1 : E) = (1 : B) := _root_.map_one φ
    exact Eq.mp (congrArg (fun z : B => Φ e - z ∈ maximalIdeal B) hφone) h
  have hunit : IsUnit (Φ e) := by
    by_contra hnu
    have hmem : Φ e ∈ maximalIdeal B := hnu
    have hone : (1 : B) ∈ maximalIdeal B := by
      simpa only [sub_sub_cancel] using (maximalIdeal B).sub_mem hmem hΦe
    exact (maximalIdeal.isMaximal B).ne_top ((Ideal.eq_top_iff_one _).mpr hone)
  apply AlgHom.ext
  intro x
  have hdx : Φ (x ⊗ₜ[R] 1 - 1 ⊗ₜ[R] x) = φ x - ψ x := by
    rw [map_sub, Algebra.TensorProduct.productMap_apply_tmul,
      Algebra.TensorProduct.productMap_apply_tmul, map_one, map_one, mul_one, one_mul]
  have hann : (x ⊗ₜ[R] (1 : E) - (1 : E) ⊗ₜ[R] x) * e = 0 := by
    rw [← neg_sub, neg_mul, Algebra.FormallyUnramified.one_tmul_sub_tmul_one_mul_elem,
      neg_zero]
  have hkey : (φ x - ψ x) * Φ e = 0 := by
    rw [← hdx, ← map_mul, hann, map_zero]
  exact sub_eq_zero.mp (hunit.mul_left_eq_zero.mp hkey)

/-- A DVR has only its zero prime and its unique nonzero prime. -/
private theorem finite_prime_spectrum_of_dvr
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    (Set.univ : Set (PrimeSpectrum R)).Finite := by
  obtain ⟨_, p, hp, huniq⟩ :=
    (IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime R).mp
      (inferInstance : IsDiscreteValuationRing R)
  let p₀ : PrimeSpectrum R := ⟨⊥, inferInstance⟩
  let p₁ : PrimeSpectrum R := ⟨p, hp.2⟩
  apply ((Set.finite_singleton p₁).insert p₀).subset
  intro q _
  have hq : q = p₀ ∨ q = p₁ := by
    by_cases hzero : q.asIdeal = ⊥
    · exact Or.inl (PrimeSpectrum.ext hzero)
    · exact Or.inr (PrimeSpectrum.ext (huniq q.asIdeal ⟨hzero, q.isPrime⟩))
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hq

/-- Finite fibers over the two-point spectrum make every etale DVR-algebra
    have finite prime spectrum. No residue field is assumed finite. -/
private theorem finite_prime_spectrum_of_etale
    {R A : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing A] [Algebra R A] [Algebra.Etale R A] : Finite (PrimeSpectrum A) := by
  have hR : (Set.univ : Set (PrimeSpectrum R)).Finite := finite_prime_spectrum_of_dvr
  have hA : (Set.univ : Set (PrimeSpectrum A)).Finite := by
    simpa only [Set.preimage_univ] using
      (Algebra.QuasiFinite.finite_comap_preimage (R := R) (S := A) hR)
  letI := hA.fintype
  exact Finite.of_surjective
    (fun q : (Set.univ : Set (PrimeSpectrum A)) => q.1)
    (fun q => ⟨⟨q, trivial⟩, rfl⟩)

/-- With finite prime spectrum, localization at the chosen prime is already
    localization at one actual element outside that prime. -/
private theorem local_away_of_finite_prime_spectrum
    {A : Type u} [CommRing A] [Finite (PrimeSpectrum A)]
    (q : Ideal A) [q.IsPrime] :
    ∃ s : A, s ∉ q ∧ IsLocalization q.primeCompl (Localization.Away s) := by
  classical
  letI := Fintype.ofFinite (PrimeSpectrum A)
  have hex (p : PrimeSpectrum A) (h : ¬ p.asIdeal ≤ q) :
      ∃ x : A, x ∈ p.asIdeal ∧ x ∉ q := by
    by_contra! H
    exact h H
  let d : PrimeSpectrum A → q.primeCompl := fun p =>
    if h : p.asIdeal ≤ q then 1
    else ⟨(hex p h).choose, (hex p h).choose_spec.2⟩
  have hd (p : PrimeSpectrum A) (h : ¬ p.asIdeal ≤ q) :
      (d p : A) ∈ p.asIdeal := by
    simpa only [d, dif_neg h] using (hex p h).choose_spec.1
  let s : q.primeCompl := ∏ p : PrimeSpectrum A, d p
  have hbelow (p : PrimeSpectrum A) (hsp : (s : A) ∉ p.asIdeal) : p.asIdeal ≤ q := by
    by_contra hbad
    have hdiv : (d p : A) ∣ (s : A) := by
      simpa only [s, Submonoid.coe_finsetProd] using
        (Finset.dvd_prod_of_mem (fun p : PrimeSpectrum A => (d p : A)) (Finset.mem_univ p))
    exact hsp (p.asIdeal.mem_of_dvd hdiv (hd p hbad))
  refine ⟨s, s.2, ?_⟩
  apply IsLocalization.of_le (Submonoid.powers (s : A)) q.primeCompl
    (Submonoid.powers_le.mpr s.2)
  intro x hx
  apply (PrimeSpectrum.basicOpen_le_basicOpen_iff_algebraMap_isUnit
    (f := (s : A)) (g := x) (S := Localization.Away (s : A))).mp
  intro p hsp
  change x ∉ p.asIdeal
  change x ∉ q at hx
  change (s : A) ∉ p.asIdeal at hsp
  exact fun hxp => hx (hbelow p hsp hxp)

section RationalStages

variable {R B : Type u} [CommRing R] [IsLocalRing R] [CommRing B] [IsLocalRing B]
variable [Algebra R B] [IsLocalHom (algebraMap R B)]

/-- The actual residue-field map, viewed over the original base ring. -/
private def base_residue_hom : ResidueField R →ₐ[R] ResidueField B where
  toRingHom := ResidueField.map (algebraMap R B)
  commutes' r := by
    rw [IsScalarTower.algebraMap_apply R B (ResidueField B)]
    change (ResidueField.map (algebraMap R B)) (residue R r) =
      residue B (algebraMap R B r)
    exact ResidueField.map_residue (algebraMap R B) r

/-- A rational stage is an actual etale subalgebra of the original target,
    with local inclusion and a compatible point over the original residue field. -/
private def RationalStage (S : Subalgebra R B) : Prop :=
  Algebra.Etale R S ∧ IsLocalHom S.val.toRingHom ∧
    ∃ δ : S →ₐ[R] ResidueField R,
      ∀ s : S, residue B (s : B) = ResidueField.map (algebraMap R B) (δ s)

/-- A pointed etale algebra lifts to the actual henselian target after the
    genuine target base change. The source base need not be henselian. -/
private theorem lift_point_to_henselian_target [HenselianLocalRing B]
    (A : Type u) [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (δ : A →ₐ[R] ResidueField R) :
    ∃ g : A →ₐ[R] B,
      ∀ a : A, residue B (g a) = ResidueField.map (algebraMap R B) (δ a) := by
  let κ : ResidueField R →ₐ[R] ResidueField B := base_residue_hom
  let ψ : B ⊗[R] A →ₐ[B] ResidueField B :=
    (AlgHom.liftEquiv R B A (ResidueField B)) (κ.comp δ)
  obtain ⟨ret, hret⟩ := etale_residue_section (B ⊗[R] A) ψ
  let g : A →ₐ[R] B := ret.restrictScalars R |>.comp Algebra.TensorProduct.includeRight
  refine ⟨g, fun a => ?_⟩
  have hpoint := hret (1 ⊗ₜ[R] a)
  rw [ResidueField.algebraMap_eq] at hpoint
  change residue B (ret (1 ⊗ₜ[R] a)) = ψ (1 ⊗ₜ[R] a) at hpoint
  change residue B (ret (1 ⊗ₜ[R] a)) = ResidueField.map (algebraMap R B) (δ a)
  refine hpoint.trans ?_
  simp only [ψ, AlgHom.liftEquiv_tmul, one_smul, AlgHom.comp_apply]
  all_goals rfl

/-- Localizing the given pointed etale algebra at its actual residue-point
    kernel produces a genuine local etale subalgebra inside the target. -/
private theorem rational_stage_of_pointed_etale
    [IsDomain R] [IsDiscreteValuationRing R] [IsDomain B]
    (hRB : Function.Injective (algebraMap R B))
    (A : Type u) [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (δ : A →ₐ[R] ResidueField R) (g : A →ₐ[R] B)
    (hg : ∀ a : A, residue B (g a) = ResidueField.map (algebraMap R B) (δ a)) :
    ∃ S : Subalgebra R B, RationalStage S ∧
      ∃ ψ : A →ₐ[R] S, ∀ a : A, (ψ a : B) = g a := by
  classical
  let q : Ideal A := RingHom.ker δ.toRingHom
  haveI : q.IsPrime := RingHom.ker_isPrime δ.toRingHom
  letI : Finite (PrimeSpectrum A) := finite_prime_spectrum_of_etale (R := R)
  obtain ⟨s, hsq, hloc⟩ := local_away_of_finite_prime_spectrum q
  let Q := Localization.Away s
  letI : IsLocalization q.primeCompl Q := hloc
  letI : IsLocalRing Q := IsLocalization.AtPrime.isLocalRing Q q
  have hsδ : δ s ≠ 0 := by
    intro hs0
    exact hsq (RingHom.mem_ker.mpr hs0)
  have husδ : IsUnit (δ s) := isUnit_iff_ne_zero.mpr hsδ
  have hgs : IsUnit (g s) := by
    apply isUnit_of_map_unit (residue B) (g s)
    apply isUnit_iff_ne_zero.mpr
    rw [hg s]
    exact (map_ne_zero_iff (ResidueField.map (algebraMap R B))
      (ResidueField.map (algebraMap R B)).injective).mpr hsδ
  let δQ : Q →ₐ[R] ResidueField R :=
    { toRingHom := IsLocalization.Away.lift (S := Q) s husδ
      commutes' r := by
        change (IsLocalization.Away.lift (S := Q) s husδ) (algebraMap R Q r) =
          algebraMap R (ResidueField R) r
        exact (congrArg (IsLocalization.Away.lift (S := Q) s husδ)
          (IsScalarTower.algebraMap_apply R A Q r)).trans
            ((IsLocalization.Away.lift_eq (S := Q) s husδ (algebraMap R A r)).trans
              (δ.commutes r)) }
  let gQ : Q →ₐ[R] B :=
    { toRingHom := IsLocalization.Away.lift (S := Q) s hgs
      commutes' r := by
        change (IsLocalization.Away.lift (S := Q) s hgs) (algebraMap R Q r) = algebraMap R B r
        exact (congrArg (IsLocalization.Away.lift (S := Q) s hgs)
          (IsScalarTower.algebraMap_apply R A Q r)).trans
            ((IsLocalization.Away.lift_eq (S := Q) s hgs (algebraMap R A r)).trans
              (g.commutes r)) }
  have hsquare : ∀ z : Q,
      residue B (gQ z) = ResidueField.map (algebraMap R B) (δQ z) := by
    have hmaps : (residue B).comp gQ.toRingHom =
        (ResidueField.map (algebraMap R B)).comp δQ.toRingHom := by
      apply IsLocalization.ringHom_ext (Submonoid.powers s)
      apply RingHom.ext
      intro a
      change residue B (gQ (algebraMap A Q a)) =
        ResidueField.map (algebraMap R B) (δQ (algebraMap A Q a))
      have hgQA : gQ (algebraMap A Q a) = g a := by
        change (IsLocalization.Away.lift (S := Q) s hgs) (algebraMap A Q a) = g a
        exact IsLocalization.Away.lift_eq (S := Q) s hgs a
      have hδQA : δQ (algebraMap A Q a) = δ a := by
        change (IsLocalization.Away.lift (S := Q) s husδ) (algebraMap A Q a) = δ a
        exact IsLocalization.Away.lift_eq (S := Q) s husδ a
      exact (congrArg (residue B) hgQA).trans
        ((hg a).trans (congrArg (ResidueField.map (algebraMap R B)) hδQA.symm))
    exact fun z => RingHom.congr_fun hmaps z
  have hδQsurj : Function.Surjective δQ := by
    intro x
    obtain ⟨r, hr⟩ := residue_surjective (R := R) x
    refine ⟨algebraMap R Q r, ?_⟩
    have h := δQ.commutes r
    rw [ResidueField.algebraMap_eq] at h
    exact h.trans hr
  letI : IsLocalHom δQ.toRingHom := IsLocalHom.of_surjective δQ.toRingHom hδQsurj
  have hcoeff : δQ.toRingHom.comp (algebraMap R Q) = residue R := by
    apply RingHom.ext
    intro r
    change δQ (algebraMap R Q r) = residue R r
    have h := δQ.commutes r
    rw [ResidueField.algebraMap_eq] at h
    exact h
  letI : IsLocalHom (δQ.toRingHom.comp (algebraMap R Q)) := by
    rw [hcoeff]
    infer_instance
  letI : IsLocalHom (algebraMap R Q) := isLocalHom_of_comp (algebraMap R Q) δQ.toRingHom
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨hdomQ, hdvrQ, hirrQ, hmaxQ⟩ :=
    Port.IsDiscreteValuationRing.of_formallyUnramified (A := R) (S := Q) hϖ
  letI := hdomQ
  letI := hdvrQ
  have hϖB : gQ (algebraMap R Q ϖ) ≠ 0 := by
    rw [gQ.commutes]
    exact (map_ne_zero_iff (algebraMap R B) hRB).mpr hϖ.ne_zero
  have hgQinj : Function.Injective gQ := by
    intro x y hxy
    apply sub_eq_zero.mp
    by_contra hne
    have hz : gQ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hirrQ
    have hnon : gQ (x - y) ≠ 0 := by
      rw [hu, map_mul, map_pow]
      exact mul_ne_zero ((Units.isUnit u).map gQ.toRingHom).ne_zero (pow_ne_zero _ hϖB)
    exact hnon hz
  letI : IsLocalHom gQ.toRingHom :=
    { map_nonunit z hz := by
        have hδz : δQ z ≠ 0 := by
          intro hzero
          have hzeroB : residue B (gQ z) = 0 := by
            rw [hsquare z, hzero, map_zero]
          exact (hz.map (residue B)).ne_zero hzeroB
        exact isUnit_of_map_unit δQ.toRingHom z (isUnit_iff_ne_zero.mpr hδz) }
  let S : Subalgebra R B := gQ.range
  let e : Q ≃ₐ[R] S := AlgEquiv.ofInjective gQ hgQinj
  have heval (x : S) : gQ (e.symm x) = (x : B) := by
    have h := congrArg (fun z : S => (z : B)) (e.apply_symm_apply x)
    change gQ (e.symm x) = (x : B) at h
    exact h
  have hlocalS : IsLocalHom S.val.toRingHom :=
    { map_nonunit x hx := by
        have hz : IsUnit (gQ (e.symm x)) := by rw [heval x]; exact hx
        have hb : IsUnit (e.symm x) := isUnit_of_map_unit gQ.toRingHom (e.symm x) hz
        have hux : IsUnit (e (e.symm x)) := hb.map e.toRingHom
        simpa only [e.apply_symm_apply] using hux }
  let δS : S →ₐ[R] ResidueField R := δQ.comp e.symm.toAlgHom
  let ψ : A →ₐ[R] S := e.toAlgHom.comp (IsScalarTower.toAlgHom R A Q)
  refine ⟨S, ?_, ψ, ?_⟩
  · refine ⟨Algebra.Etale.of_equiv e, hlocalS, δS, ?_⟩
    intro x
    change residue B (x : B) = ResidueField.map (algebraMap R B) (δQ (e.symm x))
    rw [← heval x]
    exact hsquare (e.symm x)
  · intro a
    change gQ (algebraMap A Q a) = g a
    exact IsLocalization.Away.lift_eq (S := Q) s hgs a

/-- The base residue point gives a genuine nonempty rational-stage system. -/
private theorem rational_stage_nonempty
    [IsDomain R] [IsDiscreteValuationRing R] [IsDomain B]
    (hRB : Function.Injective (algebraMap R B)) :
    Nonempty {S : Subalgebra R B // RationalStage S} := by
  obtain ⟨S, hS, _, _⟩ := rational_stage_of_pointed_etale hRB R
    (Algebra.ofId R (ResidueField R)) (Algebra.ofId R B) (fun r => by
      simpa only [Algebra.ofId_apply, ResidueField.algebraMap_eq] using
        (ResidueField.map_residue (algebraMap R B) r).symm)
  exact ⟨⟨S, hS⟩⟩

/-- Tensoring two actual rational stages and localizing at their product
    point gives a genuine common rational stage inside the same target. -/
private theorem rational_stage_directed
    [IsDomain R] [IsDiscreteValuationRing R] [IsDomain B]
    (hRB : Function.Injective (algebraMap R B)) :
    Directed (· ≤ ·) (fun i : {S : Subalgebra R B // RationalStage S} => i.1) := by
  intro i j
  let S₁ := i.1
  let S₂ := j.1
  letI : Algebra.Etale R S₁ := i.2.1
  letI : Algebra.Etale R S₂ := j.2.1
  obtain ⟨δ₁, hδ₁⟩ := i.2.2.2
  obtain ⟨δ₂, hδ₂⟩ := j.2.2.2
  let A := S₁ ⊗[R] S₂
  letI : Algebra.Etale R A := Algebra.Etale.comp R S₁ A
  let δ : A →ₐ[R] ResidueField R := Algebra.TensorProduct.productMap δ₁ δ₂
  let g : A →ₐ[R] B := Algebra.TensorProduct.productMap S₁.val S₂.val
  have hg : ∀ a : A, residue B (g a) = ResidueField.map (algebraMap R B) (δ a) := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
        calc
          residue B (g (x ⊗ₜ[R] y)) = residue B (S₁.val x * S₂.val y) :=
            congrArg (residue B) (Algebra.TensorProduct.productMap_apply_tmul S₁.val S₂.val x y)
          _ = residue B (S₁.val x) * residue B (S₂.val y) := (residue B).map_mul _ _
          _ = ResidueField.map (algebraMap R B) (δ₁ x) *
              ResidueField.map (algebraMap R B) (δ₂ y) := congrArg₂ (· * ·) (hδ₁ x) (hδ₂ y)
          _ = ResidueField.map (algebraMap R B) (δ₁ x * δ₂ y) :=
            ((ResidueField.map (algebraMap R B)).map_mul _ _).symm
          _ = ResidueField.map (algebraMap R B) (δ (x ⊗ₜ[R] y)) :=
            congrArg (ResidueField.map (algebraMap R B))
              (Algebra.TensorProduct.productMap_apply_tmul δ₁ δ₂ x y).symm
    | add a b ha hb =>
        simpa only [map_add] using congrArg₂ (· + ·) ha hb
  obtain ⟨S, hS, ψ, hψ⟩ := rational_stage_of_pointed_etale hRB A δ g hg
  refine ⟨⟨S, hS⟩, ?_, ?_⟩
  · intro x hx
    let y : S₁ := ⟨x, hx⟩
    have heq : (ψ (y ⊗ₜ[R] (1 : S₂)) : B) = x := by
      exact (hψ (y ⊗ₜ[R] (1 : S₂))).trans
        (Algebra.TensorProduct.productMap_left_apply S₁.val S₂.val y)
    exact heq ▸ (ψ (y ⊗ₜ[R] (1 : S₂))).2
  · intro x hx
    let y : S₂ := ⟨x, hx⟩
    have heq : (ψ ((1 : S₁) ⊗ₜ[R] y) : B) = x := by
      exact (hψ ((1 : S₁) ⊗ₜ[R] y)).trans
        (Algebra.TensorProduct.productMap_right_apply S₁.val S₂.val y)
    exact heq ▸ (ψ ((1 : S₁) ⊗ₜ[R] y)).2

/-- Rational-point compatibility forces every base algebra automorphism of
    the original local target to fix an actual rational stage pointwise. -/
private theorem rational_stage_fixed
    (S : Subalgebra R B) (hS : RationalStage S) (σ : B ≃ₐ[R] B) :
    ∀ s : S, σ (s : B) = (s : B) := by
  letI : Algebra.Etale R S := hS.1
  obtain ⟨δ, hδ⟩ := hS.2.2
  have ring_apply (e : B ≃ₐ[R] B) (x : B) : e.toRingHom x = e x := by
    exact (congrArg (fun f : B →+* B => f x)
      (RingEquiv.toRingHom_eq_coe e.toRingEquiv)).trans
        ((congrFun (RingEquiv.coe_toRingHom e.toRingEquiv) x).trans
          (congrFun (AlgEquiv.coe_toRingEquiv e) x))
  letI : IsLocalHom σ.toRingHom :=
    { map_nonunit x hx := by
        have h := hx.map σ.symm.toRingHom
        have hval : σ.symm.toRingHom (σ.toRingHom x) = x :=
          (ring_apply σ.symm (σ.toRingHom x)).trans
            ((congrArg σ.symm (ring_apply σ x)).trans (σ.symm_apply_apply x))
        exact Eq.mp (congrArg IsUnit hval) h }
  have hmaps : σ.toAlgHom.comp S.val = S.val := by
    apply etale_maps_eq_of_same_residue
    intro s
    obtain ⟨a, ha⟩ := residue_surjective (R := R) (δ s)
    have hdiff : (s : B) - algebraMap R B a ∈ maximalIdeal B := by
      rw [← residue_eq_zero_iff, map_sub, hδ s, ← ha,
        ResidueField.map_residue, sub_self]
    have hσdiff : σ (s : B) - algebraMap R B a ∈ maximalIdeal B := by
      have h := _root_.map_nonunit σ.toRingHom ((s : B) - algebraMap R B a) hdiff
      have hval : σ.toRingHom ((s : B) - algebraMap R B a) =
          σ (s : B) - algebraMap R B a := by
        calc
          σ.toRingHom ((s : B) - algebraMap R B a) =
              σ.toRingHom (s : B) - σ.toRingHom (algebraMap R B a) := σ.toRingHom.map_sub _ _
          _ = σ (s : B) - σ (algebraMap R B a) :=
            congrArg₂ (· - ·) (ring_apply σ (s : B)) (ring_apply σ (algebraMap R B a))
          _ = σ (s : B) - algebraMap R B a :=
            congrArg (fun z : B => σ (s : B) - z) (σ.commutes a)
      exact Eq.mp (congrArg (fun z : B => z ∈ maximalIdeal B) hval) h
    have hsmall : σ (s : B) - (s : B) ∈ maximalIdeal B := by
      have h := (maximalIdeal B).sub_mem hσdiff hdiff
      rw [_root_.sub_sub_sub_cancel_right] at h
      exact h
    have hval : (σ.toAlgHom.comp S.val) s - S.val s = σ (s : B) - (s : B) := by
      exact congrArg (fun z : B => z - (s : B)) (AlgEquiv.toAlgHom_apply σ (s : B))
    exact Eq.mpr (congrArg (fun z : B => z ∈ maximalIdeal B) hval) hsmall
  exact fun s => AlgHom.congr_fun hmaps s

end RationalStages

/-- The actual directed union of etale subalgebras is their small
    filtered colimit in the original commutative-algebra category. -/
private theorem directed_union_ind_etale
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (P : Subalgebra R B → Prop)
    [Nonempty {S : Subalgebra R B // P S}]
    (hdir : Directed (· ≤ ·) (fun i : {S : Subalgebra R B // P S} => i.1))
    (hEtale : ∀ i : {S : Subalgebra R B // P S}, Algebra.Etale R i.1) :
    (CommAlgCat.etale.{u} R).ind.{u}
      (CommAlgCat.of R (⨆ i : {S : Subalgebra R B // P S}, i.1 : Subalgebra R B)) := by
  classical
  let J := {S : Subalgebra R B // P S}
  let K : J → Subalgebra R B := fun i => i.1
  let X : Subalgebra R B := ⨆ i : J, K i
  letI : IsDirectedOrder J := ⟨hdir⟩
  letI : CategoryTheory.IsFiltered J := inferInstance
  let D : J ⥤ CommAlgCat.{u} R :=
    { obj i := CommAlgCat.of R (K i)
      map {i j} f := CommAlgCat.ofHom (Subalgebra.inclusion (leOfHom f))
      map_id i := by
        apply CommAlgCat.hom_ext
        apply AlgHom.ext
        intro x
        rfl
      map_comp f g := by
        apply CommAlgCat.hom_ext
        apply AlgHom.ext
        intro x
        rfl }
  let ι : D ⟶ (CategoryTheory.Functor.const J).obj (CommAlgCat.of R X) :=
    { app i := CommAlgCat.ofHom (Subalgebra.inclusion (le_iSup K i))
      naturality {i j} f := by
        apply CommAlgCat.hom_ext
        apply AlgHom.ext
        intro x
        rfl }
  let c₀ : CategoryTheory.Limits.Cocone D := { pt := CommAlgCat.of R X, ι := ι }
  let stageMap (c : CategoryTheory.Limits.Cocone D) (i : J) : K i →ₐ[R] c.pt :=
    { toFun := (c.ι.app i).hom
      map_zero' := _root_.map_zero (c.ι.app i).hom
      map_one' := _root_.map_one (c.ι.app i).hom
      map_add' x y := _root_.map_add (c.ι.app i).hom x y
      map_mul' x y := _root_.map_mul (c.ι.app i).hom x y
      commutes' r := (c.ι.app i).hom.commutes r }
  have compat (c : CategoryTheory.Limits.Cocone D) :
      ∀ (i j : J) (h : K i ≤ K j),
        stageMap c i = (stageMap c j).comp (Subalgebra.inclusion h) := by
    intro i j h
    have hn : D.map (homOfLE h : i ⟶ j) ≫ c.ι.app j = c.ι.app i := by
      exact (c.ι.naturality (homOfLE h : i ⟶ j)).trans
        (CategoryTheory.Category.comp_id (c.ι.app i))
    apply AlgHom.ext
    intro x
    have hh := congrArg (fun f : D.obj i ⟶ c.pt => f.hom x) hn
    exact hh.symm
  let desc (c : CategoryTheory.Limits.Cocone D) : X →ₐ[R] c.pt :=
    Subalgebra.iSupLift K hdir (stageMap c) (compat c) X le_rfl
  have desc_apply (c : CategoryTheory.Limits.Cocone D) (i : J) (y : K i) :
      desc c (Subalgebra.inclusion (le_iSup K i) y) = (c.ι.app i).hom y := by
    exact Subalgebra.iSupLift_inclusion
      (R := R) (A := B) (B := c.pt)
      (K := K) (dir := hdir) (f := stageMap c)
      (hf := compat c) (T := X) (hT := le_rfl) y (le_iSup K i)
  have hc : CategoryTheory.Limits.IsColimit c₀ :=
    { desc c := CommAlgCat.ofHom (desc c)
      fac c i := by
        apply CommAlgCat.hom_ext
        apply AlgHom.ext
        intro y
        exact desc_apply c i y
      uniq c m hm := by
        apply CommAlgCat.hom_ext
        apply AlgHom.ext
        intro x
        have hx : (x : B) ∈ X := x.2
        change (x : B) ∈ (⨆ i : J, K i : Subalgebra R B) at hx
        rw [← SetLike.mem_coe, Subalgebra.coe_iSup_of_directed hdir, Set.mem_iUnion] at hx
        obtain ⟨i, hxi⟩ := hx
        let y : K i := ⟨(x : B), hxi⟩
        have hy : Subalgebra.inclusion (le_iSup K i) y = x := Subtype.ext rfl
        have hmap := congrArg (fun f : D.obj i ⟶ c.pt => f.hom y) (hm i)
        change m.hom (Subalgebra.inclusion (le_iSup K i) y) = (c.ι.app i).hom y at hmap
        calc
          m.hom x = m.hom (Subalgebra.inclusion (le_iSup K i) y) := by rw [hy]
          _ = (c.ι.app i).hom y := hmap
          _ = desc c (Subalgebra.inclusion (le_iSup K i) y) := (desc_apply c i y).symm
          _ = desc c x := by rw [hy] }
  let pres : CategoryTheory.Limits.ColimitPresentation J (CommAlgCat.of R X) :=
    { diag := D, ι := ι, isColimit := hc }
  exact ⟨J, inferInstance, inferInstance, pres, hEtale⟩

/-- Every finite set in the actual directed union belongs to one actual stage. -/
private theorem finite_set_in_one_stage
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (P : Subalgebra R B → Prop)
    [Nonempty {S : Subalgebra R B // P S}]
    (hdir : Directed (· ≤ ·) (fun i : {S : Subalgebra R B // P S} => i.1))
    (t : Finset B)
    (ht : ∀ x ∈ t, x ∈ (⨆ i : {S : Subalgebra R B // P S}, i.1 : Subalgebra R B)) :
    ∃ i : {S : Subalgebra R B // P S}, ∀ x ∈ t, x ∈ i.1 := by
  classical
  revert ht
  induction t using Finset.induction_on with
  | empty =>
      intro ht
      exact ⟨Classical.choice inferInstance, by simp⟩
  | @insert x t hxt ih =>
      intro ht
      have hx : x ∈ (⨆ i : {S : Subalgebra R B // P S}, i.1 : Subalgebra R B) := ht x (Finset.mem_insert_self _ _)
      rw [← SetLike.mem_coe, Subalgebra.coe_iSup_of_directed hdir, Set.mem_iUnion] at hx
      obtain ⟨i, hxi⟩ := hx
      obtain ⟨j, hj⟩ := ih (fun y hy => ht y (Finset.mem_insert_of_mem hy))
      obtain ⟨k, hik, hjk⟩ := hdir i j
      refine ⟨k, fun y hy => ?_⟩
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hik hxi
      · exact hjk (hj y hy)

/-- The original monic polynomial and the original residue representative
    lift together to one genuine stage of the directed union. -/
private theorem monic_polynomial_in_one_stage
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (P : Subalgebra R B → Prop)
    [Nonempty {S : Subalgebra R B // P S}]
    (hdir : Directed (· ≤ ·) (fun i : {S : Subalgebra R B // P S} => i.1))
    (p : Polynomial (⨆ i : {S : Subalgebra R B // P S}, i.1 : Subalgebra R B)) (hp : p.Monic)
    (a₀ : (⨆ i : {S : Subalgebra R B // P S}, i.1 : Subalgebra R B)) :
    ∃ (i : {S : Subalgebra R B // P S}) (a : i.1) (q : Polynomial i.1),
      q.Monic ∧
      Subalgebra.inclusion (le_iSup (fun i : {S : Subalgebra R B // P S} => i.1) i) a = a₀ ∧
      q.map (Subalgebra.inclusion
        (le_iSup (fun i : {S : Subalgebra R B // P S} => i.1) i)).toRingHom = p := by
  classical
  let J := {S : Subalgebra R B // P S}
  let K : J → Subalgebra R B := fun i => i.1
  let X : Subalgebra R B := ⨆ i : J, K i
  let t : Finset B := insert (a₀ : B) ((Finset.range p.natDegree).image fun n => (p.coeff n : B))
  have ht : ∀ x ∈ t, x ∈ X := by
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · rw [h]
      exact a₀.2
    · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp h
      exact (p.coeff n).2
  obtain ⟨i, hi⟩ := finite_set_in_one_stage P hdir t ht
  have ha₀ : (a₀ : B) ∈ K i := hi _ (Finset.mem_insert_self _ _)
  have hcoeff : ∀ n ∈ Finset.range p.natDegree, (p.coeff n : B) ∈ K i := by
    intro n hn
    exact hi _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨n, hn, rfl⟩))
  let a : K i := ⟨(a₀ : B), ha₀⟩
  let inc : K i →ₐ[R] X := Subalgebra.inclusion (le_iSup K i)
  let q : Polynomial (K i) := Polynomial.X ^ p.natDegree +
    ∑ n ∈ (Finset.range p.natDegree).attach,
      C (⟨(p.coeff n.1 : B), hcoeff n.1 n.2⟩ : K i) * Polynomial.X ^ n.1
  have hval (n : {n // n ∈ Finset.range p.natDegree}) :
      inc (⟨(p.coeff n.1 : B), hcoeff n.1 n.2⟩ : K i) = p.coeff n.1 := Subtype.ext rfl
  have hvalRing (n : {n // n ∈ Finset.range p.natDegree}) :
      inc.toRingHom (⟨(p.coeff n.1 : B), hcoeff n.1 n.2⟩ : K i) = p.coeff n.1 := by
    exact hval n
  have hmap : q.map inc.toRingHom = p := by
    simp only [q, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, hvalRing]
    rw [Finset.sum_attach (Finset.range p.natDegree)
      (fun n => Polynomial.C (p.coeff n) * Polynomial.X ^ n)]
    exact hp.as_sum.symm
  have hinj : Function.Injective inc := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : X => (z : B)) h
  have hinjRing : Function.Injective inc.toRingHom := hinj
  have hq : q.Monic := (hinjRing.monic_map_iff (p := q)).mpr (hmap.symm ▸ hp)
  exact ⟨i, a, q, hq, Subtype.ext rfl, hmap⟩

/-- Simple roots over the original residue point are obtained in a genuine
    standard-etale stage and then carried into the same directed union. -/
private theorem henselian_rational_union
    {R B : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing B] [IsDomain B] [HenselianLocalRing B]
    [Algebra R B] [IsLocalHom (algebraMap R B)]
    (hRB : Function.Injective (algebraMap R B))
    [Nonempty {S : Subalgebra R B // RationalStage S}]
    (hdir : Directed (· ≤ ·) (fun i : {S : Subalgebra R B // RationalStage S} => i.1))
    (hlocal : IsLocalHom
      (⨆ i : {S : Subalgebra R B // RationalStage S}, i.1 : Subalgebra R B).val.toRingHom) :
    HenselianLocalRing (⨆ i : {S : Subalgebra R B // RationalStage S}, i.1 : Subalgebra R B) := by
  classical
  let J := {S : Subalgebra R B // RationalStage S}
  let K : J → Subalgebra R B := fun i => i.1
  let X : Subalgebra R B := ⨆ i : J, K i
  letI : IsLocalHom X.val.toRingHom := hlocal
  letI : IsLocalRing X := X.val.toRingHom.domain_isLocalRing
  refine { toIsLocalRing := inferInstance, is_henselian := ?_ }
  intro p hp a₀ hp₀ hder
  obtain ⟨i, a, q, hq, ha, hmap⟩ :=
    monic_polynomial_in_one_stage (RationalStage (R := R) (B := B)) hdir p hp a₀
  let S := K i
  let inc : S →ₐ[R] X := Subalgebra.inclusion (le_iSup K i)
  letI : Algebra.Etale R S := i.2.1
  obtain ⟨δ, hδ⟩ := i.2.2.2
  have incRing (x : S) : inc.toRingHom x = inc x := by
    exact (congrArg (fun f : S →+* X => f x) (AlgHom.toRingHom_eq_coe inc)).trans
      (congrFun (AlgHom.coe_toRingHom inc) x)
  have eval_inc (t : Polynomial S) (b : S) :
      (t.map inc.toRingHom).eval (inc b) = inc (t.eval b) := by
    exact (congrArg (fun x : X => (t.map inc.toRingHom).eval x) (incRing b).symm).trans
      ((Polynomial.eval_map_apply (p := t) (f := inc.toRingHom) b).trans (incRing (t.eval b)))
  have heval : inc (q.eval a) = p.eval a₀ := by
    calc
      inc (q.eval a) = (q.map inc.toRingHom).eval (inc a) := (eval_inc q a).symm
      _ = p.eval (inc a) := congrArg (fun t : Polynomial X => t.eval (inc a)) hmap
      _ = p.eval a₀ := congrArg p.eval ha
  have hmapder : q.derivative.map inc.toRingHom = p.derivative := by
    rw [← derivative_map, hmap]
  have hdeval : inc (q.derivative.eval a) = p.derivative.eval a₀ := by
    calc
      inc (q.derivative.eval a) = (q.derivative.map inc.toRingHom).eval (inc a) :=
        (eval_inc q.derivative a).symm
      _ = p.derivative.eval (inc a) :=
        congrArg (fun t : Polynomial X => t.eval (inc a)) hmapder
      _ = p.derivative.eval a₀ := congrArg p.derivative.eval ha
  have hqB : ((q.eval a : S) : B) ∈ maximalIdeal B := by
    have h := _root_.map_nonunit X.val.toRingHom (p.eval a₀) hp₀
    rw [← heval] at h
    exact h
  have hqδ : δ (q.eval a) = 0 := by
    apply (ResidueField.map (algebraMap R B)).injective
    rw [map_zero, ← hδ (q.eval a)]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hqB
  have hderB : IsUnit ((q.derivative.eval a : S) : B) := by
    have h := hder.map X.val.toRingHom
    rw [← hdeval] at h
    exact h
  have hderδ : IsUnit (δ (q.derivative.eval a)) := by
    apply isUnit_iff_ne_zero.mpr
    intro hzero
    have hz : residue B ((q.derivative.eval a : S) : B) = 0 := by
      rw [hδ (q.derivative.eval a), hzero, map_zero]
    exact (hderB.map (residue B)).ne_zero hz
  letI : Algebra S (ResidueField R) := δ.toRingHom.toAlgebra
  letI : IsScalarTower R S (ResidueField R) :=
    IsScalarTower.of_algebraMap_eq fun r => (δ.commutes r).symm
  let P : StandardEtalePair S :=
    { f := q, monic_f := hq, g := q.derivative,
      cond := ⟨1, 0, 1, by simp⟩ }
  have hPa : P.HasMap (δ a) := by
    constructor
    · change aeval (algebraMap S (ResidueField R) a) q = 0
      rw [aeval_algebraMap_apply_eq_algebraMap_eval]
      exact hqδ
    · change IsUnit (aeval (algebraMap S (ResidueField R) a) q.derivative)
      rw [aeval_algebraMap_apply_eq_algebraMap_eval]
      exact hderδ
  let A := P.Ring
  letI : Algebra R A := ((algebraMap S A).comp (algebraMap R S)).toAlgebra
  letI : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra.Etale R A := Algebra.Etale.comp R S A
  let δA : A →ₐ[R] ResidueField R := (P.lift (δ a) hPa).restrictScalars R
  obtain ⟨g, hg⟩ := lift_point_to_henselian_target (R := R) (B := B) A δA
  have hgbase : g.comp (IsScalarTower.toAlgHom R S A) = S.val := by
    apply etale_maps_eq_of_same_residue
    intro s
    have hδbase : δA (algebraMap S A s) = δ s := by
      exact (P.lift (δ a) hPa).commutes s
    have hgpoint : residue B (g (algebraMap S A s)) =
        ResidueField.map (algebraMap R B) (δ s) := by
      rw [hg, hδbase]
    rw [← residue_eq_zero_iff, map_sub]
    change residue B (g (algebraMap S A s)) - residue B (s : B) = 0
    rw [hgpoint, ← hδ s, sub_self]
  let gS : A →ₐ[S] B :=
    { toRingHom := g.toRingHom
      commutes' s := AlgHom.congr_fun hgbase s }
  have hrootB : (q.map S.val.toRingHom).IsRoot (g P.X) := by
    have h := (P.hasMap_X.map gS).1
    change q.eval₂ S.val.toRingHom (g P.X) = 0 at h
    simpa only [IsRoot, Polynomial.eval_map] using h
  obtain ⟨T, hT, ψ, hψ⟩ := rational_stage_of_pointed_etale hRB A δA g hg
  let j : J := ⟨T, hT⟩
  have hxT : g P.X ∈ T := by
    rw [← hψ P.X]
    exact (ψ P.X).2
  have hxX : g P.X ∈ X := (le_iSup K j) hxT
  let x : X := ⟨g P.X, hxX⟩
  have hpoly : p.map X.val.toRingHom = q.map S.val.toRingHom := by
    have hcomp : X.val.toRingHom.comp inc.toRingHom = S.val.toRingHom :=
      RingHom.ext (fun s => rfl)
    calc
      p.map X.val.toRingHom = (q.map inc.toRingHom).map X.val.toRingHom :=
        congrArg (fun f : Polynomial X => f.map X.val.toRingHom) hmap.symm
      _ = q.map (X.val.toRingHom.comp inc.toRingHom) := by rw [Polynomial.map_map]
      _ = q.map S.val.toRingHom := congrArg (fun f : S →+* B => q.map f) hcomp
  have hroot : p.IsRoot x := by
    have hval : X.val.toRingHom (p.eval x) = 0 := by
      rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
      change (p.map X.val.toRingHom).eval (g P.X) = 0
      rw [hpoly]
      exact hrootB
    exact (map_eq_zero_iff _ Subtype.val_injective).mp hval
  have hδX : δA P.X = δ a := StandardEtalePair.lift_X P (δ a) hPa
  have haval : (a : B) = (a₀ : B) := congrArg (fun z : X => (z : B)) ha
  have hdiffB : X.val.toRingHom (x - a₀) ∈ maximalIdeal B := by
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    rw [map_sub, map_sub]
    change residue B (g P.X) - residue B (a₀ : B) = 0
    rw [hg P.X, hδX, ← hδ a, haval, sub_self]
  have hdiff : x - a₀ ∈ maximalIdeal X := by
    change ¬ IsUnit (x - a₀)
    intro hu
    exact hdiffB (hu.map X.val.toRingHom)
  exact ⟨x, hroot, hdiff⟩

/-- The actual rational-stage union is a henselian DVR, with the original
    residue field, actual local embedding, and invariance under base automorphisms. -/
private theorem exists_rational_henselian_dvr
    {R B : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing B] [IsDomain B] [HenselianLocalRing B]
    [Algebra R B] [IsLocalHom (algebraMap R B)]
    (hRB : Function.Injective (algebraMap R B)) :
    ∃ (Rh : Type u) (cr : CommRing Rh),
      letI := cr
      ∃ dom : IsDomain Rh,
        letI := dom
        ∃ dvr : IsDiscreteValuationRing Rh,
          letI := dvr
          ∃ alg : Algebra R Rh,
            letI := alg
            HenselianLocalRing Rh ∧
            (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R Rh) ∧
            ∃ e : ResidueField R ≃+* ResidueField Rh,
              (∀ r : R, e (residue R r) = residue Rh (algebraMap R Rh r)) ∧
              ∃ f : Rh →+* B, IsLocalHom f ∧ Function.Injective f ∧
                f.comp (algebraMap R Rh) = algebraMap R B ∧
                ∀ σ : B ≃ₐ[R] B, ∀ r : Rh, σ (f r) = f r := by
  classical
  let J := {S : Subalgebra R B // RationalStage S}
  let K : J → Subalgebra R B := fun i => i.1
  let X : Subalgebra R B := ⨆ i : J, K i
  letI : Nonempty J := rational_stage_nonempty hRB
  have hdir : Directed (· ≤ ·) K := rational_stage_directed hRB
  have represent (x : X) : ∃ i : J, (x : B) ∈ K i := by
    have hx : (x : B) ∈ X := x.2
    rw [← SetLike.mem_coe, Subalgebra.coe_iSup_of_directed hdir, Set.mem_iUnion] at hx
    exact hx
  have hlocal : IsLocalHom X.val.toRingHom :=
    { map_nonunit x hx := by
        obtain ⟨i, hxi⟩ := represent x
        let y : K i := ⟨(x : B), hxi⟩
        letI : IsLocalHom (K i).val.toRingHom := i.2.2.1
        have hy : IsUnit y := isUnit_of_map_unit (K i).val.toRingHom y hx
        let inc : K i →ₐ[R] X := Subalgebra.inclusion (le_iSup K i)
        have heq : inc y = x := Subtype.ext rfl
        have hmap : IsUnit (inc y) := hy.map inc.toRingHom
        simpa only [heq] using hmap }
  letI : IsLocalHom X.val.toRingHom := hlocal
  letI : IsLocalRing X := X.val.toRingHom.domain_isLocalRing
  have hcoeff : X.val.toRingHom.comp (algebraMap R X) = algebraMap R B := by
    apply RingHom.ext
    intro r
    rfl
  letI : IsLocalHom (X.val.toRingHom.comp (algebraMap R X)) := by
    rw [hcoeff]
    infer_instance
  letI : IsLocalHom (algebraMap R X) := isLocalHom_of_comp (algebraMap R X) X.val.toRingHom
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have stage_uniformizer (i : J) :
      ∃ dvr : IsDiscreteValuationRing (K i),
        letI := dvr
        Irreducible (algebraMap R (K i) ϖ) ∧
          maximalIdeal (K i) = Ideal.span {algebraMap R (K i) ϖ} := by
    letI : Algebra.Etale R (K i) := i.2.1
    letI : IsLocalHom (K i).val.toRingHom := i.2.2.1
    letI : IsLocalRing (K i) := (K i).val.toRingHom.domain_isLocalRing
    have hcomp : (K i).val.toRingHom.comp (algebraMap R (K i)) = algebraMap R B := by
      apply RingHom.ext
      intro r
      rfl
    letI : IsLocalHom ((K i).val.toRingHom.comp (algebraMap R (K i))) := by
      rw [hcomp]
      infer_instance
    letI : IsLocalHom (algebraMap R (K i)) :=
      isLocalHom_of_comp (algebraMap R (K i)) (K i).val.toRingHom
    obtain ⟨_, hdvr, hirr, hmax⟩ :=
      Port.IsDiscreteValuationRing.of_formallyUnramified (A := R) (S := K i) hϖ
    exact ⟨hdvr, hirr, hmax⟩
  let τ : X := algebraMap R X ϖ
  have hτ0 : τ ≠ 0 := by
    intro hzero
    have h := congrArg (fun x : X => (x : B)) hzero
    change algebraMap R B ϖ = 0 at h
    apply hϖ.ne_zero
    apply hRB
    simpa only [map_zero] using h
  have hτnu : ¬ IsUnit τ := by
    intro hu
    exact hϖ.not_isUnit (isUnit_of_map_unit (algebraMap R X) ϖ hu)
  have hmax : maximalIdeal X = Ideal.span {τ} := by
    apply le_antisymm
    · intro x hx
      obtain ⟨i, hxi⟩ := represent x
      let y : K i := ⟨(x : B), hxi⟩
      let inc : K i →ₐ[R] X := Subalgebra.inclusion (le_iSup K i)
      have heq : inc y = x := Subtype.ext rfl
      obtain ⟨hdvr, hirr, hmaxi⟩ := stage_uniformizer i
      letI := hdvr
      have hynu : ¬ IsUnit y := by
        intro hu
        have hux : IsUnit x := by rw [← heq]; exact hu.map inc.toRingHom
        exact hx hux
      have hymem : y ∈ maximalIdeal (K i) := hynu
      rw [hmaxi, Ideal.mem_span_singleton] at hymem
      obtain ⟨c, hc⟩ := hymem
      apply Ideal.mem_span_singleton.mpr
      refine ⟨inc c, ?_⟩
      rw [← heq, hc, map_mul, inc.commutes]
      all_goals rfl
    · apply Ideal.span_le.mpr
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact hτnu
  have hprime : Prime τ :=
    (Ideal.span_singleton_prime hτ0).mp (by rw [← hmax]; infer_instance)
  have hfactor : IsDiscreteValuationRing.HasUnitMulPowIrreducibleFactorization X := by
    refine ⟨τ, hprime.irreducible, ?_⟩
    intro x hx
    obtain ⟨i, hxi⟩ := represent x
    let y : K i := ⟨(x : B), hxi⟩
    let inc : K i →ₐ[R] X := Subalgebra.inclusion (le_iSup K i)
    have heq : inc y = x := Subtype.ext rfl
    have hy0 : y ≠ 0 := by
      intro hzero
      apply hx
      rw [← heq, hzero, map_zero]
    obtain ⟨hdvr, hirr, hmaxi⟩ := stage_uniformizer i
    letI := hdvr
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hirr
    have hxeq : x = inc (u : K i) * τ ^ n := by
      rw [← heq, hu, map_mul, map_pow, inc.commutes]
      all_goals rfl
    refine ⟨n, ⟨Units.map inc.toRingHom.toMonoidHom u, ?_⟩⟩
    change τ ^ n * inc (u : K i) = x
    rw [hxeq, mul_comm]
  letI hdvrX : IsDiscreteValuationRing X :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization hfactor
  have hhen : HenselianLocalRing X := henselian_rational_union hRB hdir hlocal
  have hind : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R X) :=
    directed_union_ind_etale (RationalStage (R := R) (B := B)) hdir (fun i => i.2.1)
  let κX : ResidueField R →+* ResidueField X := ResidueField.map (algebraMap R X)
  have hκsurj : Function.Surjective κX := by
    intro z
    obtain ⟨x, hx⟩ := residue_surjective (R := X) z
    obtain ⟨i, hxi⟩ := represent x
    let y : K i := ⟨(x : B), hxi⟩
    obtain ⟨δ, hδ⟩ := i.2.2.2
    obtain ⟨a, ha⟩ := residue_surjective (R := R) (δ y)
    refine ⟨residue R a, ?_⟩
    rw [← hx]
    apply (ResidueField.map X.val.toRingHom).injective
    change (ResidueField.map X.val.toRingHom)
        ((ResidueField.map (algebraMap R X)) (residue R a)) =
      (ResidueField.map X.val.toRingHom) (residue X x)
    simp only [ResidueField.map_residue]
    change residue B (algebraMap R B a) = residue B (y : B)
    rw [hδ y, ← ha, ResidueField.map_residue]
  let e : ResidueField R ≃+* ResidueField X := RingEquiv.ofBijective κX ⟨κX.injective, hκsurj⟩
  have he : ∀ r : R, e (residue R r) = residue X (algebraMap R X r) :=
    fun r => ResidueField.map_residue (algebraMap R X) r
  have hfix : ∀ σ : B ≃ₐ[R] B, ∀ x : X, σ (x : B) = (x : B) := by
    intro σ x
    obtain ⟨i, hxi⟩ := represent x
    let y : K i := ⟨(x : B), hxi⟩
    exact rational_stage_fixed (K i) i.2 σ y
  exact ⟨X, inferInstance, inferInstance, hdvrX, inferInstance,
    hhen, hind, e, he, X.val.toRingHom, hlocal, Subtype.val_injective, hcoeff, hfix⟩

end ZInQ.Contrib.CloudR2Raynaud.StrictHenselization.Ordinary.Construction

namespace ZInQ.Contrib.CloudR2Raynaud.StrictHenselization.Ordinary

open IsLocalRing CategoryTheory

/-- Construct the ordinary henselian DVR over the original valuation ring,
    inside the original target valuation ring. The structural dictionaries
    are returned in the order CommRing, IsDomain, DVR, Algebra. -/
theorem exists_ordinaryDVR_toW
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O) :
    ∃ (Rh : Type u) (cr : CommRing Rh),
      letI := cr
      ∃ dom : IsDomain Rh,
        letI := dom
        ∃ dvr : IsDiscreteValuationRing Rh,
          letI := dvr
          ∃ alg : Algebra O Rh,
            letI := alg
            HenselianLocalRing Rh ∧
            (CommAlgCat.etale.{u} O).ind.{u} (CommAlgCat.of O Rh) ∧
            ∃ e : ResidueField O ≃+* ResidueField Rh,
              (∀ r : O, e (residue O r) = residue Rh (algebraMap O Rh r)) ∧
              ∃ f : Rh →+* w, IsLocalHom f ∧ Function.Injective f ∧
                f.comp (algebraMap O Rh) = comapHom hw ∧
                ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ w.decompositionSubgroup K →
                  ∀ r : Rh, σ (f r : Ω) = (f r : Ω) := by
  letI : Algebra O w := (comapHom hw).toAlgebra
  letI : IsLocalHom (algebraMap O w) := by
    change IsLocalHom (comapHom hw)
    infer_instance
  letI : HenselianLocalRing w := Construction.ambient_henselian w
  have hOw : Function.Injective (algebraMap O w) := by
    intro r s h
    apply Subtype.ext
    apply (algebraMap K Ω).injective
    have hval := congrArg (fun x : w => (x : Ω)) h
    change algebraMap K Ω (r : K) = algebraMap K Ω (s : K) at hval
    exact hval
  obtain ⟨Rh, cr, dom, dvr, alg, hhen, hind, e, he, f, hfloc, hfinj, hfO, hfixed⟩ :=
    Construction.exists_rational_henselian_dvr (R := O) (B := w) hOw
  letI := cr
  letI := dom
  letI := dvr
  letI := alg
  have hfix : ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ w.decompositionSubgroup K →
      ∀ r : Rh, σ (f r : Ω) = (f r : Ω) := by
    intro σ hσ r
    let τ : w.decompositionSubgroup K := ⟨σ, hσ⟩
    let ρ : w ≃ₐ[O] w :=
      { toRingEquiv := MulSemiringAction.toRingAut (w.decompositionSubgroup K) w τ
        commutes' a := by
          apply Subtype.ext
          change σ (algebraMap K Ω (a : K)) = algebraMap K Ω (a : K)
          exact σ.commutes (a : K) }
    have h := hfixed ρ r
    exact congrArg (fun x : w => (x : Ω)) h
  exact ⟨Rh, cr, dom, dvr, alg, hhen, hind, e, he, f, hfloc, hfinj, hfO, hfix⟩

end ZInQ.Contrib.CloudR2Raynaud.StrictHenselization.Ordinary
