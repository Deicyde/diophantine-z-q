import Mathlib

/-!
# Leaf T1 (Zariski–Nagata purity, `PkgI2.PurityBranchLocus`): the dimension-one case is glue

`PurityBranchLocus` is copied verbatim from `ZInQKernel/HDecomp/Objects.lean` (§B, `PkgI2`).
We prove its dimension-one case, so the leaf reduces to `PurityBranchLocusGe2` (the same statement
with the extra hypothesis `2 ≤ dim S_q`), a consequence of the published statement.

Dimension one: `R_p` regular local of dimension 1, `S_q` a domain of dimension 1, `R → S`
unramified at `q` (which has height 1).  Quasi-finiteness at `q` forces `R_p → S_q` injective
(else `(0)` and `qS_q` would be two comparable primes of `S_q` over `p`), Nakayama then shows
`R_p` is a domain, hence a DVR, so the torsion-free `S_q` is flat over it, and
`TPurity2.isEtaleAt_of_isUnramifiedAt_of_flat_local` (copied from `EtaleLocal.lean`) concludes.
-/

open IsLocalRing TensorProduct

universe u

namespace PkgI2

/-- Copied verbatim from `ZInQKernel/HDecomp/Objects.lean`. -/
def PurityBranchLocus : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime],
    IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap R S))) →
    IsDomain (Localization.AtPrime q) →
    IsIntegrallyClosed (Localization.AtPrime q) →
    Algebra.QuasiFiniteAt R q →
    ringKrullDim (Localization.AtPrime q) =
      ringKrullDim (Localization.AtPrime (q.comap (algebraMap R S))) →
    1 ≤ ringKrullDim (Localization.AtPrime q) →
    (∀ (q' : Ideal S) [q'.IsPrime], q' ≤ q → q'.height = 1 → Algebra.IsUnramifiedAt R q') →
    Algebra.IsEtaleAt R q

end PkgI2

namespace TPurity2

local notation "𝓀[" R "]" => ResidueField R

/-- Copied from `EtaleLocal.lean` (scratch files cannot import each other). -/
theorem isEtaleAt_of_isUnramifiedAt_of_flat_local {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FinitePresentation R S] (p : Ideal R) [p.IsPrime] (q : Ideal S)
    [q.IsPrime] [q.LiesOver p] [Algebra.IsUnramifiedAt R q]
    (hflat : letI := Localization.AtPrime.algebraOfLiesOver p q;
      Module.Flat (Localization.AtPrime p) (Localization.AtPrime q)) :
    Algebra.IsEtaleAt R q := by
  let Rp := Localization.AtPrime p
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let Sq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  let f : Sp →ₐ[S] Sq := IsLocalization.liftAlgHom
      (M := Algebra.algebraMapSubmonoid S p.primeCompl)
        (f := Algebra.ofId _ _) (by
      rintro ⟨_, x, hx, rfl⟩
      simpa using! IsLocalization.map_units (M := q.primeCompl) Sq ⟨algebraMap _ _ x,
        by simp_all [q.over_def p]⟩)
  algebraize [f.toRingHom]
  have : IsScalarTower R Sp Sq := .to₁₃₄ _ S _ _
  have : IsScalarTower Rp Sp Sq := .of_algebraMap_eq' <| by
    apply IsLocalization.ringHom_ext p.primeCompl
    simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  have : IsLocalization (Algebra.algebraMapSubmonoid Sp q.primeCompl) Sq :=
    .isLocalization_of_submonoid_le _ _ (Algebra.algebraMapSubmonoid S p.primeCompl) _
    (by rintro _ ⟨x, hx, rfl⟩; simp_all [q.over_def p])
  have : Algebra.FinitePresentation Rp Sp := by
    have : Algebra.IsPushout R Rp S Sp :=
      .symm <| Algebra.isPushout_of_isLocalization p.primeCompl _ _ _
    exact .equiv (Algebra.IsPushout.equiv R Rp S Sp)
  have : Module.Flat Rp Sq := hflat
  have hU : Algebra.FormallyUnramified R Sq := ‹_›
  have : Algebra.FormallyUnramified Rp Sq := .of_restrictScalars R Rp Sq
  have : IsLocalHom (algebraMap Rp Sq) := by
    rw [Localization.AtPrime.algebraMap_eq p q]
    infer_instance
  have : Algebra.EssFiniteType R Sq := .comp R S Sq
  have : Algebra.EssFiniteType Rp Sq := .of_comp R Rp Sq
  have : Algebra.FormallyEtale 𝓀[Rp] (𝓀[Rp] ⊗[Rp] Sq) :=
    .of_formallyUnramified_of_field _ _
  have : Algebra.FormallySmooth Rp Sq :=
    Algebra.FormallySmooth.of_formallySmooth_residueField_tensor (R := Rp) (S := Sq) (P := Sp)
      (Algebra.algebraMapSubmonoid _ q.primeCompl)
  have : Algebra.FormallySmooth R Sq := .comp R Rp Sq
  exact Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨hU, ‹_›⟩

/-- A Noetherian local ring with principal maximal ideal: a prime `P ≠ 𝔪` is `⊥` (Nakayama). -/
theorem eq_bot_of_isPrime_of_ne_maximalIdeal {A : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (hm : (maximalIdeal A).IsPrincipal) (P : Ideal A) [hP : P.IsPrime]
    (hne : P ≠ maximalIdeal A) : P = ⊥ := by
  obtain ⟨x, hx⟩ := hm
  have hxP : x ∉ P := by
    intro h
    apply hne
    refine le_antisymm (le_maximalIdeal hP.ne_top) ?_
    rw [hx, Submodule.span_le, Set.singleton_subset_iff]
    exact h
  have hle : P ≤ maximalIdeal A • P := by
    intro a ha
    have ham : a ∈ maximalIdeal A := le_maximalIdeal hP.ne_top ha
    rw [hx, Submodule.mem_span_singleton] at ham
    obtain ⟨c, rfl⟩ := ham
    have hc : c ∈ P := by
      rcases hP.mem_or_mem (show c * x ∈ P by simpa [smul_eq_mul] using ha) with h | h
      · exact h
      · exact absurd h hxP
    have hxm : x ∈ maximalIdeal A := hx ▸ Submodule.mem_span_singleton_self x
    rw [Ideal.smul_eq_mul, smul_eq_mul, mul_comm c x]
    exact Ideal.mul_mem_mul hxm hc
  exact Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal A) P
    (IsNoetherian.noetherian P) hle (by rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top])

/-- **T1, dimension one (GLUE, proved).** -/
theorem purity_dim_one (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime]
    (hreg : IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap R S))))
    (hdom : IsDomain (Localization.AtPrime q))
    (hqf : Algebra.QuasiFiniteAt R q)
    (hdim : ringKrullDim (Localization.AtPrime q) =
      ringKrullDim (Localization.AtPrime (q.comap (algebraMap R S))))
    (h1 : ringKrullDim (Localization.AtPrime q) = 1)
    (hunr : ∀ (q' : Ideal S) [q'.IsPrime], q' ≤ q → q'.height = 1 →
      Algebra.IsUnramifiedAt R q') :
    Algebra.IsEtaleAt R q := by
  set p : Ideal R := q.under R with hp
  have : Algebra.FinitePresentation R S := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have hq1 : q.height = 1 := by
    have := IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)
    rw [h1] at this
    exact_mod_cast this.symm
  have : Algebra.IsUnramifiedAt R q := hunr q le_rfl hq1
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  have hRp1 : ringKrullDim Rp = 1 := hdim.symm.trans h1
  have hreg' : IsRegularLocalRing Rp := hreg
  -- the maximal ideal of `R_p` is principal
  have hprin : (maximalIdeal Rp).IsPrincipal := by
    rw [← finrank_cotangentSpace_le_one_iff]
    have h := (IsRegularLocalRing.iff_finrank_cotangentSpace Rp).mp hreg'
    rw [hRp1] at h
    exact_mod_cast h.le
  -- `R_p → S_q` is injective
  let φ := algebraMap Rp Sq
  have hker : RingHom.ker φ = ⊥ := by
    have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
    refine eq_bot_of_isPrime_of_ne_maximalIdeal hprin _ fun hm => ?_
    -- otherwise `⊥` and the maximal ideal of `S_q` both lie over `p`
    have hqf' : Algebra.QuasiFinite R Sq := hqf
    have hbot : (⊥ : Ideal Sq).IsPrime := Ideal.isPrime_bot
    have key : (⊥ : Ideal Sq).under R = (maximalIdeal Sq).under R := by
      rw [← Ideal.under_under (B := S) (maximalIdeal Sq),
        Localization.AtPrime.under_maximalIdeal, ← Ideal.under_under (B := Rp) (⊥ : Ideal Sq)]
      have : (⊥ : Ideal Sq).under Rp = RingHom.ker φ := rfl
      rw [this, hm, Localization.AtPrime.under_maximalIdeal]
    have := Algebra.QuasiFinite.eq_of_le_of_under_eq (R := R) (⊥ : Ideal Sq) (maximalIdeal Sq)
      bot_le key
    have hfield : IsField Sq := IsLocalRing.isField_iff_maximalIdeal_eq.mpr this.symm
    have := ringKrullDim_eq_zero_of_isField hfield
    rw [this] at h1
    exact absurd h1 (by decide)
  have hinj : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).mpr hker
  have : IsDomain Rp := hinj.isDomain φ
  have hnf : ¬ IsField Rp := fun h => by
    rw [ringKrullDim_eq_zero_of_isField h] at hRp1
    exact absurd hRp1 (by decide)
  have : IsDedekindDomain Rp := ((IsDiscreteValuationRing.TFAE Rp hnf).out 5 3).mp hprin
  have : Module.IsTorsionFree Rp Sq := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r s hrs => ?_
    rw [Algebra.smul_def, mul_eq_zero] at hrs
    rcases hrs with h | h
    · exact Or.inl (hinj (by rw [h, map_zero]))
    · exact Or.inr h
  exact isEtaleAt_of_isUnramifiedAt_of_flat_local p q inferInstance

/-- The leaf restricted to dimension `≥ 2` (a consequence of the published statement). -/
def PurityBranchLocusGe2 : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime],
    IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap R S))) →
    IsDomain (Localization.AtPrime q) →
    IsIntegrallyClosed (Localization.AtPrime q) →
    Algebra.QuasiFiniteAt R q →
    ringKrullDim (Localization.AtPrime q) =
      ringKrullDim (Localization.AtPrime (q.comap (algebraMap R S))) →
    2 ≤ ringKrullDim (Localization.AtPrime q) →
    (∀ (q' : Ideal S) [q'.IsPrime], q' ≤ q → q'.height = 1 → Algebra.IsUnramifiedAt R q') →
    Algebra.IsEtaleAt R q

/-- **T1 reduces to dimension `≥ 2`.** -/
theorem purityBranchLocus_of_ge2 (h : PurityBranchLocusGe2.{u}) : PkgI2.PurityBranchLocus.{u} := by
  intro R S _ _ _ _ _ q _ hreg hdom hic hqf hdim h1 hunr
  by_cases h2 : 2 ≤ ringKrullDim (Localization.AtPrime q)
  · exact h R S q hreg hdom hic hqf hdim h2 hunr
  · have : ringKrullDim (Localization.AtPrime q) = 1 := by
      have hlt : ringKrullDim (Localization.AtPrime q) < 2 := lt_of_not_ge h2
      have hne : ringKrullDim (Localization.AtPrime q) ≠ ⊥ := by
        intro hb; rw [hb] at h1; exact absurd h1 (by decide)
      obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp hne
      rw [← hn] at h1 hlt ⊢
      have h1' : (1 : ℕ∞) ≤ n := WithBot.coe_le_coe.mp h1
      have hlt' : n < (2 : ℕ∞) := WithBot.coe_lt_coe.mp hlt
      have : n = 1 := by
        cases n with
        | top => exact absurd hlt' (by decide)
        | coe k =>
          have : 1 ≤ k := by exact_mod_cast h1'
          have : k < 2 := by exact_mod_cast hlt'
          have : k = 1 := by omega
          subst this; rfl
      rw [this]; rfl
    exact purity_dim_one R S q hreg hdom hqf hdim this hunr

/-- And conversely (trivially), so the two are equivalent. -/
theorem ge2_of_purityBranchLocus (h : PkgI2.PurityBranchLocus.{u}) : PurityBranchLocusGe2.{u} := by
  intro R S _ _ _ _ _ q _ hreg hdom hic hqf hdim h2 hunr
  exact h R S q hreg hdom hic hqf hdim (le_trans (by decide) h2) hunr

end TPurity2

#print axioms TPurity2.purity_dim_one
#print axioms TPurity2.purityBranchLocus_of_ge2
