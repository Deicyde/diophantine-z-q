import Mathlib

/-!
# T1′ (finite, dimension ≥ 2) reduces to T1″ (regular *local* base)

`PurityBranchLocusFiniteGe2` is copied from `T1Reduced.lean`.  `PurityBranchLocusLocal` (T1″) is
the same statement over a regular local ring `R` with `q` over its maximal ideal: Nagata's form
of Zariski–Nagata purity.  We prove T1″ ⇒ T1′ (localize at `p = q ∩ R`) and T1′ ⇒ T1″.
-/

open IsLocalRing

universe u

namespace TPurity2

/-- **The narrowed leaf T1′**: Zariski–Nagata purity for a *finite* `R → S` in dimension `≥ 2`. -/
def PurityBranchLocusFiniteGe2 : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Module.Finite R S] (q : Ideal S) [q.IsPrime],
    IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap R S))) →
    IsDomain (Localization.AtPrime q) →
    IsIntegrallyClosed (Localization.AtPrime q) →
    ringKrullDim (Localization.AtPrime q) =
      ringKrullDim (Localization.AtPrime (q.comap (algebraMap R S))) →
    2 ≤ ringKrullDim (Localization.AtPrime q) →
    (∀ (q' : Ideal S) [q'.IsPrime], q' ≤ q → q'.height = 1 → Algebra.IsUnramifiedAt R q') →
    Algebra.IsEtaleAt R q

/-- **T1″**: purity over a regular local ring, finite `R → S`, `q` over `𝔪_R`, dimension `≥ 2`. -/
def PurityBranchLocusLocal : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [IsRegularLocalRing R]
    [Module.Finite R S] (q : Ideal S) [q.IsPrime],
    q.comap (algebraMap R S) = maximalIdeal R →
    IsDomain (Localization.AtPrime q) →
    IsIntegrallyClosed (Localization.AtPrime q) →
    ringKrullDim (Localization.AtPrime q) = ringKrullDim R →
    2 ≤ ringKrullDim R →
    (∀ (q' : Ideal S) [q'.IsPrime], q' ≤ q → q'.height = 1 → Algebra.IsUnramifiedAt R q') →
    Algebra.IsEtaleAt R q

section
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- `(S_p)_Q ≅ S_{Q ∩ S}` as `R`-algebras. -/
noncomputable def locLocEquiv (p : Ideal R) [p.IsPrime]
    (Q : Ideal (Localization (Algebra.algebraMapSubmonoid S p.primeCompl))) [Q.IsPrime] :
    Localization.AtPrime Q ≃ₐ[R] Localization.AtPrime
      (Q.comap (algebraMap S (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)))) :=
  haveI : IsScalarTower R S (Localization.AtPrime Q) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  (IsLocalization.algEquiv
    (Q.comap (algebraMap S (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)))).primeCompl
    (Localization.AtPrime Q) _).restrictScalars R

noncomputable def atPrimeEquivOfEq {I J : Ideal S} [I.IsPrime] [J.IsPrime] (h : I = J) :
    Localization.AtPrime I ≃ₐ[R] Localization.AtPrime J := by
  subst h; exact AlgEquiv.refl

end

theorem finiteGe2_of_local (h : PurityBranchLocusLocal.{u}) : PurityBranchLocusFiniteGe2.{u} := by
  intro R S _ _ _ _ _ q _ hreg hdom hic hdim h2 hunr
  set p := q.comap (algebraMap R S) with hp
  let Rp := Localization.AtPrime p
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  have : Module.Finite Rp Sp := Module.Finite.of_isLocalization R S p.primeCompl
  have hdisj : Disjoint (Algebra.algebraMapSubmonoid S p.primeCompl : Set S) (q : Set S) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hq
    exact hs hq
  let Q : Ideal Sp := q.map (algebraMap S Sp)
  have hQ : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ Sp q inferInstance hdisj
  have hQc : Q.comap (algebraMap S Sp) = q :=
    IsLocalization.under_map_of_isPrime_disjoint _ Sp (I := q) inferInstance hdisj
  let E : Localization.AtPrime Q ≃ₐ[R] Localization.AtPrime q :=
    (locLocEquiv p Q).trans (atPrimeEquivOfEq hQc)
  have : IsRegularLocalRing Rp := hreg
  have hmax : Q.comap (algebraMap Rp Sp) = maximalIdeal Rp := by
    have h1 : (Q.comap (algebraMap Rp Sp)).under R = p := by
      show Ideal.comap _ _ = _
      rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R S Sp,
        ← Ideal.comap_comap, hQc]
    have h2 : (maximalIdeal Rp).under R = p :=
      Localization.AtPrime.under_maximalIdeal (I := p)
    rw [← IsLocalization.map_under p.primeCompl Rp (Q.comap (algebraMap Rp Sp)),
      ← IsLocalization.map_under p.primeCompl Rp (maximalIdeal Rp), h1, h2]
  have hdomQ : IsDomain (Localization.AtPrime Q) :=
    Function.Injective.isDomain (E : Localization.AtPrime Q →+* Localization.AtPrime q) E.injective
  have hicQ : IsIntegrallyClosed (Localization.AtPrime Q) :=
    IsIntegrallyClosed.of_equiv E.symm.toRingEquiv
  have hdimQ : ringKrullDim (Localization.AtPrime Q) = ringKrullDim Rp :=
    (ringKrullDim_eq_of_ringEquiv E.toRingEquiv).trans hdim
  have key : Algebra.IsEtaleAt Rp Q := by
    refine h Rp Sp Q hmax hdomQ hicQ hdimQ (h2.trans_eq hdim) ?_
    intro Q'' _ hle hht
    have hle' : Q''.comap (algebraMap S Sp) ≤ q := fun x hx => by
      have hx' : x ∈ Q.comap (algebraMap S Sp) := Ideal.comap_mono hle hx
      rwa [hQc] at hx'
    have hht' : (Q''.comap (algebraMap S Sp)).height = 1 := by
      rw [← hht]
      exact IsLocalization.height_under (Algebra.algebraMapSubmonoid S p.primeCompl) Q''
    have hU := hunr _ hle' hht'
    have : Algebra.FormallyUnramified R (Localization.AtPrime Q'') :=
      Algebra.FormallyUnramified.of_equiv (locLocEquiv p Q'').symm
    exact Algebra.FormallyUnramified.of_restrictScalars R Rp _
  have : Algebra.FormallyEtale R (Localization.AtPrime Q) := Algebra.FormallyEtale.comp R Rp _
  exact Algebra.FormallyEtale.of_equiv E

theorem atPrime_congr_regular' {A : Type u} [CommRing A] {I J : Ideal A} [I.IsPrime] [J.IsPrime]
    (h : I = J) : IsRegularLocalRing (Localization.AtPrime I) ↔
      IsRegularLocalRing (Localization.AtPrime J) := by
  subst h; rfl

theorem atPrime_congr_dim' {A : Type u} [CommRing A] {I J : Ideal A} [I.IsPrime] [J.IsPrime]
    (h : I = J) : ringKrullDim (Localization.AtPrime I) = ringKrullDim (Localization.AtPrime J) := by
  subst h; rfl

/-- For a local ring, `R ≅ R_𝔪`. -/
noncomputable def equivAtMaximal (A : Type u) [CommRing A] [IsLocalRing A] :
    A ≃ₐ[A] Localization.AtPrime (maximalIdeal A) :=
  IsLocalization.atUnits A (maximalIdeal A).primeCompl
    (fun x hx => IsLocalRing.notMem_maximalIdeal.mp hx)

/-- Conversely T1′ ⇒ T1″, so T1′ ⇔ T1″. -/
theorem local_of_finiteGe2 (h : PurityBranchLocusFiniteGe2.{u}) : PurityBranchLocusLocal.{u} := by
  intro R S _ _ _ _ _ q _ hq hdom hic hdim h2 hunr
  have e := equivAtMaximal R
  have hreg : IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap R S))) :=
    (atPrime_congr_regular' hq).mpr (IsRegularLocalRing.of_ringEquiv e.toRingEquiv)
  have hd : ringKrullDim (Localization.AtPrime (q.comap (algebraMap R S))) = ringKrullDim R :=
    (atPrime_congr_dim' hq).trans (ringKrullDim_eq_of_ringEquiv e.toRingEquiv).symm
  exact h R S q hreg hdom hic (hdim.trans hd.symm) (hdim ▸ h2) hunr

end TPurity2

#print axioms TPurity2.finiteGe2_of_local
#print axioms TPurity2.local_of_finiteGe2
