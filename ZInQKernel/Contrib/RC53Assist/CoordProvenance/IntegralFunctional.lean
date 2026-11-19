import ZInQKernel.Contrib.CloudB3RC53.CoordLink.E1aG

/-!
# The integral paired functional of the same class

The orthogonal comparison lifts the specified conjugate class with its
retained boundary.  Applying the same integral cup pairing and trace constructs
PD(-, zperp) as an integral closed functional.  Alternative lifts give the same
functional class, with an explicit dual-boundary discrepancy.

The locators are ex:arith-paired-functional, TeX 3837–3862;
ex:arith-coordinate, TeX 3877–3892; and ex:arith-common-coordinate,
TeX 4159–4177.  The orthogonal comparison, conjugation map, coefficient pairing,
local isotropy homotopies and trace must be instantiated by the actual
arithmetic diagrams.  No coordinate identity or additional printed proposition
is assumed in the construction.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.CoordProvenance.Integral

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (GAcyclic coneCx_acyclic_of_quasiIso)

variable {R : Type} [CommRing R]

/-- Lift the specified conjugate of the same actual class without changing
the coefficient ring or inserting a denominator. -/
theorem lift_same_conjugate_class {A B T : GCx R} (j : GHom A T) (c : GHom B T)
    (hj : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC j))
    (z : B.X 1) (hz : B.d 1 2 rfl z = 0) :
    ∃ zperp : A.X 1, A.d 1 2 rfl zperp = 0 ∧ ∃ b : T.X 0,
      j.f 1 1 rfl zperp - c.f 1 1 rfl z = T.d 0 1 rfl b := by
  have hcz : T.d 1 2 rfl (c.f 1 1 rfl z) = 0 := by
    rw [← c.comm 1 2 1 2 rfl rfl rfl rfl z, hz, map_zero]
  have hc : (coneCx j).d 2 3 rfl ((0 : A.X 2), c.f 1 1 rfl z) = 0 := by
    apply Prod.ext
    · exact map_zero _
    · change j.f 2 2 rfl 0 - T.d 1 2 rfl (c.f 1 1 rfl z) = 0
      rw [map_zero, hcz, sub_self]
  obtain ⟨v, hv⟩ := (coneCx_acyclic_of_quasiIso j hj) 1 2 3 rfl rfl
    ((0 : A.X 2), c.f 1 1 rfl z) hc
  have h1 := congrArg Prod.fst hv
  have h2 := congrArg Prod.snd hv
  refine ⟨v.1, h1, v.2, ?_⟩
  change j.f 1 1 rfl v.1 - T.d 0 1 rfl v.2 = c.f 1 1 rfl z at h2
  rw [← h2]
  abel

/-- Two lifts through the same actual orthogonal comparison differ by an
integral boundary, not an independently chosen scalar. -/
theorem dual_lifts_differ_by_boundary {A T : GCx R} (j : GHom A T)
    (hj : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC j))
    (z z' : A.X 1) (hz : A.d 1 2 rfl z = 0) (hz' : A.d 1 2 rfl z' = 0)
    (b : T.X 0) (hb : j.f 1 1 rfl z - j.f 1 1 rfl z' = T.d 0 1 rfl b) :
    ∃ v : A.X 0, z - z' = A.d 0 1 rfl v := by
  have hc : (coneCx j).d 1 2 rfl (z - z', b) = 0 := by
    apply Prod.ext
    · change A.d 1 2 rfl (z - z') = 0
      rw [map_sub, hz, hz', sub_self]
    · change j.f 1 1 rfl (z - z') - T.d 0 1 rfl b = 0
      rw [map_sub, hb, sub_self]
  obtain ⟨v, hv⟩ := (coneCx_acyclic_of_quasiIso j hj) 0 1 2 rfl rfl (z - z', b) hc
  exact ⟨v.1, (congrArg Prod.fst hv).symm⟩

/-- The integral functional in the pairing order PD(-, zperp). -/
def pairedFunctional {D D' : SelData R} (P : SelPairData D D')
    (tr : (coneCx P.resE).X 3 →ₗ[R] R) (zperp : (selCx D').X 1) :
    (selCx D).X 2 →ₗ[R] R :=
  (traceComp (selPair P) tr 2 1 rfl).flip zperp

/-- Every value is the specified actual cup-pairing value. -/
theorem pairedFunctional_value {D D' : SelData R} (P : SelPairData D D')
    (tr : (coneCx P.resE).X 3 →ₗ[R] R) (zperp : (selCx D').X 1)
    (v : (selCx D).X 2) : pairedFunctional P tr zperp v = tr (selCup P 2 1 3 rfl v zperp) :=
  rfl

/-- The integral functional is closed on the original cochain complex. -/
theorem pairedFunctional_closed {D D' : SelData R} (P : SelPairData D D')
    (tr : (coneCx P.resE).X 3 →ₗ[R] R)
    (htr : ∀ v, tr ((coneCx P.resE).d 2 3 rfl v) = 0)
    (zperp : (selCx D').X 1) (hzperp : (selCx D').d 1 2 rfl zperp = 0)
    (v : (selCx D).X 1) : pairedFunctional P tr zperp ((selCx D).d 1 2 rfl v) = 0 := by
  have hl := selmerCupLeibniz_proof R D D' P 1 2 1 2 2 3 rfl rfl rfl rfl v zperp
  rw [hzperp] at hl
  erw [map_zero, smul_zero, add_zero] at hl
  have h0 := htr (selCup P 1 1 2 rfl v zperp)
  rw [hl] at h0
  exact h0

/-- An integral dual boundary changes the paired functional by the explicit
primal dual boundary.  This is the off-diagonal homotopy retained in the
augmented comparison, rather than a zero-functional-cochain requirement. -/
theorem pairedFunctional_dual_boundary {D D' : SelData R} (P : SelPairData D D')
    (tr : (coneCx P.resE).X 3 →ₗ[R] R)
    (htr : ∀ v, tr ((coneCx P.resE).d 2 3 rfl v) = 0)
    (z z' : (selCx D').X 1) (b : (selCx D').X 0)
    (hb : z - z' = (selCx D').d 0 1 rfl b) (v : (selCx D).X 2) :
    pairedFunctional P tr z v - pairedFunctional P tr z' v =
      -tr (selCup P 3 0 3 rfl ((selCx D).d 2 3 rfl v) b) := by
  have he : pairedFunctional P tr z v - pairedFunctional P tr z' v =
      tr (selCup P 2 1 3 rfl v (z - z')) := by
    exact (map_sub (traceComp (selPair P) tr 2 1 rfl v) z z').symm
  rw [he, hb]
  have hl := selmerCupLeibniz_proof R D D' P 2 3 0 1 2 3 rfl rfl rfl rfl v b
  erw [sgn_two, one_smul] at hl
  have h0 := htr (selCup P 2 0 2 rfl v b)
  erw [hl, map_add] at h0
  exact eq_neg_of_add_eq_zero_right h0

/-- Alternative integral lifts give exactly the same functional class on
cohomology. -/
theorem pairedFunctional_dual_boundary_on_cycles {D D' : SelData R} (P : SelPairData D D')
    (tr : (coneCx P.resE).X 3 →ₗ[R] R)
    (htr : ∀ v, tr ((coneCx P.resE).d 2 3 rfl v) = 0)
    (z z' : (selCx D').X 1) (b : (selCx D').X 0)
    (hb : z - z' = (selCx D').d 0 1 rfl b)
    (v : (selCx D).X 2) (hv : (selCx D).d 2 3 rfl v = 0) :
    pairedFunctional P tr z v = pairedFunctional P tr z' v := by
  have h := pairedFunctional_dual_boundary P tr htr z z' b hb v
  rw [hv] at h
  erw [map_zero, LinearMap.zero_apply, map_zero, neg_zero] at h
  exact sub_eq_zero.mp h

/-- The integral construction of the same actual paired functional, before
any sign evaluation or passage to a fraction field.  The genuine Selmer
complexes instantiate these cochain and pairing objects directly. -/
theorem exists_integral_paired_functional {D Dperp Dconj : SelData R}
    (j : GHom (selCx Dperp) (selCx Dconj)) (c : GHom (selCx D) (selCx Dconj))
    (hj : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC j))
    (z : (selCx D).X 1) (hz : (selCx D).d 1 2 rfl z = 0)
    (P : SelPairData D Dperp) (tr : (coneCx P.resE).X 3 →ₗ[R] R)
    (htr : ∀ v, tr ((coneCx P.resE).d 2 3 rfl v) = 0) :
    ∃ (zperp : (selCx Dperp).X 1) (b : (selCx Dconj).X 0)
      (L : (selCx D).X 2 →ₗ[R] R),
      (selCx Dperp).d 1 2 rfl zperp = 0 ∧
      j.f 1 1 rfl zperp - c.f 1 1 rfl z = (selCx Dconj).d 0 1 rfl b ∧
      (∀ v, L v = tr (selCup P 2 1 3 rfl v zperp)) ∧
      ∀ v, L ((selCx D).d 1 2 rfl v) = 0 := by
  obtain ⟨zperp, hzperp, b, hb⟩ := lift_same_conjugate_class j c hj z hz
  exact ⟨zperp, b, pairedFunctional P tr zperp, hzperp, hb,
    pairedFunctional_value P tr zperp, pairedFunctional_closed P tr htr zperp hzperp⟩

section Genuine

open NumberField IsDedekindDomain ZInQ.Manuscript.RC.SelmerComplex

variable (N : Type) [Field N] [NumberField N] (S₀ : Set (HeightOneSpectrum (𝓞 N)))
  {A B T : Type}
  [AddCommGroup A] [Module R A] [DistribMulAction (GKS N S₀) A] [SMulCommClass (GKS N S₀) R A]
  [TopologicalSpace A] [ContinuousAdd A] [ContinuousConstSMul R A] [ContinuousSMul (GKS N S₀) A]
  [AddCommGroup B] [Module R B] [DistribMulAction (GKS N S₀) B] [SMulCommClass (GKS N S₀) R B]
  [TopologicalSpace B] [ContinuousAdd B] [ContinuousConstSMul R B] [ContinuousSMul (GKS N S₀) B]
  [AddCommGroup T] [Module R T] [DistribMulAction (GKS N S₀) T] [SMulCommClass (GKS N S₀) R T]
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul R T] [ContinuousSMul (GKS N S₀) T]
  (β : A →ₗ[R] B →ₗ[R] T)
  (hβ : ∀ (g : GKS N S₀) (a : A) (b : B), β (g • a) (g • b) = g • β a b)
  (hβc : Continuous fun p : A × B => β p.1 p.2)
  (Δ : GaloisLocalConditions N S₀ R A)
  (Δperp Δconj : GaloisLocalConditions N S₀ R B)
  (I : IsotropyData R (GKS N S₀) (fun v : Places N S₀ => Gloc N v.1)
    (fun v => locMap N S₀ v.1) β hβ hβc Δ Δperp)

/-- The integral pairing on the actual continuous-cochain Selmer complexes. -/
abbrev actualPairData :
    SelPairData (galoisSelData N S₀ R A Δ) (galoisSelData N S₀ R B Δperp) :=
  genuinePairData R (GKS N S₀) (fun v : Places N S₀ => Gloc N v.1)
    (fun v => locMap N S₀ v.1) β hβ hβc Δ Δperp I

/-- Construct the integral closed paired functional on the genuine Galois
Selmer complex from the given same actual class and its orthogonal conjugate
comparison.  Every value is an actual continuous-cochain cup value. -/
theorem exists_genuine_integral_paired_functional
    (j : GHom (selCx (galoisSelData N S₀ R B Δperp)) (selCx (galoisSelData N S₀ R B Δconj)))
    (c : GHom (selCx (galoisSelData N S₀ R A Δ)) (selCx (galoisSelData N S₀ R B Δconj)))
    (hj : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC j))
    (z : (selCx (galoisSelData N S₀ R A Δ)).X 1)
    (hz : (selCx (galoisSelData N S₀ R A Δ)).d 1 2 rfl z = 0)
    (tr : (coneCx (actualPairData N S₀ β hβ hβc Δ Δperp I).resE).X 3 →ₗ[R] R)
    (htr : ∀ v, tr ((coneCx (actualPairData N S₀ β hβ hβc Δ Δperp I).resE).d 2 3 rfl v) = 0) :
    ∃ (zperp : (selCx (galoisSelData N S₀ R B Δperp)).X 1)
      (b : (selCx (galoisSelData N S₀ R B Δconj)).X 0)
      (L : (selCx (galoisSelData N S₀ R A Δ)).X 2 →ₗ[R] R),
      (selCx (galoisSelData N S₀ R B Δperp)).d 1 2 rfl zperp = 0 ∧
      j.f 1 1 rfl zperp - c.f 1 1 rfl z = (selCx (galoisSelData N S₀ R B Δconj)).d 0 1 rfl b ∧
      (∀ v, L v = tr (selCup (actualPairData N S₀ β hβ hβc Δ Δperp I) 2 1 3 rfl v zperp)) ∧
      ∀ v, L ((selCx (galoisSelData N S₀ R A Δ)).d 1 2 rfl v) = 0 :=
  exists_integral_paired_functional j c hj z hz _ tr htr

end Genuine

end ZInQ.Contrib.RC53Assist.CoordProvenance.Integral
