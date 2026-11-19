import ZInQKernel.Contrib.RC53Assist.DKLocalAdapter.LocalDuality

/-!
# Quasi-isomorphisms of the fixed ordinary cone comparisons

The ordinary cone has terms `Bⁿ × Aⁿ⁺¹` and differential
`(b,a) ↦ (db + i(a), -da)`. Its degreewise split sequence has left term B
and right term A shifted by one. A strict square with quasi-isomorphic
vertical maps gives a quasi-isomorphism of these exact ordinary cones.

The arithmetic specialization uses only the two proved fixed local
comparison maps and their existing strict square. It adds no cone
quasi-isomorphism, local duality, or self-duality hypothesis.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Contrib.RC53Assist.DKLocalAdapter

open CategoryTheory NumberField IsDedekindDomain HomologicalComplex
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.DerivedKummerActual
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.SelfDualCore
open ZInQ.Manuscript.RC.SelmerComplex

section Generic

variable {R : Type} [CommRing R]

/-- The sign-correct relation-indexed shift by one. -/
def coneSourceShift (A : GCx R) : GCx R where
  X n := A.X (n + 1)
  d i j h := -(A.d (i + 1) (j + 1) (by omega))
  d_d i j k hij hjk a := by
    change -(A.d (j + 1) (k + 1) _ (-(A.d (i + 1) (j + 1) _ a))) = 0
    rw [map_neg, neg_neg, A.d_d]

/-- Shift the given source comparison, retaining its actual components. -/
def coneSourceShiftHom {A A' : GCx R} (p : GHom A A') :
    GHom (coneSourceShift A) (coneSourceShift A') where
  f i j h := p.f (i + 1) (j + 1) (by omega)
  comm i i₁ j j₁ hij h₁ h₂ hj a := by
    subst hij hj
    change p.f (i₁ + 1) (i₁ + 1) _ (-(A.d (i + 1) (i₁ + 1) _ a)) =
      -(A'.d (i + 1) (i₁ + 1) _ (p.f (i + 1) (i + 1) _ a))
    rw [map_neg]
    exact congrArg Neg.neg (p.comm (i + 1) (i₁ + 1) (i + 1) (i₁ + 1)
      rfl (by omega) (by omega) rfl a)

/-- Identity components identify this shift with the actual cochain shift. -/
def coneSourceShiftIso (A : GCx R) : (coneSourceShift A).toCC ≅ A.toCC⟦(1 : ℤ)⟧ :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    have h : i + 1 = j := hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change ((A.toCC⟦(1 : ℤ)⟧).d i j).hom a = ((coneSourceShift A).toCC.d i j).hom a
    rw [CochainComplex.shiftFunctor_obj_d']
    change (-(1 : ℤ)) • ((A.toCC.d (i + 1) (j + 1)).hom a) =
      ((coneSourceShift A).toCC.d i j).hom a
    erw [GCx.toCC_d_hom A (i + 1) (j + 1) (by omega) a,
      GCx.toCC_d_hom (coneSourceShift A) i j h a]
    simp only [neg_smul, one_smul]
    rfl)

/-- The shifted comparison is the same cochain shift of the original map. -/
theorem coneSourceShiftHom_toCC {A A' : GCx R} (p : GHom A A') :
    GHom.toCC (coneSourceShiftHom p) =
      (coneSourceShiftIso A).hom ≫ (GHom.toCC p)⟦(1 : ℤ)⟧' ≫ (coneSourceShiftIso A').inv := by
  ext n a
  rfl

/-- Quasi-isomorphisms remain quasi-isomorphisms under this source shift. -/
theorem coneSourceShiftHom_quasiIso {A A' : GCx R} (p : GHom A A')
    (hp : QuasiIso (GHom.toCC p)) : QuasiIso (GHom.toCC (coneSourceShiftHom p)) := by
  let := hp
  rw [coneSourceShiftHom_toCC]
  infer_instance

/-- The target complex embeds in its ordinary cone. -/
def ordinaryConeTargetInclusion {A B : GCx R} (i : GHom A B) : GHom B (ordinaryCone i) where
  f n m h := by
    subst m
    exact LinearMap.inl R (B.X n) (A.X (n + 1))
  comm n n' m m' hnm hn hm hn'm' b := by
    subst m m'
    change (B.d n n' hn b, 0) =
      (B.d n n' hm b + i.f (n + 1) n' _ 0, -(A.d (n + 1) (n' + 1) _ 0))
    simp

/-- The ordinary cone projects onto the source shifted by one. -/
def ordinaryConeSourceProjection {A B : GCx R} (i : GHom A B) :
    GHom (ordinaryCone i) (coneSourceShift A) where
  f n m h := by
    subst m
    exact LinearMap.snd R (B.X n) (A.X (n + 1))
  comm n n' m m' hnm hn hm hn'm' a := by
    subst m m'
    rfl

/-- The exact degreewise split ordinary-cone sequence. -/
def ordinaryConeSequence {A B : GCx R} (i : GHom A B) :
    ShortComplex (CochainComplex (ModuleCat.{0} R) ℤ) :=
  ShortComplex.mk (GHom.toCC (ordinaryConeTargetInclusion i))
    (GHom.toCC (ordinaryConeSourceProjection i)) (by ext n a; rfl)

/-- Split exactness uses the actual product coordinates. -/
theorem ordinaryConeSequence_shortExact {A B : GCx R} (i : GHom A B) :
    (ordinaryConeSequence i).ShortExact := by
  refine shortExact_of_degreewise_shortExact _ fun n => ?_
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    rintro ⟨b, a⟩ ha
    change a = 0 at ha
    subst a
    exact ⟨b, rfl⟩
  · rw [ModuleCat.mono_iff_injective]
    intro b b' h
    exact congrArg Prod.fst h
  · rw [ModuleCat.epi_iff_surjective]
    intro a
    exact ⟨(0, a), rfl⟩

/-- A strict square gives a morphism of the exact ordinary-cone sequences. -/
def ordinaryConeSequenceHom {A B A' B' : GCx R} (i : GHom A B) (i' : GHom A' B')
    (p : GHom A A') (q : GHom B B')
    (hsq : ∀ (n : ℤ) (a : A.X n),
      q.f n n rfl (i.f n n rfl a) = i'.f n n rfl (p.f n n rfl a)) :
    ordinaryConeSequence i ⟶ ordinaryConeSequence i' where
  τ₁ := GHom.toCC q
  τ₂ := GHom.toCC (ordinaryConeTransport i i' p q hsq)
  τ₃ := GHom.toCC (coneSourceShiftHom p)
  comm₁₂ := by
    ext n b
    change (q.f n n rfl b, 0) = (q.f n n rfl b, p.f (n + 1) (n + 1) rfl 0)
    rw [map_zero]
  comm₂₃ := by
    ext n a
    rfl

/-- Quasi-isomorphic vertical maps of a strict square give the exact cone quasi-isomorphism. -/
theorem ordinaryConeTransport_quasiIso {A B A' B' : GCx R}
    (i : GHom A B) (i' : GHom A' B') (p : GHom A A') (q : GHom B B')
    (hsq : ∀ (n : ℤ) (a : A.X n),
      q.f n n rfl (i.f n n rfl a) = i'.f n n rfl (p.f n n rfl a))
    (hp : QuasiIso (GHom.toCC p)) (hq : QuasiIso (GHom.toCC q)) :
    QuasiIso (GHom.toCC (ordinaryConeTransport i i' p q hsq)) :=
  quasiIso_τ₂ (ordinaryConeSequenceHom i i' p q hsq)
    (ordinaryConeSequence_shortExact i) (ordinaryConeSequence_shortExact i')
    hq (coneSourceShiftHom_quasiIso p hp)

end Generic

section ActualLocal

open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Contrib.RC53Assist.InnerLimitArith

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K)
  [W.IsElliptic] [HasFullTwoTorsion K S W]
  (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]

/-- The fixed actual-to-literal quotient-cone comparison is a quasi-isomorphism. -/
theorem actualConeToLiteral_quasiIso (hloc : MilneLocalFiniteness) :
    QuasiIso (GHom.toCC (actualConeToLiteral (S := S) W w hloc)) :=
  ordinaryConeTransport_quasiIso
    (ActualSelfDual.localConditionMap K w (W.baseChange (w.adicCompletion K)))
    (integralConditionMap (S := S) W w)
    (actualConditionToLiteral (S := S) W w hloc)
    (natHom (localPointCochainInv (S := S) W w))
    (actualConditionToLiteral_over_inverse_point W w hloc)
    (actualConditionToLiteral_quasiIso W w hloc)
    (fixed_point_dictionary_inverse_quasiIso W w)

end ActualLocal

end ZInQ.Contrib.RC53Assist.DKLocalAdapter
