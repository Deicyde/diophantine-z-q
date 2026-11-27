import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Join

/-! The character projection is computed on the common Picard label,
then transported through Artin reciprocity. On-the-spot (c),
for tex 9180–9194. -/

noncomputable section

open scoped NumberField WeierstrassCurve Classical
open NumberField IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Stages ZInQ.Manuscript.RC.Visibility

namespace ZInQ.Manuscript.RC.O7Residual

open O7Assemble O7Actual O7Orbits PicardFibers Eichler Adelic ThetaJoin ThetaClose PMGeometry

open TauCeti.GlobalNumberFields.NumberFieldOrder

/-- First match the two integer signs on the class group, with no
dependent projection from the staged weight record. -/
theorem character_eq_on_class {F : Type} [Field F] [NumberField F] {d : ℤ}
    {χ : Pic (CST.conductorOrder F 1) →* ℂˣ}
    (C : NormCharacterDescent F d) (hχ : IsQuadRingClassChar F 1 d χ)
    (pic : ClassGroup (𝓞 F) ≃* Pic (CST.conductorOrder F 1))
    (c : ClassGroup (𝓞 F))
    (J : integralIdealsPrimeTo (CST.conductorOrder F 1).conductorModulus)
    (hJ : (Ideal.absNorm J.val).Coprime d.natAbs)
    (hpic : (CST.conductorOrder F 1).picClass J = pic c) :
    (C.choose (pic c) : ℤ) = chiSign χ (pic c) := by
  rw [← hpic]
  exact chiSign_of_descent C hχ J hJ

section Row

attribute [local irreducible] StageKummer.datumOnModel ringClassArtinEquiv

variable {ℓ : ℕ} {W : WData ℓ} {I : GenusOddInstance W} {L : ℕ} (s : StageKummer.Setup I L)
  (i : ℕ) [Fact (s.q.stage i).p.Prime]
  [(ReducedEquation (EcurveZ ℓ) (s.q.stage i).p).IsElliptic]

variable {m : ℕ} (hN : 0 < StageKummer.level ℓ)
  (hcop : (StageKummer.level ℓ).Coprime (s.q.stage i).p)
  (H : DiscriminantData m (StageKummer.level ℓ) (s.q.stage i).p) (w : ℕ → ℤˣ)
  (hm : (m : ℤ) = -W.hstar) {ap : ℕ → ℤ} {X : PMAdelic.CoarseFibre}
  (J : PMAdelic.JetchevKane (s.q.stage i).p (StageKummer.stage_mod_four s i)
    (StageKummer.level ℓ) hN hcop X)
  (O : PMAdelic.OperatorComparison (s.q.stage i).p (StageKummer.stage_mod_four s i)
    (StageKummer.level ℓ) hN hcop X J)
  (G : PMAdelic.SpecialFibre (s.q.stage i).p (StageKummer.level ℓ)
    (ResidueAt (StageKummer.place s i)) (ReducedEquation (EcurveZ ℓ) (s.q.stage i).p) ap X)

variable {n : ℕ}
  (A : AdmissibleD (actualStage s i hN hcop H w hm J O G) (n : ℤ))
  (t : HeegnerDatum (Ecurve ℓ) I.f I.Lat I.κ ((n : ℤ) * W.hstar) 1 W.hstar)

variable
    (ι : letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf; (StageKummer.chosenDatum t).K →ₐ[ℚ] B (-1) (-((s.q.stage i).p : ℚ)))
    (T : letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
      ∀ p, Nonempty (LocalTorusChart (O7Orbits.ActualOrder (actualStage s i hN hcop H w hm J O G)) ι
        (referenceUnit _ A (selectedBasis s i hN hcop H w hm J O G A t) ι)
        (referenceAffine _ (selectedBasis s i hN hcop H w hm J O G A t) ι) p))
    (R : letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
      ∀ b, HasLocalRealizations (actualStage s i hN hcop H w hm J O G)
        (referenceAffine _ (selectedBasis s i hN hcop H w hm J O G A t) ι) b)

variable
    (P : letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
      TorusWeights.TorusParametrization (actualStage s i hN hcop H w hm J O G) (n : ℤ)
        (selectedBasis s i hN hcop H w hm J O G A t) (orbitsAt s i hN hcop H w hm J O G A t ι T R))
    (J' : letI := (StageKummer.chosenDatum t).field; letI := (StageKummer.chosenDatum t).nf
      TorusWeights.TorusIdealRead P)

/-- Compute the character projection before any change of class label. -/
theorem actual_character_projection :
    letI := (StageKummer.chosenDatum t).field
    letI := (StageKummer.chosenDatum t).nf
    ∀ c : ClassGroup (𝓞 (StageKummer.chosenDatum t).K),
      (weightsAt s i hN hcop H w hm J O G A t ι T R P J').character c =
        (((descentAt s i hN hcop H w hm J O G A t).choose (J'.pic c) : ℤ) : Coefficients hN H w) :=
  fun _ => rfl

/-- Cancellation through a composed class label. -/
theorem inverse_after_trans {A B C : Type} [Mul B] [Mul C]
    (f : A ≃ B) (e : B ≃* C) (a : A) :
    e.symm ((f.trans e.toEquiv) a) = f a := e.symm_apply_apply (f a)

set_option maxHeartbeats 300000 in
set_option linter.style.haveILetI false in
/-- The inverse Artin symbol recovers the same Picard class. -/
theorem actual_artin_projection :
    letI := (StageKummer.chosenDatum t).field
    letI := (StageKummer.chosenDatum t).nf
    letI := (StageKummer.chosenDatum t).nz
    ∀ c : ClassGroup (𝓞 (StageKummer.chosenDatum t).K),
      (ringClassArtinEquiv (CST.conductorOrder (StageKummer.chosenDatum t).K 1)).symm
        (artinAt s i hN hcop H w hm J O G A t ι T R P J' c) = J'.pic c := by
  letI := (StageKummer.chosenDatum t).field
  letI := (StageKummer.chosenDatum t).nf
  letI := (StageKummer.chosenDatum t).nz
  intro c
  simp only [artinAt]
  let e := ringClassArtinEquiv (CST.conductorOrder (StageKummer.chosenDatum t).K 1)
  have h := inverse_after_trans J'.pic.toEquiv e c
  exact h

set_option maxHeartbeats 450000 in
set_option linter.style.haveILetI false in
/-- Match the actual weight character with the selected datum's character
under the actual Artin labelling. -/
theorem artinMatchAt :
    StageKummer.ArtinMatch (StageKummer.chosenDatum t)
      (artinAt s i hN hcop H w hm J O G A t ι T R P J')
      (weightsAt s i hN hcop H w hm J O G A t ι T R P J').character := by
  letI := (StageKummer.chosenDatum t).field
  letI := (StageKummer.chosenDatum t).nf
  letI := (StageKummer.chosenDatum t).nz
  let F := (StageKummer.chosenDatum t).K
  let χ := (StageKummer.chosenDatum t).χ
  let C := descentAt s i hN hcop H w hm J O G A t
  have hχ : IsQuadRingClassChar F 1 (-(m : ℤ)) χ := by
    rw [hm, neg_neg]
    exact (StageKummer.chosenDatum t).quad
  intro c
  have hcopJ : (Ideal.absNorm (J'.ideal c).val).Coprime m := J'.coprime c
  have hc : (C.choose (J'.pic c) : ℤ) = chiSign χ (J'.pic c) :=
    character_eq_on_class C hχ J'.pic c (J'.ideal c)
      (by simpa only [Int.natAbs_neg, Int.natAbs_natCast] using hcopJ) (J'.pic_eq c)
  rw [actual_character_projection s i hN hcop H w hm J O G A t ι T R P J' c,
    actual_artin_projection s i hN hcop H w hm J O G A t ι T R P J' c]
  exact congrArg (fun x : ℤ => (x : Coefficients hN H w)) hc

end Row

end ZInQ.Manuscript.RC.O7Residual
