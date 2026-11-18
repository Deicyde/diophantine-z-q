import ZInQKernel.Contrib.OneProof.RC.Stages.Primes
import ZInQKernel.Contrib.OneProof.RC.Stages.Sequence

/-! Specialize the recursion to actual Chebotarev primes (tex 8358–8377, 8400–8401). -/

noncomputable section

open scoped WeierstrassCurve
open TauCeti ZInQ.Manuscript.RC.PrintsArith ZInQ.Manuscript.RC.GlueSweep.Tate ZInQ.Manuscript.RC.TateWiring
open ZInQ.Manuscript ZInQ.Manuscript.RC.Nonvanishing ZInQ.Manuscript.RC.Wiring
open ZInQ.Contrib.ChebFD.C10 (IsFrobAt)

open ZInQ.Contrib.CloudB3RC53

namespace ZInQ.Manuscript.RC.Stages

/-- The Frob representative, its joint-field agreement, and the two residue signs at a stage.
The finite prime exclusion contains all primes of bad reduction. -/
def ActualAt (A E : WeierstrassCurve ℚ) [A.IsElliptic] [E.IsElliptic]
    (Q : GeomPoint A) (F₀ : IntermediateField ℚ Qbar) (σ : GalQ) (Dw hstar : ℤ)
    (M p : ℕ) : Prop :=
  ∃ (hp : p.Prime) (g : GalQ), p ≠ 2 ∧ GoodAt E p ∧ GoodAt A p ∧ IsFrobAt g p ∧
    (∀ x ∈ jointField A E F₀ Q M, g x = σ x) ∧
    (PadicInt.toZModPow M).mapMatrix (tateMatrix E g) =
      (PadicInt.toZModPow M).mapMatrix (tateMatrix E σ) ∧
    (PadicInt.toZModPow M).mapMatrix (tateMatrix A g) =
      (PadicInt.toZModPow M).mapMatrix (tateMatrix A σ) ∧
    ((p : ℤ) : ZMod (2 ^ M)) = -1 ∧
    letI : Fact p.Prime := ⟨hp⟩
    legendreSym p Dw = 1 ∧ legendreSym p hstar = -1

/-- Keep one chosen sigma and one witness throughout the recursion. The finite set S
can be enlarged before the construction, including by all bad primes. -/
def actualStageSequence (A E : WeierstrassCurve ℚ) [A.IsElliptic] [E.IsElliptic]
    (Q : GeomPoint A) (F₀ : IntermediateField ℚ Qbar) [FiniteDimensional ℚ F₀] (σ : GalQ)
    (hdet : (tateMatrix E σ).det = -1) (Dw hstar : ℤ) (cw : ℕ) (S : Finset ℕ)
    {x y : Qbar} (hxmem : x ∈ F₀) (hymem : y ∈ F₀)
    (hx : x ^ 2 = (Dw : Qbar)) (hy : y ^ 2 = (hstar : Qbar))
    (hsx : σ x = x) (hsy : σ y = -y)
    (havoid : ∀ p : ℕ, p.Prime → p ∉ S →
      GoodAt E p ∧ GoodAt A p ∧ ¬ (p : ℤ) ∣ Dw ∧ ¬ (p : ℤ) ∣ hstar) :
    StageSequence (ActualAt A E Q F₀ σ Dw hstar) cw S := by
  apply stageSequence cw S
  intro M _ B
  obtain ⟨g, p, hp, hpB, hp2, hf, ha, hE, hA, hcongr⟩ :=
    exists_jointFrob A E σ hdet M F₀ Q (B ∪ S)
  have hpS : p ∉ S := fun h => hpB (Finset.mem_union_right B h)
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hEg, hAg, hd, hh⟩ := havoid p hp hpS
  have hex : ∀ z ∈ F₀, g z = σ z := fun z hz =>
    ha z (aux_le_joint A E F₀ Q M hz)
  have hsign := residueSigns_of_agreement hp2 hf hd hh hx hy
    (hex x hxmem) (hex y hymem) hsx hsy
  exact ⟨⟨p, hp, ⟨hp, g, hp2, hEg, hAg, hf, ha, hE, hA, hcongr, hsign⟩⟩,
    fun h => hpB (Finset.mem_union_left S h)⟩

/-- The fixed witness stays in the moving support at every precision. -/
theorem witness_on_stages {A E : WeierstrassCurve ℚ} [A.IsElliptic] [E.IsElliptic]
    {Q : GeomPoint A} {F₀ : IntermediateField ℚ Qbar} {σ : GalQ} {Dw hstar : ℤ} {cw : ℕ}
    {S : Finset ℕ} (q : StageSequence (ActualAt A E Q F₀ σ Dw hstar) cw S) (i : ℕ) :
    stageTest q i Dw := by
  obtain ⟨hp, g, hp2, hEg, hAg, hf, ha, hE, hA, hcongr, hD, hH⟩ := (q.stage i).arithmetic
  exact hD

/-- Choose the actual Frobenius used by the stage specialization, with its joint-field
agreement. Its place is supplied by the same IsFrobAt witness. -/
def selectedFrobenius {A E : WeierstrassCurve ℚ} [A.IsElliptic] [E.IsElliptic]
    {Q : GeomPoint A} {F₀ : IntermediateField ℚ Qbar} {σ : GalQ} {Dw hstar : ℤ} {cw : ℕ}
    {S : Finset ℕ} (q : StageSequence (ActualAt A E Q F₀ σ Dw hstar) cw S) (i : ℕ) :
    {g : GalQ // IsFrobAt g (q.stage i).p ∧
      ∀ x ∈ jointField A E F₀ Q (cw + 1 + i), g x = σ x} :=
  Classical.indefiniteDescription _ (by
    obtain ⟨hp, g, hp2, hEg, hAg, hf, ha, hE, hA, hcongr, hD, hH⟩ := (q.stage i).arithmetic
    exact ⟨g, hf, ha⟩)

/-- The chosen stage Frobenius squared acts trivially on the original curve's
global 2-power torsion. The comparison with geometric residue torsion uses the
specialization at this same place. -/
theorem actualStage_torsion_sq {A E : WeierstrassCurve ℚ} [A.IsElliptic] [E.IsElliptic]
    {Q : GeomPoint A} {F₀ : IntermediateField ℚ Qbar} {σ : GalQ} {Dw hstar : ℤ} {cw : ℕ}
    {S : Finset ℕ} (q : StageSequence (ActualAt A E Q F₀ σ Dw hstar) cw S) (i : ℕ)
    (hσ : tateRep E 2 (σ * σ) = 1) (t : TateModuleLevel 2 (GeomPoint E) (cw + 1 + i)) :
    WeierstrassCurve.Affine.Point.map (W' := E)
      (((selectedFrobenius q i).val * (selectedFrobenius q i).val) : GalQ).toAlgHom t.val =
      t.val := by
  apply global_frob_sq_on_torsion E (σ := σ) _ _ t
  · intro x hx
    exact (selectedFrobenius q i).property.2 x
      (tors_left_le_joint A E F₀ Q (cw + 1 + i) hx)
  · intro y
    obtain ⟨v, rfl⟩ := TateModule.proj_surjective
      (TateModule.tateModuleTransition_surjective_of_natCard (p := 2) (by decide)
        ((E⁄Qbar).natCard_tateModuleLevel (by norm_num : (2 : Qbar) ≠ 0))) (cw + 1 + i) y
    rw [← coe_proj_tateRep, hσ]
    rfl

/-- All bad primes and the two discriminant supports can be excluded while
retaining any separately chosen finite exclusions. -/
def stageExclusions (ℓ : ℕ) (Dw hstar : ℤ) (B : Finset ℕ) : Finset ℕ :=
  ((B ∪ S0 ℓ) ∪ Dw.natAbs.primeFactors) ∪ hstar.natAbs.primeFactors

theorem stageExclusions_good {ℓ : ℕ} (hℓ : ℓ ≠ 0) {Dw hstar : ℤ}
    (hDw : Dw ≠ 0) (hstar₀ : hstar ≠ 0) (B : Finset ℕ)
    {p : ℕ} (hp : p.Prime) (hn : p ∉ stageExclusions ℓ Dw hstar B) :
    GoodAt (Ecurve ℓ) p ∧ GoodAt (qtwist (Ecurve ℓ) Dw) p ∧
      ¬ (p : ℤ) ∣ Dw ∧ ¬ (p : ℤ) ∣ hstar := by
  let S := stageExclusions ℓ Dw hstar B
  have hbase : S0 ℓ ⊆ S := fun r hr =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hr))
  have h2 : 2 ∈ S := hbase (by simp [S0])
  have h3 : 3 ∈ S := hbase (by simp [S0])
  have hℓp : ∀ r : ℕ, r.Prime → (r : ℤ) ∣ (ℓ : ℤ) → r ∈ S := by
    intro r hr hd
    apply hbase
    have hd' : r ∣ ℓ := by exact_mod_cast hd
    simp [S0, Nat.mem_primeFactors, hr, hd', hℓ]
  have hdp : ∀ r : ℕ, r.Prime → (r : ℤ) ∣ Dw → r ∈ S := by
    intro r hr hd
    have hda : r ∣ Dw.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr hd
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Nat.mem_primeFactors.mpr ⟨hr, hda, Int.natAbs_ne_zero.mpr hDw⟩))
  have hpD : ¬ (p : ℤ) ∣ Dw := fun hd => hn (hdp p hp hd)
  have hpH : ¬ (p : ℤ) ∣ hstar := by
    intro hd
    have hda : p ∣ hstar.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr hd
    exact hn (Finset.mem_union_right _
      (Nat.mem_primeFactors.mpr ⟨hp, hda, Int.natAbs_ne_zero.mpr hstar₀⟩))
  refine ⟨?_, ?_, hpD, hpH⟩
  · by_contra hg
    exact hn (bad_curve_mem h2 h3 hℓp p hp hg)
  · rw [qtwist_Ecurve]
    by_contra hg
    apply hn (bad_curve_mem h2 h3 ?_ p hp hg)
    intro r hr hd
    exact ((Nat.prime_iff_prime_int.mp hr).dvd_or_dvd hd).elim (hdp r hr) (hℓp r hr)

#print axioms actualStage_torsion_sq
#print axioms stageExclusions_good
#print axioms selectedFrobenius
#print axioms actualStageSequence
#print axioms witness_on_stages

end ZInQ.Manuscript.RC.Stages
