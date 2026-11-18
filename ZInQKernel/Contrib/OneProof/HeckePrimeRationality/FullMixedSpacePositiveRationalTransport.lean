import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllWeightPositiveRationalSeriesTransport

/-!
# Positive rational transport of the full mixed-plus-class-series space

Both summands are the actual independently generated principal subspaces.
Their proved rational transports may reach different levels. Explicit point
scaling refines the mixed summand, and the absolute finite congruence grid
refines the class summand, to one constructed common level. The result is
transport of this sum of subspaces, not a spanning theorem for all weight-
three modular forms.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

open Complex Function Set
open scoped Real UpperHalfPlane BigOperators MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.FullMixedSpaceTransport

open RationalGaussian RationalMixedTransport ActualMixedSpanBridge RectangularMixedTransport
open AbsoluteCongruenceSeries AbsoluteSeriesRationalTransport AllWeightSeriesTrace
open TorsionWeierstrassData TorsionWeightThree

/-- The actual full mixed space is lower mixed forms plus true absolute class series. -/
def MixedSpace (N : ℕ) (hN : 0<N) : Submodule ℂ (Weight N 3) :=
  RepeatedPrimeMixedTrace.lowerMixedSpan N hN ⊔ MixedWeightThreeAddition.classSeriesSpan N hN

/-- All-label mixed point scaling is an exact identity of actual modular forms. -/
theorem restriction_mixedForm (t N : ℕ) (ht : 0<t) (hN : 0<N) (P Q : ℤ × ℤ) :
    restrictionK N (t*N) 3 (Nat.dvd_mul_left N t) (mixedForm N hN P Q)=
      mixedForm (t*N) (Nat.mul_pos ht hN) ((t : ℤ)*P.1,(t : ℤ)*P.2) ((t : ℤ)*Q.1,(t : ℤ)*Q.2) := by
  apply _root_.ModularForm.ext
  intro τ
  rw [restrictionK_apply,mixedForm_apply,mixedForm_apply]
  simp only [lambdaValue]
  rw [TorsionMuDistributionNat.xValue_scale ht N P.1 P.2 τ,TorsionCorrelation.reg_scale t N ht hN Q.1 Q.2 τ]

/-- Actual mixed-span restriction uses the proved point scaling, not inferred trace closure. -/
theorem restriction_mixedSpan (t N : ℕ) (ht : 0<t) (hN : 0<N)
    {f : Weight N 3} (hf : f∈mixedSpan N hN) :
    restrictionK N (t*N) 3 (Nat.dvd_mul_left N t) f∈mixedSpan (t*N) (Nat.mul_pos ht hN) := by
  have hle : mixedSpan N hN ≤ (mixedSpan (t*N) (Nat.mul_pos ht hN)).comap
      (restrictionK N (t*N) 3 (Nat.dvd_mul_left N t)) := by
    apply Submodule.span_le.mpr
    rintro F ⟨P,Q,hP,hQ,rfl⟩
    change restrictionK N (t*N) 3 (Nat.dvd_mul_left N t) (mixedForm N hN P Q)∈mixedSpan (t*N) (Nat.mul_pos ht hN)
    rw [restriction_mixedForm t N ht hN P Q]
    exact mixedForm_mem _ _ _ _
  exact hle hf

/-- The established all-label lower mixed span has the same honest forward refinement. -/
theorem restriction_lowerMixedSpan (t N : ℕ) (ht : 0<t) (hN : 0<N)
    {f : Weight N 3} (hf : f∈RepeatedPrimeMixedTrace.lowerMixedSpan N hN) :
    restrictionK N (t*N) 3 (Nat.dvd_mul_left N t) f∈RepeatedPrimeMixedTrace.lowerMixedSpan (t*N) (Nat.mul_pos ht hN) := by
  rw [← mixedSpan_eq_lowerMixedSpan] at hf ⊢
  exact restriction_mixedSpan t N ht hN hf

/-- Concrete actual representation in the sum of the two genuine subspaces. -/
def RepresentsFullAt (M : ℕ) (hM : 0<M) (u : ℍ → ℂ) : Prop :=
  ∃ F : Weight M 3,F∈MixedSpace M hM ∧ ∀ τ : ℍ,F τ=u τ

lemma representsFullAt_level {M L : ℕ} {hM : 0<M} {hL : 0<L} {u : ℍ → ℂ}
    (hlevel : M=L) (h : RepresentsFullAt M hM u) : RepresentsFullAt L hL u := by
  cases hlevel
  exact h

/-- A single positive multiplier transports both real summands at once.
It is chosen before the level and form, and is the product of the two proved
matrix-only multipliers. Every refinement and representation input is filled. -/
theorem uniform_fullMixedSpace_transport (A : GLQ) (hA : 0<(A.det : ℚ)) :
    ∃ (D : ℕ) (hD : 0<D),∀ (N : ℕ) (hN : 0<N) (f : Weight N 3),f∈MixedSpace N hN →
      RepresentsFullAt (D*N) (Nat.mul_pos hD hN) (⇑f ∣[(3 : ℤ)] RationalGaussian.mapR A) := by
  obtain ⟨Dm,hDm,hmixed⟩ := uniform_mixed_positive_rational A hA
  obtain ⟨Ds,hDs,hseries⟩ := uniform_classSeries_transport A hA
  refine ⟨Ds*Dm,Nat.mul_pos hDs hDm,?_⟩
  intro N hN f hf
  obtain ⟨fm,hfm,fs,hfs,rfl⟩ := Submodule.mem_sup.mp hf
  have hfmGood : fm∈mixedSpan N hN := by
    rw [mixedSpan_eq_lowerMixedSpan]
    exact hfm
  obtain ⟨Fm,hFm,hFmEq⟩ := hmixed N hN fm hfmGood
  obtain ⟨Fs,hFs,hFsEq⟩ := hseries N hN fs hfs
  have hRm : RepresentsFullAt (Ds*(Dm*N)) (Nat.mul_pos hDs (Nat.mul_pos hDm hN))
      (⇑fm ∣[(3 : ℤ)] RationalGaussian.mapR A) := by
    refine ⟨restrictionK (Dm*N) (Ds*(Dm*N)) 3 (Nat.dvd_mul_left (Dm*N) Ds) Fm,?_,?_⟩
    · apply Submodule.mem_sup_left
      rw [← mixedSpan_eq_lowerMixedSpan]
      exact restriction_mixedSpan Ds (Dm*N) hDs (Nat.mul_pos hDm hN) hFm
    · intro τ
      rw [restrictionK_apply]
      exact hFmEq τ
  have hRs : RepresentsFullAt (Dm*(Ds*N)) (Nat.mul_pos hDm (Nat.mul_pos hDs hN))
      (⇑fs ∣[(3 : ℤ)] RationalGaussian.mapR A) := by
    refine ⟨restrictionK (Ds*N) (Dm*(Ds*N)) 3 (Nat.dvd_mul_left (Ds*N) Dm) Fs,?_,?_⟩
    · apply Submodule.mem_sup_right
      exact restriction_classSeriesSpan Dm (Ds*N) hDm (Nat.mul_pos hDs hN) hFs
    · intro τ
      rw [restrictionK_apply]
      exact hFsEq τ
  have hRm' : RepresentsFullAt ((Ds*Dm)*N) (Nat.mul_pos (Nat.mul_pos hDs hDm) hN)
      (⇑fm ∣[(3 : ℤ)] RationalGaussian.mapR A) := representsFullAt_level (by ring) hRm
  have hRs' : RepresentsFullAt ((Ds*Dm)*N) (Nat.mul_pos (Nat.mul_pos hDs hDm) hN)
      (⇑fs ∣[(3 : ℤ)] RationalGaussian.mapR A) := representsFullAt_level (by ring) hRs
  obtain ⟨Gm,hGm,hGmEq⟩ := hRm'
  obtain ⟨Gs,hGs,hGsEq⟩ := hRs'
  refine ⟨Gm+Gs,Submodule.add_mem _ hGm hGs,?_⟩
  intro τ
  rw [_root_.add_apply,hGmEq τ,hGsEq τ,FunLike.coe_add,SlashAction.add_slash]
  rfl

/-- Full actual mixed-plus-class-series rational transport on a constructed
common principal level divisible by N. No desired closure, transport, EqSpan
or representation premise occurs at this endpoint. -/
theorem actual_positive_rational_MixedSpace_transport (N : ℕ) (hN : 0<N)
    (f : Weight N 3) (hf : f∈MixedSpace N hN) (A : GLQ) (hA : 0<(A.det : ℚ)) :
    ∃ (M : ℕ) (hM : 0<M),N∣M ∧
      ∃ F : Weight M 3,F∈MixedSpace M hM ∧
        ∀ τ : ℍ,F τ=(⇑f ∣[(3 : ℤ)] Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) A) τ := by
  obtain ⟨D,hD,htransport⟩ := uniform_fullMixedSpace_transport A hA
  obtain ⟨F,hF,hFeq⟩ := htransport N hN f hf
  exact ⟨D*N,Nat.mul_pos hD hN,Nat.dvd_mul_left N D,F,hF,hFeq⟩

end ZInQ.Contrib.HeckePrimeRationality.FullMixedSpaceTransport
