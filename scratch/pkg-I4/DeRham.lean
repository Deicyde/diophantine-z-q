import Mathlib

/-!
# Toward a genuine de Rham predicate: naturality of `untilt` and of Fontaine's `θ`

Draft for `docs/research/pkg-I4.md` §3.3 (task pkg-I4). The `G_{ℚ_p}`-action on Mathlib's
`BDeRham (𝓞_ℂ_[p]) p` is to be obtained by functoriality of the construction
`R ↦ AdicCompletion (ker θ[1/p]) (W(R♭)[1/p])`. Its mathematical core is the naturality of
Fontaine's `θ` in `R`; this file proves it for any ring map between `p`-adically complete rings.
-/

noncomputable section

namespace PkgI4.DR

open Ideal

variable {R S : Type*} [CommRing R] [CommRing S] (p : ℕ) [Fact p.Prime]

omit [Fact p.Prime] in
theorem span_p_le_comap (f : R →+* S) :
    span {(p : R)} ≤ (span {(p : S)}).comap f := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
  exact Ideal.mem_span_singleton_self _

/-- `R/p → S/p` induced by `f`. -/
def modPMap (f : R →+* S) : ModP R p →+* ModP S p :=
  Ideal.quotientMap _ f (span_p_le_comap p f)

variable [Fact ¬IsUnit (p : R)] [Fact ¬IsUnit (p : S)]

/-- The tilt is functorial: `R♭ → S♭`. -/
def preTiltMap (f : R →+* S) : PreTilt R p →+* PreTilt S p :=
  Perfection.map p (modPMap p f)

theorem coeff_preTiltMap (f : R →+* S) (x : PreTilt R p) (n : ℕ) :
    Perfection.coeff _ p n (preTiltMap p f x) = modPMap p f (Perfection.coeff _ p n x) :=
  rfl

variable [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S]

/-- Naturality of `untilt`. -/
theorem untilt_preTiltMap (f : R →+* S) (x : PreTilt R p) :
    PreTilt.untilt (preTiltMap p f x) = f (PreTilt.untilt x) := by
  refine Perfection.teichmuller_spec fun n => ?_
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (Perfection.coeff _ p n x)
  refine ⟨f w, ?_, ?_⟩
  · rw [coeff_preTiltMap, ← hw]
    rfl
  · have h := Perfection.teichmuller_sModEq (p := p) (I := span {(p : R)}) (x := x) (y := w) hw
    rw [SModEq.sub_mem] at h ⊢
    have h' := Ideal.mem_map_of_mem f h
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast, map_sub,
      map_pow] at h'
    have h'' := neg_mem h'
    rw [neg_sub] at h''
    exact h''

/-- **Naturality of Fontaine's `θ`**: `θ_S ∘ W(f♭) = f ∘ θ_R`. -/
theorem fontaineTheta_naturality (f : R →+* S) :
    (WittVector.fontaineTheta S p).comp (WittVector.map (preTiltMap p f)) =
      f.comp (WittVector.fontaineTheta R p) := by
  ext x
  refine (IsHausdorff.eq_iff_smodEq (I := span {(p : S)})).mpr fun n => ?_
  rw [smul_eq_mul, Ideal.mul_top, SModEq.idealQuotientMk]
  have key : (Ideal.Quotient.mk (span {(p : S)} ^ n)).comp
      ((WittVector.fontaineTheta S p).comp (WittVector.map (preTiltMap p f))) =
      (Ideal.Quotient.mk (span {(p : S)} ^ n)).comp (f.comp (WittVector.fontaineTheta R p)) := by
    refine WittVector.eq_of_apply_teichmuller_eq _ _ ⟨n, ?_⟩ fun y => ?_
    · rw [← map_natCast (Ideal.Quotient.mk (span {(p : S)} ^ n)), ← map_pow,
        Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton_self _
    · simp only [RingHom.comp_apply, WittVector.map_teichmuller,
        WittVector.fontaineTheta_teichmuller, untilt_preTiltMap]
  exact congrArg (fun g => g x) key

end PkgI4.DR

end

#print axioms PkgI4.DR.fontaineTheta_naturality
