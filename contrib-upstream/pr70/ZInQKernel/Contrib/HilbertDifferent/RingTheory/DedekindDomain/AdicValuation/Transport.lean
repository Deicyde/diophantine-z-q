/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/RingTheory/DedekindDomain/AdicValuation/Transport.lean
Original SHA-256: f3e5b2edc35e187e9df93b888d57227942a0d33db31e110dde7728845ae2a06e
Changes: contribution import paths and namespace; retained proof content.
Full licenses and provenance: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
-/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/- Adapted to the repository-pinned Mathlib API; only declarations needed by the
Hilbert different consumer are retained. Source: TauCeti@33c2099c678ea391f7ea3e0ddaf945a76a625e5d,
TauCeti/RingTheory/DedekindDomain/AdicValuation/Transport.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Localization.FractionRing
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.DedekindDomain.Ideal
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section

namespace IsDedekindDomain.HeightOneSpectrum

section DedekindDomain

variable {R R' : Type*} [CommRing R] [IsDedekindDomain R] [CommRing R'] [IsDedekindDomain R']

/- **The integer adic valuation transports along a ring isomorphism.** If the height one prime `w`
of `R'` is the image of the height one prime `v` of `R` under `e`, then the `w`-adic valuation of
`e r` is the `v`-adic valuation of `r`. -/
theorem intValuation_ringEquiv (e : R ≃+* R') {v : HeightOneSpectrum R} {w : HeightOneSpectrum R'}
    (hvw : w.asIdeal = Ideal.map e v.asIdeal) (r : R) :
    w.intValuation (e r) = v.intValuation r := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · have her : e r ≠ 0 := by simp [hr]
    have hspan : Ideal.span {e r} = Ideal.map e (Ideal.span {r}) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [w.intValuation_if_neg her, v.intValuation_if_neg hr, hvw, hspan,
      Ideal.count_factors_map_of_ringEquiv e ((Ideal.prime_iff_isPrime v.ne_bot).mpr v.isPrime)
        (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hr)]

variable {K K' : Type*} [Field K] [Field K'] [Algebra R K] [IsFractionRing R K] [Algebra R' K']
  [IsFractionRing R' K']

/- The fraction-field adic valuation transports on the image of `R`, which is the building block
for `valuation_ringEquivOfRingEquiv`. -/
private theorem valuation_ringEquivOfRingEquiv_algebraMap (e : R ≃+* R') {v : HeightOneSpectrum R}
    {w : HeightOneSpectrum R'} (hvw : w.asIdeal = Ideal.map e v.asIdeal) (r : R) :
    w.valuation K' (IsFractionRing.ringEquivOfRingEquiv e (algebraMap R K r)) =
      v.valuation K (algebraMap R K r) := by
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap e r, valuation_of_algebraMap,
    valuation_of_algebraMap]
  exact intValuation_ringEquiv e hvw r

/- **The adic valuation of the fraction field transports along a ring isomorphism.** With
`σ = IsFractionRing.ringEquivOfRingEquiv e` the induced isomorphism of fraction fields, and `w` the
image of `v` under `e`, the `w`-adic valuation of `σ f` is the `v`-adic valuation of `f`. This is
the algebraic engine of divisor Galois descent. -/
theorem valuation_ringEquivOfRingEquiv (e : R ≃+* R') {v : HeightOneSpectrum R}
    {w : HeightOneSpectrum R'} (hvw : w.asIdeal = Ideal.map e v.asIdeal) (f : K) :
    w.valuation K' (IsFractionRing.ringEquivOfRingEquiv e f) = v.valuation K f := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := R) f
  rw [map_div₀, Valuation.map_div, Valuation.map_div,
    valuation_ringEquivOfRingEquiv_algebraMap e hvw a,
    valuation_ringEquivOfRingEquiv_algebraMap e hvw b]

end DedekindDomain

section Completion

open WithZero WithZeroTopology

variable {R R' : Type*} [CommRing R] [IsDedekindDomain R] [CommRing R'] [IsDedekindDomain R']
  {K K' : Type*} [Field K] [Field K'] [Algebra R K] [IsFractionRing R K] [Algebra R' K']
  [IsFractionRing R' K'] (v : HeightOneSpectrum R) (w : HeightOneSpectrum R')

/- A field isomorphism carrying the `v`-adic valuation to the `w`-adic valuation is uniformly
continuous for the two adic uniformities. -/
theorem uniformContinuous_withValCongr (σ : K ≃+* K')
    (hσ : ∀ x, w.valuation K' (σ x) = v.valuation K x) :
    UniformContinuous (WithVal.congr (v.valuation K) (w.valuation K') σ) := by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  -- the preimage of a valuation ball is the valuation ball of the same radius
  have hcont : Continuous (Valued.v : Valuation (WithVal (v.valuation K)) ℤᵐ⁰) :=
    Valued.continuous_valuation_of_surjective <| .of_comp (v.valuation_surjective K)
  have hγ : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 :=
    (map_ne_zero_iff _ MonoidWithZeroHom.ValueGroup₀.embedding_injective).mpr γ.ne_zero
  filter_upwards [hcont.continuousAt.preimage_mem_nhds <| by
    simpa using Iio_mem_nhds_zero hγ] with x hx
  rw [Valuation.restrict_lt_iff_lt_embedding]
  simpa [hσ, WithVal.apply_ofVal] using hx

/- The isomorphism of adic completions `K_v ≃+* K'_w` extending a field isomorphism
`σ : K ≃+* K'` that carries the `v`-adic valuation to the `w`-adic valuation. -/
noncomputable def adicCompletionCongr (σ : K ≃+* K')
    (hσ : ∀ x, w.valuation K' (σ x) = v.valuation K x) :
    v.adicCompletion K ≃+* w.adicCompletion K' :=
  (adicCompletion.equiv K v).trans <|
    (UniformSpace.Completion.mapRingEquiv (WithVal.congr (v.valuation K) (w.valuation K') σ)
      (uniformContinuous_withValCongr v w σ hσ).continuous
      (uniformContinuous_withValCongr w v σ.symm fun y ↦ by
        simpa using (hσ (σ.symm y)).symm).continuous).trans
    (adicCompletion.equiv K' w).symm

variable {v w} {σ : K ≃+* K'} (hσ : ∀ x, w.valuation K' (σ x) = v.valuation K x)

/- On the underlying uniform-space completions, `adicCompletionCongr` is the completion of `σ`. -/
@[simp]
theorem toCompletion_adicCompletionCongr (x : v.adicCompletion K) :
    (adicCompletionCongr v w σ hσ x).toCompletion =
      UniformSpace.Completion.map (WithVal.congr (v.valuation K) (w.valuation K') σ)
        x.toCompletion :=
  (rfl)

/- `adicCompletionCongr` extends `σ`. -/
@[simp]
theorem adicCompletionCongr_algebraMap (x : K) :
    adicCompletionCongr v w σ hσ (algebraMap K (v.adicCompletion K) x) =
      algebraMap K' (w.adicCompletion K') (σ x) := by
  apply adicCompletion.ext
  rw [toCompletion_adicCompletionCongr]
  simp only [algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self_apply,
    adicCompletion.coe_toCompletion]
  rw [UniformSpace.Completion.map_coe (uniformContinuous_withValCongr v w σ hσ)]
  simp

/- `adicCompletionCongr` is continuous. -/
theorem continuous_adicCompletionCongr : Continuous (adicCompletionCongr v w σ hσ) := by
  have h : (adicCompletionCongr v w σ hσ : v.adicCompletion K → w.adicCompletion K') =
      adicCompletion.ofCompletion ∘
        UniformSpace.Completion.map (WithVal.congr (v.valuation K) (w.valuation K') σ) ∘
        adicCompletion.toCompletion := by
    funext x
    rw [Function.comp_apply, Function.comp_apply, ← toCompletion_adicCompletionCongr hσ,
      adicCompletion.ofCompletion_toCompletion]
  rw [h]
  exact (adicCompletion.continuous_ofCompletion K' w).comp
    (UniformSpace.Completion.continuous_map.comp (adicCompletion.continuous_toCompletion K v))

/- `adicCompletionCongr` is the only continuous ring homomorphism `K_v →+* K'_w` extending `σ`. -/
theorem eq_adicCompletionCongr_of_continuous {f : v.adicCompletion K →+* w.adicCompletion K'}
    (hf : Continuous f)
    (hfK : ∀ x : K, f (algebraMap K _ x) = algebraMap K' (w.adicCompletion K') (σ x)) :
    f = (adicCompletionCongr v w σ hσ).toRingHom :=
  DFunLike.coe_injective <| (v.denseRange_algebraMap K).equalizer hf
    (continuous_adicCompletionCongr hσ) (funext fun x ↦ by
      rw [Function.comp_apply, Function.comp_apply, hfK x, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, adicCompletionCongr_algebraMap])

/- `adicCompletionCongr` for the identity is the identity. -/
@[simp]
theorem adicCompletionCongr_one :
    adicCompletionCongr v v (1 : K ≃+* K) (fun _ ↦ rfl) =
      RingEquiv.refl (v.adicCompletion K) := by
  apply RingEquiv.toRingHom_injective
  exact (eq_adicCompletionCongr_of_continuous (fun _ ↦ rfl) continuous_id fun _ ↦ rfl).symm

/- Transporting completions along two field isomorphisms is transport along their composite. -/
@[simp]
theorem adicCompletionCongr_trans {R'' K'' : Type*} [CommRing R''] [IsDedekindDomain R'']
    [Field K''] [Algebra R'' K''] [IsFractionRing R'' K''] (u : HeightOneSpectrum R'')
    (τ : K' ≃+* K'') (hτ : ∀ y, u.valuation K'' (τ y) = w.valuation K' y) :
    (adicCompletionCongr v w σ hσ).trans (adicCompletionCongr w u τ hτ) =
      adicCompletionCongr v u (σ.trans τ) (fun x ↦ by
        rw [RingEquiv.trans_apply, hτ, hσ]) := by
  apply RingEquiv.toRingHom_injective
  apply eq_adicCompletionCongr_of_continuous
  · exact (continuous_adicCompletionCongr hτ).comp (continuous_adicCompletionCongr hσ)
  · intro x
    simp

/- The inverse of `adicCompletionCongr` is the completion of the inverse isomorphism. -/
@[simp]
theorem valued_adicCompletionCongr (x : v.adicCompletion K) :
    Valued.v (adicCompletionCongr v w σ hσ x) = Valued.v x := by
  have hK := Valued.continuous_valuation_of_surjective (valuedAdicCompletion_surjective K v)
  have hK' := Valued.continuous_valuation_of_surjective (valuedAdicCompletion_surjective K' w)
  refine congrFun ((v.denseRange_algebraMap K).equalizer
    (hK'.comp (continuous_adicCompletionCongr hσ)) hK (funext fun y ↦ ?_)) x
  rw [Function.comp_apply, Function.comp_apply, adicCompletionCongr_algebraMap]
  simp only [algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self_apply,
    valuedAdicCompletion_eq_valuation', hσ]

end Completion

end IsDedekindDomain.HeightOneSpectrum
