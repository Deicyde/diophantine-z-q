import ZInQKernel.Contrib.OneProof.RC.EvenJoin.Scoped
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.BlockDescent

/-! A vector obtained by descending the two kinds of blocks is integral at
the fixed place and can be used as the single seed of the scoped model. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine AuxInputs BlocksPerU EvenBudget EvenExpansion NumberField O12 ThetaCoeff
open UpperHalfPlane Wiring IsDedekindDomain
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}
variable {hS : SupportSpec W} {B : ℕ} [NeZero (conductor W.S)]
variable {X : Model P hS B}
variable {F : IntermediateField ℚ ℂ} [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

variable {I J : Type} [Fintype I] {N : ℕ} {avoid : Finset ℕ}
variable (i : Fin 2) (U : Finset ℕ)
variable (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
variable (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1)
variable (Y : Inventory I J X.K (evenTypes W.S hS.1) N)
variable (hc : ∀ q, Test (evenTypes W.S hS.1) avoid q → q.Coprime N)
variable (κ : X.K →+* ℂ) (seed : I → X.K)
variable (heval : ∀ n, κ ((Y.toBasis hc).eval n seed) =
    (qExpansion 1 (joinedForm hS i U hU hodd)).coeff n)

include heval in
/-- The vector from `joined_coordinates_of_block_spans` can be used before
any trace lattice is constructed: its coefficients are already the images
of the fixed integral expansion. -/
theorem joined_vector_coeff_fixedRing (C₀ : SourceAtPlace P (FixedRing v) (FixedField v))
    (E : FixedPlaceExtension v X) (hκ : κ.comp (E.fieldMap.comp C₀.eK) = C₀.eC)
    (n : ℕ) :
    (Y.toBasis hc).eval n seed =
      algebraMap X.O X.K (E.ringMap (timesTheta (fixedH (hS := hS) C₀ i U hU) n)) := by
  apply κ.injective
  rw [heval, E.apply_ringMap]
  have h₀ := commonCoeff_place C₀ hS Subtype.val_injective i U.toList
    U.nodup_toList (fun p hp => hU p (Finset.mem_toList.mp hp)) n
  change _ = κ (E.fieldMap (algebraMap (FixedRing v) (FixedField v)
    (timesTheta (dividedCoeff (source_at_place C₀ hS Subtype.val_injective) i U.toList
      U.nodup_toList (fun p hp => hU p (Finset.mem_toList.mp hp))) n)))
  rw [h₀, ← RingHom.comp_apply E.fieldMap C₀.eK, ← RingHom.comp_apply κ, hκ,
    commonCoeff_complex C₀ hS i U.toList n, joinedForm_coeff hS i U hU hodd n]

include heval in
/-- The actual coordinate premise of the scoped budget producer, using the
column map and seed identities of a model built from this inventory.
No spanning law outside the selected blocks is needed. -/
theorem coordinate_match_of_joined_vector (A : FourierData X)
    (ι : (I → X.K) →ₗ[X.K] (X.I → X.K))
    (hcolumn : ∀ z n, X.coefK (ι z) (A.index n) = (Y.toBasis hc).eval n.val z)
    (hseed : (X.F U).val = ι seed) :
    ∀ n, n ≠ 0 →
      κ (algebraMap X.O X.K (A.coeff n (X.F U))) =
        (qExpansion 1 (joinedForm hS i U hU hodd)).coeff n := by
  intro n hn
  rw [← A.expand_coeff (X.F U) ⟨n, hn⟩, X.expand_spec, hseed, hcolumn]
  exact heval n

end ZInQ.Manuscript.RC.EvenJoin
