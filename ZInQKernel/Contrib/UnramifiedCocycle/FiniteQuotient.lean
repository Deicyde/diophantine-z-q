import ZInQKernel.Contrib.UnramifiedCocycle.CyclicInflation

/-!
# Genuine finite Galois descent and the remaining local cyclic bridge

`InflatedFrom` is the baseline's agreement-on-elements predicate.  This module
proves its descent through the actual restriction `GQ → Gal(L/ℚ)`, and connects
the finite cyclic product cochain to the baseline's actual `resp p`.

The existence of the cyclic unramified quotient and its doubled lift is kept as
an explicit arithmetic obligation.  It is not supplied here as a fact and the
conditional consumer is not a closed proof of `LeafUnramified`.
-/

namespace ZInQ.Contrib.UnramifiedCocycle

open GlueDescent.B2 GlueDescent.B2Q

variable (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ L]

/-- Actual restriction of the global absolute Galois group to the given field. -/
noncomputable def finiteRestriction : GQ →* (L ≃ₐ[ℚ] L) :=
  AlgEquiv.restrictNormalHom L

theorem finiteRestriction_surjective : Function.Surjective (finiteRestriction L) :=
  AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure ℚ)

/-- A set-theoretic section.  It is not misrepresented as a group homomorphism. -/
noncomputable def finiteSection (σ : L ≃ₐ[ℚ] L) : GQ :=
  Classical.choose (finiteRestriction_surjective L σ)

@[simp] theorem finiteRestriction_section (σ : L ≃ₐ[ℚ] L) :
    finiteRestriction L (finiteSection L σ) = σ :=
  Classical.choose_spec (finiteRestriction_surjective L σ)

/-- Equality of actual restrictions gives precisely the baseline's agreement
hypothesis, in both cocycle variables. -/
theorem cocycle_eq_of_restriction_eq (ε : GQ → GQ → ℂˣ) (hi : InflatedFrom L ε)
    (σ σ' τ τ' : GQ) (hσ : finiteRestriction L σ = finiteRestriction L σ')
    (hτ : finiteRestriction L τ = finiteRestriction L τ') : ε σ τ = ε σ' τ' := by
  apply hi σ σ' τ τ'
  · intro x hx
    have h := congrArg (fun f : L ≃ₐ[ℚ] L => (f ⟨x, hx⟩ : AlgebraicClosure ℚ)) hσ
    exact (AlgEquiv.restrictNormal_commutes (act σ) L ⟨x, hx⟩).symm.trans
      (h.trans (AlgEquiv.restrictNormal_commutes (act σ') L ⟨x, hx⟩))
  · intro x hx
    have h := congrArg (fun f : L ≃ₐ[ℚ] L => (f ⟨x, hx⟩ : AlgebraicClosure ℚ)) hτ
    exact (AlgEquiv.restrictNormal_commutes (act τ) L ⟨x, hx⟩).symm.trans
      (h.trans (AlgEquiv.restrictNormal_commutes (act τ') L ⟨x, hx⟩))

/-- The cocycle on the genuine finite Galois group, with choice independence
proved by `finiteCocycle_apply`. -/
noncomputable def finiteCocycle (ε : GQ → GQ → ℂˣ) (σ τ : L ≃ₐ[ℚ] L) : ℂˣ :=
  ε (finiteSection L σ) (finiteSection L τ)

@[simp] theorem finiteCocycle_apply (ε : GQ → GQ → ℂˣ) (hi : InflatedFrom L ε)
    (σ τ : GQ) :
    finiteCocycle L ε (finiteRestriction L σ) (finiteRestriction L τ) = ε σ τ := by
  apply cocycle_eq_of_restriction_eq L ε hi
  · exact finiteRestriction_section L _
  · exact finiteRestriction_section L _

/-- Descent through a surjective homomorphism preserves the actual cocycle law.
The codomain is discrete, so its cochain is automatically locally constant. -/
theorem isSignCocycle_of_surjective_pull {G H U : Type*} [Group G] [Group H]
    [CommGroup U] [TopologicalSpace G] [TopologicalSpace H] [DiscreteTopology H]
    (q : G →* H) (hq : Function.Surjective q) (η : H → H → U)
    (hη : IsSignCocycle (pull q η)) : IsSignCocycle η := by
  refine ⟨IsLocallyConstant.of_discrete _, ?_, ?_⟩
  · intro x y
    obtain ⟨a, rfl⟩ := hq x
    obtain ⟨b, rfl⟩ := hq y
    exact hη.2.1 a b
  · intro x y z
    obtain ⟨a, rfl⟩ := hq x
    obtain ⟨b, rfl⟩ := hq y
    obtain ⟨c, rfl⟩ := hq z
    simpa only [pull, map_mul] using hη.2.2 a b c

variable [FiniteDimensional ℚ L]

/-- No sign, continuity, normalization, or cocycle hypothesis is lost in descent. -/
theorem finiteCocycle_isSignCocycle (ε : GQ → GQ → ℂˣ)
    (hε : IsSignCocycle ε) (hi : InflatedFrom L ε) : IsSignCocycle (finiteCocycle L ε) := by
  apply isSignCocycle_of_surjective_pull (finiteRestriction L)
    (finiteRestriction_surjective L)
  have he : pull (finiteRestriction L) (finiteCocycle L ε) = ε := by
    funext σ τ
    exact finiteCocycle_apply L ε hi σ τ
  rwa [he]

/-- The actual finite action induced by the baseline decomposition-group map. -/
noncomputable def localRestriction (p : Nat.Primes) : GQp p →* (L ≃ₐ[ℚ] L) :=
  (finiteRestriction L).comp (resp p)

/-- A precise sufficient arithmetic bridge.  It contains actual maps, continuity,
and compatibility with the original field's action, not a cohomology-vanishing
assumption.  Constructing this for every unramified `L,p` remains open here. -/
structure LocalCyclicLift (p : Nat.Primes) where
  n : ℕ
  positive : 0 < n
  quotient : GQp p →* CyclicGroup n
  finiteAction : CyclicGroup n →* (L ≃ₐ[ℚ] L)
  lift : GQp p →* CyclicGroup (2 * n)
  lift_continuous : Continuous lift
  lift_compatible : (cyclicReduction n).comp lift = quotient
  action_compatible : finiteAction.comp quotient = localRestriction L p

/-- A constructed arithmetic bridge supplies the *actual* sign coboundary,
with all original cocycle hypotheses unchanged. -/
theorem signCob_of_localCyclicLift (p : Nat.Primes) (D : LocalCyclicLift L p)
    (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε) (hi : InflatedFrom L ε) :
    SignCob (pull (resp p) ε) := by
  let : NeZero D.n := ⟨Nat.ne_of_gt D.positive⟩
  have hfinite := finiteCocycle_isSignCocycle L ε hε hi
  have hcyclic := isSignCocycle_pull D.finiteAction (continuous_of_discreteTopology) hfinite
  have h := signCob_of_cyclicLift D.n D.quotient D.lift D.lift_continuous
    D.lift_compatible (pull D.finiteAction (finiteCocycle L ε)) hcyclic
  have he : pull D.quotient (pull D.finiteAction (finiteCocycle L ε)) =
      pull (resp p) ε := by
    funext x y
    change finiteCocycle L ε ((D.finiteAction.comp D.quotient) x)
      ((D.finiteAction.comp D.quotient) y) = ε (resp p x) (resp p y)
    rw [D.action_compatible]
    exact finiteCocycle_apply L ε hi (resp p x) (resp p y)
  rwa [he] at h

/-- The arithmetic obligation, quantified over exactly the fields and primes in
`LeafUnramified`.  No sign cocycle or coboundary is built into this obligation. -/
def UnramifiedCyclicBridge : Prop :=
  ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (p : Nat.Primes), UnramifiedAt L p → Nonempty (LocalCyclicLift L p)

/-- Exact conditional assembly.  The explicit extra hypothesis is the remaining
arithmetic bridge, so this is not advertised as a closed leaf proof. -/
theorem leafUnramified_of_cyclicBridge (hbridge : UnramifiedCyclicBridge) : LeafUnramified := by
  intro L _ _ ε hε hi p hunr
  obtain ⟨D⟩ := hbridge L p hunr
  exact signCob_of_localCyclicLift L p D ε hε hi

end ZInQ.Contrib.UnramifiedCocycle
