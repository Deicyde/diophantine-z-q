import ZInQKernel.Contrib.CloudB3RC53.RankCounts.GlobalPrints
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison

/-!
# RankCounts: `H¹` with trivial `𝔽₂²` coefficients is two copies of `H¹` with `𝔽₂` coefficients

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-residual-bound`, tex 4479–4480 and 4521–4523:
the residual coefficient module is `W = E[2] = 𝔽₂²` with trivial action, and
`h¹(G_{K,S₀}, W) ≤ 4s` is read off from `h¹(G_{K,S₀}, 𝔽₂) ≤ 2s` by `h¹(W) = 2 h¹(𝔽₂)`.

Lane RC6 takes this as the GLUE field `h1_eq : h1 = 2 * h1S0F2` of `ResidualRankCounts`
(`ZInQKernel/Contrib/OneProof/RC/Limits/ResidualBound.lean`). Here it is
PROVED for Mathlib's `continuousCohomology` of any topological group, in particular for
`G_{K,S}` (`GaloisGroupS`, `GlobalPrints.lean`): `H1TrivialF2Square`, `RC6H1Eq`.

Proof: for a discrete module with trivial action, `H¹(G, V)` is the group of continuous
homomorphisms `G → V` (Tau Ceti's `explicitH1AddEquivContinuousCohomologyOfDiscrete` and
`H1EquivOfSmulEqSelf`, vendored in this repository), and homomorphisms into `𝔽₂ × 𝔽₂` are pairs of
homomorphisms into `𝔽₂`.

Kinds: everything PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.RankCounts

open CategoryTheory TauCeti.ContCohomology

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul (ZMod 2) V] [DiscreteTopology V]
/-- For a discrete module `V` with trivial action, `H¹(G, V)` is the group of continuous\nhomomorphisms `G → V`. PROVED (Tau Ceti comparison). -/
noncomputable def h1triv : continuousCohomology 1 (trivialRepS G V) ≃+
    Additive (ContinuousMonoidHom G (Multiplicative V)) :=
  letI := TopRep.distribMulAction (trivialRepS G V)
  haveI : DiscreteTopology (trivialRepS G V).V := by assumption
  haveI : ContinuousSMul G (trivialRepS G V).V := ⟨continuous_snd⟩
  (trivialRepS G V).explicitH1AddEquivContinuousCohomologyOfDiscrete.symm.trans
    (H1EquivOfSmulEqSelf (fun g v => rfl))

section Split
variable {G} {A B : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]

def homFst (φ : ContinuousMonoidHom G (Multiplicative (A × B))) :
    ContinuousMonoidHom G (Multiplicative A) where
  toFun g := Multiplicative.ofAdd (Multiplicative.toAdd (φ g)).1
  map_one' := by simp
  map_mul' x y := by simp [map_mul]
  continuous_toFun := continuous_ofAdd.comp (continuous_fst.comp (continuous_toAdd.comp φ.continuous))

def homSnd (φ : ContinuousMonoidHom G (Multiplicative (A × B))) :
    ContinuousMonoidHom G (Multiplicative B) where
  toFun g := Multiplicative.ofAdd (Multiplicative.toAdd (φ g)).2
  map_one' := by simp
  map_mul' x y := by simp [map_mul]
  continuous_toFun := continuous_ofAdd.comp (continuous_snd.comp (continuous_toAdd.comp φ.continuous))

def homPair (a : ContinuousMonoidHom G (Multiplicative A)) (b : ContinuousMonoidHom G (Multiplicative B)) :
    ContinuousMonoidHom G (Multiplicative (A × B)) where
  toFun g := Multiplicative.ofAdd (Multiplicative.toAdd (a g), Multiplicative.toAdd (b g))
  map_one' := by simp
  map_mul' x y := by simp [map_mul]; rfl
  continuous_toFun := continuous_ofAdd.comp
    ((continuous_toAdd.comp a.continuous).prodMk (continuous_toAdd.comp b.continuous))

noncomputable def homSplit : Additive (ContinuousMonoidHom G (Multiplicative (A × B))) ≃+
    Additive (ContinuousMonoidHom G (Multiplicative A)) × Additive (ContinuousMonoidHom G (Multiplicative B)) where
  toFun φ := (Additive.ofMul (homFst φ.toMul), Additive.ofMul (homSnd φ.toMul))
  invFun p := Additive.ofMul (homPair p.1.toMul p.2.toMul)
  left_inv φ := by ext g <;> rfl
  right_inv p := by ext g <;> rfl
  map_add' φ ψ := by ext g <;> rfl

theorem finrank_prod_self (M : Type) [AddCommGroup M] [Module (ZMod 2) M] :
    Module.finrank (ZMod 2) (M × M) = 2 * Module.finrank (ZMod 2) M := by
  by_cases h : Module.Finite (ZMod 2) M
  · rw [Module.finrank_prod]; ring
  · have h' : ¬ Module.Finite (ZMod 2) (M × M) := fun hf =>
      h (Module.Finite.of_surjective (LinearMap.fst (ZMod 2) M M) LinearMap.fst_surjective)
    rw [Module.finrank_of_not_finite h, Module.finrank_of_not_finite h']

/-- `H¹(G, 𝔽₂²) = H¹(G, 𝔽₂)²` in dimension, for trivial actions. PROVED. -/
theorem h1_eq_two_mul :
    Module.finrank (ZMod 2) (continuousCohomology 1 (trivialRepS G (ZMod 2 × ZMod 2))) =
      2 * Module.finrank (ZMod 2) (continuousCohomology 1 (trivialRepS G (ZMod 2))) := by
  let e : continuousCohomology 1 (trivialRepS G (ZMod 2 × ZMod 2)) ≃+
      continuousCohomology 1 (trivialRepS G (ZMod 2)) × continuousCohomology 1 (trivialRepS G (ZMod 2)) :=
    ((h1triv G (ZMod 2 × ZMod 2)).trans homSplit).trans
      (AddEquiv.prodCongr (h1triv G (ZMod 2)).symm (h1triv G (ZMod 2)).symm)
  let eL := e.toLinearEquiv (fun (c : ZMod 2) x => ZMod.map_smul e.toAddMonoidHom c x)
  rw [eL.finrank_eq, finrank_prod_self]

end Split

/-- **`h¹(G, 𝔽₂²) = 2 h¹(G, 𝔽₂)` for trivial coefficients (tex 4523; PROVED).** For every
topological group `G` (in particular `G_{K,S₀}`), with Mathlib's continuous cohomology of the
trivial representations on `W = 𝔽₂ × 𝔽₂` and on `𝔽₂`. (If the cohomology is infinite-dimensional
both sides are `0`.) -/
def H1TrivialF2Square : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    Module.finrank (ZMod 2) (continuousCohomology 1 (trivialRepS G (ZMod 2 × ZMod 2))) =
      2 * Module.finrank (ZMod 2) (continuousCohomology 1 (trivialRepS G (ZMod 2)))

theorem h1TrivialF2Square_proof : H1TrivialF2Square := fun G _ _ _ => h1_eq_two_mul (G := G)

/-- **RC6's field `h1_eq : h1 = 2 * h1S0F2` for `G_{K,S}` (tex 4523; PROVED).** With
`h1 = dim H¹(G_{K,S}, W)`, `W = 𝔽₂²` trivial, and `h1S0F2 = dim H¹(G_{K,S}, 𝔽₂)`, for every number
field `K` and every set `S` of primes (RC6: `S = S₀`). Source of the field text:
`ZInQKernel/Contrib/OneProof/RC/Limits/ResidualBound.lean`. -/
def RC6H1Eq : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))),
    Module.finrank (ZMod 2) (continuousCohomology 1 (trivialRepS (GaloisGroupS K S) (ZMod 2 × ZMod 2))) =
      2 * Module.finrank (ZMod 2) (continuousCohomology 1 (trivialRepS (GaloisGroupS K S) (ZMod 2)))

theorem rc6H1Eq_proof : RC6H1Eq := fun K _ _ S => h1_eq_two_mul (G := GaloisGroupS K S)

end ZInQ.Contrib.CloudB3RC53.RankCounts
