/-
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from anthropics/fermats-last-theorem, commit 6e837e75,
Definitions/Def_PadicComplex_GaloisAction.lean, lines 14–77.
The recovered upstream Lean file has no in-file copyright/author header;
its notices are recorded in the upstream ATTRIBUTION.md and NOTICE.
Source: https://github.com/anthropics/fermats-last-theorem

Compatibility changes: import the repository's genuine completion/action
instead of the unrelated global-Qbar embedding bridge; omit the final
smul_coe_padicEmbedding lemma; add the exact compatibility proofs with cpAct.
No P2M utility, new notation, or build-time code is imported or introduced.
-/
import ZInQKernel.Contrib.CloudB3W11AxCompletion.CompletionBridge

/-!
# The canonical Galois action on the actual completion, and its cpAct bridge

`SMul` and `DistribMulAction` come from Mathlib's canonical completion
instances. Uniform continuity of the algebraic Galois action makes these
instances genuine. The multiplicative action is proved by completion induction.
The exact equality with `PkgI4.cpAct` is proved below, not assumed.

The root `PadicComplex` API names are retained for the other authors porting
the public Tate/trace proofs; all declarations live in this new supporting file.
-/

set_option autoImplicit false

noncomputable section

open UniformSpace

namespace PadicComplex

variable (p : ℕ) [Fact p.Prime]

abbrev Gal : Type := PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p

theorem isometry_algEquiv (σ : Gal p) : Isometry σ := by
  refine AddMonoidHomClass.isometry_of_norm σ fun x => ?_
  exact (spectralNorm_eq_of_equiv σ x).symm

instance uniformContinuousConstSMul_gal :
    UniformContinuousConstSMul (Gal p) (PadicAlgCl p) :=
  ⟨fun σ => (isometry_algEquiv p σ).uniformContinuous⟩

@[simp]
theorem smul_coe (σ : Gal p) (x : PadicAlgCl p) :
    σ • ((x : ℂ_[p])) = ((σ x : PadicAlgCl p) : ℂ_[p]) :=
  (Completion.coe_smul σ x).symm

theorem continuous_smul_left (σ : Gal p) : Continuous fun x : ℂ_[p] => σ • x :=
  continuous_const_smul σ

theorem uniformContinuous_smul_left (σ : Gal p) : UniformContinuous fun x : ℂ_[p] => σ • x :=
  uniformContinuous_const_smul σ

instance mulSemiringAction : MulSemiringAction (Gal p) ℂ_[p] :=
  { (inferInstance : DistribMulAction (Gal p) ℂ_[p]) with
    smul_one := fun σ => by
      rw [← Completion.coe_one, smul_coe, map_one]
    smul_mul := fun σ x y => by
      refine Completion.induction_on₂ x y ?_ ?_
      · exact isClosed_eq ((continuous_fst.mul continuous_snd).const_smul σ)
          ((continuous_fst.const_smul σ).mul (continuous_snd.const_smul σ))
      · intro a b
        rw [← Completion.coe_mul, smul_coe, smul_coe, smul_coe, map_mul, Completion.coe_mul] }

@[simp]
theorem norm_smul_eq (σ : Gal p) (x : ℂ_[p]) : ‖σ • x‖ = ‖x‖ := by
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq (continuous_norm.comp (continuous_const_smul σ)) continuous_norm
  · intro a
    rw [smul_coe, norm_extends, norm_extends]
    exact (spectralNorm_eq_of_equiv σ a).symm

@[simp]
theorem nnnorm_smul_eq (σ : Gal p) (x : ℂ_[p]) : ‖σ • x‖₊ = ‖x‖₊ :=
  NNReal.eq (norm_smul_eq p σ x)

theorem isometry_smul (σ : Gal p) : Isometry fun x : ℂ_[p] => σ • x :=
  AddMonoidHomClass.isometry_of_norm (MulSemiringAction.toRingHom (Gal p) ℂ_[p] σ)
    (norm_smul_eq p σ)

instance smulCommClass_gal_padic : SMulCommClass (Gal p) ℚ_[p] ℂ_[p] :=
  inferInstance

instance smulCommClass_padic_gal : SMulCommClass ℚ_[p] (Gal p) ℂ_[p] :=
  SMulCommClass.symm _ _ _

@[simp]
theorem smul_algebraMap (σ : Gal p) (q : ℚ_[p]) :
    σ • (algebraMap ℚ_[p] ℂ_[p] q) = algebraMap ℚ_[p] ℂ_[p] q := by
  rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]

abbrev galAlgHom (σ : Gal p) : ℂ_[p] →ₐ[ℚ_[p]] ℂ_[p] :=
  MulSemiringAction.toAlgHom ℚ_[p] ℂ_[p] σ

@[simp]
theorem galAlgHom_apply (σ : Gal p) (x : ℂ_[p]) : galAlgHom p σ x = σ • x := rfl

end PadicComplex

namespace ZInQ.Contrib.CloudB3W11AxCompletion

open ZInQ.Contrib.G9.PkgI4

variable (p : ℕ) [Fact p.Prime]

/-- The canonical Mathlib completion action used by the ported public proofs
is exactly the repository's genuine `Completion.mapRingHom` action. -/
theorem galois_smul_eq_cpAct (σ : GQp p) (x : ℂ_[p]) :
    σ • x = cpAct p σ x := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq (PadicComplex.continuous_smul_left p σ) (continuous_cpAct p σ)
  | ih a => rw [PadicComplex.smul_coe, cpAct_coe]

/-- Ring-hom form of the compatibility, for functorial/action constructions. -/
theorem galois_toRingHom_eq_cpAct (σ : GQp p) :
    MulSemiringAction.toRingHom (GQp p) ℂ_[p] σ = cpAct p σ := by
  ext x
  exact galois_smul_eq_cpAct p σ x

/-- The public `galAlgHom` also has the same underlying map as `cpAct`. -/
theorem galois_galAlgHom_apply_eq_cpAct (σ : GQp p) (x : ℂ_[p]) :
    PadicComplex.galAlgHom p σ x = cpAct p σ x :=
  galois_smul_eq_cpAct p σ x

/-- Convert fixed-element hypotheses between the public action and `cpAct`,
for arbitrary intermediate fields. -/
theorem fixed_galois_smul_iff_cpAct (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (x : ℂ_[p]) :
    (∀ σ ∈ K.fixingSubgroup, σ • x = x) ↔
      (∀ σ ∈ K.fixingSubgroup, cpAct p σ x = x) := by
  simp only [galois_smul_eq_cpAct]

/-- The action conversion also respects the repository's actual cyclotomic
power scalar, without changing the twist or its sign convention. -/
theorem twisted_galois_smul_iff_cpAct (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (i : ℤ) (x : ℂ_[p]) :
    (∀ σ ∈ K.fixingSubgroup, cycPow p σ i • (σ • x) = x) ↔
      (∀ σ ∈ K.fixingSubgroup, cycPow p σ i • cpAct p σ x = x) := by
  simp only [galois_smul_eq_cpAct]

end ZInQ.Contrib.CloudB3W11AxCompletion

end
