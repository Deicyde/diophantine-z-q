import ZInQKernel.HDecomp.Objects
import ZInQKernel.HDecomp.C10.C10
import ZInQKernel.HDecomp.C10.Trace
import ZInQKernel.HDecomp.Descent.ProjRep

/-!
# glue-c10-link: the trace link of C10 (N5 L776-795)

`c_p = ½ · β(σ)⁻¹ a_σ · tr α_σ`, `α_σ = μ̄_σ ∘ F ∈ End⁰(Ā_v)`.

Objects:
* the descent glue `GlueDescent.rho T a β` (`ρ(σ) = β(σ)⁻¹ a_σ T(σ)`, `T σ = μ_σ ∘ σ`),
  `GlueDescent.rhoRep`, `GlueDescent.MatrixUnits2` (`ρ ≅ r ⊕ r`);
* pkg-I3's abelian varieties `PkgI3.AbVar`, `End`, `V_ℓ`, `homT` and the leaf
  `PkgI3.CharPolyIndepOfEll` (Mumford §19 Thm 4);
* glue-c10's `GlueC10.c10`, `GlueC10.IsFrobAt`, `GlueC10.GQ`.

No `sorry`, no `axiom`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlueDescent GlueC10 PkgI3 PkgI3.AbVar
open scoped TensorProduct

namespace GlueC10Link

/-! ## 1. `r = ρ|_W` and `tr ρ = 2 tr r` -/

section Sub

variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V] (u : MatrixUnits2 E V)
variable {G : Type*} [Monoid G]

/-- The descended two-dimensional representation `r_ℓ`: the restriction of `ρ_ℓ` to
`W = e₀₀ V` (N5 L729-730, "matrix units give `ρ_ℓ ≃ r_ℓ ⊕ r_ℓ`"). -/
def subRep (ρ : Representation E G V) (hc : ∀ g i j, Commute (ρ g) (u.e i j)) :
    Representation E G u.W where
  toFun g := (ρ g).restrict (fun _ hw => u.mapsTo_W ρ hc g hw)
  map_one' := by ext w; simp
  map_mul' g h := by ext w; simp

@[simp] theorem subRep_apply (ρ : Representation E G V) (hc : ∀ g i j, Commute (ρ g) (u.e i j))
    (g : G) (w : u.W) : ((subRep u ρ hc g) w : V) = ρ g w := rfl

/-- Under `V ≃ W × W`, `ρ g` becomes `r g × r g`. -/
theorem conj_splitEquiv (ρ : Representation E G V) (hc : ∀ g i j, Commute (ρ g) (u.e i j))
    (g : G) : u.splitEquiv.conj (ρ g) = LinearMap.prodMap (subRep u ρ hc g) (subRep u ρ hc g) := by
  apply LinearMap.ext
  intro x
  have h := u.splitEquiv_intertwines ρ hc g (u.splitEquiv.symm x)
  rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, h]
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;> simp

/-- **`tr ρ(g) = 2 · tr r(g)`** (the hypothesis `h2` of `GlueC10.trace_half`, now proved from
the matrix units). -/
theorem trace_eq_two_mul_trace_subRep [FiniteDimensional E V] (ρ : Representation E G V)
    (hc : ∀ g i j, Commute (ρ g) (u.e i j)) (g : G) :
    LinearMap.trace E V (ρ g) = 2 * LinearMap.trace E u.W (subRep u ρ hc g) := by
  rw [← LinearMap.trace_conj' (ρ g) u.splitEquiv, conj_splitEquiv u ρ hc g,
    LinearMap.trace_prodMap']
  ring

end Sub

/-! ## 2. `tr ρ(σ) = β(σ)⁻¹ a_σ tr T(σ)` -/

theorem trace_rho {G E V : Type*} [Field E] [AddCommGroup V] [Module E V]
    (T : G → Module.End E V) (a β : G → E) (g : G) :
    LinearMap.trace E V (rho T a β g) = (β g)⁻¹ * a g * LinearMap.trace E V (T g) := by
  simp [rho, map_smul, smul_eq_mul]

/-! ## 3. The trace of an endomorphism of an abelian variety on `V_ℓ ⊗ E` -/

/-- If `E ⊗_K M` is finite over `E` then `M` is finite over `K` (fields). -/
theorem finite_of_baseChange {K E M : Type*} [Field K] [Field E] [Algebra K E] [AddCommGroup M]
    [Module K M] [Module.Finite E (E ⊗[K] M)] : Module.Finite K M := by
  let b := Module.Free.chooseBasis K M
  have : Finite (Module.Free.ChooseBasisIndex K M) :=
    Module.Finite.finite_basis (Algebra.TensorProduct.basis E b)
  exact Module.Finite.of_basis b

/-- `V_ℓ(φ)` extended to `E ⊗_{ℚ_ℓ} V_ℓ(Ā)`, for a field `E ⊇ ℚ_ℓ`. -/
abbrev endE {k : Type} [Field k] {A : AbVar k} (φ : End A) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type*) [Field E] [Algebra ℚ_[ℓ] E] : Module.End E (E ⊗[ℚ_[ℓ]] A.V ℓ) :=
  ((homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ]).baseChange E

/-- **The ℓ-independent trace on `V_ℓ ⊗ E`** (from Mumford §19 Thm 4). One integer `t` is the
trace of `φ` on `E ⊗ V_ℓ(A)` for every prime `ℓ ≠ char k` and every field `E ⊇ ℚ_ℓ` over which
`E ⊗ V_ℓ(A)` is finite-dimensional. -/
theorem trace_endE_indep (hM : CharPolyIndepOfEll) {k : Type} [Field k] (A : AbVar k)
    (φ : End A) : ∃ t : ℤ, ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (E : Type*) [Field E] [Algebra ℚ_[ℓ] E] [Module.Finite E (E ⊗[ℚ_[ℓ]] A.V ℓ)],
        LinearMap.trace E _ (endE φ ℓ E) = (t : E) := by
  obtain ⟨t, ht⟩ := PkgI3.trace_indep_of_ell hM k A φ
  refine ⟨t, fun ℓ _ hℓ E _ _ _ => ?_⟩
  have : Module.Finite ℚ_[ℓ] (A.V ℓ) := finite_of_baseChange (E := E)
  classical
  let b := Module.Free.chooseBasis ℚ_[ℓ] (A.V ℓ)
  haveI : Fintype (Module.Free.ChooseBasisIndex ℚ_[ℓ] (A.V ℓ)) := Fintype.ofFinite _
  rw [endE, LinearMap.trace_baseChange, ht ℓ hℓ _ b, map_intCast]

end GlueC10Link
