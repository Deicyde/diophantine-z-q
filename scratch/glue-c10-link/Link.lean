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

open CategoryTheory.MonObj
open GlueDescent GlueC10 PkgI3
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
abbrev endE {k : Type} [Field k] {A : AbVar k} (φ : AbVar.End A) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type*) [Field E] [Algebra ℚ_[ℓ] E] : Module.End E (E ⊗[ℚ_[ℓ]] A.V ℓ) :=
  ((AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ]).baseChange E

/-- **The ℓ-independent trace on `V_ℓ ⊗ E`** (from Mumford §19 Thm 4). One integer `t` is the
trace of `φ` on `E ⊗ V_ℓ(A)` for every prime `ℓ ≠ char k` and every field `E ⊇ ℚ_ℓ` over which
`E ⊗ V_ℓ(A)` is finite-dimensional. -/
theorem trace_endE_indep (hM : CharPolyIndepOfEll) {k : Type} [Field k] (A : AbVar k)
    (φ : AbVar.End A) : ∃ t : ℤ, ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (E : Type*) [Field E] [Algebra ℚ_[ℓ] E] [Module.Finite E (E ⊗[ℚ_[ℓ]] A.V ℓ)],
        LinearMap.trace E _ (endE φ ℓ E) = (t : E) := by
  obtain ⟨t, ht⟩ := PkgI3.trace_indep_of_ell hM k A φ
  refine ⟨t, fun ℓ _ hℓ E _ _ _ => ?_⟩
  have : Module.Finite ℚ_[ℓ] (A.V ℓ) := finite_of_baseChange (E := E)
  classical
  let b := Module.Free.chooseBasis ℚ_[ℓ] (A.V ℓ)
  haveI : Fintype (Module.Free.ChooseBasisIndex ℚ_[ℓ] (A.V ℓ)) := Fintype.ofFinite _
  rw [endE, LinearMap.trace_baseChange, ht ℓ hℓ _ b, map_intCast]


/-! ## 4. The descended representation over the coefficient field `C` -/

section Desc

variable {G C : Type*} [Group G] [Field C] (c ε : G → G → C) (a β : G → C)
  (ha : ∀ g h, a g * a h * c g h = ε g h * a (g * h))
  (hβ : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0) (ha1 : a 1 = 1)
  (hβ1 : β 1 = 1)
variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V] (emb : C →+* E)
  (T : G → Module.End E V) (hT : ∀ g h, T g * T h = emb (c g h) • T (g * h)) (hT1 : T 1 = 1)

/-- **`ρ_ℓ(σ) = β(σ)⁻¹ a_σ μ_σ ∘ σ`** (N5 L723-727) with the scalars `a_σ, β(σ), c(σ,τ), ε(σ,τ)`
in the coefficient field `C` and mapped to `E` by the chosen embedding `emb : C → E`
(N5 L719-722); `T σ = μ_σ ∘ σ` on `V = V_ℓ(A) ⊗ E`. -/
def rhoL : Representation E G V :=
  rhoRep T (fun g h => emb (c g h)) (fun g h => emb (ε g h)) (fun g => emb (a g)) (fun g => emb (β g)) hT
    (fun g h => by simp only [← map_mul, ha]) (fun g h => by simp only [← map_mul, hβ])
    (fun g => (map_ne_zero emb).mpr (hβ0 g)) (by simp [rho, ha1, hβ1, hT1])

theorem rhoL_apply (g : G) :
    rhoL c ε a β ha hβ hβ0 ha1 hβ1 emb T hT hT1 g = rho T (fun g => emb (a g)) (fun g => emb (β g)) g :=
  rfl

variable (u : MatrixUnits2 E V) (hu : ∀ g i j, Commute (T g) (u.e i j))

include hu in
theorem rhoL_commute (g : G) (i j : Fin 2) :
    Commute (rhoL c ε a β ha hβ hβ0 ha1 hβ1 emb T hT hT1 g) (u.e i j) :=
  rho_commute T _ _ (u.e i j) (fun g => hu g i j) g

/-- **`r_ℓ`**: the restriction of `ρ_ℓ` to `W = e₀₀ V`, so that `ρ_ℓ ≅ r_ℓ ⊕ r_ℓ`. -/
def rL : Representation E G u.W :=
  subRep u (rhoL c ε a β ha hβ hβ0 ha1 hβ1 emb T hT hT1)
    (rhoL_commute c ε a β ha hβ hβ0 ha1 hβ1 emb T hT hT1 u hu)

end Desc

/-! ## 5. The Frobenius comparison (an input from the surface `A`) and the trace link -/

/-- **The Frobenius comparison at `ℓ` (from the surface `A`; not glue).** For `σ` a Frobenius
lift at a place `v` of good reduction with `ℓ ≠ p`, `Tσ = μ_σ ∘ σ` on `V = V_ℓ(A) ⊗ E`, `Ā = Ā_v`
over the residue field `k`, `α' = N·(μ̄_σ ∘ F) ∈ End(Ā)` (`N ≥ 1` clears the denominator of the
quasi-isogeny `μ_σ`): some `E`-linear isomorphism `Φ : V ≃ E ⊗ V_ℓ(Ā)` carries `N·Tσ` to
`V_ℓ(α')`. In the manuscript `Φ` is the reduction isomorphism (Serre–Tate), and the square
commutes by the Néron mapping property (reduction of `μ_σ`) and because `σ` acts on reduced
points as the relative `p`-Frobenius `F : Ā → Ā^{(p)} = \overline{{}^σA}` (N5 L781-786). -/
def FrobCompare (ℓ : ℕ) [Fact ℓ.Prime] {E V : Type*} [Field E] [Algebra ℚ_[ℓ] E]
    [AddCommGroup V] [Module E V] (Tσ : Module.End E V) {k : Type} [Field k] {A : AbVar k}
    (α : AbVar.End A) (N : ℕ) : Prop :=
  ∃ Φ : V ≃ₗ[E] E ⊗[ℚ_[ℓ]] A.V ℓ, Φ.conj ((N : E) • Tσ) = endE α ℓ E

/-- Under the comparison, `N · tr T(σ) = t`, the ℓ-independent trace of `α'`. -/
theorem trace_T_of_frobCompare (hM : CharPolyIndepOfEll) {k : Type} [Field k] (A : AbVar k)
    (α : AbVar.End A) : ∃ t : ℤ, ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ {E V : Type*} [Field E] [Algebra ℚ_[ℓ] E] [AddCommGroup V] [Module E V]
        [FiniteDimensional E V] (Tσ : Module.End E V) (N : ℕ), FrobCompare ℓ Tσ α N →
        (N : E) * LinearMap.trace E V Tσ = (t : E) := by
  obtain ⟨t, ht⟩ := trace_endE_indep hM A α
  refine ⟨t, fun ℓ _ hℓ E V _ _ _ _ _ Tσ N ⟨Φ, hΦ⟩ => ?_⟩
  have : Module.Finite E (E ⊗[ℚ_[ℓ]] A.V ℓ) := Module.Finite.equiv Φ
  rw [← ht ℓ hℓ E, ← hΦ, LinearMap.trace_conj', map_smul, smul_eq_mul]

/-- **The trace link (GLUE, proved from Mumford §19 Thm 4):
`c_p = ½ · β(σ)⁻¹ a_σ · tr α_σ`.** Given `Ā` and `α' ∈ End(Ā)` there is one integer `t`
(the trace of `α'` on `V_ℓ(Ā)`, the same for every `ℓ ≠ char k`) such that for every prime
`ℓ ≠ char k`, every coefficient field `E ⊇ ℚ_ℓ` with embedding `emb : C → E`, every descent datum
`(T, c, ε, a, β)` and matrix units `u`, and every `σ` whose `T σ` satisfies the Frobenius
comparison with `α'` and `N`:
`tr r_ℓ(σ) = emb(½ · β(σ)⁻¹ a_σ · t/N)`, and `t/N = tr α_σ` for `α_σ = α'/N`. -/
theorem trace_link (hM : CharPolyIndepOfEll) {k : Type} [Field k] (A : AbVar k) (α : AbVar.End A) :
    ∃ t : ℤ, ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ {G C E V : Type*} [Group G] [Field C] [CharZero C] [Field E] [Algebra ℚ_[ℓ] E]
        [AddCommGroup V] [Module E V] [FiniteDimensional E V]
        (c ε : G → G → C) (a β : G → C)
        (ha : ∀ g h, a g * a h * c g h = ε g h * a (g * h))
        (hβ : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0) (ha1 : a 1 = 1)
        (hβ1 : β 1 = 1) (emb : C →+* E) (T : G → Module.End E V)
        (hT : ∀ g h, T g * T h = emb (c g h) • T (g * h)) (hT1 : T 1 = 1)
        (u : MatrixUnits2 E V) (hu : ∀ g i j, Commute (T g) (u.e i j)) (σ : G) (N : ℕ),
        N ≠ 0 → FrobCompare ℓ (T σ) α N →
        LinearMap.trace E u.W (rL c ε a β ha hβ hβ0 ha1 hβ1 emb T hT hT1 u hu σ) =
          emb ((β σ)⁻¹ * a σ * ((t : C) / N) / 2) := by
  obtain ⟨t, ht⟩ := trace_T_of_frobCompare hM A α
  refine ⟨t, fun ℓ _ hℓ G C E V _ _ _ _ _ _ _ _ c ε a β ha hβ hβ0 ha1 hβ1 emb T hT hT1 u hu σ N
    hN hcmp => ?_⟩
  have hNT := ht ℓ hℓ (T σ) N hcmp
  have h2 := trace_eq_two_mul_trace_subRep u (rhoL c ε a β ha hβ hβ0 ha1 hβ1 emb T hT hT1)
    (rhoL_commute c ε a β ha hβ hβ0 ha1 hβ1 emb T hT hT1 u hu) σ
  rw [rhoL_apply, trace_rho] at h2
  change LinearMap.trace E u.W (subRep u _ _ σ) = _
  have hNE : (N : E) ≠ 0 := by
    rw [← map_natCast emb]; exact (map_ne_zero emb).mpr (Nat.cast_ne_zero.mpr hN)
  have h2E : (2 : E) ≠ 0 := by
    rw [← map_ofNat emb 2]; exact (map_ne_zero emb).mpr two_ne_zero
  have hβE : emb (β σ) ≠ 0 := (map_ne_zero emb).mpr (hβ0 σ)
  rw [map_div₀, map_mul, map_mul, map_inv₀, map_div₀, map_intCast, map_natCast, map_ofNat,
    ← hNT, mul_div_cancel_left₀ _ hNE, h2, mul_div_cancel_left₀ _ h2E]

end GlueC10Link
