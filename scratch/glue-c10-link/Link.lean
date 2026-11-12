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
      ∀ (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [Module.Finite E (E ⊗[ℚ_[ℓ]] A.V ℓ)],
        LinearMap.trace E _ (endE φ ℓ E) = (t : E) := by
  obtain ⟨t, ht⟩ := PkgI3.trace_indep_of_ell hM k A φ
  refine ⟨t, fun ℓ _ hℓ E _ _ _ => ?_⟩
  have : Module.Finite ℚ_[ℓ] (A.V ℓ) := finite_of_baseChange (E := E)
  classical
  let b := Module.Free.chooseBasis ℚ_[ℓ] (A.V ℓ)
  let _ : Fintype (Module.Free.ChooseBasisIndex ℚ_[ℓ] (A.V ℓ)) := Fintype.ofFinite _
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
      ∀ {E V : Type} [Field E] [Algebra ℚ_[ℓ] E] [AddCommGroup V] [Module E V]
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
    ∃ t : ℤ, (∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [Module.Finite E (E ⊗[ℚ_[ℓ]] A.V ℓ)],
        LinearMap.trace E _ (endE α ℓ E) = (t : E)) ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ {G C E V : Type} [Group G] [Field C] [CharZero C] [Field E] [Algebra ℚ_[ℓ] E]
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
  obtain ⟨t', ht'⟩ := trace_endE_indep hM A α
  have htt : ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ {E V : Type} [Field E] [Algebra ℚ_[ℓ] E] [AddCommGroup V] [Module E V]
        [FiniteDimensional E V] (Tσ : Module.End E V) (N : ℕ), FrobCompare ℓ Tσ α N →
        (N : E) * LinearMap.trace E V Tσ = (t' : E) := by
    intro ℓ _ hℓ E V _ _ _ _ _ Tσ N ⟨Φ, hΦ⟩
    have : Module.Finite E (E ⊗[ℚ_[ℓ]] A.V ℓ) := Module.Finite.equiv Φ
    rw [← ht' ℓ hℓ E, ← hΦ, LinearMap.trace_conj', map_smul, smul_eq_mul]
  clear ht t
  refine ⟨t', ht', fun ℓ _ hℓ G C E V _ _ _ _ _ _ _ _ c ε a β ha hβ hβ0 ha1 hβ1 emb T hT hT1 u hu σ N
    hN hcmp => ?_⟩
  have hNT := htt ℓ hℓ (T σ) N hcmp
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


/-! ## 6. Connection to `GlueC10.c10`: its trace hypotheses `hr₃, hr₅` discharged -/

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- `ℓ ≠ p` in a field of characteristic `p`. -/
theorem cast_ne_zero_of_charP {k : Type} [Field k] {p ℓ : ℕ} [CharP k p] (hp : p.Prime)
    (hℓ : ℓ.Prime) (hne : p ≠ ℓ) : (ℓ : k) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff k p ℓ]
  exact fun h => hne ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp h)

/-- **The trace hypothesis of C10, from the link.** For every Frobenius `g` at `p ∉ S`
(`3, 5 ∈ S`) with a Frobenius comparison at `3` and at `5` against one `(Ā, α', N)` over a field
of characteristic `p`, there is one `x = ½ β(g)⁻¹ a_g tr α_g ∈ C` with `tr r₃(g) = ι₃(x)` and
`tr r₅(g) = ι₅(x)` (N5 L788-790: "one element of `C` whose images are the traces of every
`r_ℓ`"). -/
theorem trace_link_three_five (hM : CharPolyIndepOfEll) (S : Finset ℕ) (h3S : 3 ∈ S)
    (h5S : 5 ∈ S) {G C : Type} [Group G] [Field C] [CharZero C]
    (c ε : G → G → C) (a β : G → C) (ha : ∀ g h, a g * a h * c g h = ε g h * a (g * h))
    (hβ : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0) (ha1 : a 1 = 1)
    (hβ1 : β 1 = 1)
    {k₅ V₅ : Type} [Field k₅] [Algebra ℚ_[5] k₅] [AddCommGroup V₅] [Module k₅ V₅]
    [FiniteDimensional k₅ V₅] (ι₅ : C →+* k₅) (T₅ : G → Module.End k₅ V₅)
    (hT₅ : ∀ g h, T₅ g * T₅ h = ι₅ (c g h) • T₅ (g * h)) (hT₅1 : T₅ 1 = 1)
    (u₅ : MatrixUnits2 k₅ V₅) (hu₅ : ∀ g i j, Commute (T₅ g) (u₅.e i j))
    {k₃ V₃ : Type} [Field k₃] [Algebra ℚ_[3] k₃] [AddCommGroup V₃] [Module k₃ V₃]
    [FiniteDimensional k₃ V₃] (ι₃ : C →+* k₃) (T₃ : G → Module.End k₃ V₃)
    (hT₃ : ∀ g h, T₃ g * T₃ h = ι₃ (c g h) • T₃ (g * h)) (hT₃1 : T₃ 1 = 1)
    (u₃ : MatrixUnits2 k₃ V₃) (hu₃ : ∀ g i j, Commute (T₃ g) (u₃.e i j))
    (g : G) (p : ℕ) (hp : p.Prime) (hpS : p ∉ S)
    (hFrob : ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (A : AbVar k) (α : AbVar.End A) (N : ℕ),
      N ≠ 0 ∧ FrobCompare 3 (T₃ g) α N ∧ FrobCompare 5 (T₅ g) α N) :
    ∃ x : C,
      LinearMap.trace k₃ u₃.W (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃ g) = ι₃ x ∧
      LinearMap.trace k₅ u₅.W (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₅ T₅ hT₅ hT₅1 u₅ hu₅ g) = ι₅ x := by
  obtain ⟨k, _, hk, A, α, N, hN, h3, h5⟩ := hFrob
  obtain ⟨t, -, ht⟩ := trace_link hM A α
  have h3k : ((3 : ℕ) : k) ≠ 0 :=
    cast_ne_zero_of_charP hp Nat.prime_three (fun h => hpS (h ▸ h3S))
  have h5k : ((5 : ℕ) : k) ≠ 0 :=
    cast_ne_zero_of_charP hp (by norm_num) (fun h => hpS (h ▸ h5S))
  exact ⟨_, ht 3 h3k c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃ g N hN h3,
    ht 5 h5k c ε a β ha hβ hβ0 ha1 hβ1 ι₅ T₅ hT₅ hT₅1 u₅ hu₅ g N hN h5⟩

/-- **C10 with its abelian-variety trace hypotheses discharged by the link (GLUE, proved from
Chebotarev, Brauer–Nesbitt and Mumford §19 Thm 4).** `GlueC10.c10` is applied with
`r_ℓ = rL …` (the descended representation of B1/C1) and `c := a_f` (the modular coefficients).
Its hypotheses `hr₃, hr₅` are proved:
* `hr₅` from C9 (`h₅`) and Eichler–Shimura at 5 (`hρ₅`);
* `hr₃` from the link: `x = ½ β(g)⁻¹ a_g tr α_g` has `ι₅(x) = tr r₅(g) = ι₅(a_f(p))`, so
  `x = a_f(p)` and `tr r₃(g) = ι₃(x) = ι₃(a_f(p))`.
What remains as hypotheses: the descent data and matrix units (`T_ℓ, c, ε, a, β, u_ℓ`), the
Frobenius comparison `hFrob`, C9 `h₅`, Eichler–Shimura `hρ₅, hρ₃`, continuity and
semisimplicity of `r₃, ρ₃`. -/
theorem c10_of_trace_link (hC : ChebotarevExists) (hBN : BrauerNesbittChar0)
    (hM : CharPolyIndepOfEll) (S : Finset ℕ) (h3S : 3 ∈ S) (h5S : 5 ∈ S)
    (C : Type) [Field C] [CharZero C]
    (c ε : GQ → GQ → C) (a β : GQ → C) (ha : ∀ g h, a g * a h * c g h = ε g h * a (g * h))
    (hβ : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0) (ha1 : a 1 = 1)
    (hβ1 : β 1 = 1) (af : ℕ → C)
    -- ℓ = 5
    (k₅ V₅ W₅ : Type) [Field k₅] [Algebra ℚ_[5] k₅] [AddCommGroup V₅] [Module k₅ V₅]
    [FiniteDimensional k₅ V₅] [AddCommGroup W₅] [Module k₅ W₅] (ι₅ : C →+* k₅)
    (T₅ : GQ → Module.End k₅ V₅) (hT₅ : ∀ g h, T₅ g * T₅ h = ι₅ (c g h) • T₅ (g * h))
    (hT₅1 : T₅ 1 = 1) (u₅ : MatrixUnits2 k₅ V₅) (hu₅ : ∀ g i j, Commute (T₅ g) (u₅.e i j))
    (ρ₅ : Representation k₅ GQ W₅)
    (h₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace k₅ u₅.W (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₅ T₅ hT₅ hT₅1 u₅ hu₅ g) =
        LinearMap.trace k₅ W₅ (ρ₅ g))
    (hρ₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k₅ W₅ (ρ₅ g) = ι₅ (af p))
    -- ℓ = 3
    (k₃ V₃ W₃ ιI κ : Type) [Field k₃] [Algebra ℚ_[3] k₃] [CharZero k₃] [TopologicalSpace k₃]
    [IsTopologicalRing k₃] [T2Space k₃] [AddCommGroup V₃] [Module k₃ V₃]
    [FiniteDimensional k₃ V₃] [AddCommGroup W₃] [Module k₃ W₃] [FiniteDimensional k₃ W₃]
    [Fintype ιI] [DecidableEq ιI] [Fintype κ] [DecidableEq κ] (ι₃ : C →+* k₃)
    (T₃ : GQ → Module.End k₃ V₃) (hT₃ : ∀ g h, T₃ g * T₃ h = ι₃ (c g h) • T₃ (g * h))
    (hT₃1 : T₃ 1 = 1) (u₃ : MatrixUnits2 k₃ V₃) (hu₃ : ∀ g i j, Commute (T₃ g) (u₃.e i j))
    (bV : Module.Basis ιI k₃ u₃.W) (bW : Module.Basis κ k₃ W₃) (ρ₃ : Representation k₃ GQ W₃)
    (hrc : Continuous fun g =>
      LinearMap.toMatrix bV bV (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃ g))
    (hρc : Continuous fun g => LinearMap.toMatrix bW bW (ρ₃ g))
    (hr : IsSemisimpleModule (MonoidAlgebra k₃ GQ)
      (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃).asModule)
    (hρ : IsSemisimpleModule (MonoidAlgebra k₃ GQ) ρ₃.asModule)
    (hρ₃ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k₃ W₃ (ρ₃ g) = ι₃ (af p))
    -- the Frobenius comparison, from the surface `A`
    (hFrob : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (A : AbVar k) (α : AbVar.End A) (N : ℕ),
        N ≠ 0 ∧ FrobCompare 3 (T₃ g) α N ∧ FrobCompare 5 (T₅ g) α N) :
    Nonempty ((rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃).asModule ≃ₗ[MonoidAlgebra k₃ GQ]
      ρ₃.asModule) := by
  refine GlueC10.c10 hC hBN S C af af k₅ u₅.W W₅ ι₅
    (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₅ T₅ hT₅ hT₅1 u₅ hu₅) ρ₅ h₅
    (fun g p hp hpS hg => (h₅ g p hp hpS hg).trans (hρ₅ g p hp hpS hg)) hρ₅
    k₃ u₃.W W₃ ιI κ ι₃ bV bW (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃) ρ₃
    hrc hρc hr hρ ?_ hρ₃
  intro g p hp hpS hg
  obtain ⟨x, hx₃, hx₅⟩ := trace_link_three_five hM S h3S h5S c ε a β ha hβ hβ0 ha1 hβ1
    ι₅ T₅ hT₅ hT₅1 u₅ hu₅ ι₃ T₃ hT₃ hT₃1 u₃ hu₃ g p hp hpS (hFrob g p hp hpS hg)
  have hxa : x = af p := ι₅.injective (hx₅.symm.trans ((h₅ g p hp hpS hg).trans
    (hρ₅ g p hp hpS hg)))
  rw [hx₃, hxa]


/-! ## 8. `FrobCompare` from three squares (the inputs from `A`, separated)

`A, Aσ` abelian varieties over `L` (`Aσ` plays `{}^σA`), `μ' = N μ_σ : Aσ → A` (an isogeny,
genuine `Hom`), `Ā, Ā'` abelian varieties over the residue field `k` (`Ā'` plays
`Ā^{(p)} = \overline{{}^σA}`), `F : Ā → Ā'` (relative Frobenius) and `μ̄' : Ā' → Ā` (the
reduction of `μ'`), all genuine `Hom`s of pkg-I3 abelian varieties. The Galois transport
`σ_* : V_ℓ(A) → V_ℓ(Aσ)` and the reduction isomorphisms `red, red'` are abstract `ℚ_ℓ`-linear
isomorphisms, constrained only by the squares. -/

open CategoryTheory in
/-- Composition of homomorphisms of pkg-I3 abelian varieties (`f` then `g`). -/
def homComp {K : Type} [Field K] {A B C : AbVar K} (f : AbVar.Hom A B) (g : AbVar.Hom B C) :
    AbVar.Hom A C :=
  AbVar.Hom.mk' (f.hom ≫ g.hom)

open CategoryTheory in
/-- `T_ℓ` is functorial for `homComp`. -/
theorem homT_homComp {K : Type} [Field K] {A B C : AbVar K} (ℓ : ℕ) [Fact ℓ.Prime]
    (f : AbVar.Hom A B) (g : AbVar.Hom B C) :
    AbVar.homT (ℓ := ℓ) (homComp f g) = AbVar.homT (ℓ := ℓ) g ∘ₗ AbVar.homT (ℓ := ℓ) f := by
  apply LinearMap.ext; intro x; apply Subtype.ext; funext n
  change Additive.ofMul (Additive.toMul (x.1 n) ≫ (f.hom ≫ g.hom)) =
    Additive.ofMul ((Additive.toMul (x.1 n) ≫ f.hom) ≫ g.hom)
  exact congrArg Additive.ofMul (Category.assoc _ _ _).symm

/-- `V_ℓ(f)`: the `ℚ_ℓ`-linear map of rational Tate modules. -/
abbrev Vmap {K : Type} [Field K] {A B : AbVar K} (ℓ : ℕ) [Fact ℓ.Prime] (f : AbVar.Hom A B) :
    A.V ℓ →ₗ[ℚ_[ℓ]] B.V ℓ :=
  (AbVar.homT (ℓ := ℓ) f).baseChange ℚ_[ℓ]

/-- Conjugation commutes with base change. -/
theorem conj_baseChange {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
    (f : Module.End R M) :
    (e.baseChange R A M N).conj (f.baseChange A) = (e.conj f).baseChange A := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a m
  simp [LinearEquiv.conj_apply]

/-- **`FrobCompare` from the three inputs of the surface `A` (GLUE, proved).**
* `hΨ` (the instantiation of the descent: `T(σ) = μ_σ ∘ σ`, i.e. `N·T(σ) = μ' ∘ σ_*` on
  `V ≅ E ⊗ V_ℓ(A)`);
* `hS1` (Serre–Tate reduction and Frobenius: `red' ∘ σ_* = V_ℓ(F) ∘ red`);
* `hS2` (Néron mapping property: `red ∘ V_ℓ(μ') = V_ℓ(μ̄') ∘ red'`).
Then `FrobCompare ℓ (T σ) α' N` with `α' = μ̄' ∘ F`. -/
theorem frobCompare_of_squares (ℓ : ℕ) [Fact ℓ.Prime] {L k : Type} [Field L] [Field k]
    {A Aσ : AbVar L} (mu : AbVar.Hom Aσ A) {Ab Ab' : AbVar k} (F : AbVar.Hom Ab Ab')
    (mub : AbVar.Hom Ab' Ab) (σs : A.V ℓ ≃ₗ[ℚ_[ℓ]] Aσ.V ℓ) (red : A.V ℓ ≃ₗ[ℚ_[ℓ]] Ab.V ℓ)
    (red' : Aσ.V ℓ ≃ₗ[ℚ_[ℓ]] Ab'.V ℓ)
    (hS1 : red'.toLinearMap ∘ₗ σs.toLinearMap = Vmap ℓ F ∘ₗ red.toLinearMap)
    (hS2 : red.toLinearMap ∘ₗ Vmap ℓ mu = Vmap ℓ mub ∘ₗ red'.toLinearMap)
    {E V : Type} [Field E] [Algebra ℚ_[ℓ] E] [AddCommGroup V] [Module E V]
    (Tσ : Module.End E V) (N : ℕ) (Ψ : V ≃ₗ[E] E ⊗[ℚ_[ℓ]] A.V ℓ)
    (hΨ : Ψ.conj ((N : E) • Tσ) = (Vmap ℓ mu ∘ₗ σs.toLinearMap).baseChange E) :
    FrobCompare ℓ Tσ (homComp F mub : AbVar.End Ab) N := by
  refine ⟨Ψ.trans (red.baseChange ℚ_[ℓ] E _ _), ?_⟩
  have hconj : red.conj (Vmap ℓ mu ∘ₗ σs.toLinearMap) = Vmap ℓ mub ∘ₗ Vmap ℓ F := by
    apply LinearMap.ext; intro x
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    have h2 := LinearMap.congr_fun hS2 (σs (red.symm x))
    have h1 := LinearMap.congr_fun hS1 (red.symm x)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h1 h2
    rw [h2, h1]
  rw [← LinearEquiv.conj_trans]
  change (red.baseChange ℚ_[ℓ] E _ _).conj (Ψ.conj ((N : E) • Tσ)) = _
  rw [hΨ, conj_baseChange, hconj, endE, homT_homComp]
  congr 1
  exact (LinearMap.baseChange_comp _ _).symm

/-! ## 7. Checks -/

/-- `FrobCompare` is satisfiable (non-vacuity): `V = E ⊗ V_ℓ(Ā)`, `Tσ = V_ℓ(α')`, `N = 1`,
`Φ = id`. -/
example (ℓ : ℕ) [Fact ℓ.Prime] {k : Type} [Field k] (A : AbVar k) (α : AbVar.End A)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] : FrobCompare ℓ (endE α ℓ E) α 1 :=
  ⟨LinearEquiv.refl E _, by simp⟩

end GlueC10Link

#print axioms GlueC10Link.trace_eq_two_mul_trace_subRep
#print axioms GlueC10Link.trace_endE_indep
#print axioms GlueC10Link.trace_link
#print axioms GlueC10Link.trace_link_three_five
#print axioms GlueC10Link.c10_of_trace_link
#print axioms GlueC10Link.frobCompare_of_squares
