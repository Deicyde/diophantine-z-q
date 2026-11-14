-- (leaf-fold2: copied from scratch/g0-assemble2/parts/a85_linked.lean; 0 HDec name-resolution edits)
/-! ## g0-assemble2: `LinkedTateData` reduced (g14-trace, g15-ram)

* kernel `ZInQKernel/HDecomp/C10/Link.lean` lines 26-473 (verbatim; namespace `GlueC10Link`, not in
  Leaves.lean; its imports `C10.C10`, `C10.Trace`, `Descent.ProjRep` are in Leaves.lean);
* scratch/g14-trace/part_g14.lean lines 26-348 (verbatim; namespace `G14Trace`);
* scratch/g15-ram/G15Ram.lean lines 88-1386 (verbatim; §1-§3, namespace `G15Ram`; its lines 31-86
  are copies of g0-mod-galois' `G11Out` and g0-mod-newform's `U0`, `LocalRamG`, `G15RamG`, parts 70, 77);
* new (g0-assemble2): `LocalRamWild` from `LocalData` (the first two bullets of g15-ram's
  `localRamG_of`, without G11), the joint glue `LinkedTateLocal`, and `LinkedTateData` from it and T7.
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

set_option synthInstance.maxHeartbeats 400000 in
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
  rhoRep T (fun g h => emb (c g h)) (fun g h => emb (ε g h)) (fun g => emb (a g)) (fun g => emb (β
      g)) hT
    (fun g h => by simp only [← map_mul, ha]) (fun g h => by simp only [← map_mul, hβ])
    (fun g => (map_ne_zero emb).mpr (hβ0 g)) (by simp [rho, ha1, hβ1, hT1])

theorem rhoL_apply (g : G) :
    rhoL c ε a β ha hβ hβ0 ha1 hβ1 emb T hT hT1 g = rho T (fun g => emb (a g)) (fun g => emb (β g))
        g :=
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
  refine ⟨t', ht', fun ℓ _ hℓ G C E V _ _ _ _ _ _ _ _ c ε a β ha hβ hβ0 ha1 hβ1 emb T hT hT1 u hu σ
      N
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


/-- The three inputs of `frobCompare_of_squares` at one `ℓ`, for given `μ', F, μ̄'`. -/
def FrobSquares (ℓ : ℕ) [Fact ℓ.Prime] {L k : Type} [Field L] [Field k]
    {A Aσ : AbVar L} (mu : AbVar.Hom Aσ A) {Ab Ab' : AbVar k} (F : AbVar.Hom Ab Ab')
    (mub : AbVar.Hom Ab' Ab) {E V : Type} [Field E] [Algebra ℚ_[ℓ] E] [AddCommGroup V]
    [Module E V] (Tσ : Module.End E V) (N : ℕ) : Prop :=
  ∃ (σs : A.V ℓ ≃ₗ[ℚ_[ℓ]] Aσ.V ℓ) (red : A.V ℓ ≃ₗ[ℚ_[ℓ]] Ab.V ℓ)
    (red' : Aσ.V ℓ ≃ₗ[ℚ_[ℓ]] Ab'.V ℓ) (Ψ : V ≃ₗ[E] E ⊗[ℚ_[ℓ]] A.V ℓ),
    red'.toLinearMap ∘ₗ σs.toLinearMap = Vmap ℓ F ∘ₗ red.toLinearMap ∧
    red.toLinearMap ∘ₗ Vmap ℓ mu = Vmap ℓ mub ∘ₗ red'.toLinearMap ∧
    Ψ.conj ((N : E) • Tσ) = (Vmap ℓ mu ∘ₗ σs.toLinearMap).baseChange E

theorem frobCompare_of_frobSquares (ℓ : ℕ) [Fact ℓ.Prime] {L k : Type} [Field L] [Field k]
    {A Aσ : AbVar L} (mu : AbVar.Hom Aσ A) {Ab Ab' : AbVar k} (F : AbVar.Hom Ab Ab')
    (mub : AbVar.Hom Ab' Ab) {E V : Type} [Field E] [Algebra ℚ_[ℓ] E] [AddCommGroup V]
    [Module E V] (Tσ : Module.End E V) (N : ℕ) (h : FrobSquares ℓ mu F mub Tσ N) :
    FrobCompare ℓ Tσ (homComp F mub : AbVar.End Ab) N := by
  obtain ⟨σs, red, red', Ψ, h1, h2, hΨ⟩ := h
  exact frobCompare_of_squares ℓ mu F mub σs red red' h1 h2 Tσ N Ψ hΨ

/-- **C10 from the squares (GLUE, proved from Chebotarev, Brauer–Nesbitt, Mumford §19 Thm 4).**
`c10_of_trace_link` with the Frobenius comparison replaced by its three inputs: for every
Frobenius `g` at `p ∉ S` there are abelian varieties `A, Aσ` over a field `L`, an isogeny
`μ' : Aσ → A`, abelian varieties `Ā, Ā'` over a field `k` of characteristic `p`, homomorphisms
`F : Ā → Ā'`, `μ̄' : Ā' → Ā`, and `N ≠ 0`, with `FrobSquares` at `ℓ = 3` and `ℓ = 5`. -/
theorem c10_of_squares (hC : ChebotarevExists) (hBN : BrauerNesbittChar0)
    (hM : CharPolyIndepOfEll) (S : Finset ℕ) (h3S : 3 ∈ S) (h5S : 5 ∈ S)
    (C : Type) [Field C] [CharZero C]
    (c ε : GQ → GQ → C) (a β : GQ → C) (ha : ∀ g h, a g * a h * c g h = ε g h * a (g * h))
    (hβ : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0) (ha1 : a 1 = 1)
    (hβ1 : β 1 = 1) (af : ℕ → C)
    (k₅ V₅ W₅ : Type) [Field k₅] [Algebra ℚ_[5] k₅] [AddCommGroup V₅] [Module k₅ V₅]
    [FiniteDimensional k₅ V₅] [AddCommGroup W₅] [Module k₅ W₅] (ι₅ : C →+* k₅)
    (T₅ : GQ → Module.End k₅ V₅) (hT₅ : ∀ g h, T₅ g * T₅ h = ι₅ (c g h) • T₅ (g * h))
    (hT₅1 : T₅ 1 = 1) (u₅ : MatrixUnits2 k₅ V₅) (hu₅ : ∀ g i j, Commute (T₅ g) (u₅.e i j))
    (ρ₅ : Representation k₅ GQ W₅)
    (h₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace k₅ u₅.W (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₅ T₅ hT₅ hT₅1 u₅ hu₅ g) =
        LinearMap.trace k₅ W₅ (ρ₅ g))
    (hρ₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k₅ W₅ (ρ₅ g) = ι₅ (af p))
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
    (hSq : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      ∃ (L : Type) (_ : Field L) (k : Type) (_ : Field k), CharP k p ∧
        ∃ (A Aσ : AbVar L) (mu : AbVar.Hom Aσ A) (Ab Ab' : AbVar k) (F : AbVar.Hom Ab Ab')
          (mub : AbVar.Hom Ab' Ab) (N : ℕ), N ≠ 0 ∧
          FrobSquares 3 mu F mub (T₃ g) N ∧ FrobSquares 5 mu F mub (T₅ g) N) :
    Nonempty ((rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃).asModule ≃ₗ[MonoidAlgebra k₃ GQ]
      ρ₃.asModule) := by
  refine c10_of_trace_link hC hBN hM S h3S h5S C c ε a β ha hβ hβ0 ha1 hβ1 af k₅ V₅ W₅ ι₅ T₅ hT₅
    hT₅1 u₅ hu₅ ρ₅ h₅ hρ₅ k₃ V₃ W₃ ιI κ ι₃ T₃ hT₃ hT₃1 u₃ hu₃ bV bW ρ₃ hrc hρc hr hρ hρ₃ ?_
  intro g p hp hpS hg
  obtain ⟨L, _, k, _, hk, A, Aσ, mu, Ab, Ab', F, mub, N, hN, h3, h5⟩ := hSq g p hp hpS hg
  exact ⟨k, inferInstance, hk, Ab, homComp F mub, N, hN,
    frobCompare_of_frobSquares 3 mu F mub (T₃ g) N h3,
    frobCompare_of_frobSquares 5 mu F mub (T₅ g) N h5⟩

/-! ## 7. Checks -/

/-- `FrobCompare` is satisfiable (non-vacuity): `V = E ⊗ V_ℓ(Ā)`, `Tσ = V_ℓ(α')`, `N = 1`,
`Φ = id`. -/
example (ℓ : ℕ) [Fact ℓ.Prime] {k : Type} [Field k] (A : AbVar k) (α : AbVar.End A)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] : FrobCompare ℓ (endE α ℓ E) α 1 :=
  ⟨LinearEquiv.refl E _, by simp⟩

end GlueC10Link
end

noncomputable section

namespace G14Trace

open PkgI4 (Qbar GQ LiesOver IsArithFrob GaloisRep)
open PkgI3 G0ModNewform GlueC10Link

/-! ## §1. G7Out at one `ℓ` does not fix the traces: twisting `a` (proved) -/

section Twist

variable {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime]

/-- (copied from g0-mod-galois, `part_galois.lean`, as in g0-mod-field's `GaloisCopy`)
G7's output at the coefficient prime `ℓ`. -/
def G7Out (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ))
    (c ε : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β : PkgI4.GQ → PadicAlgCl ℓ)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (Vb A ℓ)) : Prop :=
  A.dim = 2 ∧ Module.finrank ℤ (PkgI3.AbVar.End A) = 4 ∧
  (∀ g h, Tm g * Tm h = c g h • Tm (g * h)) ∧
  (∀ g h, a g * a h * c g h = ε g h * a (g * h)) ∧
  (∀ g h, β g * β h = ε g h * β (g * h)) ∧ (∀ g, β g ≠ 0) ∧
  (∀ σ, Tm (resQ K σ) = tate A ℓ σ ∧ a (resQ K σ) = 1 ∧ β (resQ K σ) = 1) ∧
  (∀ g i j, Commute (Tm g) (u.e i j)) ∧
  (∀ (f : Module.Dual (PadicAlgCl ℓ) (Vb A ℓ)) (v : Vb A ℓ),
    Continuous fun g => f (GlueDescent.rho Tm a β g v))

/-- **Twisting G7's output (proved).** If `χ : G_ℚ → ℚ̄_ℓ^×` is a continuous character trivial on
`G_K` (a character of `Gal(K/ℚ)`), then `(Tm, c, ε, χ·a, β, u)` satisfies `G7Out` whenever
`(Tm, c, ε, a, β, u)` does. -/
theorem g7Out_twist (Tm : GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ))
    (c ε : GQ → GQ → PadicAlgCl ℓ) (a β : GQ → PadicAlgCl ℓ)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (Vb A ℓ)) (h : G7Out A ℓ Tm c ε a β u)
    (χ : GQ →* (PadicAlgCl ℓ)ˣ) (hχc : Continuous χ) (hχ : ∀ σ, χ (resQ K σ) = 1) :
    G7Out A ℓ Tm c ε (fun g => (χ g : PadicAlgCl ℓ) * a g) β u := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨h1, h2, h3, fun g k => ?_, h5, h6, fun σ => ?_, h8, fun f v => ?_⟩
  · simp only [map_mul, Units.val_mul]
    linear_combination (χ g : PadicAlgCl ℓ) * (χ k) * h4 g k
  · obtain ⟨t1, t2, t3⟩ := h7 σ
    exact ⟨t1, by simp only [t2, hχ σ, Units.val_one, mul_one], t3⟩
  · have hc : Continuous fun g => (χ g : PadicAlgCl ℓ) :=
      Units.continuous_val.comp hχc
    have : (fun g => f (GlueDescent.rho Tm (fun g => (χ g : PadicAlgCl ℓ) * a g) β g v)) =
        fun g => (χ g : PadicAlgCl ℓ) * f (GlueDescent.rho Tm a β g v) := by
      funext g
      simp only [GlueDescent.rho, LinearMap.smul_apply, map_smul, smul_eq_mul]
      ring
    rw [this]
    exact hc.mul (h9 f v)

/-- The twist multiplies the traces of `ρ = β⁻¹ a Tm` by `χ`. -/
theorem trace_rho_twist (Tm : GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ))
    (a β : GQ → PadicAlgCl ℓ) (χ : GQ → PadicAlgCl ℓ) (g : GQ) :
    LinearMap.trace _ _ (GlueDescent.rho Tm (fun g => χ g * a g) β g) =
      χ g * LinearMap.trace _ _ (GlueDescent.rho Tm a β g) := by
  rw [trace_rho, trace_rho]
  ring

end Twist

/-- **The twist obstruction (proved).** If data `D` and `D'` share `r₅`, `ι₅`, `ι₃`, and the traces
of `D'.r₃` are those of `D.r₃` times `χ`, then `G14TraceCompat` for both forces
`(χ(τ) − 1)·tr r₃(τ) = 0` at almost every arithmetic Frobenius `τ` at which `tr r₅(τ)` is
algebraic (all but finitely many, by G13). So at most one twist of `r₃` by a character of
`Gal(K/ℚ)` can satisfy `G14TraceCompat`, unless `r₃` is isomorphic to its twist; which one is
fixed by the descent data, not by `G7Out` at `ℓ = 3` (`g7Out_twist`). -/
theorem twist_obstruction {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    (D D' : ModData K A) (h5 : D'.r5 = D.r5) (hι5 : D'.ι5 = D.ι5) (hι3 : D'.ι3 = D.ι3)
    (χ : GQ → PadicAlgCl 3) (htw : ∀ τ, (D'.r3.mat τ).trace = χ τ * (D.r3.mat τ).trace)
    (hc : G14TraceCompat D) (hc' : G14TraceCompat D') :
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p → IsArithFrob τ v p → ∀ c : Qbar, (D.r5.mat τ).trace = D.ι5 c →
        (χ τ - 1) * (D.r3.mat τ).trace = 0 := by
  obtain ⟨S, hS⟩ := hc
  obtain ⟨S', hS'⟩ := hc'
  refine ⟨S ∪ S', fun p hp hpS v τ hv hτ c hc5 => ?_⟩
  have h1 := hS p hp (fun h => hpS (Finset.mem_union_left _ h)) v τ hv hτ c hc5
  have h2 := hS' p hp (fun h => hpS (Finset.mem_union_right _ h)) v τ hv hτ c
    (by rw [h5, hι5]; exact hc5)
  rw [htw, hι3, ← h1] at h2
  linear_combination h2

/-! ## §2. Traces through G8's intertwining (proved) -/

/-- If `e : V ≃ ℚ̄_ℓ² × ℚ̄_ℓ²` intertwines `f g` with `m g ⊕ m g`, then `tr f(g) = 2 tr m(g)`. -/
theorem trace_of_intertwines {ℓ : ℕ} [Fact ℓ.Prime] {G V : Type*} [AddCommGroup V]
    [Module (PadicAlgCl ℓ) V] (f : G → Module.End (PadicAlgCl ℓ) V)
    (m : G → Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))
    (e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ))
    (h : Intertwines f m e) (g : G) :
    LinearMap.trace (PadicAlgCl ℓ) V (f g) = 2 * (m g).trace := by
  haveI : Module.Finite (PadicAlgCl ℓ) V := Module.Finite.equiv e.symm
  have hconj : e.conj (f g) = LinearMap.prodMap (Matrix.toLin' (m g)) (Matrix.toLin' (m g)) := by
    apply LinearMap.ext
    intro x
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h g, LinearEquiv.apply_symm_apply,
      LinearMap.prodMap_apply, Matrix.toLin'_apply]
  rw [← LinearMap.trace_conj' (f g) e, hconj, LinearMap.trace_prodMap', Matrix.trace_toLin'_eq]
  ring

/-- One coefficient prime: if `N·tr T = t` and `tr(β⁻¹ a T) = 2 tr m` (images of
`a, β ∈ ℚ̄` under `j`), then `tr m = j(½ β⁻¹ a t/N)`. -/
theorem trace_eq_image {ℓ : ℕ} [Fact ℓ.Prime] (j : Qbar →ₐ[ℚ] PadicAlgCl ℓ) {V : Type*}
    [AddCommGroup V] [Module (PadicAlgCl ℓ) V] (T : Module.End (PadicAlgCl ℓ) V) (a β : Qbar)
    (N : ℕ) (hN : N ≠ 0) (t : ℤ) (hNT : (N : PadicAlgCl ℓ) * LinearMap.trace _ V T = t)
    (m : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))
    (h2 : LinearMap.trace _ V (((j β)⁻¹ * j a) • T) = 2 * m.trace) :
    m.trace = j ((β)⁻¹ * a * ((t : Qbar) / N) / 2) := by
  have hNE : (N : PadicAlgCl ℓ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hT : LinearMap.trace _ V T = (t : PadicAlgCl ℓ) / N := by
    rw [eq_div_iff hNE, mul_comm, hNT]
  rw [map_smul, smul_eq_mul, hT] at h2
  rw [map_div₀, map_mul, map_mul, map_inv₀, map_div₀, map_intCast, map_natCast, map_ofNat]
  linear_combination (-1 / 2 : PadicAlgCl ℓ) * h2

/-! ## §3. The AV-side glue Props -/

/-- **The Frobenius trace link (GLUE, AV side; N5 L781-786).** There is a finite set `S` of
primes such that at every arithmetic Frobenius `τ` above `p ∉ S` there are an abelian variety
`Ā` over a field `k` of characteristic `p`, an endomorphism `α'` of `Ā` and `N ≠ 0` with
`FrobCompare` (kernel, `GlueC10Link`) at `ℓ = 3` and at `ℓ = 5`: some isomorphism
`ℚ̄_ℓ ⊗ V_ℓ(A) ≃ ℚ̄_ℓ ⊗ V_ℓ(Ā)` carries `N·Tm_ℓ(τ)` to `V_ℓ(α')`. In N5, `S = T ∪ {3, 5}`
(`T` = bad primes of `A/L'`), `Ā` is the reduction of `A` at the place `v ∩ L'`, `α' = N·(μ̄_τ ∘ F)`
(relative `p`-Frobenius `F`, reduction `μ̄_τ` of the isogeny `μ_τ : {}^τA → A`, defined over
`L ⊆ L'` by N5 L638-640), and the
isomorphism is the Serre–Tate reduction isomorphism. It concerns the operators `Tm_ℓ` that
g0-mod-field's `TateBridge` builds from the points-level `m_σ = μ_σ ∘ σ` (one `m_σ` for all `ℓ`). -/
def FrobTraceLink {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3)) : Prop :=
  ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ),
    LiesOver v p → IsArithFrob τ v p →
    ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (Ab : PkgI3.AbVar k) (α : PkgI3.AbVar.End Ab)
      (N : ℕ), N ≠ 0 ∧ FrobCompare 3 (Tm3 τ) α N ∧ FrobCompare 5 (Tm5 τ) α N

/-- **The Frobenius link in square form (GLUE, AV side; N5 L781-786).** As `FrobTraceLink`, with
`FrobCompare` replaced by its three inputs (kernel, `GlueC10Link.FrobSquares`): abelian
varieties `A₀, Aσ` over a field `L` (intended instance `A₀ = A`, `Aσ = {}^τA`; they are
existential and tied to `A` only through `Ψ`, so this Prop is no stronger than `FrobTraceLink`),
an isogeny `μ' : Aσ → A₀` (`N μ_τ`), abelian varieties `Ā, Ā'` over `k` of characteristic `p` (`Ā = Ā_v`,
`Ā' = Ā^{(p)}`), the relative Frobenius `F : Ā → Ā'` and the reduction `μ̄' : Ā' → Ā` of `μ'`,
with the three squares (descent instantiation `N·Tm_ℓ(τ) = μ' ∘ τ_*`; Serre–Tate
`red' ∘ τ_* = V_ℓ(F) ∘ red`; Néron mapping `red ∘ V_ℓ(μ') = V_ℓ(μ̄') ∘ red'`) at `ℓ = 3, 5`. -/
def FrobSquaresLink {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3)) : Prop :=
  ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ),
    LiesOver v p → IsArithFrob τ v p →
    ∃ (L : Type) (_ : Field L) (k : Type) (_ : Field k), CharP k p ∧
      ∃ (A₀ Aσ : PkgI3.AbVar L) (mu : PkgI3.AbVar.Hom Aσ A₀) (Ab Ab' : PkgI3.AbVar k)
        (F : PkgI3.AbVar.Hom Ab Ab') (mub : PkgI3.AbVar.Hom Ab' Ab) (N : ℕ), N ≠ 0 ∧
        FrobSquares 3 mu F mub (Tm3 τ) N ∧ FrobSquares 5 mu F mub (Tm5 τ) N

/-- `FrobSquaresLink ⇒ FrobTraceLink` (proved, kernel's `frobCompare_of_frobSquares`). -/
theorem frobTraceLink_of_squares {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3)) (h : FrobSquaresLink A Tm5 Tm3) :
    FrobTraceLink A Tm5 Tm3 := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, fun p hp hpS v τ hv hτ => ?_⟩
  obtain ⟨L, _, k, _, hk, A₀, Aσ, mu, Ab, Ab', F, mub, N, hN, h3, h5⟩ := hS p hp hpS v τ hv hτ
  exact ⟨k, inferInstance, hk, Ab, homComp F mub, N, hN,
    frobCompare_of_frobSquares 3 mu F mub (Tm3 τ) N h3,
    frobCompare_of_frobSquares 5 mu F mub (Tm5 τ) N h5⟩

/-! ## §4. One algebraic number for both traces (proved from T7) -/

/-- **The common trace (GLUE, proved from T7, `FrobTraceLink` and the scalar link).** With
`ρ_ℓ = β_ℓ⁻¹ a_ℓ Tm_ℓ`, `a_ℓ = j_ℓ ∘ a`, `β_ℓ = j_ℓ ∘ β`, and G8's intertwining of `ρ_ℓ` with
`r_ℓ ⊕ r_ℓ` at `ℓ = 3, 5`: outside a finite set, at every arithmetic Frobenius `τ`, the traces of
`r₅(τ)` and `r₃(τ)` are `j₅(x)` and `j₃(x)` for one `x = ½ β(τ)⁻¹ a(τ) tr(α')/N ∈ ℚ̄`. -/
theorem common_trace (hM : CharPolyIndepOfEll) {K : Type} [Field K] [NumberField K]
    (A : PkgI3.AbVar K) (j5 : Qbar →ₐ[ℚ] PadicAlgCl 5) (j3 : Qbar →ₐ[ℚ] PadicAlgCl 3)
    (a β : GQ → Qbar)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3)) (r5 : GaloisRep 5 2) (r3 : GaloisRep 3 2)
    (h5 : GalG8Out A 5 (GlueDescent.rho Tm5 (fun g => j5 (a g)) (fun g => j5 (β g))) r5)
    (h3 : GalG8Out A 3 (GlueDescent.rho Tm3 (fun g => j3 (a g)) (fun g => j3 (β g))) r3)
    (hF : FrobTraceLink A Tm5 Tm3) :
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p → IsArithFrob τ v p →
        ∃ x : Qbar, (r5.mat τ).trace = j5 x ∧ (r3.mat τ).trace = j3 x := by
  obtain ⟨S, hS⟩ := hF
  obtain ⟨-, e5, he5, -⟩ := h5
  obtain ⟨-, e3, he3, -⟩ := h3
  haveI : Module.Finite (PadicAlgCl 5) (Vb A 5) := Module.Finite.equiv e5.symm
  haveI : Module.Finite (PadicAlgCl 3) (Vb A 3) := Module.Finite.equiv e3.symm
  refine ⟨S ∪ {3, 5}, fun p hp hpS v τ hv hτ => ?_⟩
  have hpS1 : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
  have hp3 : p ≠ 3 := fun h => hpS (Finset.mem_union_right _ (by simp [h]))
  have hp5 : p ≠ 5 := fun h => hpS (Finset.mem_union_right _ (by simp [h]))
  obtain ⟨k, _, hk, Ab, α, N, hN, hc3, hc5⟩ := hS p hp hpS1 v τ hv hτ
  obtain ⟨t, ht⟩ := trace_T_of_frobCompare hM Ab α
  have hk3 : ((3 : ℕ) : k) ≠ 0 := cast_ne_zero_of_charP hp Nat.prime_three hp3
  have hk5 : ((5 : ℕ) : k) ≠ 0 := cast_ne_zero_of_charP hp (by norm_num) hp5
  have t5 := ht 5 hk5 (Tm5 τ) N hc5
  have t3 := ht 3 hk3 (Tm3 τ) N hc3
  refine ⟨(β τ)⁻¹ * a τ * ((t : Qbar) / N) / 2, ?_, ?_⟩
  · refine trace_eq_image j5 (Tm5 τ) (a τ) (β τ) N hN t t5 (r5.mat τ) ?_
    exact trace_of_intertwines _ r5.mat e5 he5 τ
  · refine trace_eq_image j3 (Tm3 τ) (a τ) (β τ) N hN t t3 (r3.mat τ) ?_
    exact trace_of_intertwines _ r3.mat e3 he3 τ

/-! ## §5. Choosing `ι₃` compatibly with Pan's `ι₅` (proved) -/

/-- Any two `ℚ`-embeddings of `ℚ̄` into a field differ by an endomorphism of `ℚ̄`:
`ι = j ∘ γ` (`ι(x)` is a root of the minimal polynomial of `x`, which splits in `j(ℚ̄)`). -/
theorem exists_comp_eq {F : Type*} [Field F] [Algebra ℚ F] (ι j : Qbar →ₐ[ℚ] F) :
    ∃ γ : Qbar →ₐ[ℚ] Qbar, ι = j.comp γ := by
  have hmem : ∀ x : Qbar, ∃ y : Qbar, j y = ι x := by
    intro x
    have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    set P := minpoly ℚ x with hP
    have hP0 : P.map (algebraMap ℚ Qbar) ≠ 0 :=
      Polynomial.map_ne_zero (minpoly.ne_zero hint)
    have hroot : ((P.map (algebraMap ℚ Qbar)).map (j : Qbar →+* F)).IsRoot (ι x) := by
      rw [Polynomial.map_map, j.comp_algebraMap, Polynomial.IsRoot, Polynomial.eval_map_algebraMap,
        Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    obtain ⟨y, hy⟩ := (IsAlgClosed.splits (P.map (algebraMap ℚ Qbar))).mem_range_of_isRoot hP0 hroot
    exact ⟨y, hy⟩
  choose γf hγf using hmem
  have hj : Function.Injective j := j.toRingHom.injective
  refine ⟨{ toFun := γf
            map_one' := hj (by rw [hγf, map_one, map_one])
            map_mul' := fun x y => hj (by rw [hγf, map_mul, map_mul, hγf, hγf])
            map_zero' := hj (by rw [hγf, map_zero, map_zero])
            map_add' := fun x y => hj (by rw [hγf, map_add, map_add, hγf, hγf])
            commutes' := fun q => hj (by rw [hγf, AlgHom.commutes, AlgHom.commutes]) }, ?_⟩
  ext x
  exact (hγf x).symm

/-- **`G14TraceCompat` from the common trace (GLUE, proved).** If the traces of `r₅`, `r₃` at
Frobenius are `j₅(x)`, `j₃(x)`, and `ι₅ = j₅ ∘ γ`, `ι₃ = j₃ ∘ γ`, then `G14TraceCompat` holds for
any data with these `ι₅, ι₃, r₅, r₃`. -/
theorem g14TraceCompat_of_common {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    (D : ModData K A) (j5 : Qbar →ₐ[ℚ] PadicAlgCl 5) (j3 : Qbar →ₐ[ℚ] PadicAlgCl 3)
    (γ : Qbar →ₐ[ℚ] Qbar) (h5 : D.ι5 = j5.comp γ) (h3 : D.ι3 = j3.comp γ)
    (h : ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p → IsArithFrob τ v p →
        ∃ x : Qbar, (D.r5.mat τ).trace = j5 x ∧ (D.r3.mat τ).trace = j3 x) :
    G14TraceCompat D := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, fun p hp hpS v τ hv hτ c hc => ?_⟩
  obtain ⟨x, hx5, hx3⟩ := hS p hp hpS v τ hv hτ
  have hxc : x = γ c := by
    apply j5.toRingHom.injective
    change j5 x = j5 (γ c)
    rw [← hx5, hc, h5, AlgHom.comp_apply]
  rw [hx3, hxc, h3, AlgHom.comp_apply]

/-- **G14TraceCompat on G8's construction (GLUE, proved from T7, `FrobTraceLink` and the scalar
link).** For data `D` whose `r₅`, `r₃` are G8's outputs on `ρ_ℓ = β_ℓ⁻¹ a_ℓ Tm_ℓ` with
`a_ℓ = j_ℓ ∘ a`, `β_ℓ = j_ℓ ∘ β`, and whose embeddings are `ι₅ = j₅ ∘ γ`, `ι₃ = j₃ ∘ γ`. -/
theorem g14TraceCompat_of_link (hM : CharPolyIndepOfEll) {K : Type} [Field K] [NumberField K]
    {A : PkgI3.AbVar K} (D : ModData K A) (j5 : Qbar →ₐ[ℚ] PadicAlgCl 5)
    (j3 : Qbar →ₐ[ℚ] PadicAlgCl 3) (γ : Qbar →ₐ[ℚ] Qbar) (hι5 : D.ι5 = j5.comp γ)
    (hι3 : D.ι3 = j3.comp γ) (a β : GQ → Qbar)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3))
    (h5 : GalG8Out A 5 (GlueDescent.rho Tm5 (fun g => j5 (a g)) (fun g => j5 (β g))) D.r5)
    (h3 : GalG8Out A 3 (GlueDescent.rho Tm3 (fun g => j3 (a g)) (fun g => j3 (β g))) D.r3)
    (hF : FrobTraceLink A Tm5 Tm3) : G14TraceCompat D :=
  g14TraceCompat_of_common D j5 j3 γ hι5 hι3
    (common_trace hM A j5 j3 a β Tm5 Tm3 D.r5 D.r3 h5 h3 hF)

/-! ## §6. With G12: data satisfying both `G12Spec` and `G14TraceCompat` (proved) -/

/-- **`G12Spec D ∧ G14TraceCompat D` from G8 at `3` and `5`, G12 at `5`, T7, `FrobTraceLink` and
the scalar link (GLUE, proved; with g0-mod-newform's `DirichletOfFinite`).** The embedding
`ι₅` is the one from Pan's output (`g12Spec_of_galois`); `ι₃ := j₃ ∘ γ` where `ι₅ = j₅ ∘ γ`
(`exists_comp_eq`). The data keep G8's `r₅`, `r₃`. -/
theorem g12Spec_g14_of_galois (hDF : DirichletOfFinite) (hM : CharPolyIndepOfEll) {K : Type}
    [Field K] [NumberField K] (A : PkgI3.AbVar K) (j5 : Qbar →ₐ[ℚ] PadicAlgCl 5)
    (j3 : Qbar →ₐ[ℚ] PadicAlgCl 3) (a β : GQ → Qbar)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3)) (r5 : GaloisRep 5 2) (r3 : GaloisRep 3 2)
    (h5 : GalG8Out A 5 (GlueDescent.rho Tm5 (fun g => j5 (a g)) (fun g => j5 (β g))) r5)
    (h3 : GalG8Out A 3 (GlueDescent.rho Tm3 (fun g => j3 (a g)) (fun g => j3 (β g))) r3)
    (h12 : GalG12Out r5) (hF : FrobTraceLink A Tm5 Tm3) :
    ∃ D : ModData K A, D.r5 = r5 ∧ D.r3 = r3 ∧ G12Spec D ∧ G14TraceCompat D := by
  obtain ⟨i, ιC, ι5, hspec⟩ := g12Spec_of_galois hDF A _ _ r5 r3 h5 h3 h12
  obtain ⟨γ, hγ⟩ := exists_comp_eq ι5 j5
  refine ⟨⟨i, ιC, ι5, j3.comp γ, r5, r3⟩, rfl, rfl, hspec _, ?_⟩
  exact g14TraceCompat_of_link hM _ j5 j3 γ hγ rfl a β Tm5 Tm3 h5 h3 hF

/-- **From linked G7 data (GLUE, proved).** The `A`-level form of `G14Bridge.TateBridge35`'s
conclusion (`G7Out` at 5 and 3 with scalars `j_ℓ ∘ a`, `j_ℓ ∘ β`, and `FrobTraceLink`), with
g0-mod-galois' G8-G12 as the hypotheses `hG5` (their `g8_g12` at `ℓ = 5`: `G8Out ∧ G12Out`) and
`hG3` (their `g8_g11` at `ℓ = 3`: `G8Out`), gives G8's `r₅`, `r₃` (with their `G8Out`, so that
`G15RamG` can be proved for them) and data `D` carrying them with `G12Spec ∧ G14TraceCompat`. -/
theorem g12Spec_g14_of_linked (hDF : DirichletOfFinite) (hM : CharPolyIndepOfEll) {K : Type}
    [Field K] [NumberField K] (A : PkgI3.AbVar K) (a β : GQ → Qbar)
    (j5 : Qbar →ₐ[ℚ] PadicAlgCl 5) (j3 : Qbar →ₐ[ℚ] PadicAlgCl 3)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5)) (c5 ε5 : GQ → GQ → PadicAlgCl 5)
    (u5 : GlueDescent.MatrixUnits2 (PadicAlgCl 5) (Vb A 5))
    (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3)) (c3 ε3 : GQ → GQ → PadicAlgCl 3)
    (u3 : GlueDescent.MatrixUnits2 (PadicAlgCl 3) (Vb A 3))
    (h75 : G7Out A 5 Tm5 c5 ε5 (fun g => j5 (a g)) (fun g => j5 (β g)) u5)
    (h73 : G7Out A 3 Tm3 c3 ε3 (fun g => j3 (a g)) (fun g => j3 (β g)) u3)
    (hF : FrobTraceLink A Tm5 Tm3)
    (hG5 : G7Out A 5 Tm5 c5 ε5 (fun g => j5 (a g)) (fun g => j5 (β g)) u5 →
      ∃ r5 : GaloisRep 5 2,
        GalG8Out A 5 (GlueDescent.rho Tm5 (fun g => j5 (a g)) (fun g => j5 (β g))) r5 ∧
        GalG12Out r5)
    (hG3 : G7Out A 3 Tm3 c3 ε3 (fun g => j3 (a g)) (fun g => j3 (β g)) u3 →
      ∃ r3 : GaloisRep 3 2,
        GalG8Out A 3 (GlueDescent.rho Tm3 (fun g => j3 (a g)) (fun g => j3 (β g))) r3) :
    ∃ (r5 : GaloisRep 5 2) (r3 : GaloisRep 3 2) (D : ModData K A),
      GalG8Out A 5 (GlueDescent.rho Tm5 (fun g => j5 (a g)) (fun g => j5 (β g))) r5 ∧
      GalG8Out A 3 (GlueDescent.rho Tm3 (fun g => j3 (a g)) (fun g => j3 (β g))) r3 ∧
      D.r5 = r5 ∧ D.r3 = r3 ∧ G12Spec D ∧ G14TraceCompat D := by
  obtain ⟨r5, h5, h12⟩ := hG5 h75
  obtain ⟨r3, h3⟩ := hG3 h73
  obtain ⟨D, hD5, hD3, hs, hc⟩ :=
    g12Spec_g14_of_galois hDF hM A j5 j3 a β Tm5 Tm3 r5 r3 h5 h3 h12 hF
  exact ⟨r5, r3, D, h5, h3, hD5, hD3, hs, hc⟩

end G14Trace

end

noncomputable section
/-! ## §1. The smaller named Props -/

namespace G15Ram

open PkgI4 (GQp GaloisRep)
open LadicCond G0ModNewform

section Local

variable (p : ℕ) [Fact p.Prime]

/-- **Glue: T20 + T21 transported to `ℚ̄_p`** (Hilbert's formula for the different, Serre,
*Corps locaux* IV §1 Prop. 4, and Serre's bound `v_F(𝔇) ≤ e − 1 + v_F(e)`, III §6 remark after
Prop. 13; UNVERIFIED numbering). For a finite Galois `F ⊆ ℚ̄_p` with lower ramification groups
`G_i = ramSet F i` (pulled back to `G_{ℚ_p}`) and `g_i = ramCard F i`, some `G_n` is trivial and
`∑_{i<n}(g_i − 1) ≤ e − 1 + e·v_p(e)` with `e = g_0`. Both parts are proved by t-different over
complete DVRs (`PkgI6.hilbertDifferentFormula`, `PkgI6.differentBound`). This Prop is derived
below from them and the transport `LadicDVRModel` (`hilbertSerre_of_model`). The existence of
`n` alone is already proved (`LadicCond.eventuallyTrivial`). -/
def HilbertSerreLadic : Prop :=
  ∀ F : Fld p, IsFinGal F → ∃ n : ℕ, ramSet F n ⊆ fixSet F ∧
    ∑ i ∈ Finset.range n, (ramCard F i - 1) ≤
      ramCard F 0 - 1 + ramCard F 0 * padicValNat p (ramCard F 0)

/-- **Glue (D1 at the level of `upperAbs`; N5 L796-812, L824-827).** For a finite Galois
`F ⊆ ℚ̄_p` with ramification index `e(F/ℚ_p) ≤ a!`, every absolute upper ramification group
`G_{ℚ_p}^t` with `t > 4a²` fixes `F`. Proved below from `HilbertSerreLadic`
(`upperBreakFix_of_hilbertSerre`). -/
def UpperBreakFix : Prop :=
  ∀ F : Fld p, IsFinGal F → ∀ a : ℕ, 1 ≤ a → ramCard F 0 ≤ a.factorial →
    ∀ t : ℝ, 4 * (a : ℝ) ^ 2 < t → upperAbs p t ⊆ fixSet F

/-- **Glue (Serre, *Corps locaux* IV §3: `G^t ⊆ G^0`'s wild part for `t > 0`; UNVERIFIED
numbering).** For `t > 0` every element of `G_{ℚ_p}^t` lies in wild inertia: `|σx − x| < |x|`
for all `x ≠ 0`. (Proof: take `F` = the Galois closure of `ℚ_p(x)`; `σ|_F ∈ G^t(F) = G_{ψ(t)}(F)`
with `ψ(t) > 0`, so `σ|_F ∈ G_1(F)`, and `σx/x ≡ 1 mod 𝔪_F` because `|F^×| = |ϖ|^ℤ`.)
Proved below (`upperWild`). -/
def UpperWild : Prop :=
  ∀ t : ℝ, 0 < t → upperAbs p t ⊆ wildSet

/-- **Glue (tame extensions; Serre, *Corps locaux* IV §2, Cor. 1-4 of Prop. 7: `G_1` is the
`p`-Sylow subgroup of `G_0`; UNVERIFIED numbering).** If `F ⊆ ℚ̄_p` is finite Galois and `p` does
not divide `e(F/ℚ_p)`, wild inertia fixes `F`. Proved below (`wildFixTame`). -/
def WildFixTame : Prop :=
  ∀ F : Fld p, IsFinGal F → ¬ p ∣ ramCard F 0 → wildSet ⊆ fixSet F

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- **Glue on G8's construction (G8 + G3 + R6 + D2; N5 L719-727, L819-823).** On `G_F ∩ P_p`
the representation `r` is the scalar `β(σ)` (`ρ_ℓ(σ) = β(σ)⁻¹ a_σ μ_σ ∘ σ` with `a_σ μ_σ = 1`
on `G_L ⊇ G_F`, and the Tate action of `A` trivial on `P_p ∩ G_F`: by Raynaud's criterion (R6)
`A` is semistable over `F ⊇ L_v(A[3])` (`A[5]` if `p = 3`), and then wild inertia acts trivially
(D2, `PkgI2.D2_fixed_of_raynaud`); at `p > D` by good reduction (G3) and
Néron–Ogg–Shafarevich). Here `β` is the local twist (the inverse of Glazer's `β`). -/
def TwistShape (r : GaloisRep ℓ 2) (F : Fld p) (β : GQp p → PadicAlgCl ℓ) : Prop :=
  ∀ σ ∈ fixSet F ∩ wildSet,
    ((r.restrictLocal p σ : GL (Fin 2) (PadicAlgCl ℓ)) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) =
      Matrix.scalar (Fin 2) (β σ)

/-- **Glue on G7's `β` (D3 + T16; N5 L823-844).** The local twist is trivial on
`G_{ℚ_p}^t ∩ G_F` for `t > U`: at odd `p`, `β|_{G_F}` is trivial on wild inertia (its square is
the tame `χ`, and a pro-`p` group has no quotient of order two;
`GlueConductor.char_trivial_of_odd_pgroup`);
at `p = 2`, local reciprocity with the upper numbering theorem (T16) and `(U_F^{e+1})⁴ = U_F^{3e+1}`
(D3, `GlueConductor.fourth_pow_mem`) bound the relative upper break of `β` by `3e`, and
`ψ_{F/ℚ_2}(u) ≥ u` moves it to the absolute numbering; `max(4D², 3e) ≤ U₀`
(`GlueConductor.max_le_U0`). -/
def TwistUpper (F : Fld p) (β : GQp p → PadicAlgCl ℓ) (U : ℝ) : Prop :=
  ∀ t : ℝ, U < t → ∀ σ ∈ upperAbs p t ∩ fixSet F, β σ = 1

/-- **Glue on G7's `β` at tame primes (N5 L848-851).** `β` is trivial on `P_p ∩ G_F` (for odd
`p`: `β²` is tame, `GlueConductor.char_trivial_of_odd_pgroup`). -/
def TwistTame (F : Fld p) (β : GQp p → PadicAlgCl ℓ) : Prop :=
  ∀ σ ∈ fixSet F ∩ wildSet, β σ = 1

/-- **G8-G7 local data at `p ≤ D`** (N5 L819-844): `F` the Galois closure of `L_v(A[3])`
(`A[5]` if `p = 3`), of degree `≤ (DG₀)!`, so `e(F/ℚ_p) ≤ (DG₀)!`; the local twist `β`. -/
def SmallPrimeData (r : GaloisRep ℓ 2) : Prop :=
  ∃ (F : Fld p) (β : GQp p → PadicAlgCl ℓ), IsFinGal F ∧
    ramCard F 0 ≤ (ZInQ.heightD * ZInQ.heightG0).factorial ∧
    TwistShape p r F β ∧ TwistUpper p F β U0

/-- **G8-G7 local data at `p > D`** (N5 L848-851): `F` the Galois closure of `L_v`, tame since
`[L_v:ℚ_p] ≤ D < p` (the Galois closure of a tame extension is tame); the local twist `β`. -/
def LargePrimeData (r : GaloisRep ℓ 2) : Prop :=
  ∃ (F : Fld p) (β : GQp p → PadicAlgCl ℓ), IsFinGal F ∧ ¬ p ∣ ramCard F 0 ∧
    TwistShape p r F β ∧ TwistTame p F β

/-- The local data at `p` for `r`, by the size of `p`. -/
def LocalData (r : GaloisRep ℓ 2) : Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) → SmallPrimeData p r) ∧
    ((ZInQ.heightD : ℝ) < p → LargePrimeData p r)

end Local

/-! ## §2. Local field: the break bound at the level of `upperAbs` (proved) -/

section Break

variable {p : ℕ} [Fact p.Prime] {F : Fld p}

theorem ramSet_anti {i j : ℕ} (h : i ≤ j) : ramSet F j ⊆ ramSet F i := by
  rintro σ ⟨ϖ, hϖ, hσ⟩
  refine ⟨ϖ, hϖ, fun x hx hx1 => (hσ x hx hx1).trans ?_⟩
  exact pow_le_pow_of_le_one (norm_nonneg _) hϖ.2.1.le (by omega)

theorem card_image_mono (hF : IsFinGal F) {S T : Set (GQp p)} (h : S ⊆ T) :
    Nat.card (restr F '' S) ≤ Nat.card (restr F '' T) :=
  Nat.card_mono (finite_restr hF T) (Set.image_mono h)

theorem ramCard_anti (hF : IsFinGal F) : Antitone (ramCard F) := fun _ _ h =>
  card_image_mono hF (ramSet_anti h)

theorem one_le_ramCard (hF : IsFinGal F) (i : ℕ) : 1 ≤ ramCard F i := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif hF.1
  exact Nat.one_le_iff_ne_zero.mpr (ramCard_ne_zero hF hϖ i)

/-- If `g_i ≤ 1`, then `G_i` (pulled back) fixes `F`. -/
theorem fix_of_ramCard_le_one (hF : IsFinGal F) {i : ℕ} (h : ramCard F i ≤ 1) :
    ramSet F i ⊆ fixSet F := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif hF.1
  have hfin : Finite (restr F '' ramSet F i) := (finite_restr hF (ramSet F i)).to_subtype
  have hsub : Subsingleton (restr F '' ramSet F i) := Finite.card_le_one_iff_subsingleton.mp h
  have h1 : (1 : GQp p) ∈ ramSet F i := fixSet_subset_ramSet hϖ i (fun x _ => rfl)
  intro σ hσ x hx
  have he : (⟨restr F σ, σ, hσ, rfl⟩ : restr F '' ramSet F i) = ⟨restr F 1, 1, h1, rfl⟩ :=
    Subsingleton.elim _ _
  have := congrFun (congrArg Subtype.val he) ⟨x, hx⟩
  exact this

theorem ramCardR_of_gt {t : ℝ} (ht : -1 < t) : ramCardR F t = ramCard F ⌈t⌉.toNat := by
  unfold ramCardR ramSetR
  rw [if_neg (not_le.mpr ht)]
  rfl

theorem ramCardR_anti (hF : IsFinGal F) : Antitone (ramCardR F) := by
  intro s t hst
  unfold ramCardR ramSetR
  by_cases ht : t ≤ -1
  · have hs : s ≤ -1 := hst.trans ht
    rw [if_pos ht, if_pos hs]
  · rw [if_neg ht]
    by_cases hs : s ≤ -1
    · rw [if_pos hs]
      exact card_image_mono hF (Set.subset_univ _)
    · rw [if_neg hs]
      exact card_image_mono hF (ramSet_anti (Int.toNat_le_toNat (Int.ceil_mono hst)))

/-- The integrand of Herbrand's `φ` (`phiAt`). -/
def gInt (F : Fld p) (t : ℝ) : ℝ := (ramCardR F t : ℝ) / (ramCard F 0 : ℝ)

theorem phiAt_eq (u : ℝ) : phiAt F u = ∫ t in (0 : ℝ)..u, gInt F t := rfl

theorem gInt_anti (hF : IsFinGal F) : Antitone (gInt F) := fun _ _ h =>
  div_le_div_of_nonneg_right (by exact_mod_cast ramCardR_anti hF h) (Nat.cast_nonneg _)

theorem gInt_int (hF : IsFinGal F) (a b : ℝ) :
    IntervalIntegrable (gInt F) MeasureTheory.volume a b :=
  (gInt_anti hF).intervalIntegrable

theorem g0_pos (hF : IsFinGal F) : (0 : ℝ) < ramCard F 0 := by
  exact_mod_cast one_le_ramCard hF 0

theorem gInt_le_one (hF : IsFinGal F) {t : ℝ} (ht : -1 < t) : gInt F t ≤ 1 := by
  rw [gInt, div_le_one (g0_pos hF), ramCardR_of_gt ht]
  exact_mod_cast ramCard_anti hF (Nat.zero_le _)

theorem gInt_ge (hF : IsFinGal F) (t : ℝ) : 1 / (ramCard F 0 : ℝ) ≤ gInt F t := by
  have h1 : 1 ≤ ramCardR F t := by
    have h0 : -1 < max t 0 := lt_of_lt_of_le (by norm_num) (le_max_right t 0)
    have := ramCardR_anti hF (le_max_left t 0)
    rw [ramCardR_of_gt h0] at this
    exact (one_le_ramCard hF _).trans this
  exact div_le_div_of_nonneg_right (by exact_mod_cast h1) (Nat.cast_nonneg _)

theorem gInt_nonneg (hF : IsFinGal F) (t : ℝ) : 0 ≤ gInt F t :=
  le_trans (by have := g0_pos hF; positivity) (gInt_ge hF t)

theorem phi_mono (hF : IsFinGal F) {u w : ℝ} (h : u ≤ w) : phiAt F u ≤ phiAt F w := by
  have h1 := intervalIntegral.integral_interval_sub_left (gInt_int hF 0 w) (gInt_int hF 0 u)
  have h2 : 0 ≤ ∫ t in u..w, gInt F t :=
    intervalIntegral.integral_nonneg h (fun x _ => gInt_nonneg hF x)
  rw [phiAt_eq, phiAt_eq]
  linarith

theorem phi_sub_le (hF : IsFinGal F) {w u : ℝ} (hw : 0 ≤ w) (hwu : w ≤ u) :
    phiAt F u - phiAt F w ≤ u - w := by
  rw [phiAt_eq, phiAt_eq,
    intervalIntegral.integral_interval_sub_left (gInt_int hF _ _) (gInt_int hF _ _)]
  calc ∫ t in w..u, gInt F t ≤ ∫ _ in w..u, (1 : ℝ) :=
        intervalIntegral.integral_mono_on hwu (gInt_int hF _ _) intervalIntegrable_const
          (fun x hx => gInt_le_one hF (by linarith [hx.1]))
    _ = u - w := by rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]

theorem phi_ge (hF : IsFinGal F) {u : ℝ} (hu : 0 ≤ u) :
    u * (1 / (ramCard F 0 : ℝ)) ≤ phiAt F u := by
  rw [phiAt_eq]
  calc u * (1 / (ramCard F 0 : ℝ)) = ∫ _ in (0 : ℝ)..u, (1 / (ramCard F 0 : ℝ)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    _ ≤ ∫ t in (0 : ℝ)..u, gInt F t :=
        intervalIntegral.integral_mono_on hu intervalIntegrable_const (gInt_int hF _ _)
          (fun x _ => gInt_ge hF x)

theorem phi_nat (hF : IsFinGal F) (m : ℕ) :
    phiAt F m = ∑ k ∈ Finset.range m, (ramCard F (k + 1) : ℝ) / ramCard F 0 := by
  rw [phiAt_eq]
  have h := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume)
    (f := gInt F) (a := fun k : ℕ => (k : ℝ)) (n := m) (fun k _ => gInt_int hF _ _)
  simp only [Nat.cast_zero] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
  have : ∫ x in (k : ℝ)..((k + 1 : ℕ) : ℝ), gInt F x =
      ∫ _ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (ramCard F (k + 1) : ℝ) / ramCard F 0 := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall fun x hx => ?_
    rw [Set.uIoc_of_le hk] at hx
    have hx1 := hx.1
    have hx2 := hx.2
    push_cast at hx2
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hxm : -1 < x := by linarith
    have hc : ⌈x⌉ = ((k + 1 : ℕ) : ℤ) := by
      rw [Int.ceil_eq_iff]
      push_cast
      constructor <;> linarith
    simp only [gInt]
    rw [ramCardR_of_gt hxm, hc, Int.toNat_natCast]
  rw [this, intervalIntegral.integral_const, smul_eq_mul]
  push_cast
  ring

theorem phi_eq_sum (g : ℕ → ℕ) (m : ℕ) :
    GlueConductor.phi g m = ∑ k ∈ Finset.range m, (g (k + 1) : ℚ) / g 0 := by
  induction m with
  | zero => rw [GlueConductor.phi_zero, Finset.sum_range_zero]
  | succ m ih => rw [GlueConductor.phi_succ, ih, Finset.sum_range_succ]

/-- **D1 at the level of `upperAbs` (GLUE, proved from `HilbertSerreLadic`).** -/
theorem upperBreakFix_of_hilbertSerre (h : HilbertSerreLadic p) : UpperBreakFix p := by
  classical
  intro F hF a ha hea t ht σ hσ
  have hex : ∃ n, ramSet F n ⊆ fixSet F ∧ ∑ i ∈ Finset.range n, (ramCard F i - 1) ≤
      ramCard F 0 - 1 + ramCard F 0 * padicValNat p (ramCard F 0) := h F hF
  have hex' : ∃ n, ramSet F n ⊆ fixSet F := let ⟨n, hn, _⟩ := hex; ⟨n, hn⟩
  set n := Nat.find hex' with hn_def
  have hnfix : ramSet F n ⊆ fixSet F := Nat.find_spec hex'
  obtain ⟨N, hN, hsum⟩ := hex
  have hnN : n ≤ N := Nat.find_min' hex' hN
  have hsum' : ∑ i ∈ Finset.range n, (ramCard F i - 1) ≤
      ramCard F 0 - 1 + ramCard F 0 * padicValNat p (ramCard F 0) :=
    (Finset.sum_le_sum_of_subset (Finset.range_mono hnN)).trans hsum
  set w : ℕ := n - 1 with hw
  have ha2 : (0 : ℝ) ≤ 4 * (a : ℝ) ^ 2 := by positivity
  have hφw : phiAt F w < t := by
    have h4 : phiAt F w ≤ 4 * (a : ℝ) ^ 2 := by
      by_cases hn1 : n ≤ 1
      · have hw0 : w = 0 := by omega
        rw [hw0, Nat.cast_zero, phiAt_eq, intervalIntegral.integral_same]
        exact ha2
      · have hb : ¬ ramSet F w ⊆ fixSet F := Nat.find_min hex' (by omega)
        have hgb : 2 ≤ ramCard F w := by
          by_contra hlt
          exact hb (fix_of_ramCard_le_one hF (by omega))
        have hub := GlueConductor.upper_break_le p a (Fact.out) ha (ramCard F)
          (ramCard_anti hF) (one_le_ramCard hF) w n hgb (by omega) hea hsum'
        rw [phi_nat hF]
        have hcast : ((GlueConductor.phi (ramCard F) w : ℚ) : ℝ) =
            ∑ k ∈ Finset.range w, (ramCard F (k + 1) : ℝ) / ramCard F 0 := by
          rw [phi_eq_sum]
          push_cast
          rfl
        rw [← hcast]
        exact_mod_cast hub
    linarith
  set S := {u : ℝ | -1 ≤ u ∧ t ≤ phiAt F u} with hS
  have ht0 : 0 < t := by linarith
  have hg0 := g0_pos hF
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  have hne : S.Nonempty := by
    refine ⟨w + t * ramCard F 0, by nlinarith, ?_⟩
    have h1 := phi_ge hF (u := w + t * ramCard F 0) (by positivity)
    have h2 : t ≤ (w + t * ramCard F 0) * (1 / (ramCard F 0 : ℝ)) := by
      rw [add_mul, mul_one_div, mul_one_div, mul_div_assoc, div_self hg0.ne', mul_one]
      have : (0 : ℝ) ≤ w / ramCard F 0 := div_nonneg hw0 hg0.le
      linarith
    exact h2.trans h1
  have hlb : ∀ u ∈ S, (w : ℝ) + (t - phiAt F w) ≤ u := by
    rintro u ⟨-, hu⟩
    by_cases huw : u ≤ w
    · exact absurd (hu.trans (phi_mono hF huw)) (not_le.mpr hφw)
    · have := phi_sub_le hF hw0 (le_of_not_ge huw)
      linarith
  have hψ : (w : ℝ) < sInf S := lt_of_lt_of_le (by linarith) (le_csInf hne hlb)
  have hσF : σ ∈ ramSetR F (sInf S) := hσ F hF
  unfold ramSetR at hσF
  rw [if_neg (by linarith)] at hσF
  apply hnfix
  refine ramSet_anti ?_ hσF
  have hz : ((w : ℕ) : ℤ) < ⌈sInf S⌉ := Int.lt_ceil.mpr (by exact_mod_cast hψ)
  omega

end Break

/-! ## §2b. Positive upper groups are wild (proved) -/

section Wild

variable {p : ℕ} [Fact p.Prime]

/-- `G_{ℚ_p}` acts isometrically on `ℚ̄_p` (copied from g0-mod-newform's `norm_aut`). -/
theorem norm_aut' (σ : GQp p) (y : Kbar p) : ‖σ y‖ = ‖y‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv σ y).symm

/-- For `t > 0`, `G^t(F) ⊆ G_1(F)` (pulled back): `ψ_F(t) > 0`. -/
theorem ramSet_one_of_upperSet {F : Fld p} (hF : IsFinGal F) {t : ℝ} (ht : 0 < t) {σ : GQp p}
    (hσ : σ ∈ upperSet F t) : σ ∈ ramSet F 1 := by
  set S := {u : ℝ | -1 ≤ u ∧ t ≤ phiAt F u} with hS
  have hg0 := g0_pos hF
  have hφ0 : phiAt F 0 = 0 := by rw [phiAt_eq, intervalIntegral.integral_same]
  have hne : S.Nonempty := by
    refine ⟨t * ramCard F 0, by nlinarith, ?_⟩
    have h1 := phi_ge hF (u := t * ramCard F 0) (by positivity)
    have h2 : t * ramCard F 0 * (1 / (ramCard F 0 : ℝ)) = t := by field_simp
    linarith
  have hlb : ∀ u ∈ S, t ≤ u := by
    rintro u ⟨-, hu⟩
    by_cases hu0 : u ≤ 0
    · have := phi_mono hF hu0
      linarith
    · have := phi_sub_le hF le_rfl (le_of_not_ge hu0)
      linarith
  have hψ : t ≤ sInf S := le_csInf hne hlb
  have hσF : σ ∈ ramSetR F (sInf S) := hσ
  unfold ramSetR at hσF
  rw [if_neg (by linarith)] at hσF
  refine ramSet_anti ?_ hσF
  have hz : (0 : ℤ) < ⌈sInf S⌉ := Int.lt_ceil.mpr (by push_cast; linarith)
  omega

/-- The predicate "`σ x / x ≡ 1`": `‖σ x − x‖ < ‖x‖`. -/
def WildAt (σ : GQp p) (y : Kbar p) : Prop := ‖σ y - y‖ < ‖y‖

theorem wildAt_mul {σ : GQp p} {y z : Kbar p} (hy : WildAt σ y) (hz : WildAt σ z) :
    WildAt σ (y * z) := by
  unfold WildAt at *
  have hy0 : 0 < ‖y‖ := lt_of_le_of_lt (norm_nonneg _) hy
  have hz0 : 0 < ‖z‖ := lt_of_le_of_lt (norm_nonneg _) hz
  have he : σ (y * z) - y * z = σ y * (σ z - z) + (σ y - y) * z := by rw [map_mul]; ring
  rw [he, norm_mul y z]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
  · rw [norm_mul, norm_aut']
    exact mul_lt_mul_of_pos_left hz hy0
  · rw [norm_mul]
    exact mul_lt_mul_of_pos_right hy hz0

theorem wildAt_inv {σ : GQp p} {y : Kbar p} (hy : WildAt σ y) : WildAt σ y⁻¹ := by
  unfold WildAt at *
  have hy0 : 0 < ‖y‖ := lt_of_le_of_lt (norm_nonneg _) hy
  have hy0' : y ≠ 0 := norm_pos_iff.mp hy0
  have hσy : σ y ≠ 0 := (map_ne_zero σ).mpr hy0'
  have he : σ y⁻¹ - y⁻¹ = (y - σ y) / (σ y * y) := by
    rw [map_inv₀]; field_simp
  rw [he, norm_div, norm_mul, norm_aut', norm_sub_rev, norm_inv,
    div_lt_iff₀ (by positivity)]
  calc ‖σ y - y‖ < ‖y‖ := hy
    _ = ‖y‖⁻¹ * (‖y‖ * ‖y‖) := by field_simp

theorem wildAt_one (σ : GQp p) : WildAt σ 1 := by
  unfold WildAt; simp

theorem wildAt_pow {σ : GQp p} {y : Kbar p} (hy : WildAt σ y) (n : ℕ) : WildAt σ (y ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact wildAt_one σ
  | succ n ih => rw [pow_succ]; exact wildAt_mul ih hy

theorem wildAt_zpow {σ : GQp p} {y : Kbar p} (hy : WildAt σ y) (k : ℤ) : WildAt σ (y ^ k) := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast]; exact wildAt_pow hy n
  · rw [zpow_neg, zpow_natCast]; exact wildAt_inv (wildAt_pow hy n)

theorem natCast_mem (F : Fld p) : (p : Kbar p) ∈ F := by
  rw [← map_natCast (algebraMap ℚ_[p] (Kbar p)) p]
  exact IntermediateField.algebraMap_mem _ _

/-- An element of `G_1(F)` (pulled back) satisfies `σx/x ≡ 1` for every `x ∈ F^×`. -/
theorem wild_of_ramSet_one {F : Fld p} {σ : GQp p} (hσ : σ ∈ ramSet F 1) {x : Kbar p}
    (hx : x ∈ F) (hx0 : x ≠ 0) : ‖σ x - x‖ < ‖x‖ := by
  obtain ⟨ϖ, hϖ, h1⟩ := hσ
  have hϖ1 : ‖ϖ‖ < 1 := hϖ.2.1
  have hϖpos : 0 < ‖ϖ‖ := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have hpn : ‖(p : Kbar p)‖ < 1 := by rw [norm_p_kbar]; exact inv_lt_one_of_one_lt₀ hp1
    have hp := hϖ.2.2 _ (natCast_mem F) hpn
    exact lt_of_lt_of_le (by rw [norm_p_kbar]; positivity) hp
  have hϖ0 : ϖ ≠ 0 := norm_pos_iff.mp hϖpos
  -- `ϖ` and the units of `F` satisfy `WildAt`
  have hwϖ : WildAt σ ϖ := by
    unfold WildAt
    have := h1 ϖ hϖ.1 hϖ1.le
    calc ‖σ ϖ - ϖ‖ ≤ ‖ϖ‖ ^ (1 + 1) := this
      _ < ‖ϖ‖ := by rw [pow_two]; exact mul_lt_of_lt_one_right hϖpos hϖ1
  have hwu : ∀ z ∈ F, ‖z‖ = 1 → WildAt σ z := by
    intro z hz hz1
    unfold WildAt
    rw [hz1]
    calc ‖σ z - z‖ ≤ ‖ϖ‖ ^ (1 + 1) := h1 z hz hz1.le
      _ < 1 := pow_lt_one₀ (norm_nonneg _) hϖ1 (by norm_num)
  -- discreteness: `x = ϖ^k z` with `‖z‖ = 1`
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hxpos ((one_lt_inv₀ hϖpos).mpr hϖ1)
  set k : ℤ := -(n + 1) with hk
  set z := x * (ϖ ^ k)⁻¹ with hz
  have hzF : z ∈ F := mul_mem hx (inv_mem (zpow_mem hϖ.1 k))
  have hnk : ‖ϖ ^ k‖ = ‖ϖ‖⁻¹ ^ (n + 1) := by
    rw [norm_zpow, hk, zpow_neg, inv_zpow]
  have hnk' : ‖ϖ‖⁻¹ ^ n = ‖ϖ ^ k‖ * ‖ϖ‖ := by
    rw [hnk, zpow_add₀ (inv_ne_zero hϖpos.ne'), zpow_one, mul_assoc,
      inv_mul_cancel₀ hϖpos.ne', mul_one]
  have hpk : 0 < ‖ϖ ^ k‖ := by rw [hnk]; positivity
  have hz_le : ‖z‖ ≤ 1 := by
    rw [hz, norm_mul, norm_inv, ← div_eq_mul_inv, div_le_one hpk, hnk]
    exact hn2
  have hz_gt : ‖ϖ‖ < ‖z‖ := by
    rw [hz, norm_mul, norm_inv, ← div_eq_mul_inv, lt_div_iff₀ hpk]
    rw [hnk'] at hn1
    linarith [mul_comm ‖ϖ ^ k‖ ‖ϖ‖]
  have hz1 : ‖z‖ = 1 := by
    by_contra hne
    exact absurd (hϖ.2.2 z hzF (lt_of_le_of_ne hz_le hne)) (not_le.mpr hz_gt)
  have hxz : x = ϖ ^ k * z := by
    rw [hz, mul_comm x, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero k hϖ0), one_mul]
  have := wildAt_mul (wildAt_zpow hwϖ k) (hwu z hzF hz1)
  rw [← hxz] at this
  exact this

instance isGalois_Kbar : IsGalois ℚ_[p] (Kbar p) := ⟨⟩

/-- **`UpperWild` (GLUE, proved).** For `t > 0`, `G_{ℚ_p}^t ⊆ P_p`. -/
theorem upperWild : UpperWild p := by
  intro t ht σ hσ x hx0
  let F := FiniteGaloisIntermediateField.adjoin ℚ_[p] ({x} : Set (Kbar p))
  have hF : IsFinGal F.toIntermediateField := ⟨inferInstance, inferInstance⟩
  have hxF : x ∈ F.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin ℚ_[p] {x} rfl
  exact wild_of_ramSet_one (ramSet_one_of_upperSet hF ht (hσ _ hF)) hxF hx0

end Wild

/-! ## §2d. Wild inertia fixes tame extensions (proved) -/

section Tame

variable {p : ℕ} [Fact p.Prime]

theorem wildSet_mul {σ τ : GQp p} (hσ : σ ∈ wildSet) (hτ : τ ∈ wildSet) : σ * τ ∈ wildSet := by
  intro x hx
  have hτx : τ x ≠ 0 := (map_ne_zero τ).mpr hx
  have he : (σ * τ) x - x = (σ (τ x) - τ x) + (τ x - x) := by
    rw [AlgEquiv.mul_apply]; ring
  rw [he]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ (hτ x hx))
  have := hσ (τ x) hτx
  rwa [norm_aut'] at this

theorem wildSet_pow {σ : GQp p} (hσ : σ ∈ wildSet) (k : ℕ) : σ ^ k ∈ wildSet := by
  induction k with
  | zero => rw [pow_zero]; exact one_mem_wildSet
  | succ k ih => rw [pow_succ]; exact wildSet_mul ih hσ

theorem norm_natCast_kbar {m : ℕ} (hm : ¬ p ∣ m) : ‖(m : Kbar p)‖ = 1 := by
  have h := PadicAlgCl.norm_extends p (m : ℚ_[p])
  have e : ((m : ℚ_[p]) : PadicAlgCl p) = (m : Kbar p) := map_natCast (algebraMap ℚ_[p] _) m
  rw [e] at h
  rw [h, Padic.norm_natCast_eq_one_iff]
  exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hm)

/-- In an ultrametric normed group, a finite sum of terms of norm `< c` has norm `< c`. -/
theorem norm_sum_range_lt {f : ℕ → Kbar p} {c : ℝ} (hc : 0 < c) (m : ℕ)
    (hf : ∀ k < m, ‖f k‖ < c) : ‖∑ k ∈ Finset.range m, f k‖ < c := by
  induction m with
  | zero => simpa using hc
  | succ m ih =>
    rw [Finset.sum_range_succ]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _)
      (max_lt (ih fun k hk => hf k (by omega)) (hf m (by omega)))

/-- **The averaging argument.** A wild `σ` with `σ^m x = x`, `p ∤ m`, fixes `x`. -/
theorem fix_of_wild_pow {σ : GQp p} (hσ : σ ∈ wildSet) {m : ℕ} (hm0 : 0 < m) (hpm : ¬ p ∣ m)
    {x : Kbar p} (hx : (σ ^ m) x = x) : σ x = x := by
  set S := ∑ k ∈ Finset.range m, (σ ^ k) x with hS
  have hσS : σ S = S := by
    have h1 : σ S = ∑ k ∈ Finset.range m, (σ ^ (k + 1)) x := by
      rw [hS, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_succ', AlgEquiv.mul_apply]
    have h2 := Finset.sum_range_succ' (fun k => (σ ^ k) x) m
    have h3 := Finset.sum_range_succ (fun k => (σ ^ k) x) m
    simp only [pow_zero, AlgEquiv.one_apply] at h2
    rw [hx] at h3
    rw [h1]
    rw [← hS] at h3
    linear_combination -(h3.symm.trans h2)
  have hkS : ∀ k : ℕ, (σ ^ k) S = S := by
    intro k
    induction k with
    | zero => rw [pow_zero, AlgEquiv.one_apply]
    | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hσS]
  have hm : (m : Kbar p) ≠ 0 := by
    intro h
    have := norm_natCast_kbar (p := p) hpm
    rw [h, norm_zero] at this
    exact zero_ne_one this
  set y := (m : Kbar p)⁻¹ * S with hy
  have hky : ∀ k : ℕ, (σ ^ k) y = y := by
    intro k
    rw [hy, map_mul, map_inv₀, map_natCast, hkS]
  set z := x - y with hz
  have hz0 : z = 0 := by
    by_contra hne
    have hsum : ∑ k ∈ Finset.range m, (z - (σ ^ k) z) = (m : Kbar p) * z := by
      have hterm : ∀ k ∈ Finset.range m, z - (σ ^ k) z = x - (σ ^ k) x := by
        intro k _
        rw [hz, map_sub, hky]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← hS, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, hz, hy, mul_sub, ← mul_assoc, mul_inv_cancel₀ hm,
        one_mul]
    have hlt : ‖∑ k ∈ Finset.range m, (z - (σ ^ k) z)‖ < ‖z‖ := by
      apply norm_sum_range_lt (norm_pos_iff.mpr hne)
      intro k _
      rw [norm_sub_rev]
      exact wildSet_pow hσ k z hne
    rw [hsum, norm_mul, norm_natCast_kbar hpm, one_mul] at hlt
    exact lt_irrefl _ hlt
  have hxy : x = y := sub_eq_zero.mp hz0
  rw [hxy]
  have := hky 1
  rwa [pow_one] at this

/-- The inertia subgroup at level `F`, pulled back: `{σ | ‖σx − x‖ < 1 for x ∈ 𝓞_F}`. -/
def inertiaSub (F : Fld p) (hF : IsFinGal F) : Subgroup (GQp p) where
  carrier := {σ | ∀ x ∈ F, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1}
  one_mem' := by
    intro x _ _
    simp
  mul_mem' := by
    intro σ τ hσ hτ x hx hx1
    have hτx : τ x ∈ F := apply_mem hF τ hx
    have he : (σ * τ) x - x = (σ (τ x) - τ x) + (τ x - x) := by
      rw [AlgEquiv.mul_apply]; ring
    rw [he]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ (hτ x hx hx1))
    exact hσ (τ x) hτx (by rw [norm_aut']; exact hx1)
  inv_mem' := by
    intro σ hσ x hx hx1
    have hσx : σ⁻¹ x ∈ F := apply_mem hF σ⁻¹ hx
    have h1 : ‖σ⁻¹ x‖ ≤ 1 := by rw [norm_aut']; exact hx1
    have h2 := hσ (σ⁻¹ x) hσx h1
    have he : σ (σ⁻¹ x) = x := by
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    rw [he, norm_sub_rev] at h2
    exact h2

theorem ramSet_zero_eq (F : Fld p) (hF : IsFinGal F) :
    ramSet F 0 = (inertiaSub F hF : Set (GQp p)) := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif hF.1
  ext σ
  constructor
  · rintro ⟨ϖ', hϖ', h⟩ x hx hx1
    have := h x hx hx1
    rw [zero_add, pow_one] at this
    exact lt_of_le_of_lt this hϖ'.2.1
  · intro h
    refine ⟨ϖ, hϖ, fun x hx hx1 => ?_⟩
    rw [zero_add, pow_one]
    exact hϖ.2.2 _ (F.sub_mem (apply_mem hF σ hx) hx) (h x hx hx1)

/-- `e(F/ℚ_p) = |G_0|` as the order of a subgroup of `Gal(F/ℚ_p)`. -/
theorem ramCard_zero_eq (F : Fld p) (hF : IsFinGal F) :
    haveI : Normal ℚ_[p] F := hF.2.to_normal
    ramCard F 0 =
      Nat.card ((inertiaSub F hF).map (AlgEquiv.restrictNormalHom F)) := by
  haveI : Normal ℚ_[p] F := hF.2.to_normal
  set φ : (F ≃ₐ[ℚ_[p]] F) → (F → Kbar p) := fun s x => ((s x : F) : Kbar p) with hφ
  have hφinj : Function.Injective φ := by
    intro s t h
    ext x
    have := congrFun h x
    exact this
  have himg : restr F '' ramSet F 0 =
      φ '' ((inertiaSub F hF).map (AlgEquiv.restrictNormalHom F) : Set _) := by
    rw [ramSet_zero_eq F hF, Subgroup.coe_map, Set.image_image]
    refine Set.image_congr fun σ _ => ?_
    funext x
    simp only [hφ, restr]
    exact (AlgEquiv.restrictNormalHom_apply F σ x).symm
  unfold ramCard
  rw [himg, Nat.card_image_of_injective hφinj]
  rfl

/-- **`WildFixTame` (GLUE, proved).** If `F/ℚ_p` is finite Galois with `p ∤ e(F/ℚ_p)`, wild
inertia fixes `F`. The restriction `s` of a wild `σ` lies in the inertia subgroup, of order `e`,
so its order `m` is prime to `p`; the averaging `y = m⁻¹ ∑_{k<m} σ^k x` then gives `σx = x`. -/
theorem wildFixTame : WildFixTame p := by
  intro F hF hpe σ hσ x hx
  haveI : Normal ℚ_[p] F := hF.2.to_normal
  set s := AlgEquiv.restrictNormalHom F σ with hs
  have hσI : σ ∈ inertiaSub F hF := by
    intro y _ hy1
    by_cases hy0 : y = 0
    · simp [hy0]
    · exact lt_of_lt_of_le (hσ y hy0) hy1
  have hsK : s ∈ (inertiaSub F hF).map (AlgEquiv.restrictNormalHom F) := ⟨σ, hσI, rfl⟩
  have hdvd : orderOf s ∣ ramCard F 0 := by
    rw [ramCard_zero_eq F hF]
    have := orderOf_dvd_natCard (⟨s, hsK⟩ : (inertiaSub F hF).map (AlgEquiv.restrictNormalHom F))
    rwa [Subgroup.orderOf_mk] at this
  have he0 : ramCard F 0 ≠ 0 := Nat.one_le_iff_ne_zero.mp (one_le_ramCard hF 0)
  have hm0 : 0 < orderOf s :=
    Nat.pos_of_ne_zero fun h => he0 (by rw [h] at hdvd; exact zero_dvd_iff.mp hdvd)
  have hpm : ¬ p ∣ orderOf s := fun h => hpe (h.trans hdvd)
  have hsm : AlgEquiv.restrictNormalHom F (σ ^ orderOf s) = 1 := by
    rw [map_pow, ← hs, pow_orderOf_eq_one]
  have hfix : (σ ^ orderOf s) x = x := by
    have := (AlgEquiv.restrictNormal_eq_one_iff F (σ ^ orderOf s)).mp hsm x hx
    exact this
  exact fix_of_wild_pow hσ hm0 hpm hfix

end Tame

/-! ## §2c. `HilbertSerreLadic` from T20 + T21 (proved by t-different) and a DVR model -/

section Bridge

open IsLocalRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- **Glue: the DVR model of a finite Galois `F ⊆ ℚ̄_p`** (the transport between `LadicCond`'s
norm-defined filtrations and the ring-theoretic setting of T20-T22, `PkgI6`; Serre, *Corps
locaux*, II §2 and IV §1). There are a complete DVR `A` with perfect residue field and a DVR `B`
finite, torsion-free, separable and Galois over `A` (namely `A = ℤ_p` and `B = 𝓞_F`, the elements
of norm `≤ 1`), whose lower ramification groups `PkgI6.lowerRam A B i` have the orders
`ramCard F i` and are trivial only when `ramSet F i` fixes `F`, whose ramification index is
`e = ramCard F 0`, with `(p) = 𝔪_B^e` and every integer prime to `p` a unit of `B`. -/
def LadicDVRModel (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ F : Fld p, IsFinGal F →
    ∃ (A B : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A)
      (_ : IsAdicComplete (maximalIdeal A) A) (_ : PerfectField (ResidueField A))
      (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B) (_ : Algebra A B)
      (_ : Module.Finite A B) (_ : Module.IsTorsionFree A B)
      (_ : Algebra.IsSeparable (FractionRing A) (FractionRing B))
      (_ : IsGalois (FractionRing A) (FractionRing B)),
      (∀ i, Nat.card (PkgI6.lowerRam A B i) = ramCard F i) ∧
      (∀ i, PkgI6.lowerRam A B i = ⊥ → ramSet F i ⊆ fixSet F) ∧
      Ideal.ramificationIdx (maximalIdeal B) A = ramCard F 0 ∧
      Ideal.span {(p : B)} = maximalIdeal B ^ ramCard F 0 ∧
      (∀ n : ℕ, ¬ p ∣ n → IsUnit (n : B))

/-- In `B` with `(p) = 𝔪^e` and integers prime to `p` units: `(e) = 𝔪^{e·v_p(e)}`. -/
theorem span_natCast_eq {B : Type} [CommRing B] [IsLocalRing B] {p : ℕ} (hp : p.Prime)
    {e : ℕ} (he : e ≠ 0) (hpB : Ideal.span {(p : B)} = maximalIdeal B ^ e)
    (hunit : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : B)) :
    Ideal.span {(e : B)} = maximalIdeal B ^ (e * padicValNat p e) := by
  have hdec := Nat.ordProj_mul_ordCompl_eq_self e p
  have hnd := Nat.not_dvd_ordCompl hp he
  rw [Nat.factorization_def e hp] at hdec hnd
  set v := padicValNat p e
  set u := e / p ^ v
  have hcast : (e : B) = (p : B) ^ v * (u : B) := by
    conv_lhs => rw [← hdec]
    push_cast
    rfl
  rw [hcast, ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, hpB,
    Ideal.span_singleton_eq_top.mpr (hunit u hnd), Ideal.mul_top, ← pow_mul]

variable {p : ℕ} [Fact p.Prime]

/-- **`HilbertSerreLadic` from T20 + T21 and the DVR model (GLUE, proved).** T20 and T21 are
the kernel's theorems `PkgI6.hilbertDifferentFormula`, `PkgI6.differentBound` (t-different). -/
theorem hilbertSerre_of_model (hM : LadicDVRModel p) : HilbertSerreLadic p := by
  intro F hF
  obtain ⟨A, B, _, _, _, _, _, _, _, _, _, _, _, _, _, hcard, hbot, he, hpB, hunit⟩ := hM F hF
  obtain ⟨N, hN, hD⟩ := PkgI6.hilbertDifferentFormula A B
  have hB := PkgI6.differentBound A B
  refine ⟨N, hbot N hN, ?_⟩
  have hsum : ∑ i ∈ Finset.range N, (Nat.card (PkgI6.lowerRam A B i) - 1) =
      ∑ i ∈ Finset.range N, (ramCard F i - 1) :=
    Finset.sum_congr rfl fun i _ => by rw [hcard i]
  rw [hsum] at hD
  have he0 : ramCard F 0 ≠ 0 := Nat.one_le_iff_ne_zero.mp (one_le_ramCard hF 0)
  rw [he, hD, span_natCast_eq (Fact.out) he0 hpB hunit, ← pow_add] at hB
  have hm0 : maximalIdeal B ≠ ⊥ := IsDiscreteValuationRing.not_a_field B
  have hmu : ¬ IsUnit (maximalIdeal B) := by
    rw [Ideal.isUnit_iff]
    exact (maximalIdeal.isMaximal B).ne_top
  exact (pow_dvd_pow_iff hm0 hmu).mp hB

end Bridge

/-! ## §2e. The DVR model over `ℤ_p`: the arithmetic conjuncts are automatic -/

section BridgeZp

open IsLocalRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

instance perfectField_residueField_Zp (p : ℕ) [Fact p.Prime] :
    PerfectField (ResidueField ℤ_[p]) :=
  PerfectField.of_ringEquiv (K := ZMod p) PadicInt.residueField.symm

/-- **Glue: the DVR model of a finite Galois `F ⊆ ℚ̄_p` over `ℤ_p`** (transport; Serre, *Corps
locaux* II §2, IV §1). There is a DVR `B` (namely `𝓞_F`, the elements of norm `≤ 1`), finite,
torsion-free, separable and Galois over `ℤ_p`, whose lower ramification groups
`PkgI6.lowerRam ℤ_p B i` have the orders `ramCard F i` and are trivial only when `ramSet F i`
fixes `F`. This is `LadicDVRModel` with `A = ℤ_p`; its other conjuncts are proved
(`ladicDVRModel_of_Zp`). -/
def LadicDVRModelZp (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ F : Fld p, IsFinGal F →
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B)
      (_ : Algebra ℤ_[p] B) (_ : Module.Finite ℤ_[p] B) (_ : Module.IsTorsionFree ℤ_[p] B)
      (_ : Algebra.IsSeparable (FractionRing ℤ_[p]) (FractionRing B))
      (_ : IsGalois (FractionRing ℤ_[p]) (FractionRing B)),
      (∀ i, Nat.card (PkgI6.lowerRam ℤ_[p] B i) = ramCard F i) ∧
      (∀ i, PkgI6.lowerRam ℤ_[p] B i = ⊥ → ramSet F i ⊆ fixSet F)

variable {p : ℕ} [Fact p.Prime]

/-- **`LadicDVRModel` from its `ℤ_p` form (GLUE, proved).** `e(B/ℤ_p) = |G_0|`
(t-different's `TDifferent.card_lowerRam_zero`), `(p) = 𝔪_{ℤ_p}` maps to `𝔪_B^e`
(`TDifferent.map_maximalIdeal_eq_pow`), and integers prime to `p` are units of `ℤ_p`. -/
theorem ladicDVRModel_of_Zp (h : LadicDVRModelZp p) : LadicDVRModel p := by
  intro F hF
  obtain ⟨B, _, _, _, _, _, _, _, _, hcard, hbot⟩ := h F hF
  have : IsGaloisGroup (B ≃ₐ[ℤ_[p]] B) ℤ_[p] B := TDifferent.isGaloisGroup_algEquiv ℤ_[p] B
  have : Finite (B ≃ₐ[ℤ_[p]] B) := TDifferent.finite_algEquiv ℤ_[p] B
  have : PerfectField (maximalIdeal ℤ_[p]).ResidueField :=
    PerfectField.of_ringEquiv (K := ResidueField ℤ_[p])
      (RingEquiv.ofBijective
        (algebraMap (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) (maximalIdeal ℤ_[p]).ResidueField :
          ResidueField ℤ_[p] →+* _)
        (maximalIdeal ℤ_[p]).bijective_algebraMap_quotient_residueField)
  have : Algebra.HasSeparableResidueFieldsAt ℤ_[p] B (maximalIdeal ℤ_[p]) := inferInstance
  have he : Ideal.ramificationIdx (maximalIdeal B) ℤ_[p] = ramCard F 0 := by
    rw [← TDifferent.card_lowerRam_zero ℤ_[p] B, hcard 0]
  refine ⟨ℤ_[p], B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hcard, hbot, he, ?_, ?_⟩
  · have hmap := TDifferent.map_maximalIdeal_eq_pow ℤ_[p] B
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast,
      he] at hmap
    exact hmap
  · intro n hn
    have hu : IsUnit (n : ℤ_[p]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hn
    have := hu.map (algebraMap ℤ_[p] B)
    rwa [map_natCast] at this

end BridgeZp

/-! ## §2f. The `ℤ_p`-model `𝓞_F = integralClosure ℤ_p F` (proved): `LadicDVRModelZp` -/

section DVRModelSec

open IsLocalRing Polynomial

variable {p : ℕ} [Fact p.Prime]

section Model

variable (F : Fld p)

/-- `ℤ_p → ℚ_p → F`. -/
@[reducible] def algZpF : Algebra ℤ_[p] F :=
  ((algebraMap ℚ_[p] F).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

attribute [local instance] algZpF

instance towerZpF : IsScalarTower ℤ_[p] ℚ_[p] F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The ring of integers `𝓞_F = integralClosure ℤ_p F`. -/
abbrev OF := integralClosure ℤ_[p] F

theorem norm_eq_spectral (x : F) : ‖(x : Kbar p)‖ = spectralNorm ℚ_[p] F x := by
  rw [spectralNorm.eq_of_tower (L := Kbar p) x, PadicAlgCl.spectralNorm_eq]
  rfl

variable [FiniteDimensional ℚ_[p] F]

/-- `y ∈ F` is integral over `ℤ_p` iff `‖y‖ ≤ 1` (copied from glue-sqrt-local's
`isIntegral_iff_spectralNorm_le_one`, with the norm of `ℚ̄_p`). -/
theorem isIntegral_iff_norm_le_one (y : F) :
    IsIntegral ℤ_[p] y ↔ ‖(y : Kbar p)‖ ≤ 1 := by
  rw [norm_eq_spectral]
  have hyQ : IsIntegral ℚ_[p] y := Algebra.IsIntegral.isIntegral y
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hyQ)]
  constructor
  · intro hy n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] hy, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl : minpoly ℚ_[p] y ∈ lifts (algebraMap ℤ_[p] ℚ_[p]) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hyQ)
    refine ⟨q, hqm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ_[p], hq, minpoly.aeval]

theorem mem_OF (y : F) : y ∈ OF F ↔ ‖(y : Kbar p)‖ ≤ 1 := isIntegral_iff_norm_le_one F y

theorem norm_le_one (b : OF F) : ‖((b : F) : Kbar p)‖ ≤ 1 := (mem_OF F b).mp b.2

theorem isUnit_iff_norm (b : OF F) : IsUnit b ↔ ‖((b : F) : Kbar p)‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : ‖(((u : OF F) : F) : Kbar p)‖ * ‖((((u⁻¹ : (OF F)ˣ) : OF F) : F) : Kbar p)‖ = 1 := by
      rw [← norm_mul]
      have : ((u : OF F) : F) * (((u⁻¹ : (OF F)ˣ) : OF F) : F) = 1 := by
        rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
      have h2 : (((u : OF F) : F) : Kbar p) * ((((u⁻¹ : (OF F)ˣ) : OF F) : F) : Kbar p) = 1 := by
        rw [← IntermediateField.coe_mul, this, IntermediateField.coe_one]
      rw [h2, norm_one]
    have a1 := norm_le_one F u
    have a2 := norm_le_one F (u⁻¹ : (OF F)ˣ)
    have b1 := norm_nonneg ((((u : OF F) : F) : Kbar p))
    have b2 := norm_nonneg (((((u⁻¹ : (OF F)ˣ) : OF F) : F) : Kbar p))
    nlinarith
  · intro h
    have hx0 : (b : F) ≠ 0 := by
      intro h0
      rw [h0, IntermediateField.coe_zero, norm_zero] at h
      exact zero_ne_one h
    have hinv : ‖(((b : F)⁻¹ : F) : Kbar p)‖ = 1 := by
      rw [IntermediateField.coe_inv, norm_inv, h, inv_one]
    have hint : ((b : F)⁻¹) ∈ OF F := (mem_OF F _).mpr hinv.le
    refine IsUnit.of_mul_eq_one (⟨_, hint⟩ : OF F) ?_
    apply Subtype.ext
    simp [hx0]

theorem isLocalRing_OF : IsLocalRing (OF F) := by
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  rw [mem_nonunits_iff, isUnit_iff_norm] at ha hb ⊢
  have ha' : ‖((a : F) : Kbar p)‖ < 1 := lt_of_le_of_ne (norm_le_one F a) ha
  have hb' : ‖((b : F) : Kbar p)‖ < 1 := lt_of_le_of_ne (norm_le_one F b) hb
  have := IsUltrametricDist.norm_add_le_max ((a : F) : Kbar p) ((b : F) : Kbar p)
  intro hab
  rw [Subalgebra.coe_add, IntermediateField.coe_add] at hab
  rw [hab] at this
  exact absurd this (not_le.mpr (max_lt ha' hb'))

end Model

section Model2

variable (F : Fld p) [FiniteDimensional ℚ_[p] F]

attribute [local instance] algZpF

theorem finite_OF : Module.Finite ℤ_[p] (OF F) := IsIntegralClosure.finite ℤ_[p] ℚ_[p] F (OF F)

theorem noeth_OF : IsNoetherianRing (OF F) :=
  IsIntegralClosure.isNoetherianRing ℤ_[p] ℚ_[p] F (OF F)

theorem dedekind_OF : IsDedekindDomain (OF F) :=
  IsIntegralClosure.isDedekindDomain ℤ_[p] ℚ_[p] F (OF F)

omit [FiniteDimensional ℚ_[p] F] in
theorem coe_natCast_F (n : ℕ) : ((n : F) : Kbar p) = n := map_natCast (algebraMap F (Kbar p)) n

theorem p_mem : ((p : ℕ) : F) ∈ OF F := by
  rw [mem_OF, coe_natCast_F, norm_p_kbar]
  exact inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)

theorem not_isField_OF : ¬ IsField (OF F) := by
  intro h
  have hp0 : (⟨((p : ℕ) : F), p_mem F⟩ : OF F) ≠ 0 := by
    intro h0
    have := congrArg (fun x : OF F => ((x : F) : Kbar p)) h0
    simp only [ZeroMemClass.coe_zero] at this
    rw [coe_natCast_F] at this
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) this
  obtain ⟨b, hb⟩ := h.mul_inv_cancel hp0
  have hu : IsUnit (⟨((p : ℕ) : F), p_mem F⟩ : OF F) := IsUnit.of_mul_eq_one _ hb
  rw [isUnit_iff_norm] at hu
  change ‖(((p : ℕ) : F) : Kbar p)‖ = 1 at hu
  rw [coe_natCast_F, norm_p_kbar, inv_eq_one] at hu
  have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  linarith

theorem dvr_OF : IsDiscreteValuationRing (OF F) := by
  haveI := isLocalRing_OF F
  haveI := noeth_OF F
  haveI := dedekind_OF F
  have h := (IsDiscreteValuationRing.TFAE (OF F) (not_isField_OF F)).out 1 3
  exact h.mpr (dedekind_OF F)

theorem torsionFree_OF : Module.IsTorsionFree ℤ_[p] (OF F) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  have hinj : Function.Injective (algebraMap ℤ_[p] F) :=
    (algebraMap ℚ_[p] F).injective.comp (FaithfulSMul.algebraMap_injective ℤ_[p] ℚ_[p])
  intro a b h
  apply hinj
  have := congrArg (fun x : OF F => (x : F)) h
  exact this

variable {F}

/-- The uniformizer `ϖ` as an element of `𝓞_F`. -/
def unifB {ϖ : Kbar p} (hϖ : IsUnif F ϖ) : OF F :=
  ⟨⟨ϖ, hϖ.1⟩, (mem_OF F _).mpr hϖ.2.1.le⟩

theorem coe_unifB {ϖ : Kbar p} (hϖ : IsUnif F ϖ) : (((unifB hϖ : OF F) : F) : Kbar p) = ϖ := rfl

theorem norm_unif_pos {ϖ : Kbar p} (hϖ : IsUnif F ϖ) : 0 < ‖ϖ‖ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpF : (p : Kbar p) ∈ F := by
    rw [← map_natCast (algebraMap ℚ_[p] (Kbar p)) p]
    exact IntermediateField.algebraMap_mem _ _
  have hpn : ‖(p : Kbar p)‖ < 1 := by rw [norm_p_kbar]; exact inv_lt_one_of_one_lt₀ hp1
  have hp := hϖ.2.2 _ hpF hpn
  exact lt_of_lt_of_le (by rw [norm_p_kbar]; positivity) hp

theorem mem_span_pow_iff {ϖ : Kbar p} (hϖ : IsUnif F ϖ) (k : ℕ) (b : OF F) :
    b ∈ Ideal.span {unifB hϖ ^ k} ↔ ‖((b : F) : Kbar p)‖ ≤ ‖ϖ‖ ^ k := by
  have hϖ0 := norm_unif_pos hϖ
  have hϖne : ϖ ≠ 0 := norm_pos_iff.mp hϖ0
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, rfl⟩
    have : (((c * unifB hϖ ^ k : OF F) : F) : Kbar p) = ((c : F) : Kbar p) * ϖ ^ k := by
      rw [Subalgebra.coe_mul, Subalgebra.coe_pow, IntermediateField.coe_mul,
        IntermediateField.coe_pow, coe_unifB]
    rw [this, norm_mul, norm_pow]
    calc ‖((c : F) : Kbar p)‖ * ‖ϖ‖ ^ k ≤ 1 * ‖ϖ‖ ^ k :=
          mul_le_mul_of_nonneg_right (norm_le_one F c) (by positivity)
      _ = ‖ϖ‖ ^ k := one_mul _
  · intro h
    set ϖF : F := ⟨ϖ, hϖ.1⟩
    have hϖF : ϖF ≠ 0 := by
      intro h0
      exact hϖne (congrArg (fun x : F => (x : Kbar p)) h0)
    set c : F := (b : F) * (ϖF ^ k)⁻¹ with hc
    have hcn : ‖(c : Kbar p)‖ ≤ 1 := by
      rw [hc, IntermediateField.coe_mul, IntermediateField.coe_inv, IntermediateField.coe_pow,
        norm_mul, norm_inv, norm_pow]
      have : ‖((ϖF : F) : Kbar p)‖ = ‖ϖ‖ := rfl
      rw [this]
      rw [mul_inv_le_iff₀ (by positivity), one_mul]
      exact h
    refine ⟨⟨c, (mem_OF F c).mpr hcn⟩, ?_⟩
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow]
    change c * ϖF ^ k = (b : F)
    rw [hc, mul_assoc, inv_mul_cancel₀ (pow_ne_zero k hϖF), mul_one]

theorem maximalIdeal_eq {ϖ : Kbar p} (hϖ : IsUnif F ϖ) :
    haveI := isLocalRing_OF F
    maximalIdeal (OF F) = Ideal.span {unifB hϖ} := by
  haveI := isLocalRing_OF F
  ext b
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_norm, ← pow_one (unifB hϖ),
    mem_span_pow_iff, pow_one]
  constructor
  · intro h
    exact hϖ.2.2 _ (b : F).2 (lt_of_le_of_ne (norm_le_one F b) h)
  · intro h h1
    rw [h1] at h
    exact absurd hϖ.2.1 (not_lt.mpr h)

theorem mem_maximalIdeal_pow_iff {ϖ : Kbar p} (hϖ : IsUnif F ϖ) (k : ℕ) (b : OF F) :
    haveI := isLocalRing_OF F
    b ∈ maximalIdeal (OF F) ^ k ↔ ‖((b : F) : Kbar p)‖ ≤ ‖ϖ‖ ^ k := by
  haveI := isLocalRing_OF F
  rw [maximalIdeal_eq hϖ, Ideal.span_singleton_pow, mem_span_pow_iff]

end Model2

section Galois

attribute [local instance] algZpF FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (F : Fld p) [FiniteDimensional ℚ_[p] F]

attribute [local instance] torsionFree_OF

instance faithful_OF : FaithfulSMul ℤ_[p] (OF F) := by
  rw [faithfulSMul_iff_algebraMap_injective, ← Module.isTorsionFree_iff_algebraMap_injective]
  exact torsionFree_OF F

instance faithful_frac_OF : FaithfulSMul ℤ_[p] (FractionRing (OF F)) := inferInstance


instance isFractionRing_OF : IsFractionRing (OF F) F :=
  integralClosure.isFractionRing_of_finite_extension ℚ_[p] F

theorem hcomp :
    (algebraMap (FractionRing ℤ_[p]) (FractionRing (OF F))).comp
        ((FractionRing.algEquiv ℤ_[p] ℚ_[p]).symm.toRingEquiv : ℚ_[p] →+* FractionRing ℤ_[p]) =
      ((FractionRing.algEquiv (OF F) F).symm.toRingEquiv : F →+* FractionRing (OF F)).comp
        (algebraMap ℚ_[p] F) := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
  ext z
  simp only [RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.coe_toRingEquiv]
  have h1 : (FractionRing.algEquiv ℤ_[p] ℚ_[p]).symm (algebraMap ℤ_[p] ℚ_[p] z) =
      algebraMap ℤ_[p] (FractionRing ℤ_[p]) z :=
    (FractionRing.algEquiv ℤ_[p] ℚ_[p]).symm.commutes z
  have h2 : algebraMap ℚ_[p] F (algebraMap ℤ_[p] ℚ_[p] z) =
      algebraMap (OF F) F (algebraMap ℤ_[p] (OF F) z) := rfl
  have h3 : (FractionRing.algEquiv (OF F) F).symm (algebraMap (OF F) F (algebraMap ℤ_[p] (OF F) z))
      = algebraMap (OF F) (FractionRing (OF F)) (algebraMap ℤ_[p] (OF F) z) :=
    (FractionRing.algEquiv (OF F) F).symm.commutes _
  rw [h1, h2, h3, ← IsScalarTower.algebraMap_apply ℤ_[p] (FractionRing ℤ_[p])
    (FractionRing (OF F)), IsScalarTower.algebraMap_apply ℤ_[p] (OF F) (FractionRing (OF F))]

theorem isGalois_frac [IsGalois ℚ_[p] F] :
    IsGalois (FractionRing ℤ_[p]) (FractionRing (OF F)) :=
  IsGalois.of_equiv_equiv (hcomp F)

theorem isSeparable_frac :
    Algebra.IsSeparable (FractionRing ℤ_[p]) (FractionRing (OF F)) :=
  Algebra.IsSeparable.of_equiv_equiv _ _ (hcomp F)

end Galois

section Filtration

attribute [local instance] algZpF

variable {F : Fld p} [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F]

theorem coe_galRestrict (s : F ≃ₐ[ℚ_[p]] F) (b : OF F) :
    ((galRestrict ℤ_[p] ℚ_[p] F (OF F) s b : OF F) : F) = s (b : F) :=
  algebraMap_galRestrict_apply ℤ_[p] s b

theorem mem_lowerRam_iff {ϖ : Kbar p} (hϖ : IsUnif F ϖ) (i : ℕ) (s : F ≃ₐ[ℚ_[p]] F) :
    haveI := isLocalRing_OF F
    galRestrict ℤ_[p] ℚ_[p] F (OF F) s ∈ PkgI6.lowerRam ℤ_[p] (OF F) i ↔
      ∀ x : F, ‖(x : Kbar p)‖ ≤ 1 → ‖((s x : F) : Kbar p) - x‖ ≤ ‖ϖ‖ ^ (i + 1) := by
  haveI := isLocalRing_OF F
  rw [PkgI6.mem_lowerRam]
  constructor
  · intro h x hx
    have := (mem_maximalIdeal_pow_iff hϖ (i + 1) _).mp (h ⟨x, (mem_OF F x).mpr hx⟩)
    rw [Subalgebra.coe_sub, coe_galRestrict, AddSubgroupClass.coe_sub] at this
    exact this
  · intro h b
    rw [mem_maximalIdeal_pow_iff hϖ, Subalgebra.coe_sub, coe_galRestrict,
      AddSubgroupClass.coe_sub]
    exact h b (norm_le_one F b)

end Filtration

section Card

attribute [local instance] algZpF

variable {F : Fld p} [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F]

theorem mem_ramSet_iff {ϖ : Kbar p} (hϖ : IsUnif F ϖ) (i : ℕ) (σ : GQp p) :
    haveI := isLocalRing_OF F
    σ ∈ ramSet F i ↔ galRestrict ℤ_[p] ℚ_[p] F (OF F) (AlgEquiv.restrictNormalHom F σ) ∈
      PkgI6.lowerRam ℤ_[p] (OF F) i := by
  haveI := isLocalRing_OF F
  rw [mem_lowerRam_iff hϖ]
  constructor
  · rintro ⟨ϖ', hϖ', h⟩ x hx
    rw [AlgEquiv.restrictNormalHom_apply, ← IsUnif.norm_eq hϖ hϖ']
    exact h x x.2 hx
  · intro h
    refine ⟨ϖ, hϖ, fun x hx hx1 => ?_⟩
    have := h ⟨x, hx⟩ hx1
    rwa [AlgEquiv.restrictNormalHom_apply] at this

theorem card_lowerRam (i : ℕ) :
    haveI := isLocalRing_OF F
    Nat.card (PkgI6.lowerRam ℤ_[p] (OF F) i) = ramCard F i := by
  haveI := isLocalRing_OF F
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif (inferInstance : FiniteDimensional ℚ_[p] F)
  set G := galRestrict ℤ_[p] ℚ_[p] F (OF F) with hG
  set K : Set (F ≃ₐ[ℚ_[p]] F) := {s | G s ∈ PkgI6.lowerRam ℤ_[p] (OF F) i} with hKdef
  have h1 : Nat.card (PkgI6.lowerRam ℤ_[p] (OF F) i) = Nat.card K :=
    (Nat.card_congr (G.toEquiv.subtypeEquiv (fun s => Iff.rfl))).symm
  have hK : K = AlgEquiv.restrictNormalHom F '' ramSet F i := by
    ext s
    constructor
    · intro hs
      obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (Kbar p) s
      exact ⟨σ, (mem_ramSet_iff hϖ i σ).mpr hs, rfl⟩
    · rintro ⟨σ, hσ, rfl⟩
      exact (mem_ramSet_iff hϖ i σ).mp hσ
  set φ : (F ≃ₐ[ℚ_[p]] F) → (F → Kbar p) := fun s x => ((s x : F) : Kbar p) with hφ
  have hφinj : Function.Injective φ := by
    intro s t h
    ext x
    exact congrFun h x
  have himg : restr F '' ramSet F i = φ '' (AlgEquiv.restrictNormalHom F '' ramSet F i) := by
    rw [Set.image_image]
    refine Set.image_congr fun σ _ => ?_
    funext x
    exact (AlgEquiv.restrictNormalHom_apply F σ x).symm
  unfold ramCard
  rw [himg, Nat.card_image_of_injective hφinj, ← hK, h1]

theorem fix_of_lowerRam_bot (i : ℕ) :
    haveI := isLocalRing_OF F
    PkgI6.lowerRam ℤ_[p] (OF F) i = ⊥ → ramSet F i ⊆ fixSet F := by
  haveI := isLocalRing_OF F
  intro hbot σ hσ
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif (inferInstance : FiniteDimensional ℚ_[p] F)
  have h := (mem_ramSet_iff hϖ i σ).mp hσ
  rw [hbot, Subgroup.mem_bot, ← map_one (galRestrict ℤ_[p] ℚ_[p] F (OF F))] at h
  have h1 := (galRestrict ℤ_[p] ℚ_[p] F (OF F)).injective h
  intro x hx
  exact (AlgEquiv.restrictNormal_eq_one_iff F σ).mp h1 x hx

end Card

section FinalZp

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {p : ℕ} [Fact p.Prime]

/-- **`LadicDVRModelZp` (GLUE, proved).** `B = 𝓞_F = integralClosure ℤ_p F`: a DVR (local by the
ultrametric norm, Dedekind as an integral closure, `IsDiscreteValuationRing.TFAE`), finite and
torsion-free over `ℤ_p`, with `Frac(B) ≅ F` Galois over `Frac(ℤ_p) ≅ ℚ_p`
(`IsGalois.of_equiv_equiv`); `𝔪_B^k = {‖b‖ ≤ ‖ϖ‖^k}`, and `galRestrict` identifies
`PkgI6.lowerRam ℤ_p B i` with the restrictions of `ramSet F i`. -/
theorem ladicDVRModelZp : LadicDVRModelZp p := by
  intro F hF
  haveI : FiniteDimensional ℚ_[p] F := hF.1
  haveI : IsGalois ℚ_[p] F := hF.2
  letI := algZpF F
  haveI := torsionFree_OF F
  haveI := faithful_OF F
  haveI := dvr_OF F
  exact ⟨OF F, inferInstance, inferInstance, dvr_OF F, inferInstance, finite_OF F,
    torsionFree_OF F, isSeparable_frac F, isGalois_frac F, card_lowerRam, fix_of_lowerRam_bot⟩

end FinalZp

end DVRModelSec

/-! ## §3. The reduction (proved) -/

section Reduction

theorem gl_eq_one_of_scalar {ℓ : ℕ} [Fact ℓ.Prime] {g : GL (Fin 2) (PadicAlgCl ℓ)}
    {c : PadicAlgCl ℓ} (h : (g : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) = Matrix.scalar (Fin 2) c)
    (hc : c = 1) : g = 1 := by
  apply Units.ext
  rw [h, hc, map_one, Units.val_one]

/-- **`LocalRamG` from the local pieces (GLUE, proved).** -/
theorem localRamG_of {ℓ : ℕ} [Fact ℓ.Prime] (u : ℚ) (p : ℕ) [Fact p.Prime] (hpℓ : p ≠ ℓ)
    (r : GaloisRep ℓ 2) (hUB : UpperBreakFix p) (hUW : UpperWild p) (hWT : WildFixTame p)
    (hd : LocalData p r) (h11 : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) r) :
    LocalRamG u p r := by
  refine ⟨fun hpD t ht σ hσ => ?_, fun hpD σ hσ => ?_, fun hS hM => ?_⟩
  · obtain ⟨F, β, hF, he, hsh, hup⟩ := hd.1 hpD
    have ha : 1 ≤ ZInQ.heightD * ZInQ.heightG0 :=
      Nat.mul_pos GlueDescent.heightD_pos (by unfold ZInQ.heightG0; norm_num)
    have hU0 : (0 : ℝ) ≤ U0 := by unfold U0; positivity
    have hfix : σ ∈ fixSet F := hUB F hF _ ha he t (by unfold U0 at ht; exact ht) hσ
    have hwild : σ ∈ wildSet := hUW t (by linarith) hσ
    exact gl_eq_one_of_scalar (hsh σ ⟨hfix, hwild⟩) (hup t ht σ ⟨hσ, hfix⟩)
  · obtain ⟨F, β, hF, he, hsh, htame⟩ := hd.2 hpD
    have hfix := hWT F hF he hσ
    exact gl_eq_one_of_scalar (hsh σ ⟨hfix, hσ⟩) (htame σ ⟨hfix, hσ⟩)
  · refine h11 p (Fact.out) ?_ hpℓ
    intro hT
    rcases Finset.mem_union.mp hT with h | h
    · exact hS h
    · exact hM (Nat.mem_primeFactors.mp h).2.1

/-- **`G15RamG` from smaller named Props (GLUE, proved).** Closed local-field Props
(`UpperBreakFix`, `UpperWild`, `WildFixTame`), the local data of G8/G7 on `D` (`LocalData`), and
G11's output on `D` for `T = S_mul ∪ supp M_{S_mul}(u)` (`GlueDescent.ramSet`). -/
theorem g15RamG_of_pieces
    (hUB : ∀ (p : ℕ) [Fact p.Prime], UpperBreakFix p)
    (hUW : ∀ (p : ℕ) [Fact p.Prime], UpperWild p)
    (hWT : ∀ (p : ℕ) [Fact p.Prime], WildFixTame p)
    {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalData p ⟨hp⟩ 5 _ D.r5)
    (h3 : LocalData 5 D.r3)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u := by
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨fun h5' => localRamG_of u p h5' D.r5 (hUB p) (hUW p) (hWT p) (h5 p hp h5') h11₅,
    fun h5' => ?_⟩
  subst h5'
  exact localRamG_of u 5 (by norm_num) D.r3 (hUB 5) (hUW 5) (hWT 5) h3 h11₃

/-- **`G15RamG`, with D1 discharged (GLUE, proved).** As `g15RamG_of_pieces`, with
`UpperBreakFix` replaced by the transport `HilbertSerreLadic` of T20 + T21. -/
theorem g15RamG_of_hilbertSerre
    (hHS : ∀ (p : ℕ) [Fact p.Prime], HilbertSerreLadic p)
    (hUW : ∀ (p : ℕ) [Fact p.Prime], UpperWild p)
    (hWT : ∀ (p : ℕ) [Fact p.Prime], WildFixTame p)
    {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalData p ⟨hp⟩ 5 _ D.r5)
    (h3 : LocalData 5 D.r3)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u :=
  g15RamG_of_pieces (fun p _ => upperBreakFix_of_hilbertSerre (hHS p)) hUW hWT D u h5 h3
    h11₅ h11₃

/-- **`G15RamG` from the DVR model, T20-T21 (proved in the kernel), `WildFixTame` and the data
of G7-G8-G11 on `D` (GLUE, proved).** `UpperWild` is proved (`upperWild`). -/
theorem g15RamG_of_model
    (hM : ∀ (p : ℕ) [Fact p.Prime], LadicDVRModel p)
    (hWT : ∀ (p : ℕ) [Fact p.Prime], WildFixTame p)
    {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalData p ⟨hp⟩ 5 _ D.r5)
    (h3 : LocalData 5 D.r3)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u :=
  g15RamG_of_hilbertSerre (fun p _ => hilbertSerre_of_model (hM p)) (fun p _ => upperWild) hWT
    D u h5 h3 h11₅ h11₃

/-- **`G15RamG` with all closed local-field glue proved except the DVR model (GLUE, proved).**
Hypotheses: the transport `LadicDVRModel`, the data of G7-G8 on `D` (`LocalData`), and G11's
output on `D`. -/
theorem g15RamG_of_dvrModel
    (hM : ∀ (p : ℕ) [Fact p.Prime], LadicDVRModel p)
    {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalData p ⟨hp⟩ 5 _ D.r5)
    (h3 : LocalData 5 D.r3)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u :=
  g15RamG_of_model hM (fun p _ => wildFixTame) D u h5 h3 h11₅ h11₃

/-- **`G15RamG` from the `ℤ_p`-model of finite Galois `F ⊆ ℚ̄_p` (GLUE, proved).** -/
theorem g15RamG_of_zpModel
    (hM : ∀ (p : ℕ) [Fact p.Prime], LadicDVRModelZp p)
    {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalData p ⟨hp⟩ 5 _ D.r5)
    (h3 : LocalData 5 D.r3)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u :=
  g15RamG_of_dvrModel (fun p _ => ladicDVRModel_of_Zp (hM p)) D u h5 h3 h11₅ h11₃

/-- The trivial two-dimensional representation (for the non-vacuity check below). -/
def trivRep (ℓ : ℕ) [Fact ℓ.Prime] : GaloisRep ℓ 2 := ⟨1, continuous_const⟩

/-- **Non-vacuity check (proved).** `LocalData p r` holds for the trivial representation (with
`F = ℚ_p`, `β = 1`), so the hypotheses on `D` are not contradictory. -/
theorem localData_trivRep (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime] :
    LocalData p (trivRep ℓ) := by
  have hF : IsFinGal (⊥ : Fld p) := ⟨inferInstance, inferInstance⟩
  have hshape : TwistShape p (trivRep ℓ) ⊥ (fun _ => 1) := by
    intro σ _
    simp [trivRep, PkgI4.GaloisRep.restrictLocal]
  have he : ramCard (⊥ : Fld p) 0 = 1 := by
    have h1 := one_le_ramCard hF 0
    have h2 : ramCard (⊥ : Fld p) 0 ≤ 1 := by
      unfold ramCard
      have hfin := (finite_restr hF (ramSet (⊥ : Fld p) 0)).to_subtype
      refine Finite.card_le_one_iff_subsingleton.mpr ⟨fun a b => ?_⟩
      apply Subtype.ext
      obtain ⟨σ, -, hσ⟩ := a.2
      obtain ⟨τ, -, hτ⟩ := b.2
      rw [← hσ, ← hτ]
      funext x
      obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp x.2
      simp only [restr, ← hq, AlgEquiv.commutes]
    omega
  refine ⟨fun _ => ⟨⊥, fun _ => 1, hF, ?_, hshape, fun _ _ _ _ => rfl⟩,
    fun _ => ⟨⊥, fun _ => 1, hF, ?_, hshape, fun _ _ => rfl⟩⟩
  · rw [he]; exact Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  · rw [he]; exact (Nat.Prime.one_lt Fact.out).ne' ∘ Nat.dvd_one.mp

/-- **`G15RamG` from the data of G7-G8 on `D` and G11's output alone (GLUE, proved).** Every
closed local-field input is proved: `UpperBreakFix` (from T20, T21 and `ladicDVRModelZp`),
`UpperWild`, `WildFixTame`. -/
theorem g15RamG_of_localData
    {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalData p ⟨hp⟩ 5 _ D.r5)
    (h3 : LocalData 5 D.r3)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u :=
  g15RamG_of_zpModel (fun _ _ => ladicDVRModelZp) D u h5 h3 h11₅ h11₃

end Reduction

end G15Ram
end

noncomputable section

namespace G15Ram

open PkgI4 (GQp GaloisRep)
open LadicCond G0ModNewform

/-- **Clauses (i)-(ii) of `LocalRamG` from the local data alone** (g0-assemble2; the first two
bullets of g15-ram's `localRamG_of`, whose third bullet is G11's output; the closed local-field
inputs `UpperBreakFix` (T20, T21), `UpperWild`, `WildFixTame` are g15-ram's theorems). -/
theorem localRamWild_of_localData {ℓ : ℕ} [Fact ℓ.Prime] (p : ℕ) [Fact p.Prime]
    (r : GaloisRep ℓ 2) (hd : LocalData p r) :
    HSyn.G0AssembleMod.LocalRamWild p r := by
  have hUB : UpperBreakFix p :=
    upperBreakFix_of_hilbertSerre (hilbertSerre_of_model (ladicDVRModel_of_Zp ladicDVRModelZp))
  have hUW : UpperWild p := upperWild
  have hWT : WildFixTame p := wildFixTame
  refine ⟨fun hpD t ht σ hσ => ?_, fun hpD σ hσ => ?_⟩
  · obtain ⟨F, β, hF, he, hsh, hup⟩ := hd.1 hpD
    have ha : 1 ≤ ZInQ.heightD * ZInQ.heightG0 :=
      Nat.mul_pos GlueDescent.heightD_pos (by unfold ZInQ.heightG0; norm_num)
    have hU0 : (0 : ℝ) ≤ U0 := by unfold U0; positivity
    have hfix : σ ∈ fixSet F := hUB F hF _ ha he t (by unfold U0 at ht; exact ht) hσ
    have hwild : σ ∈ wildSet := hUW t (by linarith) hσ
    exact gl_eq_one_of_scalar (hsh σ ⟨hfix, hwild⟩) (hup t ht σ ⟨hσ, hfix⟩)
  · obtain ⟨F, β, hF, he, hsh, htame⟩ := hd.2 hpD
    have hfix := hWT F hF he hσ
    exact gl_eq_one_of_scalar (hsh σ ⟨hfix, hσ⟩) (htame σ ⟨hfix, hσ⟩)

/-- **`G15RamWild` from the local data of `r₅`, `r₃`** (g0-assemble2). -/
theorem g15RamWild_of_localData {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L}
    (D : ModData L A)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalData p ⟨hp⟩ 5 _ D.r5)
    (h3 : LocalData 5 D.r3) : HSyn.G0AssembleMod.G15RamWild D := by
  intro p hp
  refine ⟨fun h5' => @localRamWild_of_localData 5 _ p ⟨hp⟩ D.r5 (h5 p hp h5'), fun h5' => ?_⟩
  subst h5'
  exact localRamWild_of_localData 5 D.r3 h3

end G15Ram

namespace HSyn.G0AssembleMod

open CategoryTheory AlgebraicGeometry
open G0ModField

/-- **Glue: linked Tate data with the Frobenius link and the local data** (g0-assemble2; replaces
g0-assemble's `LinkedTateData`, which asked for `G14TraceCompat` and `G15RamWild` themselves).
For every fibre context and G7 data: one pair `a, β : G_ℚ → ℚ̄` and embeddings `j₅, j₃` (the scalar
link, N5 L719-722), operator data at `ℓ = 5, 3` with g0-mod-galois' `G7Out` for the scalars
`j_ℓ ∘ a`, `j_ℓ ∘ β`, g14-trace's `FrobTraceLink` (N5 L781-786), and, for every `r₅`, `r₃` that G8
attaches to these data, g15-ram's `LocalData` (N5 L819-852: the local Galois closure and twist at
each `p`). `G14TraceCompat` then follows from T7 (g14-trace) and `G15RamWild` from the local
ramification theory (g15-ram, with T20, T21 proved in the kernel). -/
def LinkedTateLocal : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    letI : NumberField L' := numberField_of_fd L'
    ∃ (aQ βQ : PkgI4.GQ → PkgI4.Qbar) (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
      (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3)
      (Tm₅ : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c₅ ε₅ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5)
      (u₅ : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (Tm₃ : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c₃ ε₃ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3)
      (u₃ : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3)),
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 Tm₅ c₅ ε₅
        (fun g => j5 (aQ g)) (fun g => j5 (βQ g)) u₅ ∧
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 Tm₃ c₃ ε₃
        (fun g => j3 (aQ g)) (fun g => j3 (βQ g)) u₃ ∧
      G14Trace.FrobTraceLink (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Tm₅ Tm₃ ∧
      ∀ (r₅ : PkgI4.GaloisRep 5 2) (r₃ : PkgI4.GaloisRep 3 2),
        G0Galois.G8Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5
          (GlueDescent.rho Tm₅ (fun g => j5 (aQ g)) (fun g => j5 (βQ g))) r₅ →
        G0Galois.G8Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3
          (GlueDescent.rho Tm₃ (fun g => j3 (aQ g)) (fun g => j3 (βQ g))) r₃ →
        (∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @G15Ram.LocalData p ⟨hp⟩ 5 _ r₅) ∧
          G15Ram.LocalData 5 r₃

/-- **g0-assemble's `LinkedTateData` from `LinkedTateLocal` and T7** (g0-assemble2): `ι₃ := j₃ ∘ γ`
where `ι₅ = j₅ ∘ γ` (g14-trace's `exists_comp_eq`); `G14TraceCompat` by g14-trace's
`g14TraceCompat_of_link`; `G15RamWild` by `G15Ram.g15RamWild_of_localData`. -/
theorem linkedTateData_of_local (hM : PkgI3.CharPolyIndepOfEll) (h : LinkedTateLocal) :
    LinkedTateData := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD
  letI : NumberField L' := numberField_of_fd L'
  have h' := h Y Φ π u P hctx L A ε N χ β L' hLL' hD
  obtain ⟨aQ, βQ, j5, j3, Tm₅, c₅, ε₅, u₅, Tm₃, c₃, ε₃, u₃, h5, h3, hF, hloc⟩ := h'
  refine ⟨Tm₅, c₅, ε₅, _, _, u₅, Tm₃, c₃, ε₃, _, _, u₃, h5, h3,
    fun r₅ r₃ h8₅ h8₃ i ιC ι5 => ?_⟩
  obtain ⟨γ, hγ⟩ := G14Trace.exists_comp_eq ι5 j5
  obtain ⟨hl5, hl3⟩ := hloc r₅ r₃ h8₅ h8₃
  exact ⟨j3.comp γ,
    G14Trace.g14TraceCompat_of_link hM ⟨i, ιC, ι5, j3.comp γ, r₅, r₃⟩ j5 j3 γ hγ rfl aQ βQ
      Tm₅ Tm₃ h8₅ h8₃ hF,
    G15Ram.g15RamWild_of_localData _ hl5 hl3⟩

end HSyn.G0AssembleMod

end
