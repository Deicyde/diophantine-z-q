import ZInQKernel.Contrib.OneProof.AfTateOr
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.LocalGlobal.Completion

/-! # aftate-fix2: `r16CoreY` from Diamond–Shurman's `A_f`, universally, over `K_{f,λ}`

Task aftate-fix2 (2026-11-16), report `docs/research/aftate-fix2.md`, scratch `scratch/aftate-fix2/`.

**Target.** The bundle field `r16CoreY : R16Split.R16CoreY`. aftate-or discharged it from the leaf
`AfTateOr.AfTateDSOr`, which the review rated GLUE: (1) `A_f` was existential; (2) the "satisfies" reading
of DS 9.5.4; (3) the leaf was stated over `ℚ_ℓ ⊗ K_f`, the print over `K_{f,λ}`.

**New leaves** (§5), all over genuine definitions (§§1–4):
* `HeckeJ1DS` (Diamond–Shurman §6.3, §7.9): the Hecke operators `T_p` and `⟨d⟩` on `J₁(N)` exist over `ℚ`,
  with DS's double-coset action on divisor classes of the points `x_τ` (`IsHeckeT`, `IsDiamond`; the
  points `x_τ ∈ X(ℂ)` are cut out by the values of `K(X) = ℚ(j, f₁)` at `τ`, `AtTau`).
* `AfShimura` (Shimura 1973 Thm 1): `K_f` is a number field and `A_f = J₁(N)/I_f J₁(N)` exists over `ℚ`
  with its `K_f`-action (`IsAfQuotient`: surjective, kills `I_f J`, universal; `IsAfAction`:
  `θ(a_p) = T_p|A_f`, `θ(χ(d)) = ⟨d⟩|A_f`; `I_f` = kernel of `T_p ↦ a_p`, `⟨d⟩ ↦ χ(d)` on the free algebra).
  Now proved: `AfTateLam.afShimura_proof` (`AfShimuraProof.lean`); it carries only quotient existence, the coefficient recurrence and finiteness of `K_f`, so it is weaker than Shimura 1973 Thm 1, and its proof is not a Lean proof of that theorem.
* `AfTateDSLambda` (DS Thm 9.5.4): **for every** `(A, π, θ)` as in `AfShimura`, every `ℓ` and every place
  `λ ∣ ℓ` of `K_f`, Frobenius at `p ∤ Nℓ` on `V_λ = K_{f,λ} ⊗_{ℚ_ℓ ⊗ K_f} V_ℓ(A)` has characteristic
  polynomial `X² − a_p X + χ(p) p` over `K_{f,λ} = λ.adicCompletion K_f`.

**Glue proved here.** §0: precomposition by `g` on the functionals `V → Ω` semilinear along
`ε ∘ ρ_L : R → L → Ω` has trace and determinant `ε(tr, det of L ⊗_R g)` (basis `1 ⊗ v_i` of `L ⊗_R V`);
§0b: coeff-ext's place `λ_ι` and `ι̂ : K_λ → ℚ̄_ℓ` (copied); §6: `λ_ι ∣ ℓ`, `ι̂` restricted to `ℚ_ℓ` is the
structure map (density of `ℚ`), and `component`: the kernel's `ι`-component `frobOn` has the dimension of
`V_λ` and trace/determinant `ι̂(tr/det ρ_{f,λ})`; §7: `r16CoreY_of_printed`; §8: `dsLambda_of_tensor` (the
`K_{f,λ}` leaf follows from the `ℚ_ℓ ⊗ K_f` form `AfTateDSTensor` of DS 9.5.4, by base change of a basis);
§9: `dsLambda_of_sat_det` (a fallback for the "satisfies" reading: dimension 2 + "satisfies"
(`AfTateDSLambdaSat`) and a separate determinant statement (`AfDetLambda`) give the leaf; neither is in the fold).

No `sorry`, no `axiom`, no build-time code. -/

noncomputable section

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 40000

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

namespace AfTateLam

open scoped TensorProduct

/-! ## 0. Generic: functionals semilinear along `io = eps ∘ ρ_L` and the base change `L ⊗_R V` -/

section Generic

variable {k R V Ω L : Type*} [Field k] [CommRing R] [Algebra k R] [AddCommGroup V] [Module k V]
  [Module R V] [IsScalarTower k R V] [Field Ω] [Algebra k Ω] [Field L] [Algebra R L]
  (io : R →+* Ω) (eps : L →+* Ω) (E : Submodule Ω (V →ₗ[k] Ω))

/-- `v ↦ 1 ⊗ v`, `V → L ⊗_R V`. -/
def mk1 : V →ₗ[R] L ⊗[R] V := TensorProduct.mk R L V 1

theorem span_mk1 : Submodule.span L (Set.range (mk1 (L := L) (R := R) (V := V))) = ⊤ := by
  have key : ∀ t : L ⊗[R] V, t ∈ Submodule.span L (Set.range (mk1 (L := L) (R := R) (V := V))) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul l v =>
      have : l ⊗ₜ[R] v = l • mk1 (L := L) v := by
        simp [mk1, TensorProduct.smul_tmul']
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, rfl⟩)
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  exact eq_top_iff.2 fun t _ => key t

/-- The additive lift `l ⊗ v ↦ eps(l) φ(v)` of a semilinear functional. -/
def liftφ (heps : ∀ r : R, eps (algebraMap R L r) = io r) (φ : V →ₗ[k] Ω) (hφ : ∀ (r : R) (v : V), φ (r • v) = io r * φ v) :
    L ⊗[R] V →+ Ω :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun l : L => AddMonoidHom.mk' (fun v : V => eps l * φ v)
        (by intro a b; rw [map_add, mul_add]))
      (by intro a b; ext v; simp [add_mul]))
    (by
      intro r l v
      simp only [AddMonoidHom.mk'_apply, Algebra.smul_def, map_mul, heps, hφ]
      ring)

theorem liftφ_tmul (heps : ∀ r : R, eps (algebraMap R L r) = io r) (φ : V →ₗ[k] Ω) (hφ : ∀ (r : R) (v : V), φ (r • v) = io r * φ v) (l : L) (v : V) :
    liftφ io eps heps φ hφ (l ⊗ₜ v) = eps l * φ v := by
  simp [liftφ]

theorem liftφ_smul (heps : ∀ r : R, eps (algebraMap R L r) = io r) (φ : V →ₗ[k] Ω) (hφ : ∀ (r : R) (v : V), φ (r • v) = io r * φ v) (l : L)
    (t : L ⊗[R] V) : liftφ io eps heps φ hφ (l • t) = eps l * liftφ io eps heps φ hφ t := by
  induction t using TensorProduct.inductionOn with
  | tmul l' v =>
    rw [TensorProduct.smul_tmul', liftφ_tmul, liftφ_tmul, smul_eq_mul, map_mul, mul_assoc]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, mul_add]

variable [FiniteDimensional L (L ⊗[R] V)]

/-- A finite set of vectors `1 ⊗ v` forming a basis of `L ⊗_R V`. -/
theorem exists_basis_mk1 :
    ∃ s : Set (L ⊗[R] V), s ⊆ Set.range (mk1 (L := L) (R := R) (V := V)) ∧
      LinearIndependent L ((↑) : s → L ⊗[R] V) ∧ Submodule.span L s = ⊤ := by
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent L (Set.range (mk1 (L := L) (R := R) (V := V)))
  exact ⟨s, hs, hli, hspan.trans span_mk1⟩

/-- The chosen spanning set. -/
def sB : Set (L ⊗[R] V) := (exists_basis_mk1 (L := L) (R := R) (V := V)).choose

theorem sB_sub : sB (L := L) (R := R) (V := V) ⊆ Set.range (mk1 (L := L) (R := R) (V := V)) :=
  (exists_basis_mk1 (L := L) (R := R) (V := V)).choose_spec.1

theorem sB_li : LinearIndependent L ((↑) : sB (L := L) (R := R) (V := V) → L ⊗[R] V) :=
  (exists_basis_mk1 (L := L) (R := R) (V := V)).choose_spec.2.1

theorem sB_span : Submodule.span L (sB (L := L) (R := R) (V := V)) = ⊤ :=
  (exists_basis_mk1 (L := L) (R := R) (V := V)).choose_spec.2.2

/-- The basis of `L ⊗_R V` by vectors `1 ⊗ v`. -/
def bL : Module.Basis (sB (L := L) (R := R) (V := V)) L (L ⊗[R] V) :=
  Module.Basis.mk (sB_li (L := L) (R := R) (V := V))
    (by rw [Subtype.range_coe]; exact (sB_span (L := L) (R := R) (V := V)).ge)

instance : Fintype (sB (L := L) (R := R) (V := V)) :=
  @Fintype.ofFinite _ (Module.Finite.finite_basis (bL (L := L) (R := R) (V := V)))

/-- `v_i ∈ V` with `1 ⊗ v_i = b_i`. -/
def vB (i : sB (L := L) (R := R) (V := V)) : V := (sB_sub i.2).choose

theorem mk1_vB (i : sB (L := L) (R := R) (V := V)) : mk1 (L := L) (vB i) = bL (L := L) (R := R) (V := V) i := by
  rw [bL, Module.Basis.mk_apply]; exact (sB_sub i.2).choose_spec

/-- The functional `φ_j : v ↦ eps(b_j^*(1 ⊗ v))`. -/
def phiB (hik : ∀ x : k, io (algebraMap k R x) = algebraMap k Ω x) (heps : ∀ r : R, eps (algebraMap R L r) = io r) (j : sB (L := L) (R := R) (V := V)) : V →ₗ[k] Ω where
  toFun v := eps ((bL (L := L) (R := R) (V := V)).coord j (mk1 (L := L) v))
  map_add' u v := by rw [map_add, map_add, map_add]
  map_smul' c v := by
    rw [RingHom.id_apply, ← algebraMap_smul R c v, LinearMap.map_smul, ← algebraMap_smul L,
      LinearMap.map_smul, smul_eq_mul, map_mul, heps, hik, Algebra.smul_def]

theorem phiB_apply (hik : ∀ x : k, io (algebraMap k R x) = algebraMap k Ω x) (heps : ∀ r : R, eps (algebraMap R L r) = io r) (j : sB (L := L) (R := R) (V := V)) (v : V) :
    phiB io eps hik heps j v = eps ((bL (L := L) (R := R) (V := V)).coord j (mk1 (L := L) v)) := rfl

theorem phiB_semilin (hik : ∀ x : k, io (algebraMap k R x) = algebraMap k Ω x) (heps : ∀ r : R, eps (algebraMap R L r) = io r) (j : sB (L := L) (R := R) (V := V)) (r : R) (v : V) :
    phiB io eps hik heps j (r • v) = io r * phiB io eps hik heps j v := by
  rw [phiB_apply, phiB_apply, LinearMap.map_smul, ← algebraMap_smul L, LinearMap.map_smul,
    smul_eq_mul, map_mul, heps]

theorem phiB_vB (hik : ∀ x : k, io (algebraMap k R x) = algebraMap k Ω x) (heps : ∀ r : R, eps (algebraMap R L r) = io r) (i j : sB (L := L) (R := R) (V := V)) :
    phiB io eps hik heps j (vB i) = if i = j then 1 else 0 := by
  rw [phiB_apply, mk1_vB, Module.Basis.coord_apply, Module.Basis.repr_self]
  by_cases h : i = j
  · subst h; simp
  · rw [Finsupp.single_eq_of_ne (Ne.symm h), map_zero, if_neg h]

/-- **Expansion of a semilinear functional** in the `φ_j`. -/
theorem eq_sum_phiB (hik : ∀ x : k, io (algebraMap k R x) = algebraMap k Ω x) (heps : ∀ r : R, eps (algebraMap R L r) = io r) (φ : V →ₗ[k] Ω) (hφ : ∀ (r : R) (v : V), φ (r • v) = io r * φ v) (v : V) :
    φ v = ∑ j, φ (vB j) * phiB io eps hik heps j v := by
  have h1 : φ v = liftφ io eps heps φ hφ (mk1 (L := L) v) := by
    rw [mk1, TensorProduct.mk_apply, liftφ_tmul, map_one, one_mul]
  rw [h1, ← (bL (L := L) (R := R) (V := V)).sum_repr (mk1 (L := L) v), map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [liftφ_smul, ← mk1_vB]
  simp only [mk1, TensorProduct.mk_apply, liftφ_tmul, map_one, one_mul, phiB_apply,
    Module.Basis.coord_apply]
  ring

theorem phiB_mem (hik : ∀ x : k, io (algebraMap k R x) = algebraMap k Ω x) (heps : ∀ r : R, eps (algebraMap R L r) = io r) (hE : ∀ φ : V →ₗ[k] Ω, φ ∈ E ↔ ∀ (r : R) (v : V), φ (r • v) = io r * φ v) (j : sB (L := L) (R := R) (V := V)) : phiB io eps hik heps j ∈ E :=
  (hE _).2 (phiB_semilin io eps hik heps j)

/-- The coordinate isomorphism `E ≃ Ω^s`, `φ ↦ (φ(v_j))_j`. -/
def coordE (hik : ∀ x : k, io (algebraMap k R x) = algebraMap k Ω x) (heps : ∀ r : R, eps (algebraMap R L r) = io r) (hE : ∀ φ : V →ₗ[k] Ω, φ ∈ E ↔ ∀ (r : R) (v : V), φ (r • v) = io r * φ v) : E ≃ₗ[Ω] (sB (L := L) (R := R) (V := V) → Ω) where
  toFun φ j := (φ : V →ₗ[k] Ω) (vB j)
  map_add' _ _ := by ext j; simp
  map_smul' _ _ := by ext j; simp
  invFun a := ⟨∑ j, a j • phiB io eps hik heps j, Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (phiB_mem io eps E hik heps hE j)⟩
  left_inv φ := by
    apply Subtype.ext; apply LinearMap.ext; intro v
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    exact (eq_sum_phiB io eps hik heps (φ : V →ₗ[k] Ω) ((hE _).1 φ.2) v).symm
  right_inv a := by
    funext i
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      phiB_vB, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem finrank_E (hik : ∀ x : k, io (algebraMap k R x) = algebraMap k Ω x) (heps : ∀ r : R, eps (algebraMap R L r) = io r) (hE : ∀ φ : V →ₗ[k] Ω, φ ∈ E ↔ ∀ (r : R) (v : V), φ (r • v) = io r * φ v) : Module.finrank Ω E = Module.finrank L (L ⊗[R] V) := by
  rw [(coordE io eps E hik heps hE).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Module.finrank_eq_card_basis (bL (L := L) (R := R) (V := V))]

/-- The basis of `E` dual to `(v_i)`. -/
def basisE (hik : ∀ x : k, io (algebraMap k R x) = algebraMap k Ω x) (heps : ∀ r : R, eps (algebraMap R L r) = io r) (hE : ∀ φ : V →ₗ[k] Ω, φ ∈ E ↔ ∀ (r : R) (v : V), φ (r • v) = io r * φ v) : Module.Basis (sB (L := L) (R := R) (V := V)) Ω E :=
  Module.Basis.ofEquivFun (coordE io eps E hik heps hE)

theorem basisE_repr (hik : ∀ x : k, io (algebraMap k R x) = algebraMap k Ω x) (heps : ∀ r : R, eps (algebraMap R L r) = io r) (hE : ∀ φ : V →ₗ[k] Ω, φ ∈ E ↔ ∀ (r : R) (v : V), φ (r • v) = io r * φ v) (φ : E) (i : sB (L := L) (R := R) (V := V)) :
    (basisE io eps E hik heps hE).repr φ i = (φ : V →ₗ[k] Ω) (vB i) := by
  rw [basisE, Module.Basis.ofEquivFun_repr_apply]; rfl

/-- **Precomposition by `g` on `E` is the transpose of `eps(g_L)`.** -/
theorem toMatrix_precomp (hik : ∀ x : k, io (algebraMap k R x) = algebraMap k Ω x) (heps : ∀ r : R, eps (algebraMap R L r) = io r) (hE : ∀ φ : V →ₗ[k] Ω, φ ∈ E ↔ ∀ (r : R) (v : V), φ (r • v) = io r * φ v) (g : V →ₗ[R] V) (T : E →ₗ[Ω] E)
    (hT : ∀ φ : E, (T φ : V →ₗ[k] Ω) = (φ : V →ₗ[k] Ω) ∘ₗ (g.restrictScalars k)) :
    LinearMap.toMatrix (basisE io eps E hik heps hE) (basisE io eps E hik heps hE) T =
      ((LinearMap.toMatrix (bL (L := L) (R := R) (V := V)) (bL (L := L) (R := R) (V := V))
        (g.baseChange L)).map eps).transpose := by
  ext i j
  rw [LinearMap.toMatrix_apply, basisE_repr, hT, Matrix.transpose_apply, Matrix.map_apply,
    LinearMap.toMatrix_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  have hj : ((basisE io eps E hik heps hE j : E) : V →ₗ[k] Ω) = phiB io eps hik heps j := by
    rw [basisE, Module.Basis.coe_ofEquivFun]
    change (∑ i, (Pi.single j (1 : Ω) : _ → Ω) i • phiB io eps hik heps i) = phiB io eps hik heps j
    simp [Pi.single_apply]
  rw [hj, phiB_apply, ← mk1_vB, mk1, TensorProduct.mk_apply, TensorProduct.mk_apply,
    LinearMap.baseChange_tmul, Module.Basis.coord_apply]

theorem trace_det_precomp (hik : ∀ x : k, io (algebraMap k R x) = algebraMap k Ω x) (heps : ∀ r : R, eps (algebraMap R L r) = io r) (hE : ∀ φ : V →ₗ[k] Ω, φ ∈ E ↔ ∀ (r : R) (v : V), φ (r • v) = io r * φ v) (g : V →ₗ[R] V) (T : E →ₗ[Ω] E)
    (hT : ∀ φ : E, (T φ : V →ₗ[k] Ω) = (φ : V →ₗ[k] Ω) ∘ₗ (g.restrictScalars k)) :
    LinearMap.trace Ω E T = eps (LinearMap.trace L _ (g.baseChange L)) ∧
      @LinearMap.det E _ Ω _ _ T = eps (LinearMap.det (g.baseChange L)) := by
  have h := toMatrix_precomp io eps E hik heps hE g T hT
  constructor
  · rw [LinearMap.trace_eq_matrix_trace Ω (basisE io eps E hik heps hE), h, Matrix.trace_transpose,
      LinearMap.trace_eq_matrix_trace L (bL (L := L) (R := R) (V := V)), Matrix.trace,
      Matrix.trace, map_sum]
    rfl
  · rw [← LinearMap.det_toMatrix (basisE io eps E hik heps hE), h, Matrix.det_transpose,
      ← LinearMap.det_toMatrix (bL (L := L) (R := R) (V := V)), RingHom.map_det]
    rfl

end Generic


/-! ## 0b. The place `λ_τ` of an embedding `τ : K → ℚ̄_ℓ` and `τ̂ : K_λ → ℚ̄_ℓ` (copied verbatim from coeff-ext's
`ZInQKernel/Contrib/OneProof/DSCoeffExt.lean`, branch wip/coeff-ext d0256cea, §§2–4) -/

section CoeffExtCopy

open NumberField IsDedekindDomain

/-! ## 2. Norms on `ℚ̄_ℓ` -/

section Norm

open Polynomial

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- Copy of `SwanBridge.isIntegral_iff_norm_le_one` (forward direction). -/
theorem norm_le_one_of_isIntegral (y : PadicAlgCl ℓ) (hy : IsIntegral ℤ_[ℓ] y) : ‖y‖ ≤ 1 := by
  have hyQ : IsIntegral ℚ_[ℓ] y := (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hyQ)]
  intro n
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[ℓ] hy, coeff_map]
  exact PadicInt.norm_le_one _

theorem norm_le_one_of_isIntegral_int (y : PadicAlgCl ℓ) (hy : IsIntegral ℤ y) : ‖y‖ ≤ 1 :=
  norm_le_one_of_isIntegral y (hy.tower_top)

theorem norm_natCast_prime : ‖(ℓ : PadicAlgCl ℓ)‖ < 1 := by
  have : (ℓ : PadicAlgCl ℓ) = algebraMap ℚ_[ℓ] (PadicAlgCl ℓ) (ℓ : ℚ_[ℓ]) := by simp
  rw [this, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

end Norm

/-! ## 3. The place of a number field cut out by an embedding into `ℚ̄_ℓ` -/

section Place

variable {ℓ : ℕ} [Fact ℓ.Prime] {K : Type*} [Field K] [NumberField K] (τ : K →+* PadicAlgCl ℓ)

theorem norm_le_one_int (a : 𝓞 K) : ‖τ (a : K)‖ ≤ 1 :=
  norm_le_one_of_isIntegral_int _ ((a.isIntegral_coe).map τ.toIntAlgHom)

/-- The prime ideal `{a ∈ 𝓞_K : ‖τ a‖ < 1}`. -/
def placeIdeal : Ideal (𝓞 K) where
  carrier := {a | ‖τ (a : K)‖ < 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, norm_mul] at *
    calc ‖τ (c : K)‖ * ‖τ (a : K)‖ ≤ 1 * ‖τ (a : K)‖ :=
          mul_le_mul_of_nonneg_right (norm_le_one_int τ c) (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact ha

theorem mem_placeIdeal {a : 𝓞 K} : a ∈ placeIdeal τ ↔ ‖τ (a : K)‖ < 1 := Iff.rfl

theorem natCast_mem_placeIdeal : (ℓ : 𝓞 K) ∈ placeIdeal τ := by
  rw [mem_placeIdeal]
  simpa using (norm_natCast_prime (ℓ := ℓ))

/-- The place `λ_τ` of `K` above `ℓ` cut out by `τ : K → ℚ̄_ℓ`. -/
def place : HeightOneSpectrum (𝓞 K) where
  asIdeal := placeIdeal τ
  isPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one, mem_placeIdeal]
      simp
    · intro a b hab
      rw [mem_placeIdeal] at hab
      simp only [map_mul, norm_mul] at hab
      by_contra h
      push Not at h
      rw [mem_placeIdeal, mem_placeIdeal, not_lt, not_lt] at h
      have ha : ‖τ (a : K)‖ = 1 := le_antisymm (norm_le_one_int τ a) h.1
      have hb : ‖τ (b : K)‖ = 1 := le_antisymm (norm_le_one_int τ b) h.2
      rw [ha, hb, one_mul] at hab
      exact lt_irrefl _ hab
  ne_bot := by
    intro h
    have h1 := natCast_mem_placeIdeal (K := K) τ
    rw [h, Ideal.mem_bot] at h1
    exact (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero) h1

theorem norm_eq_one_of_not_mem {d : 𝓞 K} (hd : d ∉ (place τ).asIdeal) : ‖τ (d : K)‖ = 1 :=
  le_antisymm (norm_le_one_int τ d) (not_lt.1 hd)

/-- Valuation comparison: `v_λ(x) ≤ v_λ(y)` gives `‖τ x‖ ≤ ‖τ y‖`. -/
theorem norm_le_of_valuation_le {x y : K} (hy : y ≠ 0)
    (h : (place τ).valuation K x ≤ (place τ).valuation K y) : ‖τ x‖ ≤ ‖τ y‖ := by
  have hv : (place τ).valuation K (x / y) ≤ 1 := by
    rw [map_div₀]
    have : (place τ).valuation K y ≠ 0 := by simpa using hy
    exact (div_le_one₀ (zero_lt_iff.2 this)).2 h
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (place τ) _ hv
  have hd : ‖τ (d : 𝓞 K)‖ = 1 := norm_eq_one_of_not_mem τ d.2
  have hn := norm_le_one_int τ n
  have e := congrArg (fun z => ‖τ z‖) hnd
  simp only [map_mul, norm_mul, map_div₀, norm_div] at e
  have hd' : ‖τ (algebraMap (𝓞 K) K (d : 𝓞 K))‖ = 1 := hd
  rw [hd', mul_one] at e
  have hyn : 0 < ‖τ y‖ := norm_pos_iff.2 ((map_ne_zero τ).2 hy)
  have : ‖τ x‖ / ‖τ y‖ ≤ 1 := e ▸ hn
  exact (div_le_one₀ hyn).1 this

end Place

/-! ## 4. Extension to the completion `K_λ` -/

section Completion

variable {ℓ : ℕ} [Fact ℓ.Prime] {K : Type*} [Field K] [NumberField K] (τ : K →+* PadicAlgCl ℓ)

/-- `τ` as a ring hom on `WithVal v_λ`. -/
def τW : WithVal ((place τ).valuation K) →+* PadicAlgCl ℓ :=
  τ.comp (WithVal.equiv ((place τ).valuation K)).toRingHom

theorem continuous_τW : Continuous (τW τ) := by
  refine continuous_of_continuousAt_zero (τW τ).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hs
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (norm_natCast_prime (ℓ := ℓ))
  set y : K := (ℓ : K) ^ m
  have hy : y ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero)
  set yW : WithVal ((place τ).valuation K) := WithVal.toVal _ y
  have hyv : (Valued.v : Valuation (WithVal ((place τ).valuation K)) _) yW ≠ 0 := by
    rw [← WithVal.apply_ofVal]
    simpa [yW] using hy
  have hres : (Valued.v : Valuation (WithVal ((place τ).valuation K)) _).restrict yW ≠ 0 := by
    rwa [Ne, Valuation.restrict_eq_zero_iff]
  rw [Filter.mem_map, Valued.mem_nhds_zero]
  refine ⟨Units.mk0 _ hres, fun x hx => ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hx
  show (τW τ) x ∈ s
  apply hball
  rw [Metric.mem_ball, dist_zero_right]
  have hle : (place τ).valuation K (WithVal.ofVal x) ≤ (place τ).valuation K y := by
    rw [WithVal.apply_ofVal, WithVal.apply_ofVal]
    exact hx.le
  calc ‖τW τ x‖ = ‖τ (WithVal.ofVal x)‖ := rfl
    _ ≤ ‖τ y‖ := norm_le_of_valuation_le τ hy hle
    _ = ‖(ℓ : PadicAlgCl ℓ)‖ ^ m := by simp [y]
    _ < ε := hm

/-- A finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ` containing `τ(K)`. -/
def tgt : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ) :=
  IntermediateField.adjoin ℚ_[ℓ] (Set.range (fun i => τ (Module.finBasis ℚ K i)))

instance : FiniteDimensional ℚ_[ℓ] (tgt τ) :=
  IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsIntegral.isIntegral x))

theorem mem_tgt (x : K) : τ x ∈ tgt τ := by
  rw [← (Module.finBasis ℚ K).sum_repr x, map_sum]
  refine sum_mem fun i _ => ?_
  rw [Algebra.smul_def, map_mul, eq_ratCast, map_ratCast]
  exact mul_mem (SubfieldClass.ratCast_mem _ _)
    (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)

instance : CompleteSpace (tgt τ) := by
  have : FiniteDimensional ℚ_[ℓ] ((tgt τ).toSubalgebra.toSubmodule) :=
    (inferInstance : FiniteDimensional ℚ_[ℓ] (tgt τ))
  exact (Submodule.complete_of_finiteDimensional ((tgt τ).toSubalgebra.toSubmodule)).completeSpace_coe

/-- `τ` into the complete field `tgt τ`. -/
def τE : WithVal ((place τ).valuation K) →+* tgt τ :=
  (τW τ).codRestrict (tgt τ) (fun _ => mem_tgt τ _)

theorem continuous_τE : Continuous (τE τ) :=
  Continuous.subtype_mk (continuous_τW τ) _

/-- The continuous extension `K_λ → ℚ̄_ℓ` of `τ`. -/
def τhat : (place τ).adicCompletion K →+* PadicAlgCl ℓ :=
  ((tgt τ).val.toRingHom.comp (UniformSpace.Completion.extensionHom (τE τ) (continuous_τE τ))).comp
    (HeightOneSpectrum.adicCompletion.equiv K (place τ)).toRingHom

theorem continuous_τhat : Continuous (τhat τ) :=
  continuous_subtype_val.comp ((UniformSpace.Completion.continuous_extension).comp
    (HeightOneSpectrum.adicCompletion.continuous_toCompletion K (place τ)))

theorem τhat_algebraMap (x : K) : τhat τ (algebraMap K ((place τ).adicCompletion K) x) = τ x := by
  simp only [τhat, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]
  have : (HeightOneSpectrum.adicCompletion.equiv K (place τ))
      (algebraMap K ((place τ).adicCompletion K) x) =
      ((WithVal.toVal ((place τ).valuation K) x : WithVal _) :
        ((place τ).valuation K).Completion) := rfl
  rw [this, UniformSpace.Completion.extensionHom_coe]
  rfl

end Completion

end CoeffExtCopy

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open LeafModCurves PkgI3 PkgI3.AbVar
open PkgI4 (Qbar GQ CF coeff IsNewform)
open scoped TensorProduct MatrixGroups



/-! ## 1. The uniformization `τ ↦ x_τ ∈ X(ℂ)` of a model of `X₁(N)_alg` -/

/-- `X(ℂ)`: the complex points of a `ℚ`-scheme. -/
abbrev CPt (X : Over SpecQ) : Type := ptObj (K := ℚ) ℂ ⟶ X

/-- Diamond–Shurman's `X₁(N)_alg` with chosen generators `j_X, t_X` of `K(X)` (the body of
`AfTateOr.IsX1AlgDS` with the generators named): `K(X) = ℚ(j_X, t_X)` and the integer relations of
`(j_X, t_X)` are those of `(j(τ), f₁(τ))` on `ℍ`. -/
def IsX1Gen (N : ℕ) (X : Over SpecQ) [IsIntegral X.left] (jX tX : X.left.functionField) : Prop :=
  Subfield.closure {jX, tX} = ⊤ ∧
    ∀ F : Polynomial (Polynomial ℤ), AfTateOr.ev2 F jX tX = 0 ↔
      ∀ τ : UpperHalfPlane, (T5Glue.pp τ).g₂ ≠ 0 → (T5Glue.pp τ).g₃ ≠ 0 →
        X1Igusa.Weber.evAn N (AfTateOr.toQ F) τ = 0

/-- The rational function `g ∈ K(X)` is regular at the complex point `x` with value `c`: it is the
germ of a section `s` over an open `U` containing (the image of) `x`, and `s(x) = c`. -/
def RegAt {X : Over SpecQ} [IsIntegral X.left] (x : CPt X) (g : X.left.functionField) (c : ℂ) :
    Prop :=
  ∃ (U : X.left.Opens) (_ : Nonempty U) (s : Γ(X.left, U)) (h : ⊤ ≤ x.left ⁻¹ᵁ U),
    X.left.germToFunctionField U s = g ∧
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (x.left.appLE U ⊤ h s) = c

/-- **`x = x_τ`, the point of `X(ℂ)` at `τ ∈ ℍ`** (Diamond–Shurman §7.5–7.7: `X₁(N)(ℂ) ⊇ Γ₁(N)\ℍ`
through `ℂ(X₁(N)) = ℂ(j, f₁)`). Every `g = P(j_X, t_X)/Q(j_X, t_X) ∈ K(X)` whose meromorphic function
`P(j, f₁)/Q(j, f₁)` on `ℍ` has a limit `c` at `τ` is regular at `x` with value `c`. (Limits over the
punctured neighbourhood avoid the values of `T5Glue.weber` off Weber's generic branch. For every
`τ` exactly one complex point satisfies this: the uniformization `ℍ → X(ℂ)` is holomorphic and
non-constant, and the rational functions regular at a point determine it.) -/
def AtTau (N : ℕ) {X : Over SpecQ} [IsIntegral X.left] (jX tX : X.left.functionField) (x : CPt X)
    (τ : UpperHalfPlane) : Prop :=
  ∀ (P Q : Polynomial (Polynomial ℤ)) (c : ℂ), AfTateOr.ev2 Q jX tX ≠ 0 →
    Filter.Tendsto (fun τ' => X1Igusa.Weber.evAn N (AfTateOr.toQ P) τ' /
        X1Igusa.Weber.evAn N (AfTateOr.toQ Q) τ') (nhdsWithin τ {τ}ᶜ) (nhds c) →
      RegAt x (AfTateOr.ev2 P jX tX / AfTateOr.ev2 Q jX tX) c

/-! ## 2. Hecke operators on `J₁(N)` (Diamond–Shurman §6.3, §7.9) -/

/-- `τ ↦ (τ + j)/p`. -/
def shiftDiv (p j : ℕ) (τ : UpperHalfPlane) : UpperHalfPlane :=
  if hp : 0 < p then
    ⟨((τ : ℂ) + j) / p, by
      have h := τ.coe_im_pos
      rw [Complex.div_natCast_im, Complex.add_im, Complex.natCast_im, add_zero]
      exact div_pos h (by exact_mod_cast hp)⟩
  else τ

/-- `τ ↦ pτ`. -/
def mulNat (p : ℕ) (τ : UpperHalfPlane) : UpperHalfPlane :=
  if hp : 0 < p then
    ⟨(p : ℂ) * τ, by
      have h := τ.coe_im_pos
      simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
      exact mul_pos (by exact_mod_cast hp) h⟩
  else τ

variable {X : Over SpecQ} [IsIntegral X.left] {J : AbVar ℚ}

/-- The image `aj(x) ∈ J(ℂ)` of a complex point under the Abel–Jacobi map. -/
abbrev ajC (aj : X ⟶ J.X) (x : CPt X) : J.Pt ℂ := x ≫ aj

/-- An endomorphism acting on `J(ℂ)`. -/
abbrev endC (t : AbVar.End J) (y : J.Pt ℂ) : J.Pt ℂ := y ≫ t.hom

/-- **`t` is the Hecke operator `T_p` on `J₁(N) = Pic⁰(X₁(N))`** (Diamond–Shurman §6.3, with the coset
representatives of Prop. 5.2.1): on divisor classes of degree `0` supported on the points `x_τ`,
`T_p[x_τ] = Σ_{j<p} [x_{(τ+j)/p}] + [x_{γ(pτ)}]`, the last term only for `p ∤ N`, with
`γ = (a b; c d) ∈ SL₂(ℤ)`, `N ∣ c`, `d ≡ p (mod N)`. Classes `[x_τ] − [x_{τ'}]` are written
`aj(x_τ)/aj(x_{τ'})` in `J(ℂ)` (Abel–Jacobi). -/
def IsHeckeT (N : ℕ) (jX tX : X.left.functionField) (aj : X ⟶ J.X) (p : ℕ) (t : AbVar.End J) :
    Prop :=
  ∀ (τ τ' : UpperHalfPlane) (x x' : CPt X) (y y' : Fin p → CPt X),
    AtTau N jX tX x τ → AtTau N jX tX x' τ' →
    (∀ i : Fin p, AtTau N jX tX (y i) (shiftDiv p i τ)) →
    (∀ i : Fin p, AtTau N jX tX (y' i) (shiftDiv p i τ')) →
    (p ∣ N → endC t (ajC aj x / ajC aj x') = ∏ i, ajC aj (y i) / ajC aj (y' i)) ∧
    (¬ p ∣ N → ∀ g : SL(2, ℤ), (N : ℤ) ∣ g 1 0 → ((g 1 1 : ℤ) : ZMod N) = (p : ZMod N) →
      ∀ z z' : CPt X, AtTau N jX tX z (g • mulNat p τ) → AtTau N jX tX z' (g • mulNat p τ') →
        endC t (ajC aj x / ajC aj x') = (∏ i, ajC aj (y i) / ajC aj (y' i)) * (ajC aj z / ajC aj z'))

/-- **`δ` is the diamond operator `⟨d⟩` on `J₁(N)`** (Diamond–Shurman §6.3): `⟨d⟩[x_τ] = [x_{γτ}]` for
`γ = (a b; c d') ∈ SL₂(ℤ)` with `N ∣ c`, `d' ≡ d (mod N)`. -/
def IsDiamond (N : ℕ) (jX tX : X.left.functionField) (aj : X ⟶ J.X) (d : (ZMod N)ˣ)
    (δ : AbVar.End J) : Prop :=
  ∀ g : SL(2, ℤ), (N : ℤ) ∣ g 1 0 → ((g 1 1 : ℤ) : ZMod N) = (d : ZMod N) →
    ∀ (τ τ' : UpperHalfPlane) (x x' z z' : CPt X),
      AtTau N jX tX x τ → AtTau N jX tX x' τ' → AtTau N jX tX z (g • τ) → AtTau N jX tX z' (g • τ') →
        endC δ (ajC aj x / ajC aj x') = ajC aj z / ajC aj z'

/-! ## 3. The Hecke algebra, `I_f` and `A_f = J₁(N)/I_f J₁(N)` (Diamond–Shurman §6.6) -/

/-- Generators `T_p` (`p` prime) and `⟨d⟩` (`d ∈ (ℤ/N)^×`) of `𝕋_ℤ`. -/
abbrev HeckeGen (N : ℕ) : Type := Nat.Primes ⊕ (ZMod N)ˣ

/-- The free algebra on the generators; `𝕋_ℤ` is its image in `End(J₁(N))`. -/
abbrev HeckeFree (N : ℕ) : Type := FreeAlgebra ℤ (HeckeGen N)

/-- Eigenvalues of `f`: `T_p ↦ a_p(f)`, `⟨d⟩ ↦ χ(d)`. Its kernel maps onto `I_f = {T ∈ 𝕋_ℤ : Tf = 0}`. -/
def evF {N : ℕ} (χ : DirichletCharacter ℂ N) (f : CF N 2) : HeckeFree N →ₐ[ℤ] ℂ :=
  FreeAlgebra.lift ℤ (Sum.elim (fun p => coeff f (p : ℕ)) (fun d => χ (d : ZMod N)))

/-- The action on `J` through given `T_p`, `⟨d⟩`. -/
def heckeJ {N : ℕ} (tp : Nat.Primes → AbVar.End J) (δ : (ZMod N)ˣ → AbVar.End J) :
    HeckeFree N →ₐ[ℤ] AbVar.End J :=
  FreeAlgebra.lift ℤ (Sum.elim tp δ)

/-- `φ : J → B` kills `I_f J`. -/
def KillsIf {N : ℕ} (χ : DirichletCharacter ℂ N) (f : CF N 2) (tp : Nat.Primes → AbVar.End J)
    (δ : (ZMod N)ˣ → AbVar.End J) {B : AbVar ℚ} (φ : AbVar.Hom J B) : Prop :=
  ∀ h : HeckeFree N, evF χ f h = 0 → (heckeJ tp δ h).hom ≫ φ.hom = (0 : AbVar.Hom J B).hom

/-- **`π : J → A` is `J ↠ J/I_f J = A_f`** (Diamond–Shurman Def. 6.6.3): surjective, kills `I_f J`,
and universal among homomorphisms to abelian varieties that kill `I_f J`. -/
def IsAfQuotient {N : ℕ} (χ : DirichletCharacter ℂ N) (f : CF N 2) (tp : Nat.Primes → AbVar.End J)
    (δ : (ZMod N)ˣ → AbVar.End J) (A : AbVar ℚ) (π : AbVar.Hom J A) : Prop :=
  AlgebraicGeometry.Surjective π.hom.left ∧ KillsIf χ f tp δ π ∧
    ∀ (B : AbVar ℚ) (φ : AbVar.Hom J B), KillsIf χ f tp δ φ →
      ∃! ψ : AbVar.Hom A B, π.hom ≫ ψ.hom = φ.hom

/-- **`θ` is Diamond–Shurman's action of `K_f = (𝕋_ℤ/I_f) ⊗ ℚ` on `A_f`** (Prop. 6.6.4): `θ(a_p(f))` is
the endomorphism of `A_f` induced by `T_p`, and `θ(χ(d))` the one induced by `⟨d⟩`. -/
def IsAfAction {N : ℕ} (χ : DirichletCharacter ℂ N) (f : CF N 2) (tp : Nat.Primes → AbVar.End J)
    (δ : (ZMod N)ˣ → AbVar.End J) {A : AbVar ℚ} (π : AbVar.Hom J A)
    (θ : coeffField f →+* A.End0) : Prop :=
  (∀ p : Nat.Primes, ∃ e : AbVar.End A, (tp p).hom ≫ π.hom = π.hom ≫ e.hom ∧
      θ ⟨coeff f (p : ℕ), coeff_mem_coeffField f p⟩ = (1 : ℚ) ⊗ₜ e) ∧
  (∀ d : (ZMod N)ˣ, ∃ (c : coeffField f) (e : AbVar.End A), (c : ℂ) = χ (d : ZMod N) ∧
      (δ d).hom ≫ π.hom = π.hom ≫ e.hom ∧ θ c = (1 : ℚ) ⊗ₜ e)

/-! ## 4. `K_{f,λ}`, `V_λ = K_λ ⊗_{ℚ_ℓ ⊗ K_f} V_ℓ(A)` and `ρ_{f,λ}` (Diamond–Shurman §9.5) -/

section Lambda

open IsDedekindDomain NumberField

/-- `ℓ` as an element of `Nat.Primes`. -/
def primeL (ℓ : ℕ) [Fact ℓ.Prime] : Nat.Primes := ⟨ℓ, Fact.out⟩

/-- The `ℓ`-adic place of `ℚ`. -/
def vQ (ℓ : ℕ) [Fact ℓ.Prime] : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm (primeL ℓ)

variable {K : Type} [Field K] [NumberField K]

/-- `ℚ_ℓ → K_λ` for a place `λ ∣ ℓ` (Mathlib's `ℚ_ℓ ≅ ℚ_{v_ℓ}`, then Tau Ceti's completion map). -/
def algQl (ℓ : ℕ) [Fact ℓ.Prime] (lam : HeightOneSpectrum (𝓞 K))
    [lam.asIdeal.LiesOver (vQ ℓ).asIdeal] : ℚ_[ℓ] →+* lam.adicCompletion K :=
  ((vQ ℓ).adicCompletionExtension ℚ K lam).comp
    (RingHomClass.toRingHom (Padic.adicCompletionEquiv (𝓞 ℚ) (primeL ℓ)))

/-- `ℚ_ℓ ⊗_ℚ K → K_λ`, `x ⊗ a ↦ x · a`. -/
def rhoLam (ℓ : ℕ) [Fact ℓ.Prime] (lam : HeightOneSpectrum (𝓞 K))
    [lam.asIdeal.LiesOver (vQ ℓ).asIdeal] : ℚ_[ℓ] ⊗[ℚ] K →+* lam.adicCompletion K :=
  letI : Algebra ℚ_[ℓ] (lam.adicCompletion K) := (algQl ℓ lam).toAlgebra
  R16Used.liftHom (algebraMap K (lam.adicCompletion K))

/-- `σ ∈ G_ℚ` on `V_ℓ(A)`, linear over `ℚ_ℓ ⊗ F` (endomorphisms are defined over `ℚ`). -/
def galR (ℓ : ℕ) [Fact ℓ.Prime] (A : AbVar ℚ) {F : Type} [Field F] [Algebra ℚ F]
    (θ : F →+* A.End0) (σ : GQ) :
    letI := R16Used.tensorModule ℓ A θ; A.V ℓ →ₗ[ℚ_[ℓ] ⊗[ℚ] F] A.V ℓ :=
  letI := R16Used.tensorModule ℓ A θ
  { toFun := A.galRep ℓ σ
    map_add' := map_add _
    map_smul' := fun r v => R16Used.galRep_tsmul ℓ A θ σ r v }

/-- **`ρ_{f,λ}(σ)`**: `σ` acting on `V_λ = K_λ ⊗_{ℚ_ℓ ⊗ K} V_ℓ(A)`. -/
def frobLam (ℓ : ℕ) [Fact ℓ.Prime] (A : AbVar ℚ) (θ : K →+* A.End0) (lam : HeightOneSpectrum (𝓞 K))
    [lam.asIdeal.LiesOver (vQ ℓ).asIdeal] (σ : GQ) :
    letI := R16Used.tensorModule ℓ A θ
    letI := (rhoLam ℓ lam).toAlgebra
    (lam.adicCompletion K ⊗[ℚ_[ℓ] ⊗[ℚ] K] A.V ℓ) →ₗ[lam.adicCompletion K]
      (lam.adicCompletion K ⊗[ℚ_[ℓ] ⊗[ℚ] K] A.V ℓ) :=
  letI := R16Used.tensorModule ℓ A θ
  letI := (rhoLam ℓ lam).toAlgebra
  (galR ℓ A θ σ).baseChange _

end Lambda

/-! ## 5. The three leaves -/

section Leaves

open IsDedekindDomain NumberField

/-- **LEAF L1 (Hecke operators on `J₁(N)` over `ℚ`).** For DS's `X₁(N)_alg` (`IsX1Gen`: function field
`ℚ(j, f₁)`) with a rational point and its Jacobian `J = J₁(N)` (Albanese property, Abel–Jacobi map `aj`),
the Hecke operators `T_p` (every prime `p`) and the diamond operators `⟨d⟩` exist as endomorphisms of
`J` over `ℚ`, acting on degree-0 divisor classes of points `x_τ` by Diamond–Shurman's double-coset
formulas (`IsHeckeT`, `IsDiamond`). Diamond–Shurman, *A First Course in Modular Forms*, GTM 228 (2005),
§6.3 (`T_p` and `⟨d⟩` on `Div⁰`, `Pic⁰` and `Jac(X₁(N))`) and §7.9 (they are defined over `ℚ`); Shimura
1971 §7.2 (modular correspondences on the Jacobian, rational over `ℚ`); locators UNVERIFIED.

Dictionary audit (hecke-pin, `ZInQKernel/Contrib/OneProof/HeckePin.lean`): `IsHeckeT`/`IsDiamond` pin the
operators: `AfTateLam.HeckePin.isHeckeT_unique`, `isDiamond_unique` (two endomorphisms with DS's action on
the classes of the `x_τ` agree; inputs `X1TauPoints`, the glue `ConstOnTauPoints`). -/
def HeckeJ1DS : Prop :=
  ∀ (N : ℕ), 2 ≤ N → ∀ (X : Over SpecQ) [IsIntegral X.left] (jX tX : X.left.functionField),
    IsCurve X → IsX1Gen N X jX tX →
    ∀ (P₀ : RatPt X) (J : AbVar ℚ) (aj : X ⟶ J.X), IsJacobian X P₀ J aj →
      ∃ (tp : Nat.Primes → AbVar.End J) (δ : (ZMod N)ˣ → AbVar.End J),
        (∀ p : Nat.Primes, IsHeckeT N jX tX aj (p : ℕ) (tp p)) ∧
        (∀ d : (ZMod N)ˣ, IsDiamond N jX tX aj d (δ d))

/-- **L2 (Shimura's `A_f` over `ℚ`), proved: `AfTateLam.afShimura_proof` (`AfShimuraProof.lean`).**
The statement below has no dimension or uniqueness clause: it carries only quotient existence, the coefficient recurrence and finiteness of `K_f`, so it is weaker than Shimura 1973 Thm 1, and its proof is not a Lean proof of that theorem. It was a leaf before the m1-afshimura fold.
For a newform `f ∈ S₂(Γ₁(N))` with nebentypus `χ`, `K_f` is
a number field, and the quotient `A_f = J₁(N)/I_f J₁(N)` exists as an abelian variety over `ℚ` with the
action `θ : K_f → End⁰(A_f)` induced by the Hecke algebra (`θ(a_p) = T_p|A_f`, `θ(χ(d)) = ⟨d⟩|A_f`).
Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc. Japan 25
(1973), Thm 1 (pp. 526–527; read by the locator audit, row R16: the `ℚ`-rational quotient, the
coefficient-field action and `dim A_f = [K_f : ℚ]`); Diamond–Shurman Def. 6.6.3, Prop. 6.6.4 (over `ℂ`).
The Hecke operators are any with DS's double-coset action (by L1 they exist; they are unique since an
endomorphism of `J` is determined by its action on `J(ℂ)`).

Dictionary audit (hecke-pin, `ZInQKernel/Contrib/OneProof/HeckePin.lean`): `KillsIf` kills exactly DS's
`I_f J` (`AfTateLam.HeckePin.killsIf_iff_IfDS_of_leaves`, from `ker(heckeJ) ⊆ ker(evF)`,
`evF_eq_zero_of_heckeJ_eq_zero_of_leaves`; inputs `X1TauPoints`, `AbelJacobiX1`); `A_f` is unique up to
unique isomorphism compatible with `π` (`isAfQuotient_unique`, `induced_comm`); `θ` is unique
(`theta_unique`, via `a_n ∈ ℚ(a_p, χ(d))`, `coeff_mem_genField`); `T_p`, `⟨d⟩` are pinned
(`isHeckeT_unique`, `isDiamond_unique`). -/
def AfShimura : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 2 ≤ N → IsNewform f χ →
    ∀ (X : Over SpecQ) [IsIntegral X.left] (jX tX : X.left.functionField),
    IsCurve X → IsX1Gen N X jX tX →
    ∀ (P₀ : RatPt X) (J : AbVar ℚ) (aj : X ⟶ J.X), IsJacobian X P₀ J aj →
    ∀ (tp : Nat.Primes → AbVar.End J) (δ : (ZMod N)ˣ → AbVar.End J),
      (∀ p : Nat.Primes, IsHeckeT N jX tX aj (p : ℕ) (tp p)) →
      (∀ d : (ZMod N)ˣ, IsDiamond N jX tX aj d (δ d)) →
      FiniteDimensional ℚ (coeffField f) ∧
        ∃ (A : AbVar ℚ) (π : AbVar.Hom J A) (θ : coeffField f →+* A.End0),
          IsAfQuotient χ f tp δ A π ∧ IsAfAction χ f tp δ π θ

/-- **LEAF L3 (Diamond–Shurman Thm 9.5.4, over `K_{f,λ}`).** For every `(A, π, θ)` that is DS's
`(A_f, J₁(N) ↠ A_f, K_f-action)` (L2's characterization), every prime `ℓ` and every place `λ ∣ ℓ` of
`K_f`: `σ ∈ G_ℚ` acts on `V_λ(A_f) = K_{f,λ} ⊗_{ℚ_ℓ ⊗ K_f} V_ℓ(A_f)` (`frobLam`, the representation
`ρ_{f,λ}`), and for `p ∤ Nℓ` every arithmetic Frobenius at `p` has characteristic polynomial
`X² − a_p(f) X + χ(p) p` over `K_{f,λ}`. Diamond–Shurman GTM 228, Lemma 9.5.3 (`V_ℓ(A_f)` free of rank 2
over `K_f ⊗ ℚ_ℓ`, which defines `ρ_{f,λ}`) and Thm 9.5.4; Shimura 1971 Thm 7.14 / Ribet 1977 for the
characteristic-polynomial form; numbers UNVERIFIED. `K_f` a number field is the print's presupposition
(instance argument); finiteness of `V_λ` likewise. -/
def AfTateDSLambda : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 2 ≤ N → IsNewform f χ →
    ∀ (X : Over SpecQ) [IsIntegral X.left] (jX tX : X.left.functionField),
    IsCurve X → IsX1Gen N X jX tX →
    ∀ (P₀ : RatPt X) (J : AbVar ℚ) (aj : X ⟶ J.X), IsJacobian X P₀ J aj →
    ∀ (tp : Nat.Primes → AbVar.End J) (δ : (ZMod N)ˣ → AbVar.End J),
      (∀ p : Nat.Primes, IsHeckeT N jX tX aj (p : ℕ) (tp p)) →
      (∀ d : (ZMod N)ˣ, IsDiamond N jX tX aj d (δ d)) →
    ∀ (A : AbVar ℚ) (π : AbVar.Hom J A) (θ : coeffField f →+* A.End0),
      IsAfQuotient χ f tp δ A π → IsAfAction χ f tp δ π θ →
    ∀ [NumberField (coeffField f)] (ℓ : ℕ) [Fact ℓ.Prime]
      (lam : HeightOneSpectrum (𝓞 (coeffField f))) [lam.asIdeal.LiesOver (vQ ℓ).asIdeal],
      letI := R16Used.tensorModule ℓ A θ
      letI := (rhoLam ℓ lam).toAlgebra
      letI : Module.Free (lam.adicCompletion (coeffField f))
          (lam.adicCompletion (coeffField f) ⊗[ℚ_[ℓ] ⊗[ℚ] coeffField f] A.V ℓ) :=
        Module.Free.of_divisionRing (lam.adicCompletion (coeffField f))
          (lam.adicCompletion (coeffField f) ⊗[ℚ_[ℓ] ⊗[ℚ] coeffField f] A.V ℓ)
      ∀ [Module.Finite (lam.adicCompletion (coeffField f))
          (lam.adicCompletion (coeffField f) ⊗[ℚ_[ℓ] ⊗[ℚ] coeffField f] A.V ℓ)],
      ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
        ∃ c : coeffField f, (c : ℂ) = χ (p : ZMod N) ∧
          LinearMap.charpoly (frobLam ℓ A θ lam σ) =
            ((Polynomial.X : Polynomial (lam.adicCompletion (coeffField f))) ^ 2 -
              Polynomial.C (algebraMap (coeffField f) (lam.adicCompletion (coeffField f))
                ⟨coeff f p, coeff_mem_coeffField f p⟩) * Polynomial.X +
              Polynomial.C (algebraMap (coeffField f) (lam.adicCompletion (coeffField f))
                (c * (p : coeffField f))) : Polynomial (lam.adicCompletion (coeffField f)))

end Leaves

/-! ## 6. Glue: from `K_{f,λ}` to the `ι`-components -/

section Component

open IsDedekindDomain NumberField

variable {ℓ : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [NumberField K]

theorem liesOver_place (τ : K →+* PadicAlgCl ℓ) : (place τ).asIdeal.LiesOver (vQ ℓ).asIdeal := by
  have hmem : ((ℓ : ℕ) : 𝓞 ℚ) ∈ (place τ).asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 K)) := by
    rw [Ideal.mem_comap, map_natCast]; exact natCast_mem_placeIdeal τ
  let w : HeightOneSpectrum (𝓞 ℚ) :=
    { asIdeal := (place τ).asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 K))
      isPrime := Ideal.comap_isPrime _ _
      ne_bot := by
        intro h
        rw [h, Ideal.mem_bot] at hmem
        exact (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero) hmem }
  have hw : Rat.HeightOneSpectrum.primesEquiv w = primeL ℓ := by
    have hdvd : Rat.HeightOneSpectrum.natGenerator w ∣ ℓ := by
      rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
      have := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hmem
      rwa [map_natCast] at this
    apply Subtype.ext
    exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w)
      (Fact.out : ℓ.Prime)).1 hdvd
  have hv : vQ ℓ = w := (Equiv.symm_apply_eq _).2 hw.symm
  exact ⟨by rw [hv]⟩

theorem continuous_algQl (lam : HeightOneSpectrum (𝓞 K)) [lam.asIdeal.LiesOver (vQ ℓ).asIdeal] :
    Continuous (algQl ℓ lam) :=
  ((vQ ℓ).continuous_adicCompletionExtension ℚ K lam).comp
    (map_continuous (Padic.adicCompletionEquiv (𝓞 ℚ) (primeL ℓ)))

theorem τhat_algQl (τ : K →+* PadicAlgCl ℓ) [(place τ).asIdeal.LiesOver (vQ ℓ).asIdeal] (x : ℚ_[ℓ]) :
    τhat τ (algQl ℓ (place τ) x) = algebraMap ℚ_[ℓ] (PadicAlgCl ℓ) x := by
  have hc1 : Continuous fun x => τhat τ (algQl ℓ (place τ) x) :=
    (continuous_τhat τ).comp (continuous_algQl (place τ))
  have hc2 : Continuous (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)) := continuous_algebraMap ℚ_[ℓ] _
  have hq : (fun x => τhat τ (algQl ℓ (place τ) x)) ∘ (Rat.cast : ℚ → ℚ_[ℓ]) =
      (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)) ∘ (Rat.cast : ℚ → ℚ_[ℓ]) := by
    funext q; simp only [Function.comp_apply, map_ratCast]
  exact congrFun ((Padic.denseRange_ratCast ℓ).equalizer hc1 hc2 hq) x

variable (A : AbVar ℚ) (θ : K →+* A.End0)

theorem isScalarTower_tensor :
    letI := R16Used.tensorModule ℓ A θ; IsScalarTower ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K) (A.V ℓ) := by
  letI := R16Used.tensorModule ℓ A θ
  refine IsScalarTower.of_algebraMap_smul fun x v => ?_
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  exact R16Used.tsmul_left (R16Split.rhoV ℓ A θ) x v

theorem mem_eigenFun_iff_semilin (emb : K →+* PadicAlgCl ℓ) (φ : A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ) :
    letI := R16Used.tensorModule ℓ A θ
    φ ∈ eigenFun ℓ A θ emb ↔ ∀ (r : ℚ_[ℓ] ⊗[ℚ] K) (v : A.V ℓ), φ (r • v) = R16Used.liftHom emb r * φ v := by
  letI := R16Used.tensorModule ℓ A θ
  constructor
  · intro h r v
    exact R16Used.semilin (R16Split.rhoV ℓ A θ) emb (eigenFun ℓ A θ emb)
      (fun φ => R16Used.mem_eigenFun_iff ℓ A θ emb φ) h r v
  · intro h
    rw [R16Used.mem_eigenFun_iff]
    intro a
    apply LinearMap.ext
    intro v
    have h1 := h ((1 : ℚ_[ℓ]) ⊗ₜ a) v
    rw [R16Used.tsmul_right, R16Used.liftHom_one_tmul] at h1
    simpa using h1

theorem rhoLam_tmul (lam : HeightOneSpectrum (𝓞 K)) [lam.asIdeal.LiesOver (vQ ℓ).asIdeal]
    (x : ℚ_[ℓ]) (a : K) :
    rhoLam ℓ lam (x ⊗ₜ a) = algQl ℓ lam x * algebraMap K (lam.adicCompletion K) a := by
  letI : Algebra ℚ_[ℓ] (lam.adicCompletion K) := (algQl ℓ lam).toAlgebra
  exact R16Used.liftHom_tmul _ x a

theorem τhat_rhoLam (emb : K →+* PadicAlgCl ℓ) [(place emb).asIdeal.LiesOver (vQ ℓ).asIdeal]
    (r : ℚ_[ℓ] ⊗[ℚ] K) : τhat emb (rhoLam ℓ (place emb) r) = R16Used.liftHom emb r := by
  induction r using TensorProduct.inductionOn with
  | tmul x a =>
    rw [rhoLam_tmul, R16Used.liftHom_tmul, map_mul, τhat_algQl, τhat_algebraMap]
  | add r s hr hs => rw [map_add, map_add, hr, hs, map_add]

/-- **The `ι`-component from `ρ_{f,λ}` (glue, proved).** For `ι : K → ℚ̄_ℓ` with place `λ = λ_ι`, the
`ι`-eigenfunctionals have the dimension of `V_λ`, and `σ` acts on them with trace and determinant
`ι̂(tr ρ_λ(σ))`, `ι̂(det ρ_λ(σ))`. -/
theorem component (emb : K →+* PadicAlgCl ℓ) [FiniteDimensional ℚ_[ℓ] (A.V ℓ)] (σ : GQ) :
    letI := R16Used.tensorModule ℓ A θ
    haveI := liesOver_place emb
    letI := (rhoLam ℓ (place emb)).toAlgebra
    Module.Finite ((place emb).adicCompletion K)
        ((place emb).adicCompletion K ⊗[ℚ_[ℓ] ⊗[ℚ] K] A.V ℓ) ∧
      Module.finrank (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) =
        Module.finrank ((place emb).adicCompletion K)
          ((place emb).adicCompletion K ⊗[ℚ_[ℓ] ⊗[ℚ] K] A.V ℓ) ∧
      LinearMap.trace (PadicAlgCl ℓ) _ (frobOn ℓ A θ emb σ) =
        τhat emb (LinearMap.trace _ _ (frobLam ℓ A θ (place emb) σ)) ∧
      LinearMap.det (frobOn ℓ A θ emb σ) = τhat emb (LinearMap.det (frobLam ℓ A θ (place emb) σ)) := by
  letI := R16Used.tensorModule ℓ A θ
  haveI := liesOver_place emb
  letI := (rhoLam ℓ (place emb)).toAlgebra
  haveI := isScalarTower_tensor (ℓ := ℓ) A θ
  haveI : Module.Finite (ℚ_[ℓ] ⊗[ℚ] K) (A.V ℓ) :=
    Module.Finite.of_restrictScalars_finite ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K) (A.V ℓ)
  haveI : Module.Finite ((place emb).adicCompletion K)
      ((place emb).adicCompletion K ⊗[ℚ_[ℓ] ⊗[ℚ] K] A.V ℓ) := inferInstance
  have hik : ∀ x : ℚ_[ℓ], R16Used.liftHom emb (algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K) x) =
      algebraMap ℚ_[ℓ] (PadicAlgCl ℓ) x := by
    intro x
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      R16Used.liftHom_tmul_one]
  have heps : ∀ r, τhat emb (algebraMap (ℚ_[ℓ] ⊗[ℚ] K) ((place emb).adicCompletion K) r) =
      R16Used.liftHom emb r := fun r => τhat_rhoLam emb r
  have hE := mem_eigenFun_iff_semilin A θ emb
  refine ⟨inferInstance, finrank_E (R16Used.liftHom emb) (τhat emb) (eigenFun ℓ A θ emb) hik heps hE, ?_⟩
  exact trace_det_precomp (R16Used.liftHom emb) (τhat emb) (eigenFun ℓ A θ emb) hik heps hE
    (galR ℓ A θ σ) (frobOn ℓ A θ emb σ) (fun φ => rfl)

end Component

/-- Trace, determinant and dimension from a quadratic characteristic polynomial. -/
theorem lin_trace_det {F M : Type*} [Field F] [AddCommGroup M] [Module F M] [FiniteDimensional F M]
    (g : M →ₗ[F] M) (t d : F)
    (h : g.charpoly = Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C d) :
    Module.finrank F M = 2 ∧ LinearMap.trace F M g = t ∧ LinearMap.det g = d := by
  have hn : Module.finrank F M = 2 := by
    rw [← LinearMap.charpoly_natDegree g, h]
    compute_degree!
  let b := Module.finBasis F M
  have hM : (LinearMap.toMatrix b b g).charpoly =
      Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C d := by
    rw [LinearMap.charpoly_toMatrix, h]
  haveI : Nonempty (Fin (Module.finrank F M)) := ⟨⟨0, by omega⟩⟩
  refine ⟨hn, ?_, ?_⟩
  · rw [LinearMap.trace_eq_matrix_trace F b, Matrix.trace_eq_neg_charpoly_coeff, hM,
      Fintype.card_fin, hn]
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X]
  · rw [← LinearMap.det_toMatrix b, Matrix.det_eq_sign_charpoly_coeff, hM, Fintype.card_fin, hn]
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X]

/-! ## 7. The discharge of `r16CoreY` -/

section Discharge

open IsDedekindDomain NumberField

/-- A Frobenius element at some prime not dividing `S ≠ 0` (Chebotarev, T18, proved). -/
theorem exists_frob (S : ℕ) (hS : S ≠ 0) : ∃ (p : ℕ) (σ : GQ), p.Prime ∧ ¬ p ∣ S ∧ IsFrobAt σ p := by
  obtain ⟨p, hp, hpS, v, τ, hv, hτ, -⟩ :=
    ZInQ.Contrib.frobeniusDense ⊤ isOpen_univ 1 S.primeFactors
  refine ⟨p, τ, hp, fun h => hpS (Nat.mem_primeFactors.2 ⟨hp, h, hS⟩), ?_⟩
  exact isFrobAt_of_isArithFrob τ v p hp hv hτ

theorem finiteDimensional_V (hT : TateModuleFree) (A : AbVar ℚ) (ℓ : ℕ) [Fact ℓ.Prime] :
    FiniteDimensional ℚ_[ℓ] (A.V ℓ) := by
  obtain ⟨hfree, hfinT, -⟩ := hT ℚ A ℓ (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero)
  exact Module.Finite.base_change ℤ_[ℓ] ℚ_[ℓ] (A.T ℓ)

/-- **`r16CoreY` from the three printed leaves, Igusa and Mumford (glue, proved).** -/
theorem r16CoreY_of_printed (h1 : HeckeJ1DS) (h2 : AfShimura) (h3 : AfTateDSLambda)
    (hI : X1Igusa.IgusaGL2DS) (hM : AvSplit.MumfordTorsionAlgClosed) : R16Split.R16CoreY := by
  have hT : TateModuleFree := T5Torsion.TateFree.tateModuleFree_of_torsionStructure
    (AvSplit.torsionStructure_of_mumford hM)
  intro N χ f J hN hf hJ
  rcases Nat.lt_or_ge N 2 with hN1 | hN2
  · have h1 : N = 1 := by omega
    subst h1
    exact absurd hf (AfTateOr.not_isNewform_one χ f)
  obtain ⟨X, P₀, aj, hX, hJac⟩ := hJ
  obtain ⟨hC, hInt, jX, tX, hgen, hrel⟩ :=
    AfTateOr.isX1AlgDS_of_isX1Model (X1Igusa.x1PointsConjugate_of_igusaGL2DS hI) hN2 hX
  have hG : IsX1Gen N X jX tX := ⟨hgen, hrel⟩
  obtain ⟨tp, δ, htp, hδ⟩ := h1 N hN2 X jX tX hC hG P₀ J aj hJac
  obtain ⟨hfin, A, π, θ, hQ, hAct⟩ := h2 N χ f hN2 hf X jX tX hC hG P₀ J aj hJac tp δ htp hδ
  haveI : NumberField (coeffField f) := @NumberField.mk _ _ inferInstance hfin
  have hL := h3 N χ f hN2 hf X jX tX hC hG P₀ J aj hJac tp δ htp hδ A π θ hQ hAct
  have key : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (emb : coeffField f →+* PadicAlgCl ℓ),
      Module.finrank (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) = 2 ∧
        ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
          (∀ a : coeffField f, (a : ℂ) = coeff f p →
              LinearMap.trace (PadicAlgCl ℓ) _ (frobOn ℓ A θ emb σ) = emb a) ∧
          (∀ c : coeffField f, (c : ℂ) = χ (p : ZMod N) →
              LinearMap.det (frobOn ℓ A θ emb σ) = emb c * p) := by
    intro ℓ _ emb
    haveI := finiteDimensional_V hT A ℓ
    letI := R16Used.tensorModule ℓ A θ
    haveI := liesOver_place emb
    letI := (rhoLam ℓ (place emb)).toAlgebra
    have hfrob : ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
        Module.finrank (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) = 2 ∧
        (∀ a : coeffField f, (a : ℂ) = coeff f p →
            LinearMap.trace (PadicAlgCl ℓ) _ (frobOn ℓ A θ emb σ) = emb a) ∧
        (∀ c : coeffField f, (c : ℂ) = χ (p : ZMod N) →
            LinearMap.det (frobOn ℓ A θ emb σ) = emb c * p) := by
      intro p hp hpN σ hσ
      obtain ⟨hfinL, hrk, htr, hdet⟩ := component A θ emb σ
      obtain ⟨c, hc, hcp⟩ := @hL ℓ _ (place emb) _ hfinL p hp hpN σ hσ
      obtain ⟨h2, htr', hdet'⟩ := lin_trace_det _ _ _ hcp
      refine ⟨hrk.trans h2, fun a ha => ?_, fun c' hc' => ?_⟩
      · have : a = ⟨coeff f p, coeff_mem_coeffField f p⟩ := Subtype.ext ha
        rw [htr, htr', this, τhat_algebraMap]
      · have : c' = c := Subtype.ext (hc'.trans hc.symm)
        rw [hdet, hdet', this, τhat_algebraMap, map_mul, map_natCast]
    obtain ⟨p, σ, hp, hpN, hσ⟩ := exists_frob (N * ℓ)
      (Nat.mul_ne_zero (by omega) (Fact.out : ℓ.Prime).ne_zero)
    exact ⟨(hfrob p hp hpN σ hσ).1, fun p hp hpN σ hσ => (hfrob p hp hpN σ hσ).2⟩
  refine ⟨hfin, A, π, θ, hQ.1, ?_, fun ℓ _ emb => (key ℓ emb).2⟩
  exact R16Split.dim_eq_of_rank_two hT A θ (fun emb => (key 2 emb).1)

end Discharge

/-! ## 8. The `ℚ_ℓ ⊗ K_f` form of Diamond–Shurman 9.5.4 implies the `K_{f,λ}` form -/

section TensorForm

open IsDedekindDomain NumberField

/-- **`ρ_{A_f,ℓ}` over `ℚ_ℓ ⊗ K_f` (Diamond–Shurman Lemma 9.5.3 + Thm 9.5.4 in the `K_f ⊗ ℚ_ℓ` form)**, universal
over `A_f` as in `AfTateDSLambda`: `V_ℓ(A_f)` has a `ℚ_ℓ ⊗ K_f`-basis in which every arithmetic Frobenius at
`p ∤ Nℓ` has characteristic polynomial `X² − a_p X + χ(p)p` (isj1-dict's `AfTateAt` body). Not a leaf of
the fold: `dsLambda_of_tensor` shows that `AfTateDSLambda` is a consequence of it, so the new leaf follows
from either form of the print. -/
def AfTateDSTensor : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 2 ≤ N → IsNewform f χ →
    ∀ (X : Over SpecQ) [IsIntegral X.left] (jX tX : X.left.functionField),
    IsCurve X → IsX1Gen N X jX tX →
    ∀ (P₀ : RatPt X) (J : AbVar ℚ) (aj : X ⟶ J.X), IsJacobian X P₀ J aj →
    ∀ (tp : Nat.Primes → AbVar.End J) (δ : (ZMod N)ˣ → AbVar.End J),
      (∀ p : Nat.Primes, IsHeckeT N jX tX aj (p : ℕ) (tp p)) →
      (∀ d : (ZMod N)ˣ, IsDiamond N jX tX aj d (δ d)) →
    ∀ (A : AbVar ℚ) (π : AbVar.Hom J A) (θ : coeffField f →+* A.End0),
      IsAfQuotient χ f tp δ A π → IsAfAction χ f tp δ π θ →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      ∃ b : (letI := R16Used.tensorModule ℓ A θ;
          Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] coeffField f) (A.V ℓ)),
        ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
          ∃ c : coeffField f, (c : ℂ) = χ (p : ZMod N) ∧
            (R16Used.frobMat ℓ A θ b σ).charpoly =
              R16Used.esPoly ℓ (⟨coeff f p, coeff_mem_coeffField f p⟩ : coeffField f)
                (c * (p : coeffField f))

variable {ℓ : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [NumberField K]

theorem rhoLam_one_tmul (lam : HeightOneSpectrum (𝓞 K)) [lam.asIdeal.LiesOver (vQ ℓ).asIdeal]
    (a : K) : rhoLam ℓ lam ((1 : ℚ_[ℓ]) ⊗ₜ a) = algebraMap K (lam.adicCompletion K) a := by
  rw [rhoLam_tmul, map_one, _root_.one_mul]

/-- **Base change of the characteristic polynomial to `K_λ` (glue, proved).** -/
theorem charpoly_frobLam_of_basis (A : AbVar ℚ) (θ : K →+* A.End0)
    (lam : HeightOneSpectrum (𝓞 K)) [lam.asIdeal.LiesOver (vQ ℓ).asIdeal]
    (b : letI := R16Used.tensorModule ℓ A θ; Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] K) (A.V ℓ))
    (σ : GQ) (a d : K) (h : (R16Used.frobMat ℓ A θ b σ).charpoly = R16Used.esPoly ℓ a d) :
    letI := R16Used.tensorModule ℓ A θ
    letI := (rhoLam ℓ lam).toAlgebra
    letI : Module.Free (lam.adicCompletion K) (lam.adicCompletion K ⊗[ℚ_[ℓ] ⊗[ℚ] K] A.V ℓ) :=
      Module.Free.of_divisionRing (lam.adicCompletion K) (lam.adicCompletion K ⊗[ℚ_[ℓ] ⊗[ℚ] K] A.V ℓ)
    ∀ [Module.Finite (lam.adicCompletion K) (lam.adicCompletion K ⊗[ℚ_[ℓ] ⊗[ℚ] K] A.V ℓ)],
    LinearMap.charpoly (frobLam ℓ A θ lam σ) =
      ((Polynomial.X : Polynomial (lam.adicCompletion K)) ^ 2 -
        Polynomial.C (algebraMap K (lam.adicCompletion K) a) * Polynomial.X +
        Polynomial.C (algebraMap K (lam.adicCompletion K) d)) := by
  letI := R16Used.tensorModule ℓ A θ
  letI := (rhoLam ℓ lam).toAlgebra
  letI : Module.Free (lam.adicCompletion K) (lam.adicCompletion K ⊗[ℚ_[ℓ] ⊗[ℚ] K] A.V ℓ) :=
    Module.Free.of_divisionRing (lam.adicCompletion K) (lam.adicCompletion K ⊗[ℚ_[ℓ] ⊗[ℚ] K] A.V ℓ)
  intro _
  have hM : R16Used.frobMat ℓ A θ b σ = LinearMap.toMatrix b b (galR ℓ A θ σ) := by
    ext i j; rw [LinearMap.toMatrix_apply]; rfl
  rw [← LinearMap.charpoly_toMatrix (frobLam ℓ A θ lam σ) (Algebra.TensorProduct.basis _ b)]
  change (LinearMap.toMatrix (Algebra.TensorProduct.basis _ b) (Algebra.TensorProduct.basis _ b)
    ((galR ℓ A θ σ).baseChange _)).charpoly = _
  rw [LinearMap.toMatrix_baseChange, ← hM, Matrix.charpoly_map, h, R16Used.esPoly]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, RingHom.algebraMap_toAlgebra, rhoLam_one_tmul]

/-- **The `K_{f,λ}` leaf is a consequence of the `ℚ_ℓ ⊗ K_f` form (glue, proved).** -/
theorem dsLambda_of_tensor (h : AfTateDSTensor) : AfTateDSLambda := by
  intro N χ f hN hf X _ jX tX hC hG P₀ J aj hJ tp δ htp hδ A π θ hQ hAct _ ℓ _ lam _ _ p hp hpN σ hσ
  obtain ⟨b, hb⟩ := h N χ f hN hf X jX tX hC hG P₀ J aj hJ tp δ htp hδ A π θ hQ hAct ℓ
  obtain ⟨c, hc, hcp⟩ := hb p hp hpN σ hσ
  exact ⟨c, hc, charpoly_frobLam_of_basis A θ lam b σ _ _ hcp⟩

end TensorForm

/-! ## 9. A fallback for the "satisfies" reading: Lemma 9.5.3 + "satisfies" + a separate determinant leaf -/

section SatisfiesForm

open IsDedekindDomain NumberField

/-- The common hypotheses of the `K_{f,λ}` statements, with the conclusion `P` at each Frobenius. -/
def AtFrobLam (P : ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (A : AbVar ℚ)
    (θ : coeffField f →+* A.End0) [NumberField (coeffField f)] (ℓ : ℕ) [Fact ℓ.Prime]
    (lam : HeightOneSpectrum (𝓞 (coeffField f))) [lam.asIdeal.LiesOver (vQ ℓ).asIdeal]
    (p : ℕ) (σ : GQ), Prop) : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 2 ≤ N → IsNewform f χ →
    ∀ (X : Over SpecQ) [IsIntegral X.left] (jX tX : X.left.functionField),
    IsCurve X → IsX1Gen N X jX tX →
    ∀ (P₀ : RatPt X) (J : AbVar ℚ) (aj : X ⟶ J.X), IsJacobian X P₀ J aj →
    ∀ (tp : Nat.Primes → AbVar.End J) (δ : (ZMod N)ˣ → AbVar.End J),
      (∀ p : Nat.Primes, IsHeckeT N jX tX aj (p : ℕ) (tp p)) →
      (∀ d : (ZMod N)ˣ, IsDiamond N jX tX aj d (δ d)) →
    ∀ (A : AbVar ℚ) (π : AbVar.Hom J A) (θ : coeffField f →+* A.End0),
      IsAfQuotient χ f tp δ A π → IsAfAction χ f tp δ π θ →
    ∀ [NumberField (coeffField f)] (ℓ : ℕ) [Fact ℓ.Prime]
      (lam : HeightOneSpectrum (𝓞 (coeffField f))) [lam.asIdeal.LiesOver (vQ ℓ).asIdeal],
      ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p → P N χ f A θ ℓ lam p σ

/-- **Fallback leaf (DS Lemma 9.5.3 + Thm 9.5.4, "satisfies" reading, over `K_{f,λ}`).** `V_λ(A_f)` has
dimension 2 over `K_{f,λ}` and every Frobenius at `p ∤ Nℓ` satisfies `X² − a_p X + χ(p)p`. Not in the fold. -/
def AfTateDSLambdaSat : Prop :=
  AtFrobLam fun N χ f A θ _ ℓ _ lam _ p σ =>
    letI := R16Used.tensorModule ℓ A θ
    letI := (rhoLam ℓ lam).toAlgebra
    Module.finrank (lam.adicCompletion (coeffField f))
        (lam.adicCompletion (coeffField f) ⊗[ℚ_[ℓ] ⊗[ℚ] coeffField f] A.V ℓ) = 2 ∧
    ∃ c : coeffField f, (c : ℂ) = χ (p : ZMod N) ∧
      Polynomial.aeval (frobLam ℓ A θ lam σ)
        ((Polynomial.X : Polynomial (lam.adicCompletion (coeffField f))) ^ 2 -
          Polynomial.C (algebraMap (coeffField f) (lam.adicCompletion (coeffField f))
            ⟨coeff f p, coeff_mem_coeffField f p⟩) * Polynomial.X +
          Polynomial.C (algebraMap (coeffField f) (lam.adicCompletion (coeffField f))
            (c * (p : coeffField f)))) = 0

/-- **Fallback leaf (the determinant of `ρ_{f,λ}` at Frobenius, `det ρ_{f,λ} = χ χ_ℓ`).** For `p ∤ Nℓ`,
`det ρ_{f,λ}(Frob_p) = χ(p) p`. Printed form only if a statement check finds the determinant formula in
print (the review: possibly only Diamond–Shurman Exercise 9.6.3(b); Shimura 1971 Thm 7.14, Ribet 1977,
UNVERIFIED). Not in the fold. -/
def AfDetLambda : Prop :=
  AtFrobLam fun N χ f A θ _ ℓ _ lam _ p σ =>
    letI := R16Used.tensorModule ℓ A θ
    letI := (rhoLam ℓ lam).toAlgebra
    ∃ c : coeffField f, (c : ℂ) = χ (p : ZMod N) ∧
      LinearMap.det (frobLam ℓ A θ lam σ) =
        algebraMap (coeffField f) (lam.adicCompletion (coeffField f)) (c * (p : coeffField f))

/-- A linear map of a 2-dimensional space satisfying a monic quadratic whose constant term is its nonzero
determinant has that quadratic as characteristic polynomial. -/
theorem charpoly_of_aeval_det_lin {F M : Type*} [Field F] [AddCommGroup M] [Module F M]
    [FiniteDimensional F M] (hM : Module.finrank F M = 2) (g : M →ₗ[F] M) (t d : F)
    (h : Polynomial.aeval g (Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C d) = 0)
    (hd : LinearMap.det g = d) (hd0 : d ≠ 0) :
    g.charpoly = Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C d := by
  let b := Module.finBasisOfFinrankEq F M hM
  rw [← LinearMap.charpoly_toMatrix g b]
  refine DS965Weak.charpoly_of_aeval_det ?_ ?_ hd0
  · have hmat : LinearMap.toMatrixAlgEquiv b g = LinearMap.toMatrix b b g := by
      ext i j; rw [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
    have := Polynomial.aeval_algHom_apply (LinearMap.toMatrixAlgEquiv b).toAlgHom g
      (Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C d)
    rw [h, map_zero] at this
    rw [← hmat]
    exact this
  · rw [LinearMap.det_toMatrix]; exact hd

/-- **The fold's leaf from the fallback pair (glue, proved).** -/
theorem dsLambda_of_sat_det (hS : AfTateDSLambdaSat) (hD : AfDetLambda) : AfTateDSLambda := by
  intro N χ f hN hf X _ jX tX hC hG P₀ J aj hJ tp δ htp hδ A π θ hQ hAct _ ℓ _ lam _ _ p hp hpN σ hσ
  obtain ⟨h2, c, hc, hae⟩ := hS N χ f hN hf X jX tX hC hG P₀ J aj hJ tp δ htp hδ A π θ hQ hAct ℓ lam
    p hp hpN σ hσ
  obtain ⟨c', hc', hdet⟩ := hD N χ f hN hf X jX tX hC hG P₀ J aj hJ tp δ htp hδ A π θ hQ hAct ℓ lam
    p hp hpN σ hσ
  have hcc : c' = c := Subtype.ext (hc'.trans hc.symm)
  subst hcc
  refine ⟨c', hc, ?_⟩
  letI := R16Used.tensorModule ℓ A θ
  letI := (rhoLam ℓ lam).toAlgebra
  have hpN' : Nat.Coprime p N :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 (fun h => hpN (dvd_mul_of_dvd_left h ℓ))
  have hχ : χ (p : ZMod N) ≠ 0 := by
    have hu : IsUnit (p : ZMod N) := (ZMod.isUnit_iff_coprime p N).2 hpN'
    exact (hu.map χ).ne_zero
  have hc0 : c' ≠ 0 := by
    intro h0; apply hχ; rw [← hc', h0]; rfl
  have hd0 : algebraMap (coeffField f) (lam.adicCompletion (coeffField f)) (c' * (p : coeffField f)) ≠ 0 := by
    rw [map_ne_zero]
    exact mul_ne_zero hc0 (Nat.cast_ne_zero.2 hp.ne_zero)
  exact charpoly_of_aeval_det_lin h2 _ _ _ hae hdet hd0

end SatisfiesForm

end AfTateLam
