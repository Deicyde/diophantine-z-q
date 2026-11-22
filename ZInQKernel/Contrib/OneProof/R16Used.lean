import ZInQKernel.Contrib.OneProof.R16Split

/-! # r16-used: the field `r16CoreY` from the printed existence form of Diamond–Shurman §9.5

Task r16-used (2026-11-15), report `docs/research/r16-used.md`, scratch `scratch/r16-used/`.

**Consumers.** On the route, R16 (`LeafModCurves.R16_EichlerShimuraJ1'`, now supplied from the
field `r16CoreY : R16Split.R16CoreY` through `R16Split.r16_of_printed`) is used once:
`G0ModNewform.g13` → `commonConstituent_of_attached` (`OneProof/H/TailA.lean`), at `ℓ = 5`, the
embedding `ι = ι₅ ∘ ι_C⁻¹` (`embOf`), the newform `f` obtained from Pan–Berger's eigenform for `r₅`
(T24, T25), arbitrary level `N`, every `J₁(N)`. It uses `[K_f : ℚ] < ∞`, the quotient `π : J ↠ A`,
`θ`, the rank-two clause and the trace clause; not the dimension clause, not the determinant
clause. `R16Trace` below is that weakest form.

**The new leaf.** `AfTateCharPoly` is the existence form of Diamond–Shurman's Lemma 9.5.3 and
Theorem 9.5.4 for Shimura's `A_f` (numbers UNVERIFIED): there are a quotient `π : J₁(N) ↠ A` over
`ℚ` and `θ : K_f → End⁰(A)` such that for every prime `ℓ`, `V_ℓ(A)` is free of rank 2 over
`ℚ_ℓ ⊗_ℚ K_f` (module through `θ`), and for `p ∤ Nℓ` the characteristic polynomial over
`ℚ_ℓ ⊗ K_f` of arithmetic Frobenius in that basis is `X² − a_p X + χ(p) p`. It is the printed
statement with the abelian variety `A_f = J₁(N)/I_f J₁(N)` (no Lean definition: no Hecke
correspondences on `X₁(N)`) replaced by an existential, in the manner of the published leaf
`dsThm965` (Diamond–Shurman 9.6.5, existential in `ρ`).

**Proved here (glue).**
* `r16_of_afTate : AfTateCharPoly → PkgI3.TateModuleFree → R16_EichlerShimuraJ1'`: the
  `ι`-eigenfunctionals of a free rank-two `ℚ_ℓ ⊗ K_f`-module are 2-dimensional, Frobenius acts on
  them by `ι_R` of the transposed matrix (so trace `ι(a_p)` and determinant `ι(χ(p))p`),
  `[K_f : ℚ] < ∞` by faithfully flat descent, and `dim A = [K_f : ℚ]` from the rank-two clause
  (`R16Split.dim_eq_of_rank_two`);
* `r16CoreY_of_printed : AfTateCharPoly → AvSplit.MumfordTorsionAlgClosed → R16Split.R16CoreY`,
  the discharge of the field (`mumfordTorsionAlgClosed` is already a published leaf of the bundle);
* `r16Trace_of_r16`, `r16Trace_of_coreY`: the weakest form is a consequence of R16 and of the
  current field.

No `sorry`, no `axiom`. -/

noncomputable section

set_option linter.unusedSectionVars false

namespace R16Used

open Module PkgI3 PkgI3.AbVar LeafModCurves
open scoped TensorProduct

/-! ## 1. `ℚ_ℓ ⊗ F` acting through a ring homomorphism -/

section Lift

variable {k F S : Type*} [Field k] [Algebra ℚ k] [Field F] [Algebra ℚ F] [Ring S] [Algebra k S]

/-- `x ⊗ a ↦ x · ψ(a)` on `k ⊗_ℚ F`, additively. -/
def liftAdd (ψ : F →+* S) : k ⊗[ℚ] F →+ S :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun x : k => AddMonoidHom.mk' (fun a : F => algebraMap k S x * ψ a)
        (by intro a b; rw [map_add, mul_add]))
      (by intro x y; ext a; simp [add_mul]))
    (by
      intro q x a
      simp only [AddMonoidHom.mk'_apply]
      have hq : ψ (algebraMap ℚ F q) = algebraMap k S (algebraMap ℚ k q) := by
        have : ψ.comp (algebraMap ℚ F) = (algebraMap k S).comp (algebraMap ℚ k) :=
          RingHom.ext_rat _ _
        exact RingHom.congr_fun this q
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, hq]
      simp only [← mul_assoc]
      rw [show algebraMap k S (algebraMap ℚ k q) * algebraMap k S x =
        algebraMap k S x * algebraMap k S (algebraMap ℚ k q) by rw [← map_mul, ← map_mul, mul_comm]])

theorem liftAdd_tmul (ψ : F →+* S) (x : k) (a : F) :
    liftAdd ψ (x ⊗ₜ a) = algebraMap k S x * ψ a := by
  simp [liftAdd]

/-- `x ⊗ a ↦ x · ψ(a)` on `k ⊗_ℚ F`, a ring homomorphism. -/
def liftHom (ψ : F →+* S) : k ⊗[ℚ] F →+* S where
  toFun := liftAdd ψ
  map_one' := by
    rw [Algebra.TensorProduct.one_def, liftAdd_tmul, map_one, map_one, one_mul]
  map_mul' x y := by
    induction x using TensorProduct.inductionOn with
    | tmul x a =>
      induction y using TensorProduct.inductionOn with
      | tmul y b =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, liftAdd_tmul, liftAdd_tmul, liftAdd_tmul,
          map_mul, map_mul, mul_assoc, mul_assoc, ← mul_assoc (ψ a), ← Algebra.commutes y,
          mul_assoc]
      | add y y' hy hy' => rw [mul_add, map_add, map_add, hy, hy', mul_add]
    | add x x' hx hx' => rw [add_mul, map_add, map_add, hx, hx', add_mul]
  map_zero' := map_zero _
  map_add' := map_add _

theorem liftHom_tmul (ψ : F →+* S) (x : k) (a : F) :
    liftHom ψ (x ⊗ₜ a) = algebraMap k S x * ψ a := liftAdd_tmul ψ x a

end Lift


/-! ## 2. A free rank-two `k ⊗ F`-module: the `ι`-eigenfunctionals, trace and determinant -/

section Generic

variable {k F V Ω : Type*} [Field k] [Algebra ℚ k] [Field F] [Algebra ℚ F]
  [AddCommGroup V] [Module k V] [Field Ω] [Algebra k Ω]

/-- `V` as a `k ⊗_ℚ F`-module through `ρ : F → End_k(V)`. -/
@[instance_reducible]
def tModule (ρ : F →+* Module.End k V) : Module (k ⊗[ℚ] F) V :=
  Module.compHom V (liftHom ρ)

theorem tsmul_def (ρ : F →+* Module.End k V) (r : k ⊗[ℚ] F) (v : V) :
    (letI := tModule ρ; r • v) = liftHom ρ r v := rfl

theorem tsmul_left (ρ : F →+* Module.End k V) (x : k) (v : V) :
    (letI := tModule ρ; ((x ⊗ₜ (1 : F) : k ⊗[ℚ] F) • v)) = x • v := by
  rw [tsmul_def, liftHom_tmul, map_one, mul_one, Module.algebraMap_end_apply]

theorem tsmul_right (ρ : F →+* Module.End k V) (a : F) (v : V) :
    (letI := tModule ρ; (((1 : k) ⊗ₜ a : k ⊗[ℚ] F) • v)) = ρ a v := by
  rw [tsmul_def, liftHom_tmul, map_one, one_mul]

theorem liftHom_one_tmul (emb : F →+* Ω) (a : F) :
    liftHom emb ((1 : k) ⊗ₜ a : k ⊗[ℚ] F) = emb a := by
  rw [liftHom_tmul, map_one, one_mul]

theorem liftHom_tmul_one (emb : F →+* Ω) (x : k) :
    liftHom emb (x ⊗ₜ (1 : F) : k ⊗[ℚ] F) = algebraMap k Ω x := by
  rw [liftHom_tmul, map_one, mul_one]

variable (ρ : F →+* Module.End k V) (emb : F →+* Ω) (E : Submodule Ω (V →ₗ[k] Ω))
  (hE : ∀ φ, φ ∈ E ↔ ∀ a, φ ∘ₗ ρ a = emb a • φ)

include hE in
/-- An `ι`-eigenfunctional is semilinear along `ι_R : k ⊗ F → Ω`. -/
theorem semilin {φ : V →ₗ[k] Ω} (hφ : φ ∈ E) (r : k ⊗[ℚ] F) (v : V) :
    φ (liftHom ρ r v) = liftHom emb r * φ v := by
  induction r using TensorProduct.inductionOn with
  | tmul x a =>
    have h1 := LinearMap.congr_fun ((hE φ).1 hφ a) v
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h1
    rw [liftHom_tmul, liftHom_tmul, Module.End.mul_apply, Module.algebraMap_end_apply,
      LinearMap.map_smul, h1, smul_eq_mul, Algebra.smul_def, mul_assoc]
  | add r s hr hs => rw [map_add, LinearMap.add_apply, map_add, hr, hs, map_add, add_mul]

include hE in
/-- An `ι`-eigenfunctional is determined by its values on an `k ⊗ F`-basis. -/
theorem eval_eq (b : letI := tModule ρ; Module.Basis (Fin 2) (k ⊗[ℚ] F) V)
    {φ : V →ₗ[k] Ω} (hφ : φ ∈ E) (v : V) :
    (letI := tModule ρ; φ v = ∑ i, liftHom emb (b.repr v i) * φ (b i)) := by
  let _ := tModule ρ
  conv_lhs => rw [← b.sum_repr v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tsmul_def, semilin ρ emb E hE hφ]

/-- The inverse of the coordinate map: `w ↦ (v ↦ Σ_i ι_R(b^*_i(v)) w_i)`. -/
def coordInv (b : letI := tModule ρ; Module.Basis (Fin 2) (k ⊗[ℚ] F) V) (w : Fin 2 → Ω) :
    V →ₗ[k] Ω :=
  letI := tModule ρ
  { toFun := fun v => ∑ i, liftHom emb (b.repr v i) * w i
    map_add' := fun u v => by
      simp only [map_add, Finsupp.add_apply, add_mul, Finset.sum_add_distrib]
    map_smul' := fun x v => by
      rw [RingHom.id_apply, ← tsmul_left ρ x v, LinearEquiv.map_smul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finsupp.smul_apply, smul_eq_mul, map_mul, liftHom_tmul_one, Algebra.smul_def,
        mul_assoc] }

include hE in
theorem coordInv_mem (b : letI := tModule ρ; Module.Basis (Fin 2) (k ⊗[ℚ] F) V)
    (w : Fin 2 → Ω) : coordInv ρ emb b w ∈ E := by
  let _ := tModule ρ
  rw [hE]
  intro a
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, coordInv, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [← tsmul_right ρ a v, LinearEquiv.map_smul, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, map_mul, liftHom_one_tmul, mul_assoc]

theorem coordInv_apply_basis (b : letI := tModule ρ; Module.Basis (Fin 2) (k ⊗[ℚ] F) V)
    (w : Fin 2 → Ω) (j : Fin 2) : (letI := tModule ρ; coordInv ρ emb b w (b j) = w j) := by
  let _ := tModule ρ
  simp only [coordInv, LinearMap.coe_mk, AddHom.coe_mk, Module.Basis.repr_self]
  rw [Finset.sum_eq_single j (fun i _ hij => by rw [Finsupp.single_eq_of_ne hij, map_zero,
    zero_mul]) (fun h => absurd (Finset.mem_univ j) h), Finsupp.single_eq_same, map_one, one_mul]

/-- The coordinate map `E → Ω²`, `φ ↦ (φ(b 0), φ(b 1))`. -/
def coordL (b : letI := tModule ρ; Module.Basis (Fin 2) (k ⊗[ℚ] F) V) : E →ₗ[Ω] (Fin 2 → Ω) where
  toFun φ i := (φ : V →ₗ[k] Ω) (b i)
  map_add' _ _ := by ext i; simp
  map_smul' _ _ := by ext i; simp

include hE in
theorem coordL_bijective (b : letI := tModule ρ; Module.Basis (Fin 2) (k ⊗[ℚ] F) V) :
    Function.Bijective (coordL ρ E b) := by
  constructor
  · intro φ ψ h
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    have hi : ∀ i, (φ : V →ₗ[k] Ω) (b i) = (ψ : V →ₗ[k] Ω) (b i) := fun i => congrFun h i
    rw [eval_eq ρ emb E hE b φ.2, eval_eq ρ emb E hE b ψ.2]
    simp only [hi]
  · intro w
    exact ⟨⟨coordInv ρ emb b w, coordInv_mem ρ emb E hE b w⟩,
      funext fun j => coordInv_apply_basis ρ emb b w j⟩

/-- The coordinate isomorphism `E ≃ Ω²`. -/
def coordEquiv (b : letI := tModule ρ; Module.Basis (Fin 2) (k ⊗[ℚ] F) V) :
    E ≃ₗ[Ω] (Fin 2 → Ω) :=
  LinearEquiv.ofBijective (coordL ρ E b) (coordL_bijective ρ emb E hE b)

include hE in
theorem finrank_eq_two (b : letI := tModule ρ; Module.Basis (Fin 2) (k ⊗[ℚ] F) V) :
    Module.finrank Ω E = 2 := by
  rw [(coordEquiv ρ emb E hE b).finrank_eq, Module.finrank_fin_fun]

/-- The matrix of `g` in the basis `b`, `g(b j) = Σ_i M i j • b i`. -/
def matOf (b : letI := tModule ρ; Module.Basis (Fin 2) (k ⊗[ℚ] F) V) (g : V →ₗ[k] V) :
    Matrix (Fin 2) (Fin 2) (k ⊗[ℚ] F) :=
  letI := tModule ρ
  Matrix.of fun i j => b.repr (g (b j)) i

include hE in
/-- Precomposition by `g` on `E`, in coordinates: the transpose of `ι_R(M)`. -/
theorem coord_conj (b : letI := tModule ρ; Module.Basis (Fin 2) (k ⊗[ℚ] F) V)
    (g : V →ₗ[k] V) (T : E →ₗ[Ω] E) (hT : ∀ φ, (T φ : V →ₗ[k] Ω) = (φ : V →ₗ[k] Ω) ∘ₗ g) :
    (coordEquiv ρ emb E hE b).conj T =
      Matrix.toLin' ((matOf ρ b g).map (liftHom emb)).transpose := by
  apply LinearMap.ext
  intro w
  obtain ⟨φ, rfl⟩ := (coordEquiv ρ emb E hE b).surjective w
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  funext j
  change ((T φ : E) : V →ₗ[k] Ω) (b j) = _
  rw [hT, LinearMap.comp_apply, eval_eq ρ emb E hE b φ.2, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rfl

include hE in
theorem trace_det_of_basis (b : letI := tModule ρ; Module.Basis (Fin 2) (k ⊗[ℚ] F) V)
    (g : V →ₗ[k] V) (T : E →ₗ[Ω] E) (hT : ∀ φ, (T φ : V →ₗ[k] Ω) = (φ : V →ₗ[k] Ω) ∘ₗ g) :
    LinearMap.trace Ω E T = liftHom emb (matOf ρ b g).trace ∧
      @LinearMap.det E _ Ω _ _ T = liftHom emb (matOf ρ b g).det := by
  have h := coord_conj ρ emb E hE b g T hT
  constructor
  · have h1 := LinearMap.trace_conj' (R := Ω) (M := E) (N := Fin 2 → Ω) T (coordEquiv ρ emb E hE b)
    rw [h, Matrix.trace_toLin'_eq, Matrix.trace_transpose] at h1
    rw [← h1, AddMonoidHom.map_trace]
  · have h1 := LinearMap.det_conj (A := Ω) (M := E) (N := Fin 2 → Ω) T (coordEquiv ρ emb E hE b)
    rw [LinearEquiv.conj_apply, LinearMap.comp_assoc] at h
    rw [h, LinearMap.det_toLin', Matrix.det_transpose] at h1
    rw [← h1, RingHom.map_det]
    rfl

end Generic

/-- Trace and determinant of a `2 × 2` matrix from its characteristic polynomial. -/
theorem trace_det_of_charpoly {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) (t d : R)
    (h : M.charpoly = Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C d) :
    M.trace = t ∧ M.det = d := by
  constructor
  · rw [Matrix.trace_eq_neg_charpoly_coeff, h]
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_C]
  · rw [Matrix.det_eq_sign_charpoly_coeff, h]
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X]

/-! ## 3. The `ℚ_ℓ ⊗ K_f`-module structure on `V_ℓ(A)` -/

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `ℚ_ℓ ⊗_ℚ F` acting on `V_ℓ(A)` through `θ : F → End⁰(A)`: `x ⊗ a ↦ x · V_ℓ(θ a)`. -/
def tensorAct (A : AbVar ℚ) {F : Type} [Field F] [Algebra ℚ F] (θ : F →+* A.End0) :
    ℚ_[ℓ] ⊗[ℚ] F →+* Module.End ℚ_[ℓ] (A.V ℓ) :=
  liftHom (R16Split.rhoV ℓ A θ)

/-- **`V_ℓ(A)` as a `ℚ_ℓ ⊗_ℚ F`-module** through `θ` (DS §9.5: `V_ℓ(A_f)` as a
`K_f ⊗ ℚ_ℓ`-module). -/
@[instance_reducible]
def tensorModule (A : AbVar ℚ) {F : Type} [Field F] [Algebra ℚ F] (θ : F →+* A.End0) :
    Module (ℚ_[ℓ] ⊗[ℚ] F) (A.V ℓ) :=
  tModule (R16Split.rhoV ℓ A θ)

/-- The matrix of `σ ∈ G_ℚ` on `V_ℓ(A)` in an `ℚ_ℓ ⊗ F`-basis `b`: `σ(b j) = Σ_i M i j • b i`
(`σ` is `ℚ_ℓ ⊗ F`-linear, `frob_linear` below). -/
def frobMat (A : AbVar ℚ) {F : Type} [Field F] [Algebra ℚ F] (θ : F →+* A.End0)
    (b : letI := tensorModule ℓ A θ; Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] F) (A.V ℓ))
    (σ : PkgI4.GQ) : Matrix (Fin 2) (Fin 2) (ℚ_[ℓ] ⊗[ℚ] F) :=
  letI := tensorModule ℓ A θ
  Matrix.of fun i j => b.repr (A.galRep ℓ σ (b j)) i

/-- `G_ℚ` acts `ℚ_ℓ ⊗ F`-linearly on `V_ℓ(A)` (endomorphisms are defined over `ℚ`), so
`frobMat` is the matrix of an `ℚ_ℓ ⊗ F`-linear map. -/
theorem galRep_tsmul (A : AbVar ℚ) {F : Type} [Field F] [Algebra ℚ F] (θ : F →+* A.End0)
    (σ : PkgI4.GQ) (r : ℚ_[ℓ] ⊗[ℚ] F) (v : A.V ℓ) :
    (letI := tensorModule ℓ A θ; A.galRep ℓ σ (r • v) = r • A.galRep ℓ σ v) := by
  change A.galRep ℓ σ (liftHom (R16Split.rhoV ℓ A θ) r v) =
    liftHom (R16Split.rhoV ℓ A θ) r (A.galRep ℓ σ v)
  induction r using TensorProduct.inductionOn with
  | tmul x a =>
    rw [liftHom_tmul, Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, LinearMap.map_smul]
    congr 1
    exact (LinearMap.congr_fun (endV_comm ℓ A σ (θ a)) v).symm
  | add r s hr hs => rw [map_add, LinearMap.add_apply, map_add, hr, hs, LinearMap.add_apply]

/-- `X² − (1 ⊗ a) X + (1 ⊗ d)` over `ℚ_ℓ ⊗_ℚ F`. -/
def esPoly {F : Type} [Field F] [Algebra ℚ F] (a d : F) : Polynomial (ℚ_[ℓ] ⊗[ℚ] F) :=
  Polynomial.X ^ 2 - Polynomial.C ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] a) * Polynomial.X +
    Polynomial.C ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] d)

/-- R16's `ι`-eigenfunctionals in the form of §2. -/
theorem mem_eigenFun_iff (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0)
    (emb : F →+* PadicAlgCl ℓ) (φ : A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ) :
    φ ∈ eigenFun ℓ A θ emb ↔ ∀ a, φ ∘ₗ R16Split.rhoV ℓ A θ a = emb a • φ := Iff.rfl

/-- **The `ι`-component from a `ℚ_ℓ ⊗ F`-basis (glue, proved).** If `V_ℓ(A)` is free of rank 2
over `ℚ_ℓ ⊗_ℚ F` (basis `b`), then for every `ι : F → ℚ̄_ℓ` the `ι`-eigenfunctionals form a
space of dimension 2, and `σ ∈ G_ℚ` acts on them with trace `ι_R(tr M_σ)` and determinant
`ι_R(det M_σ)`, where `M_σ` is the matrix of `σ` in `b` and `ι_R(x ⊗ a) = x ι(a)`. -/
theorem iota_component (A : AbVar ℚ) {F : Type} [Field F] [Algebra ℚ F] (θ : F →+* A.End0)
    (b : letI := tensorModule ℓ A θ; Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] F) (A.V ℓ))
    (emb : F →+* PadicAlgCl ℓ) :
    Module.finrank (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) = 2 ∧
      ∀ σ : PkgI4.GQ,
        LinearMap.trace (PadicAlgCl ℓ) _ (frobOn ℓ A θ emb σ) =
            liftHom emb (frobMat ℓ A θ b σ).trace ∧
          LinearMap.det (frobOn ℓ A θ emb σ) = liftHom emb (frobMat ℓ A θ b σ).det := by
  have hE := mem_eigenFun_iff ℓ A θ emb
  refine ⟨finrank_eq_two (R16Split.rhoV ℓ A θ) emb _ hE b, fun σ => ?_⟩
  exact trace_det_of_basis (R16Split.rhoV ℓ A θ) emb _ hE b (A.galRep ℓ σ)
    (frobOn ℓ A θ emb σ) (fun φ => rfl)

section Statement

open scoped MatrixGroups ModularForm
open PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff HasNebentypus IsNormalizedEigenform scaleH
  oldSpace IsNewform)

/-- **Leaf: Eichler–Shimura for `A_f`, existence form of Diamond–Shurman Lemma 9.5.3 and
Theorem 9.5.4.** Let `N ≥ 1`, `f ∈ S₂(Γ₁(N))` a newform with nebentypus `χ`, and `J` a Jacobian
of `X₁(N)` over `ℚ` (`IsJ1`). Then there are an abelian variety `A` over `ℚ`, a surjective
homomorphism `π : J → A` over `ℚ` and a ring homomorphism `θ : K_f → End⁰_ℚ(A)` such that for
every prime `ℓ`:
* `V_ℓ(A)`, a `ℚ_ℓ ⊗_ℚ K_f`-module through `θ` (`tensorModule`), is free of rank 2, with a basis
  `b`; and
* for every prime `p ∤ Nℓ` and every arithmetic Frobenius `σ ∈ G_ℚ` at a prime of `ℤ̄` above `p`,
  `χ(p) ∈ K_f`, and the characteristic polynomial over `ℚ_ℓ ⊗ K_f` of the matrix of `σ` in `b`
  (`frobMat`) is `X² − (1 ⊗ a_p(f)) X + (1 ⊗ χ(p) p)` (`esPoly`).

Printed source (locators UNVERIFIED, no network): Diamond–Shurman, *A First Course in Modular
Forms*, GTM 228 (2005): Definition 6.6.3 (`A_f = J₁(N)/I_f J₁(N)`, `K_f` acting through the Hecke
algebra), §7.9/§8.? (`A_f` and the `K_f`-action defined over `ℚ`), Lemma 9.5.3 (`V_ℓ(A_f)` free of
rank 2 over `K_f ⊗ ℚ_ℓ`, which defines `ρ_{A_f,ℓ} : G_ℚ → GL₂(K_f ⊗ ℚ_ℓ)`), Theorem 9.5.4
(`ρ_{A_f,ℓ}` unramified at `p ∤ ℓN`, characteristic polynomial of `ρ_{A_f,ℓ}(Frob_𝔭)` equal to
`x² − a_p(f) x + χ(p) p` for every maximal ideal `𝔭 ⊂ ℤ̄` over `p`); the same content is
Shimura 1971 Thms 7.9-7.14 and Ribet 1977 §1. The witness is `A = A_f`; the statement is weaker
than the print in three ways: newforms only (the print has normalized eigenforms), `A_f` replaced
by an existential (it has no Lean definition: no Hecke correspondences on `X₁(N)` and no
comparison `S₂(Γ₁(N)) ≅ H⁰(X₁(N), Ω¹)`, see `docs/research/r16-split.md` §4), and the unramified
clause dropped. One convention step is not printed: the print is for Diamond–Shurman's (Shimura's)
model of `X₁(N)`, and every model of §D of `ModCurves/Leaves.lean` is `ℚ`-isomorphic to it (leaf
MC9 of bp-modcurves). If a convention gives `ā_p`, `χ̄(p)`, replace `θ` by `θ ∘ c` (`K_f` is stable
under complex conjugation `c`). -/
def AfTateCharPoly : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (J : AbVar ℚ),
    0 < N → IsNewform f χ → IsJ1 N J →
    ∃ (A : AbVar ℚ) (π : Hom J A) (θ : coeffField f →+* A.End0),
      AlgebraicGeometry.Surjective π.hom.left ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime],
        ∃ b : (letI := tensorModule ℓ A θ; Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] coeffField f) (A.V ℓ)),
          ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
            ∃ c : coeffField f, (c : ℂ) = χ (p : ZMod N) ∧
              (frobMat ℓ A θ b σ).charpoly =
                esPoly ℓ (⟨coeff f p, coeff_mem_coeffField f p⟩ : coeffField f) (c * (p : coeffField f))


/-- **The weakest form of R16 that the route uses** (not proposed as a leaf). R16 without the
dimension and determinant clauses: `[K_f : ℚ] < ∞`, and a quotient `π : J ↠ A` over `ℚ` with
`θ : K_f → End⁰(A)` such that every `ι`-component of every `V_ℓ(A)` has dimension 2 and arithmetic
Frobenius at `p ∤ Nℓ` acts on it with trace `ι(a_p(f))`. The only consumer,
`G0ModNewform.commonConstituent_of_attached` (via `g13`), reads exactly these clauses, at `ℓ = 5`
and `ι = embOf 5 ι_C ι₅`; `scratch/r16-used/Bypass.lean` re-proves `g13` from `R16Trace`. -/
def R16Trace : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (J : AbVar ℚ),
    0 < N → IsNewform f χ → IsJ1 N J →
    FiniteDimensional ℚ (coeffField f) ∧
    ∃ (A : AbVar ℚ) (π : Hom J A) (θ : coeffField f →+* A.End0),
      AlgebraicGeometry.Surjective π.hom.left ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (emb : coeffField f →+* PadicAlgCl ℓ),
        Module.finrank (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) = 2 ∧
        ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
          LinearMap.trace (PadicAlgCl ℓ) _ (frobOn ℓ A θ emb σ) =
            emb ⟨coeff f p, coeff_mem_coeffField f p⟩

/-- The weakest form is a consequence of R16. -/
theorem r16Trace_of_r16 (h : LeafModCurves.R16_EichlerShimuraJ1') : R16Trace := by
  intro N χ f J hN hf hJ
  obtain ⟨hfin, A, π, θ, hπ, -, hrest⟩ := h N χ f J hN hf hJ
  refine ⟨hfin, A, π, θ, hπ, fun ℓ _ emb => ⟨(hrest ℓ emb).1, fun p hp hpN σ hσ => ?_⟩⟩
  exact ((hrest ℓ emb).2 p hp hpN σ hσ).1 _ rfl

/-- The weakest form from the current field `r16CoreY` and the bundle's two leaves. -/
theorem r16Trace_of_coreY (h : R16Split.R16CoreY) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hCP : ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed) : R16Trace :=
  r16Trace_of_r16 (R16Split.r16_of_printed h hM hCP)

/-- `[F : ℚ] < ∞` from a `ℚ_ℓ ⊗ F`-basis of a finite-dimensional `V`. -/
theorem finiteDimensional_of_basis {k F V : Type*} [Field k] [Algebra ℚ k] [Field F]
    [Algebra ℚ F] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : F →+* Module.End k V) (b : letI := tModule ρ; Module.Basis (Fin 2) (k ⊗[ℚ] F) V) :
    FiniteDimensional ℚ F := by
  let _ := tModule ρ
  let L : (k ⊗[ℚ] F) →ₗ[k] V :=
    { toFun := fun r => r • b 0
      map_add' := fun r s => add_smul r s (b 0)
      map_smul' := fun x r => by
        rw [RingHom.id_apply, Algebra.smul_def, mul_smul, Algebra.TensorProduct.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply, tsmul_left] }
  have hL : Function.Injective L := by
    intro r s hrs
    have h := congrArg (fun v => b.repr v 0) hrs
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.map_smul, Module.Basis.repr_self,
      Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h
    exact h
  have : Module.Finite k (k ⊗[ℚ] F) := Module.Finite.of_injective L hL
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat k

/-- **R16 from the printed existence form and `T_ℓ(A)` free of rank `2 dim A` (glue, proved).** -/
theorem r16_of_afTate (h : AfTateCharPoly) (hT : PkgI3.TateModuleFree) :
    LeafModCurves.R16_EichlerShimuraJ1' := by
  intro N χ f J hN hf hJ
  obtain ⟨A, π, θ, hπ, hb⟩ := h N χ f J hN hf hJ
  have hfin : FiniteDimensional ℚ (coeffField f) := by
    obtain ⟨b, -⟩ := hb 2
    obtain ⟨hfree, hfinT, -⟩ := hT ℚ A 2 (by norm_num)
    have := hfree; have := hfinT
    exact finiteDimensional_of_basis (R16Split.rhoV 2 A θ) b
  have key : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (emb : coeffField f →+* PadicAlgCl ℓ),
      Module.finrank (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) = 2 ∧
        ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : PkgI4.GQ, IsFrobAt σ p →
          (∀ a : coeffField f, (a : ℂ) = PkgI4.coeff f p →
              LinearMap.trace (PadicAlgCl ℓ) _ (frobOn ℓ A θ emb σ) = emb a) ∧
          (∀ c : coeffField f, (c : ℂ) = χ (p : ZMod N) →
              LinearMap.det (frobOn ℓ A θ emb σ) = emb c * p) := by
    intro ℓ _ emb
    obtain ⟨b, hcp⟩ := hb ℓ
    obtain ⟨h2, htd⟩ := iota_component ℓ A θ b emb
    refine ⟨h2, fun p hp hpN σ hσ => ?_⟩
    obtain ⟨c, hc, hchar⟩ := hcp p hp hpN σ hσ
    obtain ⟨htr, hdet⟩ := trace_det_of_charpoly _ _ _ hchar
    obtain ⟨htr', hdet'⟩ := htd σ
    refine ⟨fun a ha => ?_, fun c' hc' => ?_⟩
    · have : a = ⟨PkgI4.coeff f p, coeff_mem_coeffField f p⟩ := Subtype.ext ha
      rw [htr', htr, liftHom_one_tmul, this]
    · have : c' = c := Subtype.ext (hc'.trans hc.symm)
      rw [hdet', hdet, liftHom_one_tmul, this, map_mul, map_natCast]
  refine ⟨hfin, A, π, θ, hπ, ?_, key⟩
  exact R16Split.dim_eq_of_rank_two hT A θ (fun emb => (key 2 emb).1)

/-- **The field `r16CoreY` from the printed existence form and the bundle's
`mumfordTorsionAlgClosed`** (which gives `T_ℓ(A)` free of rank `2 dim A`). -/
theorem r16CoreY_of_printed (h : AfTateCharPoly) (hM : AvSplit.MumfordTorsionAlgClosed) :
    R16Split.R16CoreY :=
  R16Split.coreY_of_r16 (r16_of_afTate h
    (T5Torsion.TateFree.tateModuleFree_of_torsionStructure (AvSplit.torsionStructure_of_mumford hM)))

end Statement

end R16Used

