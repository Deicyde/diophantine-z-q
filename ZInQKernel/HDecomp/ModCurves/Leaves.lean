import ZInQKernel.HDecomp.ModCurves.Genus
import ZInQKernel.HDecomp.ModCurves.Defs

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt3 from
`scratch/leaf-modcurves/ModCurveLeaves.lean`, §F-§H.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

noncomputable section

namespace LeafModCurves

open scoped MatrixGroups ModularForm
open PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff HasNebentypus IsNormalizedEigenform scaleH
  oldSpace IsNewform)
open WeierstrassCurve AlgebraicGeometry
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 PkgI3.AbVar

/-! ## §F. The leaf R16 (existential form) -/

section R16

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `End(A)` acting on `V_ℓ(A)` (covariantly, through `T_ℓ`). -/
def homVAdd (A : AbVar ℚ) : A.End →+ Module.End ℚ_[ℓ] (A.V ℓ) :=
  (LinearMap.baseChangeHom ℤ_[ℓ] ℚ_[ℓ] (A.T ℓ) (A.T ℓ)).toAddMonoidHom.comp (tateHom ℓ A A)

/-- `End⁰(A) = ℚ ⊗ End(A)` acting on `V_ℓ(A)`: `q ⊗ e ↦ q · V_ℓ(e)`. -/
def endV (A : AbVar ℚ) : A.End0 →+ Module.End ℚ_[ℓ] (A.V ℓ) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun q : ℚ =>
        AddMonoidHom.mk' (fun e : A.End => (q : ℚ_[ℓ]) • homVAdd ℓ A e)
          (by intro a b; simp only [map_add, smul_add]))
      (by intro a b; exact AddMonoidHom.ext fun e => by simp [add_smul]))
    (by
      intro n q e
      simp only [AddMonoidHom.mk'_apply]
      rw [map_zsmul, smul_comm (q : ℚ_[ℓ]) n, zsmul_eq_mul q n, Rat.cast_mul, Rat.cast_intCast,
        mul_smul, Int.cast_smul_eq_zsmul])

/-- **The `ι`-eigenfunctionals.** For a field `F` acting on `A` through `θ : F → End⁰(A)` and an
embedding `ι : F → ℚ̄_ℓ`: the `ℚ_ℓ`-linear maps `φ : V_ℓ(A) → ℚ̄_ℓ` with `φ ∘ θ(a) = ι(a) φ`.
When `V_ℓ(A)` is free of rank `r` over `F ⊗ ℚ_ℓ`, this is the dual of the `ι`-component
`V_ℓ(A) ⊗_{F ⊗ ℚ_ℓ, ι} ℚ̄_ℓ`, of dimension `r`. -/
def eigenFun (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0) (emb : F →+* PadicAlgCl ℓ) :
    Submodule (PadicAlgCl ℓ) (A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ) where
  carrier := {φ | ∀ a : F, φ ∘ₗ endV ℓ A (θ a) = emb a • φ}
  zero_mem' := by intro a; simp
  add_mem' := by
    intro φ ψ hφ hψ a
    simp only [Set.mem_ofPred_eq] at hφ hψ
    rw [LinearMap.add_comp, hφ a, hψ a, smul_add]
  smul_mem' := by
    intro c φ hφ a
    simp only [Set.mem_ofPred_eq] at hφ
    rw [LinearMap.smul_comp, hφ a, smul_comm]

/-- `σ ∈ G_ℚ` acting on functionals by `φ ↦ φ ∘ ρ_ℓ(σ)`: the transpose of `ρ_ℓ(σ)`. Its
restriction to `eigenFun` is the transpose of `σ` on the `ι`-component, with the same trace and
determinant. -/
def dualAct (A : AbVar ℚ) (σ : GQ) :
    (A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ) →ₗ[PadicAlgCl ℓ] (A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ) where
  toFun φ := φ ∘ₗ A.galRep ℓ σ
  map_add' _ _ := LinearMap.add_comp _ _ _
  map_smul' _ _ := LinearMap.smul_comp _ _ _

theorem homVAdd_apply (A : AbVar ℚ) (e : A.End) :
    homVAdd ℓ A e = (homT (ℓ := ℓ) e).baseChange ℚ_[ℓ] := rfl

theorem galRep_apply (A : AbVar ℚ) (σ : GQ) :
    A.galRep ℓ σ = (A.galT (ℓ := ℓ) σ).baseChange ℚ_[ℓ] := rfl

/-- `End⁰(A)` commutes with `G_ℚ` on `V_ℓ(A)` (endomorphisms are defined over `ℚ`; from the
kernel's `PkgI3.homT_galT`). -/
theorem endV_comm (A : AbVar ℚ) (σ : GQ) (x : A.End0) :
    endV ℓ A x ∘ₗ A.galRep ℓ σ = A.galRep ℓ σ ∘ₗ endV ℓ A x := by
  induction x using TensorProduct.inductionOn with
  | tmul q e =>
    have h1 : homT (ℓ := ℓ) e ∘ₗ A.galT σ = A.galT σ ∘ₗ homT e :=
      LinearMap.ext fun t => homT_galT e σ t
    simp only [endV, TensorProduct.liftAddHom_tmul, AddMonoidHom.mk'_apply, homVAdd_apply,
      galRep_apply]
    rw [LinearMap.smul_comp, LinearMap.comp_smul, ← LinearMap.baseChange_comp,
      ← LinearMap.baseChange_comp, h1]
  | add x y hx hy => simp only [map_add, LinearMap.add_comp, LinearMap.comp_add, hx, hy]

/-- `G_ℚ` preserves the `ι`-eigenfunctionals (proved, so R16 below does not assume it). -/
theorem dualAct_mem (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0)
    (emb : F →+* PadicAlgCl ℓ) (σ : GQ) :
    ∀ φ ∈ eigenFun ℓ A θ emb, dualAct ℓ A σ φ ∈ eigenFun ℓ A θ emb := by
  intro φ hφ a
  change (φ ∘ₗ A.galRep ℓ σ) ∘ₗ endV ℓ A (θ a) = emb a • (φ ∘ₗ A.galRep ℓ σ)
  rw [LinearMap.comp_assoc, ← endV_comm, ← LinearMap.comp_assoc, hφ a, LinearMap.smul_comp]

/-- `σ` acting on the `ι`-eigenfunctionals: the transpose of `σ` on the `ι`-component of
`V_ℓ(A) ⊗ ℚ̄_ℓ`. -/
def frobOn (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0) (emb : F →+* PadicAlgCl ℓ)
    (σ : GQ) : eigenFun ℓ A θ emb →ₗ[PadicAlgCl ℓ] eigenFun ℓ A θ emb :=
  (dualAct ℓ A σ).restrict (dualAct_mem ℓ A θ emb σ)

theorem dualAct_mul (A : AbVar ℚ) (σ τ : GQ) :
    dualAct ℓ A (σ * τ) = dualAct ℓ A τ ∘ₗ dualAct ℓ A σ := by
  apply LinearMap.ext; intro φ; apply LinearMap.ext; intro v
  change φ (A.galRep ℓ (σ * τ) v) = φ (A.galRep ℓ σ (A.galRep ℓ τ v))
  exact congrArg φ (LinearMap.congr_fun (map_mul (A.galRep ℓ) σ τ) v)

theorem dualAct_one (A : AbVar ℚ) : dualAct ℓ A 1 = LinearMap.id := by
  apply LinearMap.ext; intro φ; apply LinearMap.ext; intro v
  change φ (A.galRep ℓ 1 v) = φ v
  exact congrArg φ (LinearMap.congr_fun (map_one (A.galRep ℓ)) v)

theorem frobOn_mul (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0)
    (emb : F →+* PadicAlgCl ℓ) (σ τ : GQ) :
    frobOn ℓ A θ emb (σ * τ) = frobOn ℓ A θ emb τ ∘ₗ frobOn ℓ A θ emb σ := by
  apply LinearMap.ext; intro φ; apply Subtype.ext
  change dualAct ℓ A (σ * τ) φ = dualAct ℓ A τ (dualAct ℓ A σ φ)
  rw [dualAct_mul]; rfl

theorem frobOn_one (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0)
    (emb : F →+* PadicAlgCl ℓ) : frobOn ℓ A θ emb 1 = LinearMap.id := by
  apply LinearMap.ext; intro φ; apply Subtype.ext
  change dualAct ℓ A 1 φ = φ
  rw [dualAct_one]; rfl

/-- **`ρ_{f,ι}` as a representation** (glue): `G_ℚ` acting on the dual of the
`ι`-eigenfunctionals, i.e. on the `ι`-component of `V_ℓ(A) ⊗ ℚ̄_ℓ` itself (double dual), by
`σ ↦ (frobOn σ)ᵀ`. -/
def rhoF (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0) (emb : F →+* PadicAlgCl ℓ) :
    Representation (PadicAlgCl ℓ) GQ (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)) where
  toFun σ := (frobOn ℓ A θ emb σ).dualMap
  map_one' := by rw [frobOn_one, LinearMap.dualMap_id]; rfl
  map_mul' σ τ := by rw [frobOn_mul, ← LinearMap.dualMap_comp_dualMap]; rfl

theorem trace_rhoF (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0)
    (emb : F →+* PadicAlgCl ℓ) (h2 : Module.finrank (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) = 2)
    (σ : GQ) :
    LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ emb σ) =
      LinearMap.trace (PadicAlgCl ℓ) _ (frobOn ℓ A θ emb σ) := by
  have : Module.Finite (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) :=
    Module.finite_of_finrank_pos (by omega)
  exact LinearMap.trace_transpose' (frobOn ℓ A θ emb σ)

theorem finrank_rhoF (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0)
    (emb : F →+* PadicAlgCl ℓ) (h2 : Module.finrank (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) = 2) :
    Module.finrank (PadicAlgCl ℓ) (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)) = 2 := by
  have : Module.Finite (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) :=
    Module.finite_of_finrank_pos (by omega)
  rw [Subspace.dual_finrank_eq, h2]

end R16

/-- **R16. Eichler–Shimura in `J₁(N)`, existential form** (replaces the placeholder
`R16_EichlerShimuraJ1`). Let `N ≥ 1`, `f ∈ S₂(Γ₁(N))` a newform with nebentypus `χ`, and `J` a
Jacobian of `X₁(N)` over `ℚ` (`IsJ1`). Then `K_f` is a number field, and there are an abelian
variety `A` over `ℚ`, a surjective homomorphism `π : J → A` over `ℚ`, and a ring homomorphism
`θ : K_f → End⁰_ℚ(A)`, with `dim A = [K_f : ℚ]`, such that for every prime `ℓ` and every
embedding `ι : K_f → ℚ̄_ℓ`: the `ι`-component of `V_ℓ(A)` has dimension 2, and for every prime
`p ∤ Nℓ` and every arithmetic Frobenius `σ` at a place above `p`, `σ` acts on it with
trace `ι(a_p(f))` and determinant `ι(χ(p))·p`.

Sources (a consequence of three published statements, none of them the zeta clause):
(i) Shimura, J. Math. Soc. Japan 25 (1973), Thm 1, pp. 526-527, **unconditional clauses only**
(quotient `A_f` of `J₁(N)` over `ℚ`, `K_f` acting, `dim A_f = [K_f:ℚ]`); its final Euler-factor
clause carries an extra `Γ₀`/Fricke-stability condition and is **not** used here
(`docs/research/locators.md`, row R16); (ii) `V_ℓ(A_f)` free of rank 2 over `K_f ⊗ ℚ_ℓ`
(Shimura 1971 §7.4; Ribet 1977; UNVERIFIED locators); (iii) the Eichler–Shimura congruence
relation `T_p = Frob_p + p⟨p⟩Frob_p⁻¹` on `J₁(N)` mod `p ∤ N` (Shimura 1971 Thm 7.9;
Diamond–Shurman Thm 8.7.2; UNVERIFIED). The relation alone only gives an annihilating polynomial
of Frobenius on each `ι`-component; the characteristic polynomial `X² − ι(a_p)X + ι(χ(p))p` of
arithmetic Frobenius on the covariant `V_ℓ(A_f)`, `p ∤ Nℓ`, is printed as such in Diamond–Shurman
Thm 9.5.4 and Shimura 1971 Thm 7.11 / Ribet 1977 (UNVERIFIED numbers; review finding 2026-11-12),
which is the supplier to cite for the trace and determinant clauses.
Shimura's theorems are for his canonical model of `X₁(N)`; they transfer to every model of §D
because any two are `ℚ`-isomorphic (leaf MC9 of bp-modcurves: Shimura's canonical model for
`Γ₁(N)` has function field `ℚ(j, f_{(0,1/N)})`, `ℚ`-isomorphic to `K_N`; Shimura 1971 §6.7,
UNVERIFIED). If a convention gives `ā_p`, `χ̄(p)`, replace `θ` by `θ ∘ c` (`K_f` is totally real
or CM, so complex conjugation `c` preserves it): the statement is unaffected. -/
def R16_EichlerShimuraJ1' : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (J : AbVar ℚ),
    0 < N → IsNewform f χ → IsJ1 N J →
    FiniteDimensional ℚ (coeffField f) ∧
    ∃ (A : AbVar ℚ) (π : Hom J A) (θ : coeffField f →+* A.End0),
      Surjective π.hom.left ∧
      A.dim = ((Module.finrank ℚ (coeffField f) : ℕ) : WithBot ℕ∞) ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (emb : coeffField f →+* PadicAlgCl ℓ),
        Module.finrank (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) = 2 ∧
        ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
          (∀ a : coeffField f, (a : ℂ) = coeff f p →
              LinearMap.trace (PadicAlgCl ℓ) _ (frobOn ℓ A θ emb σ) = emb a) ∧
          (∀ c : coeffField f, (c : ℂ) = χ (p : ZMod N) →
              LinearMap.det (frobOn ℓ A θ emb σ) = emb c * p)

/-! ## §G. The genus and Belyi inputs of E2 / R18 -/

/-- **Leaf: `dim J₁(N)` is the genus of `Γ₁(N)`.** For `N ≥ 1` and `J` a Jacobian of `X₁(N)`,
`dim J = 1 + μ/12 − ν₂/4 − ν₃/3 − ν∞/2` with `μ = [SL₂(ℤ) : ±Γ₁(N)]`, `ν₂`, `ν₃` the fixed points
of `S`, `ST` and `ν∞` the `⟨T⟩`-orbits on `SL₂(ℤ)/±Γ₁(N)` (§A). Consequence of three published
statements: the genus formula for `Γ\ℍ*` (Shimura 1971, Prop. 1.40, UNVERIFIED number);
`X₁(N)_ℂ ≅ Γ₁(N)\ℍ*` for the canonical model (Shimura 1971 §6.7, UNVERIFIED) with leaf MC9 of
bp-modcurves; `dim Jac X = genus X` (Milne 1986, Prop. 2.1 / Thm 1.1, UNVERIFIED). The formula was
checked against the reference genus table for `N ≤ 30` (bp-modcurves `genus_check.py`). -/
def DimJ1Genus : Prop :=
  ∀ (N : ℕ) (J : AbVar ℚ), 0 < N → IsJ1 N J →
    ∃ g : ℕ, J.dim = (g : WithBot ℕ∞) ∧ (g : ℚ) = genus (CongruenceSubgroup.Gamma1 N)

/-- **Glue (proved): `dim J₁(N) ≤ N²`** (E2's `g ≤ N²`), from `DimJ1Genus` and
`genus_Gamma1_le`. -/
theorem dim_J1_le (h : DimJ1Genus) (N : ℕ) (hN : 0 < N) (J : AbVar ℚ) (hJ : IsJ1 N J) :
    ∃ g : ℕ, J.dim = (g : WithBot ℕ∞) ∧ g ≤ N ^ 2 := by
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨g, hg, hgen⟩ := h N J hN hJ
  refine ⟨g, hg, ?_⟩
  have h2 := genus_Gamma1_le N
  rw [← hgen] at h2
  exact_mod_cast h2

/-- **Belyi function over `k`** (function-field form). `t ∈ F` is transcendental over `k`, and
`k(t) ⊆ F` is unramified at every place `w` of `F/k` lying over a finite place of `k(t)` other
than `t = 0`, `t = 1`: if `t ∈ w` and `q(t) ∈ 𝔪_w` for a monic irreducible `q ∈ k[T]` with
`q ≠ T, T − 1` (then `w ∩ k(t) = k[t]_{(q)}`), then `q(t)` generates `𝔪_w` (ramification index 1).
In characteristic 0 this is preserved by extending constants to `k̄`, so for the function field of
a geometrically connected curve `X/k` it gives a Belyi map `X_k̄ → ℙ¹` of degree `[F : k(t)]`. -/
def IsBelyiFunction (k F : Type) [Field k] [Field F] [Algebra k F] (t : F) : Prop :=
  Transcendental k t ∧
  ∀ w : ValuationSubring F, (∀ c : k, algebraMap k F c ∈ w) → t ∈ w →
    ∀ q : Polynomial k, q.Monic → Irreducible q → q ≠ Polynomial.X → q ≠ Polynomial.X - 1 →
      Polynomial.aeval t q ∈ w.nonunits →
      ∀ x ∈ w.nonunits, ∃ y ∈ w, x = Polynomial.aeval t q * y

/-- **Glue target (MC1, MC5 of bp-modcurves): the standard Belyi map of `X₁(N)`.** `j/1728` is a
Belyi function on `K_N` over `ℚ`, of degree `[K_N : ℚ(j)] ≤ N²`. (Glazer N5 L868-870: "the genus
and the degree of its standard Belyi map are at most `N²`".) Provable: `j` is unramified away
from `j = 0, 1728, ∞` because `E_j` has good reduction there and `E[N]` is étale in
characteristic 0; the degree bound is `FieldX1DegreeLe` of bp-modcurves. Not a leaf. -/
def BelyiX1 : Prop :=
  ∀ (N : ℕ) (P : EjBar.toAffine.Point), 0 < N → addOrderOf P = N →
    IsBelyiFunction ℚ (fieldX1 P) (algebraMap Qj (fieldX1 P) (RatFunc.X / 1728)) ∧
    Module.finrank Qj (fieldX1 P) ≤ N ^ 2

/-! ## §H. Existence, the bundle, and the glue that C9, E1, E2 will consume -/

/-- **Existence of a pointed model of `X₁(N)` over `ℚ`.** Glue target (MC4 + MC10 of
bp-modcurves: the relative normalization of `ℙ¹_j` in `K_N` (`Y1j` is its affine chart) is a
smooth proper geometrically connected curve with function field `K_N`, and it has a `ℚ`-rational
cusp), or, as a leaf, the canonical model of Shimura 1971 §6.7 with a rational cusp
(UNVERIFIED locators). The main theorem must consume it: without it every statement
"`∀ J, IsJ1 N J → …`" is vacuous. -/
def X1ModelExists : Prop :=
  ∀ N : ℕ, 0 < N → ∃ (X : Over SpecQ) (_ : RatPt X), IsX1Model N X

/-- **The modular-curve leaves** (plus the existence statement `X1ModelExists`, a glue target
that may be taken as a leaf). -/
structure ModCurveLeaves : Prop where
  jac : JacobianExists ℚ
  x1 : X1ModelExists
  r16 : R16_EichlerShimuraJ1'
  dimJ1 : DimJ1Genus

/-- **Glue (proved): `J₁(N)` exists.** -/
theorem exists_J1 (hJ : JacobianExists ℚ) (hX : X1ModelExists) (N : ℕ) (hN : 0 < N) :
    ∃ J : AbVar ℚ, IsJ1 N J := by
  obtain ⟨X, P₀, hXm⟩ := hX N hN
  obtain ⟨J, aj, hJac⟩ := hJ X hXm.1 P₀
  exact ⟨J, X, P₀, aj, hXm, hJac⟩

/-- **Glue (proved), for E2**: a `J₁(N)` with `dim J₁(N) = g ≤ N²`. -/
theorem exists_J1_dim_le (L : ModCurveLeaves) (N : ℕ) (hN : 0 < N) :
    ∃ J : AbVar ℚ, IsJ1 N J ∧ ∃ g : ℕ, J.dim = (g : WithBot ℕ∞) ∧ g ≤ N ^ 2 := by
  obtain ⟨J, hJ⟩ := exists_J1 L.jac L.x1 N hN
  exact ⟨J, hJ, dim_J1_le L.dimJ1 N hN J hJ⟩

/-- **Glue (proved), the form C9 consumes**: for a newform `f` of level `N`, a `J₁(N)` together
with Shimura's quotient `A_f`, the `K_f`-action and the rank-2 `ι`-components with Frobenius
traces `ι(a_p(f))`. -/
theorem exists_J1_quotient (L : ModCurveLeaves) (N : ℕ) (hN : 0 < N)
    (χ : DirichletCharacter ℂ N) (f : CF N 2) (hf : IsNewform f χ) :
    ∃ J : AbVar ℚ, IsJ1 N J ∧ (∃ g : ℕ, J.dim = (g : WithBot ℕ∞) ∧ g ≤ N ^ 2) ∧
    FiniteDimensional ℚ (coeffField f) ∧
    ∃ (A : AbVar ℚ) (π : Hom J A) (θ : coeffField f →+* A.End0),
      Surjective π.hom.left ∧
      A.dim = ((Module.finrank ℚ (coeffField f) : ℕ) : WithBot ℕ∞) ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (emb : coeffField f →+* PadicAlgCl ℓ),
        Module.finrank (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) = 2 ∧
        ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
          (∀ a : coeffField f, (a : ℂ) = coeff f p →
              LinearMap.trace (PadicAlgCl ℓ) _ (frobOn ℓ A θ emb σ) = emb a) ∧
          (∀ c : coeffField f, (c : ℂ) = χ (p : ZMod N) →
              LinearMap.det (frobOn ℓ A θ emb σ) = emb c * p) := by
  obtain ⟨J, hJ, hdim⟩ := exists_J1_dim_le L N hN
  exact ⟨J, hJ, hdim, L.r16 N χ f J hN hf hJ⟩

/-- **Glue (proved), the shape of C10's hypothesis `hρ₅`**: from R16, for every newform `f` of
level `N`, every `J₁(N)`, every prime `ℓ` and every embedding `ι : K_f → ℚ̄_ℓ`, a 2-dimensional
representation `ρ` of `G_ℚ` over `ℚ̄_ℓ` (the `ι`-component of `V_ℓ(A_f)`) with
`tr ρ(g) = ι(a_p)` at every Frobenius `g` at `p ∉ S`, for any `S` containing the primes of `Nℓ`. -/
theorem rhoF_traces (hR16 : R16_EichlerShimuraJ1') (N : ℕ) (hN : 0 < N)
    (χ : DirichletCharacter ℂ N) (f : CF N 2) (hf : IsNewform f χ) (J : AbVar ℚ) (hJ : IsJ1 N J)
    (ℓ : ℕ) [Fact ℓ.Prime] (S : Finset ℕ) (hS : ∀ p, p.Prime → p ∣ N * ℓ → p ∈ S) :
    ∃ (A : AbVar ℚ) (π : Hom J A) (θ : coeffField f →+* A.End0), Surjective π.hom.left ∧
      ∀ emb : coeffField f →+* PadicAlgCl ℓ,
        Module.finrank (PadicAlgCl ℓ) (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)) = 2 ∧
        ∀ (g : GQ) (p : ℕ), p.Prime → p ∉ S → IsFrobAt g p →
          LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ emb g) =
            emb ⟨coeff f p, coeff_mem_coeffField f p⟩ := by
  obtain ⟨-, A, π, θ, hπ, -, hrest⟩ := hR16 N χ f J hN hf hJ
  refine ⟨A, π, θ, hπ, fun emb => ?_⟩
  obtain ⟨h2, hfr⟩ := hrest ℓ emb
  refine ⟨finrank_rhoF ℓ A θ emb h2, fun g p hp hpS hg => ?_⟩
  have hpN : ¬ p ∣ N * ℓ := fun hd => hpS (hS p hp hd)
  rw [trace_rhoF ℓ A θ emb h2]
  exact (hfr p hp hpN g hg).1 _ rfl


end LeafModCurves
