import ZInQKernel.HDecomp.ModCurves.Glue
import ZInQKernel.HDecomp.I3Linalg.C2

/-! # e1-sub, part 1: `VSurjOfSurjective` (proved) and `ρ_{f,ι}` as a subrepresentation of
`V_ℓ(J₁(N)) ⊗ ℚ̄_ℓ` over `G_ℚ`.

* §1 `vSurjOfSurjective`: the glue target `LeafModCurves.VSurjOfSurjective` holds, from the I3
  leaves `FaltingsSemisimple`, `FaltingsTate`, `TateModuleFree` (Faltings 1983 Satz 3, Satz 4 /
  Kor. 1; Mumford §4) and Mathlib's `ext_of_isDominant_of_isSeparated`. (No Poincaré
  reducibility is needed.)
* §2 `exists_subrep_equiv_of_surjective`: a surjective equivariant map out of a semisimple
  representation has an equivariant section onto a subrepresentation.
* §3 `rhoF_subrep_J`: R16's `ρ_{f,ι}` (`LeafModCurves.rhoF`) is isomorphic to a
  subrepresentation of `V_ℓ(J) ⊗ ℚ̄_ℓ`, for every `J₁(N)` `J`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 PkgI3.AbVar
open scoped TensorProduct

namespace E1Sub

/-! ## §1. A surjective homomorphism is surjective on `V_ℓ` -/

section VSurj

variable {K : Type} [Field K]

/-- Precomposition with `π : J → A`, `Hom(A, B) → Hom(J, B)`. -/
def precomp {J A B : AbVar K} (π : Hom J A) : Hom A B →ₗ[ℤ] Hom J B :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun f => Hom.mk' (π.hom ≫ f.hom)
      map_zero' := Hom.ext' (by simp)
      map_add' := fun f g => Hom.ext' (by simp [MonObj.comp_mul]) }

@[simp] lemma precomp_hom {J A B : AbVar K} (π : Hom J A) (f : Hom A B) :
    (precomp π f).hom = π.hom ≫ f.hom := rfl

lemma isReduced_left (A : AbVar K) : IsReduced A.X.left :=
  GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian A.X.hom

/-- Precomposition with a surjective homomorphism is injective (`A` is reduced, `B` separated). -/
lemma precomp_injective {J A B : AbVar K} (π : Hom J A) (hπ : Surjective π.hom.left) :
    Function.Injective (precomp (B := B) π) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  have h1 : π.hom ≫ f.hom = π.hom ≫ (1 : A.X ⟶ B.X) := by
    have := congrArg Hom.hom hf
    simp only [precomp_hom, Hom.hom_zero] at this
    rw [this, MonObj.comp_one]
  have := isReduced_left A
  apply Hom.ext'
  rw [Hom.hom_zero]
  apply Over.OverMorphism.ext
  exact ext_of_isDominant_of_isSeparated B.X.hom (by simp) π.hom.left
    (by rw [← Over.comp_left, ← Over.comp_left, h1])

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `V_ℓ(π)` over any field. -/
def homVK {J A : AbVar K} (π : Hom J A) : J.V ℓ →ₗ[ℚ_[ℓ]] A.V ℓ :=
  (homT (ℓ := ℓ) π).baseChange ℚ_[ℓ]

lemma homT_comp {J A B : AbVar K} (π : Hom J A) (f : Hom A B) (x : J.T ℓ) :
    homT (ℓ := ℓ) (precomp π f) x = homT f (homT π x) := by
  apply Subtype.ext; funext n
  change Additive.ofMul (Additive.toMul (x.1 n) ≫ π.hom ≫ f.hom) =
    Additive.ofMul ((Additive.toMul (x.1 n) ≫ π.hom) ≫ f.hom)
  rw [Category.assoc]

lemma tateHomZl_precomp {J A B : AbVar K} (π : Hom J A) (z : ℤ_[ℓ] ⊗[ℤ] Hom A B) (x : J.T ℓ) :
    tateHomZl ℓ J B ((precomp π).lTensor ℤ_[ℓ] z) x = tateHomZl ℓ A B z (homT π x) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a f =>
    simp only [LinearMap.lTensor_tmul]
    change (a • tateHom ℓ J B (precomp π f)) x = (a • tateHom ℓ A B f) (homT π x)
    simp only [LinearMap.smul_apply]
    exact congrArg (a • ·) (homT_comp ℓ π f x)
  | add y z hy hz => simp only [map_add, LinearMap.add_apply, hy, hz]

lemma homVK_galRep {J A : AbVar K} (π : Hom J A) (σ : Field.absoluteGaloisGroup K) :
    homVK ℓ π ∘ₗ J.galRep ℓ σ = A.galRep ℓ σ ∘ₗ homVK ℓ π := by
  have h1 : homT (ℓ := ℓ) π ∘ₗ J.galT σ = A.galT σ ∘ₗ homT π :=
    LinearMap.ext fun t => homT_galT π σ t
  change (homT π).baseChange ℚ_[ℓ] ∘ₗ (J.galT σ).baseChange ℚ_[ℓ] =
    (A.galT σ).baseChange ℚ_[ℓ] ∘ₗ (homT π).baseChange ℚ_[ℓ]
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, h1]

/-- Complement of a subrepresentation, as `IsCompl` of submodules. -/
lemma isCompl_toSubmodule {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
    {ρ : Representation k G V} {W W' : Subrepresentation ρ} (h : IsCompl W W') :
    IsCompl W.toSubmodule W'.toSubmodule := by
  constructor
  · rw [disjoint_iff]
    have := congrArg Subrepresentation.toSubmodule h.inf_eq_bot
    simp only [Subrepresentation.toSubmodule_inf] at this
    exact this
  · rw [codisjoint_iff]
    have := congrArg Subrepresentation.toSubmodule h.sup_eq_top
    simp only [Subrepresentation.toSubmodule_sup] at this
    exact this

/-- **`VSurjOfSurjective` over a number field (GLUE, proved from Faltings' Satz 3 and Satz 4 and
`TateModuleFree`).** If `π : J → A` is a homomorphism of abelian varieties over a number field
whose underlying morphism of schemes is surjective, then `V_ℓ(π) : V_ℓ(J) → V_ℓ(A)` is surjective.

Proof: the image `R` is `G_K`-stable; by semisimplicity it has an invariant complement `R'`. The
projection `p` onto `R'` is equivariant and kills `R`. Clearing denominators, `s • p` comes from an
equivariant `h : T_ℓ A → T_ℓ A`, which by Faltings is `tateHomZl z`, `z ∈ ℤ_ℓ ⊗ End(A)`. Since
`h ∘ T_ℓ(π) = 0`, injectivity of `tateHomZl` on `Hom(J, A)` and flatness of `ℤ_ℓ` over `ℤ` give
`z = 0` (precomposition with `π` is injective because `A` is reduced and `π` is dominant).
So `p = 0` and `R' = 0`. -/
theorem homVK_surjective (hS : FaltingsSemisimple) (hF : FaltingsTate) (hT : TateModuleFree)
    [NumberField K] (J A : AbVar K) (π : Hom J A) (hπ : Surjective π.hom.left) :
    Function.Surjective (homVK ℓ π) := by
  classical
  have hℓK : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨hfreeA, hfinA, -⟩ := hT K A ℓ hℓK
  have : Module.FinitePresentation ℤ_[ℓ] (A.T ℓ) := Module.finitePresentation_of_finite _ _
  -- the image as a subrepresentation
  let R : Subrepresentation (A.galRep ℓ) :=
    { toSubmodule := LinearMap.range (homVK ℓ π)
      apply_mem_toSubmodule := by
        rintro σ _ ⟨w, rfl⟩
        exact ⟨J.galRep ℓ σ w, LinearMap.congr_fun (homVK_galRep ℓ π σ) w⟩ }
  obtain ⟨R', hR'⟩ := (hS K A ℓ).exists_isCompl R
  have hc := isCompl_toSubmodule hR'.symm
  -- if `R' = 0` we are done
  suffices hR'0 : R'.toSubmodule = ⊥ by
    have htop : R.toSubmodule = ⊤ := by
      have := hc.symm.sup_eq_top
      rwa [hR'0, sup_bot_eq] at this
    intro v
    have : v ∈ R.toSubmodule := htop ▸ Submodule.mem_top
    exact this
  by_contra hne
  -- the projection onto `R'` along `R`
  set p : A.V ℓ →ₗ[ℚ_[ℓ]] A.V ℓ := R'.toSubmodule.projection R.toSubmodule hc with hpdef
  have hpeq : ∀ σ, p ∘ₗ A.galRep ℓ σ = A.galRep ℓ σ ∘ₗ p :=
    GlueI3.projection_comm R' R hc
  have hpR : ∀ w, p (homVK ℓ π w) = 0 := fun w =>
    Submodule.projection_apply_of_mem_right hc ⟨w, rfl⟩
  obtain ⟨r, hrR', hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hpr : p r = r := Submodule.projection_apply_of_mem_left hc hrR'
  -- lattice clearing (as in `PkgI3.exists_hom_ne_zero_of_equivariant`)
  let ιA : A.T ℓ →ₗ[ℤ_[ℓ]] A.V ℓ := TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (A.T ℓ) 1
  let ιJ : J.T ℓ →ₗ[ℤ_[ℓ]] J.V ℓ := TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (J.T ℓ) 1
  have : IsLocalizedModule (nonZeroDivisors ℤ_[ℓ]) ιA := inferInstance
  obtain ⟨h, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    (nonZeroDivisors ℤ_[ℓ]) ιA ((p.restrictScalars ℤ_[ℓ]) ∘ₗ ιA)
  have hs0 : (s : ℤ_[ℓ]) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hιA : Function.Injective ιA := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[ℓ]) ιA).mp hy
    exact (smul_eq_zero.mp ht).resolve_left (nonZeroDivisors.ne_zero t.2)
  have hιAσ : ∀ σ x, ιA (A.galT σ x) = A.galRep ℓ σ (ιA x) := fun σ x => by
    simp [ιA, galRep, LinearMap.baseChange_tmul]
  have hsp : ∀ x, ιA (h x) = (s : ℤ_[ℓ]) • p (ιA x) := fun x => by
    have := congrArg (fun g => g x) hs
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
      LinearMap.coe_restrictScalars, Submonoid.smul_def] at this
    exact this
  have hheq : IsGalEquivariant h := by
    intro σ x
    apply hιA
    rw [hsp, hιAσ, hιAσ, hsp]
    have := congrArg (fun g => g (ιA x)) (hpeq σ)
    simp only [LinearMap.coe_comp, Function.comp_apply] at this
    rw [this, LinearMap.map_smul_of_tower]
  -- `h ∘ T_ℓ(π) = 0`
  have hhπ : ∀ x, h (homT π x) = 0 := fun x => by
    apply hιA
    rw [hsp, map_zero]
    have : ιA (homT π x) = homVK ℓ π (ιJ x) := by
      simp [ιA, ιJ, homVK, LinearMap.baseChange_tmul]
    rw [this, hpR, smul_zero]
  -- Faltings: `h = tateHomZl z`
  obtain ⟨z, hz⟩ : h ∈ Set.range (tateHomZl ℓ A A) := by
    rw [(hF K A A ℓ).2]; exact hheq
  have hz0 : (precomp π).lTensor ℤ_[ℓ] z = 0 := by
    apply (hF K J A ℓ).1
    rw [map_zero]
    apply LinearMap.ext; intro x
    rw [tateHomZl_precomp, hz, hhπ, LinearMap.zero_apply]
  have hinj : Function.Injective ((precomp (B := A) π).lTensor ℤ_[ℓ]) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (precomp_injective π hπ)
  have hz' : z = 0 := hinj (by rw [hz0, map_zero])
  have hh0 : h = 0 := by rw [← hz, hz', map_zero]
  -- hence `p = 0`, contradicting `p r = r ≠ 0`
  have hpι : ∀ x, p (ιA x) = 0 := fun x => by
    have h1 : (s : ℤ_[ℓ]) • p (ιA x) = 0 := by rw [← hsp, hh0]; simp
    rw [← algebraMap_smul ℚ_[ℓ] (s : ℤ_[ℓ])] at h1
    exact (smul_eq_zero.mp h1).resolve_left (by
      simpa using (IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ]).ne hs0)
  have hp0 : ∀ v, p v = 0 := fun v => by
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul q x =>
      have : (q ⊗ₜ[ℤ_[ℓ]] x : A.V ℓ) = q • ιA x := by simp [ιA, TensorProduct.smul_tmul']
      rw [this, map_smul, hpι, smul_zero]
    | add v w hv hw => rw [map_add, hv, hw, add_zero]
  exact hr0 (by rw [← hpr, hp0])

end VSurj

/-- **`LeafModCurves.VSurjOfSurjective` (the glue target of leaf-modcurves), proved.** -/
theorem vSurjOfSurjective (hS : FaltingsSemisimple) (hF : FaltingsTate) (hT : TateModuleFree) :
    LeafModCurves.VSurjOfSurjective := by
  intro J A π ℓ _ hπ
  exact homVK_surjective ℓ hS hF hT J A π hπ

/-! ## §2. Equivariant sections out of a semisimple representation -/

section Section

variable {k G V W : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W]

/-- A surjective equivariant map `q : V → W` out of a semisimple representation restricts to an
equivariant isomorphism from a subrepresentation of `V` onto `W` (an invariant complement of
`ker q`). -/
theorem exists_subrep_equiv_of_surjective (ρ : Representation k G V) (σ : Representation k G W)
    (hss : ρ.IsSemisimpleRepresentation) (q : V →ₗ[k] W) (hq : Function.Surjective q)
    (hqeq : ∀ g v, q (ρ g v) = σ g (q v)) :
    ∃ (U : Subrepresentation ρ) (e : U.toSubmodule ≃ₗ[k] W),
      ∀ g (u : U.toSubmodule), e ⟨ρ g u, U.apply_mem_toSubmodule g u.2⟩ = σ g (e u) := by
  let Kr : Subrepresentation ρ :=
    { toSubmodule := LinearMap.ker q
      apply_mem_toSubmodule := fun g v hv => by
        rw [LinearMap.mem_ker] at hv ⊢; rw [hqeq, hv, map_zero] }
  obtain ⟨U, hU⟩ := hss.exists_isCompl Kr
  have hc : IsCompl Kr.toSubmodule U.toSubmodule := isCompl_toSubmodule hU
  have hbij : Function.Bijective (q ∘ₗ U.toSubmodule.subtype) := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro u hu
      have hK : (u : V) ∈ Kr.toSubmodule := hu
      exact Subtype.ext ((Submodule.disjoint_def.mp hc.disjoint) u hK u.2)
    · intro w
      obtain ⟨v, rfl⟩ := hq w
      have hv : v ∈ Kr.toSubmodule ⊔ U.toSubmodule := by rw [hc.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
      have ha' : q a = 0 := ha
      exact ⟨⟨b, hb⟩, by simp [ha']⟩
  refine ⟨U, LinearEquiv.ofBijective _ hbij, fun g u => ?_⟩
  simp [LinearEquiv.ofBijective_apply, hqeq]

end Section

/-- Base change of a surjective linear map is surjective. -/
lemma baseChange_surjective {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (E : Type*) [CommRing E] [Algebra R E] (f : M →ₗ[R] N)
    (hf : Function.Surjective f) : Function.Surjective (f.baseChange E) := by
  intro y
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul e n =>
    obtain ⟨m, rfl⟩ := hf n
    exact ⟨e ⊗ₜ m, by simp⟩
  | add y z hy hz =>
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨b, rfl⟩ := hz
    exact ⟨a + b, map_add _ _ _⟩

/-! ## §3. `ρ_{f,ι}` is a subrepresentation of `V_ℓ(J) ⊗ ℚ̄_ℓ` (over `G_ℚ`) -/

section RhoSub

open LeafModCurves
open PkgI4 (GQ)

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Evaluation of the `ι`-eigenfunctionals: `V_ℓ(A) → (eigenFun)^∨`, `v ↦ (φ ↦ φ v)`. -/
def evalEig (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0) (emb : F →+* PadicAlgCl ℓ) :
    A.V ℓ →ₗ[ℚ_[ℓ]] Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) where
  toFun v :=
    { toFun := fun φ => (φ : A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ) v
      map_add' := fun φ ψ => rfl
      map_smul' := fun c φ => rfl }
  map_add' v w := by ext φ; simp
  map_smul' c v := by ext φ; simp

/-- Its `ℚ̄_ℓ`-linear extension `V_ℓ(A) ⊗ ℚ̄_ℓ → (eigenFun)^∨`. -/
def evalEigE (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0) (emb : F →+* PadicAlgCl ℓ) :
    TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ) →ₗ[PadicAlgCl ℓ]
      Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) :=
  (evalEig ℓ A θ emb).liftBaseChange (PadicAlgCl ℓ)

theorem evalEigE_equivariant (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0)
    (emb : F →+* PadicAlgCl ℓ) (σ : GQ) (x : TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)) :
    evalEigE ℓ A θ emb (GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ) σ x) =
      rhoF ℓ A θ emb σ (evalEigE ℓ A θ emb x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e v =>
    change evalEigE ℓ A θ emb ((A.galRep ℓ σ).baseChange (PadicAlgCl ℓ) (e ⊗ₜ v)) = _
    rw [LinearMap.baseChange_tmul]
    simp only [evalEigE, LinearMap.liftBaseChange_tmul, map_smul]
    congr 1
  | add x y hx hy => simp only [map_add, hx, hy]

theorem evalEigE_surjective (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0)
    (emb : F →+* PadicAlgCl ℓ) [FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)] :
    Function.Surjective (evalEigE ℓ A θ emb) := by
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne)
    inferInstance
  set w := (Module.evalEquiv (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)).symm f
  have hfw : ∀ g, f g = g w := fun g => by
    have : f = Module.evalEquiv (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) w := by simp [w]
    rw [this]; rfl
  have hv : ∀ v, (w : A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ) v = 0 := fun v => by
    have hx : evalEigE ℓ A θ emb (1 ⊗ₜ v) ∈ LinearMap.range (evalEigE ℓ A θ emb) := ⟨_, rfl⟩
    have := Submodule.mem_map_of_mem (f := f) hx
    rw [hf, Submodule.mem_bot, hfw] at this
    simp only [evalEigE, LinearMap.liftBaseChange_tmul, one_smul] at this
    exact this
  have hw0 : w = 0 := Subtype.ext (LinearMap.ext hv)
  apply hf0
  ext g
  rw [hfw, hw0, map_zero]; rfl

/-- **`ρ_{f,ι}` as a subrepresentation (GLUE, proved).** If `V_ℓ(π) : V_ℓ(J) → V_ℓ(A)` is
surjective, the representation `rhoF ℓ A θ ι` of `G_ℚ` on `(eigenFun)^∨` is equivariantly
isomorphic to a subrepresentation of `V_ℓ(J) ⊗ ℚ̄_ℓ` (Faltings' semisimplicity of `V_ℓ(J)`,
kept under extension of scalars by `GlueI3.semisimpleBaseChange`). -/
theorem rhoF_subrep_of_surj (hS : FaltingsSemisimple) (hT : TateModuleFree) (J A : AbVar ℚ)
    (π : Hom J A) (hπ : Function.Surjective (homV ℓ π)) {F : Type} [Field F]
    (θ : F →+* A.End0) (emb : F →+* PadicAlgCl ℓ)
    [FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)] :
    ∃ (U : Subrepresentation (GlueI3.repBaseChange (PadicAlgCl ℓ) (J.galRep ℓ)))
      (e : U.toSubmodule ≃ₗ[PadicAlgCl ℓ] Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)),
      ∀ g (u : U.toSubmodule),
        e ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (J.galRep ℓ) g u, U.apply_mem_toSubmodule g u.2⟩ =
          rhoF ℓ A θ emb g (e u) := by
  have hℓ : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨-, hfin, -⟩ := hT ℚ J ℓ hℓ
  have : FiniteDimensional ℚ_[ℓ] (J.V ℓ) := inferInstance
  have hss := GlueI3.semisimpleBaseChange ℚ_[ℓ] (PadicAlgCl ℓ) _ _ (J.galRep ℓ) (hS ℚ J ℓ)
  refine exists_subrep_equiv_of_surjective _ (rhoF ℓ A θ emb) hss
    (evalEigE ℓ A θ emb ∘ₗ (homV ℓ π).baseChange (PadicAlgCl ℓ))
    ((evalEigE_surjective ℓ A θ emb).comp (baseChange_surjective _ _ hπ)) ?_
  intro g v
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [← evalEigE_equivariant]
  congr 1
  change ((homV ℓ π).baseChange _ ∘ₗ (J.galRep ℓ g).baseChange _) v =
    ((A.galRep ℓ g).baseChange _ ∘ₗ (homV ℓ π).baseChange _) v
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, homV_galRep]

end RhoSub

end E1Sub
