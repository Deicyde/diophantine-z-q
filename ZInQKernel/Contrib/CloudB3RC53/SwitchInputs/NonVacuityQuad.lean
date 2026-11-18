import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.NonVacuity

/-!
# RC53 SwitchInputs: non-vacuity of the quadratic Selmer switch steps

LESSON 2 (model non-vacuity) for the two models of `Plug.lean` that `NonVacuity.lean` leaves
uninhabited: `SelmerQuadMixedStep` and `SelmerQuadSingleStep` (tex L5003–5136), together with the
`SelmerQuadSwitch` they contain, now with genuinely nontrivial involutions.

The local data are `J₀ = diag(1, −1)` over `ℚ`, `e₊ = (1, 0)`, `e₋ = (0, 1)`, and the local
involution `(x, y) ↦ (J₀x, −J₀y)` on `F ⊕ S`. The Selmer models are concentrated in degree one; the
involutions on cohomology are induced by chain involutions of the Selmer data (`supportMap` of an
involutive change of data, identity on the global part, `J₀` on `F`, `−J₀` on `S` and on the full
local complex), so every compatibility of `SelmerQuadSwitch` is a degree-one identity on cocycles.

* `exQuadMixedStep : SelmerQuadMixedStep ℚ`: the relaxed model `exRel` of `NonVacuity.lean`
  (`U = F`), cohomology classes `c₊ = [(0, e₊)]`, `c₋ = [(0, e₋)]` of signs `+`, `−` with nonzero
  localizations.
* `exQuadSingleStep : SelmerQuadSingleStep ℚ`: a second relaxed model whose full local complex
  records the `e₋`-coordinates of both planes, so that `U = F(e₊) ⊕ S(e₊)`; there the finite-side
  cohomology `V = H¹(C(U_F))` is two-dimensional and all of sign `+`.

The general tool is the class map `cls : ker d¹ → H¹` with its naturality (`H1_cls`), surjectivity,
and, when the degree-zero term vanishes, injectivity. Classification: PROVED (non-vacuity).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory Matrix Module ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Uniform.QuadraticCase
  ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

/-! ### Classes of degree-one cocycles -/

section Cls

variable (K : CochainComplex (ModuleCat.{0} ℚ) ℤ)

theorem next_one : (ComplexShape.up ℤ).next 1 = 2 := by simp

/-- The cycles of degree one, from the kernel of `d¹`. -/
def liftK : ModuleCat.of ℚ (LinearMap.ker (K.d 1 2).hom) ⟶ K.cycles 1 :=
  K.liftCycles (ModuleCat.ofHom (LinearMap.ker (K.d 1 2).hom).subtype) 2 (next_one) (by
    ext x; exact x.2)

theorem iCycles_liftK (x : LinearMap.ker (K.d 1 2).hom) :
    (K.iCycles 1).hom ((liftK K).hom x) = x := by
  have := congrArg (fun f => ModuleCat.Hom.hom f x) (K.liftCycles_i
    (ModuleCat.ofHom (LinearMap.ker (K.d 1 2).hom).subtype) 2 (next_one) (by ext x; exact x.2))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  exact this

/-- **The class map** `ker d¹ → H¹`. -/
def clsL : LinearMap.ker (K.d 1 2).hom →ₗ[ℚ] K.homology 1 :=
  (K.homologyπ 1).hom ∘ₗ (liftK K).hom

theorem iCycles_injective : Function.Injective (K.iCycles 1).hom :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

theorem clsL_surjective : Function.Surjective (clsL K) := by
  intro v
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ 1)).mp inferInstance v
  have hc : (K.iCycles 1).hom c ∈ LinearMap.ker (K.d 1 2).hom := by
    have := congrArg (fun f => ModuleCat.Hom.hom f c) (K.iCycles_d 1 2)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero] at this
    exact LinearMap.mem_ker.mpr this
  refine ⟨⟨_, hc⟩, ?_⟩
  change (K.homologyπ 1).hom ((liftK K).hom ⟨_, hc⟩) = _
  congr 1
  apply iCycles_injective
  rw [iCycles_liftK]

theorem clsL_injective (h0 : Subsingleton (K.X 0)) : Function.Injective (clsL K) := by
  have h01 : K.d 0 1 = 0 := by ext x; rw [Subsingleton.elim x 0, map_zero]; rfl
  intro x y hxy
  have hπ : Function.Injective (K.homologyπ 1).hom := by
    have : IsIso (K.homologyπ 1) := ⟨⟨(K.isoHomologyπ 0 1 (by simp) h01).inv, by simp, by simp⟩⟩
    exact (ModuleCat.mono_iff_injective _).mp inferInstance
  have h := hπ hxy
  apply Subtype.ext
  rw [← iCycles_liftK K x, ← iCycles_liftK K y, h]

/-- **Naturality of classes**: `H¹(f) [x] = [f x]`. -/
theorem H1_cls {A B : GCx ℚ} (f : GHom A B) (x : LinearMap.ker (A.toCC.d 1 2).hom)
    (hx : ((GHom.toCC f).f 1).hom x.1 ∈ LinearMap.ker (B.toCC.d 1 2).hom) :
    H1 f (clsL A.toCC x) = clsL B.toCC ⟨_, hx⟩ := by
  change (HomologicalComplex.homologyMap (GHom.toCC f) 1).hom ((A.toCC.homologyπ 1).hom _) = _
  have hn := congrArg (fun g => ModuleCat.Hom.hom g ((liftK A.toCC).hom x))
    (HomologicalComplex.homologyπ_naturality (GHom.toCC f) 1)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hn
  rw [hn]
  change (B.toCC.homologyπ 1).hom _ = (B.toCC.homologyπ 1).hom ((liftK B.toCC).hom ⟨_, hx⟩)
  congr 1
  apply iCycles_injective
  have hi := congrArg (fun g => ModuleCat.Hom.hom g ((liftK A.toCC).hom x))
    (HomologicalComplex.cyclesMap_i (GHom.toCC f) 1)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hi
  rw [hi, iCycles_liftK, iCycles_liftK]

/-- The image of a cocycle under a chain map is a cocycle. -/
theorem map_mem_ker {A B : GCx ℚ} (f : GHom A B) (x : LinearMap.ker (A.toCC.d 1 2).hom) :
    ((GHom.toCC f).f 1).hom x.1 ∈ LinearMap.ker (B.toCC.d 1 2).hom := by
  have h := congrArg (fun g => ModuleCat.Hom.hom g x.1) ((GHom.toCC f).comm 1 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  refine LinearMap.mem_ker.mpr ?_
  rw [h, LinearMap.mem_ker.mp x.2, map_zero]

theorem H1_cls' {A B : GCx ℚ} (f : GHom A B) (x : LinearMap.ker (A.toCC.d 1 2).hom) :
    H1 f (clsL A.toCC x) = clsL B.toCC ⟨_, map_mem_ker f x⟩ :=
  H1_cls f x _

/-- Two chain maps agreeing on degree-one cocycles induce the same map on `H¹`. -/
theorem H1_congr {A B : GCx ℚ} (f g : GHom A B)
    (h : ∀ x : LinearMap.ker (A.toCC.d 1 2).hom, f.f 1 1 rfl x.1 = g.f 1 1 rfl x.1) :
    H1 f = H1 g := by
  ext v
  obtain ⟨x, rfl⟩ := clsL_surjective A.toCC v
  rw [H1_cls', H1_cls']
  congr 1
  exact Subtype.ext (by exact h x)

/-- `H¹` of a composite. -/
theorem H1_comp {A B C : GCx ℚ} (f : GHom A B) (g : GHom B C) :
    H1 g ∘ₗ H1 f = H1 (ghomComp f g) := by
  ext v
  obtain ⟨x, rfl⟩ := clsL_surjective A.toCC v
  simp only [LinearMap.comp_apply]
  rw [H1_cls', H1_cls', H1_cls']
  rfl

/-- A chain map that is the identity on degree-one cocycles is the identity on `H¹`. -/
theorem H1_eq_id {A : GCx ℚ} (f : GHom A A)
    (h : ∀ x : LinearMap.ker (A.toCC.d 1 2).hom, f.f 1 1 rfl x.1 = x.1) :
    H1 f = LinearMap.id := by
  ext v
  obtain ⟨x, rfl⟩ := clsL_surjective A.toCC v
  rw [H1_cls', LinearMap.id_apply]
  congr 1
  exact Subtype.ext (by exact h x)

/-- `h1Equiv` of a class is the cocycle itself. -/
theorem h1Equiv_cls {W : GCx ℚ} (hW : ConcDegOne W) (x : LinearMap.ker (W.toCC.d 1 2).hom) :
    h1Equiv W hW (clsL W.toCC x) = x.1 := by
  rw [h1Equiv_apply]
  have := congrArg (fun f => ModuleCat.Hom.hom f ((liftK W.toCC).hom x)) (homologyπ_h1Iso W hW)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  change (h1Iso W hW).hom.hom ((W.toCC.homologyπ 1).hom ((liftK W.toCC).hom x)) = x.1
  rw [this, iCycles_liftK]

end Cls

/-! ### The local involutions -/

section Flip

/-- `diag(1, −1, −1, …)` on `ℚ^m`: on `ℚ²` it is `J₀`. -/
def flipM (m : ℕ) : (Fin m → ℚ) →ₗ[ℚ] (Fin m → ℚ) :=
  Matrix.toLin' (Matrix.diagonal fun i => if i.val = 0 then 1 else -1)

theorem flipM_apply (m : ℕ) (v : Fin m → ℚ) (i : Fin m) :
    flipM m v i = (if i.val = 0 then 1 else -1) * v i := by
  simp [flipM, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

theorem flipM_flipM (m : ℕ) (v : Fin m → ℚ) : flipM m (flipM m v) = v := by
  ext i; rw [flipM_apply, flipM_apply]; split_ifs <;> ring

theorem flipM_zero (m : ℕ) : flipM m 0 = 0 := map_zero _

theorem negflip_negflip (m : ℕ) (v : Fin m → ℚ) : (-flipM m) ((-flipM m) v) = v := by
  rw [LinearMap.neg_apply, LinearMap.neg_apply, map_neg, neg_neg, flipM_flipM]

theorem eqvA_flip (x : Fin (dimAt 2 1) → ℚ) : eqvA 2 (flipM _ x) = J₀L (eqvA 2 x) := by
  ext j
  fin_cases j <;>
    simp [eqvA, flipM_apply, J₀L, J₀, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]

theorem eqvA_negflip (x : Fin (dimAt 2 1) → ℚ) :
    eqvA 2 ((-flipM _) x) = -J₀L (eqvA 2 x) := by
  rw [LinearMap.neg_apply, map_neg, eqvA_flip]

theorem eqvA_flip_eq_self {x : Fin (dimAt 2 1) → ℚ} (hx : J₀L (eqvA 2 x) = eqvA 2 x) :
    flipM _ x = x :=
  (eqvA 2).injective (by rw [eqvA_flip, hx])

theorem eqvA_flip_eq_neg {x : Fin (dimAt 2 1) → ℚ} (hx : J₀L (eqvA 2 x) = -eqvA 2 x) :
    flipM _ x = -x :=
  (eqvA 2).injective (by rw [eqvA_flip, hx, map_neg])

end Flip

/-! ### The mixed-sign example: `U = F` -/

section Mixed

/-- `ℚ^{dimAt 2 n}`. -/
abbrev V2 (n : ℤ) : Type := Fin (dimAt 2 n) → ℚ

/-- `ℚ^{dimAt 1 n}`. -/
abbrev V1 (n : ℤ) : Type := Fin (dimAt 1 n) → ℚ

theorem zero_apply' {M N : Type} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    (x : M) : (0 : M →ₗ[ℚ] N) x = 0 := rfl

/-- The involution of the relaxed data: identity on `G`, `(x, y) ↦ (J₀x, −J₀y)` on `U = F ⊕ S`,
`−J₀` on the full local complex `L = S`. -/
def selRelT : SupportChangeData ℚ where
  D := exRelD
  Dp := exRelD
  g := zHom fun _ => LinearMap.id
  lam := zHom fun n => -flipM (dimAt 2 n)
  mu := zHom fun n => (flipM (dimAt 2 n)).prodMap (-flipM (dimAt 2 n))
  r := zHom fun _ => 0
  hres i j h a := by
    subst h
    change (0 : V1 i →ₗ[ℚ] V2 i) a =
      (-flipM (dimAt 2 i)) ((0 : V1 i →ₗ[ℚ] V2 i) a) +
        LinearMap.snd ℚ (V2 i) (V2 i) ((0 : V1 i →ₗ[ℚ] V2 i × V2 i) a)
    erw [zero_apply']; simp
  hι i j h u := by
    subst h
    change LinearMap.snd ℚ (V2 i) (V2 i) (((flipM (dimAt 2 i)).prodMap (-flipM (dimAt 2 i))) u) =
      (-flipM (dimAt 2 i)) (LinearMap.snd ℚ (V2 i) (V2 i) u)
    rfl

/-- The involution of the finite side `C(U_F)`: `J₀` on `U_F = F`. -/
def selFT : SupportChangeData ℚ where
  D := exSideF.Dside
  Dp := exSideF.Dside
  g := zHom fun _ => LinearMap.id
  lam := zHom fun n => -flipM (dimAt 2 n)
  mu := zHom fun n => flipM (dimAt 2 n)
  r := zHom fun _ => 0
  hres i j h a := by
    subst h
    change (0 : V1 i →ₗ[ℚ] V2 i) a =
      (-flipM (dimAt 2 i)) ((0 : V1 i →ₗ[ℚ] V2 i) a) +
        LinearMap.snd ℚ (V2 i) (V2 i) (LinearMap.inl ℚ (V2 i) (V2 i) ((0 : V1 i →ₗ[ℚ] V2 i) a))
    erw [zero_apply']; simp
  hι i j h u := by
    subst h
    change LinearMap.snd ℚ (V2 i) (V2 i) (LinearMap.inl ℚ (V2 i) (V2 i) (flipM (dimAt 2 i) u)) =
      (-flipM (dimAt 2 i)) (LinearMap.snd ℚ (V2 i) (V2 i) (LinearMap.inl ℚ (V2 i) (V2 i) u))
    simp

/-- The involution of the singular side `C(U_S)`: `−J₀` on `U_S = S`. -/
def selST : SupportChangeData ℚ where
  D := exSideS.Dside
  Dp := exSideS.Dside
  g := zHom fun _ => LinearMap.id
  lam := zHom fun n => -flipM (dimAt 2 n)
  mu := zHom fun n => -flipM (dimAt 2 n)
  r := zHom fun _ => 0
  hres i j h a := by
    subst h
    change (0 : V1 i →ₗ[ℚ] V2 i) a =
      (-flipM (dimAt 2 i)) ((0 : V1 i →ₗ[ℚ] V2 i) a) +
        LinearMap.snd ℚ (V2 i) (V2 i) (LinearMap.inr ℚ (V2 i) (V2 i) ((0 : V1 i →ₗ[ℚ] V2 i) a))
    erw [zero_apply']; simp
  hι i j h u := by
    subst h
    change LinearMap.snd ℚ (V2 i) (V2 i) (LinearMap.inr ℚ (V2 i) (V2 i) ((-flipM (dimAt 2 i)) u)) =
      (-flipM (dimAt 2 i)) (LinearMap.snd ℚ (V2 i) (V2 i) (LinearMap.inr ℚ (V2 i) (V2 i) u))
    rfl

theorem pm_pm (u : V2 1 × V2 1) :
    ((flipM (dimAt 2 1)).prodMap (-flipM (dimAt 2 1)))
      (((flipM (dimAt 2 1)).prodMap (-flipM (dimAt 2 1))) u) = u := by
  rw [LinearMap.prodMap_apply, LinearMap.prodMap_apply]
  exact Prod.ext (flipM_flipM _ _) (negflip_negflip _ _)

/-- The sign involution on `H¹(C_rel)`. -/
def σrA : (selCx exRelD).toCC.homology 1 →ₗ[ℚ] (selCx exRelD).toCC.homology 1 :=
  H1 (supportMap selRelT)

/-- The sign involution on `V = H¹(C(U_F))`. -/
def σVA : (selCx exSideF.Dside).toCC.homology 1 →ₗ[ℚ] (selCx exSideF.Dside).toCC.homology 1 :=
  H1 (supportMap selFT)

/-- The sign involution on `V' = H¹(C(U_S))`. -/
def σV'A : (selCx exSideS.Dside).toCC.homology 1 →ₗ[ℚ] (selCx exSideS.Dside).toCC.homology 1 :=
  H1 (supportMap selST)

theorem σrA_sq : σrA ∘ₗ σrA = LinearMap.id := by
  refine (H1_comp _ _).trans (H1_eq_id _ fun x => ?_)
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  change (a, ((flipM _).prodMap (-flipM _)) (((flipM _).prodMap (-flipM _)) u + (0 : V1 1 →ₗ[ℚ] V2 1 × V2 1) a) +
      (0 : V1 1 →ₗ[ℚ] V2 1 × V2 1) a, (-flipM (dimAt 2 0)) ((-flipM (dimAt 2 0)) l)) = (a, u, l)
  erw [zero_apply']
  rw [add_zero, add_zero]
  refine Prod.ext rfl (Prod.ext ?_ (negflip_negflip _ l))
  exact pm_pm u

theorem σVA_sq : σVA ∘ₗ σVA = LinearMap.id := by
  refine (H1_comp _ _).trans (H1_eq_id _ fun x => ?_)
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  change (a, flipM _ (flipM _ u + (0 : V1 1 →ₗ[ℚ] V2 1) a) + (0 : V1 1 →ₗ[ℚ] V2 1) a,
      (-flipM (dimAt 2 0)) ((-flipM (dimAt 2 0)) l)) = (a, u, l)
  erw [zero_apply']
  refine Prod.ext rfl (Prod.ext ?_ (negflip_negflip _ l))
  rw [add_zero, add_zero]
  exact flipM_flipM _ u

theorem σV'A_sq : σV'A ∘ₗ σV'A = LinearMap.id := by
  refine (H1_comp _ _).trans (H1_eq_id _ fun x => ?_)
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  change (a, (-flipM _) ((-flipM _) u + (0 : V1 1 →ₗ[ℚ] V2 1) a) + (0 : V1 1 →ₗ[ℚ] V2 1) a,
      (-flipM (dimAt 2 0)) ((-flipM (dimAt 2 0)) l)) = (a, u, l)
  erw [zero_apply']
  refine Prod.ext rfl (Prod.ext ?_ (negflip_negflip _ l))
  rw [add_zero, add_zero]
  exact negflip_negflip _ u


theorem βF_clsA (x : LinearMap.ker ((selCx exSideF.Dside).toCC.d 1 2).hom) :
    exSideF.βF (clsL _ x) = eqvA 2 x.1.2.1 := by
  unfold SwitchSide.βF
  rw [LinearMap.comp_apply]
  erw [H1_cls']
  rw [LinearEquiv.coe_coe, LinearEquiv.trans_apply, h1Equiv_cls]
  rfl

theorem lam_clsA (x : LinearMap.ker ((selCx exRelD).toCC.d 1 2).hom) :
    exRel.lam (clsL _ x) = (eqvA 2 x.1.2.1.1, eqvA 2 x.1.2.1.2) := by
  unfold RelaxedLocalization.lam
  rw [LinearMap.comp_apply]
  erw [H1_cls']
  rw [LinearEquiv.coe_coe, LinearEquiv.trans_apply, h1Equiv_cls]
  rfl

theorem fixFA : σVA ∘ₗ H1 (changeMap exSideF.Dside exSideF.fs) =
    H1 (changeMap exSideF.Dside exSideF.fs) := by
  unfold σVA
  refine (H1_comp _ _).trans (H1_congr _ _ fun x => ?_)
  obtain ⟨⟨a, s, l⟩, hx⟩ := x
  have hs : s = 0 := Subsingleton.elim (α := Fin 0 → ℚ) _ _
  subst hs
  refine Prod.ext rfl (Prod.ext ?_ ((subsingleton_dimAt 2 (n := 1 - 1) (by norm_num)).elim _ _))
  change flipM _ ((0 : (Fin 0 → ℚ) →ₗ[ℚ] V2 1) 0) + (0 : V1 1 →ₗ[ℚ] V2 1) a =
    (0 : (Fin 0 → ℚ) →ₗ[ℚ] V2 1) 0
  simp only [map_zero, zero_add]
  rfl

theorem fixSA : σV'A ∘ₗ H1 (changeMap exSideS.Dside exSideS.fs) =
    H1 (changeMap exSideS.Dside exSideS.fs) := by
  unfold σV'A
  refine (H1_comp _ _).trans (H1_congr _ _ fun x => ?_)
  obtain ⟨⟨a, s, l⟩, hx⟩ := x
  have hs : s = 0 := Subsingleton.elim (α := Fin 0 → ℚ) _ _
  subst hs
  refine Prod.ext rfl (Prod.ext ?_ ((subsingleton_dimAt 2 (n := 1 - 1) (by norm_num)).elim _ _))
  change (-flipM _) ((0 : (Fin 0 → ℚ) →ₗ[ℚ] V2 1) 0) + (0 : V1 1 →ₗ[ℚ] V2 1) a =
    (0 : (Fin 0 → ℚ) →ₗ[ℚ] V2 1) 0
  simp only [map_zero, zero_add]
  rfl

theorem γFA : H1 (changeMap exRelD exSideF.f₁) ∘ₗ σVA =
    σrA ∘ₗ H1 (changeMap exRelD exSideF.f₁) := by
  unfold σVA σrA
  refine (H1_comp _ _).trans ((H1_congr _ _ fun x => ?_).trans (H1_comp _ _).symm)
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  change LinearMap.inl ℚ (V2 1) (V2 1) (flipM _ u + (0 : V1 1 →ₗ[ℚ] V2 1) a) =
    ((flipM _).prodMap (-flipM _)) (LinearMap.inl ℚ (V2 1) (V2 1) u) +
      (0 : V1 1 →ₗ[ℚ] V2 1 × V2 1) a
  refine Prod.ext rfl ?_
  change (0 : V2 1) = -flipM _ 0 + 0
  simp

theorem γSA : H1 (changeMap exRelD exSideS.f₁) ∘ₗ σV'A =
    σrA ∘ₗ H1 (changeMap exRelD exSideS.f₁) := by
  unfold σV'A σrA
  refine (H1_comp _ _).trans ((H1_congr _ _ fun x => ?_).trans (H1_comp _ _).symm)
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  change LinearMap.inr ℚ (V2 1) (V2 1) ((-flipM _) u + (0 : V1 1 →ₗ[ℚ] V2 1) a) =
    ((flipM _).prodMap (-flipM _)) (LinearMap.inr ℚ (V2 1) (V2 1) u) +
      (0 : V1 1 →ₗ[ℚ] V2 1 × V2 1) a
  refine Prod.ext ?_ rfl
  change (0 : V2 1) = flipM _ 0 + 0
  simp

theorem βFA_equiv : exSideF.βF ∘ₗ σVA = J₀L ∘ₗ exSideF.βF := by
  ext1 v
  obtain ⟨x, rfl⟩ := clsL_surjective _ v
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  unfold σVA
  erw [H1_cls']
  rw [βF_clsA, βF_clsA]
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  change eqvA 2 (flipM _ u + (0 : V1 1 →ₗ[ℚ] V2 1) a) = J₀L (eqvA 2 u)
  erw [zero_apply', add_zero]
  exact eqvA_flip u

theorem lamA_equiv : exRel.lam ∘ₗ σrA = localInv J₀L ∘ₗ exRel.lam := by
  ext1 v
  obtain ⟨x, rfl⟩ := clsL_surjective _ v
  change exRel.lam (H1 (supportMap selRelT) (clsL _ x)) = localInv J₀L (exRel.lam (clsL _ x))
  erw [H1_cls']
  rw [lam_clsA x, localInv_apply]
  refine (lam_clsA ⟨_, _⟩).trans ?_
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  change (eqvA 2 (((flipM _).prodMap (-flipM _)) u + (0 : V1 1 →ₗ[ℚ] V2 1 × V2 1) a).1,
      eqvA 2 (((flipM _).prodMap (-flipM _)) u + (0 : V1 1 →ₗ[ℚ] V2 1 × V2 1) a).2) =
    (J₀L (eqvA 2 u.1), -J₀L (eqvA 2 u.2))
  erw [zero_apply', add_zero]
  refine Prod.ext (eqvA_flip u.1) ?_
  change eqvA 2 (-(flipM _ u.2)) = -J₀L (eqvA 2 u.2)
  rw [map_neg]
  exact congrArg Neg.neg (eqvA_flip u.2)

/-- **`SelmerQuadSwitch` with genuine involutions** (`J = J₀`): `H¹(σ)` for the chain involutions
`selRelT`, `selFT`, `selST`, and the identity on the strict cohomology. -/
noncomputable def exQuadSwitchA : SelmerQuadSwitch ℚ J₀L where
  R := exRel
  SF := exSideF
  SS := exSideS
  fG := (inferInstance : FiniteDimensional ℚ (Fin (dimAt 1 1) → ℚ))
  fL := (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 0) → ℚ))
  fF := (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
  fS := (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
  eK := exSelmerQuadSwitch.eK
  σK := LinearMap.id
  σV := σVA
  σV' := σV'A
  σr := σrA
  hK := LinearMap.id_comp _
  hV := σVA_sq
  hV' := σV'A_sq
  hr := σrA_sq
  hα' := LinearMap.ext fun v => (LinearMap.congr_fun fixFA v).symm
  hβ' := βFA_equiv
  hγ' := γFA
  hα'' := LinearMap.ext fun v =>
    (LinearMap.congr_fun fixSA (exSelmerQuadSwitch.eK.symm v)).symm
  hβ'' := by
    ext1 v
    simp only [LinearMap.comp_apply, exSideS_βS_zero, map_zero]
  hγ'' := γSA
  hl := lamA_equiv


theorem J₀L_apply_zero (y : Fin 2 → ℚ) : J₀L y 0 = y 0 := by
  simp [J₀L, J₀, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem J₀L_apply_one (y : Fin 2 → ℚ) : J₀L y 1 = -y 1 := by
  simp [J₀L, J₀, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The finite plane is its own annihilator for the local pairing `β = e₂(·, J₀ ·)`. -/
theorem finPlane_lagrangian (u : (Fin 2 → ℚ) × (Fin 2 → ℚ)) :
    u ∈ finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ) ↔
      ∀ w ∈ finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ), localPair 1 J₀L u w = 0 := by
  constructor
  · intro hu w hw
    rw [mem_finPlane] at hu hw
    simp [localPair, crossPair, hu, hw]
  · intro h
    rw [mem_finPlane]
    have h1 := h (eP, 0) (mem_finPlane.mpr rfl)
    have h2 := h (eM, 0) (mem_finPlane.mpr rfl)
    simp only [localPair, crossPair, map_zero, e₂_apply, Pi.zero_apply, mul_zero, sub_zero,
      one_mul, zero_add, eP, eM] at h1 h2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, zero_mul,
      zero_sub, J₀L_apply_one, J₀L_apply_zero] at h1 h2
    ext i
    fin_cases i
    · simpa using h2
    · simpa using h1

theorem exSideF_mem_ker (c : (selCx exSideF.Dside).toCC.X 1) :
    c ∈ LinearMap.ker ((selCx exSideF.Dside).toCC.d 1 2).hom := by
  rw [LinearMap.mem_ker, exSideF_d12]
  rfl

/-- The class `[(0, u, 0)] ∈ V = H¹(C(U_F))`. -/
def clsF (u : V2 1) : (selCx exSideF.Dside).toCC.homology 1 :=
  clsL _ ⟨(show (selCx exSideF.Dside).toCC.X 1 from ((0 : V1 1), u, (0 : V2 (1 - 1)))),
    exSideF_mem_ker _⟩

theorem σVA_clsF (u : V2 1) : σVA (clsF u) = clsF (flipM _ u) := by
  unfold σVA clsF
  erw [H1_cls']
  congr 1
  apply Subtype.ext
  change ((0 : V1 1), flipM _ u + (0 : V1 1 →ₗ[ℚ] V2 1) 0, (-flipM (dimAt 2 0)) 0) =
    ((0 : V1 1), flipM _ u, (0 : V2 (1 - 1)))
  simp

theorem clsF_neg (u : V2 1) : clsF (-u) = -clsF u := by
  unfold clsF
  rw [← map_neg]
  congr 1

theorem locA_clsF (u : V2 1) :
    (exRel.lam ∘ₗ H1 (changeMap exRel.D exSideF.f₁)) (clsF u) = (eqvA 2 u, 0) := by
  change exRel.lam (H1 (changeMap exRelD exSideF.f₁) (clsF u)) = _
  unfold clsF
  erw [H1_cls']
  refine (lam_clsA ⟨_, _⟩).trans ?_
  change (eqvA 2 (LinearMap.inl ℚ (V2 1) (V2 1) u).1, eqvA 2 (LinearMap.inl ℚ (V2 1) (V2 1) u).2) = _
  simp

/-- `u₊ = e₊`, `u₋ = e₋` in `ℚ^{dimAt 2 1}`. -/
def uP : V2 1 := (eqvA 2).symm eP

def uM : V2 1 := (eqvA 2).symm eM

theorem flip_uP : flipM _ uP = uP :=
  eqvA_flip_eq_self (by simp only [uP, LinearEquiv.apply_symm_apply]; exact J₀L_eP)

theorem flip_uM : flipM _ uM = -uM :=
  eqvA_flip_eq_neg (by simp only [uM, LinearEquiv.apply_symm_apply]; exact J₀L_eM)

/-- **`SelmerQuadMixedStep` is inhabited** (tex L5003–5122): the relaxed model `exRel`
(`U = F`, Lagrangian), the genuine sign involutions of `exQuadSwitchA`, and the classes
`c₊ = [(0, e₊)]` of sign `+` and `c₋ = [(0, e₋)]` of sign `−`, whose localizations `(e±, 0)` are
nonzero. -/
noncomputable def exQuadMixedStep : SelmerQuadMixedStep ℚ where
  h2 := two_ne_zero_ℚ
  ε := 1
  hε := one_ne_zero
  J := J₀L
  hJ2 := J₀L_sq
  ep := eP
  em := eM
  hp := J₀L_eP
  hm := J₀L_eM
  he := e₂_eP_eM_ne
  X := exQuadSwitchA
  hU u := by
    change u ∈ exRel.U ↔ ∀ w ∈ exRel.U, localPair 1 J₀L u w = 0
    rw [exRel_U]
    exact finPlane_lagrangian u
  cp := clsF uP
  cm := clsF uM
  hcp := by change σVA (clsF uP) = clsF uP; rw [σVA_clsF, flip_uP]
  hcm := by change σVA (clsF uM) = -clsF uM; rw [σVA_clsF, flip_uM, clsF_neg]
  hdet _ _ := by
    change (exRel.lam ∘ₗ H1 (changeMap exRel.D exSideF.f₁)) (clsF uP) ≠ 0 ∧
      (exRel.lam ∘ₗ H1 (changeMap exRel.D exSideF.f₁)) (clsF uM) ≠ 0
    rw [locA_clsF, locA_clsF]
    simp only [uP, uM, LinearEquiv.apply_symm_apply]
    exact ⟨pair_ne_zero eP_ne, pair_ne_zero eM_ne⟩


end Mixed

/-! ### The single-sign example: `U = F(e₊) ⊕ S(e₊)` -/

section Single

/-- The projection onto the coordinates of index `≥ 1` (on `ℚ²`: the `e₋`-coordinate). -/
def antiM (m : ℕ) : (Fin m → ℚ) →ₗ[ℚ] (Fin m → ℚ) :=
  Matrix.toLin' (Matrix.diagonal fun i => if i.val = 0 then 0 else 1)

theorem antiM_apply (m : ℕ) (v : Fin m → ℚ) (i : Fin m) :
    antiM m v i = (if i.val = 0 then 0 else 1) * v i := by
  simp [antiM, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

theorem antiM_flipM (m : ℕ) (v : Fin m → ℚ) : antiM m (flipM m v) = -antiM m v := by
  ext i; simp only [antiM_apply, flipM_apply, Pi.neg_apply]; split_ifs <;> ring

theorem flipM_antiM (m : ℕ) (v : Fin m → ℚ) : flipM m (antiM m v) = -antiM m v := by
  ext i; simp only [antiM_apply, flipM_apply, Pi.neg_apply]; split_ifs <;> ring

theorem flipM_eq_self_of_anti (m : ℕ) {v : Fin m → ℚ} (h : antiM m v = 0) : flipM m v = v := by
  ext i
  have hi := congrFun h i
  simp only [antiM_apply, Pi.zero_apply] at hi
  simp only [flipM_apply]
  split_ifs with h0
  · ring
  · simp only [h0, ite_false, one_mul] at hi; rw [hi]; ring

theorem antiM_eq_zero_of_flip (m : ℕ) {v : Fin m → ℚ} (h : flipM m v = v) : antiM m v = 0 := by
  ext i
  have hi := congrFun h i
  simp only [flipM_apply] at hi
  simp only [antiM_apply, Pi.zero_apply]
  split_ifs with h0
  · ring
  · simp only [h0, ite_false] at hi; linarith

/-- `(x, y) ↦ (anti x, anti y)` on `F ⊕ S`. -/
abbrev antiQ (n : ℤ) : V2 n × V2 n →ₗ[ℚ] V2 n × V2 n := (antiM (dimAt 2 n)).prodMap (antiM (dimAt 2 n))

/-- **The relaxed Selmer data of the single-sign example**: `G = ℚ` (`res = 0`), `U_rel = F ⊕ S`,
the full local complex `L = F ⊕ S` with `ι(x, y) = (anti x, anti y)`, all in degree one. Relaxed
cocycles have `anti x = anti y = 0`, so `U = F(e₊) ⊕ S(e₊)`. -/
def exRelDB : SelData ℚ where
  G := zGCx (Pn 1)
  U := zGCx Qn
  L := zGCx Qn
  res := zHom fun _ => 0
  ι := zHom fun n => antiQ n

def exRelB : RelaxedLocalization ℚ where
  D := exRelDB
  Wrel := zGCx Qn
  gR := zHom fun _ => LinearMap.id
  eR := (eqvA 2).prodCongr (eqvA 2)
  hWrel := concDegOne_Qn

/-- The finite side: `U_F = F` (`f₁ = inl`), `W₂ = S` (`g₂ = snd`), `U_str = 0`, `W₁ = F`. -/
def exSideFB : SwitchSide exRelB (finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ)) where
  U₁ := zGCx (Pn 2)
  Ustr := zGCx Zn
  W₁ := zGCx (Pn 2)
  W₂ := zGCx (Pn 2)
  f₁ := zHom fun _ => LinearMap.inl ℚ _ _
  g₂ := zHom fun _ => LinearMap.snd ℚ _ _
  fs := zHom fun _ => 0
  g₁ := zHom fun _ => LinearMap.id
  i := zHom fun _ => LinearMap.inl ℚ _ _
  p := zHom fun _ => LinearMap.snd ℚ _ _
  hfg₂ _ _ := rfl
  f₁_inj _ := LinearMap.inl_injective
  g₂_surj _ := LinearMap.snd_surjective
  ex₂ _ u h := ⟨u.1, Prod.ext rfl h.symm⟩
  hfg₁ _ _ := by change (0 : Fin _ → ℚ) = 0; rfl
  fs_inj _ := fun _ _ _ => Subsingleton.elim _ _
  g₁_surj _ := Function.surjective_id
  ex₁ _ u h := ⟨0, by change (0 : Fin _ → ℚ) = u; exact h.symm⟩
  hRF _ _ := rfl
  hpR _ _ := rfl
  hW₁ := concDegOne_Pn 2
  hW₂ := concDegOne_Pn 2
  i_inj := LinearMap.inl_injective
  ip_exact y := ⟨fun h => ⟨y.1, Prod.ext rfl h.symm⟩, fun ⟨x, hx⟩ => by rw [← hx]; rfl⟩
  hP := by
    ext z
    simp only [LinearMap.mem_range, LinearMap.coe_comp, Function.comp_apply, mem_finPlane]
    constructor
    · rintro ⟨x, rfl⟩
      change (eqvA 2) 0 = 0
      exact map_zero _
    · intro hz
      refine ⟨(eqvA 2).symm z.1, Prod.ext ?_ ?_⟩
      · change (eqvA 2) ((eqvA 2).symm z.1) = z.1
        exact LinearEquiv.apply_symm_apply _ _
      · change (eqvA 2) 0 = z.2
        rw [map_zero, hz]

/-- The singular side: `U_S = S` (`f₁ = inr`), `W₂ = F` (`g₂ = fst`), `U_str = 0`, `W₁ = S`. -/
def exSideSB : SwitchSide exRelB (singPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ)) where
  U₁ := zGCx (Pn 2)
  Ustr := zGCx Zn
  W₁ := zGCx (Pn 2)
  W₂ := zGCx (Pn 2)
  f₁ := zHom fun _ => LinearMap.inr ℚ _ _
  g₂ := zHom fun _ => LinearMap.fst ℚ _ _
  fs := zHom fun _ => 0
  g₁ := zHom fun _ => LinearMap.id
  i := zHom fun _ => LinearMap.inr ℚ _ _
  p := zHom fun _ => LinearMap.fst ℚ _ _
  hfg₂ _ _ := rfl
  f₁_inj _ := LinearMap.inr_injective
  g₂_surj _ := LinearMap.fst_surjective
  ex₂ _ u h := ⟨u.2, Prod.ext h.symm rfl⟩
  hfg₁ _ _ := by change (0 : Fin _ → ℚ) = 0; rfl
  fs_inj _ := fun _ _ _ => Subsingleton.elim _ _
  g₁_surj _ := Function.surjective_id
  ex₁ _ u h := ⟨0, by change (0 : Fin _ → ℚ) = u; exact h.symm⟩
  hRF _ _ := rfl
  hpR _ _ := rfl
  hW₁ := concDegOne_Pn 2
  hW₂ := concDegOne_Pn 2
  i_inj := LinearMap.inr_injective
  ip_exact y := ⟨fun h => ⟨y.2, Prod.ext h.symm rfl⟩, fun ⟨x, hx⟩ => by rw [← hx]; rfl⟩
  hP := by
    ext z
    simp only [LinearMap.mem_range, LinearMap.coe_comp, Function.comp_apply, mem_singPlane]
    constructor
    · rintro ⟨x, rfl⟩
      change (eqvA 2) 0 = 0
      exact map_zero _
    · intro hz
      refine ⟨(eqvA 2).symm z.2, Prod.ext ?_ ?_⟩
      · change (eqvA 2) 0 = z.1
        rw [map_zero, hz]
      · change (eqvA 2) ((eqvA 2).symm z.2) = z.2
        exact LinearEquiv.apply_symm_apply _ _


/-- `(x, y) ↦ (J₀x, −J₀y)` on `F ⊕ S` in every degree. -/
abbrev pmQ (n : ℤ) : V2 n × V2 n →ₗ[ℚ] V2 n × V2 n := (flipM (dimAt 2 n)).prodMap (-flipM (dimAt 2 n))

theorem antiQ_pmQ (n : ℤ) (u : V2 n × V2 n) : antiQ n (pmQ n u) = pmQ n (antiQ n u) := by
  refine Prod.ext ?_ ?_
  · change antiM _ (flipM _ u.1) = flipM _ (antiM _ u.1)
    rw [antiM_flipM, flipM_antiM]
  · change antiM _ (-flipM _ u.2) = -flipM _ (antiM _ u.2)
    rw [map_neg, antiM_flipM, flipM_antiM]

theorem pmQ_pmQ (n : ℤ) (u : V2 n × V2 n) : pmQ n (pmQ n u) = u :=
  Prod.ext (flipM_flipM _ _) (negflip_negflip _ _)

def selRelTB : SupportChangeData ℚ where
  D := exRelDB
  Dp := exRelDB
  g := zHom fun _ => LinearMap.id
  lam := zHom fun n => pmQ n
  mu := zHom fun n => pmQ n
  r := zHom fun _ => 0
  hres i j h a := by
    subst h
    change (0 : V1 i →ₗ[ℚ] V2 i × V2 i) a =
      pmQ i ((0 : V1 i →ₗ[ℚ] V2 i × V2 i) a) + antiQ i ((0 : V1 i →ₗ[ℚ] V2 i × V2 i) a)
    erw [zero_apply']; simp; try rfl
  hι i j h u := by
    subst h
    exact antiQ_pmQ i u

def selFTB : SupportChangeData ℚ where
  D := exSideFB.Dside
  Dp := exSideFB.Dside
  g := zHom fun _ => LinearMap.id
  lam := zHom fun n => pmQ n
  mu := zHom fun n => flipM (dimAt 2 n)
  r := zHom fun _ => 0
  hres i j h a := by
    subst h
    change (0 : V1 i →ₗ[ℚ] V2 i × V2 i) a =
      pmQ i ((0 : V1 i →ₗ[ℚ] V2 i × V2 i) a) +
        antiQ i (LinearMap.inl ℚ (V2 i) (V2 i) ((0 : V1 i →ₗ[ℚ] V2 i) a))
    erw [zero_apply']; simp; try rfl
  hι i j h u := by
    subst h
    change antiQ i (LinearMap.inl ℚ (V2 i) (V2 i) (flipM _ u)) =
      pmQ i (antiQ i (LinearMap.inl ℚ (V2 i) (V2 i) u))
    rw [← antiQ_pmQ]
    refine congrArg (antiQ i) (Prod.ext rfl ?_)
    change (0 : V2 i) = -flipM _ 0
    simp

def selSTB : SupportChangeData ℚ where
  D := exSideSB.Dside
  Dp := exSideSB.Dside
  g := zHom fun _ => LinearMap.id
  lam := zHom fun n => pmQ n
  mu := zHom fun n => -flipM (dimAt 2 n)
  r := zHom fun _ => 0
  hres i j h a := by
    subst h
    change (0 : V1 i →ₗ[ℚ] V2 i × V2 i) a =
      pmQ i ((0 : V1 i →ₗ[ℚ] V2 i × V2 i) a) +
        antiQ i (LinearMap.inr ℚ (V2 i) (V2 i) ((0 : V1 i →ₗ[ℚ] V2 i) a))
    erw [zero_apply']; simp; try rfl
  hι i j h u := by
    subst h
    change antiQ i (LinearMap.inr ℚ (V2 i) (V2 i) ((-flipM _) u)) =
      pmQ i (antiQ i (LinearMap.inr ℚ (V2 i) (V2 i) u))
    rw [← antiQ_pmQ]
    refine congrArg (antiQ i) (Prod.ext ?_ rfl)
    change (0 : V2 i) = flipM _ 0
    simp

def σrB : (selCx exRelDB).toCC.homology 1 →ₗ[ℚ] (selCx exRelDB).toCC.homology 1 :=
  H1 (supportMap selRelTB)

def σVB : (selCx exSideFB.Dside).toCC.homology 1 →ₗ[ℚ] (selCx exSideFB.Dside).toCC.homology 1 :=
  H1 (supportMap selFTB)

def σV'B : (selCx exSideSB.Dside).toCC.homology 1 →ₗ[ℚ] (selCx exSideSB.Dside).toCC.homology 1 :=
  H1 (supportMap selSTB)

theorem σrB_sq : σrB ∘ₗ σrB = LinearMap.id := by
  refine (H1_comp _ _).trans (H1_eq_id _ fun x => ?_)
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  change (a, pmQ 1 (pmQ 1 u + (0 : V1 1 →ₗ[ℚ] V2 1 × V2 1) a) + (0 : V1 1 →ₗ[ℚ] V2 1 × V2 1) a,
      pmQ (1 - 1) (pmQ (1 - 1) l)) = (a, u, l)
  erw [zero_apply']
  rw [add_zero, add_zero]
  exact Prod.ext rfl (Prod.ext (pmQ_pmQ 1 u) (pmQ_pmQ (1 - 1) l))

theorem σVB_sq : σVB ∘ₗ σVB = LinearMap.id := by
  refine (H1_comp _ _).trans (H1_eq_id _ fun x => ?_)
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  change (a, flipM _ (flipM _ u + (0 : V1 1 →ₗ[ℚ] V2 1) a) + (0 : V1 1 →ₗ[ℚ] V2 1) a,
      pmQ (1 - 1) (pmQ (1 - 1) l)) = (a, u, l)
  erw [zero_apply']
  rw [add_zero, add_zero]
  exact Prod.ext rfl (Prod.ext (flipM_flipM _ u) (pmQ_pmQ (1 - 1) l))

theorem σV'B_sq : σV'B ∘ₗ σV'B = LinearMap.id := by
  refine (H1_comp _ _).trans (H1_eq_id _ fun x => ?_)
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  change (a, (-flipM _) ((-flipM _) u + (0 : V1 1 →ₗ[ℚ] V2 1) a) + (0 : V1 1 →ₗ[ℚ] V2 1) a,
      pmQ (1 - 1) (pmQ (1 - 1) l)) = (a, u, l)
  erw [zero_apply']
  rw [add_zero, add_zero]
  exact Prod.ext rfl (Prod.ext (negflip_negflip _ u) (pmQ_pmQ (1 - 1) l))

theorem βF_clsB (x : LinearMap.ker ((selCx exSideFB.Dside).toCC.d 1 2).hom) :
    exSideFB.βF (clsL _ x) = eqvA 2 x.1.2.1 := by
  unfold SwitchSide.βF
  rw [LinearMap.comp_apply]
  erw [H1_cls']
  rw [LinearEquiv.coe_coe, LinearEquiv.trans_apply, h1Equiv_cls]
  rfl

theorem βS_clsB (x : LinearMap.ker ((selCx exSideSB.Dside).toCC.d 1 2).hom) :
    exSideSB.βS (clsL _ x) = eqvA 2 x.1.2.1 := by
  unfold SwitchSide.βS
  rw [LinearMap.comp_apply]
  erw [H1_cls']
  rw [LinearEquiv.coe_coe, LinearEquiv.trans_apply, h1Equiv_cls]
  rfl

theorem lam_clsB (x : LinearMap.ker ((selCx exRelDB).toCC.d 1 2).hom) :
    exRelB.lam (clsL _ x) = (eqvA 2 x.1.2.1.1, eqvA 2 x.1.2.1.2) := by
  unfold RelaxedLocalization.lam
  rw [LinearMap.comp_apply]
  erw [H1_cls']
  rw [LinearEquiv.coe_coe, LinearEquiv.trans_apply, h1Equiv_cls]
  rfl

theorem subsingleton_Q0 : Subsingleton (V2 (1 - 1) × V2 (1 - 1)) := by
  have := subsingleton_dimAt 2 (n := 1 - 1) (by norm_num)
  infer_instance

theorem fixFB : σVB ∘ₗ H1 (changeMap exSideFB.Dside exSideFB.fs) =
    H1 (changeMap exSideFB.Dside exSideFB.fs) := by
  unfold σVB
  refine (H1_comp _ _).trans (H1_congr _ _ fun x => ?_)
  obtain ⟨⟨a, s, l⟩, hx⟩ := x
  have hs : s = 0 := Subsingleton.elim (α := Fin 0 → ℚ) _ _
  subst hs
  refine Prod.ext rfl (Prod.ext ?_ (subsingleton_Q0.elim _ _))
  change flipM _ ((0 : (Fin 0 → ℚ) →ₗ[ℚ] V2 1) 0) + (0 : V1 1 →ₗ[ℚ] V2 1) a =
    (0 : (Fin 0 → ℚ) →ₗ[ℚ] V2 1) 0
  simp only [map_zero, zero_add]
  rfl

theorem fixSB : σV'B ∘ₗ H1 (changeMap exSideSB.Dside exSideSB.fs) =
    H1 (changeMap exSideSB.Dside exSideSB.fs) := by
  unfold σV'B
  refine (H1_comp _ _).trans (H1_congr _ _ fun x => ?_)
  obtain ⟨⟨a, s, l⟩, hx⟩ := x
  have hs : s = 0 := Subsingleton.elim (α := Fin 0 → ℚ) _ _
  subst hs
  refine Prod.ext rfl (Prod.ext ?_ (subsingleton_Q0.elim _ _))
  change (-flipM _) ((0 : (Fin 0 → ℚ) →ₗ[ℚ] V2 1) 0) + (0 : V1 1 →ₗ[ℚ] V2 1) a =
    (0 : (Fin 0 → ℚ) →ₗ[ℚ] V2 1) 0
  simp only [map_zero, zero_add]
  rfl

theorem γFB : H1 (changeMap exRelDB exSideFB.f₁) ∘ₗ σVB =
    σrB ∘ₗ H1 (changeMap exRelDB exSideFB.f₁) := by
  unfold σVB σrB
  refine (H1_comp _ _).trans ((H1_congr _ _ fun x => ?_).trans (H1_comp _ _).symm)
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  change LinearMap.inl ℚ (V2 1) (V2 1) (flipM _ u + (0 : V1 1 →ₗ[ℚ] V2 1) a) =
    pmQ 1 (LinearMap.inl ℚ (V2 1) (V2 1) u) + (0 : V1 1 →ₗ[ℚ] V2 1 × V2 1) a
  refine Prod.ext rfl ?_
  change (0 : V2 1) = -flipM _ 0 + 0
  simp

theorem γSB : H1 (changeMap exRelDB exSideSB.f₁) ∘ₗ σV'B =
    σrB ∘ₗ H1 (changeMap exRelDB exSideSB.f₁) := by
  unfold σV'B σrB
  refine (H1_comp _ _).trans ((H1_congr _ _ fun x => ?_).trans (H1_comp _ _).symm)
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  change LinearMap.inr ℚ (V2 1) (V2 1) ((-flipM _) u + (0 : V1 1 →ₗ[ℚ] V2 1) a) =
    pmQ 1 (LinearMap.inr ℚ (V2 1) (V2 1) u) + (0 : V1 1 →ₗ[ℚ] V2 1 × V2 1) a
  refine Prod.ext ?_ rfl
  change (0 : V2 1) = flipM _ 0 + 0
  simp

theorem βFB_equiv : exSideFB.βF ∘ₗ σVB = J₀L ∘ₗ exSideFB.βF := by
  ext1 v
  obtain ⟨x, rfl⟩ := clsL_surjective _ v
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  unfold σVB
  erw [H1_cls']
  rw [βF_clsB, βF_clsB]
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  change eqvA 2 (flipM _ u + (0 : V1 1 →ₗ[ℚ] V2 1) a) = J₀L (eqvA 2 u)
  erw [zero_apply', add_zero]
  exact eqvA_flip u

theorem βSB_equiv : exSideSB.βS ∘ₗ σV'B = (-J₀L) ∘ₗ exSideSB.βS := by
  ext1 v
  obtain ⟨x, rfl⟩ := clsL_surjective _ v
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  unfold σV'B
  erw [H1_cls']
  rw [βS_clsB, βS_clsB, LinearMap.neg_apply]
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  change eqvA 2 ((-flipM _) u + (0 : V1 1 →ₗ[ℚ] V2 1) a) = -J₀L (eqvA 2 u)
  erw [zero_apply', add_zero]
  exact eqvA_negflip u

theorem lamB_equiv : exRelB.lam ∘ₗ σrB = localInv J₀L ∘ₗ exRelB.lam := by
  ext1 v
  obtain ⟨x, rfl⟩ := clsL_surjective _ v
  change exRelB.lam (H1 (supportMap selRelTB) (clsL _ x)) = localInv J₀L (exRelB.lam (clsL _ x))
  erw [H1_cls']
  rw [lam_clsB x, localInv_apply]
  refine (lam_clsB ⟨_, _⟩).trans ?_
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  change (eqvA 2 (pmQ 1 u + (0 : V1 1 →ₗ[ℚ] V2 1 × V2 1) a).1,
      eqvA 2 (pmQ 1 u + (0 : V1 1 →ₗ[ℚ] V2 1 × V2 1) a).2) =
    (J₀L (eqvA 2 u.1), -J₀L (eqvA 2 u.2))
  erw [zero_apply', add_zero]
  refine Prod.ext (eqvA_flip u.1) ?_
  change eqvA 2 (-(flipM _ u.2)) = -J₀L (eqvA 2 u.2)
  rw [map_neg]
  exact congrArg Neg.neg (eqvA_flip u.2)

theorem strB_h0 : Subsingleton ((Fin (dimAt 1 0) → ℚ) × (Fin 0 → ℚ) ×
    (V2 (0 - 1) × V2 (0 - 1))) := by
  have := subsingleton_dimAt 1 (n := 0) (by norm_num)
  have := subsingleton_dimAt 2 (n := 0 - 1) (by norm_num)
  infer_instance

theorem exSideFB_str_d12 : (selCx exSideFB.Dstr).toCC.d 1 2 = 0 := by
  ext c
  erw [GCx.toCC_d_hom _ 1 2 rfl]
  obtain ⟨a, u, x⟩ := c
  have hu : u = 0 := Subsingleton.elim (α := Fin 0 → ℚ) _ _
  subst hu
  refine Prod.ext rfl (Prod.ext rfl ?_)
  change (0 : V1 1 →ₗ[ℚ] V2 1 × V2 1) a - antiQ 1 (LinearMap.inl ℚ (V2 1) (V2 1)
    ((0 : (Fin 0 → ℚ) →ₗ[ℚ] V2 1) 0)) - 0 = 0
  erw [zero_apply']
  simp

theorem exSideSB_str_d12 : (selCx exSideSB.Dstr).toCC.d 1 2 = 0 := by
  ext c
  erw [GCx.toCC_d_hom _ 1 2 rfl]
  obtain ⟨a, u, x⟩ := c
  have hu : u = 0 := Subsingleton.elim (α := Fin 0 → ℚ) _ _
  subst hu
  refine Prod.ext rfl (Prod.ext rfl ?_)
  change (0 : V1 1 →ₗ[ℚ] V2 1 × V2 1) a - antiQ 1 (LinearMap.inr ℚ (V2 1) (V2 1)
    ((0 : (Fin 0 → ℚ) →ₗ[ℚ] V2 1) 0)) - 0 = 0
  erw [zero_apply']
  simp

theorem strSB_h0 :
    Subsingleton (exSideSB.Dstr.G.X 0 × exSideSB.Dstr.U.X 0 × exSideSB.Dstr.L.X (0 - 1)) := by
  have := subsingleton_dimAt 1 (n := 0) (by norm_num)
  have := subsingleton_dimAt 2 (n := 0 - 1) (by norm_num)
  change Subsingleton ((Fin (dimAt 1 0) → ℚ) × (Fin 0 → ℚ) × (V2 (0 - 1) × V2 (0 - 1)))
  infer_instance

theorem strFB_h0 :
    Subsingleton (exSideFB.Dstr.G.X 0 × exSideFB.Dstr.U.X 0 × exSideFB.Dstr.L.X (0 - 1)) := by
  have := subsingleton_dimAt 1 (n := 0) (by norm_num)
  have := subsingleton_dimAt 2 (n := 0 - 1) (by norm_num)
  change Subsingleton ((Fin (dimAt 1 0) → ℚ) × (Fin 0 → ℚ) × (V2 (0 - 1) × V2 (0 - 1)))
  infer_instance

theorem strSB_d01 : (selCx exSideSB.Dstr).toCC.d 0 1 = 0 := selCx_d01_zero _ strSB_h0

theorem strFB_d01 : (selCx exSideFB.Dstr).toCC.d 0 1 = 0 := selCx_d01_zero _ strFB_h0

/-- The common degree-one strict cochain module `G¹ × 0 × L⁰`. -/
abbrev TstrB : Type := (Fin (dimAt 1 1) → ℚ) × (Fin 0 → ℚ) × (V2 (1 - 1) × V2 (1 - 1))

noncomputable def eStrSB : (selCx exSideSB.Dstr).toCC.homology 1 ≃ₗ[ℚ] TstrB :=
  (h1IsoOfZero _ strSB_d01 exSideSB_str_d12).toLinearEquiv

noncomputable def eStrFB : (selCx exSideFB.Dstr).toCC.homology 1 ≃ₗ[ℚ] TstrB :=
  (h1IsoOfZero _ strFB_d01 exSideFB_str_d12).toLinearEquiv

/-- The identification of the two strict cohomology groups of the single-sign model. -/
noncomputable def eKB : (selCx exSideSB.Dstr).toCC.homology 1 ≃ₗ[ℚ]
    (selCx exSideFB.Dstr).toCC.homology 1 :=
  eStrSB.trans eStrFB.symm

/-- **`SelmerQuadSwitch` for the single-sign model** (`J = J₀`, genuine involutions). -/
noncomputable def exQuadSwitchB : SelmerQuadSwitch ℚ J₀L where
  R := exRelB
  SF := exSideFB
  SS := exSideSB
  fG := (inferInstance : FiniteDimensional ℚ (Fin (dimAt 1 1) → ℚ))
  fL := (inferInstance : FiniteDimensional ℚ (V2 0 × V2 0))
  fF := (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
  fS := (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
  eK := eKB
  σK := LinearMap.id
  σV := σVB
  σV' := σV'B
  σr := σrB
  hK := LinearMap.id_comp _
  hV := σVB_sq
  hV' := σV'B_sq
  hr := σrB_sq
  hα' := LinearMap.ext fun v => (LinearMap.congr_fun fixFB v).symm
  hβ' := βFB_equiv
  hγ' := γFB
  hα'' := LinearMap.ext fun v => (LinearMap.congr_fun fixSB (eKB.symm v)).symm
  hβ'' := βSB_equiv
  hγ'' := γSB
  hl := lamB_equiv


theorem anti_of_eqF (u : V2 1)
    (h : (0 : V1 1 →ₗ[ℚ] V2 1 × V2 1) 0 - antiQ 1 (LinearMap.inl ℚ (V2 1) (V2 1) u) -
      (0 : V2 (1 - 1) × V2 (1 - 1) →ₗ[ℚ] V2 1 × V2 1) 0 = 0) : antiM _ u = 0 := by
  have := congrArg Prod.fst h
  simpa using this

theorem anti_of_eqR (u : V2 1 × V2 1)
    (h : (0 : V1 1 →ₗ[ℚ] V2 1 × V2 1) 0 - antiQ 1 u -
      (0 : V2 (1 - 1) × V2 (1 - 1) →ₗ[ℚ] V2 1 × V2 1) 0 = 0) : antiQ 1 u = 0 := by
  simpa using h

/-- The cocycle condition of the finite side of the single-sign model: `anti u = 0`. -/
theorem cycleFB (x : LinearMap.ker ((selCx exSideFB.Dside).toCC.d 1 2).hom) :
    antiM _ x.1.2.1 = 0 := by
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  have hd := LinearMap.mem_ker.mp hx
  erw [GCx.toCC_d_hom _ 1 2 rfl] at hd
  have h3 := congrArg (fun q => q.2.2) hd
  change (0 : V1 1 →ₗ[ℚ] V2 1 × V2 1) a - antiQ 1 (LinearMap.inl ℚ (V2 1) (V2 1) u) -
    (0 : V2 (1 - 1) × V2 (1 - 1) →ₗ[ℚ] V2 1 × V2 1) l = 0 at h3
  exact anti_of_eqF u h3

/-- The cocycle condition of the relaxed single-sign model: `anti x = anti y = 0`. -/
theorem cycleRB (x : LinearMap.ker ((selCx exRelDB).toCC.d 1 2).hom) :
    antiQ 1 x.1.2.1 = 0 := by
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  have hd := LinearMap.mem_ker.mp hx
  erw [GCx.toCC_d_hom _ 1 2 rfl] at hd
  have h3 := congrArg (fun q => q.2.2) hd
  change (0 : V1 1 →ₗ[ℚ] V2 1 × V2 1) a - antiQ 1 u -
    (0 : V2 (1 - 1) × V2 (1 - 1) →ₗ[ℚ] V2 1 × V2 1) l = 0 at h3
  exact anti_of_eqR u h3

theorem J₀L_fix_iff (z : Fin 2 → ℚ) : J₀L z = z ↔ z 1 = 0 := by
  constructor
  · intro h
    have := congrFun h 1
    rw [J₀L_apply_one] at this
    linarith
  · intro h
    ext i
    fin_cases i
    · exact J₀L_apply_zero z
    · simp only [Fin.mk_one, J₀L_apply_one, h, neg_zero]

theorem eqvA_one_of_anti {v : V2 1} (h : antiM _ v = 0) : eqvA 2 v 1 = 0 := by
  rw [← J₀L_fix_iff, ← eqvA_flip, flipM_eq_self_of_anti _ h]

theorem anti_of_eqvA_one {z : Fin 2 → ℚ} (h : z 1 = 0) : antiM _ ((eqvA 2).symm z) = 0 :=
  antiM_eq_zero_of_flip _ (eqvA_flip_eq_self (by
    rw [LinearEquiv.apply_symm_apply]; exact (J₀L_fix_iff z).mpr h))

/-- The relaxed cochain `(0, u, 0)`. -/
def mkRB (u : V2 1 × V2 1) : (selCx exRelDB).toCC.X 1 := ((0 : V1 1), u, (0 : V2 (1 - 1) × V2 (1 - 1)))

/-- **The relaxed image of the single-sign model** is `F(e₊) ⊕ S(e₊)`. -/
theorem exRelB_U_iff (z : (Fin 2 → ℚ) × (Fin 2 → ℚ)) : z ∈ exRelB.U ↔ z.1 1 = 0 ∧ z.2 1 = 0 := by
  rw [← RelaxedLocalization.range_lam]
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨x, rfl⟩ := clsL_surjective (selCx exRelDB).toCC v
    have hc := cycleRB x
    exact ⟨(congrArg (fun p => p.1 1) (lam_clsB x)).trans
        (eqvA_one_of_anti (congrArg Prod.fst hc)),
      (congrArg (fun p => p.2 1) (lam_clsB x)).trans (eqvA_one_of_anti (congrArg Prod.snd hc))⟩
  · rintro ⟨h1, h2⟩
    let u : V2 1 × V2 1 := ((eqvA 2).symm z.1, (eqvA 2).symm z.2)
    have hmem : mkRB u ∈ LinearMap.ker ((selCx exRelDB).toCC.d 1 2).hom := by
      refine LinearMap.mem_ker.mpr ?_
      erw [GCx.toCC_d_hom _ 1 2 rfl]
      refine Prod.ext rfl (Prod.ext rfl ?_)
      change (0 : V1 1 →ₗ[ℚ] V2 1 × V2 1) 0 - antiQ 1 u -
        (0 : V2 (1 - 1) × V2 (1 - 1) →ₗ[ℚ] V2 1 × V2 1) 0 = 0
      rw [map_zero, map_zero, zero_sub, sub_zero, neg_eq_zero]
      exact Prod.ext (anti_of_eqvA_one h1) (anti_of_eqvA_one h2)
    refine ⟨clsL (selCx exRelDB).toCC ⟨_, hmem⟩, (lam_clsB ⟨_, hmem⟩).trans ?_⟩
    exact Prod.ext (LinearEquiv.apply_symm_apply _ _) (LinearEquiv.apply_symm_apply _ _)

/-- `F(e₊) ⊕ S(e₊)` is Lagrangian for the local pairing. -/
theorem exRelB_lagrangian (u : (Fin 2 → ℚ) × (Fin 2 → ℚ)) :
    u ∈ exRelB.U ↔ ∀ w ∈ exRelB.U, localPair 1 J₀L u w = 0 := by
  have key : ∀ w : (Fin 2 → ℚ) × (Fin 2 → ℚ), w.1 1 = 0 → w.2 1 = 0 →
      localPair 1 J₀L u w = -(u.1 1 * w.2 0) - w.1 0 * u.2 1 := by
    intro w hw1 hw2
    simp only [localPair, crossPair, e₂_apply, J₀L_apply_zero, J₀L_apply_one, hw1, hw2]
    ring
  rw [exRelB_U_iff]
  constructor
  · rintro ⟨h1, h2⟩ w hw
    rw [exRelB_U_iff] at hw
    rw [key w hw.1 hw.2, h1, h2]
    ring
  · intro h
    have hA := h (![1, 0], 0) ((exRelB_U_iff _).mpr ⟨rfl, rfl⟩)
    have hB := h (0, ![1, 0]) ((exRelB_U_iff _).mpr ⟨rfl, rfl⟩)
    rw [key _ rfl rfl] at hA hB
    simp at hA hB
    exact ⟨hB, hA⟩

theorem exSideFB_X0 : Subsingleton ((selCx exSideFB.Dside).toCC.X 0) := by
  have := subsingleton_dimAt 1 (n := 0) (by norm_num)
  have := subsingleton_dimAt 2 (n := 0) (by norm_num)
  have := subsingleton_dimAt 2 (n := 0 - 1) (by norm_num)
  change Subsingleton ((Fin (dimAt 1 0) → ℚ) × V2 0 × (V2 (0 - 1) × V2 (0 - 1)))
  infer_instance

/-- A cocycle `(a, u, 0)` of the finite side with `anti u = 0`. -/
def cycFB (a : V1 1) (u : V2 1) (hu : antiM _ u = 0) :
    LinearMap.ker ((selCx exSideFB.Dside).toCC.d 1 2).hom :=
  ⟨((a, u, (0 : V2 (1 - 1) × V2 (1 - 1))) : (selCx exSideFB.Dside).toCC.X 1), by
    refine LinearMap.mem_ker.mpr ?_
    erw [GCx.toCC_d_hom _ 1 2 rfl]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    change (0 : V1 1 →ₗ[ℚ] V2 1 × V2 1) a - antiQ 1 (LinearMap.inl ℚ (V2 1) (V2 1) u) -
      (0 : V2 (1 - 1) × V2 (1 - 1) →ₗ[ℚ] V2 1 × V2 1) 0 = 0
    rw [LinearMap.zero_apply, LinearMap.zero_apply, zero_sub, sub_zero, neg_eq_zero]
    exact Prod.ext hu (map_zero (antiM (dimAt 2 1)))⟩

theorem anti_uP : antiM _ uP = 0 := antiM_eq_zero_of_flip _ flip_uP

/-- `σ` acts trivially on `V = H¹(C(U_F))` in the single-sign model (all classes have sign `+`). -/
theorem σVB_eq_id : σVB = LinearMap.id :=
  H1_eq_id _ fun x => by
    have hc := cycleFB x
    obtain ⟨⟨a, u, l⟩, hx⟩ := x
    change (a, flipM _ u + (0 : V1 1 →ₗ[ℚ] V2 1) a, pmQ (1 - 1) l) = (a, u, l)
    erw [zero_apply']
    rw [add_zero, flipM_eq_self_of_anti _ hc]
    exact Prod.ext rfl (Prod.ext rfl (subsingleton_Q0.elim _ _))

theorem locB_cycFB (a : V1 1) (u : V2 1) (hu : antiM _ u = 0) :
    (exRelB.lam ∘ₗ H1 (changeMap exRelB.D exSideFB.f₁)) (clsL _ (cycFB a u hu)) = (eqvA 2 u, 0) := by
  change exRelB.lam (H1 (changeMap exRelDB exSideFB.f₁) (clsL _ (cycFB a u hu))) = _
  erw [H1_cls']
  refine (lam_clsB ⟨_, _⟩).trans ?_
  change (eqvA 2 (LinearMap.inl ℚ (V2 1) (V2 1) u).1, eqvA 2 (LinearMap.inl ℚ (V2 1) (V2 1) u).2) = _
  simp

/-- `a₀ = 1 ∈ G¹ = ℚ`. -/
def a₀ : V1 1 := fun _ => 1

theorem two_le_finrank_VB : 2 ≤ finrank ℚ ((selCx exSideFB.Dside).toCC.homology 1) := by
  have : FiniteDimensional ℚ ((selCx exSideFB.Dside).toCC.homology 1) := exQuadSwitchB.fin_V
  have hli : LinearIndependent ℚ ![clsL _ (cycFB a₀ 0 (map_zero _)), clsL _ (cycFB 0 uP anti_uP)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [← map_smul, ← map_smul, ← map_add] at hst
    have h0 := clsL_injective _ exSideFB_X0 (hst.trans (map_zero _).symm)
    have h1 := congrArg (fun y => y.1) h0
    change ((s • a₀ + t • (0 : V1 1)), s • (0 : V2 1) + t • uP, _) = (0 : (selCx exSideFB.Dside).toCC.X 1) at h1
    have hs := congrFun (congrArg Prod.fst h1) ⟨0, by simp [dimAt]⟩
    have ht := congrArg (fun q => eqvA 2 q.2.1) h1
    simp only [a₀, smul_zero, add_zero, zero_add, Pi.smul_apply, smul_eq_mul, mul_one] at hs ht
    refine ⟨hs, ?_⟩
    rw [map_smul, uP, LinearEquiv.apply_symm_apply] at ht
    change t • eP = eqvA 2 0 at ht
    rw [map_zero] at ht
    have := congrFun ht 0
    simpa [eP] using this
  simpa using hli.fintype_card_le_finrank

/-- **`SelmerQuadSingleStep` is inhabited** (tex L5123–5136): the single-sign model with
`U = F(e₊) ⊕ S(e₊)` (Lagrangian), the genuine sign involutions of `exQuadSwitchB`, `V = H¹(C(U_F))`
two-dimensional of sign `+` only, and `c₊ = [(0, e₊)]` with nonzero localization `(e₊, 0)`. -/
noncomputable def exQuadSingleStep : SelmerQuadSingleStep ℚ where
  h2 := two_ne_zero_ℚ
  ε := 1
  hε := one_ne_zero
  J := J₀L
  hJ2 := J₀L_sq
  ep := eP
  em := eM
  hp := J₀L_eP
  hm := J₀L_eM
  he := e₂_eP_eM_ne
  X := exQuadSwitchB
  hU u := exRelB_lagrangian u
  cp := clsL _ (cycFB 0 uP anti_uP)
  hcp := by change σVB _ = _; rw [σVB_eq_id]; rfl
  hdet _ := by
    change (exRelB.lam ∘ₗ H1 (changeMap exRelB.D exSideFB.f₁)) (clsL _ (cycFB 0 uP anti_uP)) ≠ 0
    rw [locB_cycFB]
    simp only [uP, LinearEquiv.apply_symm_apply]
    exact pair_ne_zero eP_ne
  hs1 := by
    change 1 < finrank ℚ ↥(signPart σVB (1 : ℚ))
    have : signPart σVB (1 : ℚ) = ⊤ := by
      ext v; simp [mem_signPart, σVB_eq_id]
    rw [this, finrank_top]
    exact lt_of_lt_of_le (by norm_num) two_le_finrank_VB
  hs0 := by
    change 0 = finrank ℚ ↥(signPart σVB (-1 : ℚ))
    have : signPart σVB (-1 : ℚ) = ⊥ := by
      ext v
      simp only [mem_signPart, σVB_eq_id, LinearMap.id_apply, neg_smul, one_smul,
        Submodule.mem_bot]
      constructor
      · intro h
        have h2 : (2 : ℚ) • v = 0 := by rw [two_smul]; nth_rewrite 1 [h]; exact neg_add_cancel v
        exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
      · rintro rfl; simp
    rw [this, finrank_bot]


end Single

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
