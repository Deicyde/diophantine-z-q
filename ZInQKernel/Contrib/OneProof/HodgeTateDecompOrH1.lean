import ZInQKernel.Contrib.OneProof.HodgeTateDecompOr

/-!
# The Hodge–Tate decomposition: the `H¹_ét` shape implies the Hom shape; tensor ⇔ Hom

Task htdecomp-or (2026-11-17; report `docs/research/htdecomp-or.md`). A third shape in which the Hodge–Tate
decomposition is printed (Faltings, JAMS 1 (1988), for `H¹_ét`): `ℂ_p ⊗_{ℚ_p} H¹_ét(A_{F̄}, ℚ_p) ≅
(ℂ_p ⊗_F H¹(A, 𝒪_A)) ⊕ (ℂ_p(−1) ⊗_F H⁰(A, Ω¹))`, with `H¹_ét = V_p(A)^∨`. It implies the Hom form
`HodgeTateOr.HodgeTateDecompHom` (`ℂ_p ⊗ V^∨ = Hom_{ℚ_p}(V, ℂ_p)` once `V` is finite-dimensional, which the
`H¹` shape itself forces), hence the or-leaf `HodgeTateOr.HodgeTateDecompOr`. Not part of the leaf: it shows
that the or-leaf is also a consequence of an `H¹`-shaped print.

The last section proves the converse of `hodgeTateDecompExists_of_hom` (`hom_of_tensor`), so the two disjuncts of
the or-leaf are equivalent and the or-leaf is equivalent to the field it replaces (`or_iff_field`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option synthInstance.maxHeartbeats 400000

namespace ZInQ.Contrib.HodgeTateOr

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
open ZInQ.Contrib.HodgeTateFromPairing
open scoped TensorProduct

noncomputable section

/-- **Hodge–Tate decomposition, `H¹_ét` shape, bases chosen, dimensions not specified.** Faltings, *p-adic
Hodge theory*, J. Amer. Math. Soc. 1 (1988), 255–299 (Hodge–Tate decomposition of `H^n_ét`, `n = 1`), and
for abelian varieties Fontaine 1982; locators UNVERIFIED. Printed shape: `ℂ_p ⊗_{ℚ_p} H¹_ét(A_{F̄}, ℚ_p) ≅
(ℂ_p ⊗_F H¹(A, 𝒪_A)) ⊕ (ℂ_p(−1) ⊗_F H⁰(A, Ω¹_A))`, `G_F`-equivariant. Lean form: `H¹_ét = V_p(A)^∨ =
Module.Dual ℚ_p (V_p A)` with the contragredient action `φ ↦ φ ∘ ρ(σ⁻¹)`; bases of the two `F`-spaces chosen,
dimensions `a`, `b` unnamed. -/
def HodgeTateDecompH1 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F),
    ∃ (a b : ℕ) (e : ℂ_[p] ⊗[ℚ_[p]] Module.Dual ℚ_[p] (A.V p) ≃ₗ[ℂ_[p]] (Fin a → ℂ_[p]) × (Fin b → ℂ_[p])),
      ∀ (σ : Field.absoluteGaloisGroup F) (x : ℂ_[p] ⊗[ℚ_[p]] Module.Dual ℚ_[p] (A.V p)),
        e (TensorProduct.map (cpLin p (gfToGqp p F σ)) (A.galRep p σ⁻¹).dualMap x) =
          ((fun k => cpAct p (gfToGqp p F σ) ((e x).1 k)),
            (fun k => cycPow p (gfToGqp p F σ) (-1) • cpAct p (gfToGqp p F σ) ((e x).2 k)))

variable (p : ℕ) [Fact p.Prime]

section H1

variable {F : Type*} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
  (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)

/-- `c ⊗ φ ↦ (v ↦ c φ(v))`, `ℂ_p ⊗ V^∨ → Hom_{ℚ_p}(V, ℂ_p)`. -/
def theta : ℂ_[p] ⊗[ℚ_[p]] Module.Dual ℚ_[p] V →ₗ[ℂ_[p]] (V →ₗ[ℚ_[p]] ℂ_[p]) :=
  LinearMap.liftBaseChange ℂ_[p] (LinearMap.llcomp ℚ_[p] V ℚ_[p] ℂ_[p] (Algebra.linearMap ℚ_[p] ℂ_[p]))

theorem theta_tmul (c : ℂ_[p]) (φ : Module.Dual ℚ_[p] V) (v : V) :
    theta p (c ⊗ₜ φ) v = c * algebraMap ℚ_[p] ℂ_[p] (φ v) := by
  simp [theta, LinearMap.liftBaseChange_tmul]

theorem theta_injective [FiniteDimensional ℚ_[p] V] : Function.Injective (theta p (V := V)) := by
  classical
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro w hw
  rw [LinearMap.mem_ker] at hw
  rw [Submodule.mem_bot]
  let b := Basis.ofVectorSpace ℚ_[p] V
  let bD := b.dualBasis
  let bDC := bD.baseChange ℂ_[p]
  apply bDC.repr.injective
  ext i
  have hi : ∀ w' : ℂ_[p] ⊗[ℚ_[p]] Module.Dual ℚ_[p] V, bDC.repr w' i = theta p w' (b i) := by
    intro w'
    induction w' using TensorProduct.inductionOn with
    | tmul c φ =>
      rw [theta_tmul, Basis.baseChange_repr_tmul, Basis.dualBasis_repr]
      simp [Algebra.smul_def, mul_comm]
    | add x y hx hy => rw [map_add, Finsupp.add_apply, hx, hy, map_add, LinearMap.add_apply]
  rw [hi, hw]
  simp

theorem finrank_theta [FiniteDimensional ℚ_[p] V] :
    finrank ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] Module.Dual ℚ_[p] V) = finrank ℂ_[p] (V →ₗ[ℚ_[p]] ℂ_[p]) := by
  classical
  let b := Basis.ofVectorSpace ℚ_[p] V
  rw [Module.finrank_baseChange, Subspace.dual_finrank_eq, ← (b.constr ℂ_[p]).finrank_eq,
    Module.finrank_pi, Module.finrank_eq_card_basis b]

/-- `ℂ_p ⊗ V^∨ ≅ Hom_{ℚ_p}(V, ℂ_p)` for finite-dimensional `V`. -/
def thetaEquiv [FiniteDimensional ℚ_[p] V] :
    ℂ_[p] ⊗[ℚ_[p]] Module.Dual ℚ_[p] V ≃ₗ[ℂ_[p]] (V →ₗ[ℚ_[p]] ℂ_[p]) :=
  have : FiniteDimensional ℂ_[p] (V →ₗ[ℚ_[p]] ℂ_[p]) :=
    LinearEquiv.finiteDimensional ((Basis.ofVectorSpace ℚ_[p] V).constr ℂ_[p])
  LinearEquiv.ofBijective (theta p)
    ⟨theta_injective p,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (finrank_theta p)).mp (theta_injective p)⟩

theorem thetaEquiv_apply [FiniteDimensional ℚ_[p] V] (w : ℂ_[p] ⊗[ℚ_[p]] Module.Dual ℚ_[p] V) :
    thetaEquiv p w = theta p w := rfl

/-- `θ` is equivariant: `θ(σ ⊗ ρ^∨(σ)) = σ ∘ θ(·) ∘ ρ(σ)⁻¹`. -/
theorem theta_map (σ : Field.absoluteGaloisGroup F) (w : ℂ_[p] ⊗[ℚ_[p]] Module.Dual ℚ_[p] V) :
    theta p (TensorProduct.map (cpLin p (gfToGqp p F σ)) (ρ σ⁻¹).dualMap w) =
      cpLin p (gfToGqp p F σ) ∘ₗ theta p w ∘ₗ ρ σ⁻¹ := by
  induction w using TensorProduct.inductionOn with
  | tmul c φ =>
    ext v
    rw [TensorProduct.map_tmul, theta_tmul, LinearMap.comp_apply, LinearMap.comp_apply, theta_tmul,
      cpLin_apply, cpLin_apply, map_mul, cpAct_algebraMap, LinearMap.dualMap_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, LinearMap.add_comp, LinearMap.comp_add]

/-- The `H¹` shape forces `V` to be finite-dimensional. -/
theorem finiteDimensional_of_h1 {a b : ℕ}
    (e : ℂ_[p] ⊗[ℚ_[p]] Module.Dual ℚ_[p] V ≃ₗ[ℂ_[p]] (Fin a → ℂ_[p]) × (Fin b → ℂ_[p])) :
    FiniteDimensional ℚ_[p] V := by
  classical
  have : Module.Finite ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] Module.Dual ℚ_[p] V) := Module.Finite.equiv e.symm
  let bD := Basis.ofVectorSpace ℚ_[p] (Module.Dual ℚ_[p] V)
  have : Finite (Basis.ofVectorSpaceIndex ℚ_[p] (Module.Dual ℚ_[p] V)) :=
    Module.Finite.finite_basis (bD.baseChange ℂ_[p])
  have : Module.Finite ℚ_[p] (Module.Dual ℚ_[p] V) := Module.Finite.of_basis bD
  exact (Module.finite_dual_iff ℚ_[p]).mp this

end H1

/-- **The `H¹` shape implies the Hom shape.** -/
theorem hom_of_h1 (h : HodgeTateDecompH1) : HodgeTateDecompHom := by
  intro p _ F _ _ _ A
  obtain ⟨a, b, e, he⟩ := h p F A
  have := finiteDimensional_of_h1 p e
  refine ⟨a, b, (thetaEquiv p).symm.trans e, fun σ f => ?_⟩
  obtain ⟨w, rfl⟩ := (thetaEquiv p).surjective f
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [thetaEquiv_apply, ← theta_map p (A.galRep p), ← thetaEquiv_apply, LinearEquiv.symm_apply_apply, he]

/-- The or-leaf (and so the field) from an `H¹`-shaped print. -/
theorem or_of_h1 (h : HodgeTateDecompH1) : HodgeTateDecompOr := or_of_hom (hom_of_h1 h)

theorem hodgeTateDecompExists_of_h1 (h : HodgeTateDecompH1) : HodgeTateDecompExists :=
  hodgeTateDecompExists_of_hom (hom_of_h1 h)


/-! ## The converse: the tensor form implies the Hom form (so the two disjuncts are equivalent) -/

theorem cycPow_inv_one (σ : GQp p) : cycPow p σ⁻¹ 1 = cycPow p σ (-1) := by
  simp only [cycPow, cyc_inv, inv_zpow']

section Conv

variable {F : Type*} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
  (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
variable {a b : ℕ} (e : ℂ_[p] ⊗[ℚ_[p]] V ≃ₗ[ℂ_[p]] (Fin a → ℂ_[p]) × (Fin b → ℂ_[p]))

/-- `f ↦ (⟨f, e⁻¹(0, εₖ)⟩, ⟨f, e⁻¹(εₖ, 0)⟩)`. -/
def homMap : (V →ₗ[ℚ_[p]] ℂ_[p]) →ₗ[ℂ_[p]] (Fin b → ℂ_[p]) × (Fin a → ℂ_[p]) :=
  LinearMap.prod (LinearMap.pi fun k => LinearMap.applyₗ (R := ℂ_[p]) (e.symm (0, Pi.single k 1)) ∘ₗ
      (LinearMap.liftBaseChangeEquiv ℂ_[p]).toLinearMap)
    (LinearMap.pi fun k => LinearMap.applyₗ (R := ℂ_[p]) (e.symm (Pi.single k 1, 0)) ∘ₗ
      (LinearMap.liftBaseChangeEquiv ℂ_[p]).toLinearMap)

theorem homMap_fst (f : V →ₗ[ℚ_[p]] ℂ_[p]) (k : Fin b) :
    (homMap p e f).1 k = ev p f (e.symm (0, Pi.single k 1)) := rfl

theorem homMap_snd (f : V →ₗ[ℚ_[p]] ℂ_[p]) (k : Fin a) :
    (homMap p e f).2 k = ev p f (e.symm (Pi.single k 1, 0)) := rfl

theorem homMap_injective : Function.Injective (homMap p e) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro f hf
  rw [LinearMap.mem_ker] at hf
  rw [Submodule.mem_bot]
  have h0 : ev p f ∘ₗ e.symm.toLinearMap = 0 := by
    apply LinearMap.prod_ext
    · apply LinearMap.pi_ext
      intro k x
      have h1 : (Pi.single k x : Fin a → ℂ_[p]) = x • Pi.single k 1 := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      have h2 := congrArg (fun u => u.2 k) hf
      simp only [homMap_snd, Prod.snd_zero, Pi.zero_apply] at h2
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.inl_apply, h1,
        show ((x • Pi.single k 1 : Fin a → ℂ_[p]), (0 : Fin b → ℂ_[p])) = x • (Pi.single k 1, 0) by simp,
        LinearEquiv.coe_coe, map_smul, map_smul, h2, smul_zero, LinearMap.zero_comp, LinearMap.zero_apply]
    · apply LinearMap.pi_ext
      intro k x
      have h1 : (Pi.single k x : Fin b → ℂ_[p]) = x • Pi.single k 1 := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      have h2 := congrArg (fun u => u.1 k) hf
      simp only [homMap_fst, Prod.fst_zero, Pi.zero_apply] at h2
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.inr_apply, h1,
        show ((0 : Fin a → ℂ_[p]), (x • Pi.single k 1 : Fin b → ℂ_[p])) = x • (0, Pi.single k 1) by simp,
        LinearEquiv.coe_coe, map_smul, map_smul, h2, smul_zero, LinearMap.zero_comp, LinearMap.zero_apply]
  ext v
  have := LinearMap.congr_fun h0 (e (1 ⊗ₜ v))
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, ev_tmul, one_mul] at this
  rw [this]
  rfl

include e in
theorem finiteDimensional_of_tensor : FiniteDimensional ℚ_[p] V := by
  classical
  let bV := Basis.ofVectorSpace ℚ_[p] V
  have : Module.Finite ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] V) := Module.Finite.equiv e.symm
  have : Finite (Basis.ofVectorSpaceIndex ℚ_[p] V) := Module.Finite.finite_basis (bV.baseChange ℂ_[p])
  exact Module.Finite.of_basis bV

include e in
theorem finrank_eq_of_tensor : finrank ℂ_[p] (V →ₗ[ℚ_[p]] ℂ_[p]) =
    finrank ℂ_[p] ((Fin b → ℂ_[p]) × (Fin a → ℂ_[p])) := by
  have := finiteDimensional_of_tensor p e
  have h1 := (e.trans (LinearEquiv.prodComm ℂ_[p] _ _)).finrank_eq
  have h2 := (LinearMap.liftBaseChangeEquiv (R := ℚ_[p]) (M := V) (N := ℂ_[p]) ℂ_[p]).finrank_eq
  rw [h2, Subspace.dual_finrank_eq, h1]

/-- `Hom_{ℚ_p}(V, ℂ_p) ≅ ℂ_p^b × ℂ_p^a`. -/
def homEquiv : (V →ₗ[ℚ_[p]] ℂ_[p]) ≃ₗ[ℂ_[p]] (Fin b → ℂ_[p]) × (Fin a → ℂ_[p]) :=
  have := finiteDimensional_of_tensor p e
  have : FiniteDimensional ℂ_[p] (V →ₗ[ℚ_[p]] ℂ_[p]) :=
    LinearEquiv.finiteDimensional ((LinearMap.liftBaseChangeEquiv ℂ_[p]).symm)
  LinearEquiv.ofBijective (homMap p e)
    ⟨homMap_injective p e,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (finrank_eq_of_tensor p e)).mp
        (homMap_injective p e)⟩

theorem homEquiv_apply (f : V →ₗ[ℚ_[p]] ℂ_[p]) : homEquiv p e f = homMap p e f := rfl

/-- `⟨σ f, y⟩ = σ ⟨f, σ⁻¹ y⟩`. -/
theorem ev_act (σ : Field.absoluteGaloisGroup F) (f : V →ₗ[ℚ_[p]] ℂ_[p]) (y : ℂ_[p] ⊗[ℚ_[p]] V) :
    ev p (cpLin p (gfToGqp p F σ) ∘ₗ f ∘ₗ ρ σ⁻¹) y =
      cpAct p (gfToGqp p F σ) (ev p f (TensorProduct.map (cpLin p (gfToGqp p F σ⁻¹)) (ρ σ⁻¹) y)) := by
  induction y using TensorProduct.inductionOn with
  | tmul c v =>
    rw [TensorProduct.map_tmul, ev_tmul, ev_tmul, map_mul]
    simp only [LinearMap.comp_apply, cpLin_apply, map_inv, cpAct_inv_apply']
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add, map_add]

theorem homEquiv_map
    (he : ∀ (σ : Field.absoluteGaloisGroup F) (x : ℂ_[p] ⊗[ℚ_[p]] V),
      e (TensorProduct.map (cpLin p (gfToGqp p F σ)) (ρ σ) x) =
        ((fun k => cycPow p (gfToGqp p F σ) 1 • cpAct p (gfToGqp p F σ) ((e x).1 k)),
          (fun k => cpAct p (gfToGqp p F σ) ((e x).2 k))))
    (σ : Field.absoluteGaloisGroup F) (f : V →ₗ[ℚ_[p]] ℂ_[p]) :
    homEquiv p e (cpLin p (gfToGqp p F σ) ∘ₗ f ∘ₗ ρ σ⁻¹) =
      ((fun k => cpAct p (gfToGqp p F σ) ((homEquiv p e f).1 k)),
        (fun k => cycPow p (gfToGqp p F σ) (-1) • cpAct p (gfToGqp p F σ) ((homEquiv p e f).2 k))) := by
  rw [homEquiv_apply, homEquiv_apply]
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · dsimp only
    rw [homMap_fst, homMap_fst, ev_act p ρ]
    have hy : TensorProduct.map (cpLin p (gfToGqp p F σ⁻¹)) (ρ σ⁻¹) (e.symm (0, Pi.single k 1)) =
        e.symm (0, Pi.single k 1) := by
      apply e.injective
      rw [he, LinearEquiv.apply_symm_apply]
      refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
      · simp
      · exact congrFun (cpAct_single p _ k) j
    rw [hy]
  · dsimp only
    rw [homMap_snd, homMap_snd, ev_act p ρ]
    have hy : TensorProduct.map (cpLin p (gfToGqp p F σ⁻¹)) (ρ σ⁻¹) (e.symm (Pi.single k 1, 0)) =
        (algebraMap ℚ_[p] ℂ_[p] (cycPow p (gfToGqp p F σ) (-1))) • e.symm (Pi.single k 1, 0) := by
      apply e.injective
      rw [he, map_smul, LinearEquiv.apply_symm_apply, map_inv, cycPow_inv_one]
      refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
      · have := congrFun (cpAct_single p (gfToGqp p F σ)⁻¹ k) j
        simp only at this
        show cycPow p (gfToGqp p F σ) (-1) • cpAct p (gfToGqp p F σ)⁻¹ ((Pi.single k (1 : ℂ_[p]) : Fin a → ℂ_[p]) j) =
          algebraMap ℚ_[p] ℂ_[p] (cycPow p (gfToGqp p F σ) (-1)) * (Pi.single k (1 : ℂ_[p]) : Fin a → ℂ_[p]) j
        rw [this, Algebra.smul_def]
      · simp
    rw [hy, map_smul, smul_eq_mul, map_mul, cpAct_algebraMap, Algebra.smul_def]

end Conv

/-- **The tensor form implies the Hom form**: the two disjuncts of `HodgeTateDecompOr` are equivalent, so the
Hom disjunct's conventions (action `σ ∘ f ∘ ρ(σ)⁻¹`, twist `χ⁻¹` on the second factor) are the dual of the
field's. -/
theorem hom_of_tensor (h : HodgeTateDecompExists) : HodgeTateDecompHom := by
  intro p _ F _ _ _ A
  obtain ⟨a, b, e, he⟩ := h p F A
  exact ⟨b, a, homEquiv p e, homEquiv_map p (A.galRep p) e he⟩

theorem hom_iff_tensor : HodgeTateDecompHom ↔ HodgeTateDecompExists :=
  ⟨hodgeTateDecompExists_of_hom, hom_of_tensor⟩

/-- The or-leaf is equivalent to the field it replaces. -/
theorem or_iff_field : HodgeTateDecompOr ↔ HodgeTateDecompExists :=
  ⟨hodgeTateDecompExists_of_or, or_of_tensor⟩

end

end ZInQ.Contrib.HodgeTateOr
