import ZInQKernel.Contrib.OneProof.HodgeTatePairingDecomp

/-!
# The Hodge–Tate decomposition of `V_p(A)`: tensor form OR Hom form

Task htdecomp-or (2026-11-17; report `docs/research/htdecomp-or.md`).

The research field `hodgeTateDecompExists` (`ZInQ.Contrib.HodgeTateFromPairing.HodgeTateDecompExists`,
the tensor form `ℂ_p ⊗ V_p(A) ≅ ℂ_p(1)^a ⊕ ℂ_p^b`) is proved from the disjunction of the two printed
shapes of the Hodge–Tate decomposition:

* `HodgeTateDecompExists` itself (tensor form; Fontaine 1982 if Fontaine prints the tensor form);
* `HodgeTateDecompHom` (Hom form: `Hom_{ℚ_p}(V_p(A), ℂ_p) ≅ ℂ_p^a ⊕ ℂ_p(−1)^b`, i.e. Tate's
  `Hom(T(G), C) ≅ t_{G'}(C) ⊕ t_G^*(C)(−1)` with bases chosen).

The Hom disjunct implies the tensor form by `ℂ_p`-dualization (§2): `ℂ_p ⊗ V → Hom_{ℂ_p}(Hom_{ℚ_p}(V, ℂ_p), ℂ_p)`
is injective for every `ℚ_p`-vector space `V`; the Hom form makes the target finite-dimensional, so `V` is
finite-dimensional and the map is an isomorphism, `G_F`-equivariant for the contragredient action, and the dual of
`ℂ_p^a ⊕ ℂ_p(−1)^b` is `ℂ_p^a ⊕ ℂ_p(1)^b`. No dimension of `V` is assumed: it is derived from the Hom form.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option synthInstance.maxHeartbeats 400000

namespace ZInQ.Contrib.HodgeTateOr

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
open ZInQ.Contrib.HodgeTateFromPairing
open scoped TensorProduct

noncomputable section

/-! ## §0. The two printed forms and the or-leaf -/

/-- **Hodge–Tate decomposition, Hom form, bases chosen, dimensions not specified.** Tate, *p-divisible
groups*, Proc. Conf. Local Fields (Driebergen 1966), Springer 1967, §4, the corollary to the theorem on
`Hom(T(G), C)` (for `G = A[p^∞]` of an abelian scheme over the integers of `F`, i.e. good reduction), and
Fontaine, *Formes différentielles et modules de Tate des variétés abéliennes sur les corps locaux*, Invent.
Math. 65 (1982), 379–409, Théorème principal (any abelian variety over `F`); all locators and the exact
printed wording UNVERIFIED (no network). Printed shape: a `G_F`-equivariant isomorphism
`Hom_{ℤ_p}(T_p(A), ℂ_p) ≅ (ℂ_p ⊗_F t_{A'}) ⊕ (ℂ_p(−1) ⊗_F t_A^*)`, `G_F` acting on `Hom` by
`(σ f)(x) = σ(f(σ⁻¹ x))`. Lean form: `Hom_{ℤ_p}(T_p(A), ℂ_p) = Hom_{ℚ_p}(V_p(A), ℂ_p)` (canonical, since
`V_p(A) = ℚ_p ⊗_{ℤ_p} T_p(A)` and `ℂ_p` is a `ℚ_p`-space; the tree has no `ℤ_p`-module structure on `ℂ_p`,
so the `ℚ_p` side is the one statable); after choosing `F`-bases of the two finite-dimensional `F`-spaces
(dimensions `a`, `b`, left unnamed): `ℂ_p^a ⊕ ℂ_p(−1)^b`, `σ` acting on `ℂ_p(−1)` by `c ↦ χ(σ)⁻¹ σ(c)`,
through pkg-I4's `gfToGqp` as in `HodgeTateDecompExists`. -/
def HodgeTateDecompHom : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F),
    ∃ (a b : ℕ) (e : (A.V p →ₗ[ℚ_[p]] ℂ_[p]) ≃ₗ[ℂ_[p]] (Fin a → ℂ_[p]) × (Fin b → ℂ_[p])),
      ∀ (σ : Field.absoluteGaloisGroup F) (f : A.V p →ₗ[ℚ_[p]] ℂ_[p]),
        e (cpLin p (gfToGqp p F σ) ∘ₗ f ∘ₗ A.galRep p σ⁻¹) =
          ((fun k => cpAct p (gfToGqp p F σ) ((e f).1 k)),
            (fun k => cycPow p (gfToGqp p F σ) (-1) • cpAct p (gfToGqp p F σ) ((e f).2 k)))

/-- **LEAF (Hodge–Tate decomposition of `V_p(A)`, tensor form OR Hom form).** The disjunction of the two
printed shapes: `HodgeTateDecompExists` (tensor form, `ℂ_p ⊗ V_p(A) ≅ ℂ_p(1)^a ⊕ ℂ_p^b`; Fontaine 1982,
Théorème principal, if printed in tensor form) or `HodgeTateDecompHom` (Hom form; Tate 1967 §4 corollary,
Fontaine 1982, if printed in Hom form); locators UNVERIFIED. Whichever form the print has, the leaf is a
consequence of it (`or_of_tensor`, `or_of_hom`), never stronger. -/
def HodgeTateDecompOr : Prop :=
  HodgeTateDecompExists ∨ HodgeTateDecompHom

theorem or_of_tensor (h : HodgeTateDecompExists) : HodgeTateDecompOr := Or.inl h

theorem or_of_hom (h : HodgeTateDecompHom) : HodgeTateDecompOr := Or.inr h

/-! ## §1. Cyclotomic character of an inverse -/

variable (p : ℕ) [Fact p.Prime]

theorem cyc_inv (σ : GQp p) : cyc p σ⁻¹ = (cyc p σ)⁻¹ := by
  change cyclotomicCharacter (PadicAlgCl p) p (σ.toRingEquiv)⁻¹ = _
  rw [map_inv]
  rfl

theorem cycPow_inv_neg_one (σ : GQp p) : cycPow p σ⁻¹ (-1) = cycPow p σ 1 := by
  simp only [cycPow, cyc_inv, inv_zpow', neg_neg]

theorem cpAct_inv_apply' (σ : GQp p) (x : ℂ_[p]) : cpAct p σ (cpAct p σ⁻¹ x) = x := by
  have := cpAct_inv_apply p σ⁻¹ x
  rwa [inv_inv] at this

/-! ## §2. Dualization: the Hom form implies the tensor form -/

section Dual

variable {F : Type*} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
  (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)

/-- `f ↦ (c ⊗ v ↦ c f(v))`, the evaluation pairing `Hom_{ℚ_p}(V, ℂ_p) × (ℂ_p ⊗ V) → ℂ_p`. -/
abbrev ev (f : V →ₗ[ℚ_[p]] ℂ_[p]) : ℂ_[p] ⊗[ℚ_[p]] V →ₗ[ℂ_[p]] ℂ_[p] :=
  LinearMap.liftBaseChangeEquiv ℂ_[p] f

theorem ev_tmul (f : V →ₗ[ℚ_[p]] ℂ_[p]) (c : ℂ_[p]) (v : V) :
    ev p f (c ⊗ₜ v) = c * f v := by
  simp [ev, LinearMap.liftBaseChange_tmul]

theorem ev_smul (c : ℂ_[p]) (f : V →ₗ[ℚ_[p]] ℂ_[p]) : ev p (c • f) = c • ev p f :=
  map_smul (LinearMap.liftBaseChangeEquiv ℂ_[p]) c f

/-- The evaluation pairing separates points of `ℂ_p ⊗ V`. -/
theorem eq_zero_of_ev (w : ℂ_[p] ⊗[ℚ_[p]] V) (h : ∀ f : V →ₗ[ℚ_[p]] ℂ_[p], ev p f w = 0) : w = 0 := by
  classical
  let b := Basis.ofVectorSpace ℚ_[p] V
  let bC := b.baseChange ℂ_[p]
  apply bC.repr.injective
  ext i
  have hi : ∀ w' : ℂ_[p] ⊗[ℚ_[p]] V,
      bC.repr w' i = ev p ((Algebra.linearMap ℚ_[p] ℂ_[p]) ∘ₗ b.coord i) w' := by
    intro w'
    induction w' using TensorProduct.inductionOn with
    | tmul c v =>
      rw [ev_tmul, Basis.baseChange_repr_tmul]
      simp [Algebra.smul_def, mul_comm]
    | add x y hx hy => rw [map_add, Finsupp.add_apply, hx, hy, map_add]
  rw [hi, h]
  simp

/-- **Equivariance of the evaluation pairing**: `⟨f, σ w⟩ = σ ⟨σ⁻¹ f, w⟩`. -/
theorem ev_map (σ : Field.absoluteGaloisGroup F) (f : V →ₗ[ℚ_[p]] ℂ_[p]) (w : ℂ_[p] ⊗[ℚ_[p]] V) :
    ev p f (TensorProduct.map (cpLin p (gfToGqp p F σ)) (ρ σ) w) =
      cpAct p (gfToGqp p F σ) (ev p (cpLin p (gfToGqp p F σ⁻¹) ∘ₗ f ∘ₗ ρ σ⁻¹⁻¹) w) := by
  induction w using TensorProduct.inductionOn with
  | tmul c v =>
    rw [TensorProduct.map_tmul, ev_tmul, ev_tmul, map_mul, inv_inv]
    simp only [LinearMap.comp_apply, cpLin_apply, map_inv, cpAct_inv_apply']
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

variable {a b : ℕ} (e : (V →ₗ[ℚ_[p]] ℂ_[p]) ≃ₗ[ℂ_[p]] (Fin a → ℂ_[p]) × (Fin b → ℂ_[p]))

/-- The dual basis map `ℂ_p ⊗ V → ℂ_p^b × ℂ_p^a`: pair with the `e`-preimages of the standard basis, the
`ℂ_p(−1)`-part first. -/
def dualMap : ℂ_[p] ⊗[ℚ_[p]] V →ₗ[ℂ_[p]] (Fin b → ℂ_[p]) × (Fin a → ℂ_[p]) :=
  LinearMap.prod (LinearMap.pi fun k => ev p (e.symm (0, Pi.single k 1)))
    (LinearMap.pi fun k => ev p (e.symm (Pi.single k 1, 0)))

theorem dualMap_fst (w : ℂ_[p] ⊗[ℚ_[p]] V) (k : Fin b) :
    (dualMap p e w).1 k = ev p (e.symm (0, Pi.single k 1)) w := rfl

theorem dualMap_snd (w : ℂ_[p] ⊗[ℚ_[p]] V) (k : Fin a) :
    (dualMap p e w).2 k = ev p (e.symm (Pi.single k 1, 0)) w := rfl

theorem dualMap_injective : Function.Injective (dualMap p e) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro w hw
  rw [LinearMap.mem_ker] at hw
  rw [Submodule.mem_bot]
  apply eq_zero_of_ev p w
  -- the functional `u ↦ ⟨e⁻¹ u, w⟩` vanishes on the standard basis
  let φ : ((Fin a → ℂ_[p]) × (Fin b → ℂ_[p])) →ₗ[ℂ_[p]] ℂ_[p] :=
    LinearMap.applyₗ (R := ℂ_[p]) w ∘ₗ (LinearMap.liftBaseChangeEquiv ℂ_[p]).toLinearMap ∘ₗ
      e.symm.toLinearMap
  have hφ : φ = 0 := by
    apply LinearMap.prod_ext
    · apply LinearMap.pi_ext
      intro k x
      have h1 : (Pi.single k x : Fin a → ℂ_[p]) = x • Pi.single k 1 := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      have h2 := congrArg (fun u => u.2 k) hw
      simp only [dualMap_snd, Prod.snd_zero, Pi.zero_apply] at h2
      simp only [φ, LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.zero_apply, h1]
      rw [show ((x • Pi.single k 1 : Fin a → ℂ_[p]), (0 : Fin b → ℂ_[p])) = x • (Pi.single k 1, 0) by
        simp, map_smul, map_smul, LinearMap.applyₗ_apply_apply, LinearMap.smul_apply]
      rw [smul_eq_mul]
      simp only [LinearEquiv.coe_coe] at h2 ⊢
      rw [show (LinearMap.liftBaseChangeEquiv ℂ_[p]) (e.symm (Pi.single k 1, 0)) w = 0 from h2,
        mul_zero]
    · apply LinearMap.pi_ext
      intro k x
      have h1 : (Pi.single k x : Fin b → ℂ_[p]) = x • Pi.single k 1 := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      have h2 := congrArg (fun u => u.1 k) hw
      simp only [dualMap_fst, Prod.fst_zero, Pi.zero_apply] at h2
      simp only [φ, LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.zero_apply, h1]
      rw [show ((0 : Fin a → ℂ_[p]), (x • Pi.single k 1 : Fin b → ℂ_[p])) = x • (0, Pi.single k 1) by
        simp, map_smul, map_smul, LinearMap.applyₗ_apply_apply, LinearMap.smul_apply]
      rw [smul_eq_mul]
      simp only [LinearEquiv.coe_coe] at h2 ⊢
      rw [show (LinearMap.liftBaseChangeEquiv ℂ_[p]) (e.symm (0, Pi.single k 1)) w = 0 from h2,
        mul_zero]
  intro f
  have := LinearMap.congr_fun hφ (e f)
  simpa [φ] using this

include e in
/-- The Hom form forces `V` to be finite-dimensional. -/
theorem finiteDimensional_of_dual : FiniteDimensional ℚ_[p] V := by
  classical
  let bV := Basis.ofVectorSpace ℚ_[p] V
  have : Module.Finite ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] V) :=
    Module.Finite.of_injective (dualMap p e) (dualMap_injective p e)
  have : Finite (Basis.ofVectorSpaceIndex ℚ_[p] V) := Module.Finite.finite_basis (bV.baseChange ℂ_[p])
  exact Module.Finite.of_basis bV

include e in
theorem finrank_eq_of_dual : finrank ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] V) =
    finrank ℂ_[p] ((Fin b → ℂ_[p]) × (Fin a → ℂ_[p])) := by
  have := finiteDimensional_of_dual p e
  have h1 := (e.trans (LinearEquiv.prodComm ℂ_[p] _ _)).finrank_eq
  have h2 := (LinearMap.liftBaseChangeEquiv (R := ℚ_[p]) (M := V) (N := ℂ_[p]) ℂ_[p]).finrank_eq
  rw [h1] at h2
  rw [h2, Subspace.dual_finrank_eq]

/-- The isomorphism `ℂ_p ⊗ V ≅ ℂ_p^b × ℂ_p^a`. -/
def dualEquiv : ℂ_[p] ⊗[ℚ_[p]] V ≃ₗ[ℂ_[p]] (Fin b → ℂ_[p]) × (Fin a → ℂ_[p]) :=
  haveI := finiteDimensional_of_dual p e
  LinearEquiv.ofBijective (dualMap p e)
    ⟨dualMap_injective p e,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (finrank_eq_of_dual p e)).mp
        (dualMap_injective p e)⟩

theorem dualEquiv_apply (w : ℂ_[p] ⊗[ℚ_[p]] V) : dualEquiv p e w = dualMap p e w := rfl

theorem cpAct_single {n : ℕ} (σ : GQp p) (k : Fin n) :
    (fun j => cpAct p σ ((Pi.single k (1 : ℂ_[p]) : Fin n → ℂ_[p]) j)) = Pi.single k 1 := by
  funext j
  by_cases hj : j = k
  · subst hj; simp
  · simp [hj]

/-- **The Hom form gives the tensor form**: if `e : Hom_{ℚ_p}(V, ℂ_p) ≅ ℂ_p^a ⊕ ℂ_p(−1)^b` equivariantly,
then `ℂ_p ⊗ V ≅ ℂ_p(1)^b ⊕ ℂ_p^a` equivariantly. -/
theorem dualEquiv_map
    (he : ∀ (σ : Field.absoluteGaloisGroup F) (f : V →ₗ[ℚ_[p]] ℂ_[p]),
      e (cpLin p (gfToGqp p F σ) ∘ₗ f ∘ₗ ρ σ⁻¹) =
        ((fun k => cpAct p (gfToGqp p F σ) ((e f).1 k)),
          (fun k => cycPow p (gfToGqp p F σ) (-1) • cpAct p (gfToGqp p F σ) ((e f).2 k))))
    (σ : Field.absoluteGaloisGroup F) (x : ℂ_[p] ⊗[ℚ_[p]] V) :
    dualEquiv p e (TensorProduct.map (cpLin p (gfToGqp p F σ)) (ρ σ) x) =
      ((fun k => cycPow p (gfToGqp p F σ) 1 • cpAct p (gfToGqp p F σ) ((dualEquiv p e x).1 k)),
        (fun k => cpAct p (gfToGqp p F σ) ((dualEquiv p e x).2 k))) := by
  rw [dualEquiv_apply, dualEquiv_apply]
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · -- the `ℂ_p(−1)` part of the Hom side gives the `ℂ_p(1)` part
    dsimp only
    rw [dualMap_fst, dualMap_fst, ev_map p ρ]
    have hg : cpLin p (gfToGqp p F σ⁻¹) ∘ₗ e.symm (0, Pi.single k 1) ∘ₗ ρ σ⁻¹⁻¹ =
        (algebraMap ℚ_[p] ℂ_[p] (cycPow p (gfToGqp p F σ) 1)) • e.symm (0, Pi.single k 1) := by
      apply e.injective
      rw [he, map_smul, LinearEquiv.apply_symm_apply, map_inv, cycPow_inv_neg_one]
      refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
      · simp
      · have := congrFun (cpAct_single p (gfToGqp p F σ)⁻¹ k) j
        simp only at this
        show cycPow p (gfToGqp p F σ) 1 • cpAct p (gfToGqp p F σ)⁻¹ ((Pi.single k (1 : ℂ_[p]) : Fin b → ℂ_[p]) j) =
          algebraMap ℚ_[p] ℂ_[p] (cycPow p (gfToGqp p F σ) 1) * (Pi.single k (1 : ℂ_[p]) : Fin b → ℂ_[p]) j
        rw [this, Algebra.smul_def]
    rw [hg, ev_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, cpAct_algebraMap,
      Algebra.smul_def]
  · -- the untwisted part stays untwisted
    dsimp only
    rw [dualMap_snd, dualMap_snd, ev_map p ρ]
    have hg : cpLin p (gfToGqp p F σ⁻¹) ∘ₗ e.symm (Pi.single k 1, 0) ∘ₗ ρ σ⁻¹⁻¹ =
        e.symm (Pi.single k 1, 0) := by
      apply e.injective
      rw [he, LinearEquiv.apply_symm_apply]
      refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
      · exact congrFun (cpAct_single p _ k) j
      · simp
    rw [hg]

end Dual

/-! ## §3. The field from each disjunct -/

/-- **The Hom form implies the field** (`ℂ_p`-dualization, §2). -/
theorem hodgeTateDecompExists_of_hom (h : HodgeTateDecompHom) : HodgeTateDecompExists := by
  intro p _ F _ _ _ A
  obtain ⟨a, b, e, he⟩ := h p F A
  exact ⟨b, a, dualEquiv p e, dualEquiv_map p (A.galRep p) e he⟩

/-- **The field from the or-leaf**: either printed form of the Hodge–Tate decomposition implies
`HodgeTateDecompExists`. -/
theorem hodgeTateDecompExists_of_or (h : HodgeTateDecompOr) : HodgeTateDecompExists :=
  h.elim id hodgeTateDecompExists_of_hom

end

end ZInQ.Contrib.HodgeTateOr
