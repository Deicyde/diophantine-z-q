import ZInQKernel.Contrib.HDecomp.Textbook.T10Etale
import ZInQKernel.Contrib.OneProof.DeRhamRange
import ZInQKernel.Contrib.OneProof.HodgeTateDecompOrH1
import ZInQKernel.Contrib.OneProof.MumfordTorsionAlgClosed

/-!
# derham-scholze: `V_p(A)` is de Rham by Scholze's comparison (manuscript `lem:de-rham-descent`)

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task derham-scholze, 2026-11-17).
Report `docs/research/derham-scholze.md`; scratch copy `scratch/derham-scholze/DeRhamScholze.lean`.

The manuscript (diophantine_zq.tex, `lem:de-rham-descent`, L10939-11004, step C3) proves that `V_ℓ(A)` is
de Rham by Scholze's comparison (Forum Math. Pi 1 (2013), Cor. 1.8, Thms 9.1, 9.3, corrigendum Forum Math. Pi 4
(2016) e6) for `H¹_ét(A_{F̄}, ℚ_ℓ)`, then Milne, *Abelian varieties* v2.00, Part I, Thm 12.1(a)
(`V_ℓ(A) ≅ H¹_ét(A_{F̄}, ℚ_ℓ)^∨`, Galois-equivariantly), then closure under duals (Brinon–Conrad 5.2.1, 6.3.3).

Here:
* §1 the Galois action on `Hⁱ(X_{F̄}, ℤ_ℓ)` for any `X/F` (Mathlib's pro-étale `ℓ`-adic cohomology, transport of
  t10-etale), equal by `rfl` to t10-etale's `galH` for an abelian variety;
* §2 `D_dR` and its Hodge filtration for a family of operators;
* §3 the leaf `ScholzeDeRhamAlg` (Scholze's Cor. 1.8 for the analytification, with Thms 9.1, 9.3);
* §4-§6 the glue: transport along equivariant isomorphisms, the Milne identification (t10-etale's leaf
  `T10_TateDuality`), duality, and the two research fields.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

namespace DeRhamScholze

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
open scoped TensorProduct

noncomputable section

/-! ## §1. The Galois action on `Hⁱ(X_{F̄}, ℤ_ℓ)` -/

section Gal

variable {K : Type} [Field K] (X : Over (Spec (CommRingCat.of K)))

/-- `X_{K̄} = X ×_K Spec K̄`. -/
abbrev XKbar : Scheme := pullback X.hom (T10Etale.specAlg K)

/-- `1 × Spec(σ)` on `X_{K̄}`. -/
def galAutX (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) : XKbar X ⟶ XKbar X :=
  pullback.map X.hom (T10Etale.specAlg K) X.hom (T10Etale.specAlg K) (𝟙 _) (T10Etale.specAut σ) (𝟙 _)
    (by simp) (by rw [Category.comp_id, T10Etale.specAut_comp])

lemma galAutX_mul (σ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    galAutX X (σ * τ) = galAutX X σ ≫ galAutX X τ := by
  simp only [galAutX, pullback.map_comp, T10Etale.specAut_mul, Category.comp_id]

lemma galAutX_one : galAutX X 1 = 𝟙 _ := by
  simp only [galAutX, T10Etale.specAut_one]
  exact pullback.map_id

/-- `1 × Spec(σ)` as an automorphism of the scheme `X_{K̄}`. -/
def galIsoX (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) : XKbar X ≅ XKbar X where
  hom := galAutX X σ
  inv := galAutX X σ⁻¹
  hom_inv_id := by rw [← galAutX_mul, mul_inv_cancel, galAutX_one]
  inv_hom_id := by rw [← galAutX_mul, inv_mul_cancel, galAutX_one]

/-- **The Galois action on `Hⁱ(X_{K̄}, ℤ_ℓ)`** (Mathlib's pro-étale `ℓ`-adic cohomology): `σ` acts by
transport along `1 × Spec(σ⁻¹)` (t10-etale's `galH`, for any `X` and any degree). -/
def galHX (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) (σ : Field.absoluteGaloisGroup K) :
    (XKbar X).EllAdicCohomology ℓ i →ₗ[ℤ_[ℓ]] (XKbar X).EllAdicCohomology ℓ i :=
  T10Etale.transportₗ ℓ (galIsoX X (σ⁻¹ : Field.absoluteGaloisGroup K)) i

/-- For an abelian variety and `i = 1` this is t10-etale's action `galH` (by `rfl`). -/
theorem galHX_abVar (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (σ : Field.absoluteGaloisGroup K) :
    galHX A.X ℓ 1 σ = T10Etale.galH A ℓ σ := rfl

/-- The action is by automorphisms (t10-etale's `transport_bijective`). -/
theorem galHX_bijective (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) (σ : Field.absoluteGaloisGroup K) :
    Function.Bijective (galHX X ℓ i σ) :=
  T10Etale.transport_bijective ℓ _ i

/-- `Hⁱ(X_{K̄}, ℚ_ℓ) = ℚ_ℓ ⊗_{ℤ_ℓ} Hⁱ(X_{K̄}, ℤ_ℓ)`. -/
abbrev HQ (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) := ℚ_[ℓ] ⊗[ℤ_[ℓ]] (XKbar X).EllAdicCohomology ℓ i

/-- The Galois action on `Hⁱ(X_{K̄}, ℚ_ℓ)`. -/
def rhoH (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) (σ : Field.absoluteGaloisGroup K) :
    HQ X ℓ i →ₗ[ℚ_[ℓ]] HQ X ℓ i :=
  (galHX X ℓ i σ).baseChange ℚ_[ℓ]

end Gal

/-! ## §2. `D_dR` and its Hodge filtration -/

section DR

variable (p : ℕ) [Fact p.Prime] {F : Type*} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
variable {W : Type*} [AddCommGroup W] [Module ℚ_[p] W]

/-- `D_dR(W) = (B_dR ⊗_{ℚ_p} W)^{G_F}` for a family of operators `ρ(σ)` (the carrier of `ddrTensorOver`). -/
def ddrFam (ρ : Field.absoluteGaloisGroup F → W →ₗ[ℚ_[p]] W) : Submodule ℚ_[p] (BdR p ⊗[ℚ_[p]] W) where
  carrier := {x | ∀ σ, TensorProduct.map (drAct p (gfToGqp p F σ)) (ρ σ) x = x}
  zero_mem' σ := map_zero _
  add_mem' ha hb σ := by rw [map_add, ha σ, hb σ]
  smul_mem' c x hx σ := by rw [map_smul, hx σ]

theorem ddrFam_rep (ρW : Representation ℚ_[p] (Field.absoluteGaloisGroup F) W) :
    ddrFam p (fun σ => ρW σ) = ddrTensorOver p ρW := rfl

/-- `W` is de Rham: finite-dimensional, `dim_{ℚ_p} D_dR(W) = [F:ℚ_p] · dim_{ℚ_p} W` (`IsDeRhamTensorOver`). -/
def IsDeRhamFam (ρ : Field.absoluteGaloisGroup F → W →ₗ[ℚ_[p]] W) : Prop :=
  FiniteDimensional ℚ_[p] W ∧
    finrank ℚ_[p] (ddrFam p ρ) = finrank ℚ_[p] F * finrank ℚ_[p] W

/-- `Fil^j B_dR = t^j B_dR^+ = 𝔪^j` for `j ≥ 0` (`B_dR^+` is a DVR with uniformizer `ξ`, and `t = ξ · unit`,
`TDict.tt_eq_varpi_mul_unit`), as a `ℚ_p`-subspace of `B_dR`. -/
def filB (j : ℕ) : Submodule ℚ_[p] (BdR p) where
  carrier := {x | ∃ b ∈ IsLocalRing.maximalIdeal (BDeRhamPlus 𝓞_ℂ_[p] p) ^ j,
    algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p) b = x}
  zero_mem' := ⟨0, zero_mem _, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, add_mem ha hb, map_add _ _ _⟩
  smul_mem' := by
    rintro c _ ⟨b, hb, rfl⟩
    refine ⟨qpToPlus p c * b, Ideal.mul_mem_left _ _ hb, ?_⟩
    rw [map_mul, Algebra.smul_def]
    rfl

/-- `Fil^j D_dR(W) = D_dR(W) ∩ (Fil^j B_dR ⊗ W)`. -/
def filD (ρ : Field.absoluteGaloisGroup F → W →ₗ[ℚ_[p]] W) (j : ℕ) : Submodule ℚ_[p] (BdR p ⊗[ℚ_[p]] W) :=
  ddrFam p ρ ⊓ LinearMap.range (TensorProduct.map (filB p j).subtype (LinearMap.id : W →ₗ[ℚ_[p]] W))

/-- **The Hodge filtration of `D_dR(W)` has its jumps in `[0, i]`**: `Fil⁰ D_dR = D_dR` and
`Fil^{i+1} D_dR = 0`. For `W = Hⁱ_ét` this is what the filtered comparison `D_dR(Hⁱ_ét) ≅ Hⁱ_dR(X)` gives,
since the Hodge filtration of `Hⁱ_dR` (by `H^i(Ω^{≥j})`) has `Fil⁰ = Hⁱ_dR` and `Fil^{i+1} = 0`. -/
def HodgeRange (ρ : Field.absoluteGaloisGroup F → W →ₗ[ℚ_[p]] W) (i : ℕ) : Prop :=
  filD p ρ 0 = ddrFam p ρ ∧ filD p ρ (i + 1) = ⊥

end DR

/-! ## §3. The leaf: Scholze's comparison, algebraic form (as the manuscript applies it) -/

/-- **LEAF (consequence of Scholze, Forum Math. Pi 1 (2013), Cor. 1.8, with Thms 9.1 and 9.3 and the corrigendum
Forum Math. Pi 4 (2016) e6; applied as in diophantine_zq.tex `lem:de-rham-descent`, L10953-10965).** For a finite
extension `F` of `ℚ_p` and a proper smooth `F`-scheme `X`, and every `i`, the `G_F`-representation
`Hⁱ_ét(X_{F̄}, ℚ_p)` is de Rham, and the Hodge filtration of `D_dR(Hⁱ_ét)` has its jumps in `[0, i]`.

Print (Cor. 1.8, wording quoted by h-leaves §3.1 from arXiv:1205.3463): for a proper smooth rigid-analytic
variety `X` over a complete discretely valued extension `k` of `ℚ_p` with perfect residue field, `Hⁱ(X_ét, ℚ_p)` is
de Rham, with associated filtered `k`-vector space `Hⁱ_dR(X)`. The manuscript applies it to the analytification
of `A/F` and transfers to algebraic cohomology by Thm 9.1 (coherent / filtered de Rham cohomology) and Thm 9.3
(`ℤ/ℓⁿ`-cohomology), then inverse limits. The jump clause is the filtered identification
`D_dR(Hⁱ_ét) ≅ Hⁱ_dR(X)` together with `Fil⁰ Hⁱ_dR = Hⁱ_dR`, `Fil^{i+1} Hⁱ_dR = 0` (Hodge filtration by
`Hⁱ(Ω^{≥j})`).

Lean form: `Hⁱ_ét(X_{F̄}, ℚ_p) = ℚ_p ⊗_{ℤ_p} Hⁱ(X_{F̄}, ℤ_p)` with Mathlib's pro-étale `ℓ`-adic cohomology
(`Scheme.EllAdicCohomology`, Bhatt–Scholze 2015 Def. 6.8.1) and `σ` acting by transport along `1 × Spec(σ⁻¹)`
(`galHX`, t10-etale's `galH`); `D_dR = (B_dR ⊗ W)^{G_F}` (`ddrFam`, the carrier of `ddrTensorOver`),
`Fil^j D_dR = D_dR ∩ (t^j B_dR^+ ⊗ W)` (`filD`). Dictionary steps between the print and this form (report §3):
analytification (Cor. 1.8 is for rigid spaces), Thms 9.1/9.3, `F̄` versus `ℂ_p` (invariance of étale cohomology of
proper varieties under extension of algebraically closed fields), and pro-étale versus classical `ℓ`-adic
cohomology (Bhatt–Scholze 2015 §5.6). -/
def ScholzeDeRhamAlg : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (X : Over (Spec (CommRingCat.of F))) [IsProper X.hom] [Smooth X.hom] (i : ℕ),
    IsDeRhamFam p (F := F) (rhoH X p i) ∧ HodgeRange p (F := F) (rhoH X p i) i

/-! ## §4. Transport along equivariant isomorphisms -/

section Transport

variable (p : ℕ) [Fact p.Prime] {F : Type*} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
variable {W W' : Type*} [AddCommGroup W] [Module ℚ_[p] W] [AddCommGroup W'] [Module ℚ_[p] W']
variable {ρ : Field.absoluteGaloisGroup F → W →ₗ[ℚ_[p]] W} {ρ' : Field.absoluteGaloisGroup F → W' →ₗ[ℚ_[p]] W'}

/-- `id ⊗ e : B_dR ⊗ W ≃ B_dR ⊗ W'`. -/
abbrev tEquiv (e : W ≃ₗ[ℚ_[p]] W') : (BdR p ⊗[ℚ_[p]] W) ≃ₗ[ℚ_[p]] (BdR p ⊗[ℚ_[p]] W') :=
  TensorProduct.congr (LinearEquiv.refl ℚ_[p] (BdR p)) e

theorem tEquiv_comm (e : W ≃ₗ[ℚ_[p]] W') (he : ∀ σ w, e (ρ σ w) = ρ' σ (e w)) (σ : Field.absoluteGaloisGroup F)
    (y : BdR p ⊗[ℚ_[p]] W) :
    TensorProduct.map (drAct p (gfToGqp p F σ)) (ρ' σ) (tEquiv p e y) =
      tEquiv p e (TensorProduct.map (drAct p (gfToGqp p F σ)) (ρ σ) y) := by
  induction y using TensorProduct.inductionOn with
  | tmul b w => simp [he]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_ddrFam (e : W ≃ₗ[ℚ_[p]] W') (he : ∀ σ w, e (ρ σ w) = ρ' σ (e w)) :
    (ddrFam p ρ).map (tEquiv p e).toLinearMap = ddrFam p ρ' := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩ σ
    change TensorProduct.map _ _ (tEquiv p e y) = tEquiv p e y
    rw [tEquiv_comm p e he, hy σ]
  · intro hz
    refine ⟨(tEquiv p e).symm z, fun σ => ?_, (tEquiv p e).apply_symm_apply z⟩
    apply (tEquiv p e).injective
    rw [← tEquiv_comm p e he, LinearEquiv.apply_symm_apply]
    exact hz σ

theorem map_filRange (e : W ≃ₗ[ℚ_[p]] W') (j : ℕ) :
    (LinearMap.range (TensorProduct.map (filB p j).subtype (LinearMap.id : W →ₗ[ℚ_[p]] W))).map
        (tEquiv p e).toLinearMap =
      LinearMap.range (TensorProduct.map (filB p j).subtype (LinearMap.id : W' →ₗ[ℚ_[p]] W')) := by
  have hcomp : (tEquiv p e).toLinearMap ∘ₗ TensorProduct.map (filB p j).subtype (LinearMap.id : W →ₗ[ℚ_[p]] W) =
      TensorProduct.map (filB p j).subtype (LinearMap.id : W' →ₗ[ℚ_[p]] W') ∘ₗ
        (TensorProduct.congr (LinearEquiv.refl ℚ_[p] (filB p j)) e).toLinearMap := by
    apply TensorProduct.ext'
    intro x w
    simp
  rw [← LinearMap.range_comp, hcomp, LinearMap.range_comp]
  erw [LinearEquiv.range, Submodule.map_top]

theorem map_filD (e : W ≃ₗ[ℚ_[p]] W') (he : ∀ σ w, e (ρ σ w) = ρ' σ (e w)) (j : ℕ) :
    (filD p ρ j).map (tEquiv p e).toLinearMap = filD p ρ' j := by
  rw [filD, filD, Submodule.map_inf _ (tEquiv p e).injective, map_ddrFam p e he, map_filRange p e j]

theorem isDeRhamFam_of_equiv (e : W ≃ₗ[ℚ_[p]] W') (he : ∀ σ w, e (ρ σ w) = ρ' σ (e w))
    (h : IsDeRhamFam p ρ) : IsDeRhamFam p ρ' := by
  obtain ⟨hfd, hr⟩ := h
  haveI := hfd
  refine ⟨LinearEquiv.finiteDimensional e, ?_⟩
  rw [← map_ddrFam p e he, ← e.finrank_eq, ← hr]
  exact ((tEquiv p e).submoduleMap (ddrFam p ρ)).finrank_eq.symm

theorem hodgeRange_of_equiv (e : W ≃ₗ[ℚ_[p]] W') (he : ∀ σ w, e (ρ σ w) = ρ' σ (e w)) (i : ℕ)
    (h : HodgeRange p ρ i) : HodgeRange p ρ' i := by
  obtain ⟨h0, h1⟩ := h
  refine ⟨?_, ?_⟩
  · rw [← map_filD p e he, ← map_ddrFam p e he, h0]
  · rw [← map_filD p e he, h1, Submodule.map_bot]

end Transport

/-! ## §5. Milne's identification `H¹_ét(A_{F̄}, ℚ_p) ≅ V_p(A)^∨` (t10-etale's leaf `T10_TateDuality`) -/

section Milne

variable (p : ℕ) [Fact p.Prime]

/-- `ℚ_p ⊗_{ℤ_p} Hom_{ℤ_p}(T, ℤ_p) ≅ Hom_{ℚ_p}(ℚ_p ⊗ T, ℚ_p)` for `T` finite free (Mathlib's
`IsBaseChange.toDualBaseChange`). -/
def dualBC (T : Type*) [AddCommGroup T] [Module ℤ_[p] T] [Module.Free ℤ_[p] T] [Module.Finite ℤ_[p] T] :
    ℚ_[p] ⊗[ℤ_[p]] Module.Dual ℤ_[p] T ≃ₗ[ℚ_[p]] Module.Dual ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] T) :=
  (TensorProduct.isBaseChange ℤ_[p] T ℚ_[p]).toDualBaseChange

theorem dualBC_comm {T : Type*} [AddCommGroup T] [Module ℤ_[p] T] [Module.Free ℤ_[p] T] [Module.Finite ℤ_[p] T]
    (f : T →ₗ[ℤ_[p]] T) (y : ℚ_[p] ⊗[ℤ_[p]] Module.Dual ℤ_[p] T) :
    dualBC p T ((f.dualMap).baseChange ℚ_[p] y) = (f.baseChange ℚ_[p]).dualMap (dualBC p T y) := by
  induction y using TensorProduct.inductionOn with
  | tmul a g =>
    apply (TensorProduct.isBaseChange ℤ_[p] T ℚ_[p]).algHom_ext
    intro t
    rw [LinearMap.baseChange_tmul, LinearMap.dualMap_apply]
    erw [IsBaseChange.toDualBaseChange_tmul]
    change _ = (dualBC p T (a ⊗ₜ g)) (f.baseChange ℚ_[p] (1 ⊗ₜ t))
    rw [LinearMap.baseChange_tmul]
    erw [IsBaseChange.toDualBaseChange_tmul (TensorProduct.isBaseChange ℤ_[p] T ℚ_[p]) a g (f t)]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Milne

/-! ## §6. The manuscript's lemma for `V_p(A)`, and the two research fields -/

section Main

variable (p : ℕ) [Fact p.Prime]

/-- `D_dR(Hom(V, ℚ_p))` and `D_dR(V)`: the contragredient of the contragredient is `V` (`Module.evalEquiv`). -/
theorem evalEquiv_comm {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [FiniteDimensional ℚ_[p] V]
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) (σ : Field.absoluteGaloisGroup F) (v : V) :
    Module.evalEquiv ℚ_[p] V (ρ σ v) = ρ.dual.dual σ (Module.evalEquiv ℚ_[p] V v) := by
  ext f
  simp [Representation.dual_apply, Module.Dual.transpose_apply]

/-- The Galois representation of pkg-I4's copy `A` is that of the kernel's copy `toKer A` (AbVarBC's
`vToI4_galRep`, definitional). -/
theorem galRep_apply_toKer {F : Type} [Field F] (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F)
    (σ : Field.absoluteGaloisGroup F) (v : A.V p) :
    A.galRep p σ v = ((DeRhamPrint.toKer A).galT (ℓ := p) σ).baseChange ℚ_[p] v :=
  (ZInQ.Contrib.AbVarBC.vToI4_galRep p (DeRhamPrint.toKer A) σ v).trans rfl

/-- `H¹(A_{F̄}, ℚ_p) ≅ V_p(A)^∨` from Milne's `ℤ_p`-isomorphism `φ : H¹(A_{F̄}, ℤ_p) ≅ Hom(T_p A, ℤ_p)`. -/
def milneE {F : Type} [Field F] (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F)
    [Module.Free ℤ_[p] ((DeRhamPrint.toKer A).T p)] [Module.Finite ℤ_[p] ((DeRhamPrint.toKer A).T p)]
    (φ : ((DeRhamPrint.toKer A).baseChange (AlgebraicClosure F)).X.left.EllAdicCohomology p 1 ≃ₗ[ℤ_[p]]
      Module.Dual ℤ_[p] ((DeRhamPrint.toKer A).T p)) :
    HQ A.X p 1 ≃ₗ[ℚ_[p]] Module.Dual ℚ_[p] (A.V p) :=
  (LinearEquiv.baseChange ℤ_[p] ℚ_[p] _ _ φ).trans (dualBC p ((DeRhamPrint.toKer A).T p))

set_option maxHeartbeats 4000000 in
theorem milneE_comm {F : Type} [Field F] (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F)
    [Module.Free ℤ_[p] ((DeRhamPrint.toKer A).T p)] [Module.Finite ℤ_[p] ((DeRhamPrint.toKer A).T p)]
    (φ : ((DeRhamPrint.toKer A).baseChange (AlgebraicClosure F)).X.left.EllAdicCohomology p 1 ≃ₗ[ℤ_[p]]
      Module.Dual ℤ_[p] ((DeRhamPrint.toKer A).T p))
    (hφ : ∀ (σ : Field.absoluteGaloisGroup F) x,
      φ (T10Etale.galH (DeRhamPrint.toKer A) p σ x) = ((DeRhamPrint.toKer A).galT (ℓ := p) σ⁻¹).dualMap (φ x))
    (σ : Field.absoluteGaloisGroup F) (w : HQ A.X p 1) :
    milneE p A φ (rhoH A.X p 1 σ w) = (A.galRep p).dual σ (milneE p A φ w) := by
  have hcomp : φ.toLinearMap ∘ₗ T10Etale.galH (DeRhamPrint.toKer A) p σ =
      ((DeRhamPrint.toKer A).galT (ℓ := p) σ⁻¹).dualMap ∘ₗ φ.toLinearMap := LinearMap.ext (hφ σ)
  have h1 : LinearEquiv.baseChange ℤ_[p] ℚ_[p] _ _ φ (rhoH A.X p 1 σ w) =
      ((((DeRhamPrint.toKer A).galT (ℓ := p) σ⁻¹).dualMap).baseChange ℚ_[p])
        (LinearEquiv.baseChange ℤ_[p] ℚ_[p] _ _ φ w) := by
    have h := LinearMap.congr_fun (congrArg (LinearMap.baseChange ℚ_[p]) hcomp) w
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at h
    exact h
  rw [show milneE p A φ (rhoH A.X p 1 σ w) =
      dualBC p _ (LinearEquiv.baseChange ℤ_[p] ℚ_[p] _ _ φ (rhoH A.X p 1 σ w)) from rfl, h1, dualBC_comm]
  refine LinearMap.ext fun v => ?_
  rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.dualMap_apply]
  erw [LinearMap.comp_apply, galRep_apply_toKer]

/-- **Step C3, first paragraph and Milne's identification** (manuscript L10953-10972): for an abelian variety
`A` over a finite `F/ℚ_p`, `V_p(A)^∨ ≅ H¹_ét(A_{F̄}, ℚ_p)` is de Rham, and its `D_dR` has Hodge jumps in `[0, 1]`. -/
theorem dual_deRham_of_scholze (hS : ScholzeDeRhamAlg) (hT : T10Etale.T10_TateDuality) (hM : AvSplit.MumfordTorsionAlgClosed)
    (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) :
    IsDeRhamFam p (fun σ => (A.galRep p).dual σ) ∧ HodgeRange p (fun σ => (A.galRep p).dual σ) 1 := by
  have hp : (p : F) ≠ 0 := DeRhamPrint.natCast_p_ne_zero p F
  obtain ⟨hfree, hfin, -⟩ := DeRhamPrint.tateModuleFree_of_mumford hM F (DeRhamPrint.toKer A) p hp
  obtain ⟨φ, hφ⟩ := hT F (DeRhamPrint.toKer A) p hp
  haveI : IsProper A.X.hom := A.proper
  haveI : Smooth A.X.hom := A.smooth
  obtain ⟨h1, h2⟩ := hS p F A.X 1
  exact ⟨isDeRhamFam_of_equiv p (milneE p A φ) (milneE_comm p A φ hφ) h1,
    hodgeRange_of_equiv p (milneE p A φ) (milneE_comm p A φ hφ) 1 h2⟩

/-- **`V_p(A)` is de Rham** (manuscript L10966-10974: Milne's identification, then closure under duals,
Brinon–Conrad 5.2.1 and 6.3.3; here the duality is `DeRhamPrint.isDeRhamTensorOver_dual`, proved from `B_dR` a
field and `B_dR^{G_F} = F`, `bdRInvariantsPrinted_proof`). -/
theorem isDeRhamTensorOver_of_scholze (hS : ScholzeDeRhamAlg) (hT : T10Etale.T10_TateDuality) (hM : AvSplit.MumfordTorsionAlgClosed)
    (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) :
    IsDeRhamTensorOver p (A.galRep p) := by
  obtain ⟨⟨-, hD⟩, -⟩ := dual_deRham_of_scholze p hS hT hM F A
  obtain ⟨g, hg⟩ := dim_finite_I4 A
  haveI := (DeRhamPrint.finrank_V_of_tateModuleFree p (DeRhamPrint.tateModuleFree_of_mumford
    hM) (DeRhamPrint.natCast_p_ne_zero p F) A g hg).1
  have hDD : IsDeRhamTensorOver p (A.galRep p).dual.dual :=
    DeRhamPrint.isDeRhamTensorOver_dual p (BdRInv.bdRInvariantsPrinted_proof p F) _ hD
  have hfam : IsDeRhamFam p (fun σ => (A.galRep p).dual.dual σ) := ⟨inferInstance, hDD⟩
  have he : ∀ σ x, (Module.evalEquiv ℚ_[p] (A.V p)).symm ((A.galRep p).dual.dual σ x) =
      A.galRep p σ ((Module.evalEquiv ℚ_[p] (A.V p)).symm x) := by
    intro σ x
    obtain ⟨v, rfl⟩ := (Module.evalEquiv ℚ_[p] (A.V p)).surjective x
    rw [← evalEquiv_comm, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact (isDeRhamFam_of_equiv p (Module.evalEquiv ℚ_[p] (A.V p)).symm he hfam).2

end Main

/-- **The research field `deRhamVpAbVarDirect`** (Berger's form, `DeRhamPrintDirect.lean`) from the manuscript's
route: Scholze's comparison (`ScholzeDeRhamAlg`) and Milne's identification (`T10_TateDuality`). -/
theorem deRhamVpAbVarDirect_of_scholze (hS : ScholzeDeRhamAlg) (hT : T10Etale.T10_TateDuality)
    (hM : AvSplit.MumfordTorsionAlgClosed) :
    DeRhamPrint.Direct.DeRhamVpAbVarDirect :=
  fun p _ F _ _ _ A => (DeRhamPrint.Direct.isDeRhamTensorOver_iff p (A.galRep p)).mp
    (isDeRhamTensorOver_of_scholze p hS hT hM F A)

/-! ## §7. The Hodge–Tate row: weights read off the filtered de Rham comparison -/

/-- **GLUE (on-the-spot: the manuscript's "Consequently the Tate module has weights 0,0,−1,−1", L10995-10996;
Fontaine's theorem that a de Rham representation is Hodge–Tate with `gr D_dR ≅ D_HT`).** A finite-dimensional
de Rham representation `W` of `G_F` whose Hodge filtration has its jumps in `[0, 1]` (`HodgeRange … 1`) is
Hodge–Tate with weights in `{0, 1}` (cohomological convention). Stated for `W = V^∨` in the Hom form:
`Hom_{ℚ_p}(V, ℂ_p) ≅ ℂ_p^a ⊕ ℂ_p(−1)^b`, `G_F`-equivariantly (`G_F` acting by `f ↦ σ ∘ f ∘ ρ(σ)⁻¹`; this is
`ℂ_p ⊗ V^∨` for finite-dimensional `V`, htdecomp-or's `thetaEquiv`).
Proof sketch (report §4): `gr^j D_dR(W) ↪ (ℂ_p(j) ⊗ W)^{G_F}` (`gr^j B_dR ≅ ℂ_p(j)`), so `Σ_j dim_F (ℂ_p(j) ⊗ W)^{G_F}
≥ dim_F D_dR = dim W`; Tate's theorem gives `≤` and the injectivity of `⊕_j ℂ_p(−j) ⊗_F (ℂ_p(j) ⊗ W)^{G_F} → ℂ_p ⊗ W`,
hence an isomorphism, with only `j ∈ {0, 1}` occurring. -/
def DeRhamHodgeTate01 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (V : Type) [AddCommGroup V] [Module ℚ_[p] V] (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V),
    IsDeRhamFam p (fun σ => ρ.dual σ) → HodgeRange p (fun σ => ρ.dual σ) 1 →
    ∃ (a b : ℕ) (e : (V →ₗ[ℚ_[p]] ℂ_[p]) ≃ₗ[ℂ_[p]] (Fin a → ℂ_[p]) × (Fin b → ℂ_[p])),
      ∀ (σ : Field.absoluteGaloisGroup F) (f : V →ₗ[ℚ_[p]] ℂ_[p]),
        e (cpLin p (gfToGqp p F σ) ∘ₗ f ∘ₗ ρ σ⁻¹) =
          ((fun k => cpAct p (gfToGqp p F σ) ((e f).1 k)),
            (fun k => cycPow p (gfToGqp p F σ) (-1) • cpAct p (gfToGqp p F σ) ((e f).2 k)))

/-- **The Hodge–Tate decomposition of `V_p(A)`, Hom form** (htdecomp-or's `HodgeTateDecompHom`) from Scholze's
comparison, Milne's identification and `DeRhamHodgeTate01`. -/
theorem hodgeTateDecompHom_of_scholze (hS : ScholzeDeRhamAlg) (hT : T10Etale.T10_TateDuality)
    (hM : AvSplit.MumfordTorsionAlgClosed) (hW : DeRhamHodgeTate01) : ZInQ.Contrib.HodgeTateOr.HodgeTateDecompHom := by
  intro p _ F _ _ _ A
  obtain ⟨h1, h2⟩ := dual_deRham_of_scholze p hS hT hM F A
  exact hW p F (A.V p) (A.galRep p) h1 h2

/-- **The research field `hodgeTateDecompOr`** from the manuscript's route. -/
theorem hodgeTateDecompOr_of_scholze (hS : ScholzeDeRhamAlg) (hT : T10Etale.T10_TateDuality)
    (hM : AvSplit.MumfordTorsionAlgClosed) (hW : DeRhamHodgeTate01) : ZInQ.Contrib.HodgeTateOr.HodgeTateDecompOr :=
  ZInQ.Contrib.HodgeTateOr.or_of_hom (hodgeTateDecompHom_of_scholze hS hT hM hW)

/-! ## §8. The two research fields from the new leaves (Mumford's torsion theorem is proved in the tree) -/

/-- **`deRhamVpAbVarDirect` from Scholze's comparison and Milne's identification.** -/
theorem deRhamVpAbVarDirect_of_leaves (hS : ScholzeDeRhamAlg) (hT : T10Etale.T10_TateDuality) :
    DeRhamPrint.Direct.DeRhamVpAbVarDirect :=
  deRhamVpAbVarDirect_of_scholze hS hT ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof

/-- **`hodgeTateDecompOr` from Scholze's comparison, Milne's identification and `DeRhamHodgeTate01`.** -/
theorem hodgeTateDecompOr_of_leaves (hS : ScholzeDeRhamAlg) (hT : T10Etale.T10_TateDuality)
    (hW : DeRhamHodgeTate01) : ZInQ.Contrib.HodgeTateOr.HodgeTateDecompOr :=
  hodgeTateDecompOr_of_scholze hS hT ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof hW

/-- **The manuscript's lemma for `V_p(A)`** (`lem:de-rham-descent`, parts used by the two fields): `V_p(A)` is
de Rham, `V_p(A)^∨ = H¹_ét(A_{F̄}, ℚ_p)` is de Rham with Hodge jumps in `[0, 1]`, and (with `DeRhamHodgeTate01`)
`Hom(V_p(A), ℂ_p) ≅ ℂ_p^a ⊕ ℂ_p(−1)^b`, i.e. Hodge–Tate weights in `{0, −1}`. -/
theorem lemDeRhamDescent_tate (hS : ScholzeDeRhamAlg) (hT : T10Etale.T10_TateDuality) (p : ℕ) [Fact p.Prime]
    (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) :
    IsDeRhamTensorOver p (A.galRep p) ∧ IsDeRhamFam p (fun σ => (A.galRep p).dual σ) ∧
      HodgeRange p (fun σ => (A.galRep p).dual σ) 1 :=
  ⟨isDeRhamTensorOver_of_scholze p hS hT ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof F A,
    dual_deRham_of_scholze p hS hT ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof F A⟩

end

end DeRhamScholze
