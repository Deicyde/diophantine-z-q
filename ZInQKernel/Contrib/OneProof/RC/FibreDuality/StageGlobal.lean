import ZInQKernel.Contrib.OneProof.RC.FibreDuality.StageDuality
import ZInQKernel.Contrib.OneProof.RC.Limits.GradedConeDual

/-!
# Lane RC31, round 3, part 3: the stage global duality on the finite free model, as matrices

Manuscript `diophantine_zq.tex`: the retained data "include the integral duality maps, their
homotopy inverses, and the homotopies expressing compatibility of duality with localization"
(tex 4385–4388); Lemma `ex:limits-inner-limit` (tex 4391–4451): the diagram transports to the
finite free models by `f ↦ p′ f i` (tex 4439–4442), and "a quasi-isomorphism between these bounded
free models has an integral homotopy inverse" (tex 3790–3792).

For a graded finite free model `R` of the stage complex `X` and the stage pairing data `P`:
* `modelDualityMap R P = p′ ∘ Φ ∘ i`, the transport of the stage duality map `Φ` along the model
  retract of `X` and the dual of the model retract of `Cone(res)` (PROVED: a quasi-isomorphism
  whenever `Φ` is);
* in the coordinates of the model cone, its matrix is `forwardMatOf (modelGlob) loc (modelRes)`
  and the dual differential is `dualDiffMatOf dC (modelRes)` (PROVED);
* `exists_stageMatrixDiagram`: the homotopy inverse and both homotopies, extracted as matrices,
  give a `StageMatrixDiagram` whose model data are exactly `dC`, `modelRes`, `modelGlob`, `loc`
  (PROVED).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.FibreDuality

open CategoryTheory Matrix
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.InnerLimit (splitLocalComplex splitLocalTerms Vec2 Coords)
open ZInQ.Manuscript.RC.Limits (GRetract GradedModel matCx matCx_d_apply toCC_d_hom_eq
  homotopyOfIdentities toCC_ghomComp)

/-! ### Dual coordinates over a commutative ring -/

section Generic

variable {A : Type} [CommRing A]

/-- The linear form `w ↦ v ⬝ w`, over a commutative ring. Kind: definition. -/
def dotLinR {ι : Type} [Fintype ι] (v : ι → A) : (ι → A) →ₗ[A] A where
  toFun w := v ⬝ᵥ w
  map_add' w w' := dotProduct_add v w w'
  map_smul' c w := by
    rw [dotProduct_smul]
    rfl

/-- **The dual coordinates** of a coordinate system `e : V ≃ (ι → A)`: a linear form `φ` goes to
its values on the standard basis (the ring-generic form of `dualEquivOfCoord`; tex 4385–4388).
Kind: definition. -/
def dualEquivOfCoordR {V ι : Type} [AddCommGroup V] [Module A V] [Fintype ι] [DecidableEq ι]
    (e : V ≃ₗ[A] (ι → A)) : Module.Dual A V ≃ₗ[A] (ι → A) where
  toFun φ j := φ (e.symm (Pi.single j 1))
  map_add' φ ψ := rfl
  map_smul' c φ := rfl
  invFun v := dotLinR v ∘ₗ e.toLinearMap
  left_inv φ := by
    refine LinearMap.ext fun x => ?_
    change (fun j => φ (e.symm (Pi.single j 1))) ⬝ᵥ e x = φ x
    have h1 : φ x = φ (e.symm (∑ j, (e x) j • Pi.single j (1 : A))) := by
      rw [← coord_expandR, LinearEquiv.symm_apply_apply]
    rw [h1, map_sum, map_sum]
    simp only [map_smul, smul_eq_mul, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  right_inv v := by
    funext j
    change v ⬝ᵥ e (e.symm (Pi.single j 1)) = v j
    rw [LinearEquiv.apply_symm_apply, dotProduct_single, mul_one]

/-- Evaluation of the dual coordinates. Kind: PROVED. -/
theorem dualEquivOfCoordR_apply {V ι : Type} [AddCommGroup V] [Module A V] [Fintype ι]
    [DecidableEq ι] (e : V ≃ₗ[A] (ι → A)) (φ : Module.Dual A V) (j : ι) :
    dualEquivOfCoordR e φ j = φ (e.symm (Pi.single j 1)) :=
  rfl

/-- A linear form is the dot product of its dual coordinates with the coordinates. Kind:
PROVED. -/
theorem dualEquivOfCoordR_eval {V ι : Type} [AddCommGroup V] [Module A V] [Fintype ι]
    [DecidableEq ι] (e : V ≃ₗ[A] (ι → A)) (φ : Module.Dual A V) (x : V) :
    φ x = dualEquivOfCoordR e φ ⬝ᵥ e x := by
  conv_lhs => rw [← (dualEquivOfCoordR e).symm_apply_apply φ]
  rfl

/-- Characterization of the dual coordinates by evaluation. Kind: PROVED. -/
theorem dualEquivOfCoordR_eq {V ι : Type} [AddCommGroup V] [Module A V] [Fintype ι]
    [DecidableEq ι] (e : V ≃ₗ[A] (ι → A)) (φ : Module.Dual A V) (v : ι → A)
    (h : ∀ x, φ x = v ⬝ᵥ e x) : dualEquivOfCoordR e φ = v := by
  funext j
  rw [dualEquivOfCoordR_apply, h, LinearEquiv.apply_symm_apply, dotProduct_single, mul_one]

/-- The dot product of two block vectors. Kind: PROVED. -/
theorem sumElim_dotProductR {m n : Type} [Fintype m] [Fintype n] (u x : m → A) (v y : n → A) :
    Sum.elim u v ⬝ᵥ Sum.elim x y = u ⬝ᵥ x + v ⬝ᵥ y := by
  simp [dotProduct, Fintype.sum_sum_type]

/-- Multiplying a stacked matrix by a vector. Kind: PROVED. -/
theorem fromRows_mulVec_eqR {m₁ m₂ n : Type} [Fintype n] (M : Matrix m₁ n A) (N : Matrix m₂ n A)
    (x : n → A) : Matrix.fromRows M N *ᵥ x = Sum.elim (M *ᵥ x) (N *ᵥ x) := by
  funext i
  cases i <;> rfl

/-- The matrix identity behind `forwardMatOf`. Kind: PROVED. -/
theorem forward_matrix_cleanR {m n l l' : Type} [Fintype m] [Fintype n] [Fintype l] [Fintype l']
    (Mg : Matrix m n A) (Ml : Matrix l l' A) (Rka : Matrix l m A) (s : ℤ) (x : m → A)
    (b : n → A) (w : l' → A) :
    x ⬝ᵥ (Mg *ᵥ b) + s • ((Rka *ᵥ x) ⬝ᵥ (Ml *ᵥ w)) =
      (Mgᵀ *ᵥ x) ⬝ᵥ b + (((s : A) • (Mlᵀ * Rka)) *ᵥ x) ⬝ᵥ w := by
  rw [mulVec_dotProduct_eqR Mgᵀ, transpose_transpose, smul_mulVec, ← mulVec_mulVec,
    smul_dotProduct, mulVec_dotProduct_eqR Mlᵀ, transpose_transpose, zsmul_eq_mul, smul_eq_mul]

end Generic

/-! ### The model cone and its coordinates -/

section ModelCone

variable {A : Type} [CommRing A] {X : GCx A} (R : GradedModel X) (P : StagePairingInput X)

/-- The localization of the model, `res ∘ i`, as a chain map (tex 4439–4440). Kind:
definition. -/
abbrev modelResHom : GHom R.modelCx (splitLocalComplex A) := ghomComp R.retract.i P.res

/-- The compactly supported model complex `Cone(res ∘ i)[−1]`. Kind: definition. -/
abbrev modelCone : GCx A := coneCx (modelResHom R P)

/-- **The coordinates of the model cone**: the model part as is, the split-model part through
`lCoordR` (tex 4385–4388). Kind: definition. -/
def modelConeCoord (m : ℤ) : (modelCone R P).X m ≃ₗ[A] (cIdxOf R.rank m → A) :=
  ((LinearEquiv.refl A (Fin (R.rank m) → A)).prodCongr (lCoordR A (m - 1))).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin (R.rank m)) (lIdx (m - 1)) A A).symm

/-- The coordinates of a pair `(b, y)`. Kind: PROVED. -/
theorem modelConeCoord_mk (m : ℤ) (b : Fin (R.rank m) → A)
    (y : (splitLocalComplex A).X (m - 1)) :
    modelConeCoord R P m (b, y) = Sum.elim b (lCoordR A (m - 1) y) := by
  funext s
  cases s <;> rfl

/-- **The coordinates of the dual model cone** `Hom(Cone(res ∘ i)[−1], A)[−3]` in degree `n`.
Kind: definition. -/
def modelDualCoord (n : ℤ) :
    (dualCx (modelCone R P) 3).X n ≃ₗ[A] (cIdxOf R.rank (3 - n) → A) :=
  dualEquivOfCoordR (modelConeCoord R P (3 - n))

/-- Evaluation of the dual coordinates. Kind: PROVED. -/
theorem modelDualCoord_apply (n : ℤ) (φ : (dualCx (modelCone R P) 3).X n)
    (j : cIdxOf R.rank (3 - n)) :
    modelDualCoord R P n φ j = asDual φ ((modelConeCoord R P (3 - n)).symm (Pi.single j 1)) :=
  rfl

/-- The model localization along an index equality, in coordinates. Kind: PROVED. -/
theorem lCoordR_modelRes_at (m n : ℤ) (h : m = n) (x : Fin (R.rank m) → A) :
    lCoordR A n ((modelResHom R P).f m n h x) = RkAtOf (modelRes R P) m n h *ᵥ x := by
  subst h
  exact (modelRes_mulVec R P m x).symm

/-- **The differential of the model cone in coordinates** is `compactDiffMatOf`. Kind:
PROVED. -/
theorem modelConeCoord_d (m m' : ℤ) (h : m + 1 = m') (z : (modelCone R P).X m) :
    modelConeCoord R P m' ((modelCone R P).d m m' h z) =
      compactDiffMatOf R.dC (modelRes R P) m m' h *ᵥ modelConeCoord R P m z := by
  obtain ⟨b, y⟩ := z
  revert b y
  change ∀ (b : Fin (R.rank m) → A) (y : (splitLocalComplex A).X (m - 1)), _
  intro b y
  change modelConeCoord R P m'
      (R.dC m m' h *ᵥ b,
        ((modelResHom R P).f m (m' - 1) (by omega) b - 0 :
          (splitLocalComplex A).X (m' - 1))) =
    compactDiffMatOf R.dC (modelRes R P) m m' h *ᵥ modelConeCoord R P m (b, y)
  rw [modelConeCoord_mk, modelConeCoord_mk, compactDiffMatOf, fromBlocks_mulVec, sub_zero,
    lCoordR_modelRes_at]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, add_zero]

/-- **The differential of the dual model cone in coordinates** is `dualDiffMatOf`. Kind:
PROVED. -/
theorem modelDualCoord_d (a b : ℤ) (h : a + 1 = b) (φ : (dualCx (modelCone R P) 3).X a) :
    modelDualCoord R P b ((dualCx (modelCone R P) 3).d a b h φ) =
      dualDiffMatOf R.dC (modelRes R P) a b h *ᵥ modelDualCoord R P a φ := by
  funext j
  rw [modelDualCoord_apply, dualCx_d_apply]
  have e := dualEquivOfCoordR_eval (modelConeCoord R P (3 - a)) (asDual φ)
    ((modelCone R P).d (3 - b) (3 - a) (by omega)
      ((modelConeCoord R P (3 - b)).symm (Pi.single j 1)))
  rw [modelConeCoord_d, LinearEquiv.apply_symm_apply] at e
  rw [e]
  change (-(sgn a)) • (modelDualCoord R P a φ ⬝ᵥ
    (compactDiffMatOf R.dC (modelRes R P) (3 - b) (3 - a) (by omega) *ᵥ Pi.single j 1)) = _
  rw [dualDiffMatOf]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.mul_sum, zsmul_eq_mul, mul_comm]
  simp only [mul_assoc]
  exact add_comm _ _

end ModelCone

/-! ### The transported global duality map -/

section Duality

variable {A : Type} [CommRing A] {X : GCx A} (R : GradedModel X) (P : StagePairingInput X)

/-- **The global duality map of the model**: the transport `p′ Φ i` of the stage duality map `Φ`
along the model retract of `X` and the dual of the model retract of `Cone(res)[−1]` (tex
4439–4442: "Transport any fixed finite collection of arithmetic maps by `f ↦ p′fi`"). Kind:
definition. -/
def modelDualityMap : GHom R.modelCx (dualCx (modelCone R P) 3) :=
  R.retract.transportMap ((R.retract.cone P.res).dual 3) (stageDualityMap P)

/-- The transported duality map is a quasi-isomorphism when the stage duality map is (tex
4385–4388, 4439–4442). Kind: PROVED. -/
theorem quasiIso_modelDualityMap (hΦ : QuasiIso (GHom.toCC (stageDualityMap P))) :
    QuasiIso (GHom.toCC (modelDualityMap R P)) :=
  R.retract.quasiIso_transportMap _ _ hΦ

/-- Evaluation of the transported duality map: `(b, y) ↦ glob(i x, i b) + (−1)^a loc(res i x, y)`.
Kind: PROVED (definitional). -/
theorem modelDualityMap_eval (a : ℤ) (x : Fin (R.rank a) → A) (b : Fin (R.rank (3 - a)) → A)
    (y : (splitLocalComplex A).X (3 - a - 1)) :
    asDual ((modelDualityMap R P).f a a rfl x) ((b, y) : (modelCone R P).X (3 - a)) =
      P.glob a (3 - a) (by omega) (modelIncl R a x) (modelIncl R (3 - a) b) +
        sgn a • locForm P.loc a (3 - a - 1) (P.res.f a a rfl (modelIncl R a x)) y :=
  rfl

/-- **The transported duality map in coordinates** is `forwardMatOf (modelGlob) loc (modelRes)`
(tex 4385–4388; Nekovář, *Selmer complexes*, 5.4.3). Kind: PROVED. -/
theorem modelDualCoord_forward (a : ℤ) (x : Fin (R.rank a) → A) :
    modelDualCoord R P a ((modelDualityMap R P).f a a rfl x) =
      forwardMatOf (modelGlob R P) P.loc (modelRes R P) a *ᵥ x := by
  apply dualEquivOfCoordR_eq
  intro z
  obtain ⟨b, y⟩ := z
  revert b y
  change ∀ (b : Fin (R.rank (3 - a)) → A) (y : (splitLocalComplex A).X (3 - a - 1)), _
  intro b y
  rw [modelConeCoord_mk, forwardMatOf, fromRows_mulVec_eqR, sumElim_dotProductR]
  refine (modelDualityMap_eval R P a x b y).trans ?_
  rw [← modelGlob_form R P a (3 - a) (by omega) x b, locForm_apply, ← modelRes_mulVec]
  exact forward_matrix_cleanR (modelGlob R P a (3 - a) (by omega)) (P.loc a (3 - a - 1))
    (modelRes R P a) (sgn a) x b (lCoordR A (3 - a - 1) y)

/-- **The dual model cone in coordinates**: the complex `cIdx (3 − a) → A` with the matrix
differentials `dualDiffMatOf dC (modelRes)` (tex 4385–4388). Kind: definition. -/
def modelDualMatCx : GCx A where
  X a := ModuleCat.of A (cIdxOf R.rank (3 - a) → A)
  d a b h := Matrix.toLin' (dualDiffMatOf R.dC (modelRes R P) a b h)
  d_d a b c hab hbc v := by
    change dualDiffMatOf R.dC (modelRes R P) b c hbc *ᵥ
      (dualDiffMatOf R.dC (modelRes R P) a b hab *ᵥ v) = 0
    obtain ⟨φ, rfl⟩ := (modelDualCoord R P a).surjective v
    rw [← modelDualCoord_d, ← modelDualCoord_d, (dualCx (modelCone R P) 3).d_d, map_zero]

/-- The differential of the coordinate complex. Kind: PROVED (definitional). -/
theorem modelDualMatCx_d_apply (a b : ℤ) (h : a + 1 = b) (v : cIdxOf R.rank (3 - a) → A) :
    (modelDualMatCx R P).d a b h v = dualDiffMatOf R.dC (modelRes R P) a b h *ᵥ v :=
  rfl

/-- The coordinate isomorphism onto the coordinate complex, as a chain map. Kind: definition
(PROVED chain property). -/
def modelDualCoordHom : GHom (dualCx (modelCone R P) 3) (modelDualMatCx R P) where
  f a b h := by
    subst h
    exact (modelDualCoord R P a).toLinearMap
  comm a a₁ b b₁ hab h₁ h₂ hb φ := by
    subst hab hb
    exact modelDualCoord_d R P a a₁ h₁ φ

/-- The inverse coordinates intertwine the differentials. Kind: PROVED. -/
theorem modelDualCoord_symm_d (a b : ℤ) (h : a + 1 = b) (v : cIdxOf R.rank (3 - a) → A) :
    (modelDualCoord R P b).symm (dualDiffMatOf R.dC (modelRes R P) a b h *ᵥ v) =
      (dualCx (modelCone R P) 3).d a b h ((modelDualCoord R P a).symm v) := by
  rw [LinearEquiv.symm_apply_eq, modelDualCoord_d, LinearEquiv.apply_symm_apply]

/-- The inverse coordinate isomorphism, as a chain map. Kind: definition (PROVED chain
property). -/
def modelDualCoordInv : GHom (modelDualMatCx R P) (dualCx (modelCone R P) 3) where
  f a b h := by
    subst h
    exact (modelDualCoord R P a).symm.toLinearMap
  comm a a₁ b b₁ hab h₁ h₂ hb v := by
    subst hab hb
    exact modelDualCoord_symm_d R P a a₁ h₁ v

/-- **The coordinate isomorphism** of the dual model cone with its coordinate complex, as a
homotopy equivalence (with zero homotopies). Kind: definition (PROVED identities). -/
def modelDualCoordEquiv :
    HomotopyEquiv (dualCx (modelCone R P) 3).toCC (modelDualMatCx R P).toCC where
  hom := GHom.toCC (modelDualCoordHom R P)
  inv := GHom.toCC (modelDualCoordInv R P)
  homotopyHomInvId := Homotopy.ofEq (by
    ext n φ
    exact (modelDualCoord R P n).symm_apply_apply φ)
  homotopyInvHomId := Homotopy.ofEq (by
    ext n v
    exact (modelDualCoord R P n).apply_symm_apply v)

end Duality

/-! ### The split model is finite free and bounded -/

section SplitLocal

variable {A : Type} [CommRing A]

/-- The terms of the split model are free. Kind: PROVED (instance). -/
instance splitLocal_free (n : ℤ) : Module.Free A ((splitLocalComplex A).X n) :=
  Module.Free.of_equiv (lCoordR A n).symm

/-- The terms of the split model are finite. Kind: PROVED (instance). -/
instance splitLocal_finite (n : ℤ) : Module.Finite A ((splitLocalComplex A).X n) :=
  Module.Finite.equiv (lCoordR A n).symm

/-- The split model vanishes outside the degrees `0, 1, 2` (tex 4860). Kind: PROVED. -/
theorem splitLocal_subsingleton (k : ℤ) (hk : k < 0 ∨ 2 < k) :
    Subsingleton ((splitLocalComplex A).X k) := by
  match k, hk with
  | .ofNat 0, hk => exact absurd hk (by decide)
  | .ofNat 1, hk => exact absurd hk (by decide)
  | .ofNat 2, hk => exact absurd hk (by decide)
  | .ofNat (m + 3), _ => exact inferInstanceAs (Subsingleton PUnit)
  | .negSucc m, _ => exact inferInstanceAs (Subsingleton PUnit)

end SplitLocal

/-! ### Extraction of the reverse map and the homotopies as matrices -/

section Extraction

variable {A : Type} [CommRing A] {X : GCx A} (R : GradedModel X) (P : StagePairingInput X)
variable (e : HomotopyEquiv R.modelCx.toCC (modelDualMatCx R P).toCC)

/-- The forward map of a homotopy equivalence in degree `a`, with plain types. Kind:
definition. -/
def fwdLin (a : ℤ) : (Fin (R.rank a) → A) →ₗ[A] (cIdxOf R.rank (3 - a) → A) := (e.hom.f a).hom

/-- The reverse map of a homotopy equivalence in degree `a`, with plain types. Kind:
definition. -/
def revLin (a : ℤ) : (cIdxOf R.rank (3 - a) → A) →ₗ[A] (Fin (R.rank a) → A) := (e.inv.f a).hom

/-- The source homotopy, with plain types. Kind: definition. -/
def srcLin (a b : ℤ) : (Fin (R.rank a) → A) →ₗ[A] (Fin (R.rank b) → A) :=
  (e.homotopyHomInvId.hom a b).hom

/-- The target homotopy, with plain types. Kind: definition. -/
def tgtLin (a b : ℤ) : (cIdxOf R.rank (3 - a) → A) →ₗ[A] (cIdxOf R.rank (3 - b) → A) :=
  (e.homotopyInvHomId.hom a b).hom

/-- **The reverse map as matrices** (tex 4385–4388: "their homotopy inverses"). Kind:
definition. -/
def revOf (a : ℤ) : Matrix (Fin (R.rank a)) (cIdxOf R.rank (3 - a)) A :=
  LinearMap.toMatrix' (revLin R P e a)

/-- **The source homotopy as matrices**. Kind: definition. -/
def srcOf (a b : ℤ) (_h : b + 1 = a) : Matrix (Fin (R.rank b)) (Fin (R.rank a)) A :=
  LinearMap.toMatrix' (srcLin R P e a b)

/-- **The target homotopy as matrices**. Kind: definition. -/
def tgtOf (a b : ℤ) (_h : b + 1 = a) :
    Matrix (cIdxOf R.rank (3 - b)) (cIdxOf R.rank (3 - a)) A :=
  LinearMap.toMatrix' (tgtLin R P e a b)

/-- Two matrices agreeing on all vectors are equal. Kind: PROVED. -/
theorem matrix_eq_of_mulVec {m n : Type} [Fintype n] [DecidableEq n] (M N : Matrix m n A)
    (h : ∀ v, M *ᵥ v = N *ᵥ v) : M = N := by
  ext i j
  have e := congrFun (h (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at e
  exact e

/-- The differential of `toCC` as a morphism. Kind: PROVED. -/
theorem toCC_d_eq (C : GCx A) (a b : ℤ) (h : a + 1 = b) :
    C.toCC.d a b = ModuleCat.ofHom (C.d a b h) :=
  dite_eq_left h

/-- The reverse map is a chain map, pointwise. Kind: PROVED. -/
theorem revLin_comm (a : ℤ) (v : cIdxOf R.rank (3 - a) → A) :
    revLin R P e (a + 1) (dualDiffMatOf R.dC (modelRes R P) a (a + 1) rfl *ᵥ v) =
      R.dC a (a + 1) rfl *ᵥ revLin R P e a v := by
  have hc := e.inv.comm a (a + 1)
  rw [toCC_d_eq _ a (a + 1) rfl, toCC_d_eq _ a (a + 1) rfl] at hc
  exact (congrArg (fun g => ModuleCat.Hom.hom g v) hc).symm

/-- The first homotopy-inverse identity, pointwise. Kind: PROVED. -/
theorem revLin_src (a : ℤ) (x : Fin (R.rank a) → A) :
    revLin R P e a (fwdLin R P e a x) =
      srcLin R P e (a + 1) a (R.dC a (a + 1) rfl *ᵥ x) +
        R.dC (a - 1) a (by omega) *ᵥ srcLin R P e a (a - 1) x + x := by
  have hprev : (a - 1) + 1 = a := by omega
  have hc := e.homotopyHomInvId.comm a
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel a (a + 1) from rfl),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel (a - 1) a from hprev),
    toCC_d_eq _ a (a + 1) rfl, toCC_d_eq _ (a - 1) a hprev] at hc
  exact congrArg (fun g => ModuleCat.Hom.hom g x) hc

/-- The second homotopy-inverse identity, pointwise. Kind: PROVED. -/
theorem revLin_tgt (a : ℤ) (v : cIdxOf R.rank (3 - a) → A) :
    fwdLin R P e a (revLin R P e a v) =
      tgtLin R P e (a + 1) a (dualDiffMatOf R.dC (modelRes R P) a (a + 1) rfl *ᵥ v) +
        dualDiffMatOf R.dC (modelRes R P) (a - 1) a (by omega) *ᵥ tgtLin R P e a (a - 1) v +
          v := by
  have hprev : (a - 1) + 1 = a := by omega
  have hc := e.homotopyInvHomId.comm a
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel a (a + 1) from rfl),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel (a - 1) a from hprev),
    toCC_d_eq _ a (a + 1) rfl, toCC_d_eq _ (a - 1) a hprev] at hc
  exact congrArg (fun g => ModuleCat.Hom.hom g v) hc

/-- **The reverse map is a chain map**, as matrices. Kind: PROVED. -/
theorem revOf_chain (a : ℤ) :
    revOf R P e (a + 1) * dualDiffMatOf R.dC (modelRes R P) a (a + 1) rfl -
      R.dC a (a + 1) rfl * revOf R P e a = 0 := by
  rw [sub_eq_zero]
  refine matrix_eq_of_mulVec _ _ fun v => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, revOf, revOf, LinearMap.toMatrix'_mulVec,
    LinearMap.toMatrix'_mulVec, revLin_comm]

variable {R P e}

/-- **The first homotopy-inverse identity**, as matrices, given the forward map in coordinates.
Kind: PROVED. -/
theorem revOf_src
    (hfwd : ∀ a x, fwdLin R P e a x = forwardMatOf (modelGlob R P) P.loc (modelRes R P) a *ᵥ x)
    (a : ℤ) :
    revOf R P e a * forwardMatOf (modelGlob R P) P.loc (modelRes R P) a -
        srcOf R P e (a + 1) a rfl * R.dC a (a + 1) rfl -
        R.dC (a - 1) a (by omega) * srcOf R P e a (a - 1) (by omega) - 1 = 0 := by
  rw [sub_eq_zero, sub_eq_iff_eq_add, sub_eq_iff_eq_add]
  refine matrix_eq_of_mulVec _ _ fun x => ?_
  rw [← mulVec_mulVec, ← hfwd, revOf, LinearMap.toMatrix'_mulVec, revLin_src, add_mulVec,
    add_mulVec, one_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, srcOf, srcOf,
    LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
  abel

/-- **The second homotopy-inverse identity**, as matrices, given the forward map in coordinates.
Kind: PROVED. -/
theorem revOf_tgt
    (hfwd : ∀ a x, fwdLin R P e a x = forwardMatOf (modelGlob R P) P.loc (modelRes R P) a *ᵥ x)
    (a : ℤ) :
    forwardMatOf (modelGlob R P) P.loc (modelRes R P) a * revOf R P e a -
        tgtOf R P e (a + 1) a rfl * dualDiffMatOf R.dC (modelRes R P) a (a + 1) rfl -
        dualDiffMatOf R.dC (modelRes R P) (a - 1) a (by omega) *
          tgtOf R P e a (a - 1) (by omega) - 1 = 0 := by
  rw [sub_eq_zero, sub_eq_iff_eq_add, sub_eq_iff_eq_add]
  refine matrix_eq_of_mulVec _ _ fun v => ?_
  rw [← mulVec_mulVec, revOf, LinearMap.toMatrix'_mulVec, ← hfwd, revLin_tgt, add_mulVec,
    add_mulVec, one_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, tgtOf, tgtOf,
    LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
  abel

end Extraction

/-! ### The stage matrix diagram of a stage -/

section Diagram

variable {A : Type} [CommRing A] {X : GCx A} (R : GradedModel X) (P : StagePairingInput X)

/-- **The stage matrix diagram** (tex 4385–4388, 4391–4451, one stage): for a graded finite free
model `R` of the stage complex (ranks vanishing outside `[lo, hi]`) and stage pairing data `P`
whose duality map is a quasi-isomorphism (Nekovář, *Selmer complexes*, 5.4.3 at the stage), the
transported diagram — the model differentials, the model localization `res ∘ i`, the model trace
pairing `glob(i ·, i ·)`, the local pairing, the reverse map of the transported duality map and
both homotopies — is a `StageMatrixDiagram` with exact identities. Kind: PROVED. -/
theorem exists_stageMatrixDiagram (hΦ : QuasiIso (GHom.toCC (stageDualityMap P))) (lo hi : ℤ)
    (hr : ∀ k, k < lo ∨ hi < k → R.rank k = 0) :
    ∃ S : StageMatrixDiagram A R.rank, S.dC = R.dC ∧ S.res = modelRes R P ∧
      S.glob = modelGlob R P ∧ S.loc = P.loc := by
  obtain ⟨e₀, he₀⟩ := ZInQ.Manuscript.RC.Limits.exists_homotopyEquiv_of_quasiIso_matCx
    (modelResHom R P) 3 (min (min lo (3 - hi)) (-3))
    (max (max hi (3 - lo)) 6) (fun k hk => hr k (by omega)) (fun k hk => hr k (by omega))
    (fun k hk => splitLocal_subsingleton k (by omega)) (modelDualityMap R P)
    (quasiIso_modelDualityMap R P hΦ)
  let e := e₀.trans (modelDualCoordEquiv R P)
  have hfwd : ∀ a x, fwdLin R P e a x =
      forwardMatOf (modelGlob R P) P.loc (modelRes R P) a *ᵥ x := by
    intro a x
    change ((e₀.hom ≫ GHom.toCC (modelDualCoordHom R P)).f a).hom x = _
    rw [he₀]
    exact modelDualCoord_forward R P a x
  exact ⟨⟨R.dC, R.dC_sq, modelRes R P, modelRes_comm R P, modelGlob R P, P.loc, modelRecip R P,
    revOf R P e, srcOf R P e, tgtOf R P e, revOf_chain R P e, revOf_src hfwd, revOf_tgt hfwd⟩,
    rfl, rfl, rfl, rfl⟩

end Diagram

/-! ### The converse: matrix identities give the quasi-isomorphism -/

section Converse

variable {A : Type} [CommRing A] {X : GCx A} (R : GradedModel X) (P : StagePairingInput X)

/-- The transported duality map in coordinates, as a chain map. Kind: definition. -/
def modelForwardHom : GHom R.modelCx (modelDualMatCx R P) :=
  ghomComp (modelDualityMap R P) (modelDualCoordHom R P)

/-- Its components are `forwardMatOf`. Kind: PROVED. -/
theorem modelForwardHom_apply (a : ℤ) (x : Fin (R.rank a) → A) :
    (modelForwardHom R P).f a a rfl x =
      forwardMatOf (modelGlob R P) P.loc (modelRes R P) a *ᵥ x :=
  modelDualCoord_forward R P a x

variable (S : StageMatrixDiagram A R.rank)

/-- The chain identity of the reverse map, pointwise. Kind: PROVED. -/
theorem diagramRev_comm (hd : S.dC = R.dC) (hres : S.res = modelRes R P) (a : ℤ)
    (v : cIdxOf R.rank (3 - a) → A) :
    S.rev (a + 1) *ᵥ (dualDiffMatOf R.dC (modelRes R P) a (a + 1) rfl *ᵥ v) =
      R.dC a (a + 1) rfl *ᵥ (S.rev a *ᵥ v) := by
  have hc := S.chain a
  rw [hd, hres, sub_eq_zero] at hc
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hc]

/-- The reverse map of a stage matrix diagram, as a chain map. Kind: definition (PROVED chain
property). -/
def diagramRevHom (hd : S.dC = R.dC) (hres : S.res = modelRes R P) :
    GHom (modelDualMatCx R P) R.modelCx where
  f a b h := by
    subst h
    exact Matrix.toLin' (S.rev a)
  comm a a₁ b b₁ hab h₁ h₂ hb v := by
    subst hab hb h₁
    exact diagramRev_comm R P S hd hres a v

/-- **The homotopy equivalence of a stage matrix diagram** whose model data are those of `R`
and `P`: forward map `forwardMatOf`, reverse map `rev`, homotopies `srcHom` and `tgtHom`
(tex 3790–3792, 4385–4388). Kind: definition (PROVED identities). -/
def diagramHomotopyEquiv (hd : S.dC = R.dC) (hres : S.res = modelRes R P)
    (hglob : S.glob = modelGlob R P) (hloc : S.loc = P.loc) :
    HomotopyEquiv R.modelCx.toCC (modelDualMatCx R P).toCC where
  hom := GHom.toCC (modelForwardHom R P)
  inv := GHom.toCC (diagramRevHom R P S hd hres)
  homotopyHomInvId := homotopyOfIdentities _ _ (fun a b hab => Matrix.toLin' (S.srcHom a b hab))
    (by
      intro a
      erw [toCC_d_hom_eq R.modelCx a (a + 1) rfl, toCC_d_hom_eq R.modelCx (a - 1) a (by omega)]
      apply LinearMap.ext
      intro (x : Fin (R.rank a) → A)
      change S.rev a *ᵥ ((modelForwardHom R P).f a a rfl x) =
        S.srcHom (a + 1) a rfl *ᵥ (R.dC a (a + 1) rfl *ᵥ x) +
          R.dC (a - 1) a (by omega) *ᵥ (S.srcHom a (a - 1) (by omega) *ᵥ x) + x
      have hs := S.src a
      rw [hd, hres, hglob, hloc] at hs
      have hs' : S.rev a * forwardMatOf (modelGlob R P) P.loc (modelRes R P) a =
          S.srcHom (a + 1) a rfl * R.dC a (a + 1) rfl +
            R.dC (a - 1) a (by omega) * S.srcHom a (a - 1) (by omega) + 1 := by
        rw [← sub_eq_zero, ← hs]
        abel
      rw [modelForwardHom_apply, Matrix.mulVec_mulVec, hs', Matrix.add_mulVec, Matrix.add_mulVec,
        Matrix.one_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec])
  homotopyInvHomId := homotopyOfIdentities _ _ (fun a b hab => Matrix.toLin' (S.tgtHom a b hab))
    (by
      intro a
      erw [toCC_d_hom_eq (modelDualMatCx R P) a (a + 1) rfl,
        toCC_d_hom_eq (modelDualMatCx R P) (a - 1) a (by omega)]
      apply LinearMap.ext
      intro (v : cIdxOf R.rank (3 - a) → A)
      change (modelForwardHom R P).f a a rfl (S.rev a *ᵥ v) =
        S.tgtHom (a + 1) a rfl *ᵥ (dualDiffMatOf R.dC (modelRes R P) a (a + 1) rfl *ᵥ v) +
          dualDiffMatOf R.dC (modelRes R P) (a - 1) a (by omega) *ᵥ
            (S.tgtHom a (a - 1) (by omega) *ᵥ v) + v
      have hs := S.tgt a
      rw [hd, hres, hglob, hloc] at hs
      have hs' : forwardMatOf (modelGlob R P) P.loc (modelRes R P) a * S.rev a =
          S.tgtHom (a + 1) a rfl * dualDiffMatOf R.dC (modelRes R P) a (a + 1) rfl +
            dualDiffMatOf R.dC (modelRes R P) (a - 1) a (by omega) *
              S.tgtHom a (a - 1) (by omega) + 1 := by
        rw [← sub_eq_zero, ← hs]
        abel
      rw [modelForwardHom_apply, Matrix.mulVec_mulVec, hs', Matrix.add_mulVec, Matrix.add_mulVec,
        Matrix.one_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec])

/-- **The converse of `exists_stageMatrixDiagram`**: a stage matrix diagram whose model data are
those of `R` and `P` makes the stage duality map a quasi-isomorphism (by two out of three along
the model retracts and the coordinate isomorphism). Kind: PROVED. -/
theorem quasiIso_stageDualityMap_of_diagram (hd : S.dC = R.dC) (hres : S.res = modelRes R P)
    (hglob : S.glob = modelGlob R P) (hloc : S.loc = P.loc) :
    QuasiIso (GHom.toCC (stageDualityMap P)) := by
  have h1 : QuasiIso (GHom.toCC (modelForwardHom R P)) :=
    (diagramHomotopyEquiv R P S hd hres hglob hloc).quasiIso_hom
  have hc : QuasiIso (GHom.toCC (modelDualCoordHom R P)) := (modelDualCoordEquiv R P).quasiIso_hom
  rw [modelForwardHom, toCC_ghomComp] at h1
  have h2 : QuasiIso (GHom.toCC (modelDualityMap R P)) :=
    quasiIso_of_comp_right _ (GHom.toCC (modelDualCoordHom R P))
  rw [modelDualityMap, GRetract.toCC_transportMap] at h2
  have hi := R.retract.quasiIso_i
  have hp := ((R.retract.cone P.res).dual 3).quasiIso_p
  have h3 : QuasiIso (GHom.toCC (stageDualityMap P) ≫
      GHom.toCC ((R.retract.cone P.res).dual 3).p) :=
    quasiIso_of_comp_left (GHom.toCC R.retract.i) _
  exact quasiIso_of_comp_right _ (GHom.toCC ((R.retract.cone P.res).dual 3).p)

end Converse

end ZInQ.Manuscript.RC.FibreDuality
