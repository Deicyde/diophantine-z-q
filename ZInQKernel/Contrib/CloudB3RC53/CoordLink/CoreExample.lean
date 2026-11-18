import ZInQKernel.Contrib.CloudB3RC53.CoordLink.RelCore
import ZInQKernel.Contrib.CloudB3RC53.CoordLink.NonVacuity

/-!
# E1a, part 6: a non-degenerate consistency instance (LESSON 2)

All hypotheses of `coordLink_of_triangles_core` hold together for lane ClearingComplex's witness
`identification2_example` (old part `H₁ --0--> H₂`, one genuine tame new place with block `t`),
with a NONZERO corrected coordinate `ũ = −t`:

* the (4.7) data `trianglesEx` (no unused primes, `η = 1`, `u_rel = u_prim = ũ = −t`);
* the integral two-term core `coreEx` (`D = (0)`, class `1`, functional `−t`; its augmented complex
  over `Frac 𝒪` is exact);
* `preCoreLink_ex`: `PreCoreLink` holds — both sides equal `−t`: the pre-cancellation complex gives
  `−det B · α β = −t` (`kmCoord_pre_block`) and the core gives RC15's coordinate `−t`
  (`kmCoord_twoTerm`);
* `coordLink_coreExample`: E1a for this instance.

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.CoordLink

open Matrix ZInQ.Contrib.CloudB3RC53.Torsion ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup evK uK sgnChar)

/-- `ũ = −t`. -/
def uEx : PowerSeries ℚ_[2] := ιQ (-PowerSeries.X)

/-- Interface data with `ũ = u_prim = −t`. -/
def ddEx (ℓ : ℕ) : RCData ℓ :=
  { ddZero ℓ with uTilde := fun _ _ => uEx, uPrim := fun _ _ => uEx }

theorem repEx (ℓ : ℕ) (F : Family) :
    UTildeRep (ddEx ℓ) F (fun _ => 0) (fun _ => -PowerSeries.X) := by
  intro x j
  simp only [ddEx, uEx, map_neg, coeff_ιQ, pow_zero, div_one]
  push_cast; rfl

/-- The (4.7) data: no unused primes, `η = 1`, `u_rel = ũ`. -/
def trianglesEx (ℓ : ℕ) (F : Family) (x : Addr F.b) : CommonCoordinateTrianglesN (ddEx ℓ) F x where
  R := PowerSeries ℚ_[2]
  chi := RingHom.id _
  Q := ∅
  v _ := 0
  g _ := 1
  l _ := 1
  e _ := 1
  ei _ := 1
  hsign := by simp
  hratio := by simp
  hinv := by simp
  urel := uEx
  U := ∅
  hU := by simp
  hutilde := by simp [Central.eta, ddEx]
  qn _ := 1
  hodd := by simp
  F _ := 1
  a _ := 0
  z _ := 1
  zi _ := 1
  ha := by simp
  hd := by simp
  hl := by simp
  he := by simp
  u _ := uEx
  hrel := rfl
  hprim := rfl
  eps _ := 1
  hstep := by simp

theorem hunitEx {b : ℕ} (x : Addr b) :
    IsUnit (Determinant.signEval (sgnChar x) (1 : MonoidAlgebra Lam (SignGroup b))) := by
  simp

theorem hcompatEx (ℓ : ℕ) (F : Family) (x : Addr F.b) :
    (trianglesEx ℓ F x).chi (Central.eta (trianglesEx ℓ F x).Q (trianglesEx ℓ F x).v
      (trianglesEx ℓ F x).g) = ιQ (Determinant.signEval (sgnChar x) 1) := by
  change (∏ q ∈ (∅ : Finset ℕ), Central.correctionFactor (0 : PowerSeries ℚ_[2]) 1) =
    ιQ (Determinant.signEval (sgnChar x) 1)
  rw [Finset.prod_empty, map_one, map_one]

theorem algebraMap_X_ne_zero : algebraMap Lam OO PowerSeries.X ≠ 0 := by
  rw [Determinant.algebraMap_eq_lamToO]
  exact (map_ne_zero_iff _ Determinant.lamToO_injective).mpr PowerSeries.X_ne_zero

theorem ψO_X_ne_zero : ψO PowerSeries.X ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective OO (FractionRing OO))).mpr algebraMap_X_ne_zero

/-- The integral core: `D = (0)`, class `1`, functional `−t`. -/
def coreEx : IntegralCore where
  n := 1
  D := 0
  zc _ := 1
  wc _ := -PowerSeries.X
  hz := by simp [twoTerm]
  hw := by simp [twoTerm]
  exact := by
    refine ⟨fun v hv => ?_, fun y _ => ?_, fun y hy => ?_, fun y => ?_⟩
    · funext i
      rcases i with i | i
      · exact i.elim
      · have := congrFun hv 0
        simpa [FourCx.aug, mulVec, dotProduct, Fintype.sum_sum_type] using this
    · refine ⟨Sum.elim (fun e => e.elim) (fun _ => y 0), ?_⟩
      funext i
      fin_cases i
      simp [FourCx.aug, mulVec, dotProduct, Fintype.sum_sum_type]
    · refine ⟨0, ?_⟩
      have := congrFun hy (Sum.inr ())
      simp [FourCx.aug, mulVec, dotProduct] at this
      funext i
      fin_cases i
      simp only [twoTerm]
      simp [(this.resolve_left algebraMap_X_ne_zero)]
    · refine ⟨fun _ => -(y (Sum.inr ())) / ψO PowerSeries.X, ?_⟩
      funext i
      rcases i with i | i
      · exact i.elim
      · have hA : algebraMap OO (FractionRing OO) (algebraMap Lam OO PowerSeries.X) ≠ 0 :=
          ψO_X_ne_zero
        simp [FourCx.aug, mulVec, dotProduct]
        field_simp

theorem hcoreEx (ℓ : ℕ) (F : Family) (x : Addr F.b) :
    Central.IsClassFunctionalCoord (coreEx.D.map ιQ) (ιQ ∘ coreEx.zc) (ιQ ∘ coreEx.wc)
      (trianglesEx ℓ F x).urel := by
  unfold Central.IsClassFunctionalCoord
  refine Matrix.ext fun i j => ?_
  fin_cases i; fin_cases j
  simp [coreEx, trianglesEx, uEx, vecMulVec_apply]
  change -PowerSeries.X =
    (-PowerSeries.X • (0 : Matrix (Fin 1) (Fin 1) (PowerSeries ℚ_[2])).adjugate) 0 0
  rw [Matrix.adjugate_fin_one]
  change -PowerSeries.X = -PowerSeries.X * (1 : Matrix (Fin 1) (Fin 1) (PowerSeries ℚ_[2])) 0 0
  rw [Matrix.one_apply_eq, mul_one]

/-! ### The pre-cancellation side of the example -/

/-- The class `1` on `H₁`. -/
abbrev zCore (b : ℕ) :
    Fin (Mex b).D.m0 ⊕ Unit ⊕ Fin (Mex b).D.m1 → MonoidAlgebra OO (SignGroup b) :=
  fun _ => 1

/-- The functional `1` on `H₂`, `0` on the new local summand. -/
abbrev lamCore (b : ℕ) : (Fin (Mex b).C.m1 ⊕ Unit ⊕ Fin (Mex b).C.m2) ⊕ (Mex b).C.N →
    MonoidAlgebra OO (SignGroup b) :=
  Sum.elim (fun _ => 1) (fun _ => 0)

theorem hzCore (b : ℕ) : (Mex b).D.d1 *ᵥ zCore b = 0 := by
  change ((preEx b).X.map (φO b)) *ᵥ zCore b = 0
  simp only [preEx, Matrix.map_zero _ (map_zero _)]
  exact zero_mulVec _

theorem hlamCore (b : ℕ) :
    lamCore b ᵥ* fromRows ((Mex b).C.map (φO b)).X ((Mex b).C.map (φO b)).Y = 0 := by
  have h0 : fromRows ((Mex b).C.map (φO b)).X ((Mex b).C.map (φO b)).Y = 0 := by
    refine Matrix.ext fun i j => ?_
    rcases i with i | i
    · change ((preEx b).X.map (φO b)) i j = 0
      simp [preEx]; rfl
    · change ((preEx b).Y.map (φO b)) i j = 0
      simp [preEx]; rfl
  funext j
  have hent : ∀ y, fromRows ((Mex b).C.map (φO b)).X ((Mex b).C.map (φO b)).Y y j = 0 :=
    fun y => congrFun (congrFun h0 y) j
  change (∑ y, lamCore b y * fromRows ((Mex b).C.map (φO b)).X ((Mex b).C.map (φO b)).Y y j) = 0
  exact Finset.sum_eq_zero fun y _ => by rw [hent y, mul_zero]

theorem evK_tG {b : ℕ} (x : Addr b) : evK (sgnChar x) (φO b (tG b)) = ψO PowerSeries.X := by
  rw [Determinant.evK_apply, signEval_φO]
  unfold tG
  rw [Determinant.signEval_single, map_one, Units.val_one, Int.cast_one, mul_one]
  rfl

theorem det_Bx_ex {b : ℕ} (x : Addr b) :
    (Cev ((Mex b).C.map (φO b)) x).B.det = ψO PowerSeries.X := by
  change (((preEx b).B.map (φO b)).map (evK (sgnChar x))).det = _
  have : Unique (preEx b).N := { default := ((), ()), uniq := fun _ => rfl }
  rw [Matrix.det_unique]
  simp only [preEx, Matrix.map_apply, of_apply]
  exact evK_tG x

theorem hcoreK : Central.IsClassFunctionalCoord (coreEx.D.map ψO) (ψO ∘ coreEx.zc)
    (ψO ∘ coreEx.wc) (-ψO PowerSeries.X) := by
  unfold Central.IsClassFunctionalCoord
  refine Matrix.ext fun i j => ?_
  fin_cases i; fin_cases j
  simp [coreEx, vecMulVec_apply]
  change -ψO PowerSeries.X =
    (-ψO PowerSeries.X • (0 : Matrix (Fin 1) (Fin 1) (FractionRing OO)).adjugate) 0 0
  rw [Matrix.adjugate_fin_one]
  change -ψO PowerSeries.X = -ψO PowerSeries.X * (1 : Matrix (Fin 1) (Fin 1) (FractionRing OO)) 0 0
  rw [Matrix.one_apply_eq, mul_one]

/-- **`PreCoreLink` holds in the example**: both coordinates are `−t`. -/
theorem preCoreLink_ex (F : Family) (x : Addr F.b) :
    PreCoreLink (Mex F.b) x (zCore F.b) (lamCore F.b) (hzCore F.b) (hlamCore F.b)
      (coreEx.D.map ψO) (ψO ∘ coreEx.zc) (ψO ∘ coreEx.wc) coreEx.hz coreEx.hw := by
  unfold PreCoreLink
  set C := Cev ((Mex F.b).C.map (φO F.b)) x with hCdef
  have hB : IsUnit C.B.det := isUnit_Bev _ (Mex F.b).isUnit_B x
  have e0 : IsEmpty (Fin (C.cancel hB).m0) := by change IsEmpty (Fin 0); infer_instance
  have e1 : IsEmpty (Fin (C.cancel hB).m1) := by change IsEmpty (Fin 0); infer_instance
  have e2 : IsEmpty (Fin (C.cancel hB).m2) := by change IsEmpty (Fin 0); infer_instance
  have hA0 : IsUnit (C.cancel hB).A0.det := by rw [Matrix.det_isEmpty]; exact isUnit_one
  have hA1 : IsUnit (C.cancel hB).A1.det := by rw [Matrix.det_isEmpty]; exact isUnit_one
  have hA2 : IsUnit (C.cancel hB).A2.det := by rw [Matrix.det_isEmpty]; exact isUnit_one
  refine (kmCoord_pre_block C hB _ _ _ _ hA0 hA1 hA2).trans ?_
  obtain ⟨hc⟩ := exists_contraction _ (FourCx.isExact_toBased _ coreEx.exact)
  refine Eq.trans ?_ (kmCoord_twoTerm _ _ _ _ _ _ hc hcoreK).symm
  have hX : ∀ i j, (C.cancel hB).d1 i j = 0 := fun i j => by
    change (((preEx F.b).X.map (φO F.b)).map (evK (sgnChar x))) i j = 0
    simp [preEx]; rfl
  have hR : (C.cancel hB).hRem = 0 := by
    unfold BlockComplex.hRem
    rw [hX, dotProduct, Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
  have hα : (C.cancel hB).alphaB (evK (sgnChar x) ∘ zCore F.b) = 1 := by
    unfold BlockComplex.alphaB
    rw [dotProduct, Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
    exact map_one _
  have hβ : (C.cancel hB).betaB (transportFun C (evK (sgnChar x) ∘ lamCore F.b)) = 1 := by
    unfold BlockComplex.betaB
    rw [dotProduct, Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
    unfold transportFun
    change (evK (O := OO) (sgnChar x) 1 - ((fun _ : C.N => evK (O := OO) (sgnChar x) 0) ᵥ*
      C.B⁻¹ ᵥ* C.T) (Sum.inr (Sum.inl ()))) = 1
    rw [map_one, map_zero, show (fun _ : C.N => (0 : FractionRing OO)) = 0 from rfl, zero_vecMul,
      zero_vecMul, Pi.zero_apply, sub_zero]
  split_ifs with h
  · rw [show C.B.det = ψO PowerSeries.X from det_Bx_ex x]
    erw [hα, hβ]
    rw [Matrix.det_isEmpty (A := (C.cancel hB).A0), Matrix.det_isEmpty (A := (C.cancel hB).A1),
      Matrix.det_isEmpty (A := (C.cancel hB).A2)]
    ring
  · exact absurd hR h

/-- **E1a in the example** (non-degenerate: `ũ = −t`), from `coordLink_of_triangles_core`. -/
theorem coordLink_coreExample (ℓ : ℕ) (F : Family) :
    ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep (ddEx ℓ) F e g →
      CoordLink (Mex F.b).toIdentification.B (kappaOf (Mex F.b)) (φO F.b 1) 0 e g
        (cOf (Mex F.b).D (zCore F.b) (transportFun ((Mex F.b).C.map (φO F.b)) (lamCore F.b))
          (hzCore F.b) (hμ_cancel ((Mex F.b).C.map (φO F.b)) (Mex F.b).isUnit_B (hlamCore F.b))) :=
  coordLink_of_triangles_core (ddEx ℓ) F (Mex F.b) (zCore F.b) (lamCore F.b) (hzCore F.b)
    (hlamCore F.b) 1 hunitEx (fun _ => 0) (fun _ => -PowerSeries.X) (repEx ℓ F)
    (trianglesEx ℓ F) (hcompatEx ℓ F) (fun _ => coreEx) (hcoreEx ℓ F)
    (fun x _ => preCoreLink_ex F x)

end ZInQ.Contrib.CloudB3RC53.CoordLink
