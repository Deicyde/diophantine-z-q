import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.NewLocalModel

/-!
# Consistency of the second identification (nonempty new-local family)

The GLUE input `Identification2 b dK hK cE tK` is used as a hypothesis (`clearingModel_of_km`).
This file provides the building blocks of the consistency witness `identification2_example`
(`PlaceSupport.lean`, PROVED), which has a NONEMPTY family of new places: one new place with coefficient module `Λ`, Frobenius `1 + t`
(the graph-wide prescription "scalar `1 + t`", tex 5241–5243) and `q = 1`, built as an instance of
`UnramifiedNewPlace` in the tame model (not genuine Galois cochains) (`tamePlace`: the tame model `M --(Φ−1, 0)--> M ⊕ M --(0, Φ−q)--> M` and the
unramified condition `[Φ − 1]`); its local block is `Φ − q = t`, with `det = t¹ · 1 + 2 · 0`
(`d_q = 1`); the pre-cancellation complex has this block in degrees two and three and the old part
`D¹ = H₁ → D² = H₂` zero; central ranks `(0, 1, 1, 0)`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ClearingComplex

open CategoryTheory Matrix
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup SmithBlocks aug)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3RC53.RankCounts.SmithCx

/-! ### The central counts for Smith data without disks -/

section Budget

variable {S : Type} [CommRing S] (B : SmithBlocks S OO) (hn : B.n = 3) (hm : ∀ i, B.m i = 0)

include hn hm in
theorem dd_empty (i : ℕ) : dd B i = 0 := by
  unfold dd
  split_ifs
  · exact hm i
  · rfl

include hn hm in
theorem subsingleton_centralH_three_empty : Subsingleton ((centralH B) fr₀ 3) := by
  have e := Hequiv (f := fr₀) (σ B) (σ_ne B) 3
  have : Subsingleton ((Fin (fr₀ 3) → ℤ_[2]) × Q (σ B) 3) := by
    have h1 : Subsingleton (Fin (fr₀ 3) → ℤ_[2]) :=
      ⟨fun a b => funext fun j => (show Fin 0 from j).elim0⟩
    have h2 : Subsingleton (Q (σ B) 3) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ a
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ b
      congr 1
      funext j
      have hj : db (dd B) 3 = 0 := dd_empty B hn hm 2
      exact (Fin.cast hj j).elim0
    infer_instance
  exact e.toEquiv.subsingleton

include hn hm in
theorem sum_val_σ_empty (i : ℕ) : ∑ j, ((σ B) i j).valuation = 0 := by
  have : IsEmpty (Fin (dd B i)) := by rw [dd_empty B hn hm]; infer_instance
  simp

include hn hm in
/-- **The (5.7) counts for Smith data without disks**, with all constants `0`. -/
theorem budgetInputs_of_empty : BudgetInputsAt B fr₀ 0 0 0 0 := by
  have hamp : ∀ i, 3 ≤ i → i < B.n → B.m i = 0 := fun i _ _ => hm i
  have hmTot : B.mTot = 0 := by simp [SmithBlocks.mTot, hm]
  refine ⟨?_, (centralH B) fr₀ 1, (centralH B) fr₀ 2, PUnit, PUnit, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, LinearEquiv.refl _ _, LinearMap.id, 0, 0, 0,
    ⟨Function.injective_id, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sum_finrank_centralCx B fr₀ hamp, hmTot, Fin.sum_univ_four]
    simp [fr₀]
  · intro x; simp
  · intro x; exact ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => rfl⟩
  · intro x; exact ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => rfl⟩
  · intro x
    have := subsingleton_centralH_three_empty B hn hm
    exact ⟨0, Subsingleton.elim _ _⟩
  · rw [length_torsion_H (σ B) (σ_ne B) 1, length_Q_succ (σ B) (σ_ne B) 0,
      sum_val_σ_empty B hn hm]
  · simp
  · rw [length_torsion_H (σ B) (σ_ne B) 2, length_Q_succ (σ B) (σ_ne B) 1,
      sum_val_σ_empty B hn hm]
  · simp
  · simp [finrank_centralH, fr₀]
  · simp [finrank_centralH, fr₀]

end Budget

/-! ### Selmer data with only a global complex -/

section TrivSel

variable {S : Type} [CommRing S]

/-- Selmer data `G --0--> 0 <--0-- 0`. -/
def trivSelG (G : GCx S) : SelData S where
  G := G
  U := zeroGCx S
  L := zeroGCx S
  res := zeroGHom _ _
  ι := zeroGHom _ _

/-- `G^n ≅ G^n ⊕ 0 ⊕ 0`. -/
def trivSelGEquiv (G : GCx S) (n : ℤ) : G.X n ≃ₗ[S] selT (trivSelG G) n :=
  letI : Unique (PUnit.{1} × PUnit.{1}) :=
    { default := ⟨PUnit.unit, PUnit.unit⟩, uniq := fun _ => Subsingleton.elim _ _ }
  (LinearEquiv.prodUnique (R := S) (M := G.X n) (M₂ := PUnit × PUnit)).symm

/-- The isomorphism of `G` with the Selmer complex of `trivSelG G`. -/
def trivSelGIso (G : GCx S) : G.toCC ≅ (selCx (trivSelG G)).toCC := by
  refine HomologicalComplex.Hom.isoOfComponents (fun n => (trivSelGEquiv G n).toModuleIso) ?_
  intro i j hij
  change i + 1 = j at hij
  subst hij
  ext x
  change ((selCx (trivSelG G)).toCC.d i (i + 1)).hom (trivSelGEquiv G i x) =
    trivSelGEquiv G (i + 1) ((G.toCC.d i (i + 1)).hom x)
  refine (GCx.toCC_d_hom _ i (i + 1) rfl _).trans ?_
  refine Eq.trans ?_ (congrArg (trivSelGEquiv G (i + 1)) (GCx.toCC_d_hom G i (i + 1) rfl x)).symm
  exact Prod.ext rfl (Prod.ext rfl rfl)

theorem trivSelG_qis (G : GCx S) : QuasiIso (trivSelGIso G).hom := quasiIso_of_isIso _

/-- The support change along a chain map `g : G → G⁺` with zero local data. -/
def trivSupportChange (G Gp : GCx S) (g : GHom G Gp) : SelmerDuality.SupportChangeData S where
  D := trivSelG G
  Dp := trivSelG Gp
  g := g
  lam := zeroGHom _ _
  mu := zeroGHom _ _
  r := zeroGHom _ _
  hres _ _ _ _ := rfl
  hι _ _ _ _ := rfl

theorem trivSupportChange_square (G Gp : GCx S) (g : GHom G Gp) :
    (trivSelGIso G).hom ≫ SelmerDuality.GHom.toCC
        (SelmerDuality.supportMap (trivSupportChange G Gp g)) =
      SelmerDuality.GHom.toCC g ≫ (trivSelGIso Gp).hom := by
  ext n x
  change ((g.f n n rfl x, 0 + 0, 0) : Gp.X n × PUnit × PUnit) = (g.f n n rfl x, 0, 0)
  rfl

end TrivSel

/-! ### The tame model of an unramified new place -/

section Tame

variable {S : Type} [CommRing S] (M : Type) [AddCommGroup M] [Module S M] (Φ : M →ₗ[S] M) (q : ℕ)

/-- The modules of the full local complex `M → M ⊕ M → M` (degrees `0, 1, 2`). -/
def tLX (S : Type) [CommRing S] (M : Type) [AddCommGroup M] [Module S M] : ℤ → ModuleCat S
  | 0 => ModuleCat.of S M
  | 1 => ModuleCat.of S (M × M)
  | 2 => ModuleCat.of S M
  | _ => ModuleCat.of S PUnit

/-- Its differentials `(Φ − 1, 0)` and `(0, Φ − q)`. -/
def tLd : (i : ℤ) → tLX S M i →ₗ[S] tLX S M (i + 1)
  | 0 => (Φ - LinearMap.id).prod (0 : M →ₗ[S] M)
  | 1 => (Φ - (q : S) • LinearMap.id) ∘ₗ LinearMap.snd S M M
  | _ => 0

theorem tLd_tLd (i : ℤ) (x : tLX S M i) : tLd M Φ q (i + 1) (tLd M Φ q i x) = 0 := by
  match i with
  | 0 =>
    change (Φ - (q : S) • (LinearMap.id : M →ₗ[S] M)) (0 : M) = 0
    exact map_zero _
  | 1 => rfl
  | 2 => rfl
  | Int.ofNat (n + 3) => rfl
  | Int.negSucc n =>
    change tLd M Φ q (Int.negSucc n + 1) 0 = 0
    exact map_zero _

/-- The full local complex `L_q`. -/
def tL : GCx S where
  X := tLX S M
  d i j h := by subst h; exact tLd M Φ q i
  d_d i j k hij hjk x := by subst hij hjk; exact tLd_tLd M Φ q i x

/-- The modules of the unramified condition `M → M` (degrees `0, 1`). -/
def tUX (S : Type) [CommRing S] (M : Type) [AddCommGroup M] [Module S M] : ℤ → ModuleCat S
  | 0 => ModuleCat.of S M
  | 1 => ModuleCat.of S M
  | _ => ModuleCat.of S PUnit

def tUd : (i : ℤ) → tUX S M i →ₗ[S] tUX S M (i + 1)
  | 0 => Φ - LinearMap.id
  | _ => 0

theorem tUd_tUd (i : ℤ) (x : tUX S M i) : tUd M Φ (i + 1) (tUd M Φ i x) = 0 := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | Int.ofNat (n + 2) => rfl
  | Int.negSucc n =>
    change tUd M Φ (Int.negSucc n + 1) 0 = 0
    exact map_zero _

/-- The unramified local condition `U_q = [Φ − 1]`. -/
def tU : GCx S where
  X := tUX S M
  d i j h := by subst h; exact tUd M Φ i
  d_d i j k hij hjk x := by subst hij hjk; exact tUd_tUd M Φ i x

def tι : (i : ℤ) → tUX S M i →ₗ[S] tLX S M i
  | 0 => LinearMap.id
  | 1 => LinearMap.inl S M M
  | _ => 0

theorem tι_comm (i : ℤ) (x : tUX S M i) :
    tι M (i + 1) (tUd M Φ i x) = tLd M Φ q i (tι M i x) := by
  match i with
  | 0 => rfl
  | 1 =>
    change (0 : tLX S M 2) = (Φ - (q : S) • (LinearMap.id : M →ₗ[S] M)) (0 : M)
    exact (map_zero _).symm
  | 2 => rfl
  | Int.ofNat (n + 3) => rfl
  | Int.negSucc n =>
    change tι M (Int.negSucc n + 1) 0 = tLd M Φ q (Int.negSucc n) 0
    rw [map_zero, map_zero]

/-- The inclusion of the unramified summand. -/
def tιH : GHom (tU M Φ) (tL M Φ q) where
  f i j h := by subst h; exact tι M i
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj h₁
    exact tι_comm M Φ q i x

theorem tLX_subsingleton (n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ 1) (h2 : n ≠ 2) :
    Subsingleton (tLX S M n) := by
  match n with
  | 0 => exact absurd rfl h0
  | 1 => exact absurd rfl h1
  | 2 => exact absurd rfl h2
  | Int.ofNat (k + 3) => exact (inferInstance : Subsingleton PUnit)
  | Int.negSucc k => exact (inferInstance : Subsingleton PUnit)

theorem tUX_subsingleton (n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ 1) :
    Subsingleton (tUX S M n) := by
  match n with
  | 0 => exact absurd rfl h0
  | 1 => exact absurd rfl h1
  | Int.ofNat (k + 2) => exact (inferInstance : Subsingleton PUnit)
  | Int.negSucc k => exact (inferInstance : Subsingleton PUnit)

/-- **The tame model of an unramified new place** (lane SelmerDuality's `UnramifiedNewPlace`):
coefficient module `M`, Frobenius `Φ`, residue cardinality `q` (odd). -/
def tamePlace (hq : Odd q) : SelmerDuality.UnramifiedNewPlace S where
  M := ModuleCat.of S M
  Φ := Φ
  q := q
  q_odd := hq
  Lq := tL M Φ q
  Uq := tU M Φ
  ιq := tιH M Φ q
  eL0 := LinearEquiv.refl S M
  eL1 := LinearEquiv.refl S (M × M)
  eL2 := LinearEquiv.refl S M
  Lq_zero := tLX_subsingleton M
  Lq_d0 _ := rfl
  Lq_d1 _ := rfl
  eU0 := LinearEquiv.refl S M
  eU1 := LinearEquiv.refl S M
  Uq_zero := tUX_subsingleton M
  Uq_d _ := rfl
  ιq_0 _ := rfl
  ιq_1 _ := rfl

end Tame

/-! ### A model with one new place -/

variable {b : ℕ}

/-- The new place: `M = Λ`, `Φ = 1 + t`, `q = 1`. -/
def placeEx : SelmerDuality.UnramifiedNewPlace Lam :=
  tamePlace Lam ((1 + PowerSeries.X : Lam) • LinearMap.id) 1 odd_one

/-- `t ∈ Λ[G]`. -/
def tG (b : ℕ) : MonoidAlgebra Lam (SignGroup b) := MonoidAlgebra.single 1 PowerSeries.X

/-- The pre-cancellation complex: old part `H₁ --0--> H₂`, one new local summand with block `t`. -/
def preEx (b : ℕ) : PreComplex (MonoidAlgebra Lam (SignGroup b)) where
  m0 := 0
  m1 := 0
  m2 := 0
  N := Unit × Unit
  c0 := 0
  X := 0
  Y := 0
  P := 0
  Q := 0
  T := 0
  B := of fun _ _ => tG b
  c1_c0 := by simp
  c2_c1 := by
    rw [fromBlocks_mul_fromRows]
    simp

/-- The local block `(t)`. -/
def AEx : Unit → Matrix Unit Unit Lam := fun _ => of fun _ _ => PowerSeries.X

theorem hAEx : ∀ q, AEx q = LinearMap.toMatrix (Module.Basis.singleton Unit Lam)
    (Module.Basis.singleton Unit Lam) (placeEx.Φ - ((placeEx.q : ℕ) : Lam) • LinearMap.id) := by
  intro q
  refine Matrix.ext fun i j => ?_
  rw [LinearMap.toMatrix_apply, Module.Basis.singleton_apply, Module.Basis.singleton_repr]
  change PowerSeries.X = (((1 + PowerSeries.X : Lam) • (LinearMap.id : Lam →ₗ[Lam] Lam) -
    ((1 : ℕ) : Lam) • (LinearMap.id : Lam →ₗ[Lam] Lam)) : Lam →ₗ[Lam] Lam) (1 : Lam)
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
  ring

theorem hdetEx : ∀ q : Unit, (AEx q).det =
    (PowerSeries.X : Lam) ^ (fun _ : Unit => 1) q * ((fun _ : Unit => (1 : Lamˣ)) q : Lam) +
      2 * (fun _ : Unit => (0 : Lam)) q := by
  intro q
  simp [AEx, Matrix.det_unique]

theorem hB0Ex : ((preEx b).B.submatrix (Equiv.refl _).symm (Equiv.refl _).symm).map aug =
    Matrix.blockDiagonal AEx := by
  ext ⟨i, q⟩ ⟨j, q'⟩
  simp [preEx, tG, AEx, Matrix.blockDiagonal_apply, ZInQ.Manuscript.RC.Determinant.aug]

theorem hYEx : (preEx b).Y.map (augR b) = 0 := Matrix.map_zero _ (map_zero _)
theorem hTEx : (preEx b).T.map (augR b) = 0 := Matrix.map_zero _ (map_zero _)

theorem preEx_old_mi (i : ℕ) : (((preEx b).map (augR b)).old hYEx hTEx).mi i = 0 := by
  rcases i with _ | _ | _ | i <;> rfl

theorem central_fullEx :
    let D := ((preEx b).map (augR b)).old hYEx hTEx
    D.d0.map PowerSeries.constantCoeff =
        (smithForm (preEx b).m0 (preEx b).m1 (preEx b).m2 (fun _ => 1) (fun _ => 1)
          (fun _ => 1)).d0 ∧
      D.d1.map PowerSeries.constantCoeff =
        (smithForm (preEx b).m0 (preEx b).m1 (preEx b).m2 (fun _ => 1) (fun _ => 1)
          (fun _ => 1)).d1 ∧
      D.d2.map PowerSeries.constantCoeff =
        (smithForm (preEx b).m0 (preEx b).m1 (preEx b).m2 (fun _ => 1) (fun _ => 1)
          (fun _ => 1)).d2 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j; exact j.elim0
  · ext (i | i | i) (j | j | j)
    all_goals first | exact i.elim0 | exact j.elim0 | rfl
  · ext i j; exact i.elim0

end ZInQ.Contrib.CloudB3RC53.ClearingComplex
