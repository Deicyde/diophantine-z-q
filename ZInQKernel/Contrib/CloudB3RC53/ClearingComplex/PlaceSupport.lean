import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.NewLocalConsistency
import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.SesQuasiIso

/-!
# The support change at the example place: a genuine Selmer model of the new local summand

For the example of `NewLocalConsistency.lean` (one unramified new place with `M = Λ`,
`Φ = 1 + t`, `q = 1`, local block `t`), this file builds the support change at augmentation with
the ACTUAL local data of the place, as `Identification2.scU` requires:

* `dpEx`: the new-support Selmer data: the old global complex, the unramified local condition
  `U_q = [Φ − 1]` and the full local complex `L_q = [M --(Φ−1, 0)--> M² --(0, Φ−q)--> M]` of the
  place (`tamePlace`), with `ι_q` the inclusion of the unramified summand;
* `scEx`, `scUEx`: the support change from the old Selmer data (no new place) and its
  `SupportChangeFamily` structure (the new local complexes and conditions are those of the place);
* `ψ0G`: the comparison of the augmented pre-cancellation complex (old part plus the disk
  `N --t--> N` in degrees two and three) with the Selmer complex of `dpEx`
  (`x_N ↦ (0, x_N) ∈ L_q¹`, `y_N ↦ −y_N ∈ L_q²`);
* `ψ0G_quasiIso` (PROVED): it is a quasi-isomorphism (degreewise injective with acyclic cokernel
  `Λ --(t, −1)--> Λ² --(−1, −t)--> Λ`, `quasiIso_of_ses`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ClearingComplex

open CategoryTheory Matrix
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup aug)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (GAcyclic idGHom)

variable {b : ℕ}

/-- The Frobenius of the example place. -/
abbrev ΦEx : Lam →ₗ[Lam] Lam := (1 + PowerSeries.X : Lam) • LinearMap.id

/-- The augmented old part of the example. -/
abbrev oldEx (b : ℕ) : BlockComplex Lam := ((preEx b).map (augR b)).old hYEx hTEx

/-- The augmented pre-cancellation complex of the example. -/
abbrev preA (b : ℕ) : PreComplex Lam := (preEx b).map (augR b)

/-- **The new-support Selmer data**: old global complex, the unramified condition and the full local
complex of the place. -/
def dpEx (b : ℕ) : SelData Lam where
  G := (oldEx b).toGCx
  U := tU Lam ΦEx
  L := tL Lam ΦEx 1
  res := ClearingComplex.zeroGHom _ _
  ι := tιH Lam ΦEx 1

/-- **The support change at the example place.** -/
def scEx (b : ℕ) : SelmerDuality.SupportChangeData Lam where
  D := trivSelG (oldEx b).toGCx
  Dp := dpEx b
  g := idGHom _
  lam := ClearingComplex.zeroGHom _ _
  mu := ClearingComplex.zeroGHom _ _
  r := ClearingComplex.zeroGHom _ _
  hres i j h a := by
    subst h
    change (0 : (tL Lam ΦEx 1).X i) = 0 + (tιH Lam ΦEx 1).f i i rfl 0
    rw [map_zero, add_zero]
  hι i j h u := by
    subst h
    change (tιH Lam ΦEx 1).f i i rfl 0 = 0
    rw [map_zero]

/-- **Its new local data are those of the place.** -/
def scUEx (b : ℕ) : SupportChangeFamily (scEx b) (fun _ : Unit => placeEx) where
  pL _ := idGHom _
  pU _ := idGHom _
  lam_retract _ := ⟨0, fun _ => rfl⟩
  mu_retract _ := ⟨0, fun _ => rfl⟩
  pL_surj _ z := ⟨z (), fun q => rfl⟩
  pU_surj _ z := ⟨z (), fun q => rfl⟩
  L_exact i y := ⟨fun h => ⟨0, (map_zero _).trans (h ()).symm⟩, fun ⟨x, hx⟩ q => by
    rw [← hx]; rfl⟩
  U_exact i v := ⟨fun h => ⟨0, (map_zero _).trans (h ()).symm⟩, fun ⟨x, hx⟩ q => by
    rw [← hx]; rfl⟩
  ι_compat _ _ _ := rfl

/-! ### The comparison with the augmented pre-cancellation complex -/

/-- The new local coordinate. -/
abbrev nE : Unit × Unit := ((), ())

/-- The components of `ψ₀`. -/
def ψ0c (b : ℕ) : (i : ℤ) → ((preA b).idx i → Lam) →ₗ[Lam] selT (dpEx b) i
  | 0 =>
    { toFun := fun x => (x, 0, 0)
      map_add' := fun _ _ => Prod.ext rfl (Prod.ext (add_zero 0).symm (add_zero 0).symm)
      map_smul' := fun _ _ => Prod.ext rfl (Prod.ext (smul_zero _).symm (smul_zero _).symm) }
  | 1 =>
    { toFun := fun x => (x, 0, 0)
      map_add' := fun _ _ => Prod.ext rfl (Prod.ext (add_zero 0).symm (add_zero 0).symm)
      map_smul' := fun _ _ => Prod.ext rfl (Prod.ext (smul_zero _).symm (smul_zero _).symm) }
  | 2 =>
    { toFun := fun x => (fun j => x (Sum.inl j), 0, ((0 : Lam), x (Sum.inr nE)))
      map_add' := fun _ _ => Prod.ext rfl (Prod.ext (add_zero 0).symm
        (Prod.ext (add_zero (0 : Lam)).symm rfl))
      map_smul' := fun _ _ => Prod.ext rfl (Prod.ext (smul_zero _).symm
        (Prod.ext (smul_zero _).symm rfl)) }
  | 3 =>
    { toFun := fun x => (fun j => x (Sum.inl j), 0, -x (Sum.inr nE))
      map_add' := fun _ _ => Prod.ext rfl (Prod.ext (add_zero 0).symm (neg_add _ _))
      map_smul' := fun r x => Prod.ext rfl (Prod.ext (smul_zero _).symm
        (smul_neg r (x (Sum.inr nE))).symm) }
  | _ => 0

theorem augR_tG : augR b (tG b) = PowerSeries.X := by
  simp [tG, augR, ZInQ.Manuscript.RC.Determinant.aug]

theorem ψ0c_comm (i : ℤ) (x : (preA b).idx i → Lam) :
    ψ0c b (i + 1) ((preA b).ddL i x) = (selCx (dpEx b)).d i (i + 1) rfl (ψ0c b i x) := by
  match i with
  | 0 =>
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · exact (map_zero (tUd Lam ΦEx 0)).symm
    · change (0 : Lam) = (0 : Lam) - 0 - 0
      simp
  | 1 =>
    refine Prod.ext rfl (Prod.ext rfl ?_)
    change (((0 : Lam), ((preA b).Y *ᵥ x) nE) : Lam × Lam) =
      (0 : Lam × Lam) - ((0 : Lam), (0 : Lam)) -
        (((ΦEx - LinearMap.id : Lam →ₗ[Lam] Lam)) 0, (0 : Lam))
    have hY : ∀ v : Fin (preA b).m0 ⊕ Unit ⊕ Fin (preA b).m1 → Lam, (preA b).Y *ᵥ v = 0 :=
      fun v => by rw [show (preA b).Y = 0 from hYEx, Matrix.zero_mulVec]
    have hY' : (preA b).Y *ᵥ x = 0 := hY x
    rw [hY', map_zero]
    simp
    rfl
  | 2 =>
    refine Prod.ext (funext fun j => j.elim0) (Prod.ext rfl ?_)
    change -((fromBlocks (preA b).P (preA b).Q (preA b).T (preA b).B *ᵥ x) (Sum.inr nE)) =
      (0 : Lam) - 0 -
        ((ΦEx - ((1 : ℕ) : Lam) • LinearMap.id : Lam →ₗ[Lam] Lam)) (x (Sum.inr nE))
    rw [sub_zero, zero_sub]
    congr 1
    have key : ∀ v : (Fin (preA b).m1 ⊕ Unit ⊕ Fin (preA b).m2) ⊕ (preA b).N → Lam,
        (fromBlocks (preA b).P (preA b).Q (preA b).T (preA b).B *ᵥ v) (Sum.inr nE) =
          PowerSeries.X * v (Sum.inr nE) := by
      intro v
      rw [fromBlocks_mulVec]
      change ((preA b).T *ᵥ (v ∘ Sum.inl)) nE + ((preA b).B *ᵥ (v ∘ Sum.inr)) nE = _
      rw [show (preA b).T = 0 from hTEx, Matrix.zero_mulVec]
      change (0 : Lam) + ∑ y, (preA b).B nE y * v (Sum.inr y) = _
      rw [zero_add]
      haveI : Subsingleton (preA b).N := inferInstanceAs (Subsingleton (Unit × Unit))
      refine (Fintype.sum_subsingleton (fun y => (preA b).B nE y * v (Sum.inr y)) nE).trans ?_
      change augR b (tG b) * v (Sum.inr nE) = _
      rw [augR_tG]
    refine (key x).trans ?_
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    push_cast
    ring
  | 3 =>
    exact Prod.ext (Subsingleton.elim (α := Empty → Lam) _ _)
        (Prod.ext (Subsingleton.elim (α := PUnit) _ _) (Subsingleton.elim (α := PUnit) _ _))
  | Int.ofNat (n + 4) =>
    exact (map_zero ((selCx (dpEx b)).d (Int.ofNat (n + 4)) (Int.ofNat (n + 4) + 1) rfl)).symm
  | Int.negSucc n =>
    change ψ0c b (Int.negSucc n + 1) 0 = (selCx (dpEx b)).d (Int.negSucc n) _ rfl 0
    exact (map_zero _).trans (map_zero _).symm

/-- **The comparison `ψ₀`** of the augmented pre-cancellation complex with the new-support Selmer
complex of the example. -/
def ψ0G (b : ℕ) : GHom (preA b).toGCx (selCx (dpEx b)) where
  f i j h := by subst h; exact ψ0c b i
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj h₁
    exact ψ0c_comm i x

/-! ### The cokernel `Λ --(t, −1)--> Λ² --(−1, −t)--> Λ` and the projection onto it -/

/-- The modules of the cokernel complex. -/
def QX : ℤ → ModuleCat Lam
  | 0 => ModuleCat.of Lam Lam
  | 1 => ModuleCat.of Lam (Lam × Lam)
  | 2 => ModuleCat.of Lam Lam
  | _ => ModuleCat.of Lam PUnit

/-- Its differentials. -/
def Qd : (i : ℤ) → QX i →ₗ[Lam] QX (i + 1)
  | 0 => ((PowerSeries.X : Lam) • (LinearMap.id : Lam →ₗ[Lam] Lam)).prod (-LinearMap.id)
  | 1 => -(LinearMap.fst Lam Lam Lam) - (PowerSeries.X : Lam) • LinearMap.snd Lam Lam Lam
  | _ => 0

theorem qq (x : Lam) : -((PowerSeries.X : Lam) • x) - (PowerSeries.X : Lam) • (-x) = 0 := by
  simp [smul_eq_mul]

theorem Qd_Qd (i : ℤ) (x : QX i) : Qd (i + 1) (Qd i x) = 0 := by
  match i with
  | 0 => exact qq x
  | 1 => rfl
  | 2 => rfl
  | Int.ofNat (n + 3) => rfl
  | Int.negSucc n =>
    change Qd (Int.negSucc n + 1) 0 = 0
    exact map_zero _

/-- **The cokernel complex.** -/
def Qc : GCx Lam where
  X := QX
  d i j h := by subst h; exact Qd i
  d_d i j k hij hjk x := by subst hij hjk; exact Qd_Qd i x

theorem c0a (u : Lam) :
    ((ΦEx - LinearMap.id : Lam →ₗ[Lam] Lam)) u = (PowerSeries.X : Lam) • u := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
  ring

theorem c0b (u : Lam) : (0 : Lam) - u - 0 = -u := by simp

theorem c1 (u l : Lam) :
    ((0 : Lam × Lam) - (u, 0) - (((ΦEx - LinearMap.id : Lam →ₗ[Lam] Lam)) l, 0)).1 =
      -u - (PowerSeries.X : Lam) • l := by
  simp only [Prod.fst_sub, Prod.fst_zero, c0a]
  ring

theorem q0 (x : Lam) (hx : ((PowerSeries.X : Lam) • x, -x) = ((0 : Lam), (0 : Lam))) : x = 0 :=
  neg_eq_zero.mp (congrArg Prod.snd hx)

theorem q1 (u v : Lam) (hx : -u - (PowerSeries.X : Lam) • v = 0) :
    ((PowerSeries.X : Lam) • (-v), -(-v)) = (u, v) := by
  refine Prod.ext ?_ (neg_neg v)
  change (PowerSeries.X : Lam) * (-v) = u
  change -u - (PowerSeries.X : Lam) * v = 0 at hx
  linear_combination hx

theorem q2 (x : Lam) : -(-x) - (PowerSeries.X : Lam) • (0 : Lam) = x := by simp

/-- **The cokernel complex is acyclic.** -/
theorem Qc_acyclic : GAcyclic Qc := by
  intro i j k hij hjk x hx
  subst hij hjk
  match i with
  | Int.negSucc 0 =>
    have h0 : x = 0 := q0 x hx
    exact ⟨0, (map_zero _).trans h0.symm⟩
  | 0 =>
    obtain ⟨u, v⟩ := x
    exact ⟨-v, q1 u v hx⟩
  | 1 => exact ⟨(-x, 0), q2 x⟩
  | 2 => exact ⟨0, rfl⟩
  | Int.ofNat (n + 3) => exact ⟨0, rfl⟩
  | Int.negSucc (n + 1) => exact ⟨0, rfl⟩

/-- The components of the projection onto the cokernel. -/
def πc (b : ℕ) : (i : ℤ) → selT (dpEx b) i →ₗ[Lam] QX i
  | 0 =>
    { toFun := fun c => c.2.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  | 1 =>
    { toFun := fun c => (c.2.1, c.2.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  | 2 =>
    { toFun := fun c => c.2.2.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  | _ => 0

theorem πc_comm (i : ℤ) (c : selT (dpEx b) i) :
    πc b (i + 1) ((selCx (dpEx b)).d i (i + 1) rfl c) = Qd i (πc b i c) := by
  match i with
  | 0 => exact Prod.ext (c0a c.2.1) (c0b c.2.1)
  | 1 => exact c1 c.2.1 c.2.2
  | 2 => rfl
  | 3 => rfl
  | Int.ofNat (n + 4) => rfl
  | Int.negSucc 0 => rfl
  | Int.negSucc (n + 1) => rfl

/-- **The projection onto the cokernel** (a chain map). -/
def πG (b : ℕ) : GHom (selCx (dpEx b)) Qc where
  f i j h := by subst h; exact πc b i
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj h₁
    exact πc_comm i x

theorem πψ (i : ℤ) (x : (preA b).idx i → Lam) : πc b i (ψ0c b i x) = 0 := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | Int.ofNat (n + 4) => rfl
  | Int.negSucc n => rfl

theorem ψ_inj (i : ℤ) : Function.Injective (ψ0c b i) := by
  intro x y h
  haveI : Subsingleton (preA b).N := inferInstanceAs (Subsingleton (Unit × Unit))
  match i with
  | 0 => exact congrArg Prod.fst h
  | 1 => exact congrArg Prod.fst h
  | 2 =>
    have h1 := congrArg Prod.fst h
    have h2 := congrArg (fun c => c.2.2.2) h
    funext j
    rcases j with j | n
    · exact congrFun h1 j
    · have hn : n = nE := Subsingleton.elim _ _
      subst hn
      exact h2
  | 3 =>
    have h1 := congrArg Prod.fst h
    have h2 := congrArg (fun c => c.2.2) h
    funext j
    rcases j with j | n
    · exact congrFun h1 j
    · have hn : n = nE := Subsingleton.elim _ _
      subst hn
      exact neg_injective h2
  | Int.ofNat (n + 4) => exact Subsingleton.elim (α := Empty → Lam) _ _
  | Int.negSucc n => exact Subsingleton.elim (α := Empty → Lam) _ _

theorem π_surj (i : ℤ) : Function.Surjective (πc b i) := by
  intro z
  match i with
  | 0 => exact ⟨(0, z, 0), rfl⟩
  | 1 => exact ⟨(0, z.1, z.2), rfl⟩
  | 2 => exact ⟨(0, 0, (z, 0)), rfl⟩
  | 3 => exact ⟨0, rfl⟩
  | Int.ofNat (n + 4) => exact ⟨0, rfl⟩
  | Int.negSucc n => exact ⟨0, rfl⟩

theorem πψ_exact (i : ℤ) (y : selT (dpEx b) i) (hy : πc b i y = 0) :
    ∃ x, ψ0c b i x = y := by
  match i with
  | 0 =>
    obtain ⟨g, u, l⟩ := y
    have hu : u = 0 := hy
    exact ⟨g, Prod.ext rfl (Prod.ext hu.symm rfl)⟩
  | 1 =>
    obtain ⟨g, u, l⟩ := y
    have h' : (u, l) = ((0 : Lam), (0 : Lam)) := hy
    exact ⟨g, Prod.ext rfl (Prod.ext (congrArg Prod.fst h').symm (congrArg Prod.snd h').symm)⟩
  | 2 =>
    obtain ⟨g, u, l1, l2⟩ := y
    have h1 : l1 = 0 := hy
    exact ⟨Sum.elim g (fun _ => l2), Prod.ext rfl (Prod.ext rfl (Prod.ext h1.symm rfl))⟩
  | 3 =>
    obtain ⟨g, u, l⟩ := y
    exact ⟨Sum.elim g (fun _ => -l), Prod.ext rfl (Prod.ext rfl (neg_neg l))⟩
  | Int.ofNat (n + 4) =>
    haveI := tLX_subsingleton (S := Lam) Lam (Int.ofNat (n + 4) - 1)
      (by simp only [Int.ofNat_eq_natCast]; omega) (by simp only [Int.ofNat_eq_natCast]; omega)
      (by simp only [Int.ofNat_eq_natCast]; omega)
    exact ⟨0, Prod.ext (Subsingleton.elim (α := Empty → Lam) _ _)
      (Prod.ext (Subsingleton.elim (α := PUnit) _ _)
        (Subsingleton.elim (α := tLX Lam Lam (Int.ofNat (n + 4) - 1)) _ _))⟩
  | Int.negSucc n =>
    haveI := tLX_subsingleton (S := Lam) Lam (Int.negSucc n - 1)
      (by rw [Int.negSucc_eq]; omega) (by rw [Int.negSucc_eq]; omega)
      (by rw [Int.negSucc_eq]; omega)
    exact ⟨0, Prod.ext (Subsingleton.elim (α := Empty → Lam) _ _)
      (Prod.ext (Subsingleton.elim (α := PUnit) _ _)
        (Subsingleton.elim (α := tLX Lam Lam (Int.negSucc n - 1)) _ _))⟩

/-- **`ψ₀` is a quasi-isomorphism** (PROVED): degreewise injective with acyclic cokernel. -/
theorem ψ0G_quasiIso : QuasiIso (SelmerDuality.GHom.toCC (ψ0G b)) :=
  quasiIso_of_ses (ψ0G b) (πG b) (fun i x => πψ i x) (fun i => ψ_inj i) (fun i => π_surj i)
    (fun i y hy => πψ_exact i y hy) Qc_acyclic

/-! ### Compatibility with the support comparison, and the consistency witness -/

theorem fromRows_one_inl {m n : Type} [Fintype m] [DecidableEq m] (v : m → Lam) :
    (fun j => (fromRows (1 : Matrix m m Lam) (0 : Matrix n m Lam) *ᵥ v) (Sum.inl j)) = v := by
  funext j; rw [fromRows_mulVec, Sum.elim_inl, Matrix.one_mulVec]

theorem fromRows_one_inr {m n : Type} [Fintype m] [DecidableEq m] (v : m → Lam) (k : n) :
    (fromRows (1 : Matrix m m Lam) (0 : Matrix n m Lam) *ᵥ v) (Sum.inr k) = 0 := by
  rw [fromRows_mulVec, Sum.elim_inr, Matrix.zero_mulVec, Pi.zero_apply]

theorem square_comp (n : ℤ) (x : (oldEx b).idx n → Lam) :
    (SelmerDuality.supportMap (scEx b)).f n n rfl (trivSelGEquiv (oldEx b).toGCx n x) =
      ψ0c b n (PreComplex.oinc hYEx hTEx n x) := by
  match n with
  | 0 => exact Prod.ext rfl (Prod.ext (add_zero (0 : Lam)) rfl)
  | 1 => exact Prod.ext rfl (Prod.ext (add_zero (0 : Lam)) rfl)
  | 2 =>
    refine Prod.ext (fromRows_one_inl (m := Fin 0 ⊕ Unit ⊕ Fin 0) (n := Unit × Unit) x).symm
      (Prod.ext rfl ?_)
    exact Prod.ext rfl (fromRows_one_inr (m := Fin 0 ⊕ Unit ⊕ Fin 0) (n := Unit × Unit) x nE).symm
  | 3 =>
    refine Prod.ext (funext fun j => j.elim0) (Prod.ext rfl ?_)
    exact (neg_eq_zero.mpr (fromRows_one_inr (m := Fin 0) (n := Unit × Unit) x nE)).symm
  | Int.ofNat (k + 4) =>
    haveI := tLX_subsingleton (S := Lam) Lam (Int.ofNat (k + 4) - 1)
      (by simp only [Int.ofNat_eq_natCast]; omega) (by simp only [Int.ofNat_eq_natCast]; omega)
      (by simp only [Int.ofNat_eq_natCast]; omega)
    exact Prod.ext (Subsingleton.elim (α := Empty → Lam) _ _)
      (Prod.ext (Subsingleton.elim (α := PUnit) _ _)
        (Subsingleton.elim (α := tLX Lam Lam (Int.ofNat (k + 4) - 1)) _ _))
  | Int.negSucc k =>
    haveI := tLX_subsingleton (S := Lam) Lam (Int.negSucc k - 1)
      (by rw [Int.negSucc_eq]; omega) (by rw [Int.negSucc_eq]; omega)
      (by rw [Int.negSucc_eq]; omega)
    exact Prod.ext (Subsingleton.elim (α := Empty → Lam) _ _)
      (Prod.ext (Subsingleton.elim (α := PUnit) _ _)
        (Subsingleton.elim (α := tLX Lam Lam (Int.negSucc k - 1)) _ _))

/-- **Compatibility of `ψ_old`, `ψ₀` with the support comparison.** -/
theorem squareEx : (trivSelGIso (oldEx b).toGCx).hom ≫
      SelmerDuality.GHom.toCC (SelmerDuality.supportMap (scEx b)) =
    SelmerDuality.GHom.toCC ((preA b).oldIncl hYEx hTEx) ≫
      SelmerDuality.GHom.toCC (ψ0G b) := by
  ext n x
  exact square_comp n x

/-- **Consistency of the second identification with a nonempty family of genuine new places**
(PROVED): one unramified new place (tame model, `M = Λ`, `Φ = 1 + t`, `q = 1`) with local block
`Φ − q = t`, whose new-support Selmer data carry the actual local complex and unramified condition
of the place (`scUEx`), and the augmented pre-cancellation complex quasi-isomorphic to the
new-support Selmer complex (`ψ0G_quasiIso`). The place is the 3-term tame model, not genuine
continuous cochains (see the caveat on `Identification2`). -/
def identification2_example (b : ℕ) : Identification2 b 0 0 0 0 where
  Qn := Unit
  ιn := Unit
  NP := fun _ => placeEx
  bas := fun _ => Module.Basis.singleton Unit Lam
  A := AEx
  hA := hAEx
  dq := fun _ => 1
  hd := fun _ => by norm_num
  v := fun _ => 1
  w := fun _ => 0
  hdet := hdetEx
  C := preEx b
  eN := Equiv.refl _
  hB0 := hB0Ex
  hT0 := hTEx
  hY0 := hYEx
  s := fun _ _ => 1
  s_ne := fun _ _ => one_ne_zero
  central_full := central_fullEx
  budget := budgetInputs_of_empty _ rfl fun i => by rcases i with _ | _ | _ | i <;> rfl
  sel := trivSelG _
  ψ := (trivSelGIso _).hom
  qis := trivSelG_qis _
  sc := scEx b
  scU := scUEx b
  ψ0 := SelmerDuality.GHom.toCC (ψ0G b)
  qis0 := ψ0G_quasiIso
  ψold := (trivSelGIso _).hom
  qisOld := trivSelG_qis _
  square := squareEx

theorem identification2_nonempty (b : ℕ) : Nonempty (Identification2 b 0 0 0 0) :=
  ⟨identification2_example b⟩

end ZInQ.Contrib.CloudB3RC53.ClearingComplex
