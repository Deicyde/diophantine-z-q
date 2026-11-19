import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.Lambda
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Weil

/-!
# Lane RC28 round 2, part 3: the genuine Tate module `T_2E = lim E(K_S)[2^n]`

Manuscript `diophantine_zq.tex` (11/5), tex 2836–2838 (`T = T_2E`, the `2`-adic Tate module, with
its `G_{K,S}`-action `ρ_T`).

* `Lev K S W n = E(K_S)[2^n]` (lane RC28 round 1's `TorsS`), `transLev n : E[2^{n+1}] → E[2^n]`,
  `P ↦ 2P`.
* **`TateS K S W`**: the inverse limit, the compatible sequences `(P_n)` with `2 P_{n+1} = P_n`;
  an additive group with
  * the genuine `G_{K,S}`-action (coordinatewise, on coordinates of points);
  * a **`ℤ₂`-module structure** (`a • P` has level `n` coordinate `(a mod 2^n) • P_n`);
  * the **inverse-limit topology** (a subspace of the product of the discrete `E(K_S)[2^n]`), for
    which it is a topological group and **the action is continuous** (`ContinuousSMul`).
* `projLev n : T → E(K_S)[2^n]`; **`mem_ker_projLev_iff`: `P_m = 0 ↔ P ∈ 2^m T`**, for every curve
  (no hypothesis), so the inverse-limit topology is the `2`-adic one.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.LambdaCoef

open NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Manuscript.RC.SelmerComplex (GKS)
open ZInQ.Manuscript.RC.CoefModules (TorsS KS galS coe_smul_torsS isOpen_stabilizer_torsS
  FullTorsion)

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (W : WeierstrassCurve K)

/-- `E(K_S)[2^n]`. -/
abbrev Lev (n : ℕ) : Type := TorsS K S W ((2 ^ n : ℕ) : ℤ)

/-- **`E[2^∞] ⊆ E(K_S)`**: `|E(K_S)[2^n]| = 4^n` for every `n`. GLUE input (Néron–Ogg–Shafarevich,
Silverman AEC VII.7.1; Serre–Tate 1968, Thm 1: true for `S` containing the places of bad reduction
and those above `2`); used only for the rank of `T_2E` and of its fibres. -/
class HasFullTwoTorsion : Prop where
  full : ∀ n : ℕ, FullTorsion K S W (2 ^ n)

/-- The points of `E` over `K_S`. -/
abbrev Pt : Type := (W.baseChange (KS K S)).toAffine.Point

variable {K S W}

theorem two_pow_nsmul_lev {n : ℕ} (P : Lev K S W n) : (2 ^ n : ℕ) • (P : Pt K S W) = 0 := by
  have h := (Submodule.mem_torsionBy_iff _ _).mp P.2
  rwa [natCast_zsmul] at h

theorem two_pow_nsmul_lev' {n : ℕ} (P : Lev K S W n) : (2 ^ n : ℕ) • P = 0 :=
  Subtype.ext (by rw [AddSubgroup.coe_nsmul]; exact two_pow_nsmul_lev P)

theorem mem_lev_iff {n : ℕ} (x : Pt K S W) :
    x ∈ AddSubgroup.torsionBy (Pt K S W) ((2 ^ n : ℕ) : ℤ) ↔ (2 ^ n : ℕ) • x = 0 := by
  change x ∈ Submodule.torsionBy ℤ _ _ ↔ _
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul]

variable (K S W)

/-- **The transition map `E(K_S)[2^{n+1}] → E(K_S)[2^n]`, `P ↦ 2P`.** -/
def transLev (n : ℕ) : Lev K S W (n + 1) →+ Lev K S W n where
  toFun P := ⟨2 • (P : Pt K S W), by
    rw [mem_lev_iff, smul_smul, ← pow_succ]
    exact two_pow_nsmul_lev P⟩
  map_zero' := Subtype.ext (by simp)
  map_add' P Q := Subtype.ext (by simp [nsmul_add])

theorem coe_transLev (n : ℕ) (P : Lev K S W (n + 1)) :
    ((transLev K S W n P : Lev K S W n) : Pt K S W) = 2 • (P : Pt K S W) := rfl

/-- The compatible sequences. -/
def tateSub : AddSubgroup (∀ n : ℕ, Lev K S W n) where
  carrier := {P | ∀ n, transLev K S W n (P (n + 1)) = P n}
  zero_mem' n := map_zero _
  add_mem' {P Q} hP hQ n := by
    change transLev K S W n (P (n + 1) + Q (n + 1)) = P n + Q n
    rw [map_add, hP n, hQ n]
  neg_mem' {P} hP n := by
    change transLev K S W n (-P (n + 1)) = -P n
    rw [map_neg, hP n]

/-- **The `2`-adic Tate module `T_2E = lim_n E(K_S)[2^n]`** (tex 2836–2838). -/
abbrev TateS : Type := ↥(tateSub K S W)

variable {K S W}

/-- The `n`-th coordinate of a point of the Tate module, as a point of `E(K_S)`. -/
abbrev TateS.pt (P : TateS K S W) (n : ℕ) : Pt K S W := ((P : ∀ n, Lev K S W n) n : Pt K S W)

theorem TateS.two_smul_pt (P : TateS K S W) (n : ℕ) : 2 • P.pt (n + 1) = P.pt n := by
  have h := congrArg (fun x : Lev K S W n => (x : Pt K S W)) (P.2 n)
  exact h

theorem TateS.pt_congr (P : TateS K S W) {a b : ℕ} (h : a = b) : P.pt a = P.pt b := by
  subst h; rfl

/-- **Iterated compatibility**: `2^k P_{n+k} = P_n`. Kind: PROVED. -/
theorem TateS.two_pow_smul_pt (P : TateS K S W) (n k : ℕ) : (2 ^ k : ℕ) • P.pt (n + k) = P.pt n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_comm, mul_nsmul, show n + (k + 1) = n + k + 1 from rfl, TateS.two_smul_pt, ih]

theorem TateS.ext' {P Q : TateS K S W} (h : ∀ n, P.pt n = Q.pt n) : P = Q :=
  Subtype.ext (funext fun n => Subtype.ext (h n))

theorem TateS.pt_add (P Q : TateS K S W) (n : ℕ) : (P + Q).pt n = P.pt n + Q.pt n := rfl

theorem TateS.pt_zero (n : ℕ) : (0 : TateS K S W).pt n = 0 := rfl

theorem TateS.pt_neg (P : TateS K S W) (n : ℕ) : (-P).pt n = -P.pt n := rfl

/-! ### The Galois action -/

theorem smul_lev_coe (σ : GKS K S) {n : ℕ} (P : Lev K S W n) :
    ((σ • P : Lev K S W n) : Pt K S W) = Affine.Point.map (galS K S σ).toAlgHom (P : Pt K S W) :=
  coe_smul_torsS σ P

/-- The coordinatewise action preserves compatibility. -/
theorem smul_mem_tateSub (σ : GKS K S) (P : TateS K S W) :
    (fun n => σ • (P : ∀ n, Lev K S W n) n) ∈ tateSub K S W := by
  intro n
  apply Subtype.ext
  rw [coe_transLev, smul_lev_coe, smul_lev_coe, ← map_nsmul]
  exact congrArg _ (P.two_smul_pt n)

instance : DistribMulAction (GKS K S) (TateS K S W) where
  smul σ P := ⟨fun n => σ • (P : ∀ n, Lev K S W n) n, smul_mem_tateSub σ P⟩
  one_smul P := Subtype.ext (funext fun n => one_smul _ _)
  mul_smul σ τ P := Subtype.ext (funext fun n => mul_smul _ _ _)
  smul_zero σ := Subtype.ext (funext fun n => smul_zero _)
  smul_add σ P Q := Subtype.ext (funext fun n => smul_add _ _ _)

theorem TateS.pt_smul (σ : GKS K S) (P : TateS K S W) (n : ℕ) :
    (σ • P).pt n = Affine.Point.map (galS K S σ).toAlgHom (P.pt n) :=
  smul_lev_coe σ _

/-! ### The `ℤ₂`-module structure -/

/-- `a mod 2^n`, as a natural number. -/
def resN (n : ℕ) (a : ℤ_[2]) : ℕ := (PadicInt.toZModPow n a).val

theorem resN_lt (n : ℕ) (a : ℤ_[2]) : resN n a < 2 ^ n := ZMod.val_lt _

theorem resN_mod_succ (n : ℕ) (a : ℤ_[2]) : resN (n + 1) a % 2 ^ n = resN n a := by
  have h := congrArg (fun f => f a) (PadicInt.zmod_cast_comp_toZModPow n (n + 1) (Nat.le_succ n))
  simp only [RingHom.comp_apply, ZMod.castHom_apply] at h
  rw [resN, resN, ← h, ZMod.cast_eq_val, ZMod.val_natCast]

theorem resN_add (n : ℕ) (a b : ℤ_[2]) : resN n (a + b) = (resN n a + resN n b) % 2 ^ n := by
  rw [resN, map_add, ZMod.val_add]; rfl

theorem resN_mul (n : ℕ) (a b : ℤ_[2]) : resN n (a * b) = (resN n a * resN n b) % 2 ^ n := by
  rw [resN, map_mul, ZMod.val_mul]; rfl

theorem resN_one (n : ℕ) : resN n 1 = 1 % 2 ^ n := by
  rw [resN, map_one, ← Nat.cast_one, ZMod.val_natCast]

theorem resN_zero (n : ℕ) : resN n 0 = 0 := by rw [resN, map_zero, ZMod.val_zero]

theorem resN_natCast (n m : ℕ) : resN n (m : ℤ_[2]) = m % 2 ^ n := by
  rw [resN, map_natCast, ZMod.val_natCast]

/-- On a group killed by `m`, `a • x` only depends on `a mod m`. -/
theorem nsmul_eq_of_mod_eq {A : Type*} [AddCommGroup A] {x : A} {m : ℕ} (hx : m • x = 0) {a b : ℕ}
    (h : a % m = b % m) : a • x = b • x := by
  rw [← Nat.mod_add_div a m, ← Nat.mod_add_div b m, add_nsmul, add_nsmul, mul_comm m, mul_comm m,
    mul_smul, mul_smul, hx, smul_zero, smul_zero, h]

theorem nsmul_mod_eq {A : Type*} [AddCommGroup A] {x : A} {m : ℕ} (hx : m • x = 0) (a : ℕ) :
    (a % m) • x = a • x :=
  nsmul_eq_of_mod_eq hx (Nat.mod_mod a m)

theorem resN_smul_mem (a : ℤ_[2]) (P : TateS K S W) :
    (fun n => resN n a • (P : ∀ n, Lev K S W n) n) ∈ tateSub K S W := by
  intro n
  apply Subtype.ext
  change 2 • (resN (n + 1) a • P.pt (n + 1)) = resN n a • P.pt n
  rw [smul_comm, P.two_smul_pt, ← nsmul_mod_eq (two_pow_nsmul_lev ((P : ∀ n, Lev K S W n) n)),
    resN_mod_succ]

/-- **`T_2E` is a `ℤ₂`-module**: `a • (P_n) = ((a mod 2^n) • P_n)`. -/
instance : Module ℤ_[2] (TateS K S W) where
  smul a P := ⟨fun n => resN n a • (P : ∀ n, Lev K S W n) n, resN_smul_mem a P⟩
  one_smul P := TateS.ext' fun n => by
    change resN n 1 • P.pt n = P.pt n
    rw [resN_one, nsmul_mod_eq (two_pow_nsmul_lev ((P : ∀ n, Lev K S W n) n)), one_nsmul]
  mul_smul a b P := TateS.ext' fun n => by
    change resN n (a * b) • P.pt n = resN n a • (resN n b • P.pt n)
    rw [resN_mul, nsmul_mod_eq (two_pow_nsmul_lev ((P : ∀ n, Lev K S W n) n)), mul_smul]
  smul_zero a := TateS.ext' fun n => nsmul_zero _
  smul_add a P Q := TateS.ext' fun n => nsmul_add _ _ _
  add_smul a b P := TateS.ext' fun n => by
    change resN n (a + b) • P.pt n = resN n a • P.pt n + resN n b • P.pt n
    rw [resN_add, nsmul_mod_eq (two_pow_nsmul_lev ((P : ∀ n, Lev K S W n) n)), add_nsmul]
  zero_smul P := TateS.ext' fun n => by
    change resN n 0 • P.pt n = 0
    rw [resN_zero, zero_nsmul]

theorem TateS.pt_padicSmul (a : ℤ_[2]) (P : TateS K S W) (n : ℕ) :
    (a • P).pt n = resN n a • P.pt n := rfl

/-- The Galois action is `ℤ₂`-linear. Kind: PROVED. -/
instance : SMulCommClass (GKS K S) ℤ_[2] (TateS K S W) where
  smul_comm σ a P := TateS.ext' fun n => by
    change (σ • (a • P)).pt n = (a • (σ • P)).pt n
    rw [TateS.pt_smul, TateS.pt_padicSmul, TateS.pt_padicSmul, TateS.pt_smul, map_nsmul]

/-! ### The projections and their kernels -/

/-- **The projection `T_2E → E(K_S)[2^n]`.** -/
def projLev (n : ℕ) : TateS K S W →+ Lev K S W n where
  toFun P := (P : ∀ n, Lev K S W n) n
  map_zero' := rfl
  map_add' _ _ := rfl

theorem coe_projLev (n : ℕ) (P : TateS K S W) : (projLev n P : Pt K S W) = P.pt n := rfl

theorem projLev_smul (n : ℕ) (σ : GKS K S) (P : TateS K S W) :
    projLev n (σ • P) = σ • projLev n P := rfl

theorem resN_two_pow_self (m : ℕ) : resN m ((2 : ℤ_[2]) ^ m) = 0 := by
  rw [show ((2 : ℤ_[2]) ^ m) = ((2 ^ m : ℕ) : ℤ_[2]) by push_cast; rfl, resN_natCast, Nat.mod_self]

/-- **`ker(T_2E → E(K_S)[2^m]) = 2^m T_2E`**, for every curve (no hypothesis): the inverse-limit
topology of `T_2E` is its `2`-adic topology. Kind: PROVED. -/
theorem mem_ker_projLev_iff (m : ℕ) (P : TateS K S W) :
    P.pt m = 0 ↔ ∃ Q : TateS K S W, (2 : ℤ_[2]) ^ m • Q = P := by
  constructor
  · intro hP
    have hlev : ∀ n, P.pt (n + m) ∈ AddSubgroup.torsionBy (Pt K S W) ((2 ^ n : ℕ) : ℤ) := by
      intro n
      rw [mem_lev_iff, P.pt_congr (Nat.add_comm n m), P.two_pow_smul_pt m n, hP]
    refine ⟨⟨fun n => ⟨P.pt (n + m), hlev n⟩, fun n => ?_⟩, TateS.ext' fun n => ?_⟩
    · apply Subtype.ext
      change 2 • P.pt (n + 1 + m) = P.pt (n + m)
      rw [P.pt_congr (show n + 1 + m = n + m + 1 by omega), P.two_smul_pt]
    · change resN n ((2 : ℤ_[2]) ^ m) • P.pt (n + m) = P.pt n
      rw [show ((2 : ℤ_[2]) ^ m) = ((2 ^ m : ℕ) : ℤ_[2]) by push_cast; rfl, resN_natCast,
        nsmul_mod_eq ((mem_lev_iff _).mp (hlev n)), P.two_pow_smul_pt n m]
  · rintro ⟨Q, rfl⟩
    rw [TateS.pt_padicSmul, resN_two_pow_self, zero_nsmul]

/-! ### The inverse-limit topology -/

variable (K S W) in
/-- The discrete topology on the levels (used to define the topology of `T_2E`). -/
@[reducible] def levTop (n : ℕ) : TopologicalSpace (Lev K S W n) := ⊥

attribute [local instance] levTop

instance (n : ℕ) : DiscreteTopology (Lev K S W n) := ⟨rfl⟩

/-- **The inverse-limit topology on `T_2E`**: the subspace topology of the product of the discrete
`E(K_S)[2^n]`. -/
instance tateTop : TopologicalSpace (TateS K S W) :=
  TopologicalSpace.induced (fun P : TateS K S W => (P : ∀ n, Lev K S W n)) Pi.topologicalSpace

theorem continuous_coe_tate : Continuous (fun P : TateS K S W => (P : ∀ n, Lev K S W n)) :=
  continuous_induced_dom

theorem continuous_projLev (n : ℕ) : Continuous (projLev (K := K) (S := S) (W := W) n) :=
  (continuous_apply n).comp continuous_coe_tate

/-- `T_2E` is a topological group. Kind: PROVED. -/
instance : IsTopologicalAddGroup (TateS K S W) :=
  isTopologicalAddGroup_induced (tateSub K S W).subtype

theorem continuousSMul_lev (n : ℕ) : ContinuousSMul (GKS K S) (Lev K S W n) :=
  continuousSMul_iff_stabilizer_isOpen.mpr fun P => isOpen_stabilizer_torsS P

/-- **The Galois action on `T_2E` is continuous.** Kind: PROVED. -/
instance : ContinuousSMul (GKS K S) (TateS K S W) := by
  refine ⟨continuous_induced_rng.mpr (continuous_pi fun n => ?_)⟩
  have := continuousSMul_lev (K := K) (S := S) (W := W) n
  exact continuous_fst.smul ((continuous_projLev n).comp continuous_snd)

end ZInQ.Manuscript.RC.LambdaCoef
