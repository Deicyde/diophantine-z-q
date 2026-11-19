import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.Tate

/-!
# Lane RC28 round 2: the Tate module `T_2E` is free of rank two over `ℤ₂`

Manuscript `diophantine_zq.tex` (11/5), tex 2836–2838 (`T = T_2E`, the `2`-adic Tate module, with
its `G_{K,S}`-action `ρ_T`). Under `E[2^∞] ⊆ E(K_S)` (`HasFullTwoTorsion`, GLUE input:
Néron–Ogg–Shafarevich, Silverman AEC VII.7.1):

* `transLev_surjective`: `2 : E(K_S)[2^{n+1}] → E(K_S)[2^n]` is onto (its kernel `E[2]` has `4`
  points, and `|E(K_S)[2^m]| = 4^m`);
* `projLev_surjective`: `T_2E → E(K_S)[2^n]` is onto (repeated halving); `tateQuotEquiv`:
  `T_2E / ker ≃ E(K_S)[2^n]`, and `ker_projLev_eq`: the kernel is `2^n T_2E`;
* `tateBasis`: a `ℤ₂`-basis of `T_2E` indexed by `Fin 2` (lifts of a basis of `E[2]` stay bases at
  every level, and compatible coordinates mod `2^n` define `2`-adic integers); `T_2E` is free and
  finite of rank `2`;
* `continuous_coord`: the coordinates are continuous (every `ℤ₂`-linear functional is);
* non-vacuity: `HasFullTwoTorsion K Set.univ W` for every elliptic `W` (`K_{all primes} = K̄`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.LambdaCoef

open NumberField IsDedekindDomain WeierstrassCurve
open scoped Pointwise
open Module (Basis)
open ZInQ.Manuscript.RC.CoefModules (TorsS KS FullTorsion finite_torsS torsS_addEquiv_prod
  inclTors inclTors_injective coe_inclTors natCard_torsBar inclS)
open ZInQ.Contrib.CloudB3RC53.RankCounts (unramifiedOutside IsUnramifiedOutside)

attribute [local instance] levTop

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K}

/-! ### Level counts and the transition maps -/

/-- `E(K_S)[2^n]` is finite. Kind: PROVED (tex 2836–2838). -/
instance finite_lev [W.IsElliptic] (n : ℕ) : Finite (Lev K S W n) :=
  finite_torsS (Nat.cast_ne_zero.mpr (pow_ne_zero n two_ne_zero))

omit [NumberField K] in
/-- `|E(K_S)[2^n]| = (2^n)^2`. Kind: PROVED from the GLUE input `HasFullTwoTorsion`
(Silverman AEC VII.7.1; tex 2836–2838). -/
theorem natCard_lev [HasFullTwoTorsion K S W] (n : ℕ) : Nat.card (Lev K S W n) = (2 ^ n) ^ 2 :=
  HasFullTwoTorsion.full n

/-- A point of `E(K_S)[2]` is killed by `2`. Kind: PROVED (tex 2836–2838). -/
theorem two_nsmul_lev_one (R : Lev K S W 1) : 2 • (R : Pt K S W) = 0 := by
  exact two_pow_nsmul_lev R

/-- The kernel of `2 : E(K_S)[2^{n+1}] → E(K_S)[2^n]` is `E(K_S)[2]`. Kind: definition
(tex 2836–2838). -/
def kerTransEquiv (n : ℕ) : (transLev K S W n).ker ≃ Lev K S W 1 where
  toFun Q := ⟨((Q : Lev K S W (n + 1)) : Pt K S W), by
    rw [mem_lev_iff, pow_one]
    have h := congrArg Subtype.val ((AddMonoidHom.mem_ker).mp Q.2)
    rw [coe_transLev] at h
    exact h⟩
  invFun R := ⟨⟨(R : Pt K S W), by
      rw [mem_lev_iff, pow_succ, mul_smul, two_nsmul_lev_one R, smul_zero]⟩,
    (AddMonoidHom.mem_ker).mpr (Subtype.ext (by rw [coe_transLev]; exact two_nsmul_lev_one R))⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `|ker(2 : E[2^{n+1}] → E[2^n])| = 4`. Kind: PROVED (tex 2836–2838). -/
theorem natCard_ker_transLev [HasFullTwoTorsion K S W] (n : ℕ) :
    Nat.card (transLev K S W n).ker = 4 := by
  rw [Nat.card_congr (kerTransEquiv n), natCard_lev]
  norm_num

/-- **Halving**: `2 : E(K_S)[2^{n+1}] → E(K_S)[2^n]` is surjective. Kind: PROVED (counting: the
kernel has `4` points; tex 2836–2838, under the GLUE input Silverman AEC VII.7.1). -/
theorem transLev_surjective [W.IsElliptic] [HasFullTwoTorsion K S W] (n : ℕ) :
    Function.Surjective (transLev K S W n) := by
  rw [← AddMonoidHom.range_eq_top, ← AddSubgroup.card_eq_iff_eq_top]
  have h1 := AddSubgroup.card_mul_index (transLev K S W n).ker
  rw [AddSubgroup.index_ker, natCard_ker_transLev, natCard_lev,
    show (2 ^ (n + 1)) ^ 2 = 4 * (2 ^ n) ^ 2 by ring] at h1
  rw [natCard_lev]
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h1

/-! ### Surjectivity of the projections -/

/-- Repeated halving of a point of `E(K_S)[2^n]`: a sequence `R_k ∈ E(K_S)[2^{n+k}]` with
`R_0 = P` and `2 R_{k+1} = R_k`. Kind: definition (tex 2836–2838). -/
def halves [W.IsElliptic] [HasFullTwoTorsion K S W] (n : ℕ) (P : Lev K S W n) :
    (k : ℕ) → Lev K S W (n + k)
  | 0 => P
  | k + 1 => (transLev_surjective (K := K) (S := S) (W := W) (n + k) (halves n P k)).choose

/-- `2 R_{k+1} = R_k`. Kind: PROVED (tex 2836–2838). -/
theorem two_smul_halves [W.IsElliptic] [HasFullTwoTorsion K S W] (n : ℕ) (P : Lev K S W n)
    (k : ℕ) : 2 • (halves n P (k + 1) : Pt K S W) = halves n P k :=
  congrArg Subtype.val
    (transLev_surjective (K := K) (S := S) (W := W) (n + k) (halves n P k)).choose_spec

/-- `2^k R_k = P`. Kind: PROVED (tex 2836–2838). -/
theorem two_pow_smul_halves [W.IsElliptic] [HasFullTwoTorsion K S W] (n : ℕ) (P : Lev K S W n)
    (k : ℕ) : (2 ^ k : ℕ) • (halves n P k : Pt K S W) = P := by
  induction k with
  | zero => rw [pow_zero, one_smul]; rfl
  | succ k ih => rw [pow_succ, mul_smul, two_smul_halves, ih]

/-- The point of `T_2E` with level-`m` coordinate `2^n R_m`. Kind: definition (tex 2836–2838). -/
def liftTate [W.IsElliptic] [HasFullTwoTorsion K S W] (n : ℕ) (P : Lev K S W n) :
    TateS K S W :=
  ⟨fun m => ⟨(2 ^ n : ℕ) • (halves n P m : Pt K S W), by
      have h := two_pow_nsmul_lev (halves n P m)
      rw [mem_lev_iff, smul_smul, ← pow_add, Nat.add_comm]
      exact h⟩,
    fun m => Subtype.ext (by
      rw [coe_transLev]
      change 2 • (2 ^ n : ℕ) • (halves n P (m + 1) : Pt K S W) =
        (2 ^ n : ℕ) • (halves n P m : Pt K S W)
      rw [smul_comm, two_smul_halves])⟩

/-- **`T_2E → E(K_S)[2^n]` is surjective.** Kind: PROVED (tex 2836–2838). -/
theorem projLev_surjective [W.IsElliptic] [HasFullTwoTorsion K S W] (n : ℕ) :
    Function.Surjective (projLev (K := K) (S := S) (W := W) n) :=
  fun P => ⟨liftTate n P, Subtype.ext (two_pow_smul_halves n P n)⟩

/-- **`T_2E / ker(proj_n) ≃ E(K_S)[2^n]`.** Kind: definition (tex 2836–2838). -/
def tateQuotEquiv [W.IsElliptic] [HasFullTwoTorsion K S W] (n : ℕ) :
    (TateS K S W ⧸ (projLev (K := K) (S := S) (W := W) n).ker) ≃+ Lev K S W n :=
  QuotientAddGroup.quotientKerEquivOfSurjective _ (projLev_surjective n)

/-- `tateQuotEquiv` on classes. Kind: PROVED (tex 2836–2838). -/
theorem tateQuotEquiv_mk [W.IsElliptic] [HasFullTwoTorsion K S W] (n : ℕ) (P : TateS K S W) :
    tateQuotEquiv n (QuotientAddGroup.mk P) = projLev n P := rfl

/-- **`ker(T_2E → E(K_S)[2^n]) = 2^n T_2E`** (no hypothesis). Kind: PROVED (tex 2836–2838). -/
theorem ker_projLev_eq (n : ℕ) :
    (projLev (K := K) (S := S) (W := W) n).ker =
      ((2 : ℤ_[2]) ^ n • (⊤ : Submodule ℤ_[2] (TateS K S W))).toAddSubgroup := by
  ext P
  rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · intro h
    obtain ⟨Q, hQ⟩ := (mem_ker_projLev_iff n P).mp (congrArg Subtype.val h)
    exact ⟨Q, Submodule.mem_top, hQ⟩
  · rintro ⟨Q, -, hQ⟩
    exact Subtype.ext ((mem_ker_projLev_iff n P).mpr ⟨Q, hQ⟩)

/-! ### Level bases -/

/-- The levels at `1` of `e₁, e₂` are independent mod `2` (a basis of `E[2]`). Kind: definition
(tex 2836–2838). -/
def IndepOne (e₁ e₂ : TateS K S W) : Prop :=
  ∀ a b : ℕ, a • e₁.pt 1 + b • e₂.pt 1 = 0 → 2 ∣ a ∧ 2 ∣ b

/-- **Independence propagates**: `a e₁ₙ + b e₂ₙ = 0` forces `2^n ∣ a, b`. Kind: PROVED
(induction on `n`; tex 2836–2838). -/
theorem dvd_of_indep (e₁ e₂ : TateS K S W) (h1 : IndepOne e₁ e₂) :
    ∀ n a b : ℕ, a • e₁.pt n + b • e₂.pt n = 0 → 2 ^ n ∣ a ∧ 2 ^ n ∣ b := by
  intro n
  induction n with
  | zero => intro a b _; exact ⟨by simp, by simp⟩
  | succ n ih =>
    intro a b h
    have h' : a • e₁.pt n + b • e₂.pt n = 0 := by
      rw [← e₁.two_smul_pt n, ← e₂.two_smul_pt n, smul_comm a 2, smul_comm b 2, ← smul_add, h,
        smul_zero]
    obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := ih a b h'
    have h'' : a' • e₁.pt 1 + b' • e₂.pt 1 = 0 := by
      have q₁ := e₁.two_pow_smul_pt 1 n
      have q₂ := e₂.two_pow_smul_pt 1 n
      rw [e₁.pt_congr (Nat.add_comm 1 n)] at q₁
      rw [e₂.pt_congr (Nat.add_comm 1 n)] at q₂
      rw [← q₁, ← q₂, smul_smul, smul_smul, mul_comm a', mul_comm b']
      exact h
    obtain ⟨⟨a'', rfl⟩, ⟨b'', rfl⟩⟩ := h1 a' b' h''
    exact ⟨⟨a'', by ring⟩, ⟨b'', by ring⟩⟩

/-- The map `(ℤ/2^n)² → E(K_S)[2^n]`, `(a, b) ↦ a x + b y`. Kind: definition (tex 2836–2838). -/
def levPair (n : ℕ) (x y : Lev K S W n) : ZMod (2 ^ n) × ZMod (2 ^ n) →+ Lev K S W n where
  toFun c := c.1.val • x + c.2.val • y
  map_zero' := by simp
  map_add' c d := by
    simp only [Prod.fst_add, Prod.snd_add]
    rw [ZMod.val_add, ZMod.val_add, nsmul_mod_eq (two_pow_nsmul_lev' x),
      nsmul_mod_eq (two_pow_nsmul_lev' y), add_nsmul, add_nsmul]
    abel

/-- `levPair` as points. Kind: PROVED (tex 2836–2838). -/
theorem coe_levPair (n : ℕ) (x y : Lev K S W n) (c : ZMod (2 ^ n) × ZMod (2 ^ n)) :
    ((levPair n x y c : Lev K S W n) : Pt K S W) = c.1.val • (x : Pt K S W) + c.2.val • y := rfl

/-- `levPair` at the levels of an independent pair is injective. Kind: PROVED (tex 2836–2838). -/
theorem levPair_injective (e₁ e₂ : TateS K S W) (h1 : IndepOne e₁ e₂) (n : ℕ) :
    Function.Injective (levPair n (projLev n e₁) (projLev n e₂)) := by
  refine (injective_iff_map_eq_zero _).mpr fun c hc => ?_
  have h : c.1.val • e₁.pt n + c.2.val • e₂.pt n = 0 := congrArg Subtype.val hc
  obtain ⟨d1, d2⟩ := dvd_of_indep e₁ e₂ h1 n _ _ h
  exact Prod.ext ((ZMod.val_eq_zero _).mp (Nat.eq_zero_of_dvd_of_lt d1 (ZMod.val_lt _)))
    ((ZMod.val_eq_zero _).mp (Nat.eq_zero_of_dvd_of_lt d2 (ZMod.val_lt _)))

/-- **The levels of an independent pair are `ℤ/2^n`-bases of `E(K_S)[2^n]`.** Kind: PROVED
(injective, and both sides have `4^n` elements; tex 2836–2838). -/
theorem levPair_bijective [W.IsElliptic] [HasFullTwoTorsion K S W] (e₁ e₂ : TateS K S W)
    (h1 : IndepOne e₁ e₂) (n : ℕ) :
    Function.Bijective (levPair n (projLev n e₁) (projLev n e₂)) :=
  (levPair_injective e₁ e₂ h1 n).bijective_of_nat_card_le
    (le_of_eq (by rw [natCard_lev, Nat.card_prod, Nat.card_zmod, sq]))

/-- An independent pair exists (lifts of a basis of `E(K_S)[2]`). Kind: PROVED (tex 2836–2838). -/
theorem exists_indepOne [W.IsElliptic] [HasFullTwoTorsion K S W] :
    ∃ e₁ e₂ : TateS K S W, IndepOne e₁ e₂ := by
  obtain ⟨φ⟩ := torsS_addEquiv_prod W (HasFullTwoTorsion.full (K := K) (S := S) (W := W) 1)
  obtain ⟨e₁, he₁⟩ := projLev_surjective (K := K) (S := S) (W := W) 1 (φ.symm (1, 0))
  obtain ⟨e₂, he₂⟩ := projLev_surjective (K := K) (S := S) (W := W) 1 (φ.symm (0, 1))
  refine ⟨e₁, e₂, fun a b h => ?_⟩
  have h' : a • φ.symm (1, 0) + b • φ.symm (0, 1) = 0 := by
    apply Subtype.ext
    rw [← he₁, ← he₂]
    exact h
  rw [← map_nsmul, ← map_nsmul, ← map_add, AddEquiv.map_eq_zero_iff] at h'
  simp only [Prod.smul_mk, Prod.mk_add_mk, nsmul_eq_mul, mul_one, mul_zero, add_zero, zero_add,
    Prod.mk_eq_zero] at h'
  have ha := (ZMod.natCast_eq_zero_iff a (2 ^ 1)).mp h'.1
  have hb := (ZMod.natCast_eq_zero_iff b (2 ^ 1)).mp h'.2
  rw [pow_one] at ha hb
  exact ⟨ha, hb⟩

/-! ### `2`-adic integers from compatible residues -/

/-- **Compatible residues mod `2^n` define a `2`-adic integer.** Kind: PROVED (Mathlib's
`PadicInt.lift` applied to evaluation maps on `ℤ[X]`; tex 2836–2838). -/
theorem exists_padicInt_of_compat (α : ∀ n : ℕ, ZMod (2 ^ n))
    (hα : ∀ k1 k2 (h : k1 ≤ k2), ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2 ^ k1)) (α k2) = α k1) :
    ∃ a : ℤ_[2], ∀ n, PadicInt.toZModPow n a = α n := by
  let f : ∀ k : ℕ, Polynomial ℤ →+* ZMod (2 ^ k) :=
    fun k => Polynomial.eval₂RingHom (Int.castRingHom _) (α k)
  have hf : ∀ (k1 k2) (hk : k1 ≤ k2),
      (ZMod.castHom (pow_dvd_pow 2 hk) _).comp (f k2) = f k1 := by
    intro k1 k2 hk
    apply Polynomial.ringHom_ext
    · intro c
      simp [f]
    · simpa [f] using hα k1 k2 hk
  refine ⟨PadicInt.lift hf Polynomial.X, fun n => ?_⟩
  have := congrArg (fun g => g Polynomial.X) (PadicInt.lift_spec hf n)
  simpa [f] using this

/-! ### The basis -/

/-- The `ℤ₂`-linear map `ℤ₂² → T_2E`, `c ↦ c₀ e₁ + c₁ e₂`. Kind: definition (tex 2836–2838). -/
def pairMap (e₁ e₂ : TateS K S W) : (Fin 2 → ℤ_[2]) →ₗ[ℤ_[2]] TateS K S W :=
  (LinearMap.proj 0).smulRight e₁ + (LinearMap.proj 1).smulRight e₂

/-- `pairMap e₁ e₂ c = c₀ e₁ + c₁ e₂`. Kind: PROVED (tex 2836–2838). -/
theorem pairMap_apply (e₁ e₂ : TateS K S W) (c : Fin 2 → ℤ_[2]) :
    pairMap e₁ e₂ c = c 0 • e₁ + c 1 • e₂ := rfl

/-- `pairMap` is injective for an independent pair. Kind: PROVED (tex 2836–2838). -/
theorem pairMap_injective (e₁ e₂ : TateS K S W) (h1 : IndepOne e₁ e₂) :
    Function.Injective (pairMap e₁ e₂) := by
  refine (injective_iff_map_eq_zero _).mpr fun c hc => ?_
  rw [pairMap_apply] at hc
  have hn : ∀ n, PadicInt.toZModPow n (c 0) = 0 ∧ PadicInt.toZModPow n (c 1) = 0 := by
    intro n
    have h : resN n (c 0) • e₁.pt n + resN n (c 1) • e₂.pt n = 0 :=
      congrArg (fun P : TateS K S W => P.pt n) hc
    obtain ⟨d0, d1⟩ := dvd_of_indep e₁ e₂ h1 n _ _ h
    exact ⟨(ZMod.val_eq_zero _).mp (Nat.eq_zero_of_dvd_of_lt d0 (resN_lt n _)),
      (ZMod.val_eq_zero _).mp (Nat.eq_zero_of_dvd_of_lt d1 (resN_lt n _))⟩
  refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
  · show c 0 = 0
    exact PadicInt.ext_of_toZModPow.mp fun n => by rw [(hn n).1, map_zero]
  · show c 1 = 0
    exact PadicInt.ext_of_toZModPow.mp fun n => by rw [(hn n).2, map_zero]

/-- `pairMap` is surjective for an independent pair. Kind: PROVED (level coordinates are
compatible, hence `2`-adic integers; tex 2836–2838). -/
theorem pairMap_surjective [W.IsElliptic] [HasFullTwoTorsion K S W] (e₁ e₂ : TateS K S W)
    (h1 : IndepOne e₁ e₂) : Function.Surjective (pairMap e₁ e₂) := by
  intro P
  have hb := fun n => levPair_bijective e₁ e₂ h1 n
  choose c hc using fun n => (hb n).2 (projLev n P)
  have hcP : ∀ n, (c n).1.val • e₁.pt n + (c n).2.val • e₂.pt n = P.pt n :=
    fun n => congrArg Subtype.val (hc n)
  have hcompat : ∀ k1 k2 (h : k1 ≤ k2),
      ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2 ^ k1)) (c k2).1 = (c k1).1 ∧
      ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2 ^ k1)) (c k2).2 = (c k1).2 := by
    intro k1 k2 h
    have key : levPair k1 (projLev k1 e₁) (projLev k1 e₂)
        (ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2 ^ k1)) (c k2).1,
          ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2 ^ k1)) (c k2).2) =
        levPair k1 (projLev k1 e₁) (projLev k1 e₂) (c k1) := by
      rw [hc k1]
      apply Subtype.ext
      rw [coe_levPair]
      simp only [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
      have p₁ := e₁.two_pow_smul_pt k1 (k2 - k1)
      have p₂ := e₂.two_pow_smul_pt k1 (k2 - k1)
      have p := P.two_pow_smul_pt k1 (k2 - k1)
      rw [e₁.pt_congr (Nat.add_sub_cancel' h)] at p₁
      rw [e₂.pt_congr (Nat.add_sub_cancel' h)] at p₂
      rw [P.pt_congr (Nat.add_sub_cancel' h)] at p
      rw [nsmul_mod_eq (two_pow_nsmul_lev (projLev k1 e₁)),
        nsmul_mod_eq (two_pow_nsmul_lev (projLev k1 e₂)), coe_projLev,
        coe_projLev, coe_projLev, ← p₁, ← p₂, ← p, ← hcP k2, smul_add, smul_comm _ (c k2).1.val,
        smul_comm _ (c k2).2.val]
    have := (hb k1).1 key
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  obtain ⟨a, ha⟩ := exists_padicInt_of_compat (fun n => (c n).1)
    (fun k1 k2 h => (hcompat k1 k2 h).1)
  obtain ⟨b, hb'⟩ := exists_padicInt_of_compat (fun n => (c n).2)
    (fun k1 k2 h => (hcompat k1 k2 h).2)
  refine ⟨![a, b], TateS.ext' fun n => ?_⟩
  rw [pairMap_apply]
  change resN n a • e₁.pt n + resN n b • e₂.pt n = P.pt n
  rw [resN, resN, ha n, hb' n]
  exact hcP n

/-- The basis attached to an independent pair. Kind: definition (tex 2836–2838). -/
def basisOfPair [W.IsElliptic] [HasFullTwoTorsion K S W] {e₁ e₂ : TateS K S W}
    (h1 : IndepOne e₁ e₂) : Basis (Fin 2) ℤ_[2] (TateS K S W) :=
  Basis.ofEquivFun (LinearEquiv.ofBijective (pairMap e₁ e₂)
    ⟨pairMap_injective e₁ e₂ h1, pairMap_surjective e₁ e₂ h1⟩).symm

/-- **`T_2E` has a `ℤ₂`-basis of size two.** Kind: PROVED (tex 2836–2838). -/
theorem exists_basis [W.IsElliptic] [HasFullTwoTorsion K S W] :
    Nonempty (Basis (Fin 2) ℤ_[2] (TateS K S W)) := by
  obtain ⟨e₁, e₂, h⟩ := exists_indepOne (K := K) (S := S) (W := W)
  exact ⟨basisOfPair h⟩

/-- **A `ℤ₂`-basis of `T_2E`** (tex 2836–2838). Kind: definition. -/
def tateBasis [W.IsElliptic] [HasFullTwoTorsion K S W] : Basis (Fin 2) ℤ_[2] (TateS K S W) :=
  Classical.choice exists_basis

/-- `T_2E` is a free `ℤ₂`-module. Kind: PROVED (tex 2836–2838). -/
instance free_tate [W.IsElliptic] [HasFullTwoTorsion K S W] : Module.Free ℤ_[2] (TateS K S W) :=
  Module.Free.of_basis tateBasis

/-- `T_2E` is a finite `ℤ₂`-module. Kind: PROVED (tex 2836–2838). -/
instance finite_tate [W.IsElliptic] [HasFullTwoTorsion K S W] :
    Module.Finite ℤ_[2] (TateS K S W) :=
  Module.Finite.of_basis tateBasis

/-- **`rank_{ℤ₂} T_2E = 2`.** Kind: PROVED (tex 2836–2838). -/
theorem finrank_tate [W.IsElliptic] [HasFullTwoTorsion K S W] :
    Module.finrank ℤ_[2] (TateS K S W) = 2 := by
  rw [Module.finrank_eq_card_basis (tateBasis (K := K) (S := S) (W := W)), Fintype.card_fin]

/-! ### Continuity of the coordinates -/

/-- **Every `ℤ₂`-linear functional on `T_2E` is continuous** (`ker proj_n = 2^n T_2E` is open
and maps into `2^n ℤ₂`). Kind: PROVED (tex 2836–2838). -/
theorem continuous_of_linear (f : TateS K S W →ₗ[ℤ_[2]] ℤ_[2]) : Continuous f := by
  refine continuous_of_continuousAt_zero f ?_
  unfold ContinuousAt
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  have hopen : IsOpen {P : TateS K S W | projLev n P = 0} :=
    (isOpen_discrete {(0 : Lev K S W n)}).preimage (continuous_projLev n)
  filter_upwards [hopen.mem_nhds (show (0 : TateS K S W) ∈ {P | projLev n P = 0} from map_zero _)]
    with P hP
  obtain ⟨Q, rfl⟩ := (mem_ker_projLev_iff n P).mp (congrArg Subtype.val (show projLev n P = 0
    from hP))
  rw [map_smul, map_zero, dist_zero_right, smul_eq_mul]
  have h2 : ‖(2 : ℤ_[2]) ^ n‖ = (1 / 2 : ℝ) ^ n := by
    have := PadicInt.norm_p_pow (p := 2) n
    rw [Nat.cast_ofNat] at this
    rw [this, zpow_neg, zpow_natCast, one_div, inv_pow]
    norm_num
  calc ‖(2 : ℤ_[2]) ^ n * f Q‖ = ‖(2 : ℤ_[2]) ^ n‖ * ‖f Q‖ := norm_mul _ _
    _ ≤ ‖(2 : ℤ_[2]) ^ n‖ * 1 := mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (norm_nonneg _)
    _ < ε := by rw [mul_one, h2]; exact hn

/-- **The coordinates of `tateBasis` are continuous.** Kind: PROVED (tex 2836–2838). -/
theorem continuous_coord [W.IsElliptic] [HasFullTwoTorsion K S W] (i : Fin 2) :
    Continuous fun P : TateS K S W => tateBasis.repr P i :=
  (continuous_of_linear ((tateBasis (K := K) (S := S) (W := W)).coord i)).congr fun _ =>
    Module.Basis.coord_apply _ _ _

/-! ### Non-vacuity -/

/-- Every finite subextension of `K̄/K` lies in `K_S` for `S` the set of all primes (its normal
closure is finite and normal, and the unramifiedness condition is vacuous). Kind: PROVED
(tex 2836–2838). -/
theorem le_unramifiedOutside_univ (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] : E ≤ unramifiedOutside K Set.univ := by
  have hL : FiniteDimensional K (IntermediateField.normalClosure K E (AlgebraicClosure K)) ∧
      Normal K (IntermediateField.normalClosure K E (AlgebraicClosure K)) ∧
      IsUnramifiedOutside K Set.univ (IntermediateField.normalClosure K E (AlgebraicClosure K)) :=
    ⟨normalClosure.is_finiteDimensional K E _, normalClosure.normal K E _,
      fun v hv => absurd (Set.mem_univ v) hv⟩
  refine E.le_normalClosure.trans ?_
  unfold unramifiedOutside
  exact le_iSup₂_of_le (IntermediateField.normalClosure K E (AlgebraicClosure K)) hL le_rfl

/-- **`K_S = K̄` for `S` the set of all primes** (the unramifiedness condition is vacuous).
Kind: PROVED (tex 2836–2838). -/
theorem unramifiedOutside_univ : unramifiedOutside K Set.univ = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  have : FiniteDimensional K (IntermediateField.adjoin K {x}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  exact le_unramifiedOutside_univ _ (IntermediateField.mem_adjoin_simple_self K x)

omit [NumberField K] in
/-- The point map along the identity is the identity. Kind: PROVED (tex 2836–2838). -/
theorem map_algHom_id {L : Type} [Field L] [Algebra K L] [DecidableEq L]
    (P : (W.baseChange L).toAffine.Point) : Affine.Point.map (AlgHom.id K L) P = P := by
  rcases P with _ | ⟨x, y, h⟩
  · exact map_zero _
  · rw [Affine.Point.map_some]
    rfl

/-- For all primes, `E(K_S)[N] → E(K̄)[N]` is onto. Kind: PROVED (tex 2836–2838). -/
theorem inclTors_surjective_univ [W.IsElliptic] (N : ℕ) [NeZero N] :
    Function.Surjective (inclTors (S := Set.univ) W N) := by
  intro Q
  let e : KS K Set.univ ≃ₐ[K] AlgebraicClosure K :=
    (IntermediateField.equivOfEq unramifiedOutside_univ).trans IntermediateField.topEquiv
  have hcomp : (inclS K Set.univ).comp e.symm.toAlgHom = AlgHom.id K _ := by
    ext y
    rfl
  refine ⟨⟨Affine.Point.map e.symm.toAlgHom Q.1, ?_⟩, ?_⟩
  · have hQ : (N : ℤ) • Q.1 = 0 := (Submodule.mem_torsionBy_iff _ _).mp Q.2
    change _ ∈ Submodule.torsionBy ℤ _ (N : ℤ)
    rw [Submodule.mem_torsionBy_iff, ← map_zsmul, hQ, map_zero]
  · apply Subtype.ext
    rw [coe_inclTors, Affine.Point.map_map, hcomp, map_algHom_id]

/-- **Non-vacuity**: for `S` the set of all primes, `E[2^∞] ⊆ E(K_S)`. Kind: PROVED
(tex 2836–2838; no Néron–Ogg–Shafarevich input needed here). -/
instance hasFullTwoTorsion_univ [W.IsElliptic] : HasFullTwoTorsion K Set.univ W where
  full n := by
    have hb : Function.Bijective (inclTors (S := Set.univ) W (2 ^ n)) :=
      ⟨inclTors_injective W _, inclTors_surjective_univ _⟩
    unfold FullTorsion
    rw [Nat.card_congr (Equiv.ofBijective _ hb), natCard_torsBar]

/-- Non-vacuity of the basis: `T_2E` over `K_{all primes}` has rank two. Kind: PROVED
(tex 2836–2838). -/
example [W.IsElliptic] : Nonempty (Basis (Fin 2) ℤ_[2] (TateS K Set.univ W)) ∧
    Module.finrank ℤ_[2] (TateS K Set.univ W) = 2 :=
  ⟨exists_basis, finrank_tate⟩

end ZInQ.Manuscript.RC.LambdaCoef
