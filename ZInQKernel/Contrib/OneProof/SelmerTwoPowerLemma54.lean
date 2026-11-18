import ZInQKernel.Contrib.OneProof.PoleS12.Leaves

/-!
# The `ℤ₂`-corank is well defined, and Lemma 5.4 from its leaves

Fork issue #83. Over the genuine Selmer groups of `ZInQ.Manuscript.SelmerTwoPower`
(`selmerAt E 1 = Sel₂(E/ℚ)`, `selmerTwoPower E = Sel_{2^∞}(E/ℚ)`, `Z2Corank`, `SelmerCorankOne`):

* `corank_unique`, `Z2Corank.unique`: the corank is well defined, `Z2Corank M r` holds for at most
  one `r` (count `2ᵏ`-torsion: `#(ℚ₂/ℤ₂)[2ᵏ] = 2ᵏ`).
* The leaves of Lemma 5.4: `MazurRubinParityTwo` (printed: Mazur–Rubin, Invent. Math. 181 (2010),
  §2, proof of Lemma 2.5, display (2)); `SelmerCofinite`, `KummerSelmerRelation` (textbook GLUE).
* `lemma54_of_leaves`: Lemma 5.4 (`lem:corank`, `diophantine_zq.tex` lines 1072–1084), in the form
  `ZInQ.Manuscript.PoleS12.Lemma54`, from the three leaves.
-/

open WeierstrassCurve

namespace ZInQ.Manuscript.SelmerTwoPower

/-! ### The corank is well defined -/

section Corank

/-- The `m`-torsion subgroup of an abelian group, as a type. -/
abbrev TorsionType (A : Type*) [AddCommGroup A] (m : ℕ) : Type _ := {a : A // m • a = 0}

lemma card_torsionType_congr {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B)
    (m : ℕ) : Nat.card (TorsionType A m) = Nat.card (TorsionType B m) :=
  Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
    change m • x = 0 ↔ m • e x = 0
    rw [← map_nsmul, AddEquivClass.map_eq_zero_iff])

lemma card_torsionType_prod (A B : Type*) [AddCommGroup A] [AddCommGroup B] (m : ℕ) :
    Nat.card (TorsionType (A × B) m) = Nat.card (TorsionType A m) * Nat.card (TorsionType B m) := by
  rw [← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun x => (⟨x.1.1, congrArg Prod.fst x.2⟩, ⟨x.1.2, congrArg Prod.snd x.2⟩)
      invFun := fun y => ⟨(y.1.1, y.2.1), Prod.ext y.1.2 y.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

lemma card_torsionType_pi (A : Type*) [AddCommGroup A] (m r : ℕ) :
    Nat.card (TorsionType (Fin r → A) m) = Nat.card (TorsionType A m) ^ r := by
  rw [show Nat.card (TorsionType A m) ^ r = Nat.card (Fin r → TorsionType A m) by
    rw [Nat.card_fun, Nat.card_fin]]
  refine Nat.card_congr
    { toFun := fun x i => ⟨x.1 i, congrFun x.2 i⟩
      invFun := fun y => ⟨fun i => (y i).1, funext fun i => (y i).2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

/-- `#(ℚ₂/ℤ₂)[2ᵏ] = 2ᵏ`. -/
lemma card_torsionType_Q2Z2 (k : ℕ) : Nat.card (TorsionType Q2Z2 (2 ^ k)) = 2 ^ k := by
  have hp0 : (2 : ℚ_[2]) ≠ 0 := by norm_num
  have hpk : ((2 : ℚ_[2]) ^ k) ≠ 0 := pow_ne_zero _ hp0
  have hint : ∀ x : ℚ_[2], x ∈ (PadicInt.subring 2).toAddSubgroup ↔ ‖x‖ ≤ 1 :=
    fun x => PadicInt.mem_subring_iff 2
  have hnat : ∀ n : ℕ, ‖(n : ℚ_[2])‖ ≤ 1 := fun n => by
    have := PadicInt.norm_le_one (n : ℤ_[2]); exact_mod_cast this
  let f : ZMod (2 ^ k) → TorsionType Q2Z2 (2 ^ k) := fun a =>
    ⟨(((a.val : ℚ_[2]) / (2 : ℚ_[2]) ^ k : ℚ_[2]) : Q2Z2), by
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, nsmul_eq_mul, hint]
      push_cast
      rw [mul_div_cancel₀ _ hpk]
      exact hnat _⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have h1 := congrArg Subtype.val hab
      simp only [f] at h1
      rw [QuotientAddGroup.eq, hint] at h1
      obtain ⟨w, hw0⟩ : ∃ w : ℤ_[2], (w : ℚ_[2]) =
          -((a.val : ℚ_[2]) / (2 : ℚ_[2]) ^ k) + (b.val : ℚ_[2]) / (2 : ℚ_[2]) ^ k :=
        ⟨⟨_, h1⟩, rfl⟩
      have hw : ((a.val : ℤ_[2]) - (b.val : ℤ_[2])) = ((2 : ℕ) : ℤ_[2]) ^ k * (-w) := by
        apply PadicInt.ext
        simp only [PadicInt.coe_sub, PadicInt.coe_natCast, PadicInt.coe_mul, PadicInt.coe_pow,
          PadicInt.coe_neg, hw0]
        push_cast
        field_simp
        ring
      have h2 := congrArg (PadicInt.toZModPow k) hw
      rw [map_sub, map_natCast, map_natCast, map_mul, map_pow, map_natCast,
        ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h2
      have h3 : (((2 : ℕ) : ZMod (2 ^ k)) ^ k) = 0 := by
        rw [← Nat.cast_pow, ZMod.natCast_self]
      rw [h3, zero_mul, sub_eq_zero] at h2
      exact h2
    · rintro ⟨t, ht⟩
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective t
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, hint] at ht
      obtain ⟨y, hy0⟩ : ∃ y : ℤ_[2], (y : ℚ_[2]) = 2 ^ k • x := ⟨⟨_, ht⟩, rfl⟩
      refine ⟨PadicInt.toZModPow k y, Subtype.ext ?_⟩
      simp only [f]
      rw [QuotientAddGroup.eq, hint]
      have hy : y - ((PadicInt.toZModPow k y).val : ℤ_[2]) ∈
          RingHom.ker (PadicInt.toZModPow k : ℤ_[2] →+* ZMod (2 ^ k)) := by
        rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
      rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hy
      obtain ⟨w, hw⟩ := hy
      have hw' := congrArg (fun z : ℤ_[2] => (z : ℚ_[2])) hw
      simp only [PadicInt.coe_sub, PadicInt.coe_natCast, PadicInt.coe_mul,
        PadicInt.coe_pow, hy0] at hw'
      have : -((((PadicInt.toZModPow k y).val : ℚ_[2]) / (2 : ℚ_[2]) ^ k)) + x = (w : ℚ_[2]) := by
        field_simp
        rw [nsmul_eq_mul] at hw'
        push_cast at hw'
        linear_combination hw'
      rw [this]
      exact PadicInt.norm_le_one w
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_zmod]

lemma card_torsionType_finite_le {F : Type*} [AddCommGroup F] [Finite F] (m : ℕ) :
    1 ≤ Nat.card (TorsionType F m) ∧ Nat.card (TorsionType F m) ≤ Nat.card F := by
  constructor
  · have : Nonempty (TorsionType F m) := ⟨⟨0, smul_zero _⟩⟩
    exact Nat.one_le_iff_ne_zero.mpr (Nat.card_pos.ne')
  · exact Nat.card_le_card_of_injective _ Subtype.val_injective

/-- **The corank is well defined**: `(ℚ₂/ℤ₂)^r × F₁ ≅ (ℚ₂/ℤ₂)^s × F₂` with `F₁, F₂` finite forces
`r = s`. -/
theorem corank_unique {A : Type*} [AddCommGroup A] {r s : ℕ} {F₁ F₂ : Type}
    [AddCommGroup F₁] [Finite F₁] [AddCommGroup F₂] [Finite F₂]
    (e₁ : A ≃+ (Fin r → Q2Z2) × F₁) (e₂ : A ≃+ (Fin s → Q2Z2) × F₂) : r = s := by
  have key : ∀ k : ℕ, 2 ^ (k * r) * Nat.card (TorsionType F₁ (2 ^ k)) =
      2 ^ (k * s) * Nat.card (TorsionType F₂ (2 ^ k)) := by
    intro k
    have h1 := card_torsionType_congr e₁ (2 ^ k)
    have h2 := card_torsionType_congr e₂ (2 ^ k)
    rw [card_torsionType_prod, card_torsionType_pi, card_torsionType_Q2Z2] at h1 h2
    rw [pow_mul, pow_mul, ← h1, ← h2]
  have aux : ∀ {r s : ℕ} {F₁ F₂ : Type} [AddCommGroup F₁] [Finite F₁] [AddCommGroup F₂]
      [Finite F₂], (∀ k : ℕ, 2 ^ (k * r) * Nat.card (TorsionType F₁ (2 ^ k)) =
        2 ^ (k * s) * Nat.card (TorsionType F₂ (2 ^ k))) → ¬ r < s := by
    intro r s F₁ F₂ _ _ _ _ hk hrs
    set N := Nat.card F₁
    have h := hk N
    obtain ⟨-, hle⟩ := card_torsionType_finite_le (F := F₁) (2 ^ N)
    obtain ⟨hge, -⟩ := card_torsionType_finite_le (F := F₂) (2 ^ N)
    have hsplit : 2 ^ (N * s) = 2 ^ (N * r) * 2 ^ (N * (s - r)) := by
      rw [← pow_add]; congr 1
      rw [← Nat.mul_add]; congr 1; omega
    rw [hsplit, mul_assoc] at h
    have hpos : 0 < 2 ^ (N * r) := pow_pos (by omega) _
    have h' := Nat.eq_of_mul_eq_mul_left hpos h
    have hlt : N < 2 ^ (N * (s - r)) := by
      calc N < 2 ^ N := Nat.lt_two_pow_self
        _ ≤ 2 ^ (N * (s - r)) := Nat.pow_le_pow_right (by omega)
            (Nat.le_mul_of_pos_right N (by omega))
    have : 2 ^ (N * (s - r)) ≤ N := by
      calc 2 ^ (N * (s - r)) ≤ 2 ^ (N * (s - r)) * Nat.card (TorsionType F₂ (2 ^ N)) :=
            Nat.le_mul_of_pos_right _ hge
        _ = Nat.card (TorsionType F₁ (2 ^ N)) := h'.symm
        _ ≤ N := hle
    omega
  rcases lt_trichotomy r s with h | h | h
  · exact absurd h (aux key)
  · exact h
  · exact absurd h (aux fun k => (key k).symm)

/-- `Z2Corank M r` holds for at most one `r`. -/
theorem Z2Corank.unique {M : Type*} [AddCommGroup M] {r s : ℕ} (hr : Z2Corank M r)
    (hs : Z2Corank M s) : r = s := by
  obtain ⟨F₁, _, _, ⟨e₁⟩⟩ := hr
  obtain ⟨F₂, _, _, ⟨e₂⟩⟩ := hs
  exact corank_unique e₁ e₂

end Corank

/-! ### The leaves of Lemma 5.4 -/

/-- **The parity of the `2^∞`-Selmer corank (printed leaf).** Mazur–Rubin, "Ranks of twists of
elliptic curves and Hilbert's tenth problem", Invent. Math. 181 (2010), §2, proof of Lemma 2.5,
display (2), for an elliptic curve over a number field `K`:
`corank_{ℤ₂}(Sel_{2^∞}(E/K)) ≡ d₂(E/K) + dim_{𝔽₂} E(K)[2] (mod 2)`, `d₂ = dim_{𝔽₂} Sel₂(E/K)` (the
print has `ℤ_p` for `ℤ₂`; journal page not determined, arXiv 0904.3709v3 p. 6). The display is
asserted inside a proof ("Using the Cassels pairing it is straightforward to show (see for example
[MR2, Proposition 2.1])"), and [MR2] = Mazur–Rubin, Ann. of Math. 166 (2007), Proposition 2.1, is
stated for odd `p`; the argument for `p = 2` is the same, from Cassels' theorem that the pairing on
`Ш/div` is alternating (Poonen–Stoll, Ann. of Math. 150 (1999), Remarks after Corollary 12) and
nondegenerate (Milne, ADT I Theorem 6.13(a)).

Here for `K = ℚ`, the Selmer groups of `SelmerTwoPower`, and `E(ℚ)[2]` as the kernel of
multiplication by `2` on `E(ℚ)` (the spelling of `PoleS12.FullTwoTorsion`). Mazur–Rubin's `Sel₂`
(Definition 2.3, local Kummer images) is Tau Ceti's kernel-defined `selmerGroup`
(`WeierstrassCurve.mem_selmerGroup_iff_forall_torsionRes_mem_range_kummerMap`), and their
`Sel_{2^∞} = lim→ Sel_{2ⁿ}` is the kernel `selmerTwoPower` (Milne, ADT I §6, p. 75). The
manuscript's proof of Lemma 5.4 (`diophantine_zq.tex` lines 1076–1084) uses the Cassels–Tate
pairing on `Ш[2^∞]/div` directly (`\cite{poonenstoll}`, line 1081, no theorem numbers in the 11/5
text; Version 19 cites Corollaries 4, 7 and Theorem 8); this leaf is the printed consequence of the
same pairing argument. -/
def MazurRubinParityTwo : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → ∀ r a b : ℕ, Z2Corank (selmerTwoPower E) r →
    Nat.card (selmerAt E 1) = 2 ^ a →
    Nat.card (nsmulAddMonoidHom 2 : E.toAffine.Point →+ E.toAffine.Point).ker = 2 ^ b →
    r ≡ a + b [MOD 2]

/-- **`Sel_{2^∞}(E/ℚ)` is cofinitely generated (GLUE, textbook).** Milne, *Arithmetic Duality
Theorems*, 2nd ed., I Remark 6.7, p. 77: `S(K, A)(m)` is an extension of a finite group by a
divisible group isomorphic to a direct sum of copies of `ℚ_ℓ/ℤ_ℓ`; the divisible subgroup is a
direct summand (divisible groups are injective), with finitely many copies since `Sel_{2^∞}[2]` is
finite. -/
def SelmerCofinite : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → ∃ r : ℕ, Z2Corank (selmerTwoPower E) r

/-- **`#Sel₂(E/ℚ) = #E(ℚ)[2] · #Sel_{2^∞}(E/ℚ)[2]` (GLUE, textbook).** The long exact sequence of
`0 → E[2] → E[2^∞] → E[2^∞] → 0` (multiplication by `2` is onto on `E(ℚˢ)[2^∞]`) shows that
`H¹(G_ℚ, E[2]) → H¹(G_ℚ, E[2^∞])[2]` is onto with kernel `E(ℚ)[2^∞]/2`; with the kernel definitions,
`Sel₂` is the preimage of `Sel_{2^∞}`, so `Sel₂ → Sel_{2^∞}[2]` is onto with the same kernel, and
`#E(ℚ)[2^∞]/2 = #E(ℚ)[2]` since `E(ℚ)[2^∞]` is finite. Equivalently, from Milne ADT I Prop. 6.4 and
Mazur–Rubin 2007 (2.1)–(2.2) with Mordell–Weil. Tau Ceti's long exact sequence of continuous
cohomology makes this provable in Lean. (Not to be confused with `PoleS12.KummerSelmerM`, which
compares the explicit system `SelM ℓ` with `Sel₂(E_ℓ/ℚ)`.) -/
def KummerSelmerRelation : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic →
    Nat.card (selmerAt E 1) =
      Nat.card (nsmulAddMonoidHom 2 : E.toAffine.Point →+ E.toAffine.Point).ker *
        Nat.card {x : selmerTwoPower E // (2 : ℕ) • x = 0}

private lemma half_ne_zero_two_torsion :
    ((((2 : ℚ_[2])⁻¹ : ℚ_[2]) : Q2Z2) ≠ 0) ∧
      (2 : ℕ) • (((2 : ℚ_[2])⁻¹ : ℚ_[2]) : Q2Z2) = 0 := by
  constructor
  · rw [Ne, QuotientAddGroup.eq_zero_iff]
    intro h
    have h' : ‖((2 : ℚ_[2])⁻¹)‖ ≤ 1 := (PadicInt.mem_subring_iff 2).mp h
    rw [norm_inv] at h'
    have h2 : ‖(2 : ℚ_[2])‖ = 2⁻¹ := by
      have := Padic.norm_p (p := 2)
      exact_mod_cast this
    rw [h2, inv_inv] at h'
    norm_num at h'
  · rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    rw [nsmul_eq_mul]
    norm_num

private lemma two_pow_le_card_torsion (r : ℕ) (F : Type) [AddCommGroup F]
    [Finite {y : (Fin r → Q2Z2) × F // (2 : ℕ) • y = 0}] :
    2 ^ r ≤ Nat.card {y : (Fin r → Q2Z2) × F // (2 : ℕ) • y = 0} := by
  obtain ⟨hne, h2⟩ := half_ne_zero_two_torsion
  set h : Q2Z2 := (((2 : ℚ_[2])⁻¹ : ℚ_[2]) : Q2Z2)
  let f : (Fin r → Bool) → {y : (Fin r → Q2Z2) × F // (2 : ℕ) • y = 0} := fun ε =>
    ⟨(fun i => if ε i then h else 0, 0), by
      ext i
      · simp only [Prod.smul_fst, Pi.smul_apply, Prod.fst_zero, Pi.zero_apply]
        split_ifs
        · exact h2
        · exact smul_zero _
      · simp⟩
  have hf : Function.Injective f := by
    intro ε δ hεδ
    funext i
    have := congrArg (fun y => y.1.1 i) hεδ
    simp only [f] at this
    by_cases hε : ε i <;> by_cases hδ : δ i <;> simp_all
  have := Nat.card_le_card_of_injective f hf
  simpa [Nat.card_fun] using this

/-- **Lemma 5.4 from its leaves**, in the form `PoleS12.Lemma54`. With `#Sel₂ = 8` and
`#E(ℚ)[2] = 4`, `KummerSelmerRelation` gives `#Sel_{2^∞}[2] = 2`; for
`Sel_{2^∞} ≅ (ℚ₂/ℤ₂)^r × F` (`SelmerCofinite`) the `2^r` points `(ε_i/2)_i` are `2`-torsion, so
`r ≤ 1`; parity (`MazurRubinParityTwo`, `3 + 2` odd) gives `r = 1`. -/
theorem lemma54_of_leaves (hP : MazurRubinParityTwo) (hC : SelmerCofinite)
    (hK : KummerSelmerRelation) : PoleS12.Lemma54 := by
  intro E hE h4 h8
  have h4' : Nat.card (nsmulAddMonoidHom 2 : E.toAffine.Point →+ E.toAffine.Point).ker = 4 := h4
  have hk := hK E hE
  rw [h8, h4'] at hk
  have hN : Nat.card {x : selmerTwoPower E // (2 : ℕ) • x = 0} = 2 := by omega
  obtain ⟨r, F, hF1, hF2, ⟨e⟩⟩ := hC E hE
  have hN' : Nat.card {y : (Fin r → Q2Z2) × F // (2 : ℕ) • y = 0} = 2 := by
    rw [← card_torsionType_congr e 2]; exact hN
  have : Finite {y : (Fin r → Q2Z2) × F // (2 : ℕ) • y = 0} :=
    Nat.finite_of_card_ne_zero (by rw [hN']; norm_num)
  have hle := two_pow_le_card_torsion r F
  rw [hN'] at hle
  have hr : r ≤ 1 := by
    by_contra hr
    have : 2 ^ 2 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hpar := hP E hE r 3 2 ⟨F, hF1, hF2, ⟨e⟩⟩ (by rw [h8]; norm_num) (by rw [h4']; norm_num)
  have hr1 : r = 1 := by
    interval_cases r
    · exact absurd hpar (by decide)
    · rfl
  subst hr1
  exact ⟨F, hF1, hF2, ⟨e⟩⟩

end ZInQ.Manuscript.SelmerTwoPower
