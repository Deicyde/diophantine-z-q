import ZInQKernel.RouteK.Rank5b.Sec3.Thm36

/-!
# Theorem 3.6 for `n ≡ 5 (mod 8)`, and the hypothesis `CertifiedRankTYZ`

* `T5b_eq_genusSum5b`: for odd `d`, the genus sum `T5b d` defined with residues mod 8 equals
  `genusSum5b` of the bits (the class of `d_B` mod 8 is read off `(y(B), z(B))`);
* `det_M5b_eq_T5b` (**Theorem 3.6**, tyz-5b §3.3): for squarefree `d ≡ 5 (mod 8)`, `det M_5b = T_5b(d)`;
* `CertifiedRankTYZ`: the hypothesis CR₃ in the terms of Tian–Yuan–Zhang, and
  `certifiedRank5b_of_certifiedRankTYZ : CertifiedRankTYZ → CertifiedRank5b`.
-/

namespace ZInQ.RouteK.Rank5b

open Finset Sec3 Selmer

variable {d : ℕ}

theorem recip_bits (hd : Odd d) : Recip (aBit d) (yBit d) := fun _ _ hij => aBit_add_aBit hd hij

theorem yBit_eq_lam8 (hd : Odd d) (q : d.primeFactors) : yBit d q = lam8 ((q : ℕ) : ZMod 8) :=
  (natConfig_lam_eq_yBit hd q).symm.trans (Selmer.natConfig_lam_eq_lam8 hd q)

theorem zBit_eq_mu8 (hd : Odd d) (q : d.primeFactors) : zBit d q = mu8 ((q : ℕ) : ZMod 8) :=
  (natConfig_mu_eq_zBit hd q).symm.trans (Selmer.natConfig_mu_eq_mu8 hd q)

theorem dProd_mem_oddClasses (hd : Odd d) (B : Finset d.primeFactors) :
    ((dProd B : ℕ) : ZMod 8) ∈ oddClasses := by
  rw [dProd, Nat.cast_prod]
  exact prod_mem_oddClasses _ _ fun q _ =>
    natCast_mem_oddClasses (Selmer.odd_prime_of_mem_primeFactors hd q)

theorem sum_yBit_eq (hd : Odd d) (B : Finset d.primeFactors) :
    ∑ q ∈ B, yBit d q = lam8 ((dProd B : ℕ) : ZMod 8) := by
  rw [dProd, Nat.cast_prod, lam8_prod _ _ fun q _ =>
    natCast_mem_oddClasses (Selmer.odd_prime_of_mem_primeFactors hd q)]
  exact Finset.sum_congr rfl fun q _ => yBit_eq_lam8 hd q

theorem sum_zBit_eq (hd : Odd d) (B : Finset d.primeFactors) :
    ∑ q ∈ B, zBit d q = mu8 ((dProd B : ℕ) : ZMod 8) := by
  rw [dProd, Nat.cast_prod, mu8_prod _ _ fun q _ =>
    natCast_mem_oddClasses (Selmer.odd_prime_of_mem_primeFactors hd q)]
  exact Finset.sum_congr rfl fun q _ => zBit_eq_mu8 hd q

theorem mod8_iff (n k : ℕ) (hk : k < 8) : n % 8 = k ↔ (n : ZMod 8) = (k : ZMod 8) := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hk]

theorem class_iff (hd : Odd d) (B : Finset d.primeFactors) :
    (dProd B % 8 = 7 ↔ ∑ q ∈ B, yBit d q = 1 ∧ ∑ q ∈ B, zBit d q = 0) ∧
    (dProd B % 8 = 3 ↔ ∑ q ∈ B, yBit d q = 1 ∧ ∑ q ∈ B, zBit d q = 1) ∧
    (dProd B % 8 = 7 ∨ dProd B % 8 = 3 ∨ dProd B % 8 = 1 ↔
      ¬(∑ q ∈ B, yBit d q = 0 ∧ ∑ q ∈ B, zBit d q = 1)) := by
  rw [sum_yBit_eq hd, sum_zBit_eq hd, mod8_iff _ 7 (by norm_num), mod8_iff _ 3 (by norm_num),
    mod8_iff _ 1 (by norm_num)]
  have hc := dProd_mem_oddClasses hd B
  generalize ((dProd B : ℕ) : ZMod 8) = c at hc ⊢
  revert c; decide

theorem admissible_iff (hd : Odd d) (P : Finpartition (univ : Finset d.primeFactors)) :
    Admissible5bNat d P ↔ Admissible5b (yBit d) (zBit d) P := by
  unfold Admissible5bNat Admissible5b
  rw [Finset.filter_congr fun B _ => (class_iff hd B).1,
    Finset.filter_congr fun B _ => (class_iff hd B).2.1]
  exact and_congr Iff.rfl (and_congr Iff.rfl (forall₂_congr fun B _ => (class_iff hd B).2.2))

/-- The genus sum `T5b d`, defined with residues mod 8, is `genusSum5b` of the bits. -/
theorem T5b_eq_genusSum5b (hd : Odd d) : T5b d = genusSum5b (aBit d) (yBit d) (zBit d) := by
  unfold T5b genusSum5b gBit
  exact Finset.sum_congr rfl fun P _ => if_congr (admissible_iff hd P) rfl rfl

/-- For squarefree `d ≡ 1 (mod 4)`, `y(V) = Σ_{p ∣ d} y_p = 0`. -/
theorem sum_yBit_univ (hd5 : d % 8 = 5) (hsq : Squarefree d) : ∑ q, yBit d q = 0 := by
  have hd : Odd d := Nat.odd_iff.2 (by omega)
  have h1 : ∏ q ∈ (d.primeFactors).attach, ((q : ℕ)) = d := by
    rw [Finset.prod_attach d.primeFactors (fun q => q)]
    exact Nat.prod_primeFactors_of_squarefree hsq
  rw [sum_yBit_eq hd, dProd, Finset.prod_coe_sort_eq_attach, h1]
  rw [show (d : ZMod 8) = ((5 : ℕ) : ZMod 8) from (mod8_iff d 5 (by norm_num)).1 hd5]
  decide

/-- **Theorem 3.6** (Smith's Theorem 2.2, row 5b; tyz-5b §3.3): for squarefree `d ≡ 5 (mod 8)`,
`det M_5b = T_5b(d)`. -/
theorem det_M5b_eq_T5b (hd5 : d % 8 = 5) (hsq : Squarefree d) : (M5b d).det = T5b d := by
  have hd : Odd d := Nat.odd_iff.2 (by omega)
  rw [M5b_eq_M5bG, T5b_eq_genusSum5b hd]
  exact det_M5bG_eq_genusSum5b (recip_bits hd) (sum_yBit_univ hd5 hsq) _

/-- **CR₃ in the terms of Tian–Yuan–Zhang.** For every squarefree `d ≡ 5 (mod 8)` with
`#Sel₂(C_d) = 8` (`dim Sel₂ = 3`) and odd genus sum `T_5b(d) = 1`, every 2-Selmer class of
`C_d : y² = x³ − d²x` comes from a rational point: `D_{a,b}(ℚ) ≠ ∅` for every `(a, b) ∈ Sel₂(C_d)`.

*Trust statement.* This is a consequence of the following published theorems, none of which is
formalized here:

* **Tian–Yuan–Zhang** (Y. Tian, X. Yuan, S.-W. Zhang, *Genus periods, genus points and congruent
  number problem*, Asian J. Math. 21 (2017), no. 4, 721–774; arXiv:1411.4728), in the form proved in
  the proof of their Theorem 3.5(2) (§3.3, "Proof of Theorem 3.5: part (2)"): for squarefree
  `n ≡ 5 (mod 8)`, if the `(7, 3)` genus sum `Σ_{d₀ ≡ 7, d₁ ≡ 3 (8)} g(d₀) g(d₁) 𝓛(n/d₀d₁)` is odd,
  then `2^{−ρ(n)}𝓛(n)` is odd, so `𝓛(n) ≠ 0` and `ord_{s=1} L(C_n, s) = 1` (the root number is `−1`).
  See `docs/research/tyz-5b.md` §1 (Proposition 1.1; the citation caveat on the reading of the
  statement of Theorems 1.2 and 3.5(2)) and `docs/research/nt-tyz.md`.
* **Rédei's formula** (genus theory: Gauss, Rédei 1934; tyz-5b Proposition 2.3): `g(d) =
  #2Cl(ℚ(√−d)) mod 2` equals the determinant forms used in the definition of `gBit`
  (`Sec3.redeiG`), so that `T5b d` is the genus sum of TYZ. The identity `T5b d = det M_5b`
  (`det_M5b_eq_T5b`, Theorem 3.6) is proved in Lean; Proposition 2.3 is not.
* **Gross–Zagier and Kolyvagin** (manuscript Lemma 5.5, `lem:forward-rank`): analytic rank one
  gives `rank C_d(ℚ) = 1`; then `dim C_d(ℚ)/2C_d(ℚ) = 2 + 1 = 3 = dim Sel₂(C_d)`, so the Kummer map
  is onto `Sel₂(C_d)`, i.e. every Selmer class has `D_{a,b}(ℚ) ≠ ∅` (`Selmer.loc_iff_kummer`). -/
def CertifiedRankTYZ : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → (Sel2 d).ncard = 8 → T5b d = 1 →
    ∀ ab ∈ Sel2 d, Loc ℚ d ab.1 ab.2

/-- **CR₃^5b from CR₃^TYZ**, by Theorem 3.6 (`det_M5b_eq_T5b`). -/
theorem certifiedRank5b_of_certifiedRankTYZ (h : CertifiedRankTYZ) : CertifiedRank5b :=
  fun d hd5 hsq h8 hdet => h d hd5 hsq h8 (by rw [← det_M5b_eq_T5b hd5 hsq]; exact hdet)

end ZInQ.RouteK.Rank5b
