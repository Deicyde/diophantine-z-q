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

theorem natMod8_eq_iff_cast (n k : ℕ) (hk : k < 8) : n % 8 = k ↔ (n : ZMod 8) = (k : ZMod 8) := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hk]

theorem dProd_class_iff (hd : Odd d) (B : Finset d.primeFactors) :
    (dProd B % 8 = 7 ↔ ∑ q ∈ B, yBit d q = 1 ∧ ∑ q ∈ B, zBit d q = 0) ∧
    (dProd B % 8 = 3 ↔ ∑ q ∈ B, yBit d q = 1 ∧ ∑ q ∈ B, zBit d q = 1) ∧
    (dProd B % 8 = 7 ∨ dProd B % 8 = 3 ∨ dProd B % 8 = 1 ↔
      ¬(∑ q ∈ B, yBit d q = 0 ∧ ∑ q ∈ B, zBit d q = 1)) := by
  rw [sum_yBit_eq hd, sum_zBit_eq hd, natMod8_eq_iff_cast _ 7 (by norm_num), natMod8_eq_iff_cast _ 3 (by norm_num),
    natMod8_eq_iff_cast _ 1 (by norm_num)]
  have hc := dProd_mem_oddClasses hd B
  generalize ((dProd B : ℕ) : ZMod 8) = c at hc ⊢
  revert c; decide

theorem admissible5bNat_iff (hd : Odd d) (P : Finpartition (univ : Finset d.primeFactors)) :
    Admissible5bNat d P ↔ Admissible5b (yBit d) (zBit d) P := by
  unfold Admissible5bNat Admissible5b
  rw [Finset.filter_congr fun B _ => (dProd_class_iff hd B).1,
    Finset.filter_congr fun B _ => (dProd_class_iff hd B).2.1]
  exact and_congr Iff.rfl (and_congr Iff.rfl (forall₂_congr fun B _ => (dProd_class_iff hd B).2.2))

/-- The genus sum `T5b d`, defined with residues mod 8, is `genusSum5b` of the bits. -/
theorem T5b_eq_genusSum5b (hd : Odd d) : T5b d = genusSum5b (aBit d) (yBit d) (zBit d) := by
  unfold T5b genusSum5b gBit
  exact Finset.sum_congr rfl fun P _ => if_congr (admissible5bNat_iff hd P) rfl rfl

/-- For squarefree `d ≡ 1 (mod 4)`, `y(V) = Σ_{p ∣ d} y_p = 0`. -/
theorem sum_yBit_univ (hd5 : d % 8 = 5) (hsq : Squarefree d) : ∑ q, yBit d q = 0 := by
  have hd : Odd d := Nat.odd_iff.2 (by omega)
  have h1 : ∏ q ∈ (d.primeFactors).attach, ((q : ℕ)) = d := by
    rw [Finset.prod_attach d.primeFactors (fun q => q)]
    exact Nat.prod_primeFactors_of_squarefree hsq
  rw [sum_yBit_eq hd, dProd, Finset.prod_coe_sort_eq_attach, h1]
  rw [show (d : ZMod 8) = ((5 : ℕ) : ZMod 8) from (natMod8_eq_iff_cast d 5 (by norm_num)).1 hd5]
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

*Trust statement.* This is not proved in Lean. It follows from the following published results,
together with Theorem 3.6 (`det_M5b_eq_T5b`, proved); of them, only Rédei's formula is proved in
Lean:

* **Tian–Yuan–Zhang** (Y. Tian, X. Yuan, S.-W. Zhang, *Genus periods, genus points and congruent
  number problem*, Asian J. Math. 21 (2017), no. 4, 721–774; read in arXiv:1411.4728v1, the journal
  text was not available): Theorem 3.5 (first assertion) and the argument of the proof of
  Theorem 3.5(2) in §3.3, for `n ≡ 5 (mod 8)`, as completed in `docs/research/nt-tyz.md` §4
  (Proposition N; reviewed in `docs/research/rv-nt-tyz.md` and `docs/research/rv-prop-n.md`).
  For squarefree `n ≡ 5 (mod 8)`: if
  the `(7, 3)` genus sum `Σ_{d₀ ≡ 7, d₁ ≡ 3 (8)} g(d₀) g(d₁) 𝓛₁(n/d₀d₁)` is odd, where `𝓛₁(m)` is
  the sum of `Π g(B)` over the set partitions of the primes of `m` into blocks `≡ 1 (mod 8)`, then
  TYZ's invariant `𝓛(n)` is nonzero, so `ord_{s=1} L(C_n, s) ≤ 1`, and since the root number is `−1`
  (Birch–Stephens), `ord_{s=1} L(C_n, s) = 1`. TYZ's Theorem 1.2 must not be cited literally (with
  "all `d_i > 1`" it is false; nt-tyz §1.4). TYZ's own definition of `𝓛(n)` uses Coates–Wiles,
  Rubin, Gross–Zagier and Kolyvagin (TYZ §1).
* **Rédei's formula** (genus theory; L. Rédei, J. Reine Angew. Math. 171 (1934), 55–60; the `κ`
  forms are derived in `docs/research/tyz-5b.md` Proposition 2.3): for every nonempty set `B` of
  primes of `d`, `gBit d B = #2Cl(ℚ(√−d_B)) mod 2`. So `T5b d` is the `(7, 3)` genus
  sum above for `n = d`. This step is proved in Lean (`RouteK.Redei.redeiFormula`).
* **Gross–Zagier** (Invent. Math. 84 (1986), 225–320), over an imaginary quadratic field `K` that
  satisfies the Heegner hypothesis and has `L(C_d^K, 1) ≠ 0` (Bump–Friedberg–Hoffstein);
  `C_d` is modular because it has CM by `ℤ[i]` (Deuring, Shimura). This gives
  `ord_{s=1} L(C_d, s) = 1 ⟹ rank C_d(ℚ) ≥ 1` (`docs/research/pc-audit.md` RK7). Neither
  Kolyvagin nor BCDT is needed for this step.

Then (elementary, `docs/research/pc-audit.md` RK9): `C_d(ℚ)[2]` has order 4, so
`dim C_d(ℚ)/2C_d(ℚ) = 2 + rank ≥ 3 = dim Sel₂(C_d)`. The Kummer map is injective on
`C_d(ℚ)/2C_d(ℚ)` (Silverman X.1.4), hence onto `Sel₂(C_d)`, and every Selmer class has
`D_{a,b}(ℚ) ≠ ∅` (`Selmer.loc_iff_kummer`). Neither finiteness of `Ш` nor the Cassels–Tate
pairing is used.

Under `d % 8 = 5` and `Squarefree d`, `CertifiedRankTYZ` is equivalent to `CertifiedRank5b` by
Theorem 3.6 (review: `docs/research/rv-cr5b-sec3.md`). Lean derives it from
`Rank.CertifiedRankTYZClRk` (`Redei.certifiedRankTYZRk_of_certifiedRankTYZClRk`,
`Rank.certifiedRankTYZ_of_certifiedRankTYZRk'`); see `docs/research/cr3-trust.md`. -/
def CertifiedRankTYZ : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → (Sel2 d).ncard = 8 → T5b d = 1 →
    ∀ ab ∈ Sel2 d, Loc ℚ d ab.1 ab.2

/-- **CR₃^5b from CR₃^TYZ**, by Theorem 3.6 (`det_M5b_eq_T5b`). -/
theorem certifiedRank5b_of_certifiedRankTYZ (h : CertifiedRankTYZ) : CertifiedRank5b :=
  fun d hd5 hsq h8 hdet => h d hd5 hsq h8 (by rw [← det_M5b_eq_T5b hd5 hsq]; exact hdet)

end ZInQ.RouteK.Rank5b
