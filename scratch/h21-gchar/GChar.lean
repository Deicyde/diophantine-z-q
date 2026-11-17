import ZInQKernel.OneProof.TYZSplit
import ZInQKernel.Contrib.OneProof.TYZThm21Span
import ZInQKernel.Contrib.OneProof.TYZGenusFold.Jacobi

/-!
# h21-gchar: TYZ's genus character `χ_{d₁,d₂}` is the Legendre-symbol character of the Lean statement

Task h21-gchar, step (b) of the queue10 verdict on `h21C` (`TYZGenusFold.TYZThm21PairsC`). Report
`docs/research/h21-gchar.md`.

TYZ = Tian–Yuan–Zhang, arXiv:1411.4728v1. The source is not on this host; line numbers come from the project notes
and are UNVERIFIED here: `χ_{n,1} = 1` (L510, per h29-proof), the quadratic periods (L551–552), Theorem 2.1
(L554–559), the §3 wording "the unique Hecke character over `K_n` associated to the extension `K_n(√d₁*)`"
(L1304–1305, read by h33-sign).

* §1 `dstar d = d* = (−1)^{(d−1)/2} d`.
* §2 **TYZ's `χ_{d₁,d₂}`, class-field-theoretic form**: the character of `Cl_n = Gal(H_n/K_n)` attached to the
  quadratic extension `K_n(√d₂*)` (`IsTYZChi`, over the tree's `IsExtChar`, Tau Ceti's Artin map), pulled back to
  ideal classes by the Artin isomorphism (`tyzChiCl`). Proved: it exists, is unique, and equals the Lean statement's
  `gchar n (divSet n d₂)` (`tyzChiCl_eq_gchar`).
* §3 **norm form** (the standard formula on ideals): `χ([𝔞]) = (d₂*/N𝔞)` (Jacobi symbol) for `N𝔞` prime to `2d₂`
  (`gchar_mk0_eq_jacobiSym`), and, on ideals with `N𝔞` prime to `2n`, also the `d₁`-side formula
  `(D₁/N𝔞)`, `D₁ = d₁*` for `n ≡ 3 (mod 4)` and `−4d₁*` for `n ≡ 1 (mod 4)` (`jacobiSym_d₁_side`); a character of
  `Cl(K_n)` is determined by these values (`isTYZChiNorm_unique`).
* §4 `h21C` and `h21S` restated with TYZ's character (`TYZThm21PairsG`, `TYZThm21SpanG`), each proved equivalent to
  the old statement; and the restated statements do not depend on which factor carries the character
  (`K_n(√d₂*)` or `K_n(√d₁*)`, `tyzThm21SpanG_iff_swap`).

No `sorry`, no `axiom`.
-/

set_option linter.style.longLine false

noncomputable section

open NumberField
open scoped nonZeroDivisors Quaternion

namespace ZInQ.Contrib.H21GChar

open ZInQ.Literature ZInQ.PropN ZInQ.RouteK.Rank5b ZInQ.RouteK.Redei ZInQ.Contrib.TYZDecomp
open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.Contrib.TYZDecomp.H29Genus
open ZInQ.Contrib.TYZGenus.TYZ35 (gchar divSet sgn2)
open ZInQ.Contrib.TYZGenus.TYZSplit (ClG art IsExtChar chiT coe_chiT isExtChar_chiT isExtChar_unique
  prod_pstar_divSet map_divSet)
open ZInQ.Contrib.H21CSteps ZInQ.Contrib.TYZGenusFold

/-! ## §1. `d*` -/

/-- **`d* = (−1)^{(d−1)/2} d`** for odd `d` (TYZ's notation, L1304–1305 UNVERIFIED): `d` if `d ≡ 1 (mod 4)`, `−d`
otherwise. -/
def dstar (d : ℕ) : ℤ := if d % 4 = 1 then (d : ℤ) else -(d : ℤ)

theorem dstar_eq_neg_one_pow {d : ℕ} (hd : Odd d) : dstar d = (-1) ^ ((d - 1) / 2) * (d : ℤ) := by
  obtain ⟨k, rfl⟩ := hd
  have : (2 * k + 1 - 1) / 2 = k := by omega
  rw [this, dstar]
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [if_pos (by omega), Even.neg_one_pow ⟨j, rfl⟩, one_mul]
  · rw [if_neg (by omega), Odd.neg_one_pow ⟨j, rfl⟩, neg_one_mul]

theorem dstar_ne_zero {d : ℕ} (hd : d ≠ 0) : dstar d ≠ 0 := by
  unfold dstar; split_ifs <;> omega

theorem dstar_mod_four {d : ℕ} (hd : d % 2 = 1) : dstar d % 4 = 1 := by
  unfold dstar; split_ifs <;> omega

/-- `d₁* d₂* = n*` for odd `d₁`, `d₂`. -/
theorem dstar_mul {d₁ d₂ : ℕ} (h1 : d₁ % 2 = 1) (h2 : d₂ % 2 = 1) : dstar d₁ * dstar d₂ = dstar (d₁ * d₂) := by
  have hm : (d₁ * d₂) % 4 = (d₁ % 4) * (d₂ % 4) % 4 := Nat.mul_mod _ _ _
  unfold dstar
  have h1' : d₁ % 4 = 1 ∨ d₁ % 4 = 3 := by omega
  have h2' : d₂ % 4 = 1 ∨ d₂ % 4 = 3 := by omega
  rcases h1' with h1' | h1' <;> rcases h2' with h2' | h2' <;> rw [h1', h2'] at hm <;> norm_num at hm <;>
    simp only [h1', h2', hm, if_true, Nat.cast_mul] <;> norm_num <;> ring

/-- **Jacobi reciprocity with `d*`**: `(d*/m) = (m/d)` for odd `d`, `m`. -/
theorem jacobiSym_dstar {d m : ℕ} (hd : Odd d) (hm : Odd m) : jacobiSym (dstar d) m = jacobiSym m d := by
  have hd4 : d % 4 = 1 ∨ d % 4 = 3 := by have := Nat.odd_iff.1 hd; omega
  rcases hd4 with h | h
  · rw [dstar, if_pos h]; exact jacobiSym.quadratic_reciprocity_one_mod_four h hm
  · rw [dstar, if_neg (by omega), jacobiSym.neg _ hm]
    have hm4 : m % 4 = 1 ∨ m % 4 = 3 := by have := Nat.odd_iff.1 hm; omega
    rcases hm4 with h' | h'
    · rw [ZMod.χ₄_nat_one_mod_four h', one_mul]
      exact jacobiSym.quadratic_reciprocity_one_mod_four' hd h'
    · rw [ZMod.χ₄_nat_three_mod_four h', jacobiSym.quadratic_reciprocity_three_mod_four h h']
      ring

/-! ## §2. TYZ's `χ_{d₁,d₂}`: the character of `K_n(√d₂*)` (class field theory) -/

variable {n : ℕ} [NeZero n]

variable (n) in
/-- **TYZ's genus character `χ_{d₁,d₂}`** (TYZ §2, the quadratic periods L551–552, UNVERIFIED; same wording as §3,
L1304–1305: "the unique Hecke character over `K_n` associated to the extension"), for `n = d₁d₂` odd: the character
`χ` of `Cl_n = Gal(H_n/K_n)` (`H_n` the Hilbert class field, Tau Ceti's ring class field) attached to the quadratic
extension `K_n(√d₂*)`, i.e. every lift `ρ ∈ Gal(ℚ̄/ℚ)` of `t ∈ Cl_n` multiplies `√d₂*` by `χ(t)` (`IsExtChar`). The
choice of the factor `d₂` is the one compatible with `χ_{n,1} = 1` (L510, UNVERIFIED) and with "`χ_{d₁,d₂}` is trivial
on `K_{n,2}^×` iff `d₂* ≡ 1 (mod 8)`" in the proof of Theorem 2.1 (rv-tyz-inputs §1.2 item 4); §4 shows that the
restated hypothesis is the same with the other factor. -/
def IsTYZChi (d₂ : ℕ) (χ : ClG n →* ℤˣ) : Prop := IsExtChar n (dstar d₂) χ

variable (n) in
/-- TYZ's `χ_{d₁,d₂}` on `Cl_n = Gal(H_n/K_n)`: the character of `K_n(√d₂*)` when it exists (it exists and is unique
for `d₂ ∣ n`, `tyzChi_eq_chiT`); `1` otherwise. -/
def tyzChi (d₂ : ℕ) : ClG n →* ℤˣ :=
  haveI := Classical.propDecidable
  if h : ∃ χ, IsTYZChi n d₂ χ then h.choose else 1

variable (n) in
/-- **TYZ's `χ_{d₁,d₂}` on ideal classes**: `t ∈ Cl(K_n)` is sent through the Artin isomorphism
`Cl(K_n) ≃ Gal(H_n/K_n)` (`art n`, Tau Ceti's `ringClassArtinEquiv`) and evaluated by `tyzChi`. This is the function
TYZ sum against in `P(d₁, d₂) = Σ_{t ∈ Cl_n} χ_{d₁,d₂}(t) f_n(t)` (L551–552, UNVERIFIED). -/
def tyzChiCl (d₂ : ℕ) (t : ClassGroup (𝓞 (QNeg n))) : ℤ := ((tyzChi n d₂ (art n t) : ℤˣ) : ℤ)

theorem odd_of_dvd_odd {d : ℕ} (hn : Odd n) (hd : d ∣ n) : d % 2 = 1 :=
  Nat.odd_iff.1 (Odd.of_dvd_nat hn hd)

/-- The genus character `χ_T`, `T` the primes of `d₂`, is the character of `K_n(√d₂*)`. -/
theorem isTYZChi_chiT (hn : Odd n) (hsq : Squarefree n) {d₂ : ℕ} (hd : d₂ ∣ n) :
    IsTYZChi n d₂ (chiT n (divSet n d₂)) :=
  isExtChar_chiT hn hsq _ _ (Or.inl (by rw [prod_pstar_divSet hsq hd (odd_of_dvd_odd hn hd)]; rfl))

/-- **Uniqueness**: TYZ's `χ_{d₁,d₂}` is determined by the extension `K_n(√d₂*)`. -/
theorem isTYZChi_unique {d₂ : ℕ} (hd : d₂ ≠ 0) {χ χ' : ClG n →* ℤˣ} (h : IsTYZChi n d₂ χ)
    (h' : IsTYZChi n d₂ χ') : χ = χ' :=
  isExtChar_unique (dstar_ne_zero hd) h h'

theorem dvd_ne_zero {d : ℕ} (hd : d ∣ n) : d ≠ 0 := by
  rintro rfl; exact NeZero.ne n (Nat.eq_zero_of_zero_dvd hd)

/-- `tyzChi` is the genus character `χ_{T(d₂)}`. -/
theorem tyzChi_eq_chiT (hn : Odd n) (hsq : Squarefree n) {d₂ : ℕ} (hd : d₂ ∣ n) :
    tyzChi n d₂ = chiT n (divSet n d₂) := by
  have h : ∃ χ, IsTYZChi n d₂ χ := ⟨_, isTYZChi_chiT hn hsq hd⟩
  rw [tyzChi, dite_eq_left h]
  exact isTYZChi_unique (dvd_ne_zero hd) h.choose_spec (isTYZChi_chiT hn hsq hd)

theorem isTYZChi_tyzChi (hn : Odd n) (hsq : Squarefree n) {d₂ : ℕ} (hd : d₂ ∣ n) :
    IsTYZChi n d₂ (tyzChi n d₂) := by
  rw [tyzChi_eq_chiT hn hsq hd]; exact isTYZChi_chiT hn hsq hd

/-- **Step (b): TYZ's `χ_{d₁,d₂}` is the Lean statement's character.** For odd squarefree `n` and `d₂ ∣ n`, the
character of `K_n(√d₂*)` read on ideal classes through the Artin map is `gchar n (divSet n d₂)`
`= Π_{q ∣ d₂} (N𝔞/q)`, the character in `quadPeriod`. -/
theorem tyzChiCl_eq_gchar (hn : Odd n) (hsq : Squarefree n) {d₂ : ℕ} (hd : d₂ ∣ n)
    (t : ClassGroup (𝓞 (QNeg n))) : tyzChiCl n d₂ t = gchar n (divSet n d₂) t := by
  rw [tyzChiCl, tyzChi_eq_chiT hn hsq hd, coe_chiT]
  exact congrArg (gchar n (divSet n d₂)) ((art n).symm_apply_apply t)

/-! ## §3. The norm form: `χ_{d₁,d₂}([𝔞]) = (d₂*/N𝔞)` -/

/-- If `I + (M) = O`, then `N I` is prime to `M`. -/
theorem coprime_absNorm_of_sup_span_eq_top {M : ℕ} {I : Ideal (𝓞 (QNeg n))}
    (h : I ⊔ Ideal.span {(M : 𝓞 (QNeg n))} = ⊤) : Nat.Coprime (Ideal.absNorm I) M := by
  refine Nat.coprime_of_dvd fun p hp hpI hpM => ?_
  have hle : Ideal.span {(M : 𝓞 (QNeg n))} ≤ Ideal.span {(p : 𝓞 (QNeg n))} := by
    rw [Ideal.span_singleton_le_span_singleton]; exact Nat.cast_dvd_cast hpM
  have h' : I ⊔ Ideal.span {(p : 𝓞 (QNeg n))} = ⊤ := top_le_iff.1 (h ▸ sup_le_sup_left hle I)
  exact not_dvd_absNorm_of_sup_span_eq_top hp h' hpI

variable (n) in
/-- **Every ideal class contains an integral ideal of norm prime to `M`** (`M > 1`); the proof of the tree's
`exists_mk0_coprime` with `q` replaced by `M`. -/
theorem exists_mk0_coprime' (M : ℕ) (hM : 1 < M) (c : ClassGroup (𝓞 (QNeg n))) :
    ∃ I : (Ideal (𝓞 (QNeg n)))⁰, ClassGroup.mk0 I = c ∧ Nat.Coprime (Ideal.absNorm (I : Ideal (𝓞 (QNeg n)))) M := by
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective c⁻¹
  have hJ0 : (J : Ideal (𝓞 (QNeg n))) ≠ 0 := nonZeroDivisors.coe_ne_zero J
  have hq0 : Ideal.span {(M : 𝓞 (QNeg n))} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact natCast_ne_zero_O (by omega)
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq
    (I := (J : Ideal (𝓞 (QNeg n))) * Ideal.span {(M : 𝓞 (QNeg n))}) (J := J)
    (Ideal.mul_le_inf.trans inf_le_left) (mul_ne_zero hJ0 hq0)
  have haJ : a ∈ (J : Ideal (𝓞 (QNeg n))) := ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  obtain ⟨Mi, hMi⟩ := Ideal.dvd_span_singleton.2 haJ
  have hcop : Mi ⊔ Ideal.span {(M : 𝓞 (QNeg n))} = ⊤ := by
    have h1 : (J : Ideal (𝓞 (QNeg n))) * (Ideal.span {(M : 𝓞 (QNeg n))} ⊔ Mi) = J * ⊤ := by
      rw [Ideal.mul_sup, ← hMi, ha, Ideal.mul_top]
    rw [sup_comm]; exact mul_left_cancel₀ hJ0 h1
  have hM0 : Mi ≠ 0 := by
    rintro rfl
    rw [Ideal.zero_eq_bot, bot_sup_eq, Ideal.span_singleton_eq_top, isUnit_iff_dvd_one,
      show (1 : 𝓞 (QNeg n)) = ((1 : ℕ) : 𝓞 (QNeg n)) by simp, natCast_dvd_natCast_iff] at hcop
    exact hM.ne' (Nat.dvd_one.1 hcop)
  set M' : (Ideal (𝓞 (QNeg n)))⁰ := ⟨Mi, mem_nonZeroDivisors_of_ne_zero hM0⟩
  refine ⟨M', ?_, coprime_absNorm_of_sup_span_eq_top hcop⟩
  have h1 : ClassGroup.mk0 J * ClassGroup.mk0 M' = 1 := by
    rw [← map_mul, ClassGroup.mk0_eq_one_iff (J * M').2]
    have e : ((J * M' : (Ideal (𝓞 (QNeg n)))⁰) : Ideal (𝓞 (QNeg n))) = Ideal.span {a} := by
      rw [Submonoid.coe_mul]; exact hMi.symm
    rw [e]
    exact ⟨⟨a, rfl⟩⟩
  rw [hJ] at h1
  exact (inv_mul_eq_one.1 h1).symm

/-- `Π_{q ∈ T(d₂)} q = d₂` for squarefree `d₂ ∣ n`. -/
theorem prod_divSet (hsq : Squarefree n) {d₂ : ℕ} (hd : d₂ ∣ n) :
    ∏ q ∈ divSet n d₂, (q : ℕ) = d₂ := by
  have h := congrArg (fun s => ∏ p ∈ s, p) (map_divSet (n := n) hd)
  simp only [Finset.prod_map, Function.Embedding.coe_subtype] at h
  rw [h, Nat.prod_primeFactors_of_squarefree (hsq.squarefree_of_dvd hd)]

/-- **The norm formula**: for odd squarefree `n`, `d₂ ∣ n` and an integral ideal `𝔞` with `N𝔞` prime to `2d₂`,
`χ_{T(d₂)}([𝔞]) = Π_{q ∣ d₂} (N𝔞/q) = (N𝔞/d₂) = (d₂*/N𝔞)` (Jacobi reciprocity). -/
theorem gchar_mk0_eq_jacobiSym (hn : Odd n) (hsq : Squarefree n) {d₂ : ℕ} (hd : d₂ ∣ n)
    (I : (Ideal (𝓞 (QNeg n)))⁰) (hcop : Nat.Coprime (Ideal.absNorm (I : Ideal (𝓞 (QNeg n)))) (2 * d₂))
    (c : ClassGroup (𝓞 (QNeg n))) (hc : ClassGroup.mk0 I = c) :
    gchar n (divSet n d₂) c = jacobiSym (dstar d₂) (Ideal.absNorm (I : Ideal (𝓞 (QNeg n)))) := by
  classical
  set m := Ideal.absNorm (I : Ideal (𝓞 (QNeg n))) with hmdef
  have hm : Odd m := by
    have h2 : Nat.Coprime m 2 := Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 d₂) hcop
    exact Nat.odd_iff.2 (by
      rcases Nat.mod_two_eq_zero_or_one m with h | h
      · exact absurd (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm h2) (Nat.dvd_of_mod_eq_zero h)) (by norm_num)
      · exact h)
  have hqm : ∀ q ∈ divSet n d₂, ¬ (q : ℕ) ∣ m := by
    intro q hq h
    have hqd : (q : ℕ) ∣ d₂ := by
      simpa [divSet] using hq
    exact (Nat.prime_of_mem_primeFactors q.2).one_lt.ne'
      ((Nat.Coprime.coprime_dvd_right (dvd_mul_of_dvd_right hqd 2) hcop).symm.eq_one_of_dvd h)
  have hterm : ∀ q ∈ divSet n d₂, sgn2 (chi n q c) = jacobiSym m q := by
    intro q hq
    rw [← hc]
    have hqp := Nat.prime_of_mem_primeFactors q.2
    have := Fact.mk hqp
    rw [chi_mk0 n hn hsq q I (hqm q hq), sgn2_ofAdd, ← jacobiSym.legendreSym.to_jacobiSym]
    exact ((ZInQ.RouteK.legBit_eq_iff_legendreSym (intCast_natCast_zmod_ne_zero (hqm q hq)) _).mp rfl).symm
  have hJm : gchar n (divSet n d₂) c = jacobiSym m d₂ := by
    unfold gchar
    rw [Finset.prod_congr rfl hterm,
      show jacobiSym m d₂ = jacobiSym m (∏ q ∈ divSet n d₂, (q : ℕ)) by rw [prod_divSet hsq hd],
      jacobiSym_finsetProd_right (ι := n.primeFactors) _ _ (fun q => (q : ℕ))
        fun q _ => (Nat.prime_of_mem_primeFactors q.2).ne_zero]
  rw [hJm, jacobiSym_dstar (Nat.odd_iff.2 (odd_of_dvd_odd hn hd)) hm]

variable (n) in
/-- **TYZ's `χ_{d₁,d₂}`, norm form** (the standard formula for the genus character of the decomposition
`d_K = d₂* · (d_K/d₂*)`): `χ([𝔞]) = (d₂*/N𝔞)` (Jacobi symbol) for every integral ideal `𝔞` with `N𝔞` prime to
`2n`. -/
def IsTYZChiNorm (d₂ : ℕ) (χ : ClassGroup (𝓞 (QNeg n)) → ℤ) : Prop :=
  ∀ I : (Ideal (𝓞 (QNeg n)))⁰, Nat.Coprime (Ideal.absNorm (I : Ideal (𝓞 (QNeg n)))) (2 * n) →
    χ (ClassGroup.mk0 I) = jacobiSym (dstar d₂) (Ideal.absNorm (I : Ideal (𝓞 (QNeg n))))

/-- A function on `Cl(K_n)` is determined by the norm formula. -/
theorem isTYZChiNorm_unique {d₂ : ℕ} {χ χ' : ClassGroup (𝓞 (QNeg n)) → ℤ} (h : IsTYZChiNorm n d₂ χ)
    (h' : IsTYZChiNorm n d₂ χ') : χ = χ' := by
  funext c
  obtain ⟨I, rfl, hI⟩ := exists_mk0_coprime' n (2 * n) (by have := NeZero.ne n; omega) c
  rw [h I hI, h' I hI]

theorem isTYZChiNorm_gchar (hn : Odd n) (hsq : Squarefree n) {d₂ : ℕ} (hd : d₂ ∣ n) :
    IsTYZChiNorm n d₂ (gchar n (divSet n d₂)) := fun I hI =>
  gchar_mk0_eq_jacobiSym hn hsq hd I (Nat.Coprime.coprime_dvd_right (Nat.mul_dvd_mul_left 2 hd) hI) _ rfl

/-- **The two forms of TYZ's character agree**: the character of `K_n(√d₂*)` (class field theory) satisfies the
norm formula, so it is the unique function with the norm formula. -/
theorem isTYZChiNorm_tyzChiCl (hn : Odd n) (hsq : Squarefree n) {d₂ : ℕ} (hd : d₂ ∣ n) :
    IsTYZChiNorm n d₂ (tyzChiCl n d₂) := by
  have : tyzChiCl n d₂ = gchar n (divSet n d₂) := funext (tyzChiCl_eq_gchar hn hsq hd)
  rw [this]; exact isTYZChiNorm_gchar hn hsq hd

/-- **The `d₁`-side formula.** For `n = d₁d₂` odd squarefree and `N𝔞` prime to `2n`, `(d₂*/N𝔞) = (D₁/N𝔞)` with
`D₁ = d_K/d₂*` the complementary fundamental discriminant: `D₁ = d₁*` for `n ≡ 3 (mod 4)` (`d_K = −n`) and
`D₁ = −4d₁*` for `n ≡ 1 (mod 4)` (`d_K = −4n`). -/
theorem jacobiSym_d₁_side (hn : Odd n) {d₁ d₂ : ℕ} (hd : d₁ * d₂ = n) (I : Ideal (𝓞 (QNeg n))) (hI : I ≠ ⊥)
    (hcop : Nat.Coprime (Ideal.absNorm I) (2 * n)) :
    jacobiSym (if n % 4 = 3 then dstar d₁ else -4 * dstar d₁) (Ideal.absNorm I) =
      jacobiSym (dstar d₂) (Ideal.absNorm I) := by
  set m := Ideal.absNorm I with hmdef
  have hJ := jacobiSym_neg_absNorm I hI hcop
  have h1 : d₁ % 2 = 1 := odd_of_dvd_odd hn ⟨d₂, hd.symm⟩
  have h2 : d₂ % 2 = 1 := odd_of_dvd_odd hn ⟨d₁, by rw [← hd, mul_comm]⟩
  have hmul := dstar_mul h1 h2
  rw [hd] at hmul
  have hgcd : Int.gcd (dstar d₂) (m : ℤ) = 1 := by
    have hcop2 : Nat.Coprime m d₂ := Nat.Coprime.coprime_dvd_right
      (dvd_mul_of_dvd_right ⟨d₁, by rw [← hd, mul_comm]⟩ 2) hcop
    unfold dstar; split_ifs
    · rw [Int.gcd_natCast_natCast]; exact hcop2.symm
    · rw [Int.neg_gcd, Int.gcd_natCast_natCast]; exact hcop2.symm
  have hsq2 := jacobiSym.sq_one hgcd
  have hm : Odd m := by
    have h2' : Nat.Coprime m 2 := Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 n) hcop
    exact Nat.odd_iff.2 (by
      rcases Nat.mod_two_eq_zero_or_one m with h | h
      · exact absurd (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm h2') (Nat.dvd_of_mod_eq_zero h)) (by norm_num)
      · exact h)
  split_ifs with h4
  · -- `d₁* d₂* = −n`
    have hn' : dstar n = -(n : ℤ) := by rw [dstar, if_neg (by omega)]
    rw [hn'] at hmul
    have : jacobiSym (dstar d₁) m * jacobiSym (dstar d₂) m = 1 := by
      rw [← jacobiSym.mul_left, hmul]; exact hJ
    linear_combination (jacobiSym (dstar d₂) m) * this - (jacobiSym (dstar d₁) m) * hsq2
  · -- `d₁* d₂* = n`
    have h41 : n % 4 = 1 := by have := Nat.odd_iff.1 hn; omega
    have hn' : dstar n = (n : ℤ) := by rw [dstar, if_pos h41]
    rw [hn'] at hmul
    have h4m : jacobiSym 4 m = 1 := jacobiSym.at_four hm
    have : jacobiSym (-4 * dstar d₁) m * jacobiSym (dstar d₂) m = 1 := by
      rw [← jacobiSym.mul_left, show -4 * dstar d₁ * dstar d₂ = 4 * (-(n : ℤ)) by rw [mul_assoc, hmul]; ring,
        jacobiSym.mul_left, h4m, hJ, one_mul]
    linear_combination (jacobiSym (dstar d₂) m) * this - (jacobiSym (-4 * dstar d₁) m) * hsq2

/-! ## §4. `h21C` and `h21S` with TYZ's character -/

variable (n) in
/-- **TYZ's quadratic period with TYZ's character** `P(d₁, d₂) = Σ_{t ∈ Cl_n} χ_{d₁,d₂}(t) f_n(t)` (L551–552,
UNVERIFIED), `χ_{d₁,d₂}` the character of `K_n(√d₂*)` through the Artin map (`tyzChiCl`), indexed by `d₂`. The class
`t` is read in `B̂^×` as in `quadPeriod` (`clLift`, `tauHatU`). -/
def quadPeriodTYZ (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) (f : ℍ[AQ] → ℤ) (d₂ : ℕ) : ℤ :=
  ∑ t : ClassGroup (𝓞 (QNeg n)), tyzChiCl n d₂ t * f ((tauHatU n τ (clLift n t) : ℍ[AQ]ˣ) : ℍ[AQ])

theorem quadPeriodTYZ_eq (hn : Odd n) (hsq : Squarefree n) (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) (f : ℍ[AQ] → ℤ)
    {d₂ : ℕ} (hd : d₂ ∣ n) : quadPeriodTYZ n τ f d₂ = quadPeriod n τ f d₂ := by
  unfold quadPeriodTYZ quadPeriod
  exact Finset.sum_congr rfl fun t _ => by rw [tyzChiCl_eq_gchar hn hsq hd]

/-- **`h21S` with TYZ's character `χ_{d₁,d₂}`**: TYZ Theorem 2.1 (L554–559, UNVERIFIED here) with `π_ℤ^{U_n}` read
through Theorem 2.4(1) (h21c-steps, `IsTestVectorSpan`) and the quadratic period formed with TYZ's genus character
(the character of `K_n(√d₂*)`, class field theory, `quadPeriodTYZ`). Word for word `H21CSteps.TYZThm21Span` with
`quadPeriod` replaced by `quadPeriodTYZ`. -/
def TYZThm21SpanG : Prop :=
  ∀ (n : ℕ) [NeZero n], Squarefree n → 1 < n → (n % 8 = 1 ∨ n % 8 = 3) →
    ∀ τ : QNeg n →ₐ[ℚ] ℍ[ℚ], AdmissibleTau n τ → ∀ f : ℍ[AQ] → ℤ, IsTestVectorSpan n τ f →
      ∀ ℓ : ℕ → ℂ, IsLcalSignC ℓ → ∀ d₁ d₂ : ℕ, d₁ * d₂ = n →
        (d₁ % 8 ≠ 1 → d₂ % 8 ≠ 1 → quadPeriodTYZ n τ f d₂ = 0) ∧
        (d₂ % 8 = 1 → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
          (quadPeriodTYZ n τ f d₂ : ℂ) = ε * 2 ^ (n.primeFactors.card - 1) *
            ((NumberField.Units.torsionOrder (QNeg n) / 2 : ℕ) : ℂ) * (ℓ d₁ * ℓ d₂))

/-- **`h21C` with TYZ's character**: `TYZGenusFold.TYZThm21PairsC` with `quadPeriod` replaced by `quadPeriodTYZ`. -/
def TYZThm21PairsG : Prop :=
  ∀ (n : ℕ) [NeZero n], Squarefree n → 1 < n → (n % 8 = 1 ∨ n % 8 = 3) →
    ∀ τ : QNeg n →ₐ[ℚ] ℍ[ℚ], AdmissibleTau n τ → ∀ f : ℍ[AQ] → ℤ, IsTestVector n τ f →
      ∀ ℓ : ℕ → ℂ, IsLcalSignC ℓ → ∀ d₁ d₂ : ℕ, d₁ * d₂ = n →
        (d₁ % 8 ≠ 1 → d₂ % 8 ≠ 1 → quadPeriodTYZ n τ f d₂ = 0) ∧
        (d₂ % 8 = 1 → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
          (quadPeriodTYZ n τ f d₂ : ℂ) = ε * 2 ^ (n.primeFactors.card - 1) *
            ((NumberField.Units.torsionOrder (QNeg n) / 2 : ℕ) : ℂ) * (ℓ d₁ * ℓ d₂))

theorem odd_of_cl {n : ℕ} (hcl : n % 8 = 1 ∨ n % 8 = 3) : Odd n := Nat.odd_iff.2 (by omega)

/-- `TYZThm21SpanG → TYZThm21Span` (`h21S`). -/
theorem tyzThm21Span_of_G (h : TYZThm21SpanG) : TYZThm21Span := by
  intro n _ hsq h1 hcl τ hτ f hf ℓ hℓ d₁ d₂ hd
  have hdv : d₂ ∣ n := ⟨d₁, by rw [← hd, mul_comm]⟩
  have e := quadPeriodTYZ_eq (odd_of_cl hcl) hsq τ f hdv
  rw [← e]
  exact h n hsq h1 hcl τ hτ f hf ℓ hℓ d₁ d₂ hd

/-- `TYZThm21Span → TYZThm21SpanG`. -/
theorem tyzThm21SpanG_of_span (h : TYZThm21Span) : TYZThm21SpanG := by
  intro n _ hsq h1 hcl τ hτ f hf ℓ hℓ d₁ d₂ hd
  have hdv : d₂ ∣ n := ⟨d₁, by rw [← hd, mul_comm]⟩
  have e := quadPeriodTYZ_eq (odd_of_cl hcl) hsq τ f hdv
  rw [e]
  exact h n hsq h1 hcl τ hτ f hf ℓ hℓ d₁ d₂ hd

/-- `TYZThm21PairsG → TYZThm21PairsC` (`h21C`). -/
theorem tyzThm21PairsC_of_G (h : TYZThm21PairsG) : TYZThm21PairsC := by
  intro n _ hsq h1 hcl τ hτ f hf ℓ hℓ d₁ d₂ hd
  have hdv : d₂ ∣ n := ⟨d₁, by rw [← hd, mul_comm]⟩
  have e := quadPeriodTYZ_eq (odd_of_cl hcl) hsq τ f hdv
  rw [← e]
  exact h n hsq h1 hcl τ hτ f hf ℓ hℓ d₁ d₂ hd

/-- `TYZThm21PairsC → TYZThm21PairsG`. -/
theorem tyzThm21PairsG_of_pairsC (h : TYZThm21PairsC) : TYZThm21PairsG := by
  intro n _ hsq h1 hcl τ hτ f hf ℓ hℓ d₁ d₂ hd
  have hdv : d₂ ∣ n := ⟨d₁, by rw [← hd, mul_comm]⟩
  have e := quadPeriodTYZ_eq (odd_of_cl hcl) hsq τ f hdv
  rw [e]
  exact h n hsq h1 hcl τ hτ f hf ℓ hℓ d₁ d₂ hd

/-- The new `h21S`-form implies the new `h21C`-form (through h21c-steps' dictionary). -/
theorem tyzThm21PairsG_of_spanG (h : TYZThm21SpanG) : TYZThm21PairsG :=
  tyzThm21PairsG_of_pairsC (tyzThm21PairsC_of_span (tyzThm21Span_of_G h))

/-! ### The other factor: `χ` attached to `K_n(√d₁*)` -/

/-- **TYZ Theorem 2.1 with the character of the first factor**, `K_n(√d₁*)` (`quadPeriodTYZ n τ f d₁`): the reading
in which TYZ's `χ_{d₁,d₂}` is attached to `d₁` rather than to `d₂`. -/
def TYZThm21SpanG₁ : Prop :=
  ∀ (n : ℕ) [NeZero n], Squarefree n → 1 < n → (n % 8 = 1 ∨ n % 8 = 3) →
    ∀ τ : QNeg n →ₐ[ℚ] ℍ[ℚ], AdmissibleTau n τ → ∀ f : ℍ[AQ] → ℤ, IsTestVectorSpan n τ f →
      ∀ ℓ : ℕ → ℂ, IsLcalSignC ℓ → ∀ d₁ d₂ : ℕ, d₁ * d₂ = n →
        (d₁ % 8 ≠ 1 → d₂ % 8 ≠ 1 → quadPeriodTYZ n τ f d₁ = 0) ∧
        (d₂ % 8 = 1 → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
          (quadPeriodTYZ n τ f d₁ : ℂ) = ε * 2 ^ (n.primeFactors.card - 1) *
            ((NumberField.Units.torsionOrder (QNeg n) / 2 : ℕ) : ℂ) * (ℓ d₁ * ℓ d₂))

theorem mod8_swap {n d₁ d₂ : ℕ} (hcl : n % 8 = 1 ∨ n % 8 = 3) (hd : d₁ * d₂ = n) :
    (n % 8 = 1 → (d₂ % 8 = 1 ↔ d₁ % 8 = 1)) ∧ (n % 8 = 3 → d₂ % 8 = 1 → d₁ % 8 = 3) := by
  have h := Nat.mul_mod d₁ d₂ 8
  rw [hd] at h
  have h1 : d₁ % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have h2 : d₂ % 8 < 8 := Nat.mod_lt _ (by norm_num)
  interval_cases hx : d₁ % 8 <;> interval_cases hy : d₂ % 8 <;> omega

/-- **The restated hypothesis does not depend on the factor carrying the character.** For `n ≡ 3 (mod 8)` the two
characters agree (`χ_{d₁,d₂} = χ_{d₂,d₁}`, `quadPeriod_div`); for `n ≡ 1 (mod 8)`, both clauses are symmetric under
`d₁ ↔ d₂` (`d₂ ≡ 1 ⇔ d₁ ≡ 1 (mod 8)`). -/
theorem tyzThm21SpanG_iff_swap : TYZThm21SpanG ↔ TYZThm21SpanG₁ := by
  constructor
  · intro h n _ hsq h1 hcl τ hτ f hf ℓ hℓ d₁ d₂ hd
    have hn := odd_of_cl hcl
    have hd' : d₂ * d₁ = n := by rw [mul_comm]; exact hd
    obtain ⟨hs1, hs3⟩ := mod8_swap hcl hd
    rcases hcl with h8 | h8
    · obtain ⟨hA, hB⟩ := h n hsq h1 (Or.inl h8) τ hτ f hf ℓ hℓ d₂ d₁ hd'
      refine ⟨fun a b => hA b a, fun h2 => ?_⟩
      obtain ⟨ε, hε, he⟩ := hB ((hs1 h8).1 h2)
      exact ⟨ε, hε, by rw [he]; ring⟩
    · have hdv1 : d₁ ∣ n := ⟨d₂, hd.symm⟩
      have hdv2 : d₂ ∣ n := ⟨d₁, hd'.symm⟩
      have hq : quadPeriodTYZ n τ f d₁ = quadPeriodTYZ n τ f d₂ := by
        rw [quadPeriodTYZ_eq hn hsq τ f hdv1, quadPeriodTYZ_eq hn hsq τ f hdv2]
        have := quadPeriod_div (by omega) hsq h1 τ f hdv2
        rwa [show n / d₂ = d₁ by rw [← hd, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (dvd_ne_zero hdv2))]] at this
      rw [hq]
      exact h n hsq h1 (Or.inr h8) τ hτ f hf ℓ hℓ d₁ d₂ hd
  · intro h n _ hsq h1 hcl τ hτ f hf ℓ hℓ d₁ d₂ hd
    have hn := odd_of_cl hcl
    have hd' : d₂ * d₁ = n := by rw [mul_comm]; exact hd
    obtain ⟨hs1, hs3⟩ := mod8_swap hcl hd'
    rcases hcl with h8 | h8
    · obtain ⟨hA, hB⟩ := h n hsq h1 (Or.inl h8) τ hτ f hf ℓ hℓ d₂ d₁ hd'
      refine ⟨fun a b => hA b a, fun h2 => ?_⟩
      obtain ⟨ε, hε, he⟩ := hB ((hs1 h8).2 h2)
      exact ⟨ε, hε, by rw [he]; ring⟩
    · have hdv1 : d₁ ∣ n := ⟨d₂, hd.symm⟩
      have hdv2 : d₂ ∣ n := ⟨d₁, hd'.symm⟩
      have hq : quadPeriodTYZ n τ f d₁ = quadPeriodTYZ n τ f d₂ := by
        rw [quadPeriodTYZ_eq hn hsq τ f hdv1, quadPeriodTYZ_eq hn hsq τ f hdv2]
        have := quadPeriod_div (by omega) hsq h1 τ f hdv2
        rwa [show n / d₂ = d₁ by rw [← hd, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (dvd_ne_zero hdv2))]] at this
      rw [← hq]
      exact h n hsq h1 (Or.inr h8) τ hτ f hf ℓ hℓ d₁ d₂ hd

end ZInQ.Contrib.H21GChar

#print axioms ZInQ.Contrib.H21GChar.tyzChiCl_eq_gchar
#print axioms ZInQ.Contrib.H21GChar.isTYZChiNorm_tyzChiCl
#print axioms ZInQ.Contrib.H21GChar.jacobiSym_d₁_side
#print axioms ZInQ.Contrib.H21GChar.tyzThm21Span_of_G
#print axioms ZInQ.Contrib.H21GChar.tyzThm21SpanG_of_span
#print axioms ZInQ.Contrib.H21GChar.tyzThm21PairsC_of_G
#print axioms ZInQ.Contrib.H21GChar.tyzThm21PairsG_of_pairsC
#print axioms ZInQ.Contrib.H21GChar.tyzThm21SpanG_iff_swap
