# rv-redei: adversarial review of the Lean proof of Rédei's formula

Reviewed state: `origin/main` at `8718d41d` (branch `wip/rv-redei`). Scope: `ZInQKernel/RouteK/Redei/`
(Field, Primes, Entry, Ambiguous, Genus, Dirichlet, FourRank, Kernel, Bridge), the statement
`ZInQ.RouteK.Rank5b.RedeiFormula` (`RouteK/Rank5b/Sec3/RedeiStatement.lean`), the theorem
`ZInQ.RouteK.Redei.redeiFormula`, the two main-theorem variants that no longer take `RedeiFormula`, and
the trust statements and `KERNEL_PLAN.md` text that describe them.

## Verdict

**No blocker.** The statement is faithful. A PARI cross-check on 30 pairs agrees with it, and the
proof is unconditional. The build passes, and all 50 entries of `scripts/print_axioms.lean` depend only on
`propext`, `Classical.choice` and `Quot.sound`. Two docstring defects remain, neither blocking (N1, N2
below). There are also a few cosmetic items and one stale blueprint page outside the Lean tree.

## 1. Faithfulness of the statement

### 1.1 `gCl n` is `#(2 Cl(ℚ(√−n)))`

- `QNeg n := QuadraticAlgebra ℚ (−n) 0` is `ℚ[ω]/(ω² = −n + 0·ω)`, i.e. `ℚ(√−n)`.
  Its `Field` structure is Mathlib's (`Mathlib/Algebra/QuadraticAlgebra/Basic.lean:607`). It is
  enabled by `Fact (∀ r, r² ≠ a + 0·r)`, which comes from `Fact ¬IsSquare (−n)`
  (`QNeg.factNotIsSquare`, proved for `NeZero n`). The field operations are the algebra's own ring
  operations, and no second `Field` instance competes.
- `𝓞 (QNeg n)` is `NumberField.RingOfIntegers`, the integral closure of `ℤ`, i.e. the full ring of
  integers, not `ℤ[√−n]`. `Redei/Field.lean` itself uses `θ = (1+ω)/2 ∈ 𝓞` for `n ≡ 3 (mod 4)`
  (`isIntegral_theta`).
- `ClassGroup` is Mathlib's ideal class group of the Dedekind domain `𝓞`. For an imaginary quadratic
  field it equals the narrow class group. It is finite (`Fintype` instance), so `Nat.card` is not the
  junk value `0`.
- `(powMonoidHom 2).range` is the subgroup `Cl²`, so `gCl n = #Cl² = #(2Cl)` in additive notation.
  This is TYZ's `g(n)` (`nt-tyz.md` Notation: `g(d) = #2Cl(ℚ(√−d)) mod 2`, TYZ §1 L363).
- `RedeiFormula` applies `gCl` only at `dProd B`. That number is squarefree and odd
  (`redeiB_squarefree`, `redeiB_odd`), so `QNeg (dProd B)` is exactly the field TYZ mean.

### 1.2 `gBit` is Rédei's bit

`gBit d B = redeiG (aBit d) (yBit d) (zBit d) B` (`Sec3/Defs.lean:77`), where:
- `aBit d i j = legBit p_i p_j`, i.e. `[p_j/p_i]`;
- `yBit = λ_p = [−1/p]` and `zBit = μ_p = [2/p]`;
- `lapl` is the Rédei Laplacian `L_B`, with diagonal `Σ_{k∈B, k≠i} a_ik = [(d_B/p_i)/p_i]`;
- `κ_ρ(B) = det L_B[B∖ρ, B∖ρ]`;
- `redeiG` is `Σ y_ρ κ_ρ` if `y(B) = 1`, else `Σ z_ρ κ_ρ`.

This is tyz-5b Proposition 2.3 term for term (case 1 through `Σ y_ρ κ_ρ = κ(B)`, Lemma 2.2(1)).
`gBit d B` depends only on `B`, not on the other primes of `d`.

### 1.3 `RedeiFormula` matches its trust text

```
∀ d, Odd d → Squarefree d → ∀ B : Finset d.primeFactors, B.Nonempty →
  (dProd B % 8 = 7 ∨ dProd B % 8 = 3 ∨ dProd B % 8 = 1) → (gCl (dProd B) : ZMod 2) = gBit d B
```

This is the docstring's claim: odd squarefree `d`, nonempty `B`, `d_B ≡ 7, 3, 1 (mod 8)`. The
nonemptiness hypothesis is needed. For `B = ∅`, `gBit d ∅ = 0` (empty sum) while `g(1) = #2Cl(ℚ(i)) = 1`.
The proof is stronger than the statement. `gCl_dProd_eq_gBit` (Bridge.lean:267) needs only `Odd d`
and `B.Nonempty`: no squarefreeness of `d` and no mod-8 condition, so `d_B ≡ 5` is covered too.

### 1.4 `T5bCl` is the genus sum of Proposition N

`T5bCl d` sums `Π_{B∈π} gCl(d_B)` over the set partitions `π` of the primes of `d` (Finpartition of
`univ`, so the blocks are nonempty). A partition counts when it has exactly one block `≡ 7`,
exactly one block `≡ 3`, and every block in `{7, 3, 1} (mod 8)`. Such a partition is the same thing as a choice of
`(d₀ ≡ 7, d₁ ≡ 3)` together with a partition of `n/d₀d₁` into blocks `≡ 1`. So the sum is
`Σ_{d₀≡7, d₁≡3} g(d₀) g(d₁) 𝓛₁(n/d₀d₁)` (`𝓛₁(1) = 1` is the empty product). That is `T_5b(n)` of
`nt-tyz.md` Proposition N. `T5bCl_eq_T5b` uses `RedeiFormula` exactly on the blocks of admissible
partitions, which are nonempty and in classes `7, 3, 1`.

### 1.5 PARI cross-check (30 pairs, one after another)

`scratch/rv-redei/gbit_check.py` (cypari2 / PARI 2.17) transcribes `gBit` from the Lean definitions
(`legBit`, `lapl`, `kappa`, `redeiG`). It compares that with the parity of `#Cl²` from
`quadclassunit(D)`, where `D = −d_B` for `d_B ≡ 3 (mod 4)` and `D = −4d_B` otherwise. The 30 pairs
`(d, B)` cover 1 to 5 primes in `B` and all three classes `7, 3, 1 (mod 8)`. In 18 of them `d` has
primes outside `B`. **30/30 agree.** Both parities occur (14 even, 16 odd), so the formula is not
trivially constant.

```
d=       35 B=[7]                    d_B=        7 mod8=7 Cl=[]             #2Cl mod 2=1 gBit=1 ok
d=       69 B=[23]                   d_B=       23 mod8=7 Cl=[3]            #2Cl mod 2=1 gBit=1 ok
d=     3955 B=[7, 113]               d_B=      791 mod8=7 Cl=[32]           #2Cl mod 2=0 gBit=0 ok
d=      527 B=[31, 17]               d_B=      527 mod8=7 Cl=[18]           #2Cl mod 2=1 gBit=1 ok
d=    20951 B=[7, 41, 73]            d_B=    20951 mod8=7 Cl=[94, 2]        #2Cl mod 2=1 gBit=1 ok
d=     3315 B=[3, 5]                 d_B=       15 mod8=7 Cl=[2]            #2Cl mod 2=1 gBit=1 ok
d=     6477 B=[127, 17]              d_B=     2159 mod8=7 Cl=[60]           #2Cl mod 2=0 gBit=0 ok
d=    14637 B=[7, 17, 41]            d_B=     4879 mod8=7 Cl=[26, 2]        #2Cl mod 2=1 gBit=1 ok
d=      143 B=[11, 13]               d_B=      143 mod8=7 Cl=[10]           #2Cl mod 2=1 gBit=1 ok
d=      255 B=[3, 17]                d_B=       51 mod8=3 Cl=[2]            #2Cl mod 2=1 gBit=1 ok
d=      779 B=[19, 41]               d_B=      779 mod8=3 Cl=[10]           #2Cl mod 2=1 gBit=1 ok
d=    34013 B=[43, 113]              d_B=     4859 mod8=3 Cl=[30]           #2Cl mod 2=1 gBit=1 ok
d=    19491 B=[3, 73, 89]            d_B=    19491 mod8=3 Cl=[28, 2]        #2Cl mod 2=0 gBit=0 ok
d=  1324147 B=[11, 17, 73, 97]       d_B=  1324147 mod8=3 Cl=[18, 6, 2]     #2Cl mod 2=1 gBit=1 ok
d=    15015 B=[3, 5, 7, 11, 13]      d_B=    15015 mod8=7 Cl=[12, 2, 2, 2]  #2Cl mod 2=0 gBit=0 ok
d=       85 B=[17]                   d_B=       17 mod8=1 Cl=[4]            #2Cl mod 2=0 gBit=0 ok
d=      123 B=[41]                   d_B=       41 mod8=1 Cl=[8]            #2Cl mod 2=0 gBit=0 ok
d=      231 B=[3, 11]                d_B=       33 mod8=1 Cl=[2, 2]         #2Cl mod 2=1 gBit=1 ok
d=     1241 B=[17, 73]               d_B=     1241 mod8=1 Cl=[16, 2]        #2Cl mod 2=0 gBit=0 ok
d=      455 B=[5, 13]                d_B=       65 mod8=1 Cl=[4, 2]         #2Cl mod 2=0 gBit=0 ok
d=    78761 B=[17, 41, 113]          d_B=    78761 mod8=1 Cl=[60, 2, 2]     #2Cl mod 2=0 gBit=0 ok
d=     6555 B=[3, 19]                d_B=       57 mod8=1 Cl=[2, 2]         #2Cl mod 2=1 gBit=1 ok
d=      805 B=[7, 23]                d_B=      161 mod8=1 Cl=[8, 2]         #2Cl mod 2=0 gBit=0 ok
d= 25838569 B=[41, 73, 89, 97]       d_B= 25838569 mod8=1 Cl=[148, 4, 2, 2] #2Cl mod 2=0 gBit=0 ok
d=      339 B=[113]                  d_B=      113 mod8=1 Cl=[8]            #2Cl mod 2=0 gBit=0 ok
d=     5365 B=[5, 29]                d_B=      145 mod8=1 Cl=[4, 2]         #2Cl mod 2=0 gBit=0 ok
d=      651 B=[7, 31, 3]             d_B=      651 mod8=3 Cl=[4, 2]         #2Cl mod 2=0 gBit=0 ok
d=      105 B=[3, 5, 7]              d_B=      105 mod8=1 Cl=[2, 2, 2]      #2Cl mod 2=1 gBit=1 ok
d=       95 B=[19]                   d_B=       19 mod8=3 Cl=[]             #2Cl mod 2=1 gBit=1 ok
d=     7215 B=[5, 13, 3]             d_B=      195 mod8=3 Cl=[2, 2]         #2Cl mod 2=1 gBit=1 ok
pairs: 30 mismatches: 0
```

### 1.6 Instances in Lean

To check that the hypotheses can be met and that the conclusion carries information, a scratch file
(compiled with `lake env lean` after `lake build ZInQKernel`, then deleted per the task rules)
derives three facts from `Redei.redeiFormula`:
- `Odd (gCl 7)` (true: `h(−7) = 1`);
- `Odd (gCl 19)` (true: `h(−19) = 1`);
- `Even (gCl 17)` (true: `Cl(−68) ≅ ℤ/4`, `#2Cl = 2`).

It also checks `ramSet 1 = {2}`, which is the junk case behind the earlier `n = 1` defect. All of it
compiles, with axioms `propext, Classical.choice, Quot.sound`. Source:

```lean
import ZInQKernel

/-!
rv-redei: instantiate `redeiFormula` on small cases, to check that its hypotheses are satisfiable and
that its conclusion carries real information (both parities occur):
* `d = 7`  (`B = {7}`,  `d_B ≡ 7`): `gBit = 1`, so `#2Cl(ℚ(√−7))` is odd  (true: `h = 1`);
* `d = 19` (`B = {19}`, `d_B ≡ 3`): `gBit = 1`, so `#2Cl(ℚ(√−19))` is odd (true: `h = 1`);
* `d = 17` (`B = {17}`, `d_B ≡ 1`): `gBit = 0`, so `#2Cl(ℚ(√−17))` is even (true: `Cl ≅ ℤ/4`).
-/

open ZInQ.RouteK ZInQ.RouteK.Rank5b ZInQ.RouteK.Rank5b.Sec3

namespace RvRedeiScratch

theorem gCl_congr {m n : ℕ} [NeZero m] [NeZero n] (h : m = n) : gCl m = gCl n := by
  subst h; rfl

theorem dProd_univ_of_prime {p : ℕ} (hp : p.Prime) :
    dProd (Finset.univ : Finset p.primeFactors) = p := by
  unfold dProd
  rw [Finset.prod_coe_sort p.primeFactors (fun x => x), hp.primeFactors, Finset.prod_singleton]

theorem gBit_univ_of_prime {p : ℕ} (hp : p.Prime) :
    gBit p Finset.univ = if lamBit p = 1 then lamBit p else muBit p := by
  have hmem : p ∈ p.primeFactors := by simp [hp.primeFactors]
  have hall : ∀ x : p.primeFactors, x = ⟨p, hmem⟩ := fun x => by
    apply Subtype.ext
    have h := Nat.mem_primeFactors.1 x.2
    exact (Nat.prime_dvd_prime_iff_eq h.1 hp).1 h.2.1
  have hu : (Finset.univ : Finset p.primeFactors) = {⟨p, hmem⟩} := by
    ext x; simp [hall x]
  have hk : ∀ ρ, kappa (aBit p) Finset.univ ρ = 1 := by
    intro ρ
    unfold kappa
    have : IsEmpty ↥((Finset.univ : Finset p.primeFactors).erase ρ) := by
      constructor
      rintro ⟨x, hx⟩
      rw [Finset.mem_erase] at hx
      exact hx.1 ((hall x).trans (hall ρ).symm)
    exact Matrix.det_isEmpty
  unfold gBit redeiG
  simp only [hk, mul_one]
  rw [hu]
  simp only [Finset.sum_singleton]
  rfl

theorem case7 : Odd (gCl 7) := by
  have hp : Nat.Prime 7 := by norm_num
  have : Fact (Nat.Prime 7) := ⟨hp⟩
  have h := Redei.redeiFormula 7 (by decide) hp.squarefree Finset.univ
    ⟨⟨7, by simp [hp.primeFactors]⟩, Finset.mem_univ _⟩ (by rw [dProd_univ_of_prime hp]; omega)
  rw [gBit_univ_of_prime hp, lamBit_eq] at h
  rw [gCl_congr (dProd_univ_of_prime hp)] at h
  norm_num at h
  exact (ZMod.natCast_eq_one_iff_odd).1 h

theorem case19 : Odd (gCl 19) := by
  have hp : Nat.Prime 19 := by norm_num
  have : Fact (Nat.Prime 19) := ⟨hp⟩
  have h := Redei.redeiFormula 19 (by decide) hp.squarefree Finset.univ
    ⟨⟨19, by simp [hp.primeFactors]⟩, Finset.mem_univ _⟩ (by rw [dProd_univ_of_prime hp]; omega)
  rw [gBit_univ_of_prime hp, lamBit_eq] at h
  rw [gCl_congr (dProd_univ_of_prime hp)] at h
  norm_num at h
  exact (ZMod.natCast_eq_one_iff_odd).1 h

theorem case17 : Even (gCl 17) := by
  have hp : Nat.Prime 17 := by norm_num
  have : Fact (Nat.Prime 17) := ⟨hp⟩
  have h := Redei.redeiFormula 17 (by decide) hp.squarefree Finset.univ
    ⟨⟨17, by simp [hp.primeFactors]⟩, Finset.mem_univ _⟩ (by rw [dProd_univ_of_prime hp]; omega)
  rw [gBit_univ_of_prime hp, lamBit_eq, muBit_eq 17 (by norm_num)] at h
  rw [gCl_congr (dProd_univ_of_prime hp)] at h
  norm_num at h
  exact (ZMod.natCast_eq_zero_iff_even).1 h

/-- The junk case excluded by `1 < n`: `OddGClStatement`'s right side fails at `n = 1`
(checked in the redei-four report); here only that `ramSet 1 = {2}` is nonempty while
`(1).primeFactors = ∅`, i.e. the `e = 0 ∨ e = e_n` disjunction would exclude `e = 1_{2}`. -/
example : Redei.ramSet 1 = {2} := by simp [Redei.ramSet]

end RvRedeiScratch

#print axioms RvRedeiScratch.case7
#print axioms RvRedeiScratch.case17
```

## 2. Vacuity and junk values

`redeiFormula : RedeiFormula` is a closed theorem about `gCl` and `gBit`. Its statement uses none
of `chi`, `ambigClass`, `psi`, `ramIdeal`, `ramSet`, `redeiEntry` or `genusMap`. Because the
kernel checks the proof, no junk value inside the chain can make the final theorem false. What
remains to check is (a) that `RedeiFormula` is not vacuous, and (b) that the intermediate
statements are honest.
- (a) Its hypotheses can be met, and its conclusion takes both values (§1.5, §1.6).
- `OddGClStatement` (Bridge.lean:39) has the hypotheses `NeZero n`, `Odd n`, `Squarefree n`, `1 < n`.
  `gCl_dProd_eq_gBit` discharges them at `n = d_B` (`redeiB_odd`, `redeiB_squarefree`,
  `redeiB_one_lt`, from `B.Nonempty`). After the `1 < n` fix it holds at every remaining `n`:
  - `n = 3` (`ramSet = {3}`, `R_33 = [1/3] = 0`, kernel `= {0, e_3}`, `h = 1`);
  - `n = 5` (`R_{5,2} = [2/5] = 1`, kernel `{0, e_5}`, `Cl ≅ ℤ/2`, `#2Cl = 1`);
  - `n = 17` (both entries `0`, kernel `= 𝔽₂²`, `#2Cl = 2`).

  These match by hand. tyz-5b (G1) writes "`d > 3` in case 1". At `d = 3` the kernel is still
  `{0, e_d}`, so the Lean `1 < n` is the right bound.
- Junk branches, all guarded:
  - `chi` is `1` unless `n` is squarefree. Every use carries `hsq`.
  - `ramIdeal p` is `⊤` for non-prime `p`. It is only evaluated at `p ∈ ramSet n`, which is prime
    (`prime_of_mem_ramSet`).
  - `ramSet` assumes `n` odd. Every theorem about it takes `Odd n`.
  - `ambigClass` falls back to `1` when `[𝔭_p]² ≠ 1`. `ambigClass_eq` shows the fallback never
    fires for odd squarefree `n`.
  - `chiBit` depends on a chosen representative. `chiBit_mk0` proves independence.
  - `redeiEntry` reads `n/q` with `Nat` division, which is exact for `q ∣ n`.
- No hypothesis of a used theorem is unsatisfiable. The chain needs only `Odd`, `Squarefree`,
  `1 < n`, the existence of a nontrivial automorphism (`exists_conj_ne_one`, proved) and
  `B.Nonempty`.

## 3. Main-theorem variants and documentation

- In `git diff 2b048334^1 2b048334`, `…_sixContactMin_certifiedRankTYZCl` (RouteK/Rank5bSec3.lean:67)
  and `…_sixContactMin_certifiedRankTYZClRk` (RouteK/RankVariants.lean:67) change only in two ways:
  the `hR : RedeiFormula` argument is removed, and `RouteK.Redei.redeiFormula` takes its place in
  the proof term. Nothing else changed. Both are in `scripts/print_axioms.lean`.
- `KERNEL_PLAN.md` (lines ~126–163) is accurate: `RedeiFormula` is the theorem `redeiFormula`, and
  the class-number variants take only SixContactMin and the TYZ hypothesis.
- The trust statements of `CertifiedRank` (Hypotheses/CertifiedRank.lean:38–41), `CertifiedRankSel`
  (Selmer/Covering.lean:376–378), `CertifiedRankRk`, `CertifiedRankTYZRk` and `CertifiedRankTYZClRk`
  (Rank/Statements.lean:35–38, 55–56, 70) correctly say that Rédei's formula is proved in Lean.
  They also correctly say that the class-number form needs no Rédei formula.

Findings (not blocking, docstrings only):

- **N1.** `RouteK/Rank5b/Sec3/TYZ.lean:107–108` (trust statement of `CertifiedRankTYZ`) says "for
  every set `B` of primes of `d` with `d_B ≢ 5 (mod 8)`, `gBit d B = #2Cl(ℚ(√−d_B)) mod 2`". This is
  false for `B = ∅`, where `gBit d ∅ = 0` but `g(1) = 1`. This is the same kind of edge case as the
  `n = 1` defect. The Lean statement has `B.Nonempty` and is correct. Fix: "every nonempty set". The
  restriction `≢ 5` could be dropped, since `gCl_dProd_eq_gBit` covers every nonempty `B`.
- **N2.** `TYZ.lean:92–93` says "It follows from the following published results, none of them
  formalized here". Its own Rédei bullet (line 109) says "This step is proved in Lean". Fix: "none of
  them formalized here except Rédei's formula".
- Cosmetic: `CertifiedRankTYZCl`'s docstring (RedeiStatement.lean:96–97) cites only the conditional
  `certifiedRankTYZ_iff_of_redeiFormula`. It could add the unconditional `Redei.certifiedRankTYZ_iff'`.
  `KERNEL_PLAN.md` says "the eight modules of redei-plan §3.2". There are nine files: the plan's eight
  plus the small `Entry.lean`.
- Outside the Lean tree: `blueprint/roadmap/rank-5b/certified-rank-5b.md:16–34` is stale. It says
  "none of which is formalized", but row 5b (Theorem 3.6), Rédei's formula and RK9 are now proved.
  It also states TYZ's conclusion as "`2^{−ρ(n)}𝓛(n)` is odd", while nt-tyz's Proposition N uses only
  `𝓛(n) ≠ 0`.

## 4. Build and axioms

- `lake build ZInQKernel`: **Build completed successfully (9918 jobs)**. No errors and no `sorry`
  warnings (6 min wall time).
- `lake env lean scripts/print_axioms.lean`: 50 entries, every one
  `[propext, Classical.choice, Quot.sound]`. This includes `RouteK.Redei.oddGClStatement`,
  `RouteK.Redei.redeiFormula`, `certifiedRankTYZ_iff'`, `certifiedRankTYZRk_of_certifiedRankTYZClRk`
  and the two variants `…_certifiedRankTYZCl` and `…_certifiedRankTYZClRk`.
- `ZInQKernel/RouteK/Redei/` and `RedeiStatement.lean` contain no `axiom`, `native_decide`,
  `implemented_by`, `extern`, `set_option` or `sorry`.
