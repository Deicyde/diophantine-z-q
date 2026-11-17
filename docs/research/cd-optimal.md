# cd-optimal: `CdOptimal` from the eta-quotient transformation law and one non-divisibility

Status: research note (task cd-optimal, 2026-11-16), branch `wip/cd-optimal`, base wip/gz-optimal 2631cd0b.
Lean: new files `ZInQKernel/Contrib/OneProof/CdOptimal.lean` and `ZInQKernel/Contrib/OneProof/CdOptimal/`
(`Unif.lean`, `Structure.lean`, `Level32.lean`). Nothing else under `ZInQKernel/` was edited. Scratch, checks and log:
`scratch/cd-optimal/`.

Marks. **VERIFIED**: read in a source named here, computed, or compiled. **STANDARD**: a published theorem with an
exact reference. **SPECULATIVE**: an assessment. This host has no network and no copy of Newman, Gordon–Hughes, Ono,
Ihara, Ribet or Serre. **Every theorem number and locator of the literature below is UNVERIFIED** (from memory).

---

## 0. Main result

**`CdOptimal` is not proved outright. It is reduced, in Lean, to one printed classical statement and one strictly
smaller piece of glue.**

```lean
-- CdOptimal.lean
theorem ZInQ.CdOpt.cdOptimal_of (hW : EtaW32Character) (hT : CdTwistedPeriodOdd) :
    ZInQ.GZOptimal.CdOptimal
theorem ZInQ.CdOpt.grossZagierFormulaCd_of_cdLeaves (hGZ : ZInQ.GZOptimal.GrossZagierModuliOptCd)
    (hW : EtaW32Character) (hT : CdTwistedPeriodOdd) : ZInQ.GZHL3.GrossZagierFormulaCd
theorem ZInQ.CdOpt.periodLattice_le_of_etaW32 (hW : EtaW32Character) ... :
    ZInQ.GZOptimal.periodLattice f ≤ L.lattice          -- Λ_f ⊆ L(C_d), every admissible d
```

* **`EtaW32Character`** (new leaf, **printed form**: an instance of the Newman / Gordon–Hughes transformation law of
  eta quotients). The quotient `v = η(8τ)η(32τ)²/η(16τ)³` satisfies `v(γτ) = (2/d) v(τ)` on `Γ₀(32)`.
* **`CdTwistedPeriodOdd`** (new glue, **not printed**). For `d ≡ 5 (mod 8)` squarefree and every period lattice `L`
  of `C_d`, some period `Φ_d(γτ) − Φ_d(τ)` (`γ ∈ Γ₀(32d²)`) lies outside `(1 + i) L`.
  - It is true numerically for every tested `d` (§4).
  - It is the non-congruence half of `CdOptimal`. §4 explains why no congruence or cusp computation can prove it.

Everything else is proved in Lean. All theorems use only `[propext, Classical.choice, Quot.sound]` (VERIFIED,
`scratch/cd-optimal/out_check.txt`):

1. **Uniqueness of the period lattice** (`lattice_eq_of_g₂_g₃`): two period pairs with the same `g₂, g₃` have the same
   lattice. The proof is unconditional. It runs gz-weil's uniformization argument in a general form (`Unif.lean`).
2. **`Λ_f` is a `ℤ[i]`-module stable under complex conjugation** (`I_mul_mem_LamCd`, `conj_mem_LamCd`). So is every
   period lattice of `C_d` (`I_mul_mem_of_cd`, `conj_mem_of_cd`, from 1). This is unconditional.
3. **Classification** (`lattice_eq_of_periods`, unconditional): if `Λ_f ⊆ L` and some period lies outside `(1+i)L`,
   then `L = c₀ Λ_f` with `c₀ ∈ ℚ`.
4. **`Λ_f ⊆ L` for every admissible `d`**, from `EtaW32Character` (`LamCd_le_of_etaW32`). This is `CdOptimal`'s
   inclusion with `c₀ = 1`. It sharpens gz-weil's `2 Λ_f ⊆ L`.
5. **The fold**:
   - `scratch/cd-optimal/MainEdit.lean` proves `ZInQ.FrozenTarget` (`frozenTarget_cdoptimal`, standard axioms,
     VERIFIED). There `hL3` is replaced by `{GrossZagierModuliOptCd, EtaW32Character, CdTwistedPeriodOdd}`. The chain
     is otherwise gz-optimal's route A: heegner-32's `grossZagierHeegnerCd_of_printed` and gz-conj's
     `grossConjugationCd`.
   - `scratch/cd-optimal/autofold.json` discharges gz-optimal's project-glue leaf `cdOptimal`.
   - `autofold-formula.json` discharges the field `grossZagierFormulaCd` directly.

**Target: missed.** The target was `hL3` replaced by `GrossZagierModuliOptCd` alone. Here `hL3` becomes
`GrossZagierModuliOptCd` + `EtaW32Character` (printed) + `CdTwistedPeriodOdd` (glue). The counts:
- **Glue**: one glue statement (`CdOptimal`, an equality of lattices up to a rational factor) is replaced by a
  strictly smaller one (`CdTwistedPeriodOdd`, one non-divisibility per `d`). The glue count is unchanged.
- **Printed leaves**: +1 (`EtaW32Character`). It is a classical theorem, and the kernel already has its squared form
  (gz-theta's `η²` multiplier).

---

## 1. The objects

* `Φ_d(τ) = Σ_{n≥1} aₙ(C_d)/n · qⁿ` is gz-weil's `eichlerCd d` (`aₙ = heckeCoeff d n`, Deuring, proved).
* `Λ_d = LamCd d = span_ℤ {Φ_d(γτ) − Φ_d(τ) : γ ∈ Γ₀(32d²), τ ∈ ℍ}`. For a newform `f` of `C_d`,
  gz-optimal's `periodLattice f = Λ_d` (`periodLattice_eq_LamCd`): the level is `32d²` (gz-statements'
  `level_eq_of_coeff_cd`), and `eichler f = Φ_d`.
* A period lattice of `C_d` is a `PeriodPair` with `g₂ = 4d²`, `g₃ = 0` (gz-weil's `isPeriodLattice_cd_iff`).
* Level 32:
  - `Φ₁` and its periods `ρ(γ) = Φ₁(γτ) − Φ₁(τ)` for `γ ∈ Γ₀(32)` (τ-independent: gz-weil's `period_const`);
  - `Λ₁ = span ρ(Γ₀(32))`;
  - `L₁` is a lattice of `C₁ = 32a2 : y² = x³ − x`.

## 2. The proof

### 2.1 Uniqueness of the lattice (`Unif.lean`)

gz-weil's C5–C7 (`WeilParam.lean`) are restated for arbitrary data:
- an open preconnected `U`;
- analytic `X, Y` with `Y² = X³ + AX + B`;
- `X' = 2YΦ'` with `Φ' ≠ 0`;
- a lattice `L` of the curve (`g₂ = −4A`, `g₃ = −4B`).

Then:
- `℘_L(Φ + c₀) = X` on `U` (`local_eq_gen`, `global_eq_gen`);
- if `X ∘ g = X` and `Φ ∘ g = Φ + ω` on `U`, then `ω ∈ L` (`period_mem_gen`).

For `U = ℂ ∖ L'`, `X = ℘_{L'}`, `Y = ℘'_{L'}/2`, `Φ = id`, `g = (· + ω')`, this gives `L' ⊆ L` whenever `g₂, g₃`
agree. Hence the two lattices are equal (VERIFIED, compiled).

### 2.2 Symmetries of `Λ_d` (`Structure.lean`)

* `aₙ(C_d) = 0` unless `n ≡ 1 (mod 4)`: in `heckeCoeff`, `unitOf` vanishes unless `p₁² + p₂² ≡ 1 (mod 4)`. So
  `Φ_d(τ + 1/4) = iΦ_d(τ)`.
* `γ ↦ T^{1/4} γ T^{−1/4}` preserves `Γ₀(32d²)`. This uses Tau Ceti's lemma `exists_upperRightHom_mul_mapGL_…` with
  `M = 4`. Hence `iΛ_d ⊆ Λ_d`.
* `aₙ ∈ ℤ`, so `conj Φ_d(τ) = Φ_d(−τ̄)`. The map `γ ↦ diag(1,−1) γ diag(1,−1)` preserves `Γ₀(32d²)`. Hence
  `conj Λ_d ⊆ Λ_d`.
* For a lattice `L` of `C_d`:
  - `iL` and `L̄` (`scalePP L I`, `conjPP L`) have the same `g₂ = 4d²` and `g₃ = 0`;
  - so `iL = L` and `L̄ = L` by 2.1.

### 2.3 Classification (`Structure.lean`, `lattice_eq_of_periods`)

* A lattice stable under `i` is `ℤ[i]ω` for a shortest nonzero `ω`. The proof is Gaussian rounding:
  `‖z − (round Re z + i round Im z)‖ < 1`.
* So `L = ℤ[i]ω` and `Λ_d = ℤ[i]μ`, and `Λ_d ⊆ L` gives `μ = (p + qi)ω`.
* Conjugation stability gives `ω̄ = u₀ω` and `μ̄ = u₁μ` with units `u₀, u₁`. Hence
  `(p − qi)u₀ = u₁(p + qi)`, and this forces `q = 0`, `p = 0` or `p = ±q` (`gauss_conj_cases`).
* The cases `p = ±q` put `Λ_d` inside `(1 + i)L`, which the hypothesis excludes.
* So `μ = k ω` or `μ = k i ω`, hence `Λ_d = kL` and `L = (1/k) Λ_d`.

### 2.4 `Λ_d ⊆ L` (`Level32.lean`)

* **The model of `C₁` on `X_{Γ'}`, `Γ' = Γ₀(32) ∩ {(2/d) = 1}.**
  - On x0-32's model `y² = x³ + 4x` of `X₀(32)`, put `w = η(16τ)³/(η(8τ)η(32τ)²) = 1/v`. Then `w² = x` (tyz-cm's
    `xC_eq_even`).
  - So `s = −y/w` has `s² = x² + 4`. Put `x₁ = (x + s)/2` and `y₁ = yx₁²/(1 + x₁²)`.
  - These satisfy `y₁² = x₁³ − x₁` and `x₁ − 1/x₁ = x` (the 2-isogeny `C₁ → 32a1`), and `dx₁/dτ = 2y₁ · 2πi f₁`
    (`hasDerivAt_x1C`, from x0-32's `etaModelDifferential`, proved by gz-weil).
  - VERIFIED, compiled. `x₁ = q⁻² ∏_{n≡±3 (8)} (1 − q⁴ⁿ) / ∏_{n≡±1 (8)} (1 − q⁴ⁿ)` is the reciprocal of the
    Göllnitz–Gordon continued fraction at `q⁴` (VERIFIED to `q⁴⁰`, `py/x1fit.gp`).
* **The leaf** gives `w(γτ) = (2/d) w(τ)`, so `x₁, y₁` are `Γ'`-invariant. Then `period_mem_gen` with `U = ℍ` gives
  `ρ(γ) ∈ L₁` for every `γ ∈ Γ'` and every lattice `L₁` of `C₁` (`period_mem_C1`).
* **The twist.**
  1. For `γ ∈ Γ₀(32d²)`, `γ₁₀ = 32d²k`, the identity is
     `d(Φ_d(γτ) − Φ_d(τ)) = Σ_a 𝓕χ_d(a) ρ(γ'_a)` (gz-weil's `period_identity`, restated as `period_identity'` with
     the entries of the `γ'_a`).
  2. All `γ'_a` share `γ₁₀`. Their `(0,0)` and `(1,1)` entries move by multiples of `32dk`.
  3. So `δ_a = γ'_a γ'_0⁻¹ ∈ Γ₁(32)` (`δ₁₁ = 1 + 32(…)`), and `ρ(γ'_a) − ρ(γ'_0) = ρ(δ_a) ∈ L₁` (with
     `L₁ = gL`).
  4. Also `Σ_a 𝓕χ_d(a) = dχ_d(0) = 0` (Fourier inversion at `0`).
  5. Hence `Φ_d(γτ) − Φ_d(τ) = Σ_a χ_d(a) m_a` with `m_a ∈ L`, using `𝓕χ = gχ` and `g² = d`.

## 3. The two new statements and their ratings

| Statement | Kind | Rating and reason |
| --- | --- | --- |
| `EtaW32Character` | published | **LEAF, printed form (a consequence: one instance).** Newman, *Construction and application of a class of modular functions* I/II (Proc. LMS 1957/1959), and Gordon–Hughes, *Multiplicative properties of η-products* II (1981). As stated in Ono, *The web of modularity* (CBMS 102, 2004), Thm 1.64. The hypotheses (for `N = 32`, `r₈ = 1`, `r₁₆ = −3`, `r₃₂ = 2`): `k = ½Σr_δ = 0`, `Σδr_δ = 24 ≡ 0`, `Σ(N/δ)r_δ = 0`. The character is `((−1)^k s / d)` with `s = ∏δ^{r_δ} = 8·32²/16³ = 2`. Stated over the kernel's `X0.etaD` and Mathlib's `χ₈`. Locators UNVERIFIED. One point for a statement check: the print states the law for `d > 0` or with `(cτ+d)^k`; for `k = 0` and the even character `χ₈` the sign of `d` is immaterial. Numerically VERIFIED for 602 matrices (`py/wchar.gp`). |
| `CdTwistedPeriodOdd` | project glue | **GLUE, not printed** (SPECULATIVE). A period computation, numerically true (§4). Given 2.4 it says that `C_d`, not its 2-isogenous curve `y² = x³ + 4d²x`, is `X₀(32d²)`-optimal up to an odd integer factor. No published statement of optimality for the whole family `C_d` is known to me. |

`CdTwistedPeriodOdd` is weaker than `Λ_f = L` (the numerically observed `c₀ = 1`). It is stated concretely over
`eichlerCd`, `Γ₀(32d²)` and `PeriodPair`; no newform is involved.

## 4. The residual `CdTwistedPeriodOdd`

**Why it is the non-congruence half.** Everything in 2.4 is congruence data:
- `ρ mod L₁` is the character `χ₈(d)` (VERIFIED numerically for all `γ` with `c ≤ 768`, `py/analyze.py`);
- it is proved from the leaf.

`CdTwistedPeriodOdd` asks about `ρ` modulo `(1 + i) L₁ = 2Λ₁` (`Λ₁ = ((1+i)/2) L₁`, VERIFIED numerically,
`py/lev32b_out.txt`):
- on `Γ'`, `ρ mod (1+i)L₁` is the character attached to the unramified double cover `√x₁` of `X_{Γ'} ≅ C₁`. This is
  the 2-torsion point `(0,0)` (Weil pairing);
- it does not depend on `(a mod 256, c mod 512)` (VERIFIED numerically): it is not a congruence character.

So no computation with congruence subgroups, eta quotients or cusp values can decide it:
- **Twisted sums cancel at the cusps.** For a cusp `r = A/C` of `X₀(32d²)`, the cusps `r + a/d` of `X₀(32)` all lie
  in the same class modulo `Γ'`: the `a`-dependence enters only through multiples of `32`. So
  `Φ_d(r) ≡ g⁻¹(Σ_a χ_d(a)) t = 0 (mod L)`. This is a derivation, checked only in the cases worked out above; it is
  SPECULATIVE beyond them.
- Consequently the real-component criterion fails too. That criterion would be: a real point of `X₀(32d²)` on the
  non-identity component of `C_d(ℝ)` forces `Λ_d ⊄ (1+i)L`. It cannot be fed with cusps.

**A reduction modulo 2 to level 32** (derivation; not formalized):
1. `χ_d(a) ≡ 1 (mod 2)` on units, so `P(γ) := gΛ_d`-period `≡ Σ_{a unit} ρ(γ'_a)`.
2. With the Hecke relation `Σ_{b mod p} Φ₁(τ + b/p) = a_p Φ₁(pτ) − Φ₁(p²τ)` (`p ∤ 32`), `a_p` even, and Möbius
   inversion over `e ∣ d`:
   `P(γ) ≡ Σ_{e ∣ d} ρ(γ^{(e²)}) (mod (1+i)L₁)`, where `γ^{(e²)} = diag(e²,1) γ diag(e²,1)⁻¹ ∈ Γ₀(32)`.
3. So `CdTwistedPeriodOdd(d)` follows from: **some `γ ∈ Γ₀(32d²)` has `Σ_{e∣d} ρ(γ^{(e²)}) ∉ (1+i)L₁`**. This is a
   statement about `f₁` and the degeneracy maps `X₀(32d²) → X₀(32)` alone.

Numerically (`py/twn_mod2.gp`, output `py/twn_mod2_out.txt`, VERIFIED as a computation; it relies on the derived
reduction 1–3):
- with `γ∞ = A/(32d²)`, an odd `A ≤ 23` works for **all 32 squarefree `d ≡ 5 (mod 8)` with `5 ≤ d ≤ 301`**. The
  coordinates are integral to within `4·10⁻¹⁸`. This also checks that the `χ₈` parts cancel, as 2.4 predicts;
- this is consistent with gz-optimal's direct computation `Λ_d = L` for the 18 values `d ≤ 165`, and it extends the
  evidence to `d ≤ 301` using level-32 periods only;
- `py/twn_table_out.txt` gives, for the primes `p ≡ 5 (mod 8)` up to 109 and all odd `A ≤ 31`, the parity bit of
  `ρ(A/(32p²)) + ρ(A/32)`. Every row has a `1`. For `A = 5` the bit is `1` exactly when `(p/5) = −1` (the 7 primes `13 ≤ p ≤ 109`; consistent with the primes up to 293 in the run above, where `A = 5` succeeded exactly for `(p/5) = −1`).
  For `A = 13` no such Legendre rule holds (`p = 61`). A quartic-residue law may lie behind the bits (SPECULATIVE).

**A possible proof (SPECULATIVE).** For `d = p` prime, the criterion says that `ψ = ρ mod (1+i)L₁` on `Γ'` is not
invariant under conjugation by `diag(p², 1)` on `Γ₀(32p²)`. Suppose it were. Then `ψ` would extend to the group
generated by `Γ'` and `diag(p, p⁻¹)`, an HNN extension inside `SL₂(ℤ[1/p])`. By the congruence subgroup property of
`SL₂(ℤ[1/p])` (Serre 1970) its kernel would be a congruence subgroup, contradicting the non-congruence of `ker ψ`.
This is close in spirit to Ihara's lemma (Ihara 1975; Ribet 1984 and 1990). Three things are unproved here:
- the finite-index and HNN details;
- the non-congruence of `ker ψ` (numerical only);
- the composite case.

## 5. Deliverables

| File | Content | Check |
| --- | --- | --- |
| `ZInQKernel/Contrib/OneProof/CdOptimal/Unif.lean` | general uniformization lemmas; `lattice_eq_of_g₂_g₃` | `lake build` (VERIFIED) |
| `ZInQKernel/Contrib/OneProof/CdOptimal/Structure.lean` | `aₙ = 0` off `1 mod 4`; `Φ_d(τ+1/4) = iΦ_d`; `conj Φ_d(τ) = Φ_d(−τ̄)`; `LamCd`, `periodLattice_eq_LamCd`; `i`- and conjugation-stability; Gaussian rounding; `conjPP`; `lattice_eq_of_periods` | `lake build` (VERIFIED) |
| `ZInQKernel/Contrib/OneProof/CdOptimal/Level32.lean` | `vC`, `wC`, leaf `EtaW32Character`; the model `x₁, y₁` of `C₁`; `period_mem_C1`; `period_identity'`; `LamCd_le_of_etaW32` | `lake build` (VERIFIED) |
| `ZInQKernel/Contrib/OneProof/CdOptimal.lean` | `CdTwistedPeriodOdd`; `cdOptimal_of`; `periodLattice_le_of_etaW32`; `grossZagierFormulaCd_of_cdLeaves` | `lake build` (VERIFIED) |
| `scratch/cd-optimal/Check.lean`, `out_check.txt` | `#print axioms`, 9 theorems | standard axioms (VERIFIED) |
| `scratch/cd-optimal/MainEdit.lean`, `out_mainedit.txt` | `frozenTarget_cdoptimal` | standard axioms (VERIFIED) |
| `scratch/cd-optimal/Discharges.lean`, `discharges-output.txt` | `#discharges` | below |
| `scratch/cd-optimal/autofold.json` | field `cdOptimal` ← `cdOptimal_of`, leaves `etaW32Character` (published), `cdTwistedPeriodOdd` (project glue) | JSON checked |
| `scratch/cd-optimal/autofold-formula.json` | field `grossZagierFormulaCd` ← `grossZagierFormulaCd_of_cdLeaves` (alternative to gz-optimal's spec) | JSON checked |
| `scratch/cd-optimal/Target.lean`, `out_target.txt` | verbatim copy of `CdOptimal`, `rfl` against the original; `cdOptimal_target` | standard axioms (VERIFIED) |
| `scratch/cd-optimal/py/` | PARI scripts and outputs (level-32 periods `lev32b_out.txt`, eta fits, `w` character `wchar.gp`, mod-2 check `twn_mod2_out.txt`, parity table `twn_table_out.txt`) | computed |

**`#discharges`** (`scratch/cd-optimal/discharges-output.txt`, VERIFIED):
- command: `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
  +ZInQKernel.Contrib.OneProof.CdOptimal`, then `lake env lean scratch/cd-optimal/Discharges.lean`;
- result: 61 open hypotheses, 3123 theorems checked, 9 discharge one (the same 9 as before), no line for `CdOpt`;
- as for gz-optimal, `hL3` is a top-level all-`E` argument and the theorems here prove its `C_d` chain. The fold is the
  Main edit or the autofold spec, once gz-optimal's field exists.

Proposed `locators.md` row (for the integrator): `EtaW32Character` → Ono, *The web of modularity*, Thm 1.64; Newman
1957/1959; Gordon–Hughes 1981 (all UNVERIFIED; read the sign convention for `d < 0` and the definition of `s`).

## 6. What remains

* **`CdTwistedPeriodOdd`** (the open glue). A proof needs non-congruence input (§4). The Ihara / congruence subgroup
  route is a sketch only.
* **`EtaW32Character` in Lean** (optional; it is a printed leaf). This needs the eta multiplier for odd powers. The
  kernel has only the `η²` multiplier (`GZTheta/Eta.lean`).
* The mod-2 reduction of §4 (Hecke relation, Möbius inversion) is derived on paper, not in Lean. Formalizing it
  would restate the residual at level 32 (about `f₁` and the degeneracy maps only). It would not make the residual
  easier to prove.
