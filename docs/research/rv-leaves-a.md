# rv-leaves-a: adversarial review of the I1, I5 and assembly leaves

Task rv-leaves-a, 2026-11-11, 22:23-23:15 PST. Scope: pkg-I1's `ThetaModularity`, `QMHauptmodul`,
`IgusaClebschSeparation` (`scratch/pkg-I1/I1.lean`); pkg-I5's `BostEC`, `BostGoodGenus2`,
`PazukiGoodGenus2` and the definitions they use (`scratch/pkg-I5/I5.lean`); glue-assembly's
`GlueOutputs` and `sixContactMinAt_of_glueOutputs` (`scratch/glue-assembly/`). Results log:
`scratch/rv-leaves-a/log.md`.

Marks: VERIFIED (read, computed or compiled here), STANDARD (published, exact reference),
SPECULATIVE. No network access, and none of the papers was available here, so every theorem
number is UNVERIFIED unless another note records it as read (ASTRA-READ).

## Verdicts

| Statement | Verdict | One-line reason |
| --- | --- | --- |
| `ThetaModularity` | **FAITHFUL** | Igusa's theta expressions for `ψ₄` and `χ₁₀` plus their modularity for `Sp₄(ℤ)`, with trivial character. It is a direct consequence of those results. Signs and weights were re-run numerically on 5 generators |
| `QMHauptmodul` | **FAITHFUL, but COMPOSITE** (not printed anywhere as one theorem) | Lin–Yang Ex. 30 (divisors of `ψ₄`, `χ₁₀` on the QM curve), Igusa's theta expressions and the Shimura/Hashimoto modular embedding, combined by glue. It is true: an independent numerical check (below) found every value, the invariance under all three Atkin–Lehner classes, and local orders `4, 6, 2` at the three elliptic points. Its BG citation should be narrowed (see the BG 3.7 section) |
| `IgusaClebschSeparation` | **FAITHFUL** | Clebsch–Bolza–Igusa: in characteristic 0, invariants separate the stable `SL₂`-orbits of binary sextics, and `J₂, J₄, J₆, J₁₀` generate the even-degree invariants up to `J₈`, with `4J₈ = J₂J₆ − J₄²` |
| `BostEC` | **FAITHFUL** (a consequence) | In Faltings' normalization Bost's bound reads `h_F ≥ −log(π√2)·g ≈ −1.4913g`, and the leaf's `−3/2` is weaker |
| `BostGoodGenus2` | **FAITHFUL** (a consequence), conditional on the good-model bridge | `−3 ≤ h_F`, with `faltingsHeightGood` equal to the stable Faltings height of `Jac C` (BLR 9.5, Liu, Lockhart; STANDARD). Non-vacuity is SPECULATIVE (see below) |
| `PazukiGoodGenus2` | **FAITHFUL modulo an UNVERIFIED normalization; hardened form given** | Pazuki 2012 Cor. 1.3(2) read through Thomae. It shifts `h_F` by `log π` (Deligne's normalization). If Pazuki's normalization is a larger shift, the leaf is stronger than published. The hardened form with `+3` covers every shift `≤ 3`, costs nothing downstream, and compiles |
| `GlueOutputs` | **Correct glue interface, NOT a leaf** (a disguised height bound, as its author says) | Each conjunct is the output of the cited theorem with the right constants: GR14 `κ`, Faltings Lemma 5, Bost and Pazuki are checked below; Javanpeykar's constant is UNVERIFIED. It must not be announced as a literature statement |
| `sixContactMinAt_of_glueOutputs` | **VERIFIED; conclusion is exactly `ZInQ.SixContactMin`** | Compiled here against the real `ZInQKernel.Hypotheses.HeightMin`: `SixContactMinAt Mult.S_mul = ZInQ.SixContactMin` by `rfl`, and `GlueOutputs Mult.S_mul → ZInQ.SixContactMin` uses only the three standard axioms |

None of the eight statements is VACUOUS or WRONG, and none is trivially true. One correction to
glue-assembly §1.3: scratch files *can* import `HeightMin` once
`lake build ZInQKernel.Hypotheses.HeightMin` has been run, which builds the upstream `lean/`
package. It succeeded here (9065 jobs).

## 1. Lean checks (VERIFIED: compiled, `lake env lean`, axioms `propext, Classical.choice, Quot.sound`)

- `scratch/rv-leaves-a/ConclusionCheck.lean`. This is glue-assembly's `GlueAssembly.lean` with
  `import ZInQKernel.Hypotheses.HeightMin` added, plus:
  ```lean
  example : GlueAssembly.SixContactMinAt ZInQ.Mult.S_mul = ZInQ.SixContactMin := rfl
  theorem rvLeavesA_sixContactMin_of_glueOutputs (h : GlueAssembly.GlueOutputs ZInQ.Mult.S_mul) :
      ZInQ.SixContactMin := GlueAssembly.sixContactMinAt_of_glueOutputs h
  ```
  Output: `ConclusionCheck.out`, EXIT 0. The report's "word for word" claim is therefore now a
  kernel `rfl`, not a visual comparison. The constants involved are `heightH6`, `heightD`,
  `contactSet`, `contactSupport` and `ratHeight`. They are the kernel's own, imported through
  `HeightConstant` and `HeightMin`; they are not copies.
- `scratch/rv-leaves-a/PazukiHardened.lean`. This is the hardened F3 bookkeeping
  (`pazuki_shift_mono`, `log_pi_le_three`, `f3_numerics_robust`, `f3_numerics_of_logpi`):
  - from `hθ ≤ max(1, h_F+3)/2 + C₂ log(max(1, h_F+3)+2)` it gets the same
    `hθ ≤ 10000·2²⁴·max(1, h_F)` as pkg-I5's `f3_numerics`;
  - the original `log π` form implies the hardened one.
- `scratch/rv-leaves-a/I5Hardened.lean`. pkg-I5's `I5.lean` plus the hardened leaf
  `PazukiGoodGenus2'` (text in §3.3) and
  `pazukiGoodGenus2'_of_pazukiGoodGenus2 : PazukiGoodGenus2 → PazukiGoodGenus2'`. Compiled.
- `scratch/rv-leaves-a/ConclusionCheckHardened.lean`. The whole assembly with `PazukiOutput`
  hardened to `hA + 3` and `pazuki_numerics` re-proved, which gives
  `GlueOutputs' Mult.S_mul → ZInQ.SixContactMin` with the same final constant. Compiled, EXIT 0,
  axioms `propext, Classical.choice, Quot.sound`.

## 2. pkg-I1

### 2.1 `ThetaModularity` — FAITHFUL

- **Published statement.** Igusa, *On Siegel modular forms of genus two (II)*, Amer. J. Math. 86
  (1964), gives `ψ₄ = 2⁻² Σ_{m even} θ_m⁸` and `χ₁₀ = −2⁻¹⁴ ∏_{m even} θ_m²` (UNVERIFIED page;
  the constants agree with LNY §2.2 as used by F1). These are modular forms of weight 4 and 10
  for `Γ₂ = Sp₄(ℤ)` with trivial character (STANDARD). The leaf asserts exactly the
  transformation laws, up to the nonzero constants `2⁻²` and `−2⁻¹⁴`.
- **Normalizations checked.**
  - `thetaConst` is the standard `θ[a,b](Ω) = Σ exp(πi vᵀΩv + 2πi vᵀ(b/2))`, `v = n + a/2`.
  - Even characteristics are those with `aᵀb ≡ 0 (mod 2)`; there are 10, by `decide`.
  - Mathlib's `symplecticGroup` uses `J = [[0,−1],[1,0]]`, which defines the same group as the
    textbook `[[0,1],[−1,0]]`. `spAct` and `spFactor` are the standard action and factor.
  - Off `𝔥₂`, `tsum` would give 0, but the leaf is restricted to `Ω ∈ SiegelH2`.
- **Numerics.** `theta_modular.py` re-run here (`theta_modular.rerun.txt`): on 5 generators,
  the relative error is at most `4·10⁻²⁵`, while the wrong sign `−det¹⁰` gives an error of 2.
  VERIFIED.

### 2.2 `QMHauptmodul` — FAITHFUL (composite)

- **What it rests on.**
  1. Lin–Yang 2020, Ex. 30: on the disc-6 QM curve `X ≅ X₆/W`, `div ψ₄ ∝ P₋₃` and
     `div χ₁₀ ∝ P₋₄`, so `χ₁₀²/ψ₄⁵|_X` has divisor `P₋₄ − P₋₃` and degree 1 (rv-up §3.4,
     UNVERIFIED locator).
  2. Igusa's theta expressions (§2.1).
  3. The identification of `Omega τ` as a period matrix of the principally polarized QM surface
     with Riemann form `Trd(μ⁻¹xȳ)`. This is classical (Shimura; Hashimoto, *Explicit form of
     quaternion modular embeddings*, Osaka J. Math. 32 (1995), UNVERIFIED). For this datum it is
     a computation, i.e. glue.
  4. `Γ*\ℍ` has signature `(0; 2, 4, 6)` (STANDARD: Elkies 1998 for `X*(6)`; Michon), with the
     elliptic points `P₋₂₄`, `P₋₄`, `P₋₃`.

  No single paper prints the leaf. It is a consequence of these results, and it is not stronger
  than them. The announcement should call it a *composite* leaf and list the four inputs.
- **Hypotheses checked.**
  - `B = (2,−3)` with Mathlib's `QuaternionAlgebra ℚ 2 0 (−3)` (`i² = 2`, `j² = −3`).
  - The `𝒪` basis and `μ = 2j+ij`, with `μ² = −6`.
  - The Gram matrix of `Trd(μ⁻¹xȳ)` has determinant 1 (proved in Lean).
  - `ι` is a ring homomorphism on the basis (`qm_embed.py`).
  - `Γ* = ι(N_B(𝒪)) ∩ {det > 0}`. Since `1+i ∈ 𝒪` has reduced norm −1, `N_B(𝒪)⁺` meets every
    class of `N_B(𝒪)/ℚ^×𝒪^×`, so `Γ*` really is the group of `X₆/W` with `W = ⟨w₂, w₃⟩`
    (VERIFIED: `nrd(1+i) = 1 − 2`).
  - For `det > 0`, Mathlib's `GL(2,ℝ)` action on `ℍ` is the Möbius action.
  - The CM clauses quantify over all `x ∈ 𝒪` with `x² = −1`, `x² − x + 1 = 0` or `x² = −6`.
    This is correct because each such fixed point is the unique elliptic point of `Γ*` of order
    4, 6 or 2 respectively. Every `x` with `x² = −6` has `xO = P₂P₃`, so it normalizes `𝒪`.
- **Numerical check, independent of pkg-I1.** `scratch/rv-leaves-a/qm_check.py` is coded from the
  Lean definitions alone; its output is `qm_check.output.txt`, 30 digits, VERIFIED.
  - `Ω(τ)` is symmetric with `Im Ω > 0` at 3 points.
  - Normalizer elements of reduced norm 2, 3 and 6 were found by search. `j_θ(γτ) = j_θ(τ)` to
    `10⁻²⁹`, so all three Atkin–Lehner classes act trivially, not only `w₆`. This settles the
    "twisting" worry: the forgetful map factors through `X₆/W`.
  - At `√2+i`, the fixed point of `i+j`: `j_θ = 0` with local order `3.994 ≈ 4`.
  - At `i√3`, the fixed point of `(1+j)/2`: a pole of order `5.995 ≈ 6`.
  - At `4.18154i`, the fixed point of `μ`: `j_θ = −0.592592592593 = −16/27`, and
    `j_θ + 16/27` has order `1.999 ≈ 2`.
  - A second `x` with `x² = −1`, namely `−i/2 + j + ij/2`, also gives `j_θ = 0`.

  The orders `(4, 6, 2)` equal the elliptic orders, so the zero and the pole are simple on the
  orbifold. With Lin–Yang's divisor statement this gives degree 1, i.e. the fibres are exactly
  the `Γ*`-orbits.
- **Not vacuous.** The CM clauses have instances (`cm4`, `cm3`, `cm24` are proved). `Omega τ`
  is in `𝔥₂`, so `jDen ≢ 0` and the formula clause has content. `F0mat τ · Pinv` is invertible on
  `ℍ`, because it is the B-period matrix of a polarized lattice; otherwise Lean's `⁻¹ = 0` would
  make the clause degenerate (SPECULATIVE beyond the sampled points, STANDARD in theory).

### 2.3 `IgusaClebschSeparation` — FAITHFUL

- **Published statement.** Igusa, *Arithmetic variety of moduli for genus two*, Ann. of Math. 72
  (1960). Over an algebraically closed field of characteristic `≠ 2`, two genus-2 curves are
  isomorphic iff their `[J₂:J₄:J₆:J₈:J₁₀]` agree in weighted projective space. In
  characteristic 0, `J₈ = (J₂J₆ − J₄²)/4`, so `[J₂:J₄:J₆:J₁₀]` suffices (STANDARD).
  Equivalently, by GIT, sextics with nonzero discriminant are stable with closed orbits, and the
  degree-15 invariant's sign is absorbed by `e = −1`.
- **Checks.**
  - `sexticAct` gives `e·(cx+d)⁶f((ax+b)/(cx+d))`.
  - The weights `r, r², r³, r⁵` match `J_{2k}(e·f|M) = (e·det³M)^{2k}J_{2k}(f)`.
  - `J10 ≠ 0` is equivalent to nonzero binary discriminant.
  - The Lean `J`'s match PARI `genus2igusa` on 3 sextics (`decide`). PARI's convention for
    `y² = f` may be the `J`'s of `4f`. That is a weighted rescaling with `r = 16`, so it does not
    affect separation or `lyVec` proportionality.
- **Use.** Only `⇐` carries content, and `equiv_of_lyVec` uses only `⇐`.

### 2.4 Baba–Granath Prop. 3.7

None of the three I1 leaves *needs* BG 3.7 or 3.9:
- `ThetaModularity` and `IgusaClebschSeparation` do not mention BG.
- `QMHauptmodul`'s content is the analytic Hauptmodul with its three values. The `−16/27` at the
  `μ`-fixed point is checked here directly from the theta expression, and in rv-up by
  `endo24.py`/`theta24.py`.

But `QMHauptmodul`'s docstring cites "Baba–Granath 2008 Thm 2.1 **and §3**". §3 contains
Props. 3.7-3.10, where the defect lies. **Repair (citation only):** cite BG Thm 2.1 and the §3
datum (Lemma 3.1, the twisting involutions), not "§3", and add "BG Props. 3.7, 3.9 and Lin–Yang
eq. (2) not used". This matches rv-up §3.5. pkg-I5 and glue-assembly do not cite BG.

## 3. pkg-I5

### 3.1 Normalization of the Faltings height

- `hypGram`/`hypVol` give Faltings' original metric `(i/2)^g ∫ η∧η̄`:
  - two sheets give the factor 2;
  - `(i/2)dx∧dx̄ = dλ`;
  - `det((i/2)∫_C ωᵢ∧ω̄ⱼ) = |det Ω₁|² det Im τ = (i/2)^g ∫_J |ω₁∧…∧ω_g|²` (Riemann bilinear
    relations, STANDARD).
- The integrands are Lebesgue-integrable: simple roots are `1/|x−a|` in 2D, and at infinity the
  decay is `|x|^{2i−deg P}` with `deg P ≥ 5` and `i ≤ 1`.
- Deligne's `(i/2π)^g` normalization shifts the height by `+(g/2) log π`. VERIFIED from
  pkg-I5's `ec_height_check` output: `−1.321117 = −0.748752 − ½ log π`, and `−0.748752` is
  Deligne's value at `j = 0`.

### 3.2 `BostEC`, `BostGoodGenus2` — FAITHFUL (consequences)

- **Published statement.** Bost 1996 (Duke Math. J. 82, or Astérisque 237; UNVERIFIED locator):
  `h(A) ≥ −(g/2) log(2π)` in Deligne's normalization, i.e. `h_F(A) ≥ −g log(π√2) = −1.49130·g`
  in Faltings' (the CMH form recorded in pkg-I5 E4c). GR14 §9 records `−(3/2)·dim A` (ASTRA-READ).
- **Arithmetic** (VERIFIED, python): `½ log(2π²) = 1.49130 < 3/2`. So `−(3/2)g` is a consequence
  in either normalization. The margin is small (`0.0087g`) but sufficient.
- **Consistency.** `BostEC` at `j = 0` reads `−1.321 ≥ −1.5`. Reading Bost's bound as `−(g/2)log 2π`
  in *Faltings'* normalization would contradict this value, so the Deligne reading is forced.
- **`faltingsHeightGood`.**
  - `Good` says `disc₆(4f+h²) = 2¹²·unit`, i.e. Liu's `Δ` is a unit. Then the Weierstrass model
    is smooth (Liu 1996).
  - `Pic⁰` is the Néron model (BLR 9.5 Thm 4).
  - `H⁰(𝒞, ω) = 𝒪_K⟨dx/(2y+h), x dx/(2y+h)⟩`.

  So the height has no finite-place term, and it equals the stable height (STANDARD). `binDisc`
  correctly uses `lc²·disc₅` when `deg P = 5`.
- **Non-vacuity of `Good`.** SPECULATIVE that it is satisfiable: take a curve with potentially
  good reduction everywhere, then extend the field to get good reduction and a global Weierstrass
  model. If `Good` were never satisfiable the leaf would be vacuous but still not stronger than
  Bost. Either way H does not use it: QM surfaces need not have a good curve model (pkg-I5 §3.3).

### 3.3 `PazukiGoodGenus2` — FAITHFUL modulo normalization; hardened version

- **Published statement.** Pazuki, *Theta height and Faltings height*, Bull. SMF 140 (2012),
  Cor. 1.3(2), at `g = r = 2`: `h_Θ ≤ ½ max(1, h) + C₂ log(max(1, h) + 2)`, with
  `C₂ = 1000·2⁴(log 2⁴)⁵` as N5 reads it (ASTRA-READ by h-trust; constant and normalization
  UNVERIFIED here).
- **Composite steps checked.**
  - The direction sup-norm `≤` Euclidean is correct.
  - Heights are invariant under extension of `L`, because `absLogHeight` divides by the degree.
  - Permuting the roots permutes the coordinates, which does not change the height.
  - Thomae (Mumford, *Tata Lectures on Theta II*, IIIa §8, STANDARD) gives
    `θ_T⁴ ∝ Δ(T)Δ(Tᶜ)` over the 10 splittings into triples, so the eighth powers are
    `κ²·Θ_T(a)` and the leading coefficient drops out projectively.
  - Level-2 characteristics give the 16 half-integer theta constants, 6 of which vanish, so the
    projective height equals that of the 10 even ones.
- **The one risk.** `X_D = max(1, h_F + log π)` presumes that Pazuki uses Deligne's normalization.
  The right side is increasing in `X_D`. If his `h` exceeded `h_F + log π`, the leaf would be
  STRONGER THAN PUBLISHED.
- **Hardened leaf** (compiled ingredients in `PazukiHardened.lean`): the same statement with
  `max 1 (faltingsHeightGood E + 3)` in both places. It is a consequence for any normalization
  shift `s ≤ 3`. `f3_numerics_robust` keeps the constant `10000·2²⁴`, so N5's final constant is
  unchanged. Recommended text:
  ```lean
  def PazukiGoodGenus2' : Prop :=
    ∀ (K : Type) [Field K] [NumberField K] (E : Genus2Eq (𝓞 K)), E.Good →
      ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] (a : Fin 6 → L),
        E.P.natDegree = 6 →
        (E.P.map (algebraMap (𝓞 K) K)).map (algebraMap K L) =
          Polynomial.C (algebraMap K L (algebraMap (𝓞 K) K E.P.leadingCoeff)) *
            ∏ i, (X - Polynomial.C (a i)) →
        thetaHeightThomae a ≤
          max 1 (faltingsHeightGood E + 3) / 2 +
            pazukiC2 * Real.log (max 1 (faltingsHeightGood E + 3) + 2)
  ```
  The same change applies to glue-assembly's `PazukiOutput` (`hA + log π` ↦ `hA + 3`).
  `f3_numerics_of_logpi` shows that the old form implies the new one, so the change can be made
  without re-proving anything downstream, apart from swapping `pazuki_numerics` for the robust
  lemma. The `Genus2Eq`/`thomaePoint` text above was not recompiled here: it is a two-token edit
  of pkg-I5's compiled `PazukiGoodGenus2`.

## 4. glue-assembly: `GlueOutputs`

### 4.1 Field by field

| Conjunct | Published source | Constant check | Verdict |
| --- | --- | --- | --- |
| `3779136(∏z)⁴/(Σz⁸)⁵ = J(u)` | F1 = `QMHauptmodul` + `ThetaModularity` + the canonical model (I1-a, not statable) | Degree 40/40, so projective. `J(u) ≠ 0` (`Ju_ne_zero`), so a zero denominator is excluded | OK |
| `PazukiOutput` | Pazuki Cor. 1.3(2) | as §3.3, sup ≤ L² (glue-assembly §2.7) | OK modulo normalization; harden to `+3` |
| `hFJ ≤ 1.3·10⁷N¹²` | Javanpeykar 2014, Thm 1.1.1 (`h_Fal(X) ≤ 13·10⁶ g·deg_B(X)⁵`, UNVERIFIED form) with `g, deg_B(X₁(N)) ≤ N²` | `13·10⁶·N²·N¹⁰`. `deg_B ≤ [PSL₂ℤ : ±Γ₁(N)] ≤ N²` (STANDARD) | OK if the printed form is `g·d⁵`. Safe whether Javanpeykar uses Faltings' or Deligne's normalization, since Deligne's is larger |
| `L ≤ 1024g³(64g² log 14g + log d + 2 log max(hFJ, log d, 1))` | GR14 Thm 1.4: `κ = ((14g)^{64g²} d max(h, log d, 1)²)^{2¹⁰g³}` | `log κ` term by term: `2¹⁰ = 1024`, `log(14g)^{64g²}`, `2 log max` ✓. GR's `h` is Faltings' original (Bost appears there as `−log(π√2)g`) ✓. The witness `hFJ := h_F(J₁(N))` makes monotonicity harmless | OK |
| `hA + hZ ≤ hFJ + L/2` | Faltings 1983 Lemma 5 + additivity | independent of normalization | OK |
| `−(3/2)g ≤ hZ` | Bost | §3.2. `dim Z ≤ g`, and `dim Z = 0` gives 0 | OK |
| `CMOutput` | GR14 with source `E²`: `g = 2` gives `14g = 28`, `64g² = 256`, `2¹⁰g³ = 8192`, `h(E²) = 2h(E)` | ✓ | OK (and unused: NoCM) |

Minor points:
- `L` has no lower bound (`log deg ≥ 0` is missing). This is harmless: it only weakens the
  hypothesis.
- `d` must be the degree of a field over which the GR isogeny is defined. That is B3's job.

### 4.2 Status

- `GlueOutputs` is **not vacuous**: `z` exists after a field extension.
- It is **not trivially true**: for any `z` with `Φ(z) = J(u)`, `h(J(u)) ≤ 40h(z) + 16` (F2).
- But it is **essentially equivalent to `JHeightBound`**. The witness `hA` is free, and the
  NonCM conjuncts are satisfiable for any small `hA` (choose `L`, `hZ`). So its content is
  "some preimage `z` of `J(u)` under `Φ` has height `≤ f(X(D)M²⁴)`", and `JHeightBound` gives
  such a `z` explicitly (`z = (t, 1, …, 1)`).

It is the glue interface it says it is, a disguised height bound. **The announcement must not
list it as a leaf.** The leaves behind it are Javanpeykar, GR14, Faltings Lemma 5, Bost and
Pazuki for abelian varieties of dimension up to `N²`. All of these need Faltings heights of
abelian varieties, which Mathlib lacks. Only the genus-1 and good-genus-2 special cases
(`BostEC`, `BostGoodGenus2`, `PazukiGoodGenus2`) are statable today, and none of them covers
what H uses.

### 4.3 The assembly theorem

VERIFIED (§1): `GlueOutputs Mult.S_mul → ZInQ.SixContactMin` compiles against the kernel's own
definitions, and the identification is a kernel `rfl`.

## 5. What remains unchecked

- All published theorem numbers and constants, in particular Pazuki's `C₂` and normalization,
  and the exact printed form of Javanpeykar Thm 1.1.1. No papers were available here.
- Satisfiability of `Genus2Eq.Good` is SPECULATIVE.
- The Lin–Yang Ex. 30 divisor statement, which `QMHauptmodul`'s degree-1 claim rests on, was not
  read. The numerics corroborate it only locally, through the elliptic orders.
