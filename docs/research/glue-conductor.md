# glue-conductor: Glazer's uniform conductor bound as leaves and glue (h-trust D1-D5)

Status: research note (task glue-conductor, 2026-11-11). Scope: steps D1-D4 of
`docs/research/h-trust.md` (the break bound, semistability and wild inertia at odd `p`, the
`p = 2` paragraph, the conductor exponents), plus how D5 uses Carayol, ending in `N ≤ Q_R M²`.
Source: `diophantine_zq.tex` L796-857 (the conductor paragraph) and L385-400 (the constants).
Lean drafts: `scratch/glue-conductor/` (log: `scratch/glue-conductor/log.md`). No file under
`ZInQKernel/`, `blueprint/` or other notes was edited.

Marks: **VERIFIED** means compiled in Lean, computed exactly, or read in a source quoted here.
**STANDARD** means a published theorem with a reference; theorem numbers given from memory are
marked UNVERIFIED (no network). **SPECULATIVE** means an assessment.

## Summary

1. **Every integer or rational inequality in D1-D5 is now a Lean theorem** (VERIFIED, compiled
   with `lake env lean`, no `sorry`; `#print axioms` gives only `propext`, `Classical.choice` and
   `Quot.sound`). That covers D1's chain `u_last ≤ 2δ/e ≤ 2(1 + log₂ a!) ≤ 4a²`, the Herbrand
   integral, `ψ(u) ≥ u`, the Swan and Artin bounds `Sw ≤ 2U₀` and `a_p ≤ 2 + 2U₀ ≤ E₀`, the
   tame case, the constants (`G₀ = |GL₄(𝔽₅)|`, `max(4D², 3e) ≤ U₀`), and the level product
   `N ≤ Q_R·M_S(u)²`. The level product is stated over the repository's own `heightQ`,
   `heightE0` and `contactSupport`.
2. **D1 is proved over genuine Mathlib definitions from two statable leaves** (VERIFIED). These
   are Hilbert's different formula and Serre's different bound. Both are stated as
   `def … : Prop` over Mathlib's `differentIdeal ℤ (𝓞 L)`, `Ideal.ramificationIdx`, and the
   lower ramification groups `G_i = (P^{i+1}).inertia Gal(L/ℚ)` (Mathlib's `Ideal.inertia`). The
   theorem is `D1_genuine`, and it uses Mathlib's `card_inertia_eq_ramificationIdxIn` for
   `|G_0| = e`.
3. **D3's unit step no longer needs a citation** (VERIFIED). N5 gets
   `(U_F^{e+1})⁴ = U_F^{3e+1}` from the formal logarithm (Silverman IV.6.4). It is now proved
   in both directions for every complete local ring with `(2) = 𝔪^e`, by Hensel's lemma applied
   to two square roots (`Dyadic.lean`). One literature input is removed.
4. **What remains literature (leaves).** These are listed in §3.
   - Statable over Mathlib today: the two D1 leaves (stated). Herbrand's quotient theorem and
     the subgroup formula are statable for finite Galois towers but not stated here.
   - Not statable today: local reciprocity with upper numbering (D3); conductors of ℓ-adic
     representations (D4); Raynaud's criterion, unipotence of inertia under semistable reduction,
     and Néron–Ogg–Shafarevich (D2, D4); Carayol's Théorème A (D5).

   The obstacle is the one wk-h §3 named: Mathlib has no ℓ-adic Galois representations of
   abelian varieties or modular forms, no Artin conductor and no upper numbering on `G_{ℚ_p}`.
5. **No error found in N5 L796-857** (VERIFIED as reasoning, on top of rv-h-novel §§5-8). There
   are two precision points and one simplification (§4):
   - The hypothesis of the D2 lemma must bear on the *values* of `β`, because a pro-`p` group
     has elements of infinite order.
   - At `p = 2` the field in the `β` argument is `F = L_v`, so `e ≤ D`; this is rv-h-novel's R2.
   - Given A6, Raynaud's criterion is needed only at `p = 3`.

## 1. Notation (N5 L385-400, L651-716)

- `a := D·G₀`, `U₀ := 4a²`, `E₀ := 10a²` (`heightE0 = 10(heightD·heightG0)²`).
- `T := S ∪ supp M`, where `M = M_S(u)` (`contactSupport S u`), and `R ≥ max(D, max S, 10¹²)`
  is real. Also `Q_R := R^{R·E₀}` (`heightQ R`, a real power).
- `L/ℚ` is Galois, `[L:ℚ] ≤ D`, and `L` is unramified outside `T`. `A/K ⊂ L` is the QM surface,
  with good reduction at every place `v ∤ 3` (A6).
- `β: G_ℚ → μ_{2m}` is the cochain of B3. `β|_{G_L}` is a character, and `β² = χ` on `G_L`,
  where `χ` is tame at odd `p` and its 2-part has conductor dividing 4.
- `ρ_ℓ(σ) = β(σ)⁻¹ a_σ μ_σ ∘ σ ≅ r_ℓ ⊕ r_ℓ`, where `dim r_ℓ = 2`, `r₅` is used at `p ≠ 5`,
  and `r₃` at `p = 5`.

Lower ramification data of a finite Galois extension at one prime: `g_i = |G_i|`, with
`g_0 = e`, `g` antitone, and `g_i = 1` for large `i`. Herbrand's function at an integer is
`φ(m) = Σ_{i=1}^m g_i/g_0`, and `G^u = G_i` for `φ(i−1) < u ≤ φ(i)` (Serre, *Corps locaux*,
IV §3). The last upper break is `φ(b)`, where `b` is the largest `i` with `G_i ≠ 1`.

## 2. The steps as lemmas

Each step lists its statement, its literature inputs (leaves, with package), its glue, and its
Lean status. Lean names refer to `scratch/glue-conductor/{Breaks,Level,Dyadic}.lean`, namespace
`GlueConductor`.

### D1. Break bound (N5 L796-812)

**Lemma D1.** Let `F/ℚ_p` be finite of degree `≤ a`, and let `F̃` be its Galois closure. Then
`G_{ℚ_p}^u ⊆ G_{F̃}` for every `u > 4a²`.

Proof skeleton and inputs:
- (a) `[F̃:ℚ_p] ≤ a!`, so `e(F̃/ℚ_p) ≤ a!`. Galois theory (the Galois group embeds in `S_a`).
  Glue: provable over Mathlib, not done.
- (b) `δ := v_P(𝔇_{F̃/ℚ_p}) ≤ e − 1 + e·v_p(e)`.
  - Leaf **L1**: Serre, *Corps locaux* III §6, the remark after Prop. 13 (UNVERIFIED numbering),
    `v_L(𝔇) ≤ e − 1 + v_L(e)` (I6).
  - N5's one-line proof is Serre's argument (distinct valuations of the terms of `f'(π)`).
  - VERIFIED numerically on 15 fields, sharp for `ℚ(ζ₃, 3^{1/3})` and `ℚ(ζ₅, 5^{1/5})`
    (`c3_breaks.py`, rerun: `scratch/glue-conductor/c3_breaks.out`, "ALL OK: True").
- (c) `δ = Σ_{i≥0}(|G_i| − 1)`. Leaf **L2**: Hilbert's formula, Serre IV §1 Prop. 4
  (UNVERIFIED numbering) (I6).
- (d) `δ/e = 1 − 1/e + ∫₀^∞(1 − |G^u|⁻¹)du`, `u_last ≤ 2δ/e`, and
  `2δ/e ≤ 2(1 + log₂ a!) ≤ 4a²`. Glue, **proved**:
  - `herbrand_integral` (step-function form: `δ_{n+1}/e = 1 − 1/e + Σ_{i=1}^n (φ(i) − φ(i−1))(1 − 1/g_i)`);
  - `phi_le_two_delta` (`g_i ≥ 2` for `i ≤ b` ⇒ `φ(b) ≤ 2δ/e`);
  - `two_delta_le` (`δ ≤ e−1+e·v_p(e)`, `e ≤ a!`, `a ≥ 1` ⇒ `2δ ≤ 2(1 + ⌊log₂ a!⌋)e ≤ 4a²e`);
  - combined: `upper_break_le` (`φ(b) ≤ 4a²`).
- (e) The relative break bound becomes absolute: the image of `G_{ℚ_p}^u` in `Gal(F̃/ℚ_p)` is
  `Gal(F̃/ℚ_p)^u`, which is trivial for `u > u_last`. Leaf **L3**: Herbrand's theorem, Serre IV §3
  Prop. 14 (UNVERIFIED numbering) (I6).

Over genuine definitions: **`D1_genuine` (VERIFIED)** proves (b)-(d) for a Galois number field
`L/ℚ` and a prime `P | p` of `𝓞 L` from `HilbertDifferentFormula` (L2) and
`SerreDifferentBound` (L1), both stated over Mathlib's `differentIdeal ℤ (𝓞 L)`. Its
hypotheses are `e ≤ a!` and `G_b ≠ ⊥`, and its conclusion is `φ(b) ≤ 4a²`. The global groups
`(P^{i+1}).inertia Gal(L/ℚ)` equal the local `G_i` of the completion, and the local different
exponent equals `v_P(differentIdeal)` (Serre I §7, III §4, IV §1; UNVERIFIED numbering). So the
two leaves are consequences of the published local statements.

### D2. Semistability and wild inertia at odd `p` (N5 L813-823)

**Lemma D2.** Let `p ≤ R`, `v | p` a place of `L`, `n = 3` (`n = 5` if `p = 3`),
`F = L_v(A[n])`. Then:
- (i) `[F:ℚ_p] ≤ D·G₀ = a`;
- (ii) `A_F` has semistable reduction, and `P_F` (wild inertia) acts trivially on `V_ℓ(A)` for
  `ℓ ≠ p`;
- (iii) for `u > U₀`, every `σ ∈ G_{ℚ_p}^u` lies in `P_F ∩ G_L` and acts trivially on `V_ℓ(A)`;
- (iv) for odd `p`, `β` is trivial on `P_F`.

Inputs:
- (i) `[L_v:ℚ_p] ≤ D`, and `Gal(L_v(A[n])/L_v) ↪ GL₄(𝔽_n)`. Glue: **proved** `card_GL4_F5`
  (`|GL₄(𝔽₅)| = 116064000000 = G₀`) and `card_GL4_F3` (`24261120`), from Mathlib's
  `Matrix.card_GL_field`.
- (ii) Leaf **L4**: Raynaud's criterion (Silverberg–Zarhin, Ann. Inst. Fourier 45 (1995),
  Thm 3.5; ASTRA-READ in h-trust). Leaf **L5**: semistable reduction implies that inertia acts
  unipotently on `V_ℓ`, so the pro-`p` group `P_F` acts through a finite unipotent group, which
  is trivial (SGA 7 I, Exp. IX, §3; UNVERIFIED numbering). Both are I2.
- (iii) Glue: D1 with this `a`, together with "`G_{ℚ_p}^u ⊂ P` for `u > 0`" (the definition of
  upper numbering) and `G_F ⊂ G_L`.
- (iv) Glue, **proved** `char_trivial_of_odd_pgroup`. Its input is that the values of `β` have
  `p`-power order, because `β|_{P_F}` is continuous into the finite group `μ_{2m}` and so its
  image is a finite `p`-group; `pow_card_eq_one_of_pgroup` supplies this on a finite quotient.
  It also uses `β² = χ = 1` on `P_F`, since `χ` is tame.

### D3. The `p = 2` paragraph (N5 L823-844)

**Lemma D3.** Let `p = 2`, `F = L_v`, `e = e(F/ℚ₂) ≤ D`. Then `β|_{G_F}` is trivial on
`G_F^w` for `w > 3e`, and `β` is trivial on `G_{ℚ₂}^u` for `u > max(4D², 3e)`, which is
`≤ U₀`.

Inputs:
- `β⁴ = 1` on `U_F`. Glue: the 2-part of `χ` has conductor dividing 4, and the odd parts of
  `χ` are unramified at 2.
- `U_F^{3e+1} ⊆ (U_F^{e+1})⁴`. **Proved** `exists_fourth_root` (with the converse
  `fourth_pow_mem`) for any complete local ring with `(2) = 𝔪^e`. This replaces Silverman
  AEC IV.6.4.
- From "trivial on `U_F^{3e+1}`" to "trivial on `G_F^w` for `w > 3e`". Leaf **L6**: local class
  field theory with upper numbering, `ω_F(U_F^n) = G_F^n·[G_F,G_F]/[G_F,G_F]` for integers `n`,
  with integral upper breaks (Hasse–Arf) for real `w` (Serre, *Corps locaux* XV §2,
  UNVERIFIED numbering) (I6).
- `u_last(F/ℚ₂) ≤ 4D²`. D1 with `a = D` (`F/ℚ₂` is Galois because `L/ℚ` is).
- The subgroup formula `G_{ℚ₂}^u ∩ G_F = G_F^{ψ_{F/ℚ₂}(u)}`. Leaf **L7**: Serre IV §1 Prop. 2
  and IV §3 Prop. 15 (UNVERIFIED numbering), which needs `F/ℚ₂` Galois (I6). Glue, **proved**:
  `ψ(u) ≥ u` via `phi_le_self` (`φ(m) ≤ m`).
- `max(4D², 3e) ≤ U₀`. **Proved** `max_le_U0`.

### D4. Conductor exponents (N5 L845-852)

**Lemma D4.** For `ℓ ∈ {3,5}` with `p ≠ ℓ`, the Artin conductor exponent of `r_ℓ` at `p` is:
- (i) `≤ 2 + 2U₀ ≤ E₀` if `p ≤ R`;
- (ii) `≤ 2` if `R < p ∈ T`;
- (iii) `0` if `p ∉ T`.

Inputs:
- Leaf **L8**: the conductor of an ℓ-adic representation of `G_{ℚ_p}`, `ℓ ≠ p`, is
  `a = codim V^{I} + Sw`, with `Sw = ∫₀^∞ codim V^{G^u} du`, where wild inertia acts through a
  finite quotient (Serre, *Corps locaux* VI §2; Serre–Tate 1968 §2; UNVERIFIED numbering)
  (I6/I4). For a Weil–Deligne representation, the tame term `dim V − dim V^{I}_{N=0}` is still
  `≤ dim r = 2`.
- (i) `ρ_ℓ` is trivial on `G^u` for `u > U₀` (D2(iii) and (iv), D3). Glue, **proved**:
  - `swan_le` (`c_i ≤ 2` and `c_i = 0` when `φ(i) > U` ⇒ `Sw ≤ 2U`);
  - `artin_le` (`a ≤ 2 + 2U`);
  - `two_add_two_U0_le_E0` (`2 + 8a² ≤ 10a²`).
- (ii) `[L_v:ℚ_p] ≤ D < p`, so `L_v/ℚ_p` is tame and `P_{ℚ_p} ⊂ G_{L_v}`. By A6 and leaf
  **L9** (Néron–Ogg–Shafarevich, Serre–Tate 1968 Thm 1; I2), `V_ℓ(A)` is unramified over `L_v`.
  `β` is trivial on `P` by D2(iv). So `Sw = 0`. Glue, **proved**:
  - `wild_trivial_of_tame` (`p^k ∣ e < p` ⇒ `p^k = 1`, so `G_1 = 1`);
  - `swan_eq_zero_of_tame`.
- (iii) `L` is unramified at `p`, `A` has good reduction (A6, since `3 ∈ S ⊂ T`), and `β` is
  unramified (B3). By L9, `r_ℓ` is unramified at `p`.

### D5. From conductor to level (N5 L852-857)

**Lemma D5.** If `f` is the newform with `r₅ ≅ ρ_{f,λ}^∨`, `λ | 5`, and `r₃ ≅ ρ_{f,λ'}^∨`,
`λ' | 3`, then `v_p(N_f) = a_p(r₅)` for `p ≠ 5` and `v_5(N_f) = a_5(r₃)`. Hence
`N_f ≤ Q_R·M²`.

Inputs:
- Leaf **L10**: Carayol 1986, Théorème (A), at `F = ℚ`, weight 2 (I4). Duality preserves the
  conductor.
- The product, glue, **proved over the repository's definitions**: `level_le`. Its hypotheses
  are:
  - `R ≥ 1` real and `max S ≤ R`;
  - `v_p(N) ≤ E₀` at `p ≤ R`;
  - `v_p(N) ≤ 2` at `p > R`;
  - `p | N ⇒ p ∈ S ∨ p | contactSupport S u`.

  Its conclusion is `(N:ℝ) ≤ heightQ R · (contactSupport S u)²`. The large primes divide `M`,
  which is a product of distinct primes (`Finset.prod_primes_dvd`), and the small part is at
  most `R^{#{p ≤ R}·E₀} ≤ R^{R E₀}` (`prod_small_le`).

## 3. Leaves of the cluster

| Leaf | Statement used | Source (numbering UNVERIFIED unless noted) | Package | Statable in Mathlib v4.35 over genuine definitions? |
| --- | --- | --- | --- | --- |
| L1 | `v_P(𝔇) ≤ e − 1 + e·v_p(e)` | Serre CL III §6, remark after Prop. 13 | I6 | **yes, stated**: `SerreDifferentBound` |
| L2 | `v_P(𝔇) = Σ_{i≥0}(|G_i|−1)`, `G_i = 1` for large `i` | Serre CL IV §1 Prop. 4 | I6 | **yes, stated**: `HilbertDifferentFormula` |
| L3 | upper numbering passes to quotients | Serre CL IV §3 Prop. 14 (Herbrand) | I6 | yes for finite Galois towers (needs `G^u` for real `u`, defined from `ramGroup` and `φ`); the absolute form needs an upper filtration on `G_{ℚ_p}` (absent) |
| L4 | Raynaud: `A[n]` rational, `n ≥ 3`, `p ∤ n` ⇒ semistable | Silverberg–Zarhin 1995 Thm 3.5 (ASTRA-READ) | I2 | no (Néron models, abelian varieties over local fields) |
| L5 | semistable ⇒ inertia unipotent on `V_ℓ` | SGA 7 I Exp. IX §3 | I2 | no (Tate modules) |
| L6 | local reciprocity sends `U^n` onto `G^n_{ab}`; Hasse–Arf | Serre CL XV §2 | I6 | no (no local Artin map) |
| L7 | `G^u ∩ H = H^{ψ_{K'/K}(u)}` | Serre CL IV §1 Prop. 2, IV §3 Prop. 15 | I6 | as L3 |
| L8 | `a = codim V^I + ∫₀^∞ codim V^{G^u}du` for ℓ-adic `V` | Serre CL VI §2; Serre–Tate 1968 §2 | I6/I4 | no (no ℓ-adic Galois representations, no conductor) |
| L9 | Néron–Ogg–Shafarevich | Serre–Tate 1968 Thm 1 | I2 | no |
| L10 | `v_p(N_f) = a_p(ρ_{f,λ})`, `p ≠ ℓ` | Carayol 1986 Thm (A) (h-trust D5: coverage at all `p ≠ ℓ` "to check") | I4 | no (no newforms or their Galois representations) |

Removed from the leaf list by Lean proofs: Silverman AEC IV.6.4 (`exists_fourth_root`), and
the arithmetic of D1, D4 and D5. Easy remaining Lean work (glue, SPECULATIVE effort: days):
- (a) of D1 over Mathlib;
- stating L3 and L7 for finite towers with real-indexed `G^u`;
- deriving `|G_1|` a `p`-group from the genuine definitions.

Prerequisite survey (`prereq-survey.md`, row D1/D3/D4) reports that Tau Ceti has upper
ramification groups, Herbrand's theorem, `ψ`, Artin conductor exponents and Hilbert's formula.
That was not checked here, since Tau Ceti is not in this worktree. If it holds, L2 and L3 become
theorems there, and only L1 would remain on the local-field side.

## 4. Findings

1. **No error in N5 L796-857** (VERIFIED as reasoning). This agrees with rv-h-novel §§5-8.
2. **D2's last sentence needs its hypothesis on the image** (VERIFIED in Lean). "A pro-`p`
   group has no quotient of order two" is right. A formal version that assumes every *element*
   has `p`-power order is false for pro-`p` groups (`ℤ_p`). The correct input is that `β` is
   continuous into the finite group `μ_{2m}`, so its image is a finite `p`-group
   (`char_trivial_of_odd_pgroup`, restated in log Step 4).
3. **At `p = 2` the field is `L_v`.** The `β`-argument uses `F = L_v`, so `e ≤ [L:ℚ] ≤ D`
   (rv-h-novel R2). `L_v(A[3])` has `e ≤ DG₀`, and with that field `3e ≤ U₀` would still hold,
   but `F/ℚ₂` would not be known to be Galois as L7 requires.
4. **Raynaud is needed only at `p = 3`** (SPECULATIVE simplification, VERIFIED as reasoning
   given A6). A6 gives good reduction of `A` at every place `v ∤ 3` of `K`. So at `p ≤ R`,
   `p ≠ 3`, inertia of `L_v` already acts trivially on `V_ℓ(A)` (L9), with `F = L_v` and
   `a = D`. N5's Raynaud route does not depend on A6 at `p ≤ R`. Since A6 is used anyway at
   `p > R`, either route leaves the trust base as it is. Keep N5's route unless L4 proves hard
   to formalize.
5. **The constants have slack.** `2δ/e ≤ 2(1 + v_p(e))` with `v_p(e) ≤ log₂ a! ≤ a²`, against
   N5's `4a²`. None of this is needed.

## 5. What compiles (VERIFIED, `lake env lean`, 2026-11-11, one file at a time)

| File | Imports | Main theorems | `sorry` |
| --- | --- | --- | --- |
| `scratch/glue-conductor/Breaks.lean` | Mathlib | `herbrand_integral`, `phi_le_self`, `phi_le_two_delta`, `two_delta_le`, `upper_break_le`, `swan_le`, `artin_le`, `wild_trivial_of_tame`, `swan_eq_zero_of_tame`, `char_trivial_of_odd_pgroup`, `card_GL4_F5`, `card_GL4_F3`, `max_le_U0`, `two_add_two_U0_le_E0`, `D1_genuine` (from leaves `HilbertDifferentFormula`, `SerreDifferentBound`) | none |
| `scratch/glue-conductor/Level.lean` | `ZInQKernel.Hypotheses.Height` | `level_le`, `prod_small_le`, `contactSupport_pos'` | none |
| `scratch/glue-conductor/Dyadic.lean` | Mathlib | `exists_sq_eq_one_add`, `exists_fourth_root`, `fourth_pow_mem` | none |

`#print axioms` (`upper_break_le`, `D1_genuine`, `card_GL4_F5`, `level_le`,
`exists_fourth_root`, `fourth_pow_mem`) gives `propext`, `Classical.choice` and `Quot.sound`.

## 6. Biggest obstacle

D2-D5 are statements about ℓ-adic representations of `G_{ℚ_p}` attached to an abelian surface
and to a newform: their semistability, their conductors and Carayol's comparison. Mathlib
v4.35 cannot state any of these. Once Tate modules with Galois action and the Artin conductor
of a finite-image wild part exist, the glue is what is proved here, plus D1(e) and L7 for the
absolute Galois group.
