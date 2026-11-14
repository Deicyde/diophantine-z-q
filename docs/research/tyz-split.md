# tyz-split: the TYZ-side GLUE rows T-11 and T-5 split into published forms

Task tyz-split, 2026-11-14. Branch `wip/tyz-split` (base f70ec251). Lean: `scratch/tyz-split/T11.lean`
(row T-11) and `scratch/tyz-split/T5.lean` (row T-5), both importing built kernel modules. Results
log: `scratch/tyz-split/log.md`. Compiler output: `scratch/tyz-split/T11.out`, `T5.out`.
Marks: **VERIFIED** (compiled, or read in a named source at a line number), **STANDARD** (published,
exact reference), **SPECULATIVE**, **UNVERIFIED** (theorem numbers from memory; this host has no network).
TYZ = Tian–Yuan–Zhang, arXiv:1411.4728v1 (Asian J. Math. 21 (2017) 721–774); `Lnnnn` are line numbers of
`~/tyz-src/Period7.tex`, **read for this task** (only a few words are quoted below). Model work; no human review.

## 0. Main result

1. **T-11 is done.** `TYZ35.TYZThm33Pinned ℓ` (for every `ℓ` with `IsTYZLcal ℓ`) is now a Lean theorem
   from one leaf, `TYZSplit.TYZThm33`: TYZ Theorem 3.3 (L1299–1311) in its printed form over the
   kernel's definitions, restricted to `n ≡ 5, 7 (mod 8)` (VERIFIED compiled, axioms
   `[propext, Classical.choice, Quot.sound]`):

   ```lean
   theorem ZInQ.Contrib.TYZGenus.TYZSplit.tyzThm33Pinned_of_tyzThm33
       (h : TYZThm33) (ℓ : ℕ → ℤ) (hℓ : IsTYZLcal ℓ) : TYZ35.TYZThm33Pinned ℓ
   theorem ZInQ.Contrib.TYZGenus.TYZSplit.tyzThm35ReadingA_of_printedThm33
       (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
       (hS : Shimura.ShimuraReciprocityModFn) (h33 : TYZThm33) : ZInQ.Literature.TYZThm35ReadingA
   ```

   What used to be glue inside the row is now proved: the genus character `χ_T` used by the row
   (`gchar`, built from `(N𝔞/q)`) is TYZ's `χ_{d₀,d₁}`, the character of `Gal(H_n/K_n)` on `√d₁`
   (resp. `√d₁*`) (`isChiPair_pairSet`); the "excluded" characters (`n ≡ 5`, `d₁ ≡ 5, 7`) are none of the
   `χ_{d₀,d₁}` (`not_isChiPair_excluded`); `h₂(n) = dim_{𝔽₂} Cl_n/2Cl_n = #ramSet − 1` (`h2G_eq`); TYZ's
   sum over `Φ ⊂ Cl'_n` is the row's sum over a lift family (`pchiG_chiT`). Reading the source settled
   tyz-35's three HUMAN CHECK items: TYZ fix an **arbitrary** `Φ` (L1279), so the row's `∀ f` needs no
   "independent of the lifts" argument; the convention `K_n(√d₁)` / `K_n(√d₁*)` is printed (L1304–1305);
   `h₂ = dim_{𝔽₂} Cl_n/2Cl_n` is printed (L992). Lemma 3.14 is not a separate leaf: its conclusion is
   the first sentence of the printed Theorem 3.3, which TYZ derive from it (L1913), and its hypotheses
   (root numbers of `L(A_{K_n}, χ, s)`, the 2-component of a Hecke character) have no Lean definition.

2. **T-5 is not done; it is split into its CM part and its modular-curve part.** No printed form of
   Shimura's reciprocity law (Shimura 1971 Thm 5.4 or Thm 6.31, Gross 1984 §3) can be stated over
   current Lean definitions (§3.1). `scratch/tyz-split/T5.lean` proves (VERIFIED compiled, standard axioms)

   ```lean
   theorem ZInQ.Contrib.TYZGenus.TYZSplitT5.shimuraReciprocityModFn_of_split
       (hCM : CMModuli) (hX : X0RatStructure) : Shimura.ShimuraReciprocityModFn
   ```

   where `CMModuli` is the row for finitely many explicit functions per level (`j` and the symmetric
   functions of Weber values on the level structure, over Mathlib's `PeriodPair.weierstrassP`, `g₂`,
   `g₃`): a consequence of Shimura Thm 5.4 (with torsion) by the lattice computation of shimura-modfn
   §1; and `X0RatStructure` contains no CM: on `Y₀(N)` the `ℚ`-structure of rational `q`-expansions is
   the moduli `ℚ`-structure (canonical model of `X₀(N)`). Both are GLUE in the strict count. This
   split avoids the obstruction that shimura-modfn found for the `(j, j_N)` plane model at singular
   points (`D = −28`): the Weber coordinates separate all points of `Y₀(N)`.

No row statement was changed; neither row is false, vacuous or stronger than its sources (T-11 now
follows in Lean from the printed theorem; T-5 by shimura-modfn's check and §3.3).

## 1. Table

| row | old form | new leaves (published form, source) | new glue | Lean name of the proof |
|---|---|---|---|---|
| T-11 `TYZ35.TYZThm33Pinned` (∀ ℓ, `IsTYZLcal ℓ` →) | composite: TYZ Thm 3.3 with Lemma 3.14 and pinned conventions (signs in `ε`, `P_χ` independent of the lifts, genus characters, `h₂`) | `TYZSplit.TYZThm33`: TYZ Theorem 3.3, Period7.tex L1299–1311, with the definitions of §3.1 (`Cl_n`, `Cl'_n`, `σ` L1263–1265; `Φ`, `P_χ` L1279–1284; `𝒫` L1288–1295; `h₂` L992), for `n ≡ 5, 7 (mod 8)`; `𝒫(d)` kept existential (its coefficient needs Néron–Tate regulators) | none (all proved: §2.3) | `TYZSplit.tyzThm33Pinned_of_tyzThm33`, `TYZSplit.thm33Pinned_of_tyzThm33`; headline form `TYZSplit.tyzThm35ReadingA_of_printedThm33` |
| T-5 `Shimura.ShimuraReciprocityModFn` | composite: Shimura 1971 Thm 5.4 with the canonical model of `X₀(N)` (shimura-modfn) | none statable in printed form (§3.1) | `TYZSplitT5.CMModuli` (consequence of Shimura Thm 5.4 with torsion; CM part); `TYZSplitT5.X0RatStructure` (composite: canonical model of `X₀(N)` + separation of points by Weber coordinates; no CM) | `TYZSplitT5.shimuraReciprocityModFn_of_split` |

Effect on the frontier count (r3, strict): T-11 GLUE → LEAF (published form, specialization to
`n ≡ 5, 7` with `𝒫` existential); T-5 one GLUE → two GLUE (CM part a consequence of one theorem, so a
leaf in the lenient count; modular-curve part a composite).

## 2. T-11

### 2.1 What the source says (VERIFIED, read in Period7.tex)

* §3.1 (L1171–1284): `A : 2y² = x³ + x ≅ (X₀(32), ∞)`; for `n ≡ 5`, `f_n = f₀ − f₀∘[i]`, for `n ≡ 7`,
  `f_n = i₀` (L1195–1198); embeddings of `K_n` in `M₂(ℚ)` (L1203–1205) whose fixed points are the
  roots of `[16(n+1), −8, 1]` (`n ≡ 5`) and `[(n+δ²)/4, δ, 1]` (`n ≡ 7`), i.e. the kernel's
  `CM.tyzZn`, `tyzZ7`; `z_n = f_n(P_n)`, `H'_n = H_n(z_n)` (L1245–1251); Prop. 3.2 (`CM point1`,
  L1253–1261: `Gal(H'_n/H_n) = ℤ/2` for `n ≡ 5`, `H'_n(√2)` the ring class field of conductor 4;
  `H'_n = H_n` for `n ≡ 7`); `Cl_n = Gal(H_n/K_n)`, `Cl'_n = Gal(H'_n/K'_n)`, `K'_n = K_n` for
  `n ≡ 5, 7`, `σ` the order-two element of `Gal(H'_n/H_n)` (L1263–1265); "Fix a set `Φ ⊂ Cl'_n` of
  representatives" (L1279), `P_χ := Σ_{t∈Φ} f_n(P_n)^t χ(t)` (L1283).
* `𝒫(n) := 2^{−1−ρ(n)} 𝓛(n) α_n ∈ A(K_n)^- ⊗ ℚ`, `α_n` a generator of the free part when `𝓛(n) ≠ 0`,
  `𝒫(n) = 0` if `𝓛(n) = 0` (L1288–1295); `𝓛(n)` (L336–345) for `n ≡ 5, 6, 7` involves `L′(E_n, 1)` and
  the regulator `R_n` (twice a Néron–Tate height, L352); `𝓛` is defined up to sign (L364).
* **Theorem 3.3** (`GZ`, L1299–1311): `P_χ` is non-torsion only if `χ = χ_{d₀,d₁}`, `n = d₀d₁`,
  `0 < d₀ ≡ 5, 6, 7`, `0 < d₁ ≡ 1, 2, 3 (mod 8)`, the character of `K_n(√d₁)` (`n ≡ 5, 6`) or `K_n(√d₁*)`
  (`n ≡ 7`); then `P_χ = ε(d₀,d₁) 2^{h₂(n)} 𝓛(d₁) 𝒫(d₀)` in `A(H'_n(i)) ⊗ ℚ`, `ε = ±i` on `(5,3)`,
  `±1` otherwise. `h₂(n) = dim_{𝔽₂} Cl_n/2Cl_n` (L992).
* Lemma 3.14 (`char'`, L1868–1877): a character with root number `−1` and trivial 2-component (when
  2 is not split) is a `χ_{d₀,d₁}`. The proof of Theorem 3.3 uses it for the first sentence (L1913).

### 2.2 The leaf (Lean, `T11.lean` §1–§2)

Definitions (all over kernel objects): `ClG n = Gal(H_n/K_n)` (Tau Ceti's ring class field of the
maximal order); `Restricts n ρ t` (`ρ ∈ Gal(ℚ̄/ℚ)` restricts to `t` on `H_n ⊂ ℚ̄`); `IsPhi n φ`
(`φ t` restricts to `t`); `PchiG n φ χ = Σ_t χ(t)·φ(t)(z_n)`, `z_n = TYZ35.basePt n`;
`IsExtChar n e χ` (every lift of `t` multiplies the square roots of `e` by `χ(t)`), `IsChiPair n d₁ χ =
IsExtChar n (radTYZ n d₁) χ` with `radTYZ` = `d₁` (`n ≡ 5`), `d₁*` (`n ≡ 7`); `h2G n = log₂ [Cl_n : 2Cl_n]`;
`EpsTYZ ε` (the printed classes, on contributing pairs); `InMinus d P` (`P ∈ A(K_d)^-`). Then

```lean
def TYZThm33 : Prop :=
  ∀ ℓ : ℕ → ℤ, (∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ((ℓ m : ℂ)) ^ 2 = lcalSq m) →
  ∃ (Q : ℕ → PtA) (m : ℕ → ℕ) (ε : ℕ → ℕ → GaussianInt),
    (∀ d, 0 < m d) ∧ (∀ d, InMinus d (Q d)) ∧ EpsTYZ ε ∧
    (∀ d : ℕ, Squarefree d → (d % 8 = 5 ∨ d % 8 = 6 ∨ d % 8 = 7) →
      (¬ ∃ F : ℂ → ℂ, IsLContinuation (curveC d) F ∧ analyticOrderAt F 1 ≤ 1) →
        IsOfFinAddOrder (Q d)) ∧
    ∀ n : ℕ, ∀ _ : NeZero n, Squarefree n → (n % 8 = 5 ∨ n % 8 = 7) →
      ∀ φ : ClG n → GalQ, IsPhi n φ → ∀ χ : ClG n →* ℤˣ,
        (¬ IsOfFinAddOrder (PchiG n φ χ) →
          ∃ d₀ d₁ : ℕ, d₀ * d₁ = n ∧ (d₀ % 8 = 5 ∨ d₀ % 8 = 6 ∨ d₀ % 8 = 7) ∧
            (d₁ % 8 = 1 ∨ d₁ % 8 = 2 ∨ d₁ % 8 = 3) ∧ IsChiPair n d₁ χ) ∧
        ∀ d₀ d₁ : ℕ, d₀ * d₁ = n → (d₀ % 8 = 5 ∨ d₀ % 8 = 6 ∨ d₀ % 8 = 7) →
          (d₁ % 8 = 1 ∨ d₁ % 8 = 2 ∨ d₁ % 8 = 3) → IsChiPair n d₁ χ →
          IsOfFinAddOrder ((m d₀ : GaussianInt) • PchiG n φ χ -
            (ε d₀ d₁ * 2 ^ h2G n * (ℓ d₁ : GaussianInt)) • Q d₀)
```

**Why it is the printed theorem or weaker (never stronger).**
* `A(H'_n(i)) ⊗ ℚ ⊂ A(ℚ̄) ⊗ ℚ` (injective); a vector is `Q/m`; equality = the cleared difference is
  torsion. The kernel's `A : y² = x³ + 4x` is `ℚ`-isomorphic to TYZ's `2y² = x³ + x` by `(x,y) ↦ (2x,4y)`,
  compatibly with `[i]`.
* `𝒫(d)` enters only as `Q d / m d` with `Q d ∈ A(K_d)^-` and `Q d` torsion when `ord_{s=1} L(E_d,s) > 1`
  (then `𝓛(d) = 0` by definition, L345, so `𝒫(d) = 0`, L1295); the value `2^{−1−ρ(d)}𝓛(d)` of the
  coefficient is forgotten. This weakens the printed theorem. (`m d = 2^{1+ρ(d)}·den`, `Q d = num·α_d`
  realize it, since TYZ prove `𝓛(d) ∈ ℚ`, L2017–2019.)
* `ℓ` ranges over integer sign choices of `𝓛` on `d₁ ≡ 1, 3` (`ℓ² = 𝓛²`); since `ε` is chosen after
  `ℓ`, a sign change of `ℓ(d₁)` is absorbed by `ε(d₀,d₁) ↦ −ε(d₀,d₁)`, which stays in its class.
* `n ≡ 5, 7` only (fewer cases); then `d₀, d₁` are odd, so the classes `6`, `2` are vacuous.
* `Φ` ↔ lift families: given `φ`, `{φ(t)|_{H'_n}}` is a set of representatives of `Cl'_n/⟨σ⟩` because
  `H'_n/K_n` is abelian (Prop. 3.2: `H'_n ⊆` the ring class field of conductor 4) and `⟨σ⟩ = Gal(H'_n/H_n)`
  is the kernel of `Cl'_n → Cl_n`; conversely every `Φ` lifts. `z_n^t` only depends on `t|_{H'_n}`,
  since `z_n ∈ A(H'_n)` by the definition of `H'_n`. So `∀ φ` is TYZ's `∀ Φ`.
* `χ` is a character of `Cl_n = Gal(H_n/K_n)` itself, and `χ_{d₀,d₁}` is defined by its action on
  `√d₁` resp. `√d₁*` (if the square root were not in `H_n` no `χ` would qualify, which would only
  weaken the leaf; it is in `H_n`, `sqrt_pstar_mem'`).

**Remaining HUMAN CHECK (inherited, not new).** The leaf uses the kernel's pinned `z_n` (`basePt`):
for `n ≡ 5`, `(1 − [i]) f₀(P_n)`. TYZ's `f_n = f₀ − f₀∘[i]` with `[i]` an automorphism of
`X_U ≅ X₀(32)_{ℚ(i)}`; on `ℂ`-points `f₀∘[i] = [±i]∘f₀` depending on the component of `X_U` that
carries `P_n = [h, 1]`. The sign was pinned numerically by cm-numeric / tyz-t1 (Theorem 3.3 checked
on 73 contributing pairs and 102 excluded characters) and is coupled to the `K_n(√d₁)` convention
(tyz-35 §2.4(b)); it is not derived from the text here.

### 2.3 The glue (all proved, `T11.lean` §3–§4)

| step | Lean | content |
|---|---|---|
| characters as homs | `sgnU`, `gcharHom`, `chiT`, `coe_chiT` | `χ_T = Π_{q∈T} χ_q` as `Pic(𝒪_{K_n}) →* ℤˣ`, transported to `Cl_n` by the Artin isomorphism |
| lift families | `restricts_of_acts`, `acts_of_restricts`, `exists_restricts`, `isPhi_of_liftFamily`, `pchiG_chiT` | `IsLiftFamily f` gives `IsPhi (f ∘ Art⁻¹)` and `P_{χ_T} = Pchi f T` (reindexing by the Artin isomorphism) |
| `√q*` | `sqrt_pstar_mem'`, `restricts_sqrt_pstar` | `√q* ∈ H_n` and a lift of `t` acts on it by `χ_q(Art⁻¹ t)` (kernel: `T321.artinPstarChi_odd`, `T321.sqrt_pstar_mem`, `sqrtPstarInHilbert`) |
| `K_n(√e)` | `sqProd`, `restricts_sqProd`, `sqProd_sq`, `restricts_fix_sqrt_negn`, `isExtChar_chiT` | `χ_T` is the character of `K_n(√e)` when `e = Π_{q∈T} q*` or `e·Π q* = −n` (`√−n ∈ K_n` is fixed) |
| pairs | `prod_pstar_divSet`, `mod8_of_mul`, `isChiPair_pairSet` | `χ_{pairSet n d₀ d₁} = χ_{d₀,d₁}` for `d₁ ≡ 1, 3`, both classes of `n` |
| excluded characters | `isExtChar_unique`, `gchar_single`, `gchar_inj`, `divSet_inj`, `not_isChiPair_excluded` | for `n ≡ 5` the `2^k` characters `χ_T` are distinct (`exists_chi_eq`), so `χ_{pairSet}` with `d₁ ≡ 5, 7` is no `χ_{d₀',d₁'}` |
| `h₂` | `sqSub_comm`, `sqSub_map`, `h2G_eq` | `log₂ [Cl_n : 2Cl_n] = #ramSet n − 1` (kernel's `card_ker_sq_eq`, `Subgroup.index_range`) |
| row | `tyzThm33Pinned_of_tyzThm33` | the five conjuncts of `TYZThm33Pinned ℓ` from the leaf |

## 3. T-5

### 3.1 Printed forms and why none is a Lean leaf today

* Shimura, *Introduction to the arithmetic theory of automorphic functions* (1971), **Thm 5.4**
  (UNVERIFIED number; statement STANDARD): for `E ≅ ℂ/𝔞`, `𝔞` a lattice in `K`, `σ ∈ Aut(ℂ/K)` and an
  idele `s` of `K` with `σ = [s, K]` on `K^ab`, there is `ξ′ : ℂ/s⁻¹𝔞 ≅ E^σ` with `ξ(u)^σ = ξ′(s⁻¹u)` for
  `u ∈ K/𝔞`. Needs the idelic Artin map `[s, K]` on `K^ab` and the action of finite ideles on
  lattices of `K`. (Tau Ceti, vendored in the kernel, has a global class formation with an
  `absoluteArtinMap`, so `[s, K]` is definable in principle; relating it to `ringClassArtinEquiv` and
  to `Aut(ℂ/K)` was not attempted.)
* Shimura 1971, **Thm 6.31** (UNVERIFIED): `f(z)^{[s⁻¹,K]} = f^{τ(q_z(s))}(z)` for `f ∈ 𝔉` (modular
  functions of all levels with coefficients in `ℚ^ab`). Needs in addition Shimura's action
  `τ : GL₂(𝔸_f) → Aut(𝔉)`, whose existence is itself a theorem (Thm 6.23); nothing in Mathlib.
* Gross, *Heegner points on `X₀(N)`* (1984), §3 (UNVERIFIED): `Art(𝔟)(𝒪, 𝔫, [𝔞]) = (𝒪, 𝔫, [𝔞𝔟⁻¹])` on
  `X₀(N)(H)`. Needs `X₀(N)` as a curve over `ℚ`; and it assumes Gross's Heegner condition, while the
  row (and its uses: `[16(n+1), −8, 1]` has conductor 4 at level 32) does not.
* Cox, *Primes of the form x² + ny²*, Thm 11.1 / Cor. 11.37 (UNVERIFIED): the `j`-form only;
  shimura-modfn showed that the `j`-form cannot give the row at singular points of the `(j, j_N)` model.

So the row is a composite of a CM theorem and the canonical model of `X₀(N)`; the derivation
(shimura-modfn §1) is short on paper, but each input needs definitions that Lean does not have.

### 3.2 The split (Lean, `T5.lean`)

* `modCoord N τ i`: `i = 0`: `j(τ) = 1728 g₂³/Δ` of `ℂ/⟨1, τ⟩`; `1 ≤ i ≤ N − 1`: the `i`-th elementary
  symmetric function of the Weber values `h(k/N)`, `1 ≤ k ≤ N − 1` (`h = (g₂g₃/Δ)℘`, or `(g₂²/Δ)℘²` if
  `g₃ = 0`, `(g₃/Δ)℘³` if `g₂ = 0`; Shimura (4.1.3), UNVERIFIED number). Over Mathlib's `PeriodPair`.
* `CMModuli`: the row's data and hypotheses (any `N ≥ 1`), conclusion: the coordinates of `τ_Q` are
  algebraic and `ρ` maps them to those of `τ_{Q'}`.
* `X0RatStructure`: for `N ≥ 1`, `g` with `IsRatModFn N g`, and `τ, τ'` whose coordinates are
  algebraic and `ρ`-conjugate, `g(τ), g(τ')` are algebraic and `ρ`-conjugate.
* `shimuraReciprocityModFn_of_split` (three lines; `heegnerForm_level_pos` handles `N = 0`).

### 3.3 Why both parts are true, and what each needs (SPECULATIVE in detail, STANDARD in substance)

* `CMModuli`: Thm 5.4 gives `(E_L, C)^σ ≅ (E_{s⁻¹L}, s⁻¹C)` for `σ` extending `ρ`; shimura-modfn §1
  identifies `s⁻¹(L, L_N)` with `(L′, L′_N)` up to homothety; `j` and the multiset of Weber values of
  `C \ 0` are invariants of the isomorphism class of `(E, C)`, computed from any Weierstrass model, so
  `σ` acts on them by conjugation (the branch of `h` is the same at `τ_Q` and `τ_{Q′}`, since `j` is
  conjugated and `g₃ = 0 ⇔ j = 1728`, `g₂ = 0 ⇔ j = 0`). Needed in Lean: Thm 5.4 (or its Weber-function
  corollary) and the lattice computation; extension of `ρ ∈ Gal(ℚ̄/ℚ)` to `Aut(ℂ)`.
* `X0RatStructure`: the coordinates separate the points of `Y₀(N)(ℂ)` (`j` fixes `E`; `h(u) = h(u′)` iff
  `u′ ∈ Aut(E)u`; a generator of `C` meets the orbits of `C′ \ 0` only if `C′ ∈ Aut(E)·C`), and they are
  `ℚ`-rational on the moduli space; if the coordinates of `τ` are algebraic then `E` and `C` are defined
  over `ℚ̄`, `τ′` is the point `ρ(τ)`, and `g(ρ(τ)) = ρ(g(τ))` for `g` in the `ℚ`-structure of rational
  `q`-expansions, because that is the moduli `ℚ`-structure (canonical model: Shimura 1971 §6.7, Thm 6.23,
  Prop 6.9; Deligne–Rapoport; Diamond–Shurman Ch. 7; UNVERIFIED numbers). Needed in Lean: modular
  curves over `ℚ` and the `q`-expansion principle. No CM is involved.

Compared with shimura-modfn's split (`MainTheoremCMj ∧ RatX0Rep ∧ ShimuraReciprocityModFnSingular`),
nothing of the row survives as a "restriction of the original": the CM input is only about the
finitely many coordinate functions at each level, and the non-CM input holds at every point.

## 4. Compile status (VERIFIED)

* `lake build ZInQKernel.Contrib.TYZChain.Main` (10388 jobs, success; after copying tyz-chain's
  `Contrib` build directory).
* `lake env lean scratch/tyz-split/T11.lean`: 0 errors, no `sorry`; `#print axioms` of
  `tyzThm33Pinned_of_tyzThm33` and `tyzThm35ReadingA_of_printedThm33`: `[propext, Classical.choice,
  Quot.sound]` (`T11.out`).
* `lake env lean scratch/tyz-split/T5.lean`: 0 errors, no `sorry`; `shimuraReciprocityModFn_of_split`:
  `[propext, Classical.choice, Quot.sound]` (`T5.out`).

## 5. What remains

* T-11: the leaf `TYZThm33` (TYZ Theorem 3.3; its proof needs the explicit Gross–Zagier formula of
  Yuan–Zhang–Zhang, TYZ Thm A.9 L3062–3077, Néron–Tate heights and Kolyvagin, none in Lean); the
  inherited HUMAN CHECK on the `[i]`-sign of `z_n` (§2.2).
* T-5: `CMModuli` and `X0RatStructure` (GLUE). A printed-form CM leaf would need Shimura's Thm 5.4 in
  idelic form over Tau Ceti's `absoluteArtinMap`, plus the lattice computation, in Lean.
* Integration: `T11.lean` and `T5.lean` import kernel modules only (`TYZChain.Main`, `ShimuraModFn`);
  they can move to `ZInQKernel/Contrib/` unchanged up to the namespace.
