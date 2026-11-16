# gz-heegner: `GZHL3.HeegnerPointRational` from the main theorem of complex multiplication and the canonical model of `X₀(N)`

Status: research note (task gz-heegner, 2026-11-15), branch `wip/gz-heegner` (base c118e9d2, gz-hl3 on leaf-fold20).
Lean: `ZInQKernel/Contrib/OneProof/GrossZagierHeegner/Heegner.lean` (137 KB) and
`ZInQKernel/Contrib/OneProof/GrossZagierHeegner/HeegnerCd.lean`. Both are new files. Nothing else under `ZInQKernel/`
was edited. Development copies, checks and log: `scratch/gz-heegner/`.

Marks. **VERIFIED**: read in a source named here, computed, or compiled. **STANDARD**: a published theorem with an
exact reference. **SPECULATIVE**: an assessment. This host has no network and no copy of Shimura, Deligne–Rapoport
or Gross. **Every theorem number and locator of the literature below is UNVERIFIED** (from memory).

---

## 0. Main result

**`HeegnerPointRational` is proved in Lean from two printed leaves. No new open Prop is introduced.**

```lean
theorem ZInQ.GZHeegner.heegnerPointRational_of_printed
    (hCM : T5Glue.ShimuraMainCM) (hX : ZInQ.GZHeegner.X0ModuliGaloisMero) :
    ZInQ.GZHL3.HeegnerPointRational
```

* `#print axioms` gives `[propext, Classical.choice, Quot.sound]` (VERIFIED, `lake build` and `lake env lean`;
  `scratch/gz-heegner/Check.lean`, output `out_check.txt`).
* `T5Glue.ShimuraMainCM` is already the hypothesis `hCM` of `frozenTarget`.
* `X0ModuliGaloisMero` is the printed form of the kernel's `T5Glue.X0ModuliGalois` (hypothesis `hX`). It is the
  same canonical-model theorem, stated for every `g ∈ ℚ(X₀(N))` regular at the two points, not only for `g` regular
  on all of `ℍ`. The kernel's statement is a special case: `x0ModuliGalois_of_mero : X0ModuliGaloisMero →
  T5Glue.X0ModuliGalois` (VERIFIED, compiled). So a fold replaces `hX` by `X0ModuliGaloisMero` and adds nothing.

**Finding: `X0ModuliGalois` as stated cannot give the Heegner point (SPECULATIVE as an impossibility; the facts
behind it are STANDARD).** The kernel's `IsRatModFn N g` asks for a `q`-expansion valid on all of `ℍ`, so `g` is
holomorphic on `ℍ`.

* The coordinates `x∘φ`, `y∘φ` of a modular parametrization `φ` have poles at the non-cuspidal points of `φ⁻¹(O)`.
  These exist whenever `deg φ` exceeds the multiplicity of `O` at cusps, which is the typical case.
* Every nonconstant rational function on `E` has poles, and `φ(Y₀(N))` misses at most finitely many points of
  `E(ℂ)`. So no function pulled back from `E` is regular on `ℍ` in general.
* Building a regular-on-`ℍ` multiple of `x∘φ` needs the algebraic theory of `X₀(N)_ℚ`, which is itself canonical-model
  content.

The printed theorem (Shimura 1971 §6.7, Deligne–Rapoport VI–VII) covers every `g ∈ ℚ(X₀(N))` regular at the point,
which is exactly `X0ModuliGaloisMero`. The kernel's form was a weakening of the print, so the change makes the leaf
closer to the print, not stronger.

**Effect on the counts** (kinds.tsv convention: strict GLUE = kind not `published`):

* gz-hl3's split of `hL3` had three composites. `HeegnerPointRational` is now proved, so the composites drop to two
  (`StrongWeilCurve`, `IsogenyLattice`), alongside gz-hl3's three printed leaves.
* `hX` (kind consequence, GLUE) becomes `X0ModuliGaloisMero` (kind consequence, GLUE), so the strict count is unchanged
  there.
* Net against gz-hl3's split: **−1 strict and −1 strictest GLUE, no new leaf, no new glue.**
* Net against the current `frozenTarget`, where `hL3` is one composite: the combined split is +1 strict GLUE (2
  composites in place of 1), down from gz-hl3's +2. Making the whole `hL3` split net negative also needs the
  parametrization composites `StrongWeilCurve` / `IsogenyLattice`, or the `C_d` composite `ShimuraCMParamCd`, in
  printed form. That is outside this task (§6).

The `C_d` form is also proved: `heegnerPointRationalCd_of_printed` and `grossZagierHeegnerCd_of_printed` in
`HeegnerCd.lean` (VERIFIED, compiled).

---

## 1. The leaves

| Leaf | Statement | Source (UNVERIFIED locators) | Rating | Reason |
| --- | --- | --- | --- | --- |
| `T5Glue.ShimuraMainCM` (existing, `hCM`) | main theorem of CM with torsion, idelic form, Weierstrass coordinates | Shimura 1971 Thm 5.4; Lang, *Elliptic functions* Ch. 10 Thm 3 | **printed form** (as rated in kinds.tsv, statement review 2026-11-14) | unchanged; used through the kernel's proved `T5Glue.cmModuli_of_t5` |
| `ZInQ.GZHeegner.X0ModuliGaloisMero` (replaces `hX`) | for `g ∈ ℚ(X₀(N))` (`IsRatModFnMero`) regular at `τ` and `τ'` (`RegularAt`), algebraic moduli point `(E_τ, ⟨1/N⟩)`, `σ ∈ Aut(ℂ)` carrying it to `(E_{τ'}, ⟨k/N⟩)`: `σ(g(τ)) = g(τ')` | Shimura 1971 §6.7, Prop. 6.9, Thm 6.23; Deligne–Rapoport LNM 349 VI.6, VII; Diamond–Shurman §7.5–7.7 | **consequence, same kind as `hX`** | like `hX`, it glues the coarse moduli space over `ℚ`, the `q`-expansion principle and the analytic map `τ ↦ (ℂ/⟨1, τ⟩, ⟨1/N⟩)`. The only change from `hX` is the regularity hypothesis, which is now the printed one (regular at the point) |

The definitions behind the new leaf (`Heegner.lean` §2):

* **`IsRatModFnMero N g`** says `g : ℍ → ℂ` has four properties:
  - it is `Γ₀(N)`-invariant;
  - it is meromorphic at every point of `ℍ` (Mathlib `MeromorphicAt` of `g ∘ ofComplex`);
  - it has moderate growth at every cusp: `g(γτ) = O(e^{2πk Im τ})` as `Im τ → ∞`, for each `γ ∈ SL₂(ℤ)`;
  - it has a rational Laurent expansion `q^k g = Σ aₙ qⁿ`, `aₙ ∈ ℚ`, for `Im τ > T`.

  This is `ℚ(X₀(N))` as a set of functions on `ℍ`, with junk values at poles. It is the kernel's `IsRatModFn` with
  "the `q`-expansion holds on all of `ℍ`" replaced by "near `∞`" and "meromorphic". The growth clause is needed: without
  it, `exp(t)` for a Hauptmodul `t` would plausibly be a counterexample (SPECULATIVE example).
* **`RegularAt g τ`**: `AnalyticAt ℂ (g ∘ ofComplex) τ`. This includes the requirement that `g τ` is the value of the
  analytic function there.
* The moduli hypotheses (algebraic `modCoord`, `IsConjModel`, the `k/N` condition) are verbatim from `hX`.

**Not vacuous.** The proof applies the leaf only to `x∘φ`, `y∘φ` and `1/(x∘φ − t)`. All three are shown in Lean to
satisfy `IsRatModFnMero` (§3, `isRatModFnMero_coords` with the three `param*` theorems), and the regularity
hypotheses are discharged at the actual Heegner points. `x0ModuliGalois_of_mero` also shows that every `IsRatModFn`
function is `IsRatModFnMero` and regular everywhere (`regularAt_of_hasSum`: a `q`-expansion valid on `ℍ` has radius
of convergence `≥ 1`).

---

## 2. The proof (all VERIFIED, compiled; Lean names in `Heegner.lean`)

Fix the data of `HeegnerPointRationalAt E`:

* `E/ℚ` elliptic, and `f` a newform of level `N` and trivial character with `aₙ(f) = aₙ(E)`;
* an odd fundamental `D < −4` with the Heegner hypothesis, and `β`;
* a complete set `S` of Heegner representatives of residue `β`;
* the period lattice `L`, and `c ∈ ℚ^×` with `c Λ_f ⊆ L`;
* `K = ℚ(δ)`, `δ² = D`, with `ι(δ) = i√|D|`.

Write `D = −m`. Then `m ≡ 3 (mod 4)`, `m` is squarefree, and `D = discOf m 1`.

1. **Every `σ ∈ Aut(ℂ)` fixing `κ(ℚ(√−m))` permutes the points `φ(τ_Q)`, `Q ∈ S`** (`heegnerC_fixed`), where
   `φ(τ) = weierPt E L (c φ_f(τ))`.
   - Restriction gives `τ_σ ∈ Gal(Kˢ/K)` (kernel `exists_tau_of_sigma`) and `ρ ∈ Gal(ℚ̄/ℚ)` (`exists_galQ_of_sigma`).
   - `τ_σ|_H ∈ Gal(H/K)` is `Art([J])` for an ideal `J = ⟨a, (−b + √D)/2⟩` with `a` prime to `∏_{Q∈S} A_Q`
     (`heegnerClassJ`, Tau Ceti's Artin isomorphism and Chebotarev theorem).
   - For `Q ∈ S`, the Dirichlet composite `Q' = [aA, B', C']`, `B' ≡ B (2A)`, `B' ≡ −b (2a)`, keeps the residue `β`
     and satisfies `J·⟨1, τ_{Q'}⟩ = ⟨1, τ_Q⟩` and `J·⟨1/N, τ_{Q'}⟩ = ⟨1/N, τ_Q⟩` (`exists_compose`).
   - The kernel's `CMModuli`, proved from `ShimuraMainCM` (`T5Glue.cmModuli_of_t5`), gives algebraic moduli
     coordinates of `τ_Q` that `ρ` carries to those of `τ_{Q'}`. The kernel's `moduli_transport` turns this into the
     moduli hypotheses of `X0ModuliGaloisMero`.
   - `X0ModuliGaloisMero` applied to `x∘φ`, `y∘φ`, `1/(x∘φ − t)` gives `σ(φ(τ_Q)) = φ(τ_{Q'})` (`point_transport`).
     The case where one of the two points is `O` is excluded with `t ∈ {0, 1}`: `1/(x − t)` is `0` at `O` and nonzero
     at a finite point with `x ≠ t`.
   - `φ(τ_{Q'}) = φ(τ_R)` for the representative `R ∈ S` of `Q'`, by `c Λ_f ⊆ L` (`weierPt_smul`).
   - `Q ↦ R` is injective. Equivalent forms give homothetic lattice pairs (`pairHom_of_equiv`); multiplication by `J`
     preserves homothety; homothetic pairs come from equivalent forms (`equiv_of_pairHom`).
2. So `heegnerC = Σ_{Q∈S} φ(τ_Q)` is fixed by `Aut(ℂ/κK)`. Its coordinates lie in `κ(K)` (`mem_kappa_of_fixed`: the
   kernel's `fixedAlgebraic`, the extension `exists_ringEquiv_extend`, and Mathlib's
   `InfiniteGalois.mem_range_algebraMap_iff_fixed` for `Kˢ/K`). Transport along `θ : ℚ(√−m) → K` with `ι ∘ θ = κ`
   gives `y ∈ E(K)` with `ι(y) = heegnerC`.

### The analytic glue: the coordinates of `φ` lie in `ℚ(X₀(N))` (§8, §9)

| Prop (glue, all proved) | Content | Proof |
| --- | --- | --- |
| `ParamRegular` (`paramRegular`) | `x∘φ`, `y∘φ`, `1/(x∘φ − t)` are meromorphic on `ℍ`, and regular where expected | `φ_f = Σ aₙ/n qⁿ` has radius `≥ 1` (the `q`-expansion of `f` converges on `|q| < 1`); `℘`, `℘'` are meromorphic everywhere (`weierstrassPExcept`); `1/(℘ − c₀)` is analytic at lattice points with value `0` |
| `ParamCuspGrowth` (`paramCuspGrowth`) | growth at every cusp, one exponent per function | `D φ_f = f` by termwise differentiation (`hasDerivAt_pseries`); Mathlib's `normalizedDerivOfComplex_SL_slash` gives `D(φ_f ∘ γ) = f|₂γ`; `f|₂γ` is `N`-periodic (`γTᴺγ⁻¹ ∈ Γ(N) ⊆ Γ₁(N)`), holomorphic and zero at `∞`, so it has a `q_N`-expansion with no constant term; its termwise antiderivative `G` has `D G = f|₂γ`, so `φ_f(γτ) = K₀ + G(q_N)` (`exists_const_eichler`); then `x∘φ∘γ` is meromorphic in `q_N` at `0` (`growth_of_meromorphicAt`) |
| `ParamQExpansion` (`paramQExpansion`) | rational Laurent expansions at `∞` | see the list below |
| `HeegnerClassJ` (`heegnerClassJ`) | each ideal class of `ℚ(√−m)` contains `⟨a, (−b + √D)/2⟩` with `(a, M) = 1` | Chebotarev in the Hilbert class field (copy of `RingClassTwo.exists_prime_picClass_eq` for the maximal order); a split or ramified prime is `⟨p, θ − r⟩` by `ℤ + ℤθ` coordinates; an inert prime is principal, so its class is `1` and `J = 𝓞_K` |

The proof of `ParamQExpansion`:

- `φ_f = q V(q)` with `V(0) = a₁ = 1`.
- `Ŷ(w) = w²℘_{L−0}(cwV(w)) + (c²V(w)²)⁻¹ − bw²` is analytic at `0`, and `Ŷ(q) = q² x(φ)`.
- `Ŷ` satisfies `(wŶ' − 2Ŷ)² = (4(Ŷ + bw²)³ − g₂w⁴(Ŷ + bw²) − g₃w⁶)·Z'²` near `0`, from `℘'² = 4℘³ − g₂℘ − g₃` and
  the identity theorem.
- The Taylor series at `0` is a ring hom commuting with `d/dw` (`tay_mul` via the Leibniz rule
  `iteratedDeriv_mul`, and `tay_deriv`).
- The formal equation has a unique solution with constant term `1/c²` (`odePhi_unique`): the coefficient of the new
  term at order `n` is `−4(n + 1)/c²`.
- Every `σ ∈ Aut(ℂ)` maps solutions to solutions, since `b, g₂, g₃, c, aₙ ∈ ℚ`. So the Taylor coefficients are fixed by
  `Aut(ℂ)`, hence rational (`rat_of_fixed`).
- `y∘φ` and `1/(x∘φ − t)` follow by cancellation (`fixed_of_mul`). The convergence near `0` comes from Mathlib's
  `hasSum_taylorSeries_on_ball`.

### Other glue (proved)

* `exists_compose`. The sign `B' ≡ −b (mod 2a)` was checked with sympy before the proof: 401/401 cases hold, while the
  other sign holds in 116/401 (VERIFIED, `scratch/gz-heegner/py/compose.py`). The integer coordinates of the four
  products were computed with sympy (`py/coords.py`).
* `pairHom_of_equiv` and `equiv_of_pairHom`: `Γ₀(N)`-equivalence of Heegner forms is the same as homothety of the
  pairs `(⟨1, τ⟩, ⟨1/N, τ⟩)`. The sign of the determinant comes from `Im(conj(j)·jτ')`.
* `regularAt_of_hasSum`, `x0ModuliGalois_of_mero`.

---

## 3. Integration (contributor kit, `docs/one-proof/CONTRIBUTING.md`)

* **Files.**
  - `ZInQKernel/Contrib/OneProof/GrossZagierHeegner/Heegner.lean` imports `…OneProof.GrossZagierHeegner` (gz-hl3)
    and `…OneProof.RingClassLattice` (the module declaring `ShimuraMainCM` and `X0ModuliGalois`). It does not import
    `OneProof.Main`.
  - `ZInQKernel/Contrib/OneProof/GrossZagierHeegner/HeegnerCd.lean` imports gz-hl3's `Cd.lean` and `Heegner.lean`.
  - `scratch/gz-heegner/mk.py` regenerates `Heegner.lean` from the development file `scratch/gz-heegner/Heegner.lean`.
* **`#discharges`** (VERIFIED, `scratch/gz-heegner/Discharges.lean`, output `discharges-output.txt`):

  ```
  DISCHARGES [hL3] by ZInQ.GZHeegner.grossZagierHeegner_of_printed
    still assumes: [ZInQ.GZHL3.WeierstrassUniformization, ZInQ.GZHL3.StrongWeilCurve, ZInQ.GZHL3.IsogenyLattice,
   ZInQ.GZHL3.GrossZagierFormula, ZInQ.GZHL3.GrossConjugation, T5Glue.ShimuraMainCM, ZInQ.GZHeegner.X0ModuliGaloisMero]
    axioms: [propext, Classical.choice, Quot.sound]
  DISCHARGES [hX] by ZInQ.GZHeegner.x0ModuliGalois_of_mero
    still assumes: [ZInQ.GZHeegner.X0ModuliGaloisMero]
    axioms: [propext, Classical.choice, Quot.sound]
  #discharges: 65 open hypotheses, 1615 theorems checked, 8 discharge one
  ```
* **The `Main.lean` edit**, on top of gz-hl3's (`hL3` and `hX` are top-level hypotheses of `frozenTarget`, so autofold
  does not cover them):
  1. add `import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.Heegner`;
  2. replace the binder `(hX : T5Glue.X0ModuliGalois)` by `(hX : ZInQ.GZHeegner.X0ModuliGaloisMero)`, and every use
     of `hX` by `(ZInQ.GZHeegner.x0ModuliGalois_of_mero hX)`;
  3. replace the binder `hL3` by gz-hl3's leaves without `hHP`, and the argument `hL3` by
     `(ZInQ.GZHeegner.grossZagierHeegner_of_printed hU hSW hI hGZ hGC hCM hX)`.
* **kinds.tsv.**
  - The `hX` row gets the new constant `ZInQ.GZHeegner.X0ModuliGaloisMero`: kind consequence, GLUE, same source,
    flag unread.
  - gz-hl3's proposed `HeegnerPointRational` row is dropped.
  - `locators.md` needs no new row: the source of `hX` is unchanged.

---

## 4. Checks of the statement `X0ModuliGaloisMero` (SPECULATIVE where not marked)

* **Not stronger than the print.**
  - `IsRatModFnMero` describes elements of `ℂ(X₀(N))`: invariance, meromorphy on `ℍ`, and meromorphy at every cusp
    through the growth bound (a pole in the region `Im τ > T` would violate the bound near it). The rational expansion
    at `∞` puts them in `ℚ(X₀(N))`, the function field of the canonical model.
  - For such `g` regular at the algebraic point `x`, `g(x)^σ = g^σ(x^σ) = g(x^σ)` is the printed statement.
  - Junk values at poles are never used: regularity at `τ` and `τ'` is assumed.
* **The moduli hypotheses** are those of `hX`, already reviewed (statement review 2026-11-14).
* **The change only weakens a hypothesis of `hX`**: regular on `ℍ` becomes regular at two points. So it can only
  strengthen the leaf, and only up to the printed statement. A reader should confirm that Shimura's / Deligne–Rapoport's
  statement is for functions regular at the point (§5, pages 1–2).

---

## 5. Pages a human must read (locators UNVERIFIED)

1. Shimura, *Introduction to the arithmetic theory of automorphic functions* (1971), §6.7 and Thm 6.23. Check that the
   Galois equivariance `f(x)^σ = f^σ(x^σ)` of the canonical model is stated for `f` in the function field, finite at
   `x`.
2. Deligne–Rapoport, LNM 349, VI.6 and VII, or Diamond–Shurman §7.5–7.7. The same statement for `X₀(N)_ℚ` and the
   `q`-expansion principle.

Nothing in the proof of `HeegnerPointRational` needs a page of Gross (1984) or Gross–Zagier: the Heegner-point
combinatorics, the class group and the analysis are proved.

---

## 6. What remains for the `hL3` split

The `hL3` split still has two composites. Neither was in this task.

* **`StrongWeilCurve`**: Eichler–Shimura together with a rational Manin constant, in analytic form.
* **`IsogenyLattice`**: Faltings together with the analytic description of isogenies.

The `C_d` form replaces both by `ShimuraCMParamCd`. With `HeegnerPointRational` proved, the `hL3` split is net
negative exactly when those parametrization statements become printed forms or are proved.

---

## 7. Reproduction

```
lake build ZInQKernel.Contrib.OneProof.GrossZagierHeegner.Heegner ZInQKernel.Contrib.OneProof.GrossZagierHeegner.HeegnerCd
lake env lean scratch/gz-heegner/Check.lean        # axioms; output out_check.txt
lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges
lake env lean scratch/gz-heegner/Discharges.lean   # output discharges-output.txt
```

Development: `scratch/gz-heegner/Heegner.lean` is the single development file, which `mk.py` turns into the
contributor file. `Lattice.lean`, `ClassJ.lean` and `Analytic.lean` are the step-by-step development copies.
