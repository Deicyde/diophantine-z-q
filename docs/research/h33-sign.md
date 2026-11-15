# h33-sign: the sign of `[i]` in the leaf `TYZThm33` (TYZ Theorem 3.3)

Task h33-sign, 2026-11-15. Target: the top hypothesis `h33 = ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33`
of `ZInQ.OneProof.frozenTarget` (`ZInQKernel/OneProof/TYZSplit.lean` L157–176; row `h33` of
`docs/one-proof/kinds.tsv`). Source: Tian–Yuan–Zhang, arXiv:1411.4728v1, `~/tyz-src/Period7.tex`
(cited as Lnnnn; at most a line quoted). Scratch: `scratch/h33-sign/` (log `log.md`).

## Verdict

**The pending-review flag can be removed. The statement is correct as written, and no corrected
statement is needed.** The kernel's choice `z_n = f₀(P_n) − [i] f₀(P_n)` for `n ≡ 5 (mod 8)` (`tyzZn`,
with `[i](x, y) = (−x, i·y)` and `ι_C(i) = +I`) is the sign Tian–Yuan–Zhang use. Three independent
arguments establish it:

1. **TYZ's own text (VERIFIED, read).** In the proof of Prop. 3.5 for `n ≡ 5`, TYZ evaluate the Hecke
   operators on the cusps `[∞] = [∞,1]` and `[0] = [∞,w]`, which lie on the identity component (the
   component of `P_n = [h,1]`). They solve the resulting equations with the ℂ-linear uniformization `τ`
   and get `α = −i, β = 1, γ = i` (L1564–1566; the first equation is `τ((1−i)/2) = ατ(1/2) + τ(1/2)`).
   So on the identity component TYZ's `[i] ∈ Aut_{ℚ(i)}(X_U)` acts as complex multiplication by `+I`,
   which is the kernel's `iPt`.
2. **Lean (VERIFIED, compiled; `scratch/h33-sign/Sign.lean`, standard axioms only).** TYZ's
   Theorem 3.6(1) (L1408–1413) includes `z̄_n = −z_n + τ(1)` for `n ≡ 5`. This fixes the reading
   without appealing to point 1:
   * `conj_zAlt`: under the other reading, `z' = P + [i]P`, we get `c(z') = z' − τ(1)` (this uses the
     kernel's Lean proof `T321.tyzThm36ConjFive_of`: Fricke involution plus `τ ↦ τ + 1/4` acting as
     `(x,y) ↦ (−x, iy)`, from `xC_add_quarter`, `yC_add_quarter` and `etaModelFricke`).
   * `torsion_of_alt_thm36`: if `z'` also satisfied TYZ's Thm 3.6(1), then `f₀(P_n)` would be torsion.
   * **Main theorem `tyzThm33With_iff_of_reading`** (`hA : CMAlgebraic`): take any family `zT` of CM
     points of TYZ's shape (`n ≡ 5`: one of `±(P − [i]P)`, `±(P + [i]P)`; `n ≡ 7`: `±f₀(P_n)`) that
     satisfies the conjugation part of TYZ's printed Theorem 3.6(1). Then TYZ's Theorem 3.3 for `zT`
     (`TYZThm33With zT`, i.e. the kernel's display with `basePt` replaced by `zT`) is equivalent to
     the leaf `TYZThm33`.
   * `basePt_reading`: the kernel's `basePt` satisfies these hypotheses, so the theorem is not vacuous.
   * So whichever way one reads `[i]`, the leaf is TYZ's Theorem 3.3 for TYZ's own `z_n`. If TYZ's `z_n`
     were the other reading, it would have to be torsion, and then both sides are torsion and both
     statements agree (`tyzThm33With_imp`).
3. **Exact and numerical computation (VERIFIED, computed).**
   * `qexp.py` (PARI, exact rational q-series to `O(q^~295)`) re-checks the eta-model curve equation,
     `x(t+1/4) = −x(t)` and `y(t+1/4) = +I·y(t)` (the `−I` variant is nonzero, valuation −3), and the
     Fricke translation formula. These are independent checks of identities the kernel already proves
     in Lean.
   * `cm.py` (200 digits; Prop. 3.5(2) at 5 values of `τ`; then 20 squarefree `n ≡ 5 (mod 8)`, `n ≤ 181`):
     - Prop. 3.5(2) in the form `φ(τ/(1−8τ)) = [i]φ(τ) + τ((1−i)/2)` holds with `[i] = +I` and fails
       with `−I` (5/5).
     - `z̄ + z = (0,0) = τ(1)` holds for the kernel's `z_n` (20/20) and fails for `P + [I]P` (0/20).
     - `z_n` is numerically non-torsion (20/20).

Nothing about the sign is left to computation alone. Every step that the leaf's truth needs is
either a Lean theorem or a reading of TYZ's printed text, recorded below. The computations are
consistency checks.

## What the sign argument still rests on (outside Lean, recorded)

* **Shape of TYZ's `z_n`.** TYZ's `z_n` is `±(P ∓ [i]P)`, resp. `±f₀(P_n)`, where `P` is the kernel's
  `tyzHeegnerPt n = phiC(h)`. This holds because:
  - `i₀ = ±phiC`: the eta model is a ℚ-isomorphism `(X₀(32), ∞) → (A, O)`, which is x0-32's leaf
    `X0AnalyticModel` (q-expansion principle). `Aut_ℚ(A, O) = ±1` (L1174).
  - TYZ's `X_U ≅ X₀(32)_{ℚ(i)}` (L1191–1193) with `[i]` the CM automorphism, so on a component
    `f₀∘[i] = [±i]∘f₀`.
  - `P_n = [h,1]` with `h ∈ ℍ` the fixed point of TYZ's embedding (L1203–1205, L1245–1252); `Iso.lean`
    `fixed5`/`fixed7` checks this against `tyzForm`/`tyzForm7`.

  This hypothesis is (h5)/(h7) of the main theorem.
* **TYZ Theorem 3.6(1) as printed.** It is used only to pin the sign, and it is not a hypothesis of
  `frozenTarget`. Point 1 is an independent in-text confirmation that does not use it.
* **The kernel leaf `CMAlgebraic`** (algebraicity of CM values; already a leaf of the kernel).

## Check of every other sign and normalization in `TYZThm33` (all VERIFIED: read in Period7.tex)

| Item | Source | Lean | Check |
|---|---|---|---|
| scope `n ≡ 5, 7` | §3 is for `n ≡ 5,6,7` (L1167) | `n % 8 = 5 ∨ 7` | sub-case, so weaker |
| `Cl_n = Gal(H_n/K_n)`, `χ : Cl_n → {±1}` | L1263, L1300 | `ClG n →* ℤˣ` | equal |
| `Φ ⊂ Cl'_n` representatives, `K'_n = K_n` (5, 7) | L1263, L1279 | lifts `φ t ∈ G_ℚ` with `Restricts` | every `Φ` arises; `P_χ` mod torsion is independent of `Φ` since `z^{σ_ϖ²} − z` is torsion (Thm 3.6(1), L1411) |
| `P_χ = Σ_{t∈Φ} f_n(P_n)^t χ(t)` | L1283 | `PchiG` | equal (left/right action irrelevant for quadratic `χ`) |
| `χ_{d₀,d₁}` for `K_n(√d₁)` (5,6), `K_n(√d₁*)` (7) | L1304–1305 | `IsChiPair`, `radTYZ` | equal; `d₁* = (−1)^{(d₁−1)/2} d₁` is `radTYZ` |
| `√d₁` resp. `√d₁*` in `H_n` | genus theory (STANDARD) | (`IsExtChar` satisfiable) | `d₁* ≡ 1 (4)`; for `n ≡ 5`, `d₁ ≡ 3`: `K_n(√d₁) = K_n(√−d₀)`, `−d₀ ≡ 1 (4)` |
| `0 < d₀ ≡ 5,6,7`, `0 < d₁ ≡ 1,2,3` | L1303 | as printed (ℕ) | equal |
| `P_χ = ε 2^{h₂(n)} 𝓛(d₁) 𝒫(d₀)` in `A(H'_n(i)) ⊗ ℚ` | L1306–1308 | `m d₀ • P_χ − (ε 2^{h2G n} ℓ d₁) • Q d₀` torsion | equal, with `𝒫(d₀) = Q d₀ / m d₀`; `ℤ[i]` acts through `iPt` |
| `ε = ±i` iff `(d₀,d₁) ≡ (5,3)`, else `±1` | L1309 | `EpsTYZ` | equal; flipping the sign of `[i]` in the `ℤ[i]`-action keeps the class |
| `h₂(n) = dim_{𝔽₂} Cl_n/2Cl_n` | L992 | `h2G = log₂ [Cl_n : ⟨squares⟩]` | equal (`Cl_n` is abelian) |
| `𝒫(n) = 2^{−1−ρ(n)} 𝓛(n) α_n ∈ A(K_n)^- ⊗ ℚ`, `A(K_n)^- = {ᾱ = −α}`, `𝒫 = 0` if `𝓛 = 0` | L1291–1295 | `InMinus d (Q d)`; `Q d` torsion when `ord ≥ 2` | weaker (forgets the coefficient's value) |
| `𝓛(n) = 0` iff `ord_{s=1} > 1` | L338–345 | hypothesis `¬∃F, … ≤ 1` | equal zero set |
| `𝓛(m)² = L(E_m,1)/(2^{2k−2−a} Ω_{m,∞})`, `k` = # odd prime factors, `a = 1` for odd `m` | L338–349 | `lcalSq m` with `2^{2k−3}` | equal (root number `+1` for `m ≡ 1,3`, so `ord ≠ 1`) |
| `Ω_{n,∞} = (2/√n) ∫₁^∞ dx/√(x³−x)` | L350–351 | `omegaTYZ` | equal |
| `𝓛` defined up to sign | L364 | `∀ ℓ` with `ℓ² = lcalSq`; `ε` chosen after `ℓ` | sign absorbed in `ε` |
| `E_n : ny² = x³ − x` | L312 | `curveC n : y² = x³ − n²x` | ℚ-isomorphic (`Iso.lean` `tyzE_to_curveC`); Mathlib's L-series uses local minimal models (rv-lit.md) |
| `A : 2y² = x³ + x` | L1173 | `curveA : y² = x³ + 4x` | ℚ-isomorphic by `(2x, 4y)`, commutes with `[i]` (`Iso.lean`) |
| embeddings `K_n → M₂(ℚ)` | L1203–1205 | `tyzForm = [16(n+1), −8, 1]`, `tyzForm7 = [(n+δ²)/4, δ, 1]` | fixed points and discriminants `−64n`, `−n` (`Iso.lean`); kernel `δ` is one admissible choice |
| `P_n = [h,1]`, `h ∈ ℍ` | L1245–1252 | `cmPoint` with `+I√−D` | equal |
| `f_n = f₀ − f₀∘[i]` (5), `i₀` (7) | L1196–1199 | `tyzZn`, `tyzZ7` | the sign is settled above |

## Lean

* `scratch/h33-sign/Sign.lean` (imports `ZInQKernel.OneProof.TYZSplit`): 0 errors, 0 warnings.
  - `#print axioms` for `tyzThm33With_iff_of_reading`, `basePt_reading`, `torsion_of_alt_thm36` and
    `tyzThm33Copy_iff` gives `[propext, Classical.choice, Quot.sound]`.
  - `TYZThm33Copy` is a verbatim copy of the kernel statement (`Iff.rfl` with it).
  - `iPt_pullback_differential` shows the kernel's `[i]` multiplies the invariant differential by
    `+I`, which is the normalized CM.
* `scratch/h33-sign/Iso.lean` (Mathlib only): 0 errors, 0 warnings. It checks the curve isomorphisms,
  the compatibility with `[i]`, the Heegner fixed points and the discriminants.

## Recommendation for the integrator

In `docs/one-proof/kinds.tsv` row `h33`, replace "pending review: the sign [i] … chosen numerically"
by "sign of [i] verified from TYZ's text (α = −i, L1564–1566) and pinned by TYZ Thm 3.6(1) in Lean
(h33-sign)". The row stays `published`/`LEAF`. There is still no human review of TYZ's paper itself.
A small stale remark: the docstring of `TYZGenus.CM.tyzForm` says "source not on this host"; the
source is now at `~/tyz-src/Period7.tex`, and it agrees with the form.
