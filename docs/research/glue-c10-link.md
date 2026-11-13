# glue-c10-link: the trace link of C10, `c_p = ½·β(σ)⁻¹a_σ·tr α_σ`

Status: research note (task glue-c10-link, 2026-11-12). Lean file:
`scratch/glue-c10-link/Link.lean`. Results log: `scratch/glue-c10-link/log.md`. No file under
`ZInQKernel/`, `blueprint/`, or another task's notes or scratch directory was edited.

Marks: **VERIFIED** means compiled or read in a source. **STANDARD** means a published theorem.
**SPECULATIVE** means an assessment. Theorem numbers given from memory are UNVERIFIED.

## Verdict

**The trace link is proved in Lean, and it discharges the abelian-variety trace hypotheses
`hr₃, hr₅` of `GlueC10.c10`.** This closes the gap that rv-wave17 (§Verdict item 3) and
glue-c10 (§3 item 3) left open.

- The link is `GlueC10Link.trace_link`. Fix an abelian variety `Ā` over a field `k` and an
  endomorphism `α' ∈ End(Ā)`. Then there is one integer `t`, the trace of `α'` on
  `E ⊗ V_ℓ(Ā)`, the same for every prime `ℓ ≠ char k`. Take any descent datum, matrix units and
  `σ` whose `T(σ)` is conjugate to `V_ℓ(α')/N` (`FrobCompare`). Then
  `tr r_ℓ(σ) = ι_ℓ(½ · β(σ)⁻¹ a_σ · t/N)`, and `t/N = tr α_σ` for `α_σ = α'/N ∈ End⁰(Ā)`.
- **C10 with the link plugged in** is `GlueC10Link.c10_of_trace_link`. Its trace hypotheses
  `hr₃, hr₅` are proved, not assumed. It applies `GlueC10.c10` verbatim:
  - `r_ℓ` is the descended representation of B1/C1 (`rL`, built from `GlueDescent.rhoRep`
    and `MatrixUnits2`);
  - `c := a_f`, the modular coefficients.
- **The input from `A`, split into its three geometric parts**, is
  `GlueC10Link.c10_of_squares`. The parts are the descent instantiation, the Serre–Tate/Frobenius
  square and the Néron square. The morphisms `μ' : {}^σA → A`, `F : Ā → Ā^{(p)}` and
  `μ̄' : Ā^{(p)} → Ā` are genuine `Hom`s of pkg-I3 abelian varieties.

No proof has a `sorry`. `#print axioms` on all seven main theorems shows only `propext`,
`Classical.choice` and `Quot.sound`. VERIFIED: `lake env lean scratch/glue-c10-link/Link.lean`,
11:58 PST, no errors and no warnings. The file imports `ZInQKernel.HDecomp.{Objects, C10.C10,
C10.Trace, Descent.ProjRep}` and uses their definitions unchanged.

**Leaves used:** `ChebotarevExists`, `BrauerNesbittChar0` (pkg-I6, via `c10`) and
`PkgI3.CharPolyIndepOfEll` (Mumford §19 Thm 4). No new leaf is introduced.

## 1. Statements (all in `scratch/glue-c10-link/Link.lean`, namespace `GlueC10Link`)

| Lean name | Statement | Hypotheses | Status |
| --- | --- | --- | --- |
| `subRep u ρ hc` | `r = ρ\|_W`, `W = e₀₀V`, as a `Representation E G W` | `ρ` commutes with the matrix units | def |
| `conj_splitEquiv` | `V ≃ W × W` conjugates `ρ g` to `r g × r g` | same | **proved** |
| `trace_eq_two_mul_trace_subRep` | `tr ρ(g) = 2·tr r(g)` | `dim V < ∞` | **proved** |
| `trace_rho` | `tr(β(g)⁻¹a(g)T(g)) = β(g)⁻¹a(g)·tr T(g)` | — | **proved** |
| `finite_of_baseChange` | `E ⊗_K M` finite over `E` ⇒ `M` finite over `K` | fields | **proved** |
| `endE α ℓ E` | `V_ℓ(α)` extended to `E ⊗_{ℚ_ℓ} V_ℓ(Ā)`: `((homT α).baseChange ℚ_ℓ).baseChange E` | — | def |
| `trace_endE_indep` | `∃ t : ℤ, ∀ ℓ ≠ char k, ∀ E ⊇ ℚ_ℓ` (with `E ⊗ V_ℓ(Ā)` finite), `tr_E(endE α ℓ E) = t` | `CharPolyIndepOfEll` | **proved** |
| `rhoL`, `rL` | `ρ_ℓ = β⁻¹ a T` (`GlueDescent.rhoRep`) with scalars `c, ε, a, β ∈ C` mapped by `ι : C → E`; `r_ℓ = ρ_ℓ\|_W` | the cocycle identities in `C`, `β ≠ 0`, `a 1 = β 1 = 1`, `T 1 = 1` | defs |
| `FrobCompare ℓ Tσ α N` | `∃ Φ : V ≃ₗ[E] E ⊗ V_ℓ(Ā)`, `Φ (N·Tσ) Φ⁻¹ = endE α ℓ E` | — | def (input from `A`) |
| `trace_T_of_frobCompare` | `∃ t : ℤ, ∀ ℓ ≠ char k`: `FrobCompare ℓ Tσ α N ⇒ N·tr Tσ = t` | `CharPolyIndepOfEll` | **proved** |
| **`trace_link`** | `∃ t : ℤ`, (`tr_E(endE α ℓ E) = t` for all `ℓ ≠ char k`, `E`) ∧ (for all `ℓ ≠ char k`, descent data, `u`, `σ`, `N ≠ 0`: `FrobCompare ℓ (T σ) α N ⇒ tr r_ℓ(σ) = ι(β(σ)⁻¹·a(σ)·(t/N)/2)`) | `CharPolyIndepOfEll` | **proved** |
| `trace_link_three_five` | `3, 5 ∈ S`, `p ∉ S`, `(k, CharP k p, Ā, α', N ≠ 0)` with `FrobCompare` at 3 and 5 ⇒ `∃ x ∈ C`, `tr r₃(g) = ι₃ x ∧ tr r₅(g) = ι₅ x` | `CharPolyIndepOfEll` | **proved** |
| **`c10_of_trace_link`** | `r₃ ≅ ρ₃` as `k₃[G_ℚ]`-modules, `r₃ = rL …` | Chebotarev, Brauer–Nesbitt, Mumford §19 Thm 4; see §3 | **proved** |
| `homComp`, `homT_homComp` | composition in pkg-I3 `Hom`; `T_ℓ(g∘f) = T_ℓ(g)∘T_ℓ(f)` | — | def, **proved** |
| `conj_baseChange` | `(e⊗A)(f⊗A)(e⊗A)⁻¹ = (efe⁻¹)⊗A` | — | **proved** |
| `frobCompare_of_squares` | `hΨ, hS1, hS2` (§3) ⇒ `FrobCompare ℓ Tσ (μ̄'∘F) N` | — | **proved** |
| `FrobSquares`, `frobCompare_of_frobSquares` | the three squares packaged at one `ℓ` | — | def, **proved** |
| **`c10_of_squares`** | `c10_of_trace_link` with `hFrob` replaced by `FrobSquares` at 3 and 5 | same leaves | **proved** |
| `example` (§7) | `FrobCompare ℓ (endE α ℓ E) α 1` (`Φ = id`): `FrobCompare` can hold | — | **proved** (non-vacuity) |

## 2. How the proofs go

1. **Halving.** `MatrixUnits2.splitEquiv : V ≃ W × W` intertwines `ρ g` with `r g × r g`
   (descent glue `splitEquiv_intertwines`). So `tr ρ(g) = tr(r g × r g) = 2 tr r(g)`, by
   `LinearMap.trace_conj'` and `LinearMap.trace_prodMap'`. This proves the hypothesis `h2` that
   `GlueC10.trace_half` assumed. (VERIFIED)
2. **Scalars.** `ρ(g) = (β(g)⁻¹a(g))•T(g)`, and the trace is linear. (VERIFIED)
3. **Comparison.** `tr(N·T(σ)) = tr(Φ(N·T(σ))Φ⁻¹) = tr_E(endE α' ℓ E)`. Base change preserves the
   trace twice (`LinearMap.trace_baseChange`: `ℤ_ℓ → ℚ_ℓ` is built into `V_ℓ`, then `ℚ_ℓ → E`),
   and `PkgI3.trace_indep_of_ell` makes the result the integer `t`. It needs a finite basis of
   `V_ℓ(Ā)`. That basis comes from `dim V < ∞` through `Φ` and `finite_of_baseChange`, so the
   leaf `TateModuleFree` is not needed. (VERIFIED)
4. **Algebra.** `2 tr r(σ) = ι(β)⁻¹ι(a)·tr T(σ)` and `N·tr T(σ) = t`. Then
   `tr r(σ) = ι(β(σ)⁻¹a(σ)(t/N)/2)`. Here `2 ≠ 0` and `N ≠ 0` in `E`, because `ι` is injective
   and `C` has characteristic 0. (VERIFIED)
5. **One element for both primes.** `t` is chosen once for `(Ā, α')`, before `ℓ`. So
   `x = ½β(σ)⁻¹a_σ t/N ∈ C` serves `ℓ = 3` and `ℓ = 5` alike. `CharP k p` with `p ∉ S ∋ 3, 5`
   gives `(3 : k) ≠ 0` and `(5 : k) ≠ 0` (`cast_ne_zero_of_charP`). (VERIFIED)
6. **Into `c10`.** Apply `GlueC10.c10` with `c := a_f`:
   - `hr₅` is `h₅` (C9) followed by `hρ₅` (Eichler–Shimura at 5);
   - for `hr₃`, the element `x` of item 5 has `ι₅(x) = tr r₅(g) = tr ρ₅(g) = ι₅(a_f(p))`, so
     `x = a_f(p)` by injectivity of `ι₅`, and `tr r₃(g) = ι₃(x) = ι₃(a_f(p))`. (VERIFIED)
7. **Squares.** Let `Φ = Ψ ⋅ (red ⊗ E)`. Then `Φ(N·T(σ))Φ⁻¹ = (red (μ'∘σ_*) red⁻¹) ⊗ E` by
   `hΨ` and `conj_baseChange`. Next, `red ∘ μ' ∘ σ_* ∘ red⁻¹ = μ̄' ∘ red' ∘ σ_* ∘ red⁻¹` by
   `hS2`, and this equals `μ̄' ∘ F` by `hS1`. Finally `V_ℓ(μ̄' ∘ F) = V_ℓ(μ̄') ∘ V_ℓ(F)`
   (`homT_homComp`, `LinearMap.baseChange_comp`). (VERIFIED)

**A finding about the per-prime element `c_p`.** N5 (L788-790) produces one element of `C` for
each lift `σ`. `c10` asks for `c p` that depends on `p` only. Item 6 avoids the question: the
link gives an element `x_g` for each Frobenius element `g`, and `x_g = a_f(p)` follows. So no
argument is needed that `x_g` does not depend on `σ` or `v` (unramifiedness of `r_ℓ` at `p`,
conjugation invariance). In particular, the hypotheses `hr₃, hr₅` no longer carry rv-wave17's
usage condition (item 2) that `r₃, r₅` be unramified outside `S`. The condition survives as the
condition that `hFrob`/`hSq` be true: `p ∉ S` must be a prime of good reduction, unramified in
`L`, with `p ≠ 3, 5`. `3, 5 ∈ S` is now an explicit hypothesis (`h3S`, `h5S`). (VERIFIED for
the Lean; the reading of N5 is from diophantine_zq.tex L776-795.)

## 3. Exactly which hypotheses still come from the surface `A`

In `c10_of_squares` (and `c10_of_trace_link`), everything else is proved or is a leaf.

**From `A` (not statable over Mathlib's objects today; see below):**

1. **Descent instantiation at `ℓ = 3, 5`.** This is the same abstraction as the descent glue
   (glue-descent): `V_ℓ` finite-dimensional over `E_ℓ ⊇ ℚ_ℓ`, `T_ℓ : G_ℚ → End(V_ℓ)` with
   `T_ℓ(g)T_ℓ(h) = ι_ℓ(c(g,h))T_ℓ(gh)` and `T_ℓ(1) = 1`, and matrix units `u_ℓ` commuting with
   `T_ℓ`. Here `T(σ) = μ_σ∘σ` on `V_ℓ(A)⊗E`, and `u_ℓ` is the image of `B⊗E ≅ M₂(E)`.
2. **The Frobenius squares `hSq`.** For every Frobenius `g` at `p ∉ S` there are:
   - fields `L` and `k` with `CharP k p`;
   - pkg-I3 abelian varieties `A, Aσ` over `L` and `Ā, Ā'` over `k`;
   - `μ' : Aσ → A`, `F : Ā → Ā'`, `μ̄' : Ā' → Ā`, and `N ≠ 0`.

   At each `ℓ ∈ {3, 5}` there are also `ℚ_ℓ`-isomorphisms `σ_* : V_ℓ(A) ≅ V_ℓ(Aσ)`,
   `red : V_ℓ(A) ≅ V_ℓ(Ā)`, `red' : V_ℓ(Aσ) ≅ V_ℓ(Ā')` and `Ψ : V_ℓ ≅ E ⊗ V_ℓ(A)`, with:
   - `hΨ`: `Ψ(N·T_ℓ(g))Ψ⁻¹ = (V_ℓ(μ')∘σ_*)⊗E`. This is the instantiation `T(σ) = μ_σ∘σ`, with
     `μ_σ = μ'/N`.
   - `hS1`: `red'∘σ_* = V_ℓ(F)∘red`. This is Serre–Tate specialization at good reduction
     (`red`, `red'` are the reduction isomorphisms; pkg-I2's `ReductionTorsionBijective` at
     finite level). It also uses the fact that `g ∈ D_𝔓` acts on reduced points as the relative
     `p`-Frobenius `F : Ā → Ā^{(p)} = \overline{{}^σA}` (N5 L781-786; STANDARD).
   - `hS2`: `red∘V_ℓ(μ') = V_ℓ(μ̄')∘red'`. This is the Néron mapping property (`μ̄'` is the
     special fibre of the extension of `μ'`; pkg-I2's `NeronMappingAbelianScheme`) together
     with functoriality of reduction.
3. **Continuity of `r₃`** (`hrc`). It holds because the Tate action is continuous, `β` is
   continuous and `μ_σ` is locally constant.
4. **Semisimplicity of `r₃`** (`hr`). It comes from Faltings' Satz 3 with
   `GlueC10.semisimple_of_le`, as in glue-c10.
5. **The scalar data** `c, ε, a, β ∈ C` with the identities `ha`, `hβ`, `β ≠ 0` and
   `a 1 = β 1 = 1`. These are outputs of B1-B3. The real arithmetic is
   `GlueDescent.sign_normalization`, and the cochain comes from B2-B3. In this file they are
   hypotheses.

**Not from `A`:**
- `h₅` (C9: `r₅ ≅ ρ_{f,ι₅}` on traces; Pan and Shimura);
- `hρ₃, hρ₅` (Eichler–Shimura for `ρ_f`; `S` must also contain the primes dividing the level);
- continuity and semisimplicity of `ρ₃` (modular side);
- the leaves Chebotarev, Brauer–Nesbitt and Mumford §19 Thm 4.

**Why `hSq` is still a hypothesis.** It quantifies over genuine pkg-I3 abelian varieties and
genuine `Hom`s. But `σ_*`, `red`, `red'` and `Ψ` are abstract linear isomorphisms, constrained
only by the squares. Stating them as the actual maps would need three things Mathlib lacks:
- the conjugate variety `{}^σA` and the transport `A(\bar ℚ) → {}^σA(\bar ℚ)`;
- the special fibre of an abelian scheme as an `AbVar k`, and the identification of `κ(𝔓)` with
  `AlgebraicClosure k`;
- the relative Frobenius morphism.

pkg-I2 has `HasGoodReduction`, `IsReductionOf` and `ReductionTorsionBijective` at the level of
points. Passing to Tate modules and building the three objects above is the remaining work.
Since the isomorphisms are existential, `hSq` is no stronger than the geometric facts. The
genuine reduction maps satisfy it. (SPECULATIVE as to effort; the truth of the squares is
STANDARD.)

## 4. Faithfulness checks

- **`FrobCompare` and `FrobSquares` can hold.** The §7 `example` proves `FrobCompare` with
  `Φ = id`. The squares hold for the genuine reduction maps (STANDARD, §3 item 2). Neither
  hypothesis states its conclusion: the conclusion is a trace identity in `C`, and the
  hypotheses are conjugacy statements about linear maps. (VERIFIED for the example.)
- **Direction of Frobenius.** `T_ℓ` is built from points, so it is homology. An arithmetic
  Frobenius `g ∈ D_𝔓` acts on reduced points as `F`, which raises coordinates to the `p`-th
  power. So `T(σ)` is matched with `μ̄'∘F`, not with its inverse. This is the convention of N5
  L781-786 and of Tate's theorem that the Frobenius endomorphism acts on `T_ℓ` as the
  arithmetic Frobenius (STANDARD; Tate 1966, locator UNVERIFIED).
- **`α_σ ∈ End⁰`.** `μ_σ` is a quasi-isogeny, so the Lean takes `α' = N·α_σ ∈ End(Ā)` and
  divides by `N`. `tr α_σ = t/N ∈ ℚ` (VERIFIED in the statement of `trace_link`).
- **ℓ-independence.** One `t` serves every `ℓ ≠ char k` and every coefficient field `E`
  (`trace_link`, first conjunct). This is N5's "independent of the coefficient prime"
  (L788-790).
- **Universes.** `E, V, G, C` are in `Type`. The existential `∃ t` fixes universes, and `c10`
  is stated over `Type`.

## 5. Files

| File | Imports | Content | `sorry` |
| --- | --- | --- | --- |
| `scratch/glue-c10-link/Link.lean` | `ZInQKernel.HDecomp.{Objects, C10.C10, C10.Trace, Descent.ProjRep}` | §§1-8 above, the non-vacuity example, `#print axioms` | none |
| `scratch/glue-c10-link/log.md` | — | results log | — |

**Integration.** `Link.lean` compiles against the built modules (`lake build` of the four
imports, 60 s). It can go to `ZInQKernel/HDecomp/C10/Link.lean` unchanged. Two notation clashes
forced renames:
- `ι` and `μ` are tokens once `CategoryTheory.MonObj` is open, so the file uses `emb`, `ιI`,
  `mu` and `mub`;
- `T` clashes with `PkgI3.AbVar.T`, so `PkgI3.AbVar` is not opened.
