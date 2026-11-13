# rv-blueprints: adversarial review of the three formalization blueprints

Task rv-blueprints, 2026-11-12. Reviewed: `docs/research/bp-faltings.md`,
`docs/research/bp-modcurves.md` and `docs/research/bp-qmmoduli.md`, with their Lean files in
`scratch/bp-*/`. This review's own files are in `scratch/rv-blueprints/` (results log `log.md`).
No file under `ZInQKernel/` or `blueprint/`, and no other task's notes or scratch files, was
edited.

Marks: **VERIFIED** means read in a source, computed, or compiled. **STANDARD** means published,
with a reference. **SPECULATIVE** means a judgement. A theorem number recalled from memory is
marked **UNVERIFIED** (this host has no network). The manuscript `diophantine_zq.tex` is cited as
N5 with line numbers.

## 0. Verdicts

| Blueprint | Verdict | Failing or weak claims (repairs in §§1-3) |
| --- | --- | --- |
| **bp-faltings** | **SOUND AFTER REPAIRS** | The central claim is correct: the infimum over smooth group models is the stable Faltings height in Faltings' normalization, and Deligne's is `h_D = h_F + (g/2) log π`. Four repairs. (F1) Additivity H7 is **not** definitional for the infimum: the direction that step E4 uses, `h(A) + h(Z) ≤ h(A × Z)`, needs Néron models (M5) and H5. (F2) Each of R18-R22 is a consequence of its publication only together with H5, so H5 must be proved or entered as an explicit leaf. (F3) AT1 is a plumbing test, not a normalization test, and no test checks `g ≥ 2`: add AT4 (additivity for `E₁ × E₂`) and AT5 (base change). (F4) R19 is the one leaf whose truth depends on the source's normalization. |
| **bp-modcurves** | **SOUND AFTER REPAIRS** | The interface `ρ_{f,ℓ} ⊂ V_ℓ(J₁(N))`, `g ≤ N²` and Belyi degree `≤ N²` is captured faithfully. "Albanese predicate + existence leaf" is neither vacuous nor a disguised conclusion. (M1) The leaf MC9, "our model ≅ Shimura's canonical model", is stated over an object the blueprint never defines. It is also unnecessary, because the existential R16 is invariant under isomorphism of `J` (proved in Lean here). R16 should be stated directly for the `K_N` model. |
| **bp-qmmoduli** | **SOUND AFTER REPAIRS** | "Field-valued points suffice" holds for the **h-trust route** (h-b1's Prop. TS and the Raynaud route for A6). It does not hold for N5 as printed, which builds Buzzard's integral moduli scheme (Q1). The proposed field-point package is **too weak in four places**: (Q2) R5fp's degree form cannot run A10; (Q3) R1an, a statement at each point, cannot run F1; (Q4) no listed leaf supplies `π₀(X₆) = 1`, which Lemma NV step 4 uses; it must be added as a leaf or derived as glue; (Q5) R2fp's one-way CM clauses do not give Lemma NV step 2. Each repair is a consequence of the same sources and stays at field level. |

Lean (VERIFIED, compiled with `lake env lean`, one process at a time). Every blueprint file
compiles with no error and no `sorry`. An appended audit command runs `Lean.collectAxioms` on
**every** declaration of each file, 629 declarations in all, and finds no axiom other than
`propext`, `Classical.choice`, `Quot.sound` (§4). The review adds three compiled files and an appended audit fragment, all with
standard axioms only:
- `Normalizations.lean`: the normalization arithmetic for R19, R21 and R22.
- `R5Repair.lean`: the repaired R5 statement `R5fpStrong`, with a proof that it implies the
  blueprint's `R5fp` (the file is `QMAbVar.lean` minus its `#print axioms` block, plus these).
- `R16Transfer.lean`: the existential R16 transfers along isomorphisms of `J` as group objects
  (`[IsMonHom e.inv]`). Its module header, copied from `Jacobian.lean`, describes declarations
  the file does not contain.
- `audit_tail.lean`: the axiom audit (a fragment appended to each file, not a compiled file of
  its own).

Computations (VERIFIED): `at3_check.py` re-derives the normalization value of AT3, and
`sheet_check.py` checks the sign claim of bp-qmmoduli §2.2 on 30 samples.

## 1. bp-faltings

### 1.1 The definition (H3) is the stable Faltings height (correct)

Let `h(A_L, 𝒢) = [L:ℚ]⁻¹(log #(ω_𝒢/𝓞_L η) − ½ ∑_σ log ‖η‖²_σ)`, where
`‖η‖²_σ = (i/2)^g (−1)^{g(g−1)/2} ∫ η∧η̄`, the positive value, which is what `torusMetricSq`
computes. Then `inf_{L,𝒢} h(A_L, 𝒢) = h_F^st(A)`. The argument is STANDARD; the BLR locators are
UNVERIFIED.
- **Fixed `L`.** BLR's Néron mapping property extends `𝒢_L ≅ A_L` to a morphism `𝒢 → 𝒩_L` for
  every smooth `𝓞_L`-scheme `𝒢`. Neither a group structure nor separatedness is needed.
- **Lattice comparison.** Pulling back invariant differentials gives `ω_{𝒩_L} ⊆ ω_𝒢` inside
  `⋀^g H⁰(A_L, Ω¹)`. A larger lattice gives a larger `#(ω/𝓞η)`, so `h(𝒢) ≥ h(𝒩_L)`
  (`modelHeight_le_of_le`, BUILT).
- **Varying `L`.** For `L ⊆ L'`, `h(𝒩_L) = h(𝒩_L ⊗ 𝓞_{L'}) ≥ h(𝒩_{L'})`, with equality when `A_L`
  is semistable, because the identity components agree (SGA 7 IX 3.3, UNVERIFIED). So the
  infimum is the semistable Néron value. Heights decrease under extension, and the stable height
  is the minimum.
- **No model too many or too few.** The infimum cannot fall below the Néron value, because every
  smooth model maps to `𝒩_L`. It does not miss the Néron value, because `𝒩_L` is smooth,
  separated and of finite type.
- **Normalizations.**
  - Deligne's `(i/2π)^g` metric is `π^{−g}` times Faltings', so `h_D = h_F + (g/2) log π` (H6).
  - Lebesgue measure on `ℂ` is `(i/2) dz∧dz̄`, so `torusMetricSq` is Faltings'.
  - VERIFIED here (`at3_check.py`): for `y² = x³ + 1`, `faltingsHeightEC` computed by 2-d
    numerical integration is `−1.3211174284280`. An independent evaluation through the
    `η`-product, `−(1/12)log(|η(ρ)|²⁴(Im ρ)⁶) − log 2π`, agrees to 19 digits. Deligne's recalled
    minimum `−0.74875248` (STANDARD, locator UNVERIFIED) minus `½ log π` gives `−1.32111742`,
    the same to the 8 digits of the recalled constant.
- **`EReal`.** Taking the infimum in `EReal` is the right call. The index set (finite extensions
  as a structure in one universe) causes no difficulty, because `iInf` accepts any `Sort`.

### 1.2 The leaves R18-R22 for this definition

Each leaf is a consequence of its publication **together with H5**, the theorem that the infimum
equals the published height. Directions (VERIFIED in Lean, `Normalizations.lean`):

| Leaf | Holds as stated in h-decomposition? | Why |
| --- | --- | --- |
| R18 Javanpeykar `h_F(Jac X) ≤ 13·10⁶ g d⁵` | yes, in either normalization | an upper bound on `h_D ≥ h_F` bounds `h_F` (`faltings_le_deligne`) |
| R19 Gaudron–Rémond, `κ(A)` with `max(h_F(A), log[K:ℚ], 1)` | **yes only if** Gaudron–Rémond's `h` is the original Faltings normalization (locators.md read it so) | `κ` is monotone in the height, so the `h_F` form is the stronger statement (`faltings_kappa_le` proves only the inner `max` inequality; monotonicity of `κ` is not in Lean); an `h_D`-normalized original would not imply it |
| R20 Faltings Lemma 5 | yes | a difference of heights; for stable heights, base change to a common semistable field (H4/H5) |
| R21 Bost, `h_F ≥ −(3/2) dim A` | yes, in either normalization | `bost_F_of_D`: `h_D ≥ −(g/2)log 2π` gives `h_F ≥ −(g/2)log(2π²) ≥ −(3/2)g`, since `log(2π²) < 3` (proved) |
| R22 Pazuki, hardened `X_D = max(1, h_F + 3)` | yes | `log π < 3` (`log_pi_lt_three`) |

### 1.3 Finding F1: additivity is not "from the definition"

E4 (N5 L893-899) bounds `h_F(A)` by `h_F(A × Z) − h_F(Z)`. It therefore needs
`h(A) + h(Z) ≤ h(A × Z)`. Under the infimum definition, product models `𝒢_A × 𝒢_Z` give only the
opposite inequality, `h(A × Z) ≤ h(A) + h(Z)`. The needed direction holds because the infimum for
`A × Z` is attained by `𝒩_A × 𝒩_Z` over a common semistable field. That fact is immediate from
the Néron mapping property (a product of Néron models is a Néron model), but it needs M5 and H5.
Hence:
- bp-faltings §2.6, row H7, "from AV6, AR3 and the covolume of a product lattice", is incomplete;
- the former h-decomposition remark under R20, "Additivity and invariance under base change of the
  stable height follow from the definition: glue", is false for additivity (corrected since, in
  h-decomposition.md by leaf-adopt, crediting this finding).

Invariance under base change does follow from H4 alone: extensions of `L` are cofinal among
extensions of `K`, by taking composita.

### 1.4 Acceptance tests

- **AT1 is a plumbing test.** Its right side `faltingsHeightEC` is defined by the same integral
  (`hypVol 1` is `(i/2)∫ω∧ω̄` for `ω = dx/√P`). AT1 checks that the lattice, period and
  coefficient maps of a real `GroupModel` produce that integral. That is necessary, but it is
  not a normalization check.
- **AT3 is the normalization check.** It is re-verified here (§1.1).
- **Missing: `g ≥ 2`.** No test exercises the `(i/2)^g` sign and the `⋀^g` structure against an
  independent value. AT2's right side is again a formula of the same kind.
- **Add AT4** (additivity on a product of elliptic curves):
  `faltingsHeight (E₁ × E₂) = faltingsHeightEC E₁ + faltingsHeightEC E₂`. It ties the `g = 2`
  normalization to the verified `g = 1` one, and it needs H7 (so M5/H5, §1.3).
- **Add AT5** (base change): `faltingsHeight (A_L) = faltingsHeight A` (H4).

### 1.5 Repairs (exact text)

1. §0 item 1. After "enter only in the theorem "the infimum is finite and is attained by the
   Néron model over a semistable field" (node H5)", insert: "and in the direction
   `h(A) + h(B) ≤ h(A × B)` of the additivity H7, which step E4 uses (rv-blueprints §1.3)". Then
   replace "The leaves R18-R22 can be **stated** without H5." by: "The leaves R18-R22 can be
   **stated** without H5, but each is a consequence of its publication only together with H5.
   So H5 must be proved (WP-F) or entered as an explicit leaf with its sources (Faltings 1983 §1;
   Deligne, Sém. Bourbaki 616; BLR; SGA 7 IX)."
2. §2.6, row H7. Replace the route cell by: "`≤` from product models (AV6, AR3, covolume of a
   product lattice). The direction `≥`, the one E4 uses, needs the Néron model of `A_L × B_L` to
   be `𝒩_A × 𝒩_B` (mapping property, M5) over a common semistable `L` (H5). Tier M given M5 and
   H5."
3. §2.6, row H5. Replace "independent of `K` (`h(A_L) = h(A)`)" by "(independence of `K`,
   `h(A_L) = h(A)`, follows from H4 alone, by cofinality of composita)".
4. §2.7. Add the rows AT4 and AT5 of §1.4.
5. §2.8, row R19. Add: "Normalization-sensitive: a consequence only if Gaudron–Rémond's `h` is
   the original Faltings normalization. R18 and R20-R22 hold in either normalization
   (rv-blueprints `Normalizations.lean`)."
6. §4.3. Add: "`AbVar.periodData` must be *defined* from AN3, as the uniformization satisfying its
   specification. A choice of an arbitrary pair would give a wrong height, because every theorem
   about `HodgeData` holds for every pair."

## 2. bp-modcurves

### 2.1 What the proof uses is captured

VERIFIED by reading N5 L860-876 and h-decomposition §3 rows G13, G17 and G18.
- **(a) The constituent.** `ρ_{f,ℓ}` is a constituent of `V_ℓ(J₁(N))`, through the existential
  R16 and G13.
  - G13 is correct: `V_ℓ(π)` is onto for a surjective homomorphism (Poincaré reducibility). The
    `ι`-component is a `G_ℚ`-stable direct summand of `V_ℓ(A) ⊗ ℚ̄_ℓ`, so it is a quotient of
    `V_ℓ(J) ⊗ ℚ̄_ℓ`.
  - The arithmetic-Frobenius convention on the covariant `V_ℓ` (trace `a_p`, determinant
    `χ(p)p`) is right.
  - The `a_p` versus `ā_p` ambiguity is indeed absorbed by `θ ↦ θ∘c`. The `ι`-component for
    `θ∘c` is the `ι∘c`-component for `θ`, and complex conjugation preserves `K_f`, which is
    totally real or CM.
- **(b) The genus.** `g = dim J ≤ N²`, by Riemann–Hurwitz for a Belyi map:
  `2g − 2 ≤ d − 3`, so `g ≤ (d − 1)/2`.
- **(c) The Belyi degree.** `d = [K_N : ℚ(j)] ≤ N²/2`, and `j/1728` is unramified outside
  `{0, 1, ∞}`.
  - `K_N = ℚ(j)(x(P))` is the function field of the `(E, ℤ/N ↪ E)` model. It is the fixed field
    of the stabilizer of `±P` in `GL₂(ℤ/N)`, which has index `J₂(N)/2` and full determinant.
  - The choice of model of `E_j` over `ℚ(j)` changes `x(P)` only by a factor in `ℚ(j)^×` (a
    quadratic twist), so it does not change `K_N` (STANDARD).
- **Arithmetic.** `13·10⁶·g·d⁵ ≤ 13·10⁶·N¹²` (checked by reading).

### 2.2 "Albanese predicate + existence leaf" is not a vacuous or disguised leaf

`IsJacobian X P₀ J aj` (`Jacobian.lean`, VERIFIED compiled) is a universal property over genuine
Mathlib objects:
- the scheme `X` over `Spec K`;
- the point `P₀ : 𝟙_ ⟶ X`;
- the repository's `AbVar` (group object, proper, smooth, geometrically integral);
- Mathlib's `IsMonHom`.

It has no free data fields. Checked against the standard statement (Milne 1986, Prop. 6.1,
UNVERIFIED number):
- the factorization through a unique **homomorphism** is harmless, because a pointed morphism of
  abelian varieties is a homomorphism (rigidity);
- `IsCurve` (proper, `SmoothOfRelativeDimension 1`, geometrically connected) is the standard
  notion; smoothness and geometric connectedness give geometric integrality;
- genus 0 is covered: `J = Spec K` is an `AbVar`, and every pointed map `ℙ¹ → A` is constant.

So `JacobianExists K` (Weil; Chow; Milne 1986 Thm 1.1) is the published existence theorem, not
stronger. The predicate encodes nothing about `V_ℓ(J)`, so R16 stated as "for every `J` with
`IsJacobian` …" is not a disguised conclusion. The blueprint's own warning is right: the main
theorem must take `JacobianExists` as an explicit hypothesis, and MC10 (a rational base point) is
needed to apply it.

### 2.3 Finding M1: leaf MC9 is over an undefined object, and unnecessary

MC9 ("`ℚ`-isomorphism between the `K_N` model and Shimura's canonical model") is listed as a leaf
(§3, §4, §6, §10 item 2). The blueprint never defines Shimura's canonical model, so as a Lean
leaf it would be stated over an undefined object. It is also not needed. Every clause of the
existential R16 except the surjection `π : J ↠ A` concerns `A` alone. So the conclusion
transfers along any isomorphism `J ≅ J'` of group objects (`exists_quotient_transfer`, which
assumes `[IsMonHom e.inv]`; VERIFIED compiled), in
particular between the Jacobians of `ℚ`-isomorphic models.

The `ℚ`-isomorphism of the `K_N` model with Shimura's model is a classical fact that belongs to
R16's citation chain (Shimura 1971 Ch. 6; Diamond–Im §9.3; UNVERIFIED locators). It is not a
Lean statement.

### 2.4 Repairs (exact text)

1. §0 item 2, fourth bullet. Replace "transported to our model of `X₁(N)` by the leaf MC9
   (ℚ-isomorphism with Shimura's canonical model)" by: "stated directly for our model of
   `X₁(N)`. The passage from Shimura's canonical model belongs to the citation chain: a
   `ℚ`-isomorphism of curves induces an isomorphism of Jacobians, and the existential form is
   invariant under it (rv-blueprints `exists_quotient_transfer`)."
2. §4, row MC9. Replace the status "leaf (found missing by review)" by: "not a Lean leaf
   (Shimura's canonical model is not defined here). It is a fact of R16's citation chain;
   R16 is stated for the `K_N` model." In §3, change "MC9 [leaf]" to "MC9 [citation chain]".
3. §6, last sentence of the boxed statement. Replace "Shimura's theorem is about his canonical
   model, so this form uses leaf MC9." by: "Shimura's theorem is about his canonical model. Its
   transfer to the `K_N` model is part of the citation chain, and in Lean it is the glue
   `exists_quotient_transfer`."
4. §10 item 2. Replace "Using R16 for our `J` needs a `ℚ`-isomorphism between the two curves (or
   their Jacobians): **leaf MC9**." by: "Using R16 for our `J` needs a `ℚ`-isomorphism between
   the two curves, as a citation-chain fact; no Lean leaf is needed."
5. (Recommendation, not a soundness repair.) State MC5' and R18 with `g := dim J`, where `J` is
   the Jacobian of MC6. Riemann–Hurwitz becomes `2 dim J − 2 = d − n₀ − n₁ − n_∞`, a consequence
   of Riemann–Hurwitz and `dim Jac = genus`. This avoids defining the genus through `Ω¹`, which
   Mathlib lacks for schemes, and makes MC6'' a citation-chain fact.

## 3. bp-qmmoduli

### 3.1 Where the proof uses the canonical model, the Hecke action and reciprocity

Checked against N5 L405-545 (read) and h-trust A1-A10, with h-b1 §§1.2-3 and rv-h-cm §7.2 (read).

| Step | Canonical model (`ℚ`-structure) | Hecke action `Γ'` | Reciprocity | Field points enough? |
| --- | --- | --- | --- | --- |
| A3 | `Γ'` acts over `ℚ` with quotient `P¹_j` | yes (degree `≤ |Γ'| = 144`) | no | yes: R1hecke + R2fp. The generic fibre is a `Γ'`-orbit |
| A4 | the object over the residue field `κ(x)` | no | no | yes: R1fp. `K₃` is neat, so objects are rigid and the field points are a bijection |
| A5, Prop. TS | the function field `M = ℚ(Y^{(1)})` and `π` | `M/ℚ(j)` is Galois (h-b1 M2) | no | yes. h-b1 §1.2 uses only `M`, the normalization of `P¹_R` in `M`, the branch values and Lemma NV. No integral model of `Y₃` |
| A5, Lemma NV step 2 | residue fields at the points over `b_i` | fibres are `Γ'`-orbits | **yes**: CM points of level 3 | yes, with R1rec, and with **R2fp's CM clauses as biconditionals** (Q5): "every point over `b_i` is CM by the maximal order" is M9, done there by the analytic enumeration of elliptic elements |
| A5, Lemma NV step 4 | `X₆ → P¹_j` is a geometrically connected `W`-cover (h-b1 M10) | `W` | `π₀` | yes, but it needs a **`π₀` clause** (Q4); no listed leaf gives it |
| A6 | `A[3] ⊂ A(K)` | no | no | yes (`QML3.goodReduction`, VERIFIED compiled) |
| A7 | `σx` lies in the fibre of `x` because `π` is defined over `ℚ` | the fibre is one `Γ'`-orbit, and `Γ'` changes only `(ι, η)` | no | yes: R1fp naturality for `σ ∈ Aut(ℚ̄/ℚ)` + R2fp |
| A10 (rv-h-cm §7.2) | the `ℚ`-model `ℚ(t)(√−t, √(3(t−1)))` of `X₆`; residue fields `ℚ(x)` | `W` | **yes**: the constants, and González–Rotger's fields | yes, but only with **R5 in the strength of Thm 5.12** (Q2) |
| F1 | none | none | none | **no**: it needs the complex uniformization as a **family** (Q3) |

Twist conventions checked here (SPECULATIVE to STANDARD; the adelic computation is my own):
- A global normalizer element `w` acts by `(A, ι, η) ↦ (A, ι∘Ad(w), η∘Ad(w))`. This is the
  blueprint's `twist`.
- An inner twist by `u ∈ 𝒪^×` equals `rightMul u⁻¹`, through the isomorphism `ι(u)⁻¹`.
- `𝒪^× → (𝒪/3𝒪)^×` is onto (Eichler's norm theorem and strong approximation).
- So "`∃ α u`" in R2fp covers `Γ'`.

### 3.2 Findings

- **Q1 (the scope of the verdict).** N5 as printed **does** use `Y₃` as a moduli scheme over a
  base. L444-478 apply Buzzard's theorem to `V₁(5)` over `ℤ[1/30]`, add the finite étale sheaf
  `Isom_𝒪(𝒪/3𝒪, A[3])`, and descend the universal abelian scheme. L529-530 conclude: "The proper
  model and its universal abelian scheme give good reduction outside the places over S." The
  blueprint's verdict holds for the **h-trust route**, which replaces L443-530 by h-b1's Prop. TS
  and A6 by the Raynaud route. The blueprint says this inside item 1 but states the verdict
  without the qualification.
- **Q2 (R5fp is too weak for A10).**
  - Case `D(R) ≠ 1` of rv-h-cm §7.2 uses `k ⊆ ℚ(x)`, which R5fp's degree form
    (`[ℚ(x):ℚ] ∈ {h, 2h}`) does not give.
  - Counterexample to sufficiency: `R = 𝒪_{ℚ(√−19)}`. Here `h = 1`, and 2 and 3 are inert, so
    `b = 2` and there are 4 CM points, as many as a free `W`-orbit. `ℚ(x) = ℚ(√−19)` has degree
    2, the same as the fibre field `ℚ(i)`. So neither the degree nor the count excludes `x`;
    only `ℚ(√−19) ⊄ ℚ(i)` does.
  - Step 2 of the same proof (the twist constants of the `t`-model) also needs the exact fields
    over `t = 1` and `t = ∞` (`ℚ(i)` and `ℚ(√−3)`). These follow from the containment clause
    together with the degree.
  - Repair: `R5fpStrong` (compiled, `R5Repair.lean`). For `b ≥ 1`, `[ℚ(x):ℚ] = 2·#Pic R` and
    `k ↪ ℚ(x)`. For `b = 0`, `[ℚ(x):ℚ] = #Pic R`.
  - It is a consequence of González–Rotger Thm 5.12 (`ℚ(x) = H_R` if `D(R) ≠ 1`, `[H_R:ℚ(x)] = 2`
    otherwise) and `[H_R:k] = #Pic R`. It needs no ring class fields in the statement.
  - `R5fp_of_R5fpStrong` is proved.
- **Q3 (R1an is too weak for F1).**
  - R1an as written gives, for each `P` separately, a `τ` with `P.A(ℂ) ≅ ℂ²/ι(𝒪)(τ,1)ᵀ`. The
    glue "two holomorphic Hauptmoduln of `Γ*∖ℍ` with the same values at three points coincide"
    needs more:
    - (b) every `τ ∈ ℍ` occurs, i.e. the polarized torus is `P_τ.A(ℂ)` for some `P_τ` over `ℂ`;
    - (c) `τ ↦ π(Φ⁻¹[P_τ])` is holomorphic on `ℍ`.
  - Neither follows from statements at each point.
  - With (b) and (c), `π ∘ u` is a holomorphic bijection `Γ*∖ℍ → P¹` (by R2fp's fibre clause).
    Then `j_θ∘Ω∘(π∘u)⁻¹` is a Möbius map fixing `0, ∞, −16/27`, hence the identity.
  - (b) and (c) are consequences of Shimura 1967, Main Thm I, and Deligne 1971 §4.15 (analytic
    families). Locators UNVERIFIED.
- **Q4 (`π₀` is missing).**
  - h-b1 Lemma NV step 4 uses h-b1 M10: `X₆ → P¹_j` is a geometrically connected `W`-Galois
    cover, whose inertia generators are distinct and nontrivial.
  - A10 step 2 uses the same fact: the shape `ℚ(t)(√(at), √(b(t−1)))` is forced only for a
    geometrically connected `(ℤ/2)²`-cover branched at the three points.
  - None of R1fp, R1hecke, R2fp, R1rec or R5fp gives `π₀(X₆_ℚ̄) = 1`.
  - Repair: add **R1pi0**, "`ℚ` is algebraically closed in `ℚ(Y)^H`, where `H` is the image of
    `rightMul`". This is the function field of `X₆`. It follows from Deligne 1971 §2:
    `π₀(Sh_{K₀}) = ℚ^×_{>0}∖𝔸_f^×/nrd(K₀) = 1` (UNVERIFIED locator).
  - It is consistent with the blueprint's own computation `π₀(Y₃) = 2` (§2.1), which I
    re-derived: `nrd(1 + 3𝒪₃) = 1 + 3ℤ₃`.
  - Alternative to a new leaf (SPECULATIVE sketch, not checked in detail): derive `π₀ = 1` as
    glue.
    - The generic fibre of `X₆ → P¹` is a free `W`-orbit of 4 points.
    - The fibre over each of `0, ∞, −16/27` has 2 points: `#CM(R) = 2^b h(R) = 2` for the three
      orders, by R5fpCount, with existence given by Q5.
    - Four components of degree 1 would give 4 points over `0`.
    - Two components of degree 2 would each be ramified over all three values. That is
      impossible, because a quadratic extension `ℚ̄(j)(√f)` is branched at an even number of
      points (Kummer theory).
    - Either route is acceptable. The blueprint must contain one of them.
- **Q5 (R2fp's CM clauses must be biconditionals).**
  - Lemma NV step 2 (through h-b1 M9) needs "every point over `b_i` is CM by the maximal order of
    discriminant −4, −3, −24".
  - R2fp states only `HasCM4 → π = 0` (etc.), and `R5fpCount` is guarded by "`∃ P` with
    `com P ≅ R`". So no field-point leaf gives the converse, or even the existence of these CM
    points.
  - The biconditional is true. `com ⊇ ℤ[i]` forces `com = ℤ[i]`, and the fibre over `0` is a
    single `Γ'`-orbit. It is a consequence of Baba–Granath's identification of the three
    elliptic points with these CM points (Thm 2.1 and the §3 datum).
  - Existence then follows from the surjectivity of `π`.
- **§2.2 (a polarization is determined by `(A, ι)`).** The argument is sound.
  - Uniqueness is as in h-trust A4 item 2.
  - The lattice core is compiled (`eq_smul_E0`, `eq_pm_E0_of_principal`, inside the audited
    file).
  - The sign claim is VERIFIED numerically here (`sheet_check.py`, 30 random complex structures
    `J`, `J² = −1`). `x ↦ E₀(xJ, x)` is negative definite on the sheet `c > 0`, with eigenvalues
    in `[−50.8, −0.028]`, and positive definite on `c < 0`, with eigenvalues in `[0.063, 46.7]`.
  - Existence over a general field of characteristic 0 needs the Lefschetz principle to reach
    `ℂ`. That is STANDARD.

### 3.3 Repairs (exact text)

1. §0, first line. Replace "**The argument never uses the moduli scheme `Y₃` over a general
   base.**" by: "**The h-trust route (h-b1's Prop. TS for A5, the Raynaud route for A6) never
   uses the moduli scheme `Y₃` over a general base.** N5 as printed does (L443-530: Buzzard's
   integral moduli scheme over `ℤ[1/30]`, its universal abelian scheme and stable models). The
   field-point leaves serve the h-trust route."
2. §0 item 4 and §2.4. Replace "R1fp + R1hecke + R2fp + R1rec + R5fp" by "R1fp + R1hecke + R1pi0
   + R2fp (biconditional CM clauses) + R1rec + R5fpStrong".
3. §1 table.
   - Row A5 (Lemma NV): add to the substitute "+ R1pi0 (h-b1 M10, step 4) + R2fp's biconditional
     CM clauses (h-b1 M9, step 2)".
   - Row A10: replace "**R5fp**" by "**R5fpStrong** (rv-blueprints `R5Repair.lean`; the degree
     form R5fp does not suffice)".
   - Row F1: replace "**R1an**" by "**R1an** in family form (every `τ` occurs; `τ ↦ π(P_τ)`
     holomorphic)".
4. §2.3, R2fp. Replace the three implications `(∃ φ ∈ com P, …) → π(Φ⁻¹[P]) = c` by
   biconditionals `↔`.
5. §2.3, R5fp. Replace the degree disjunction by `R5fpStrong`:
   `(1 ≤ b → [ℚ(x):ℚ] = 2·#Pic R ∧ Nonempty (k →ₐ[ℚ] ℚ(x))) ∧ (b = 0 → [ℚ(x):ℚ] = #Pic R)`.
6. §2.3, new statement after R1rec (or the glue sketch of Q4 in its place): "R1pi0 (Deligne 1971 §2, UNVERIFIED locator): for `H` the
   image of `rightMul`, `ℚ` is algebraically closed in `ℚ(Y)^H`, i.e. `X₆ = Y/H` is geometrically
   connected."
7. §2.3, R1an. Append: "(b) for every `τ ∈ ℍ` there are `P_τ : QML3 ℂ` and such an isomorphism;
   (c) `τ ↦ π(Φ⁻¹[P_τ]) ∈ P¹(ℂ)` is holomorphic on `ℍ`. The Hauptmodul comparison uses (b) and
   (c)."

## 4. Compile and axiom audit (VERIFIED)

Method:
- Each blueprint file was copied to `scratch/rv-blueprints/Audit_<name>.lean`, with
  `audit_tail.lean` appended.
- The appended command runs `Lean.collectAxioms` on every declaration the file adds
  (`env.constants.map₂`) and reports any axiom outside `propext`, `Classical.choice`,
  `Quot.sound`.
- The runner `run_audit.sh` compiles the files one after another, one Lean process at a time.
- Outputs are in `scratch/rv-blueprints/audit_out/`.

| File | Exit | Errors | Warnings | `sorry` | Declarations | Non-standard axioms |
| --- | --- | --- | --- | --- | --- | --- |
| bp-faltings/Hodge | 0 | 0 | 0 | 0 | 125 | none |
| bp-faltings/Models | 0 | 0 | 0 | 0 | 40 | none |
| bp-modcurves/Gamma1Genus | 0 | 0 | 0 | 0 | 44 | none |
| bp-modcurves/TateNormalForm | 0 | 0 | 0 | 0 | 12 | none |
| bp-modcurves/Jacobian | 0 | 0 | 0 | 0 | 38 | none |
| bp-modcurves/ModularCurveDefs | 0 | 0 | 0 | 0 | 20 | none |
| bp-modcurves/AnalyticModuli | 0 | 0 | 0 | 0 | 16 | none |
| bp-modcurves/PointTransport | 0 | 0 | 0 | 0 | 70 | none |
| bp-qmmoduli/QMOrder | 0 | 0 | 21 (linter) | 0 | 81 | none |
| bp-qmmoduli/Units72 | 0 | 0 | 0 | 0 | 7 | none |
| bp-qmmoduli/QMAbVar | 0 | 0 | 9 (linter) | 0 | 176 | none |

- `QMAbVar` imports the prebuilt kernel module `ZInQKernel.HDecomp.A6.A6`.
- Its A6 theorem takes the leaves (`NeronOggShafarevich`, `RaynaudCriterion`, `TorsionStructure`)
  as explicit hypotheses, not as axioms.
- The warnings are unused-tactic and deprecation linters only.
- The leaf `Prop`s (`JacobianExists`, `R5fp`, `R5fpCount`, `PeriodAreaFormula`, `FieldX1Degree`,
  …) are definitions, not assumptions, and none is used as an axiom.

Review files (compiled, standard axioms only):

| File | Content |
| --- | --- |
| `Normalizations.lean` | `log_two_pi_sq_lt_three`, `bost_F_of_D`, `log_pi_lt_three`, `faltings_le_deligne`, `faltings_kappa_le` |
| `R5Repair.lean` | a copy of `QMAbVar.lean` minus its `#print axioms` block, plus `R5fpStrong` and `R5fp_of_R5fpStrong` |
| `R16Transfer.lean` | `exists_quotient_transfer` (over bp-modcurves' `AbVar` copy) |

## 5. Not checked

- Primary sources: Javanpeykar §2.3, Gaudron–Rémond's normalization, Bost, Faltings' Lemma 5,
  González–Rotger Thm 5.12, Baba–Granath, Shimura, Deligne and BLR were not read here (no
  network). Their content is taken from `locators.md` and h-decomposition. Locators recalled
  here are UNVERIFIED.
- The uncompiled signatures of the blueprints (bp-faltings `Models.lean` comment block,
  bp-modcurves §9, bp-qmmoduli R1fp/R1hecke/R2fp/R1rec) were reviewed as mathematics only.
- Not reviewed for statement faithfulness: AT2's genus-2 formula, and the cost estimates of all
  three blueprints (SPECULATIVE there).
