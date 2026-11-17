## 5. Re-sourcing R2 to `Y₃ → P¹_j` (scope only; not done)

**What the two `X₆` fields give today** (VERIFIED by reading TailZ70/TailZ75 docstrings, TailZ21, GRX6AbPrint.lean):

| field | statement (short) | feeds |
|---|---|---|
| `x6CoarseModuliIdeal` | `X₆ = X₀(6,1)` over `ℚ` is a coarse moduli scheme of QM pairs: proper smooth curve, `Ψ : X₆(ℚ̄) ≃ {QM pairs}/≅` Galois-natural, Atkin–Lehner `w_m` in ideal-quotient form, classifying maps of level-3 families over proper smooth curves | the `X₆` witness `(X, Ψ, fY)` of the moduli row (`X6Props`), via `GRX6AbPrint.x6ModuliWitness_of_coarse` with `shimuraMainThmIDeligneY3AbU` |
| `elkiesX6StarEveryIdeal` | Elkies §3: on every witness, some `t : X₆ → P¹` with `ℚ(X₆)^W = ℚ(t)`, CM values `t = 0, 1, ∞` at discriminants `−24, −4, −3`, charts `s² = −t`, `r² = 3(t − 1)` | `π₆` and `R2X6PropsIff` (fibres of `π₆` = `W`-orbits, CM values), `X6Surj`, through `elkiesX6StarPrinted` / `babaGranathRationalAb` |

The consumers read the row through `LeafQM.AV.R1R2fp_Y`: `(Y, Φ, π := π₆ ∘ fY)` with `R1fpProps`, `R1heckeProps`,
`R2fpProps` (fibres of `π` on `Y₃(ℚ̄)` = `Aut 𝒪`-twist classes, values `0, ∞, −16/27` at the CM points `−4, −3, −24`),
plus the conjuncts listed by the clause scan (§5.1).

**The manuscript's route** (L421-441): the normalizer `N` of `𝒪̂` acts on the level-3 curve `Y₃` (all determinant
components) through `N/(𝔸_f^× K₃)`, the quotient is `P¹_j` with branch values `0, ∞, −16/27` and indices `4, 6, 2`
(`[babagranath, linyang]`, L420-422), and `deg(Y₃ → P¹_j) ≤ 4·|(𝒪/3𝒪)^×| ≤ 324`; the integral model comes from
Buzzard Thm 2.1 / Cor. 2.3 applied to `V₁(5)` over `ℤ[1/30]` (L444-470). `X₆` never appears.

**What a re-source needs.**

1. *From y3-route-a* (Buzzard Thm 2.1/Cor 2.3 as the manuscript cites, L444): the fine moduli scheme `Y₃` over `ℚ`
   (and `ℤ[1/30]`) with its universal QM abelian scheme and full level-3 structure, i.e. the content of the current
   research field `y3FineModuliAbP` (`R1fpPropsAbP`), in the printed form. This replaces the `Y₃` half of the witness;
   it does not give `π`.
2. *Beyond y3-route-a*:
   - (a) **the normalizer action on `Y₃`** by `ℚ`-automorphisms inducing the twists `α ∈ Aut 𝒪` and the right
     multiplications `u ∈ 𝒪^×` on points: this is `R1heckeProps`, already in the row and proved in the tree
     (`heckeOfFine_proof`, from the fine moduli property);
   - (b) **the quotient `Y₃/G` by a finite group of automorphisms** as a proper smooth curve with `(Y₃/G)(ℚ̄) =
     Y₃(ℚ̄)/G` (textbook leaf: Mumford, *Abelian varieties* §7 Thm 1, or SGA 1 Exp. V Prop. 1.8 with normality ⇒
     smoothness of a curve in characteristic 0; not in Mathlib; locators UNVERIFIED);
   - (c) **the identification `Y₃/N ≅ P¹_j`** with the stated branch values: the manuscript cites Baba–Granath and
     Lin–Yang (L420-422). Baba–Granath state it for `X₆/W` (the tree's `babaGranathRationalAb`, Baba–Granath §3);
     to avoid `X₆` one needs either `Y₃/N = X₆/W` (which is the forgetful map, i.e. `X₆` again) or Lin–Yang's form:
     the polarized moduli point of the fibre as a function of `j`, `[J₂ : J₄ : J₆ : J₁₀] = [12(j+1) : 6(j²+j+1) :
     4(j³−2j²+1) : j³]` (L544-547; the tree has `LeafPush2.LinYangTuple`, `linYang_j_eq`), which defines
     `π : Y₃ → P¹` directly from the Igusa invariants of the universal family;
   - (d) **the fibre clause of `R2fpProps`** on `Y₃` (same `π`-value ⇔ `Aut 𝒪`-twist-equivalent QM pairs): from (b)
     and (c) with Baba–Granath's polarized equivalence relation `V_ℤ = V/W` (L534-537) — or, on the Lin–Yang route,
     Igusa's theorem that `[J₂:…:J₁₀]` determines the principally polarized surface plus "isomorphic ppav ⇒ twist
     equivalent" (Baba–Granath);
   - (e) **surjectivity of `π` on `ℚ̄`-points** (the first half of `X6Surj`, used to choose a fibre over `J(u)`, A4):
     immediate from (b) (a non-constant map of proper curves);
   - (f) **the CM existence clause** `CMExists` (three CM points with the given values): the clause scan (§5.1) says
     which conjuncts of the row are read on the CM-branch route.
3. *What would leave the route*: `x6CoarseModuliIdeal` and `elkiesX6StarEveryIdeal` (and `babaGranathRationalAb`'s
   `X₆` form, `rayClassCMAb` if only used for `X₆`), replaced by (b), (c) (Lin–Yang or Baba–Granath on `Y₃/N`) and
   (d). Net: two GLUE fields out, at least two new leaves in ((b) textbook, (c) printed), plus the glue for (d) unless
   (c)'s print states the fibre clause. **Not a net GLUE gain by itself**; its value is following the manuscript
   (no `X₆` at all, L421-441) rather than the count.
