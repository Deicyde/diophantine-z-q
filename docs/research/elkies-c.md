# elkies-c: Elkies' CM values at every CM point, proved from the CM point of each discriminant

Task elkies-c, 2026-11-17/18. Base `wip/x6-coarse` 0dc0c1fa with `origin/main` (5c7d9ba7) merged. Contribution:
`ZInQKernel/Contrib/OneProof/ElkiesX6StarCM.lean` (namespace `ElkiesC`, imports `X6AtkinLehnerIdeal`, the module
that defines `ElkiesX6StarEveryIdeal`, plus `R5fpCountLe` and the helper below) and the helper
`ZInQKernel/Contrib/OneProof/ElkiesC/ClassNumber24.lean` (the closed facts for `ℚ(√−6)`). Working files and logs:
`scratch/elkies-c/`. No other file under `ZInQKernel/` or `blueprint/` was edited. Model work, no human review.

Marks: **VERIFIED** = compiled, computed, or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a locator recalled without a source (no network on this host).

## 1. Main result

(STATUS: see §6; this section is final only when §6 says compiled.)

**Step (c) of the Elkies row and the reviewer's `HasCM` step are proved glue.** The CM clause of
`X6ALIdeal.ElkiesX6StarEveryIdeal` (x6-coarse) and of the bundle field `ElkiesPrint.ElkiesX6StarEvery` says: at
**every** `ℚ̄`-point `x` whose QM pair has `HasCM24` (resp. `HasCM4`, `HasCM3`), `t(x) = 0` (resp. `1`, `∞`). Elkies
prints the value at **the** CM point of each discriminant of `X*(6)`. The new leaf `ElkiesC.ElkiesX6StarOneIdeal`
keeps every other clause verbatim and states the CM clause in the weakest printed reading: **some** point with
`HasCM_D` has that value. From it and the three textbook fields (`uniformizationLeafAll`, `gagaMorphism`,
`mumfordTorsionAlgClosed`, all three proved in the tree by contributions) the old leaf follows:

```lean
theorem ElkiesC.elkiesX6StarEveryIdeal_of_one (h : ElkiesX6StarOneIdeal) (hU : UniformizationLeafAll)
    (hG : GAGAMorphism) (hM : MumfordTorsionAlgClosed) : X6ALIdeal.ElkiesX6StarEveryIdeal
theorem ElkiesC.elkiesX6StarEvery_of_one_twist (h : ElkiesX6StarOneIdeal) (hX : GRX6AbPrint.X6CoarseModuli)
    (hY : ShimuraMainThmIDeligneY3AbU) (hU) (hG) (hM) : ElkiesPrint.ElkiesX6StarEvery
```

The proof, for each of the three discriminants `D = −24, −4, −3` (`R_D = ℤ[√−6], ℤ[i], ℤ[ζ₃]`):

1. **Exactness (the reviewer's deciding step).** `HasCM_D P.q → End_𝒪(A) ≅ R_D` (`com_equiv_of_rel`): on the
   lattice model of `P_ℂ` (gr56-prove's `datQ`), the root `φ` acts by a scalar `c`, `c` is an eigenvalue
   `ι(x)v = cv` of some `x ∈ 𝒪` (`exists_O`), `x` satisfies the same quadratic relation, and `y ↦ x` is an optimal
   embedding of `𝓞_k = ℤ[y]` (its preimage of `𝒪` is integral since `𝒪` is, `isIntegral_of_mem_O`, and contains
   `ℤ[y]`; `𝓞_k = ℤ[y]` is rayclass-cft's `ringOfIntegersGen_*`). `GR56.com_equiv_of_eig` then gives
   `End_𝒪 ≅ 𝓞_k`. With the converse (`hasRel_of_com_equiv`): `hasCM24_iff_com`, `hasCM4_iff_com`, `hasCM3_iff_com`;
   with gr-dict's dictionary: `hasCM24_iff_isGRCMPoint` etc. (the `HasCM_D` points are González–Rotger's CM points
   by `R_D`, i.e. Elkies' CM points of discriminant `D`).
2. **At most two points** (`cm_le_two_*`): `EichlerBound.r5fpCountLe_proof` gives `#CM(R) ≤ 2^{b(k)} h(R)`; for
   `ℤ[i]`, `ℤ[ζ₃]` this is `2·1` (Pi0X6's `inertCount6_K4/K3`, `pic_R4/R3`); for `ℤ[√−6]` it is `1·h ≤ 2`, from the
   new `ElkiesC.ClassNumber24` (§3).
3. **Galois stability** (`hasRel_galPt`): the Galois clause of `X6Props`, the uniqueness of base change
   (`ShimuraSplit.bc_uniquePair`) and `End_𝒪` of x6-coarse's base change `bcAut σ` (via `endBC`).
4. **The conjugate is another point** (`moved_of_val`): at a point over `t = 0`, `1`, `∞`, Elkies' charts give a
   coordinate with square `−3`, `−1`, `−3` in the residue field (`r² = 3(t − 1)`, `s² = −t`, and `b² = 3(1/t − 1)`
   on the chart at `∞`), so some `σ ∈ Aut(ℚ̄/ℚ)` moves the point (`Pi0X6.galPt_eq_self_iff`).
5. **Conclusion** (`every_of_one_core`): with `x₀` the printed point and `σ` as in 4, the points `x`, `x₀`, `σx₀`
   all have `HasCM_D`, so two of them coincide by 1–2; `x₀ ≠ σx₀`, and `t(σx₀) = σ(t(x₀)) = t(x₀)` since the value
   is rational (`Pi0X6.val_galPt`). So `t(x) = t(x₀)`.

The stabilizer route of the task statement (each elliptic point index occurs once, p. 17) is not used: it needs the
`W`-action on CM points and the branch locus of `X → X/W`, neither of which the tree has. The counting route uses
only proved pieces plus `h(ℤ[√−6]) ≤ 2`, which is proved here.

## 2. The new leaf

```lean
def ElkiesC.ElkiesX6StarOneIdeal : Prop :=
  ∀ Y Φ X Ψ fY, R1fpPropsAb Y Φ → X6Props Y Φ X Ψ fY → ALIdealClause X Ψ →
    ∃ t : ToP1 X.left,
      (∀ (_ : IsIntegral X.left) (hη : genericPoint X.left ∈ t.U),
        fixedByWIdeal Ψ = (Subfield.closure {X.left.presheaf.germ t.U _ hη t.f} : Set X.left.functionField)) ∧
      ((∃ x P, Ψ x = ⟦P⟧ ∧ HasCM24 P.q ∧ t.val x.left = some 0) ∧
       (∃ x P, Ψ x = ⟦P⟧ ∧ HasCM4 P.q ∧ t.val x.left = some 1) ∧
       (∃ x P, Ψ x = ⟦P⟧ ∧ HasCM3 P.q ∧ t.val x.left = ∞)) ∧
      X6Glue.ElkiesCharts X t
```

**Rating: not printed form (consequence), one step closer to it than `ElkiesX6StarEveryIdeal`.** Its CM clause is now
a direct consequence of the printed value at the CM point of `X*(6)` (the existential is witnessed by any point
over Elkies' CM point, whose surface has `End_𝒪 ≅ R_D ∋ √−6, i, ζ₃`). It asserts nothing at the other `HasCM_D`
points: that passage is the proved glue of §1. The remaining consequence step is (a), `ℚ(X/W) = ℚ(X)^W` (the
function-field clause), which is with another worker. The CM clause is read through the moduli interpretation, as
in every `X₆` leaf (Shimura 1967; locators UNVERIFIED). Converse: `one_of_everyIdeal` (the old leaf implies the new
one given `CMExists` on every witness), so the new leaf is not stronger than the old one.

## 3. `h(ℚ(√−6)) ≤ 2` and the other closed facts for `ℚ(√−6)` (`ElkiesC.ClassNumber24`)

All for `K24 = ℚ(s6)` (`ShimuraGlue.Ray.K24`, `s6 = √−6` in `ℚ(ζ₂₄)`), `𝓞 = ℤ[√−6]`:

| statement | proof |
|---|---|
| `discr_K24 : discr K24 = −24` | basis `{1, √−6}` (`basis24`, from `ringOfIntegersGen_K24`), traces `2, 0, −12` |
| `p2_sq : 𝔭₂² = (2)`, `p3_sq : 𝔭₃² = (3)`, `p2_mul_p3 : 𝔭₂𝔭₃ = (√−6)` | `𝔭₂ = (2, √−6)`, `𝔭₃ = (3, √−6)`, explicit generators |
| `eq_p2`, `eq_p3` | an ideal of norm 2 (3) is prime, contains `2` (`3`), hence `√−6`, hence `𝔭₂` (`𝔭₃`), same norm |
| `minkowski_lt_four` | Minkowski's bound `(4/π)·(2/4)·√24 = 2√24/π < 4` |
| `classGroup_mem`, `card_classGroup_le_two` | Mathlib's `exists_ideal_in_class_of_norm_le`: each class is `[(1)]`, `[𝔭₂]` or `[𝔭₃] = [𝔭₂]⁻¹ = [𝔭₂]` |
| `pic_R24_le_two`, `pic_R24_ne_zero` | `ClassGroup.equivPic` |
| `inertCount6_K24 : inertCount6 K24 = 0` | `(2)`, `(3)` not prime: `√−6 ∉ (p)`, `(√−6)² ∈ (p)` |
| `conductor_R24 = 1` | `relIndex_self` |

(`h = 2` exactly is true but only `≤ 2` is needed.)

## 4. Discharges and fold

(filled in §6 when run.)

## 5. Leaf and glue table, with ratings

| statement | kind | rating | reason |
|---|---|---|---|
| `ElkiesX6StarOneIdeal` | consequence (replaces `elkiesX6StarEvery`) | **not printed form** | step (a) `ℚ(X/W) = ℚ(X)^W` remains a consequence step; the CM clause is now the printed value at one CM point per discriminant (weakest reading) |
| everything else in `ElkiesX6StarCM.lean`, `ElkiesC/ClassNumber24.lean` | glue | proved | — |

## 6. Status of the checks

(to be filled)
