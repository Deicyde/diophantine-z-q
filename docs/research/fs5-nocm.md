# fs5-nocm: FS5 `FibreComTrivial` (NoCM on the fibre) proved, with the repaired QM clauses, from leaves, one new leaf and one named glue Prop

Task fs5-nocm, 2026-11-13. Base 2dd83306, merged with `origin/wip/qm-pin` and
`origin/wip/mobius-glue` (`origin/wip/g0-fibresimple` was already in the base).

- Lean: `scratch/fs5-nocm/FS5NoCM.lean` and `scratch/fs5-nocm/FS5Curves.lean`, assembled from the
  parts `part0`, `partB`, `partD`, `partE`, `partG`, `partH`, `partI`, `partE2` by `assemble.sh`.
- Results log: `scratch/fs5-nocm/log.md`.
- No file under `ZInQKernel/`, `blueprint/` or another task's directory was edited.
- Model work only, no human review.

## 1. Result

**Main result (VERIFIED, compiled).** g0-fibresimple's glue piece FS5 is proved in Lean. The
statement is verbatim, with `R1fpProps` read as after qm-pin's full repair. Its inputs are:

- leaves: the repaired QM leaf bundle, R5fpCount, T27 (Yu), T6 (Mumford), and one new leaf N1b′
  `CMOptimalEmbedding`. N1b′ is Shimura's description of CM points: `End_𝒪(A) ≅ φ⁻¹(𝒪)` for an
  embedding `φ : k → B`;
- glue: one new named glue Prop N2, and mobius-glue's `MobiusGlue` (itself proved from
  `CurveRatFactor`, `CurveSurj` and T5).

```lean
-- FS5NoCM.lean
theorem FS5NoCM.fibreComTrivialFull_of_leaves'' (hL : R1R2fpFull) (hM : MobiusGlue)
    (t27 : PkgI3.QMDichotomyYu) (t6 : PkgI3.HomFreeFinite) (hE : CMOptimalEmbedding)
    (hK : X6KummerFibre) (hC : R5fpCount) : FibreComTrivialFull

-- FS5Curves.lean (MobiusGlue replaced by mobius-glue's inputs)
theorem FS5NoCM.fibreComTrivialFull_of_curves_leaves' (hL : R1R2fpFull)
    (hRF : CurveRatFactor) (hSu : CurveSurj) (hT : ObjBridge.TorsionStructure)
    (t27 : PkgI3.QMDichotomyYu) (t6 : PkgI3.HomFreeFinite) (hE : CMOptimalEmbedding)
    (hK : X6KummerFibre) (hC : R5fpCount) : FibreComTrivialFull
```

The variants `fibreComTrivialFull_of_leaves'` and `fibreComTrivialFull_of_curves_leaves` take
N1b `CMConductorCoprime6` in place of N1b′. N1b is the conductor statement itself, sourced to
Eichler's optimal-embedding theory. It is a possible alternative leaf; N1b′ is closer to a
printed statement.

**Structure of the proof.**

1. **FS5 for the leaf's own triple** (`fibreComTrivialOwn_of`). This is NoCM: rv-h-cm §7.2 with
   rv-nocm's corrected count `2^b h`. It is stated for every witness `(Y, Φ, X, Ψ, fY, π₆)` of the
   repaired bundle, not for a `Classical.choice` of one. It uses an intermediate Prop
   `ComIntOrQuadOrder` (N1a), `CMConductorCoprime6` (N1b) and the glue N2.
2. **Transfer to every triple** (`fibreComTrivialFull_of_own`). This is qm-pin's
   `pointwise_of_witness_mor`, given `MobiusGlue` and the CM objects of the bundle.
3. **N1a is proved, not assumed** (`comIntOrQuadOrder_of_leaves`). By T27 at `B = (2,−3)`,
   `End⁰(A) ≅ B` or `≅ M₂(ℚ(√d))`, and both cases are compiled from T6:
   - **`End⁰ ≅ B`** (`com_int_of_end0_quat`): `End_𝒪(A) = ℤ`.
   - **CM case** (`comOfMatrixEnd0_of_homFree`): `End_𝒪(A)` is isomorphic to a subring of finite
     index of `𝒪_k`, where `k = ℚ(√d)` is shown in Lean to be a totally complex quadratic number
     field.
4. **N1b is proved from the leaf N1b′** (`cmConductorCoprime6_of`). If `R = φ⁻¹(𝒪)`, then
   `p ∤ [𝒪_k : R]` for `p = 2, 3` (`not_dvd_conductor_of_optimal`):
   - otherwise Cauchy's theorem in `𝒪_k/R` gives `y ∉ R` with `p y ∈ R`;
   - `φ(y)` has the minimal polynomial of `y`, which has integer coefficients, so `nrd φ(y) ∈ ℤ`;
   - `φ(p y) = ofInt v` then has `p² ∣ nrd`, which forces `p ∣ v` (N5's `𝒪` is the set of integral
     elements of `B_p`: finite checks modulo 4 and 9 by `decide`, `check2`, `check3`);
   - so `φ(y) ∈ 𝒪` and `y ∈ R`, a contradiction.

Every `#print axioms` gives `[propext, Classical.choice, Quot.sound]` (20 lines in `run1.txt`, 3 in
`run2.txt`). `lake env lean` exits 0: `FS5NoCM.lean` (1390 lines) in 24 s, and `FS5Curves.lean`
(2684 lines) in 25 s.

**Verdict on the statement.**

- With the repaired clauses, FS5 is **true, and is now proved from leaves (one of them new, N1b′)
  plus two pieces of glue** (N2 and `MobiusGlue`).
- The un-repaired FS5 (old `R1fpProps`) is kept in the file for reference. It is not a
  consequence of the leaves (g0-fibresimple §2).
- After qm-pin's full edit is integrated, the two texts coincide.

### Named Props

| name | kind | content | source / status |
|---|---|---|---|
| `R1R2fpFull` | leaf bundle (existing) | `LeafQM.AV.R1R2fp` with qm-pin's repaired `R1fpProps`: R1fp + R1fam + R1univ, R1hecke, `X6Props`, `R2X6Props` (Baba–Granath), `CMExists`, `R1recProps`, `X6Surj`, `R5ptProps` (González–Rotger Thm 5.12, point form) | qm-pin §2 (text checked equal to `QM-Leaves-full.patch`) |
| `R5fpCount` | leaf (existing, kernel) | `#CM(R) = 2^{b(k)} h(R)` | González–Rotger Prop. 5.6; Jordan 1981 |
| T27 `PkgI3.QMDichotomyYu` | leaf (existing, kernel) | `End⁰(A) ≅ B` or `M₂(ℚ(√d))`, `d < 0` | Yu, JPAA 2013, Thm 1.1 |
| T6 `PkgI3.HomFreeFinite` | leaf (existing, kernel) | `Hom(A, B)` is a free `ℤ`-module of finite rank | Mumford §19 Thm 3 |
| `MobiusGlue` | glue (existing) | `π' = π ∘ g` for two triples related by `Φ' = Φ ∘ g` | proved by mobius-glue from `CurveRatFactor`, `CurveSurj` (curve glue) and T5 |
| N1a `ComIntOrQuadOrder` | glue (new), **proved** | `End_𝒪(A)` is `ℤ` or ≅ a subring of finite index of `𝒪_k`, `k` imaginary quadratic | `comIntOrQuadOrder_of_leaves` from T27, T6 |
| N1a-CM `ComOfMatrixEnd0` | glue (new), **proved** | the CM case of N1a | `comOfMatrixEnd0_of_homFree` from T6 |
| N1b `CMConductorCoprime6` | **proved** from N1b′ (or usable as an alternative leaf) | if `End_𝒪(A) ≅ R`, an order of an imaginary quadratic `k`, then `(f(R), 6) = 1` | `cmConductorCoprime6_of`; as a leaf: Eichler's local optimal-embedding numbers (Vignéras LNM 800, Ch. II §3 / Ch. III §5) |
| **N1b′ `CMOptimalEmbedding`** | **leaf (new)** | if `End_𝒪(A) ≅ R` (an order of `k`), then `R = φ⁻¹(𝒪)` for some `ℚ`-embedding `φ : k → B` | Shimura, Ann. of Math. 85 (1967); Jordan 1981 §3; González–Rotger 2006 §5 (`End_𝒪(A_τ) ≅ φ_τ(k) ∩ 𝒪`), transported to the given `k`. Locators UNVERIFIED |
| **N2 `X6KummerFibre`** | **glue (new)** | on the bundle's `X₆`, for rational `j₀ ∉ {0, −16/27}`: (i) every point over `j₀` has residue field `ℚ(√−t₀, √(3(t₀−1)))`, `t₀ = 1 + 27j₀/16`; (ii) the fibre has four distinct `ℚ̄`-points | Elkies' Kummer model of `X₆ → X₆/W` (rv-h-cm §2.3-2.4, `GlueRepo.PR.fibre_iff`), plus transport to an arbitrary witness (§3.3). Not compiled |

**What was proved here** (all compiled):

- **NoCM arithmetic.**
  - The Elkies identities in `ℚ̄` (`elkies_sq`, from the kernel's `GlueRepo.PR.t_eq` and
    `t_sub_one`).
  - `ℚ(iH/G³, 540iF/G³) = ℚ(i)` (`adjoin_pair_eq`) and `[ℚ(i) : ℚ] = 2`
    (`finrank_adjoin_sqrt_neg_one`).
  - 2 is not inert in a number field containing `√−1` (`two_not_prime_of_sqrt_neg_one`).
  - The four-element count against `#CM(R) = 2`, and the case analysis on `b(k)`
    (`nocm_on_witness`).
- **Transfer** to all triples (`fibreComTrivialFull_of_own`).
- **N1b from N1b′** (`cmConductorCoprime6_of`, `not_dvd_conductor_of_optimal`, `dvd_of_sq_dvd_Qf`,
  `check2`, `check3`, `nrd_ofInt`).
- **N1a, case `End⁰ ≅ B`** (`com_int_of_end0_quat`):
  - the QM image of `B` is all of `End⁰` (g0-fibresimple's `qmBasis`; an injective map of
    4-dimensional spaces);
  - so `1 ⊗ φ` is central, and the centre of `ℍ[ℚ,2,−3]` is `ℚ` (`B6_central_eq`);
  - `φ` is integral over `ℤ` (`End(A)` is finite over `ℤ`, T6), so the scalar is an integer;
  - `m ↦ 1 ⊗ m` is injective (`tmul_one_injective`, T6).
- **N1a, CM case** (`comOfMatrixEnd0_of_homFree`):
  - `ℚ[X]/(X² − d)`, `d < 0`, is a totally complex quadratic number field
    (`adjRoot_numberField`).
  - A matrix commuting with `I, J ∈ M₂(K)` with `I² = 2`, `J² = −3`, `JI = −IJ` is scalar
    (`commute_quat_scalar`: `1, I, J, IJ` is a `K`-basis).
  - `φ ↦ (scalar of e(1 ⊗ φ))` is an injective ring map `ψ : End_𝒪(A) → k`.
  - Its image consists of integral elements (T6). It contains `1` and `s√d` with `s ≠ 0` (FS4's
    localization step). So it has rank 2 in `𝒪_k`, hence finite index
    (`Submodule.finiteQuotientOfFreeOfRankEq`).

## 2. Statements (namespace `FS5NoCM`; kernel definitions from `LeafQM.AV`)

**FS5, verbatim from g0-fibresimple** (`FibreComTrivial`; old `R1fpProps`). A Python comparison
with `scratch/g0-fibresimple/FibreSimple.lean` confirms the text is identical (VERIFIED).

**FS5 with the repaired clauses** (`FibreComTrivialFull`). This is the same text with `R1fpProps`
replaced by `R1fpPropsFull`. `R1fpPropsFull` is character for character the body of the patched
`R1fpProps` in `scratch/qm-pin/QM-Leaves-full.patch`, lines 63-70 (VERIFIED by string comparison):

```lean
def FibreComTrivialFull : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpPropsFull Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (y : fieldPt LeafQM.AV.Qbar ⟶ Y) (P : QML3 LeafQM.AV.Qbar), Φ LeafQM.AV.Qbar y = M3.mk P →
      π.val (K := LeafQM.AV.Qbar) y.left = OnePoint.some (algebraMap ℚ LeafQM.AV.Qbar (Jmap u)) →
      ∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End P.A)
```

`r1fpPropsFull_iff` shows `R1fpPropsFull ↔ R1fpPropsU` (qm-pin's name).

**Which definitions the names refer to.** The kernel definitions the statement uses are textually
identical to the copies in `FibreSimple.lean` (VERIFIED by string comparison): `R1fpProps`,
`R2fpProps`, `X6Props`, `R2X6Props`, `CMExists`, `X6Surj`, `R5ptProps`, `R5fpCount`, `com`,
`residueImage`, `inertCount6`, `conductor`, `QML3`, `QMPair`, `ToP1`, `ToP1.val`, `fieldPt`,
`PtEquiv`, `M3` and `QMStr`.

- `Jmap` is `ZInQ.JHeight.Jmap` and `contactSet` is `ZInQ.contactSet`.
- The qm-pin block (`QMFamily` … `cm_objects_of_R1R2fp`) is `QMPin.lean` lines 34-95 and 507-619,
  verbatim.
- In `FS5Curves.lean` the same block comes from `MobiusGlue.lean`. Its definitions are identical
  to the qm-pin copies (checked).
- g0-fibresimple's proved `B6_isUnit` … `qm_embeds_end0` are `olean/Tail.lean` lines 40-116,
  verbatim (checked).

**FS5 for the leaf's own triple** (`FibreComTrivialOwn`). For every witness
`(Y, Φ, X, Ψ, fY, π₆)` with `R1R2fpFullProps` (the clause list of the repaired bundle), every
object over `J(u)`, `u ∉ 𝒞`, of the triple `(Y, Φ, π₆ ∘ fY)` has `com = ℤ`.

**The new named Props.** Full docstrings are in `partB.lean` §C and `partG.lean`:

```lean
def ComIntOrQuadOrder : Prop :=            -- N1a, proved (comIntOrQuadOrder_of_leaves)
  ∀ P : QMPair Qbar, (∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : AbVar.End P.A)) ∨
    ∃ (k : Type) (_ : Field k) (_ : NumberField k) (_ : NumberField.IsTotallyComplex k),
      Module.finrank ℚ k = 2 ∧ ∃ R : Subring k, R ≤ (integralClosure ℤ k).toSubring ∧
        conductor R ≠ 0 ∧ Nonempty (com P.q ≃+* R)

def CMConductorCoprime6 : Prop :=          -- N1b, proved from N1b′ (cmConductorCoprime6_of)
  ∀ (P : QMPair Qbar) (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 → ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring →
      conductor R ≠ 0 → Nonempty (com P.q ≃+* R) → Nat.Coprime (conductor R) 6

def X6KummerFibre : Prop :=                -- N2, glue
  ∀ Y Φ X Ψ fY π₆, R1R2fpFullProps Y Φ X Ψ fY π₆ →
    ∀ j₀ : ℚ, j₀ ≠ 0 → j₀ ≠ -16 / 27 →
      (∀ x : fieldPt Qbar ⟶ X, π₆.val (K := Qbar) x.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
        ∀ a b : Qbar, a ^ 2 = -algebraMap ℚ Qbar (1 + 27 * j₀ / 16) →
          b ^ 2 = 3 * (algebraMap ℚ Qbar (1 + 27 * j₀ / 16) - 1) →
          residueImage (X := X.left) x.left = IntermediateField.adjoin ℚ {a, b}) ∧
      ∃ f : Fin 4 → (fieldPt Qbar ⟶ X), Function.Injective f ∧
        ∀ i, π₆.val (K := Qbar) (f i).left = OnePoint.some (algebraMap ℚ Qbar j₀)
```

```lean
def CMOptimalEmbedding : Prop :=           -- N1b′, leaf (partI.lean)
  ∀ (P : AV.QMPair AV.Qbar) (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 → ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring →
      AV.conductor R ≠ 0 → Nonempty (AV.com P.q ≃+* R) →
        ∃ φ : k →ₐ[ℚ] B, R = O.comap φ.toRingHom
```

(`ComOfMatrixEnd0`, the CM case of N1a, is stated in `partG.lean` and proved in `partH.lean`.
`B`, `O` in N1b′ are `LeafQM.B = ℍ[ℚ,2,−3]` and N5's maximal order `LeafQM.O`.)

## 3. The proof

### 3.1 NoCM on a witness (`nocm_on_witness`)

Let `y` be a `ℚ̄`-point of `Y` over `J(u)` with object `P`, let `x = fY(y)`, and let
`Ψ x = [P.forget]` (`X6Props`).

1. **Setup.** If `com P.q` is not `ℤ`, N1a gives `com P.q ≅ R ⊆ 𝒪_k` with `k` imaginary quadratic,
   and N1b gives `(f(R), 6) = 1`. So `R5ptProps` applies at `x`:
   - `[ℚ(x) : ℚ] = (b = 0 ? 1 : 2) · h(R)`;
   - if `b ≥ 1`, then `k ↪ ℚ(x)`.
2. **Residue field.** `J(u) ≠ 0, −16/27` (`GlueRepo.PR.J_ne_zero`, `J_ne_branch`). By N2 (i) with
   `a = iH/G³`, `b = 540iF/G³` (`elkies_sq`), `ℚ(x) = ℚ(a, b) = ℚ(i)`, which has degree 2.
3. **Four classes with CM by `R`.** N2 (ii) gives four distinct points `x_j` over `J(u)`. Their
   classes `Ψ x_j` are distinct, since `Ψ` is a bijection. Each is an `Aut(𝒪)`-twist of `P.forget`
   (the fibre clause of `R2X6Props`), so each has `com ≅ com P.q ≅ R` (`comEquiv`, `com_twist`).
   So the set `CM(R)` of R5fpCount contains four elements.
4. **`#CM(R) = 2`.**
   - If `b = 0`: `h = 2` and `#CM(R) = 2⁰ · 2 = 2`.
   - If `b ≥ 1`: `h = 1`, and `k ↪ ℚ(i)` is onto (equal degrees), so `k` contains `ι` with
     `ι² = −1`. Then 2 is not inert in `k` (`two_not_prime_of_sqrt_neg_one`), so `b = 1` and
     `#CM(R) = 2¹ · 1 = 2`.
5. **Contradiction.** Since `#CM(R) = 2 ≠ 0`, the set is finite, so it cannot contain four
   distinct elements. Hence `com P.q = ℤ`.

This is rv-h-cm §7.2 in the form rv-nocm §1.1 repaired. The case `D(R) ≠ 1` is closed by the
count, as rv-nocm suggests, and not by locating `x` over `t = 1`. The example `D = −19` (`b = 2`,
`h = 1`, degree 2) is excluded by `k ↪ ℚ(i)`, which is why R5 needs its embedding clause.

### 3.2 Transfer (`fibreComTrivialFull_of_own`)

This is qm-pin's `pointwise_of_witness_mor`, applied as follows:

- the witness triple is `(Y₀, Φ₀, π₆ ∘ fY)`, with `R1fpPropsU` from `r1fpPropsFull_iff` and
  `R2fpProps` from `R2fpProps_of_X6`;
- the relation is `R(t, P) = ∀ u ∉ 𝒞, t = J(u) → com P.q = ℤ`;
- `MobiusGlue` is assumed, and the CM objects come from `cm_objects_of_R1R2fp`.

### 3.3 Why the remaining new Props are true (arguments; SPECULATIVE where not marked)

- **N1b′ (leaf).** For `(A, ι)` over `ℂ` with CM, `A = ℂ²/𝒪v_τ`.
  - `End_𝒪(A)` is the set of `b ∈ B^op` preserving `𝒪v_τ` and commuting with the complex
    structure, i.e. `𝒪^op ∩ k_τ`. The canonical involution identifies `B^op ≅ B` and preserves
    `𝒪`, so `End_𝒪(A) ≅ φ_τ(k) ∩ 𝒪`.
  - Given an abstract `R ≅ End_𝒪(A)` inside `k`, the isomorphism extends to fraction fields
    `σ : k ≅ k_τ` (`R` has rank 2), and `φ = φ_τ ∘ σ` has `φ⁻¹(𝒪) = R`.
  - Characteristic 0 transfers the statement from `ℂ` to `ℚ̄`. Argued; locators UNVERIFIED.
- **N1b (now proved from N1b′; as an alternative leaf).** Two published facts give it.
  - Eichler's local optimal-embedding number at a prime `p` ramified in `B` is
    `m_p(R) = 1 − {R/p}`. The Eichler symbol `{R/p}` equals `(k/p)` if `p ∤ f`, and 1 if `p | f`.
    So for `p | 6`, `p | f` gives `m_p = 0` (Vignéras Ch. II §3 / Ch. III §5, theorem numbers
    UNVERIFIED).
  - CM points with `End_𝒪(A) ≅ R` correspond to optimal embeddings `R ↪ 𝒪` modulo `𝒪^×`
    (Jordan 1981; González–Rotger 2006 §5).
  - Consistency: the same numbers give R5fpCount's `2^b h(R)`, with `m_p = 2` for `p` inert and 1
    for `p` ramified. `R5fp`'s hypothesis `(f, 6) = 1` is the same condition, and rv-nocm checked
    it on Elkies' 24 rows.
  - The statement is intrinsic: an order determines its conductor up to ring isomorphism, since
    `disc R = f² d_k`.
- **N2 (glue).** The genuine part is Elkies' Kummer model: `ℚ(X₆) = ℚ(t)(y₁, y₂)` with
  `y₁² = −t`, `y₂² = 3(t − 1)`, and `W` acting by sign changes.
  - The constants `−1, 3` are rv-h-cm §2.3's. rv-nocm §1.3 checked them against González–Rotger
    Thm 5.12 on all 24 rational CM values.
  - They are also consistent with `X₆(ℝ) = ∅`: real points would need `t ≤ 0` and `t ≥ 1` at
    once.
  - The cover is branched only at `t = 0, 1, ∞`, each with index 2. Riemann–Hurwitz gives genus 0,
    as it should for `X₆`. The fixed points of `w₂, w₆, w₃` (over `t = 1, 0, ∞`) are the CM points
    of discriminants `−4, −24, −3`.
  - Over `t₀ ∉ {0, 1, ∞}`, the affine model is smooth, so it is the curve there. The `ℚ̄`-points
    over `t₀` are `(t₀, ±a, ±b)`: four points, since `ab ≠ 0`. Each has residue field `ℚ(a, b)`.

  N2 is stated for an arbitrary witness of the repaired bundle. It transfers from the genuine
  `X₆` as follows:
  - qm-pin's `phi_part` and `MobiusGlue` give `g : Y → Y₃` with `Φ = Φ₃ ∘ g` and `π = π₃ ∘ g`;
  - `fY` is onto `X(ℚ̄)` (`X6Surj`), and `Ψ(fY y) = [forget Φ(y)]` (`X6Props`);
  - so `π₆(x)` depends only on the pair `Ψ(x)`, the same way as on the genuine `X₆`, and the fibre
    over `j₀` consists of the same four classes;
  - the residue field of a `ℚ̄`-point is the fixed field of its Galois stabilizer (STANDARD), and
    the Galois-equivariance in `X6Props` makes that stabilizer the stabilizer of the pair. This
    step also needs rigidity: two base changes of a pair are isomorphic as pairs.

  This transport is argued, not compiled.

## 4. What compiles (all VERIFIED)

| file | content | outcome |
|---|---|---|
| `FS5NoCM.lean` (1390 lines) | qm-pin block; §B statements; §C named Props; §D arithmetic; §E NoCM and transfer; §G N1a split (`B6_central_eq`, `com_int_of_end0_quat`, `comIntOrQuadOrder_of`); §H N1a-CM (`commute_quat_scalar`, `adjRoot_numberField`, `root_lin_indep`, `comOfMatrixEnd0_of_homFree`, `comIntOrQuadOrder_of_leaves`, `fibreComTrivialFull_of_leaves'`); §I N1b from N1b′ (`check2`, `check3`, `dvd_of_sq_dvd_Qf`, `not_dvd_conductor_of_optimal`, `cmConductorCoprime6_of`, `fibreComTrivialFull_of_leaves''`) | exit 0, 0 errors, no `sorry`; 20 `#print axioms` lines, all standard (`run1.txt`) |
| `FS5Curves.lean` (2684 lines) | `MobiusGlue.lean` (lines 1-1439, plus imports) + qm-pin's `cm_objects_of_R1R2fp` + §B-§I + `fibreComTrivialFull_of_curves(_leaves)(')` | exit 0, 0 errors; 3 lines, standard axioms (`run2.txt`) |

Kernel modules used: `ZInQKernel.HDecomp.QM.Leaves`, `ZInQKernel.HDecomp.Repo.PRArith`,
`ZInQKernel.Hypotheses.JHeight` and `ZInQKernel.HDecomp.Descent.B1Quat`.
`ZInQKernel.HDecomp.Textbook.SkolemNoether` is used for `FS5Curves` only. All were built with
`lake build`.

**Lean pitfall.** With `letI : Fact (Irreducible f)` in context, the `Field` and `CommRing`
instances of `AdjoinRoot f` do not unify at reducible transparency. As a result `ring`,
`linear_combination` and `rw [map_intCast]` fail on mixed terms. The workaround is to state the
helper lemmas without the `Fact` (`root_lin_indep`, `root_lin_indep_int`) and to pass between the
two forms with `exact` or `rfl`.

## 5. Integration (not applied: these are other tasks' files)

1. **After qm-pin's full edit of `QM/Leaves.lean`.**
   - `R1fpPropsFull` is `R1fpProps`, `R1R2fpFull` is `R1R2fp`, and `FibreComTrivialFull` is
     g0-fibresimple's `FibreComTrivial` verbatim.
   - Drop §B's copies, `r1fpPropsFull_iff` and `R1fpPropsFull.old`.
   - Put §C-§I in a new module importing `QM.Leaves`, `Repo.PRArith`, `JHeight`, `Descent.B1Quat`
     and qm-pin's `QM/Pin.lean`. The Tail copies (`B6_isUnit` … `qm_embeds_end0`) are shared with
     g0-fibresimple's integration.
2. **In g0-fibresimple's `FibreSimplePieces`.**
   - Replace the field `comTrivial : FibreComTrivial` by `fibreComTrivialFull_of_leaves''`.
   - Its inputs are the bundle (`QMLeaves.r1r2`), `R5fpCount` (`QMLeaves.r5count`), T27 and T6
     (`TextbookLeaves`), N1b′, N2, and `MobiusGlue` (from mobius-glue's `mobiusGlue_of_curves`).
3. **Lists.** Add N1b′ `CMOptimalEmbedding` to the leaf list (Shimura; Jordan; González–Rotger).
   Add N2 `X6KummerFibre` to the glue list.

## 6. What remains

- **N2** (glue). There are two parts:
  - the Kummer model of `X₆ → P¹`: an explicit equation for a curve that the leaves give only by
    its moduli clauses. It cannot be stated more concretely without an explicit model of `X₆` in
    the leaves;
  - the transport to an arbitrary witness, which needs the scheme fact "residue field = fixed field
    of the point's Galois stabilizer", rigidity, and qm-pin's comparison.
- **N1b′** (leaf). The locators are UNVERIFIED (no network). A human check of Shimura's
  `End_𝒪(A_τ) ≅ φ_τ(k) ∩ 𝒪`, and of the `B^op` convention, is advisable, as it was for R5.
- `MobiusGlue`'s inputs (`CurveRatFactor`, `CurveSurj`) remain mobius-glue's open curve glue.
