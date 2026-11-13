# fs5-nocm: FS5 `FibreComTrivial` (NoCM on the fibre) proved, with the repaired QM clauses, from the leaves and three named Props

Task fs5-nocm, 2026-11-13. Base 2dd83306, merged with `origin/wip/qm-pin` and
`origin/wip/mobius-glue` (`origin/wip/g0-fibresimple` was already in the base). Lean:
`scratch/fs5-nocm/FS5NoCM.lean` and `scratch/fs5-nocm/FS5Curves.lean`, assembled from the parts
`part0`, `partB`, `partD`, `partE`, `partE2` by `assemble.sh`. Results log:
`scratch/fs5-nocm/log.md`. No file under `ZInQKernel/`, `blueprint/` or another task's directory
was edited. This is model work with no human review.

## 1. Result

**Main result (VERIFIED, compiled).** g0-fibresimple's glue piece FS5 is proved in Lean. It is read
with qm-pin's full repair of `R1fpProps` and is otherwise verbatim. The inputs are the QM leaf
bundle, the leaf R5fpCount, qm-pin/mobius-glue's `MobiusGlue`, and three named Props:

```lean
theorem FS5NoCM.fibreComTrivialFull_of (hL : R1R2fpFull) (hM : MobiusGlue)
    (hA : ComIntOrQuadOrder) (hB : CMConductorCoprime6) (hK : X6KummerFibre)
    (hC : R5fpCount) : FibreComTrivialFull

-- the same with MobiusGlue replaced by mobius-glue's inputs (FS5Curves.lean):
theorem FS5NoCM.fibreComTrivialFull_of_curves (hL : R1R2fpFull) (hRF : CurveRatFactor)
    (hSu : CurveSurj) (hT : ObjBridge.TorsionStructure) (hA : ComIntOrQuadOrder)
    (hB : CMConductorCoprime6) (hK : X6KummerFibre) (hC : R5fpCount) : FibreComTrivialFull
```

The proof has two steps, as the task asked.

1. **FS5 for the leaf's own triple.** `fibreComTrivialOwn_of : … → FibreComTrivialOwn` is NoCM
   (rv-h-cm §7.2 with rv-nocm's corrected count `2^b h`). It is stated for every witness
   `(Y, Φ, X, Ψ, fY, π₆)` of the repaired bundle, not for a `Classical.choice` of one, so it is a
   statement about the published data.
2. **Transfer to every triple.** `fibreComTrivialFull_of_own : R1R2fpFull → MobiusGlue →
   FibreComTrivialOwn → FibreComTrivialFull` uses qm-pin's `pointwise_of_witness_mor`. The CM
   objects it needs come from the bundle (`cm_objects_of_R1R2fp`).

Every `#print axioms` gives `[propext, Classical.choice, Quot.sound]`. `lake env lean` exits 0 for
both files: 7.6 s and 11.8 s (`run1.txt`, `run2.txt`).

**Verdict on the statement.**

- With the repaired clauses, FS5 is **true and now provable glue**. Its universal quantifier over
  triples costs only `MobiusGlue`, as qm-pin predicted.
- The un-repaired FS5 (old `R1fpProps`) is kept in the file for reference. It is not a
  consequence of the leaves (g0-fibresimple §2).
- After the integration of qm-pin's full edit, the two texts coincide.

### Named Props

| name | kind | content | source / status |
|---|---|---|---|
| `R1R2fpFull` | leaf bundle (existing) | `LeafQM.AV.R1R2fp` with qm-pin's repaired `R1fpProps`: R1fp + R1fam + R1univ, R1hecke, `X6Props`, `R2X6Props` (Baba–Granath), `CMExists`, `R1recProps`, `X6Surj`, `R5ptProps` (González–Rotger Thm 5.12, point form) | qm-pin §2 (text checked equal to `QM-Leaves-full.patch`) |
| `R5fpCount` | leaf (existing, kernel) | `#CM(R) = 2^{b(k)} h(R)` | González–Rotger Prop. 5.6; Jordan 1981 |
| `MobiusGlue` | glue (existing) | `π' = π ∘ g` for two triples related by `Φ' = Φ ∘ g` | proved by mobius-glue from `CurveRatFactor`, `CurveSurj` (curve glue) and T5 |
| **N1a `ComIntOrQuadOrder`** | glue (new) | `End_𝒪(A)` is `ℤ`, or is isomorphic to a subring of finite index of `𝒪_k`, `k` imaginary quadratic | from T27 (Yu's dichotomy, `PkgI3.QMDichotomyYu`), FS4's centralizer argument and T6. Not compiled |
| **N1b `CMConductorCoprime6`** | leaf (new) | if `End_𝒪(A) ≅ R`, an order of `k`, then `(f(R), 6) = 1` | Eichler's local optimal-embedding numbers (Vignéras LNM 800, Ch. II §3 / Ch. III §5) with the CM-point/optimal-embedding correspondence (Jordan 1981 §3; González–Rotger 2006 §5). Locators UNVERIFIED |
| **N2 `X6KummerFibre`** | glue (new) | on the bundle's `X₆`, for rational `j₀ ∉ {0, −16/27}`: (i) every point over `j₀` has residue field `ℚ(√−t₀, √(3(t₀−1)))`, `t₀ = 1 + 27j₀/16`; (ii) the fibre has four distinct `ℚ̄`-points | Elkies' Kummer model of `X₆ → X₆/W` (rv-h-cm §2.3-2.4, `GlueRepo.PR.fibre_iff`), plus transport to an arbitrary witness (§3.3). Not compiled |

What was **proved here**, not assumed (all compiled):

- the Elkies identities in `ℚ̄`: `elkies_sq`, from the kernel's `GlueRepo.PR.t_eq` and `t_sub_one`;
- `ℚ(iH/G³, 540iF/G³) = ℚ(i)` (`adjoin_pair_eq`, using `h₁_ne_zero`);
- `[ℚ(i) : ℚ] = 2` (`finrank_adjoin_sqrt_neg_one`);
- 2 is not inert in a number field containing `√−1` (`two_not_prime_of_sqrt_neg_one`), which
  gives `b(k) ≤ 1` when `k ≅ ℚ(i)`;
- the count: four distinct classes with CM by `R`, from N2 (ii), `R2X6Props`, `com_twist` and
  `comEquiv`, against `#CM(R) = 2`;
- the case analysis on `b(k)` with R5's degree and embedding clauses;
- the transfer from the leaf's witnesses to all triples.

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
- In `FS5Curves.lean` the same block comes from `MobiusGlue.lean`. The definitions are identical
  to the qm-pin copies (checked).

**FS5 for the leaf's own triple** (`FibreComTrivialOwn`). For every witness
`(Y, Φ, X, Ψ, fY, π₆)` with `R1R2fpFullProps` (the clause list of the repaired bundle), every
object over `J(u)`, `u ∉ 𝒞`, of the triple `(Y, Φ, π₆ ∘ fY)` has `com = ℤ`.

**The three new named Props.** Full docstrings are in `partB.lean` §C. N1a and N1b quantify over
QM pairs over `ℚ̄`. N2 quantifies over the witnesses of the repaired bundle:

```lean
def ComIntOrQuadOrder : Prop :=
  ∀ P : QMPair Qbar, (∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : AbVar.End P.A)) ∨
    ∃ (k : Type) (_ : Field k) (_ : NumberField k) (_ : NumberField.IsTotallyComplex k),
      Module.finrank ℚ k = 2 ∧ ∃ R : Subring k, R ≤ (integralClosure ℤ k).toSubring ∧
        conductor R ≠ 0 ∧ Nonempty (com P.q ≃+* R)

def CMConductorCoprime6 : Prop :=
  ∀ (P : QMPair Qbar) (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 → ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring →
      conductor R ≠ 0 → Nonempty (com P.q ≃+* R) → Nat.Coprime (conductor R) 6

def X6KummerFibre : Prop :=
  ∀ Y Φ X Ψ fY π₆, R1R2fpFullProps Y Φ X Ψ fY π₆ →
    ∀ j₀ : ℚ, j₀ ≠ 0 → j₀ ≠ -16 / 27 →
      (∀ x : fieldPt Qbar ⟶ X, π₆.val (K := Qbar) x.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
        ∀ a b : Qbar, a ^ 2 = -algebraMap ℚ Qbar (1 + 27 * j₀ / 16) →
          b ^ 2 = 3 * (algebraMap ℚ Qbar (1 + 27 * j₀ / 16) - 1) →
          residueImage (X := X.left) x.left = IntermediateField.adjoin ℚ {a, b}) ∧
      ∃ f : Fin 4 → (fieldPt Qbar ⟶ X), Function.Injective f ∧
        ∀ i, π₆.val (K := Qbar) (f i).left = OnePoint.some (algebraMap ℚ Qbar j₀)
```

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

### 3.3 Why the new Props are true (arguments; SPECULATIVE where not marked)

- **N1a (glue).** Over `ℚ̄` in characteristic 0, T27 gives two cases.
  - *`End⁰(A) ≅ B`.* The QM image of `B` is all of `End⁰` (dimension 4, injective). The centralizer
    is the centre `ℚ`, and `com = End(A) ∩ ℚ = ℤ`, because endomorphisms are integral over `ℤ`.
  - *`End⁰(A) ≅ M₂(k)`.* `B ⊗ k ≅ M₂(k)`, so the centralizer of `B` is the centre `k` (FS4's
    argument, compiled by g0-fibresimple as `centralizerOfMatrixEnd0_of_homFree`). `com` is a
    lattice in `k` (T6) of integral elements, hence an order.
  - The inputs are T27, T6 and the integrality of endomorphisms (the characteristic polynomial,
    Mumford §19 Thm 4, UNVERIFIED). None of this is compiled: it needs the field `k` and the order
    to be built as Lean objects from the isomorphism of T27.
- **N1b (leaf).** Two published facts give it.
  - Eichler's local optimal-embedding number at a prime `p` ramified in `B` is
    `m_p(R) = 1 − {R/p}`. The Eichler symbol `{R/p}` equals `(k/p)` if `p ∤ f`, and 1 if `p | f`.
    So for `p | 6`, `p | f` gives `m_p = 0` (Vignéras Ch. II §3 / Ch. III §5, theorem numbers
    UNVERIFIED).
  - CM points with `End_𝒪(A) ≅ R` correspond to optimal embeddings `R ↪ 𝒪` modulo `𝒪^×`
    (Jordan 1981; González–Rotger 2006 §5).
  - Consistency: the same numbers give R5fpCount's `2^b h(R)`, with `m_p = 2` for `p` inert and 1
    for `p` ramified. `R5fp`'s hypothesis `(f, 6) = 1` is the same condition, and rv-nocm checked
    it on Elkies' 24 rows.
- **N2 (glue).** The genuine part is Elkies' Kummer model: `ℚ(X₆) = ℚ(t)(y₁, y₂)` with
  `y₁² = −t`, `y₂² = 3(t − 1)`, and `W` acting by sign changes.
  - The constants `−1, 3` are rv-h-cm §2.3's. rv-nocm §1.3 checked them against González–Rotger
    Thm 5.12 on all 24 rational CM values.
  - The cover is branched only at `t = 0, 1, ∞`, each with index 2. Riemann–Hurwitz gives genus 0,
    as it should for `X₆`.
  - Over `t₀ ∉ {0, 1, ∞}`, the affine model is smooth, so it is the curve there. The points over
    `t₀` are `(t₀, ±a, ±b)`: four points, since `ab ≠ 0`. Each has residue field `ℚ(a, b)`.

  N2 is stated for an arbitrary witness of the repaired bundle. It transfers from the genuine
  `X₆` as follows:
  - qm-pin's `phi_part` and `MobiusGlue` give `g : Y → Y₃` with `Φ = Φ₃ ∘ g` and `π = π₃ ∘ g`;
  - `fY` is onto `X(ℚ̄)` (`X6Surj`), and `Ψ(fY y) = [forget Φ(y)]` (`X6Props`);
  - so `π₆(x)` depends only on the pair `Ψ(x)`, the same way as on the genuine `X₆`, and the fibre
    over `j₀` consists of the same four classes;
  - the residue field of a `ℚ̄`-point is the fixed field of its Galois stabilizer (STANDARD), and
    the Galois-equivariance in `X6Props` makes that stabilizer the stabilizer of the pair, which
    does not depend on the witness.

  This transport is argued, not compiled. N2 does not hold for the old clause list, by the same
  relabeling as g0-fibresimple §2.

## 4. What compiles (all VERIFIED)

| file | content | outcome |
|---|---|---|
| `FS5NoCM.lean` (~520 lines) | qm-pin block, §B statements, §C named Props, §D arithmetic, §E `nocm_on_witness`, `fibreComTrivialOwn_of`, `fibreComTrivialFull_of_own`, `fibreComTrivialFull_of` | exit 0, 0 errors, no `sorry`; 7 `#print axioms` lines, all standard (`run1.txt`) |
| `FS5Curves.lean` (~2000 lines) | `MobiusGlue.lean` (lines 1-1439, plus two imports) + qm-pin's `cm_objects_of_R1R2fp` + the same §B-§E + `fibreComTrivialFull_of_curves` | exit 0, 0 errors; `fibreComTrivialFull_of_curves` standard axioms (`run2.txt`) |

Kernel modules used: `ZInQKernel.HDecomp.QM.Leaves`, `ZInQKernel.HDecomp.Repo.PRArith`,
`ZInQKernel.Hypotheses.JHeight` (and `ZInQKernel.HDecomp.Textbook.SkolemNoether` for
`FS5Curves`). They were built with `lake build`.

## 5. Integration (not applied: these are other tasks' files)

1. **After qm-pin's full edit of `QM/Leaves.lean`.**
   - `R1fpPropsFull` is `R1fpProps`, `R1R2fpFull` is `R1R2fp`, and `FibreComTrivialFull` is
     g0-fibresimple's `FibreComTrivial` verbatim.
   - Drop §B's copies, `r1fpPropsFull_iff` and `R1fpPropsFull.old` (then `h.1`, the identity).
   - Put §C-§E in a new module importing `QM.Leaves`, `Repo.PRArith`, `JHeight` and qm-pin's
     `QM/Pin.lean`.
2. **In g0-fibresimple's `FibreSimplePieces`.**
   - Replace the field `comTrivial : FibreComTrivial` by the inputs of `fibreComTrivialFull_of`.
   - The bundle and `R5fpCount` are already in `QMLeaves` (`r1r2`, `r5count`).
   - `MobiusGlue` comes from mobius-glue's `mobiusGlue_of_curves` (`CurveRatFactor`, `CurveSurj`,
     T5).
   - The new named Props are N1a and N2 (glue) and N1b (leaf).
3. **Leaf list.** Add N1b `CMConductorCoprime6` (Eichler/Vignéras with Jordan/González–Rotger).
   Add N1a and N2 to the glue list.

## 6. What remains

- **N1a** (glue). This is linear algebra on T27's output plus integrality of endomorphisms. The
  Lean cost is constructing `k` and the order from `End⁰(A) ≅ M₂(ℚ(√d))`.
- **N2** (glue). There are two parts:
  - the Kummer model of `X₆ → P¹`, i.e. an explicit equation for a curve given only by its moduli
    clauses. This is the main geometric input and is not statable more concretely without an
    explicit model of `X₆` in the leaves;
  - the transport to an arbitrary witness, which needs the scheme fact "residue field = fixed field
    of the point's Galois stabilizer" and qm-pin's comparison.
- **N1b** (leaf). The locators are UNVERIFIED (no network). A human check of the
  optimal-embedding correspondence is advisable, as it was for R5.
- `MobiusGlue`'s inputs (`CurveRatFactor`, `CurveSurj`) remain mobius-glue's open curve glue.
