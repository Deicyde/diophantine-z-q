# x6-kummer: N2 `X6KummerFibre` proved from one explicit leaf (the conic model of `X₆`) and the existing `MobiusGlue`; N1b checked

Task x6-kummer, 2026-11-13. Base 322303a2 (`wip/integrate-w39`).

- Lean: `scratch/x6-kummer/X6Kummer.lean` (N2) and `scratch/x6-kummer/N1b.lean` (N1b re-check).
  Both are concatenations of parts: `X6Kummer.lean` = `part0` + `partB` + `partC` + `partR` +
  `partD` + `partE`; `N1b.lean` = `part0` + `partN`.
- Computation: `scratch/x6-kummer/conic_check.py`, output in `conic_check.txt`.
- Results log: `scratch/x6-kummer/log.md`.
- No file under `ZInQKernel/`, `blueprint/` or another task's directory was edited.
- Model work only, no human review.

## 1. Result

**Main result (VERIFIED, compiled).** fs5-nocm's glue Prop N2 `X6KummerFibre` is proved in Lean.
The statement is copied verbatim; a string comparison with `scratch/fs5-nocm/FS5NoCM.lean` gives
identical text. The proof needs two inputs:

- **one new leaf**, `X6ConicModel`. It says that `X₆ = X₀(6,1)` is the conic
  `C : Y² + 3X² + 3Z² = 0`, with `π₆ = −16(X² + Z²)/(27Z²)`, on `ℚ̄`-points of one witness of the
  leaf bundle;
- **the existing curve glue** `LeafQM.AV.Pin.MobiusGlue` from qm-pin. mobius-glue already proved
  it from `CurveRatFactor`, `CurveSurj` and T5.

```lean
theorem X6Kummer.x6KummerFibre_of_conic (hM : MobiusGlue) (hL : X6ConicModel) : X6KummerFibre
```

Everything between the leaf and N2 is proved in this task. That includes a second glue Prop I had
introduced, `PairBaseChangeUnique`, which is proved from pullback uniqueness and mul-rigidity's
`rigidityHom`.

Compile outcome:

- `lake env lean scratch/x6-kummer/X6Kummer.lean` exits 0, with no errors and no `sorry`, in 33 s
  at load about 13.
- All 8 `#print axioms` lines give `[propext, Classical.choice, Quot.sound]` (`run1.txt`).

**Verdict on N2.**

- N2 is **true** and its statement needs no correction.
- N2 is not glue in the strict sense. Its constants `−1, 3` are arithmetic facts about the curve
  `X₆`, and they cannot be derived from the bundle's clause list in Lean. That geometric content
  is now isolated in one explicit, checkable leaf equation. Everything else is compiled: the
  residue fields, the fibre count, and the transport to an arbitrary witness.

**N1b verdict** (§4). `CMConductorCoprime6` is true and is a consequence of published statements.

- Eichler's optimal-embedding theory supplies only the local half: an optimal embedding into the
  maximal order of the ramified `B_p` has conductor prime to `p`. That half is **already proved in
  Lean for the project's order** (fs5-nocm `not_dvd_conductor_of_optimal`, re-compiled here on this
  base).
- The other half cannot come from Eichler's theory: it is the fact that `End_𝒪(A)` *is* an
  optimally embedded order. This is Shimura's description of CM points, fs5-nocm's leaf
  `CMOptimalEmbedding`.
- Recommendation: replace the leaf N1b by `CMOptimalEmbedding` together with the compiled
  `cmConductorCoprime6_of`.

### Named Props

| name | kind | content | status |
|---|---|---|---|
| `X6KummerFibre` (N2) | target, verbatim | residue field `ℚ(√−t₀, √(3(t₀−1)))` and four points over rational `j₀ ∉ {0, −16/27}`, on every witness | **proved** from the two rows below |
| `X6ConicModel` (N2-L′) | **leaf (new)** | one witness of the repaired bundle has a bijection `X(ℚ̄) ≃ C(ℚ̄)` that commutes with `Aut(ℚ̄/ℚ)`, with `π₆ = −16(X²+Z²)/(27Z²)` | Elkies 1998 §3 (the model of `X₆ → X*(6)`); Kurihara 1979 (the conic). Locators UNVERIFIED. Constants independently derived by rv-h-cm §2.3 |
| `MobiusGlue` | glue (existing) | two triples with `Φ' = Φ ∘ g` have `π' = π ∘ g` | qm-pin. Proved by mobius-glue from `CurveRatFactor`, `CurveSurj`, T5 |
| `PairBaseChangeUnique` | glue (new), **proved** | base change of a QM pair along `σ ∈ Aut(ℚ̄/ℚ)` is unique up to `QMIso` | `pairBaseChangeUnique`, from `IsPullback.isoIsPullback` and `rigidityHom` |
| `X6KummerModel` (N2-L) | intermediate, **proved** from N2-L′ | the fibre form: an equivariant bijection between the fibre over `j₀` and the pairs `(a, b)` with `a² = −t₀`, `b² = 3(t₀−1)`, on one witness | `x6KummerModel_of_conic`. It could itself serve as the leaf (the fibre form is a direct consequence of the published model) |
| `X6KummerEquiv` (N2′) | intermediate, **proved** | the fibre form on every witness | `x6KummerEquiv_of_model` |
| `CMConductorCoprime6` (N1b) | leaf (fs5-nocm) | the CM order has conductor prime to 6 | true. **Proved** from `CMOptimalEmbedding` (fs5-nocm, re-compiled here) |

## 2. Statements

**Target (verbatim from fs5-nocm, namespace `FS5NoCM`).**

```lean
def X6KummerFibre : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left), R1R2fpFullProps Y Φ X Ψ fY π₆ →
    ∀ j₀ : ℚ, j₀ ≠ 0 → j₀ ≠ -16 / 27 →
      (∀ x : fieldPt Qbar ⟶ X, π₆.val (K := Qbar) x.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
        ∀ a b : Qbar, a ^ 2 = -algebraMap ℚ Qbar (1 + 27 * j₀ / 16) →
          b ^ 2 = 3 * (algebraMap ℚ Qbar (1 + 27 * j₀ / 16) - 1) →
          residueImage (X := X.left) x.left = IntermediateField.adjoin ℚ {a, b}) ∧
      ∃ f : Fin 4 → (fieldPt Qbar ⟶ X), Function.Injective f ∧
        ∀ i, π₆.val (K := Qbar) (f i).left = OnePoint.some (algebraMap ℚ Qbar j₀)
```

**How the bundle's names resolve.**

- On this base, pin-apply has integrated qm-pin's repair into `ZInQKernel/HDecomp/QM/Leaves.lean`.
  So the names `R1famProps` and `R1univProps` in the copied `R1fpPropsFull` resolve to the
  kernel's, which makes `R1fpPropsFull` the kernel's `R1fpProps` and `R1R2fpFull` the kernel's
  `R1R2fp`. Both identifications are `Iff.rfl` (`r1fpPropsFull_iff_kernel`,
  `r1r2fpFull_iff_kernel`). This is the reading fs5-nocm §5.1 prescribes after integration.
- fs5-nocm's private copies of qm-pin's block do not compile next to the kernel: Lean reports
  `Ambiguous term R1famProps` (VERIFIED). So the kernel module `QM/Pin.lean` (`phi_part`,
  `MobiusGlue`, `cm_objects_of_R1R2fp`) is used instead.

**The new leaf** (`partE.lean`; the full docstring gives sources and checks).

```lean
abbrev ConicPt : Type :=   -- C(ℚ̄): affine part Z = 1, and the points [1 : b : 0] at infinity
  {p : Qbar × Qbar // p.2 ^ 2 + 3 * p.1 ^ 2 + 3 = 0} ⊕ {b : Qbar // b ^ 2 = -3}

def ConicModel (X : Over (Spec (CommRingCat.of ℚ))) (π₆ : ToP1 X.left) : Prop :=
  ∃ e : (fieldPt Qbar ⟶ X) ≃ ConicPt,
    (∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : fieldPt Qbar ⟶ X),
      e (fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x) = conicGal σ (e x)) ∧
    (∀ (x : fieldPt Qbar ⟶ X) p, e x = Sum.inl p →
      π₆.val (K := Qbar) x.left = OnePoint.some (-16 * (p.1.1 ^ 2 + 1) / 27)) ∧
    (∀ (x : fieldPt Qbar ⟶ X) b, e x = Sum.inr b → π₆.val (K := Qbar) x.left = OnePoint.infty)

def X6ConicModel : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left), R1R2fpFullProps Y Φ X Ψ fY π₆ ∧ ConicModel X π₆
```

`conicGal σ` acts coordinatewise.

**The new glue** (`partC.lean`; proved in `partD.lean`).

```lean
def PairBaseChangeUnique : Prop :=
  ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (P Q Q' : QMPair Qbar),
    IsBaseChangeOfPair (σ : Qbar →+* Qbar) P Q → IsBaseChangeOfPair (σ : Qbar →+* Qbar) P Q' →
      Nonempty (QMIso Q.q Q'.q)
```

**The fibre form** (`partB.lean`): `KummerFibreEquiv X π₆`. For rational `j₀ ∉ {0, −16/27}` there
is a bijection `e` from `{x : π₆(x) = j₀}` to `{(a, b) : a² = −t₀, b² = 3(t₀ − 1)}` with
`e(σ·x) = (σ a, σ b)`. `X6KummerModel` is "some witness has it", and `X6KummerEquiv` is "every
witness has it".

## 3. The proof

### 3.1 Residue fields from the Galois action (`partB`, compiled)

- **`galPt_eq_self_iff`.** For `σ ∈ Aut(ℚ̄/ℚ)` and a `ℚ̄`-point `x` of a `ℚ`-scheme:
  `x ∘ Spec σ = x` iff `σ` fixes the residue field image `residueImage x ⊆ ℚ̄` pointwise.
  - A `ℚ̄`-point is a pair `(p, κ(p) ↪ ℚ̄)` (`Scheme.SpecToEquivOfField`).
  - Composing with `Spec σ` keeps `p` and composes the embedding with `σ` (the kernel's
    `specToEquivOfField_comp`).
  - Fixing the generators is the same as fixing the field they generate (`fix_adjoin_iff`, via
    `adjoin_algHom_ext`).
- **`intermediateField_eq_of_fix_iff`.** Two subfields of `ℚ̄` with the same fixing group are
  equal. This is infinite Galois theory, `InfiniteGalois.fixedField_fixingSubgroup`, with
  `IsGalois ℚ ℚ̄` from `IsAlgClosure.isGalois`.

### 3.2 N2 from the fibre form (`x6KummerFibre_of_equiv`, compiled)

**(i) Residue field.**

1. Let `e(x) = (a₁, b₁)`. Then `σ·x` lies in the same fibre (`galPt_mem_fibre`, from
   `ToP1.val_comp`).
2. By the equivariance and injectivity of `e`: `σ·x = x ⟺ (σa₁, σb₁) = (a₁, b₁)`.
3. Since `a₁ = ±a` and `b₁ = ±b` (`fix_iff_of_sq_eq`), this is `σ` fixing `{a, b}`, i.e. fixing
   `ℚ(a, b)`.
4. By §3.1, `residueImage x = ℚ(a, b)`.

**(ii) Four points.** With `a² = −t₀` and `b² = 3(t₀ − 1)`, we have `a, b ≠ 0`, because
`t₀ = 0 ⟺ j₀ = −16/27` and `t₀ = 1 ⟺ j₀ = 0`. So the four pairs `(±a, ±b)` are distinct
(characteristic 0), and `e⁻¹` gives four distinct points.

### 3.3 Transport to every witness (`kummerFibreEquiv_transport`, compiled)

Let `W₀` be the witness of the leaf and `W` any witness, and put `H = Ψ₀⁻¹ ∘ Ψ : X(ℚ̄) ≃ X₀(ℚ̄)`.

- **`π₆ = π₀ ∘ H`.**
  - qm-pin's `phi_part` gives `g : Y → Y₀` with `Φ = Φ₀ ∘ g`.
  - `MobiusGlue`, applied to the triples `(Y₀, Φ₀, π₀ ∘ f₀)` and `(Y, Φ, π₆ ∘ fY)`, gives
    `π₆ ∘ fY = π₀ ∘ f₀ ∘ g` on `ℚ̄`-points. Both triples have `R2fpProps` by `R2fpProps_of_X6`;
    the CM objects come from `cm_objects_of_R1R2fp`.
  - `H ∘ fY = f₀ ∘ g` by the forgetful clause of `X6Props` on both witnesses.
  - `fY` is onto `X(ℚ̄)` (`X6Surj`).
- **`H(σ·x) = σ·H(x)`.**
  - The Galois clause of `X6Props` on both witnesses gives `Ψ(σ·x) = [Q]` and `Ψ₀(σ·Hx) = [Q']`,
    with `Q` and `Q'` both base changes of the same `P` along `σ`.
  - `PairBaseChangeUnique` gives `Q ≅ Q'`.
- **Conclusion.** `e := e₀ ∘ H` restricted to the fibres is the required equivariant bijection.

### 3.4 `PairBaseChangeUnique` (`pairBaseChangeUnique`, compiled)

1. The two pullback squares give an isomorphism `e : Q.A ≅ Q'.A` over `Spec ℚ̄`
   (`IsPullback.isoIsPullback`).
2. `e` commutes with `ι`, and `e` and `e⁻¹` preserve the identity sections. Both are checked after
   composing with the pullback projections (`IsPullback.hom_ext`). The identity `ℚ̄`-point is `η`
   (`one_pt_left`).
3. By rigidity (mul-rigidity's `rigidityHom`, copied verbatim as `partR.lean`), `e` and `e⁻¹` are
   homomorphisms, so they form a `QMIso`.

### 3.5 The fibre form from the conic form (`kummerFibreEquiv_of_conic`, compiled)

A point over a rational `j₀` cannot be at infinity, where `π₆ = ∞`. On the affine part,
`−16(a² + 1)/27 = j₀` is equivalent to `a² = −t₀`, and then `b² = −3a² − 3 = 3(t₀ − 1)`
(`conic_fibre_iff`). Conversely, every root pair `(a, b)` lies on `C`. The equivariance is that of
`e`.

### 3.6 Why the leaf `X6ConicModel` is a consequence of published statements

- **Shape (STANDARD).** `X₆ → X*(6) = X₆/W ≅ P¹` is a `(ℤ/2)²`-cover branched at three points
  `t = 0, 1, ∞` (the CM points of discriminants `−24, −4, −3`), each with inertia one of
  `w₆, w₂, w₃`. Each quadratic subcover `X₆/⟨w⟩` is branched at the two points whose inertia is
  not `⟨w⟩`. So `ℚ(X₆) = ℚ(t)(√(c₀t), √(c₁(t − 1)))` for some `c₀, c₁ ∈ ℚ^×/ℚ^×2`.
- **Constants.** Elkies (ANTS-III 1998, §3, locator UNVERIFIED) gives `(c₀, c₁) = (−1, 3)`. rv-h-cm
  §2.3 derives the same constants without Elkies' table (VERIFIED there by `check.py` part B), from
  Shimura reciprocity (González–Rotger Thm 5.8) at the three elliptic points and `X₆(ℝ) = ∅`.
  rv-nocm §1.3 Part B checked the fibre fields against González–Rotger Thm 5.12 on all 24 rational
  CM points.
- **From the shape to the leaf.** Put `X = √−t`, `Y = √(3(t − 1))`, `Z = 1`. Then
  `Y² + 3X² + 3 = 0` and `j = 16(t − 1)/27 = −16(X² + Z²)/(27Z²)`. This `j` is the coordinate of
  R2fp, since a Möbius map is fixed by its values `0, ∞, −16/27` at `−4, −3, −24`. An isomorphism
  of `ℚ`-schemes gives a Galois-equivariant bijection on `ℚ̄`-points.
- **Checks** (VERIFIED, `conic_check.py`, output in `conic_check.txt`):
  - The involutions `X ↦ −X`, `Y ↦ −Y` and `(X, Y) ↦ (−X, −Y)` fix exactly two points each,
    lying over `j = −16/27`, `0` and `∞` respectively.
  - The residue fields there are `ℚ(√−3)`, `ℚ(i)` and `ℚ(√−3)`. These agree with `R5ptProps`:
    - `ℤ[√−6]`: `b = 0`, `h = 2`, degree 2;
    - `ℤ[i]`: `b = 1`, `h = 1`, and the field must contain `ℚ(i)`;
    - `ℤ[ζ₃]`: `b = 1`, `h = 1`, and the field must contain `ℚ(√−3)`.
  - `C` and Kurihara's `x² + y² + 3 = 0` both have Hilbert symbols `−1` exactly at `3` and `∞`.
    Both correspond to `(−1, −3)_ℚ ≅ (−3, −3)_ℚ`, so they are isomorphic over `ℚ`.
  - Five sample fibres consist of four distinct points on `C` with `π = j₀`.
- **Robustness.** The swap `X ↔ Z` is an automorphism of `C` over `ℚ` that normalizes `W` and
  exchanges the orbits over `∞` and `−16/27`. Under the other assignment of the `−3` and `−24`
  points, the fibre form `KummerFibreEquiv` is therefore unchanged. The fibre form depends only on
  the constants and on the `ℤ[i]` orbit being `Y = 0`, which `R5ptProps` forces (its field is
  `ℚ(i)`).
- **Existential form.** The leaf is existential over the witness, like `LeafQM.AV.R1R2fp`: the
  genuine objects are a witness. It is stronger than the bundle `R1R2fp` (it implies it), so at
  integration it can replace the bundle or sit beside it.
- **The fibre form as an alternative leaf.** `X6KummerModel` would also do as the leaf. It is a
  direct consequence of the same published model and is slightly weaker.

## 4. N1b `CMConductorCoprime6`: check against the sources

**Statement** (fs5-nocm). If `End_𝒪(A) ≅ R` for a subring `R` of finite index in `𝒪_k`, `k`
imaginary quadratic, then `(conductor R, 6) = 1`.

**Truth.** True. The statement is intrinsic: a ring isomorphism `R ≅ R'` extends to the fraction
fields and carries `𝒪_k` to `𝒪_{k'}`, so the conductor is an invariant. When `End_𝒪(A) = ℤ` the
hypothesis is vacuous, because `ℤ` has rank 1 while `R` has rank 2.

**Decomposition.**

1. **Eichler's local theory** (Vignéras LNM 800, Ch. II §1 and §3, Ch. III §5; theorem numbers
   UNVERIFIED). This half is provable with the project's order, and is proved.
   - At `p | 6`, `B_p` is a division algebra whose unique maximal order is
     `𝒪_p = {x : nrd x ∈ ℤ_p}`. So `𝒪_p ∩ k_p = 𝒪_{k,p}`, and an optimal embedding `R ↪ 𝒪` has
     `p ∤ f(R)`.
   - For N5's `𝒪 = ℤ⟨1, i, (1+j)/2, (i+k)/2⟩ ⊂ (2,−3)_ℚ` this is fs5-nocm's
     `not_dvd_conductor_of_optimal`. It uses finite checks modulo `4` and `9` (`check2`, `check3`)
     and needs no leaf.
   - **Re-compiled here on this base** (`N1b.lean`, exit 0, 9 s, standard axioms): `dvd_of_sq_dvd_Qf`,
     `not_dvd_conductor_of_optimal` and `cmConductorCoprime6_of : CMOptimalEmbedding →
     CMConductorCoprime6`.
2. **Shimura's description of CM points** (fs5-nocm's leaf N1b′ `CMOptimalEmbedding`: `R = φ⁻¹(𝒪)`
   for some `φ : k → B`). This half is not Eichler theory, so N1b is not provable from Eichler's
   theory alone. It is the published moduli description of CM points: Shimura 1967; Jordan,
   thesis (1981) §3; González–Rotger 2006 §5 (locators UNVERIFIED). rv-h-cm §3 also records that
   for `N = 1`, González–Rotger's "optimal embeddings mod `𝒪¹`" agrees with `End_𝒪(A_x) = K ∩ 𝒪`.

   The argument for faithfulness (checked here):
   - Over `ℂ` (and `End(A_ℚ̄) = End(A_ℂ)` in characteristic 0), `Λ = H₁(A, ℤ)` is a left
     `𝒪`-module through `ι : 𝒪 →+* End A`. It is projective of rank one, so `Λ ≅ 𝒪`, because the
     class number of `𝒪` is 1 for `D = 6` (STANDARD).
   - An `𝒪`-linear endomorphism of `Λ` is right multiplication by some `β ∈ 𝒪`. It is
     holomorphic iff `β` commutes with the complex structure `j_τ ∈ B_ℝ`.
   - So `End_𝒪(A) ≅ (𝒪 ∩ K_τ)^op = 𝒪 ∩ K_τ`, with `K_τ` the centralizer of `j_τ`.
   - An isomorphism `R ≅ 𝒪 ∩ K_τ` extends to `φ : k ≅ K_τ ⊂ B` with `φ⁻¹(𝒪) = R`.
   - Even without class number one, `Λ ≅ I` gives the right order `O_r(I)`, which equals `𝒪` at
     `p | 6`. That suffices for the conductor, and type number 1 lets one conjugate back to `𝒪`.

**Verdict.**

- N1b is a consequence of published statements: `CMOptimalEmbedding` (published) plus a compiled
  Lean proof of the Eichler half.
- It is not a literal published statement. González–Rotger assume `(f, D) = 1` as a hypothesis;
  Eichler/Vignéras state the local embedding criterion.
- **Recommended leaf list:** `CMOptimalEmbedding` in place of `CMConductorCoprime6`, with
  `cmConductorCoprime6_of` as glue (compiled).

## 5. What compiles (all VERIFIED)

| file | content | outcome |
|---|---|---|
| `X6Kummer.lean` (part0, B, C, R, D, E) | the verbatim statement; Galois action and residue fields; reduction of N2 to the fibre form; transport; rigidity (copied); `pairBaseChangeUnique`; conic form; `x6KummerFibre_of_conic` | exit 0, 0 errors, no `sorry`, 33 s; 8 `#print axioms` lines, all standard (`run1.txt`) |
| `N1b.lean` (part0, N) | fs5-nocm §I verbatim (minus its final consumer theorem) | exit 0, 9 s; 3 `#print axioms` lines, all standard |

Kernel modules used: `ZInQKernel.HDecomp.QM.Leaves` and `ZInQKernel.HDecomp.QM.Pin`, both built
with `lake build`. Mathlib modules: `AlgebraicGeometry.Group.Abelian`, `AlgClosed.Basic`,
`ZariskisMainTheorem`.

## 6. Integration (not applied)

1. Put §B-§E and §G (`partB`, `partC`, `partD`, `partE`) in a new module importing `QM.Pin` and
   mul-rigidity's integrated `Rigidity` module; drop `partR`.
2. In fs5-nocm's consumers, replace the hypothesis `hK : X6KummerFibre` with
   `x6KummerFibre_of_conic hM hL`. `hM : MobiusGlue` is already a hypothesis there.
3. Leaf list:
   - add `X6ConicModel` (Elkies/Kurihara; it implies the bundle `R1R2fp`);
   - replace N1b `CMConductorCoprime6` by `CMOptimalEmbedding`.
4. Glue list:
   - remove N2 (proved);
   - `PairBaseChangeUnique` is proved and need not be listed.

## 7. What remains

- **`X6ConicModel`**, a leaf. Its locators (Elkies §3, Kurihara) are UNVERIFIED because there is
  no network. A human check of the constants against Elkies' paper is advisable, although rv-h-cm
  §2.3 derives them independently.
- **`MobiusGlue`**, existing glue: mobius-glue's open curve glue `CurveRatFactor`, `CurveSurj`.
- **`CMOptimalEmbedding`**, a leaf. Locators UNVERIFIED.
