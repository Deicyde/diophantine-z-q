# qm-pin: pinning the moduli map `Φ` of the QM leaves (repair of rv-g0pieces §4)

Task qm-pin, 2026-11-13. Base 883c4ddf merged with `origin/wip/rv-g0pieces`, `origin/wip/g0-split`
and `origin/wip/notes-fix`. Scratch: `scratch/qm-pin/` (results log `log.md`). No file under
`ZInQKernel/`, `blueprint/` or another task's directory was edited. The edits for the integration
are given as patches (§5). Model work only, no human review.

## 1. Result

**The repair: pin `Φ` by the universal family.** I chose option 1 of rv-g0pieces §4. Two clauses
are appended to `R1fpProps`. `R2fpProps` is unchanged. Both new clauses are consequences of
Shimura–Deligne R1(a), under the same Lemma P premise as the existing QM leaves.

- **`R1famProps Y Φ`** (required). There is a family `𝒜 → Y` (`QMFamily`): `𝒜 → Y` is proper and
  smooth of relative dimension 2, with endomorphisms `ι(a)` over `Y` and sections `η(a)`. For every
  field point `y`, every object `P` in the class `Φ_K(y)` is the fibre `y*𝒜` (`IsFibreOf`: a
  pullback square compatible with `ι` and `η`). For the genuine `Y₃` this is the universal object,
  with `λ` forgotten.
- **`R1univProps Y Φ`** (recommended, for provability). Let `S/ℚ` be a proper smooth curve. Every
  family over `S` whose field fibres are all objects is classified by a morphism `g : S → Y`:
  `Φ(s ≫ g)` is the class of the fibre at `s`. This is the existence half of R1(a)'s universal
  property, restricted to these bases.

**Effect on the three UNSURE pieces.** Let `(Y, Φ, π)` and `(Y', Φ', π')` both satisfy the repaired
clauses. Then they agree up to a morphism `g : Y' → Y`: `Φ' = Φ ∘ g` on field points and
`π' = π ∘ g` on `ℚ̄`-points (§3).

- The `Φ`-half of this comparison is compiled from `R1univProps` (`phi_part`).
- The `π`-half is one named piece of curve glue, `MobiusGlue` (argued in §3.2, not compiled).
- A statement `∀ u, ∀ y P, Φ y = [P] → π y = J(u) → R_u(P)` therefore transfers from the leaf's
  own triple to every triple (`pointwise_of_witness_mor`, compiled). `FibreSimple`,
  `ThetaPointOfFibre` and `ModularConstituent` all have this shape.
- So their universal quantifier over `(Y, Φ, π)` now costs only `MobiusGlue`. They are true
  whenever the genuine-triple arguments of rv-g0pieces §2.1-2.3 are, and they become provable
  glue in the project's sense. Without `R1univProps` they are still true (the comparison is then
  R1(a)'s universal property, §3.3), but not provable from the leaves.

**The attack, re-run (compiled).**

- rv-g0pieces' `r1fp_relabel` no longer goes through. A natural relabeling `τ` keeps the repaired
  list only if a `QMFamily` over `Y` realizes the relabeled classes as fibres
  (`r1fpPin_relabel_iff`).
- Relabelings by automorphisms of `Y` survive (`r1fpPin_aut`, `r2fp_aut`). They are harmless,
  because they change no fibre statement (`transfer_pointwise`).
- Given the comparison, every surviving relabeling is of that kind (`relabel_geometric`).
- For the old list, the same comparison statement (`PinUniqueOld`) would force every R2-compatible
  natural relabeling to be geometric (`relabel_geometric_old`). rv-g0pieces' `relabelPt` with a
  non-continuous `s` contradicts this.

**The glue still goes through (compiled).** The kernel module `QM/Leaves.lean`, `Split.lean` and
`h-decomposition/Leaves.lean` were all compiled with the edit applied: 0 errors, and no new `sorry`
(§4).

- In the kernel file, the only proof change is two `obtain` patterns.
- A4 (`exists_fibre_object`), A7 (`conj_twist_of_rational`, `conj_iso_of_rational`), NV step 2
  (`unramified_over_branch`, `residue_unramified_over_branch`), h-b1 M9 (`cm_of_val`) and
  notes-fix's strengthened `fibre_conjugates_isomorphic` all compile unchanged otherwise.
- In `Split.lean`, `HSyn.glueOutputs_of_leaves` and `sixContactMin_of_leaves` still depend only on
  `[propext, Classical.choice, Quot.sound]`.

**The open arithmetic question (§6).** Are two rational fibres of `Y₃ → P¹` ever `ℚ`-isomorphic?

- Such fibres are `G`-torsors, `|G| = 144`, so `Y_t ≅ Y_s` iff their Galois closures coincide,
  `L_t = L_s`.
- For fixed `u`, only finitely many rational `s` qualify (Faltings, applied to twists of `Y₃`, whose
  geometric components have genus 4).
- For `u` with full monodromy, the fibre over `J(u)` is never `ℚ`-isomorphic to a rational CM fibre.
  The group fact behind this is computed; the reduction to it is argued.
- The question is not settled. After the repair, soundness no longer depends on it.

## 2. The repaired statement

In `scratch/qm-pin/QMPin.lean`, namespace `LeafQM.AV.Pin`, over the kernel's definitions
(`QML3`, `M3`, `fieldPt`, `PtEquiv`, `IsBaseChangeOf`):

```lean
structure QMFamily (S : Scheme.{0}) where
  F : Over S
  proper : IsProper F.hom
  smooth : SmoothOfRelativeDimension 2 F.hom
  iota : O → (F.left ⟶ F.left)
  iota_over : ∀ a : O, iota a ≫ F.hom = F.hom
  eta : O → (S ⟶ F.left)
  eta_sec : ∀ a : O, eta a ≫ F.hom = 𝟙 S

def IsFibreOf {S : Scheme.{0}} (𝒜 : QMFamily S) {K : Type} [Field K]
    (y : Spec (CommRingCat.of K) ⟶ S) (P : QML3 K) : Prop :=
  ∃ g : P.A.X.left ⟶ 𝒜.F.left,
    IsPullback g P.A.X.hom 𝒜.F.hom y ∧
    (∀ a : O, (P.q.iota a).hom.left ≫ g = g ≫ 𝒜.iota a) ∧
    (∀ a : O, (Additive.toMul (P.e.eta a)).left ≫ g = y ≫ 𝒜.eta a)

def R1famProps (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  ∃ 𝒜 : QMFamily Y.left, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y) (P : QML3 K),
    Φ K y = M3.mk P → IsFibreOf 𝒜 y.left P

def R1univProps (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    ∀ 𝒜' : QMFamily S.left,
      (∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ S), ∃ P : QML3 K,
        IsFibreOf 𝒜' s.left P) →
      ∃ g : S ⟶ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ S) (P : QML3 K),
        IsFibreOf 𝒜' s.left P → Φ K (s ≫ g) = M3.mk P
```

Repaired `R1fpProps` (full form; the minimal form omits the last conjunct):

```lean
def R1fpProps (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  IsProper Y.hom ∧ SmoothOfRelativeDimension 1 Y.hom ∧ Nonempty (fieldPt Qbar ⟶ Y) ∧
  (∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →ₐ[ℚ] L)
    (y : fieldPt K ⟶ Y) (P : QML3 K), Φ K y = M3.mk P →
      ∃ Q : QML3 L, Φ L (fieldMap f ≫ y) = M3.mk Q ∧ IsBaseChangeOf (f : K →+* L) P Q) ∧
  R1famProps Y Φ ∧ R1univProps Y Φ
```

Notes on the definitions:

- **No group law in the family.** Rigidity recovers it: a proper smooth scheme with a section
  whose geometric fibres are abelian varieties is an abelian scheme (Mumford, GIT Ch. 6; theorem
  number UNVERIFIED).
- **Faithfulness does not depend on the group law either.** The genuine universal object has
  every listed property.
- **The `Y`-scheme `𝒜` is genuine.** It is a Mathlib `Over Y.left` with real morphisms; nothing
  abstract was invented for the purpose.
- **Only one direction of the fibre relation is stated** (`Φ y = [P] → IsFibreOf`). It is enough to
  pin `Φ`. The converse would need rigidity, to make the scheme isomorphism between two fibres a
  group isomorphism.

### 2.1 Faithfulness (each QM leaf stays the published statement or a consequence)

- **`R1famProps`.** R1(a) says `Y₃` represents the functor `S ↦ {(A, ι, λ, η)}/≅` on `ℚ`-schemes
  (Deligne 1971 Thm 4.21, Cor. 5.7, Ex. 5.8, as in the kernel docstring; audit verdict
  "qualified consequence").
  - The representing object carries a universal `(𝒜, ι, λ, η)`. `𝒜 → Y₃` is an abelian scheme of
    relative dimension 2, hence proper and smooth of relative dimension 2. The `ι(a)` are
    endomorphisms over `Y₃`, and `η` gives the sections `η(a)` of `𝒜[3]` matching `a mod 3`.
  - By Yoneda, the object at `y : Spec K → Y₃` is `y*(𝒜, ι, λ, η)`. That is a pullback square
    compatible with `ι` and `η`.
  - Any `P` in the same class is isomorphic to it as a `QML3`. Composing the isomorphism with the
    square gives `IsFibreOf` (`IsPullback.of_iso`, `QML3.Iso.equivariant`, `QML3.Iso.level`).
  - Forgetting `λ` is allowed. Lemma P enters exactly where it entered before: in identifying
    `M3 K` with the classes of the PEL problem. (STANDARD as an argument; same status as `R1fp`.)
- **`R1univProps`.** This is representability applied to `S`, a proper smooth curve over `ℚ`.
  Take a family `𝒜'` over `S` whose field fibres are all objects.
  - It is an abelian scheme with origin `η(0)` (rigidity, above).
  - `ι` is a ring homomorphism to `End_S(𝒜')`, and `η` is `𝒪`-linear and 3-torsion. These
    identities hold on every field fibre, and `S` and `𝒜'` are reduced.
  - `(𝒪/3𝒪)_S → 𝒜'[3]` is a map of finite étale group schemes that is an isomorphism on fibres,
    hence an isomorphism.
  - The type-`μ` principal polarization of the generic fibre (Lemma P, characteristic 0) extends to
    a homomorphism over the normal base. Homomorphisms of abelian schemes over a normal base extend
    (Faltings–Chai I.2.7; number UNVERIFIED). The inverse extends too, and the extension is a
    polarization on every fibre, with Rosati involution of type `μ` (a closed condition).
  - So `(𝒜', ι, λ, η) ∈ F(S)` is classified by some `g : S → Y₃`.
  - Verdict: a consequence of R1(a), rigidity and Lemma P. The new ingredient, beyond what the
    field-point leaf used, is the extension of the polarization over a normal base. Argued; the
    locators of the ingredients are UNVERIFIED.
- **Unchanged leaves.** `R2fpProps`, `R1heckeProps`, `X6Props`, `R2X6Props(Iff)`, `CMExists`,
  `R1recProps`, `X6Surj`, `R5ptProps`, `R1rec`, `R5fp`, `R5fpCount`.

### 2.2 Why not option 2 (an F1 clause in `R2fp`) or option 3 (the leaf's own triple)

- **Option 2 (F1 clause).** The clause would say: for every `ℚ̄`-point `y` with `Φ y = [P]`, a
  period matrix `Ω` of `P.A` has `3779136(∏θ)⁴/(∑θ⁸)⁵ = π(y)`.
  - *If `Ω` ranges over every principal polarization, it does not pin `π`.* A QM surface has
    several principal polarizations. A relabeling that moves the fibre over `J(u₁)` to the fibre
    over `s₂` survives if any polarization of `A_{s₂}` has theta value `J(u₁)`. rv-g0pieces §4
    already noted this residue for `FibreSimple`.
  - *If `Ω` is pinned to the type-`μ` polarization, the clause becomes a composite.* Pinning needs
    the lift of `ι(𝒪)` to `ℂ²` and the Rosati condition `N_aᴴ (Im Ω)⁻¹ = (Im Ω)⁻¹ N_{μ⁻¹āμ}`.
    These are statable, but the clause would be a composite of R1(a), R1(b), R2, R3 and R4. That
    is glue F1 moved into a leaf, and it would hinge on the normalization of `π` against Lin–Yang's
    `j` (`QMHauptmodul`), the very item that F1 is meant to prove.
  - Rejected: it does not keep the leaf "a consequence of the published statement".
- **Option 3 (the leaf's own triple).** The pieces would be stated for the witness that
  `Classical.choice` picks from the leaf. Their truth would then depend on that choice, and the
  pieces would not be provable glue. Rejected.
- **Option 1 (chosen).** It adds only what R1(a) prints: the universal object and its universal
  property. In Lean it costs three definitions and no new mathematics.

## 3. Why the repaired clauses pin the triple (`PinUnique`)

Compiled statement shapes: `SameTriple` (an isomorphism `g : Y' ≅ Y`) and `SameTripleMor` (a
morphism) say that `Φ' = Φ ∘ g` on field points over every field and `π' = π ∘ g` on
`ℚ̄`-points. `PinUnique` says any two triples satisfying the minimal repaired list are `SameTriple`.

### 3.1 What is compiled (`scratch/qm-pin/QMPin.lean`)

All of these are compiled, with axioms `[propext, Classical.choice, Quot.sound]`:

- **`transfer_pointwise`, `transfer_exists`, `transfer_pointwise_mor`.** Pointwise statements, and
  statements in `FibreOver`'s `∃`-form, transfer along `SameTriple` or `SameTripleMor`.
- **`pointwise_of_witness`** (under `PinUnique`) and **`pointwise_of_witness_mor`** (under
  `MobiusGlue` and the existence of CM objects). A statement proved for the leaf's triple holds for
  every triple satisfying the repaired list.
- **`phi_part`.** `R1univProps` for `(Y, Φ)` and the minimal repaired list for `(Y', Φ')` give
  `g : Y' → Y` with `Φ' = Φ ∘ g`. The proof applies `R1univ` to the family of `Y'`; the fibres
  exist because `Φ'` is onto.
- **`sameTripleMor_of_mobius`.** `phi_part` together with `MobiusGlue`.
- **`cm_objects_of_R1R2fp`.** CM objects of the three kinds exist, from the leaf bundle
  (`CMExists`, `X6Surj`, `X6Props`).
- **`r1fpPin_relabel_iff`, `r1fpPin_aut`, `r2fp_aut`, `sameTriple_aut`.** These cover what survives
  of a relabeling.
- **`relabel_geometric`, `relabel_geometric_old`.** These state what the comparison forces.

### 3.2 `MobiusGlue` (stated, argued, not compiled)

Hypotheses:

- `g : Y' → Y` with `Φ' = Φ ∘ g`;
- both triples satisfy the full repaired list and `R2fpProps`;
- CM objects of the three kinds exist.

Conclusion: `π' = π ∘ g` on `ℚ̄`-points.

Argument:

1. **Same fibres.** By the two fibre clauses, `π'(y₁) = π'(y₂)` iff `Φ' y₁` and `Φ' y₂` are
   twist-equivalent, iff `π(g y₁) = π(g y₂)`.
2. **Both maps are nonconstant on every geometric component `C` of `Y'`.** Their fibres are finite:
   the fibres of `π'` correspond, through the bijection `Φ'`, to twist classes, which are finite
   because `Aut 𝒪` and the level structures are finite.
3. **The induced map `h`.** So `h : P¹(ℚ̄) → P¹(ℚ̄)`, `h(π(g y)) = π'(y)`, is a well-defined
   bijection. `π ∘ g|_C` is nonconstant and proper, so it is onto `P¹`.
4. **`h` is a morphism.** The image `Γ_C ⊆ P¹ × P¹` of `(π ∘ g, π')|_C` is an irreducible curve
   inside the graph of `h`. Its first projection is bijective on `ℚ̄`-points, so it is finite of
   degree 1 in characteristic 0, hence an isomorphism onto the normal curve `P¹`. Then
   `h = pr₂ ∘ pr₁⁻¹` is a morphism, injective, hence of degree 1: a Möbius map.
5. **`h` is the identity.** CM objects of the three kinds exist, so there are `y` with
   `HasCM4 (Φ' y)` and so on. Both CM clauses then give `h(0) = 0`, `h(∞) = ∞` and
   `h(−16/27) = −16/27`. Hence `h = id`.

This is algebraic geometry of curves, so it is glue: true, and provable in principle from Mathlib's
scheme theory (Lean cost large). SPECULATIVE only in the sense of not being compiled.

### 3.3 Without `R1univProps`: `PinUnique` from R1(a) (argued)

Let `T = (Y, Φ, 𝒜, π)` satisfy the minimal list, and let `T₃` be the genuine triple.

- **Step 1: a morphism `g : Y → Y₃`.** By §2.1, `(𝒜, ι, η)` with the extended `λ` is an object over
  `Y`. Representability gives `g : Y → Y₃` with `Φ = Φ₃ ∘ g` on all field points.
- **Step 2: `g` is an isomorphism.** `Φ` and `Φ₃` are bijective, so `g` is bijective on `K`-points
  for every field `K`. Hence `g` is injective, with isomorphic residue fields, and surjective. It is
  proper (`Y` proper, `Y₃` separated) and quasi-finite, hence finite. On each component it is
  birational onto a normal curve, so it is an isomorphism (Zariski's main theorem; STANDARD).
- **Step 3: `π = π₃ ∘ g`.** §3.2 with `g`.
- **Conclusion.** `SameTriple(T₃, T)`. Composing two such gives `PinUnique`.

So the three pieces are TRUE under the minimal repair too, given the genuine-triple arguments. A
Lean proof would then need R1(a)'s universal property, which is not a leaf; `R1univProps` supplies
it.

### 3.4 Why the old list fails `PinUnique`

`relabel_geometric_old` (compiled): under `PinUniqueOld`, an R2-compatible natural relabeling `τ`
satisfies `τ_K(y) = y ≫ g` for an automorphism `g`.

- rv-g0pieces' `relabelPt` has this property only when its point bijection `s` and residue maps `φ`
  come from an automorphism.
- A fibre-preserving example: permute two closed points with isomorphic residue fields inside one
  rational fibre. Such points exist whenever `im ρ_t ≠ G` (§6). This keeps R2 and is not geometric.
- So `PinUniqueOld` is false whenever such a fibre exists. The family clause is exactly what
  `PinUnique` adds (`r1fpPin_relabel_iff`).

## 4. Lean outcomes (all VERIFIED; outputs in `scratch/qm-pin/run*.txt`)

| file | content | outcome |
|---|---|---|
| `QMPin.lean` | §1 defs, §2 glue on `R1R2fpPin`, §3 attack, §4 `R1univ`/`MobiusGlue` reduction (imports kernel `QM.Leaves`) | 0 errors, 5.7 s, 20 `#print axioms` all standard (run5) |
| `QMLeavesEdited.lean` | kernel `QM/Leaves.lean` with the minimal edit (imports `QM.Pairs`) | 0 errors, 6.7 s |
| `QMLeavesFull.lean` | kernel `QM/Leaves.lean` with the full edit | 0 errors, 6.5 s |
| `QMPinKernel.lean` | `QMLeavesEdited` + §3 lemmas on the patched name (candidate `QM/Pin.lean`, minimal edit) | 0 errors, 6.6 s, 10 axioms lines standard |
| `QMPinKernelFull.lean` | `QMLeavesFull` + §3-§4 lemmas on the patched name, incl. `r1fpPin_aut` with `R1univProps` (candidate `QM/Pin.lean`, full edit) | 0 errors, 1m49s under load 29 (7 s CPU), 13 axioms lines standard |
| Split, minimal edit (`Split.patch`) | `scratch/g0-split/Split.lean` edited | 0 errors, 0 `sorry`, 2m28s; `glueOutputs_of_leaves`, `sixContactMin_of_leaves`, `thetaPazuki`, … standard |
| Split, full edit (`Split-full.patch`) | the same with `R1univProps` | 0 errors, 0 `sorry`, 2m27s; same axioms |
| h-decomposition Leaves, minimal / full | `scratch/h-decomposition/Leaves.lean` edited | 0 errors; only the known `sorry` (`HSyn.glueOutputs_of_leaves`); 2m41s / 3m12s |

The 20k-line edited copies are not kept. Regenerate them with
`python3 scratch/qm-pin/apply_edit.py IN OUT {min|full}` from the repository root.

## 5. Exact edits for the integration (not applied here)

Recommended: the **full** edit (`R1famProps` and `R1univProps`). The minimal edit is enough for
truth but not for provability (§3.3).

1. **`ZInQKernel/HDecomp/QM/Leaves.lean`.** Apply `scratch/qm-pin/QM-Leaves-full.patch` (unified
   diff against the current file; 114 lines).
   - Insert `QMFamily`, `IsFibreOf`, `R1famProps` and `R1univProps` before `R1fpProps`.
   - Append `∧ R1famProps Y Φ ∧ R1univProps Y Φ` to `R1fpProps`, and update its docstring.
   - In `conj_twist_of_rational` and `conj_iso_of_rational`, change
     `obtain ⟨-, -, -, hnat⟩ := h1` to `obtain ⟨-, -, -, hnat, -, -⟩ := h1`.
   - Update the R1fp docstring ("Lean form", "Why faithful").
   - Nothing else in `ZInQKernel/` mentions `R1fpProps` (grep), and only `ZInQKernel/HDecomp.lean`
     imports the module.
   - `scripts/print_axioms.lean` is unchanged: the patch adds definitions only.
   - Optional: add the §3-§4 lemmas as a new module `ZInQKernel/HDecomp/QM/Pin.lean`. Its content
     is the `namespace Pin … end Pin` block of `scratch/qm-pin/QMPinKernelFull.lean` inside `LeafQM.AV`, with header
     `import ZInQKernel.HDecomp.QM.Leaves` and the same `open` lines. It was compiled appended to
     the fully edited `QM/Leaves.lean`, and its 13 `#print axioms` lines are standard and could
     go into `scripts/print_axioms.lean`. `QMPinKernel.lean` is the same for the minimal edit.
2. **`scratch/g0-split/Split.lean`.** Apply `Split-full.patch`: the same definition block, and the
   two patterns at the old lines 15387 and 15410. The ten pieces need no textual change: they
   quantify over `R1fpProps`, which now contains the pin. Optional docstring change at
   `FibreSimple`, `ThetaPointOfFibre` and `ModularConstituent`: "quantify over every triple
   satisfying the repaired clauses; by `PinUnique` (qm-pin) this is the leaf's own triple up to
   `MobiusGlue`".
3. **`scratch/h-decomposition/Leaves.lean`** (leaf-adopt3's file). Apply `HDecLeaves-full.patch`
   (same edit).
4. **Docs.**
   - `docs/research/h-decomposition.md`, R1 entry (the sentence at the current line 516,
     "`R1fpProps`: a proper smooth curve `Y/ℚ` …"): add "with `Φ` induced by a family `𝒜 → Y`
     (proper, smooth of relative dimension 2, `ι`, level sections; `R1famProps`) and classifying
     families over proper smooth curves (`R1univProps`), qm-pin".
   - `docs/research/g0-split.md` line 99 ("Their truth uses that these clauses pin down `Y₃` and
     the Hauptmodul"): replace with "Their truth uses `PinUnique` (qm-pin §3): with `R1famProps`
     and `R1univProps` every triple is the leaf's up to a morphism, modulo the curve glue
     `MobiusGlue`; without the family clause the claim was false (rv-g0pieces §3)".
5. **rv-g0pieces' `Exotic.lean`** carries its own copy of the old `R1fpProps`, so it keeps
   compiling. Against the repaired definition, its `r1fp_relabel` is replaced by
   `r1fpPin_relabel_iff`.

## 6. The open arithmetic question

*Question (rv-g0pieces):* are two rational fibres of `π : Y₃ → P¹`, one over `J(u)` with `u ∉ 𝒞`,
ever isomorphic as `ℚ`-schemes? Claims are argued and SPECULATIVE unless marked otherwise.
Only the group theory was computed: no explicit model of `Y₃ → P¹` is available offline.

1. **Degrees and genus** (computed by hand).
   - `|(𝒪/3𝒪)^×| = 72` (VERIFIED, `deck_group.py`; `𝒪₃/3𝒪₃` is the maximal order of the ramified
     quaternion algebra over `ℚ₃` modulo `π²`).
   - The norm-one image of `𝒪¹` has order 36, so each geometric component of `Y₃` has degree 18
     over `X₆` (`−1 ∉ Γ(3)`).
   - `X₆ = X₀(6,1)` has signature `(0; 2, 2, 3, 3)`: `e₂ = e₃ = 2` by the Eichler formulas
     (STANDARD).
   - Riemann–Hurwitz for a torsion-free `Γ(3)`: `2g − 2 = −36 + 18 + 24`, so `g = 4` for each of
     the two components.
   - `π` has degree `36 · 4 = 144`.
2. **Fibres are torsors.** The group `G` generated by `R1hecke`'s automorphisms acts by
   `ℚ`-automorphisms, and its orbits on `ℚ̄`-points are the `π`-fibres (R2fp). The stabilizer of a
   non-branch point is the generic stabilizer, which is trivial in the image `G_Y ⊆ Aut Y`. So
   `|G_Y| = 144`, and the fibre over a rational non-branch `t` is a `G_Y`-torsor over `ℚ`, given by
   `ρ_t : G_ℚ → G_Y`. The only branch values are `0, ∞, −16/27`, and `J(u)` is never one of them
   off `𝒞` (rv-g0pieces §2.1).
3. **Criterion.** `Y_t ≅ Y_s` as `ℚ`-schemes iff `L_t = L_s`, where `L_t = ℚ̄^{ker ρ_t}` is the
   Galois closure of the residue fields. Proof: as a `G_ℚ`-set, `Y_t` is `[G_Y : im ρ_t]` copies
   of `G_ℚ/ker ρ_t`.
4. **Finiteness.** For fixed `t`, `L_s = L_t` forces `ρ_s = φ ∘ ρ_t` for one of finitely many
   embeddings `φ : im ρ_t → G_Y`. Then `s` is the image of a rational point of the twist `Y^{φρ_t}`.
   The geometric components of that twist have genus 4, so it has finitely many rational points
   (Faltings 1983; STANDARD). So for each `u`, only finitely many `s` qualify. The bound is
   ineffective.
5. **CM fibres (relevant to `FibreSimple`).**
   - There are finitely many rational CM values (Elkies' table: 24 non-elliptic and 3 elliptic).
   - All points over a CM value `s` with CM by `R ⊂ k` are CM points, so `L_s ⊆ k^{ab}` (Shimura
     reciprocity; STANDARD). Hence `Gal(L_s/ℚ)` has an abelian subgroup of index at most 2.
   - The deck group of `Y₃ → X₆` is `D = (𝒪/3𝒪)^×/±1`. It has no abelian subgroup of index at
     most 2. VERIFIED by computation (`scratch/qm-pin/deck_group.py`, on the kernel's basis of `𝒪`
     and `mulCoord`, itself checked against the quaternion product on 30 random pairs):
     - `|(𝒪/3𝒪)^×| = 72`, the norm-one subgroup has order 36, and `nrd(1+i) = −1`;
     - `|D| = 36`, with element orders `{1: 1, 2: 9, 3: 8, 4: 18}` (so `D ≅ F₉ ⋊ C₄` with a
       faithful action);
     - the centralizer of the normal Sylow-3 subgroup is that subgroup (order 9), and `Z(D) = 1`.
   - So whenever `im ρ_{J(u)}` contains `D` (in particular `im ρ_{J(u)} = G_Y`, which holds for `u`
     outside a thin set by Hilbert irreducibility), `Y_{J(u)}` is not `ℚ`-isomorphic to any CM
     fibre.
   - The exceptional `u` form a thin set. By 4, only finitely many of them can pair with a given
     CM value.
6. **Height version (relevant to `ThetaPointOfFibre`).** No exclusion. For each `u₁` there are
   finitely many candidate `s₂`, and nothing here compares their heights.
7. **Status.** Open. After the repair it no longer bears on soundness: `PinUnique` (or its
   `R1univ` + `MobiusGlue` form) rules relabeled triples out whatever the answer.

## 7. What remains

- **`MobiusGlue`.** Glue; stated and argued, not compiled.
- **The genuine-triple arguments for the three pieces** (rv-g0pieces §2.1-2.3): NoCM, F1 on the
  actual surface, Glazer §4. They are unchanged by this task, and their Lean proofs are future
  glue.
- **Faithfulness of `R1univProps`.** It needs the extension of the type-`μ` polarization over a
  normal base (Faltings–Chai I.2.7, UNVERIFIED number) beside Lemma P. A human check of §2.1 is
  advisable.
