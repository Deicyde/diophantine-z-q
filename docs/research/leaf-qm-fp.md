# leaf-qm-fp: the Shimura-curve leaves R1, R2, R5 as concrete Lean statements (field-point form)

Status: research note (task leaf-qm-fp, 2026-11-12). Lean file: `scratch/leaf-qm-fp/QMLeaves.lean`
(results log `scratch/leaf-qm-fp/log.md`). It imports the kernel module `ZInQKernel.HDecomp.A6.A6`
(prebuilt here; otherwise run `lake build ZInQKernel.HDecomp.A6.A6` first). Blueprint followed:
`docs/research/bp-qmmoduli.md` §2.3.

Marks. **VERIFIED**: read in a source named here, computed, or compiled. **STANDARD**: a published
result with its reference. **SPECULATIVE**: an assessment. This host has no network, so theorem
numbers recalled from memory are marked **UNVERIFIED**; numbers marked "read by the audit" come
from `docs/research/locators.md`. Steps A1-F4 are those of `docs/research/h-trust.md`.

---

## 0. Main result

**The three opaque placeholders `R01_ShimuraDeligne`, `R02_BabaGranath` and `R05_GonzalezRotger`
of `scratch/h-decomposition/Leaves.lean` now have concrete Lean statements, in field-point form,
over the kernel's `PkgI3.AbVar` and genuine Mathlib objects.** They compile, with no `sorry` and
no `axiom` anywhere in the file (VERIFIED: `lake env lean scratch/leaf-qm-fp/QMLeaves.lean`, about
24 s; every `#print axioms` at the end of the file gives `propext`, `Classical.choice`,
`Quot.sound`).

The leaves, bundled as `LeafQM.AV.QMLeaves`:

| Lean name | Replaces | Content (field-point form) | Source |
| --- | --- | --- | --- |
| `R1R2fp` (with `R1fpProps`, `R1heckeProps`, `X6Props`, `R2X6Props`, `CMExists`, `R1recProps`) | R1(a), R1(c), R1(d), R2 | a proper smooth curve `Y/ℚ` with `Y(K) ≃ M3 K` for every field `K ⊇ ℚ`, natural in `K`; `Γ'` acts by automorphisms of `Y`; a proper smooth curve `X/ℚ` with `X(ℚ̄) ≃ {QM pairs}/≅`, Galois-equivariant, with the `W`-twists and the forgetful map `Y → X`; a morphism `π₆ : X → P¹` whose fibres are the `W`-orbits and whose values at the CM points of discriminants −4, −3, −24 are `0, ∞, −16/27`; these CM points exist | Shimura 1967 / Deligne 1971 (R1), Baba–Granath 2008 Thm 2.1, Lemma 3.1 (R2) |
| `R1recProps` (inside `R1R2fp`) and `R1rec` | R1(d) | point form: the residue field of a `ℚ̄`-point of `Y₃` whose object has CM by `ℤ[i]`, `ℤ[ζ₃]` or `ℤ[√−6]` is a number field unramified at every `p ≥ 5`; object form (`R1rec`): the same for the field of moduli of the object, unramified at every `p ≥ 5` | Shimura reciprocity (Shimura 1967 Main Thm II; Deligne 1971 §3) |
| `R5fp` | R5(ii) | on `X₆`: `[ℚ(x):ℚ] = 2h(R)` and `k ⊆ ℚ(x)` if some `p ∣ 6` is inert in `k`; `[ℚ(x):ℚ] = h(R)` otherwise | González–Rotger 2006, Thm 5.12 (with Thm 5.8) |
| `R5fpCount` | R5(i) | on `X₆`: `#CM(R) = 2^{b(R)} h(R)` | González–Rotger 2006, Prop. 5.6 |

Glue proved in the same file from these leaves (VERIFIED, compiled):
- `R1R2fp_Y` and `R2fpProps_of_X6`: the morphism `π = π₆ ∘ fY : Y₃ → P¹` (`ToP1.comp`, the
  pullback of charts) with the R2 clauses on `Y₃` (fibres and CM values), from the clauses on
  `X₆`.
- `ToP1.val_comp` (`π(y ∘ Spec f) = f(π(y))`) and `ToP1.val_comp_right`
  (`(π ∘ h)(y) = π(h ∘ y)`), for morphisms to `P¹` given by charts.
- **`conj_iso_of_rational`: step A7's statement.** Let `y` be a `K`-point of `Y` with rational
  `π`-value and object `P`. For any two embeddings `K → ℚ̄`, the two base changes of `P` exist as
  objects, and their QM pairs are `Aut(𝒪)`-twists of each other. In particular their abelian
  surfaces are isomorphic over `ℚ̄`. The variant `conj_twist_of_rational` does the same for
  `σ ∈ Aut(ℚ̄/ℚ)`.
- **`cm_of_val`: h-b1 M9 on `X₆`.** Every `ℚ̄`-point over `0`, `∞`, `−16/27` has CM by `ℤ[i]`,
  `ℤ[ζ₃]`, `ℤ[√−6]` respectively. It uses `conjHom` and `HasCM*.of_iso`, `hasCM*_twist`: the CM
  predicates are invariant under isomorphisms and twists.
- For A3 (and A6):
  - `M3.rightMul_rightMul`: `𝒪^×` acts on classes.
  - **`Level3.onto`**, from the kernel's leaf `TorsionStructure`: in characteristic 0 every
    3-torsion `K̄`-point is the image of a level point. The proof is a count:
    `𝒪/3𝒪 ↪ A(K)[3] ↪ A(K̄)[3]`, with 81 = 81. So all of `A[3]` is `K`-rational, and the
    `K`-point form of `Level3` agrees with the moduli problem's level structure, which closes
    the "equivalent in characteristic 0" remark of §1 in Lean. This is also the hypothesis
    `hrat` of the kernel's A6.
  - **`Level3.torsor`**: any two level structures on one `(A, ι)` differ by right
    multiplication by some `u₀ ∈ 𝒪` invertible mod `3𝒪`. It is proved via
    `Level3.exists_mul_of_range_le` and `Level3.range_le`.
  - Consequence: a `ℚ̄`-fibre of `Y₃ → X₆` has at most `#(𝒪/3𝒪)^× = 72` points
    (bp-qmmoduli's `Units72`). Assembling this count in Lean is a small step not done here.
- **Lemma NV step 2.** `residue_unramified_over_branch` (from `R1R2fp` alone) says: a
  `ℚ̄`-point of `Y₃` over `0`, `∞` or `−16/27` has a residue field that is a number field
  unramified at every `p ≥ 5`. This is the form h-b1 §3 uses. `unramified_over_branch` (from
  `R1R2fp` and `R1rec`) is the same for fields of moduli.
- **A6 on the leaves' objects (`QML3.goodReduction`).** Every `QML3` object over a field of
  characteristic 0 has good reduction at every DVR in which 3 is a unit. It follows from the
  kernel's leaves `NeronOggShafarevich`, `RaynaudCriterion`, `TorsionStructure` through
  `GlueA6Alg.goodReduction_of_QM_rational3'`. The rationality hypothesis comes from
  `Level3.onto` (`hrat`, `galAct_bcPt`). Applied to the fibre object of R1fp, this is A4 + A6.
- `R5fpWeak_of_R5fp` (bp-qmmoduli's degree disjunction), `R1fp_of_R1R2fp`.

**One finding about R5** (VERIFIED by reading rv-h-cm §7.2). NoCM needs more than the degree of
`ℚ(x)`. In the case `D(R) ≠ 1` the proof uses `ℚ(x) = H_R ⊇ k`. With the degree alone,
`k = ℚ(√−19)` is not excluded: there `h = 1`, `b = 2` and `2h = 2`, the same degree as the fibre
field `ℚ(i)`. So `R5fp` carries the containment `k ↪ ℚ(x)` when `b(k) ≥ 1`. bp-qmmoduli's
`R5fp` (degree in `{h, 2h}`) is too weak for A10.

**Dependence on an unreviewed claim** (found by the review, §6). `QML3` and `QMPair` omit the
polarization. So the faithfulness of every leaf rests on the published theorems **plus**
bp-qmmoduli §2.2: for a QM pair `(A, ι)` in characteristic 0, a principal polarization with Rosati
involution `x ↦ μ⁻¹x̄μ` exists and is unique. §2.2 is SPECULATIVE. Its uniqueness half was
checked by the review; its existence half (class number one and the sign argument) is
unformalized. Polarizations cannot be stated in Lean today, so this cannot be split off as a Lean
hypothesis. Buzzard's polarization-free moduli problem would remove it (UNVERIFIED for full
level 3).

What is not done: no leaf is proved (they are leaves). The steps A2-A5 and A10 still need glue
that Mathlib cannot support today, listed in §4: degree theory of finite morphisms of curves,
Galois theory of the function field of `Y₃` over `ℚ(j)`, the explicit model of `X₆ → P¹`, and
residue fields of points versus fields of moduli. R3 (Lin–Yang) and R1(b) (complex
uniformization, R1an) are outside this task.

---

## 1. Definitions built (cheap, no `sorry`)

All in namespace `LeafQM.AV` of `QMLeaves.lean`.

- **The order** `O : Subring B`, `B = QuaternionAlgebra ℚ 2 0 (−3)`. Copied from
  `scratch/bp-qmmoduli/QMAbVar.lean` §0.
- **QM structures** `QMStr A`: an injective ring homomorphism `𝒪 →+* End_K(A)`. With it:
  - `qmAct` (the action on `A(L)`);
  - `not_qmStr_zero` (sanity: the zero abelian variety has no QM structure);
  - `QMStr.twist α` for `α ∈ Aut(𝒪)`.

  Copied from bp-qmmoduli.
- **Level-3 structures** `Level3 q`: `η : 𝒪 →+ A(K)`, `𝒪`-linear, kernel exactly `3𝒪`.
  - **Changed from bp-qmmoduli**, whose `η` takes values in `A(K̄)`, is Galois-fixed and is onto
    `A(K̄)[3]`. That form base-changes only through the counting leaf `TorsionStructure`, which
    was bp-qmmoduli's open half of N8.
  - The new form is equivalent for abelian surfaces in characteristic 0 (STANDARD). `η` embeds
    `𝒪/3𝒪` (81 elements) into `A(K)[3] ⊆ A(K̄)[3]`, which also has 81 elements (Mumford §4,
    the kernel's leaf `TorsionStructure`). So `η` is onto, `A[3]` is constant, and `η` is an
    `𝒪`-linear isomorphism `(𝒪/3𝒪)_K ≅ A[3]`. The converse is clear.
  - Operations: `Level3.rightMul u` (`u ∈ 𝒪^×`), with `rightMul_eq_self` (units `≡ 1 mod 3`
    act trivially), and `Level3.twist α`.
- **Objects** `QML3 K`: `A : AbVar K`, `A.dim = 2`, `q`, `e`.
  - Isomorphisms `QML3.Iso`, with `refl`, `symm`, `trans`, and `isoSetoid`.
  - **`M3 K`** is the `Quotient` by isomorphism.
  - The `Γ'`-operations `M3.twist α` and `M3.rightMul u` act on classes.
- **QM pairs** `QMPair K` (objects of `X₆`): `QMIso`, `pairSetoid`, `QML3.forget`,
  `QMPair.twist`.
- **The centralizer** `com q = End_𝒪(A)`, and the CM predicates `HasCM4`, `HasCM3`, `HasCM24`
  (an element of `com` with `φ² = −1`, `φ² − φ + 1 = 0`, `φ² = −6`). With them: `com_twist`,
  `conjHom`, `HasCM*.of_iso`.
- **Base change as a relation.** `IsBaseChangeOf f P Q` (`f : K →+* L`) says there is a
  morphism `g : Q.A → P.A` such that:
  - the square over `Spec L → Spec K` is a pullback (`Mathlib.IsPullback`);
  - `g` commutes with `ι`;
  - `g` carries `η_Q` to `η_P` (at `a = 0` this is the identity section; by rigidity, Mumford
    §4 Cor. 1, `g` then respects the group laws).

  `IsBaseChangeOfPair` is the same for pairs. This formulation avoids constructing `A_L` as a
  `QML3 L`, which would need `dim A_L = dim A`, not in Mathlib.
- **Fields of moduli** `fieldOfModuli3 P` and `fieldOfModuliPair P` (for `P` over
  `ℚ̄ = AlgebraicClosure ℚ`): the fixed field of the subgroup generated by
  `{σ : IsBaseChangeOf σ P P}`.
- `UnramifiedAbove5 F`: `F` is finite over `ℚ` and `p ∤ NumberField.discr F` for every prime
  `p ≥ 5`.
- **Morphisms to `P¹` by charts**, `ToP1 X`. Mathlib v4.35 has no `P¹` with its point bijection
  (bp-qmmoduli N11). The structure consists of opens `U, V` with `U ⊔ V = ⊤`, sections
  `f ∈ Γ(U)` and `g ∈ Γ(V)` with `fg = 1` on `U ∩ V`, and `D(f) = D(g) = U ∩ V`. This is
  exactly a morphism `X → P¹`: glue `U → 𝔸¹` and `V → 𝔸¹` along `t ↦ 1/t` (STANDARD).
  - `ToP1.val π y ∈ OnePoint K` is the value at a `K`-point. It is computed with Mathlib's
    `Scheme.SpecToEquivOfField` and `Scheme.evaluation`: `f(x)` mapped to `K` if `x ∈ U`, and
    `∞` otherwise.
  - `ToP1.val_comp` is its naturality. `ToP1.comp h π` composes with a morphism of schemes,
    and `ToP1.val_comp_right` computes its values.
- **Field points**: `fieldPt K` (`Spec K` over `Spec ℚ`), `fieldMap f`, and `PtEquiv Y`
  (`∀ K, (Spec K ⟶ Y) ≃ M3 K`).
- For R5: `conductor R = [𝒪_k : R]` (via `AddSubgroup.relIndex`) and
  `inertCount6 k = #{p ∈ {2,3} : p𝒪_k prime}`.

## 2. The leaves, with their published statements and faithfulness

Each Lean docstring repeats this information. "Faithful" means that the Lean statement is the
printed one or a consequence of it, never stronger.

### 2.1 `R1fpProps` / `R1fp` (R1(a), field points)

```lean
def R1fpProps (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  IsProper Y.hom ∧ SmoothOfRelativeDimension 1 Y.hom ∧ Nonempty (fieldPt Qbar ⟶ Y) ∧
  ∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →ₐ[ℚ] L)
    (y : fieldPt K ⟶ Y) (P : QML3 K), Φ K y = M3.mk P →
      ∃ Q : QML3 L, Φ L (fieldMap f ≫ y) = M3.mk Q ∧ IsBaseChangeOf (f : K →+* L) P Q
```

- **Published.** Shimura–Deligne: for `𝒪` and the neat level `K₃`, the functor on `ℚ`-schemes
  of `(A, ι, λ, η)` is represented by a smooth projective curve `Y₃/ℚ`.
  - Deligne, Sém. Bourbaki 389 (1971), Thm 4.21, Cor. 5.7, Ex. 5.8 and §§4.8-4.17, read by the
    audit with the verdict "qualified consequence".
  - Shimura, Ann. of Math. 85 (1967), Main Thms I-II (UNVERIFIED).
  - Alternatively Buzzard, Duke Math. J. 87 (1997), Thm 2.1, Cor. 2.3 (UNVERIFIED), which has
    no polarization.
- **Faithful.**
  - The clause `Nonempty (fieldPt Qbar ⟶ Y)` guards against vacuity, as the review asked: if
    `QML3` were mis-encoded as empty, `Y = ∅` would satisfy every other clause. `X6Props` has
    the same guard.
  - Restricting the representing isomorphism to `Spec K` gives the bijections and their
    naturality; projective implies proper.
  - `M3 K` drops `λ`. bp-qmmoduli §2.2 argues that `λ` exists and is unique for this datum in
    characteristic 0 (SPECULATIVE until reviewed; its lattice core is proved there,
    `BPQM.eq_pm_E0_of_principal`). Buzzard's route does not need this.
  - `η` lives on `K`-points (§1).
  - `Y` is **not** required to be geometrically connected: it has two components over
    `ℚ(√−3)` (bp-qmmoduli §2.1). Requiring connectedness would make the leaf false.
  - **Caveat (audit):** the audit could not confirm that Deligne's PEL model specializes to
    *this* functor (lattice, polarization-compatible level structure, PEL conditions, component
    convention, `E(G,h) = ℚ`). The leaf is therefore a qualified consequence until a human
    checks those conditions.

### 2.2 `R1heckeProps` (R1(c))

`twist α` (`α ∈ Aut 𝒪`) and `rightMul u` (`u ∈ 𝒪^×`) are each induced by an automorphism
`g : Y ≅ Y` over `ℚ`: `Φ K (y ≫ g.hom) = M3.twist α (Φ K y)`.

- **Published.** The finite-adelic normalizer of `K₃` acts on `Y₃` over `ℚ` (Deligne 1971
  §§4.15-4.21; Deligne 1979 §2.7, UNVERIFIED). The audit adds that at fixed level only the
  subgroup preserving the level and the datum acts.
- **Faithful, and in fact a consequence of R1(a) alone.** The operations
  `(A, ι, η) ↦ (A, ι∘α, η∘α)` and `η ↦ η(·u)` are defined for families over any base and are
  natural. By Yoneda, a natural automorphism of a representable functor is composition with an
  automorphism of the representing scheme. No adelic statement is needed. The audit's
  qualification does not bite, because only operations preserving the datum are used.

### 2.3 `X6Props`, `R2X6Props`, `CMExists` (R1 at level one, and R2)

- `X6Props`:
  - `X` is proper and smooth of relative dimension 1 over `ℚ`;
  - `Ψ : X(ℚ̄) ≃ {QM pairs over ℚ̄}/≅` is Galois-equivariant (`IsBaseChangeOfPair`);
  - each twist `α` is induced by an automorphism of `X` (the group `W`);
  - `fY : Y → X` is `(A, ι, η) ↦ (A, ι)` on `ℚ̄`-points.

  The morphism `Y₃ → P¹` is then `π₆.comp fY.left`, with no further assumption.
- `R2X6Props`, for `ℚ̄`-points `x, x'` with pairs `P, Q`:
  - `π₆(x) = π₆(x') ↔ ∃ α ∈ Aut 𝒪, (A_P, ι_P∘α) ≅ (A_Q, ι_Q)`;
  - `HasCM4 → π₆ = 0`, `HasCM3 → π₆ = ∞`, `HasCM24 → π₆ = −16/27`.
- `CMExists`: points with each of the three CM types exist.

**Published.**
- Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1 (p. 737) and Lemma 3.1 (pp. 739-740), read
  by the audit with the verdict YES. The forgetful map identifies the polarized moduli space
  with `X₆/W`; `X₆/W ≅ P¹_ℚ`; the images of the three CM points are rational.
- The coarse moduli property of `X₆ = X₀(6,1)` is R1 at level one (Shimura, Deligne; locator
  UNVERIFIED).

**Faithful.**
- `π₆` is `X₆ → X₆/W ≅ P¹`, in a coordinate chosen so that the three rational CM images are
  `0, ∞, −16/27`. `PGL₂(ℚ)` is sharply 3-transitive on `P¹(ℚ)`, so this normalization adds
  nothing. The identification of `π₆` with N5's `J` is F1's business (`PkgI1.QMHauptmodul`,
  together with R3 and R4).
- `W`-conjugacy equals `∃ α ∈ Aut 𝒪`. Indeed `Aut(𝒪) = N_B(𝒪)/ℚ^×` (Skolem–Noether, T13), and
  inner twists are trivial on classes, since `ι(u)` is an isomorphism `(A, ι∘Ad u) ≅ (A, ι)`.
- The coarse property gives `Ψ` and its Galois-equivariance in characteristic 0. `fY` comes from
  the coarse universal property, and `W` from naturality of the twists.
- **Not asserted: the orbifold orders `(4, 6, 2)`.** They are not ramification indices of
  `X₆ → X₆/W`, whose indices are `(2,2,2)` (audit; rv-nocm §2). The indices `(4,6,2)` of
  `Y₃ → P¹` are glue (`RvNocm.ramification_eq_orbifold_order`).
- The CM clauses need each of `CM(−4)`, `CM(−3)`, `CM(−24)` to be a single `W`-orbit. Each
  has two points on `X₆`, by `2^b h`. This comes from Baba–Granath's §3.1 elliptic-order table
  (p. 740, read by the audit; signature `(0; 2, 4, 6)`), not from Thm 2.1 and Lemma 3.1 alone
  (review, §6).
- `CMExists`: the "distinguished points" of Lemma 3.1 are images of CM points. CM points by `R`
  exist iff `R` embeds optimally in `𝒪` (Shimura/Eichler, STANDARD). The three orders do embed,
  via `i + j`, `(1 + j)/2` and `μ`.
- Composite: the fibre clause combines Baba–Granath with R1 at level one.

### 2.4 `R1recProps` and `R1rec` (R1(d), unramified form)

```lean
def R1recProps (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
    (HasCM4 P.q ∨ HasCM3 P.q ∨ HasCM24 P.q) →
      UnramifiedAbove5 (residueImage (X := Y.left) y.left)

def R1rec : Prop :=
  ∀ P : QML3 Qbar, (HasCM4 P.q ∨ HasCM3 P.q ∨ HasCM24 P.q) →
    UnramifiedAbove5 (fieldOfModuli3 P)
```

- **Published.** Shimura reciprocity for CM points on the canonical model (Shimura 1967 Main
  Thm II; Deligne 1971 §§3.7-3.13 and Thm 4.19, read by the audit as "consequence with
  qualifications"). `Gal(E^ab/E)` acts on a CM point `y` through `rec`, and `∏_{ℓ≠3} 𝒪_{E,ℓ}^×`
  maps into `K₃`, so `E(y)/E` is unramified outside 3 (h-b1 §3 step 2).
- **Faithful.**
  - `ℚ(y) ⊆ E(y)`, and `E/ℚ` is ramified only at 2 and 3. This is the only consequence used, by
    Lemma NV step 2.
  - The point form `R1recProps` is the printed form, since reciprocity is about points of the
    canonical model. `residueImage y` is the image of `κ(x) ↪ ℚ̄`, computed with
    `Scheme.SpecToEquivOfField`.
  - The object form needs "field of moduli = `ℚ(y)`" (fine moduli, R1).
- **Why both.** The bridge from fields of moduli to residue fields cannot be proved in Lean with
  the present definitions. It needs the uniqueness of base change up to isomorphism of objects,
  which needs rigidity: a morphism of abelian varieties preserving 0 is a homomorphism, and
  Mathlib does not have this. One inclusion (field of moduli ⊆ residue field) would go through,
  but that is the wrong direction for unramifiedness. So the bundle carries the point form, and
  the object form remains as a separate leaf.

### 2.5 `R5fp`, `R5fpCount` (R5)

```lean
def R5fp : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 →
    ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring → Nat.Coprime (conductor R) 6 →
      ∀ P : QMPair Qbar, Nonempty (com P.q ≃+* R) →
        Module.finrank ℚ (fieldOfModuliPair P) =
          (if inertCount6 k = 0 then 1 else 2) * Nat.card (CommRing.Pic R) ∧
        (inertCount6 k ≠ 0 → Nonempty (k →ₐ[ℚ] fieldOfModuliPair P))
```

**Published** (González–Rotger, J. Math. Soc. Japan 58 (2006), read by the audit in arXiv
v1/v2 and the journal, YES on `X₀(D, N)`):
- Thm 5.12 (p. 946): `ℚ(x) = H_R` if `D(R) ≠ 1`, and a specified index-2 subfield of `H_R` if
  `D(R) = 1`;
- Prop. 5.6 (p. 943): `#CM(R) = 2^{#{p | D(R)N(R)}} h(R)`;
- here `D(R) = ∏_{p | 6 inert in k} p` (rv-nocm §3.1, h-decomposition R5). The printed
  condition is `D(R)·N*(R) ≠ 1`, with `N*(R) = 1` at `N = 1`.

**Faithful.**
- The degree of the printed field: `[H_R : ℚ] = 2h(R)`, and `H_R ⊇ k`. `h(R) = #CommRing.Pic R`.
- `ℚ(x)` is the field of moduli for the coarse space `X₆`.
- "CM by `R`" is `End_𝒪(A) ≅ R`.
- Everything is on `X₆`, not on `Y₃` or `X₆/W`. This is the audit's point: at disc −24 the
  quotient value is rational while `[H_R : ℚ] = 4`.
- **The count carries `2^{b}`.** The old `#CM(R) = h(R)` is false: at disc −19, `h = 1` and
  there are four CM points.
- The reading of `D(R)` was checked on Elkies' 24 rows (rv-nocm Part B, computed there).
  `R5fpWeak` drops the case split.
- In `R5fpCount`, the hypothesis "`R` occurs as some `End_𝒪(A)`" is (Emb): `R` embeds optimally
  in `𝒪`, so neither 2 nor 3 splits.

## 3. Comparison with the placeholders of `Leaves.lean`

- **`R01_ShimuraDeligne`** (a)-(d) becomes `R1R2fp` (the `R1fpProps`, `R1heckeProps` and
  `X6Props` parts, and `R1recProps` for (d)); `R1rec` is the object form of (d). Part (b),
  complex uniformization, is R1an. It needs the analytification (bp-qmmoduli N14) and is not
  stated here.
- **`R02_BabaGranath`** becomes `R2X6Props` and `CMExists` (inside `R1R2fp`). Its orbifold-order
  sentence is deliberately not a leaf clause (§2.3).
- **`R05_GonzalezRotger`** becomes `R5fp` and `R5fpCount`. The simple transitivity of
  `W(R) × Gal(H_R/k)` is not stated, because the adopted NoCM proof (rv-h-cm §7.2) does not use
  it.

Integration (SPECULATIVE plan): the definitions of §1 should become one kernel module (with
bp-qmmoduli's `QMOrder.lean`), say `ZInQKernel/HDecomp/QM/`. The `HSyn.Leaves` fields `r1`, `r2`,
`r5` would then be replaced by `QMLeaves`.

## 4. How the glue steps A2-A5, A7, A10 consume these leaves, and what is missing

Size tiers as in bp-qmmoduli (S < 500 lines, M 500-3 000, L 3 000-15 000; SPECULATIVE).

| Step | Leaves consumed | Already compiled here | Missing |
| --- | --- | --- | --- |
| **A2** (`Γ*\ℍ = P¹_j`, elliptic points `0, ∞, −16/27` of orbifold orders 4, 6, 2) | `R2X6Props`, `CMExists`, `X6Props` (W) | `cm_of_val` (the fibres over the three values are exactly the CM points of the three types) | The orbifold orders as stabilizer orders. One needs the group `Γ'` generated by `twist` and `rightMul` acting on `M3 ℚ̄`, with stabilizer of a CM point `≅ (com P)^×/±1` extended by its `W`-stabilizer. This uses `End(A_ℚ̄)` for CM points (A9-type input) and `RvNocm.ramification_eq_orbifold_order`. M. A5 needs only "index divides (4, 6, 2)" (`inertia_trivial_of_dvd`), and the stabilizer bound gives that. |
| **A3** (`deg(Y₃ → P¹_j)` divides 144, at most 324) | `R1fpProps`, `R1heckeProps`, `R2fpProps` (via `R1R2fp_Y`), kernel leaf `TorsionStructure` | `M3.rightMul_rightMul`; `Level3.onto`; **`Level3.torsor`** (the level structures on `(A, ι)` are one `(𝒪/3𝒪)^×`-orbit) | (i) Counting the classes: injecting the fibre into `(𝒪/3𝒪)^× × W` and using `Units72`, S. With the torsor, a geometric fibre of `Y₃ → P¹` has at most `72·4` points, or 144 after `±1` and the two components. (ii) **Degree theory**: for a finite morphism of smooth curves in characteristic 0, the degree equals the number of geometric points over an étale value. Mathlib lacks it (no degree of a finite morphism of curves, no generic étaleness). M-L. |
| **A4** (an object `(A, ι, λ, η)` over the residue field of a point) | `R1fpProps` | the objects themselves: `Quotient.out (Φ K y)` is a `QML3 K` with `A.dim = 2` | (i) A point of `Y` with residue field `κ` as a morphism `fieldPt κ ⟶ Y`: Mathlib's `fromSpecResidueField` plus the `ℚ`-algebra structure on `κ`. S. (ii) `λ`, if a consumer (Faltings height, T9/R22) needs it: polarizations (N12, L-VL). |
| **A5** (Prop. TS, Lemma NV, h-b1 M1-M10) | `R1fpProps` (generic point through `K = ℚ(Y)`), `R1heckeProps` (M1), `R2fpProps` (`π`, fibres), `CMExists` with `cm_of_val` (M9), `R1recProps` (Lemma NV step 2) | `cm_of_val`; **`residue_unramified_over_branch`** (Lemma NV step 2: residue fields of the points over the three branch values are unramified at `p ≥ 5`); `ToP1.val_comp` (M2's "all points over `j₀` have the same residue field" is an orbit statement once `Γ'` and Galois commute) | (i) M2: the `ℚ`-irreducible component `Y^{(1)}`, its function field `M = ℚ(Y^{(1)})` (Mathlib `Scheme.functionField`), the action of `Γ'` on `M`, and the fixed field `π^*ℚ(j)` (Artin). This needs "`π` is the quotient by `Γ'`", from the fibre clause plus degree theory. M-L. (ii) M8: the fibre field as the residue field of `M` at a place over `j₀`. Lemma NV and M8 need only residue fields of points, which is why `R1recProps` is stated on points: the field-of-moduli bridge needs rigidity (§2.4). (iii) Prop. TS itself: h-b1's glue with T1-T2 (purity, Abhyankar). (iv) Lemma NV steps 3-4: decomposition and inertia groups (Mathlib has `Ideal.inertia`), plus the indices of A2. M4's indices: as in A2. |
| **A7** (the conjugates of `A` are geometrically isomorphic) | `R1fpProps`, `R2fpProps` | **`conj_iso_of_rational`** (the statement of A7 for any `K`-point with rational `π`-value) and `conj_twist_of_rational` | Only the plumbing to the manuscript's `A`: identify the fibre surface with the object at a `K`-point over `j₀ = J(u) ∈ ℚ` (A4), and `π = J` (F1, or just "`π(y) = J(u)` is rational", true for any coordinate in which the fibre lies over a rational point). The Igusa-vector route of N5 is not needed: R2's fibre clause suffices (h-trust A7 remark, now a proof). |
| **A10** (NoCM, rv-h-cm §7.2) | `R5fp` (with the containment), `R5fpCount`, `R2X6Props`, `CMExists`, `X6Props` (W and Galois) | `com_twist` and `HasCM*.of_iso` (`W·x ⊆ CM(R)`), `cm_of_val` (`CM(ℤ[i])` = the fibre over `t = 1`, i.e. `j = 0`, as rv-nocm requires) | (i) **The model** `ℚ(t)(√(−t), √(3(t−1)))` of `X₆ → P¹` and the fibre over `t(u)` with residue field `ℚ(i)` (rv-h-cm §2.3: Kummer theory over `ℚ(t)`, with the twist constants from the fields of the elliptic points, i.e. `R5fp` at discs −4, −3, −24). This needs the function field of `X₆` and degree-4 Galois covers of `P¹`. M-L. (ii) Residue field of a point of `X₆` equals `fieldOfModuliPair` (from the Galois-equivariance of `Ψ`; S-M). (iii) `com = ℤ ⇒ End⁰(A_ℚ̄) = B`: the A9 dichotomy (T27), separate. (iv) The arithmetic: `h(R) = 1 ⇒ R = ℤ[i]` given `2 ∤ f`, class numbers, etc. S. |

**Summary of what remains.** The leaves needed by A2-A5, A7 and A10 are now all concrete. A7 is
proved from them up to plumbing. A2, A3, A5 and A10 still need four pieces of glue absent from
Mathlib:
1. degree theory for finite morphisms of curves;
2. Galois theory of a function-field cover with its decomposition and inertia groups;
3. the explicit Kummer model of `X₆ → P¹`;
4. residue fields of points versus fields of moduli.

None is research-level, but (1)-(3) are M-L each (SPECULATIVE).

## 5. Risks and open checks

1. **§2.2 of bp-qmmoduli** (the polarization exists and is determined by `(A, ι)`) is assumed by
   every leaf through `M3` and `QMPair` (§0). It is SPECULATIVE until a human review, or it can
   be avoided by Buzzard's polarization-free moduli problem (UNVERIFIED).
2. **The audit's qualifications on R1**: the specialization of Deligne's PEL model to this
   functor. Human check needed.
3. **`Level3` on `K`-points** is equivalent to the moduli problem's level structure only in
   characteristic 0 (or prime to 3). All fields here are `ℚ`-algebras, so this is safe.
4. **`IsBaseChangeOf` pins the group law only through rigidity** (identity section at `a = 0`).
   If a reviewer prefers it explicit, add the compatibility of the multiplications.
5. **`ToP1`** encodes morphisms to `P¹_ℤ`. For `X` over `ℚ` this is the same as `P¹_ℚ` over
   `ℚ`. The conditions `D(f) = D(g) = U ∩ V` are what make the value `∞` on `V ∖ U` correct.
6. **`R5fp`'s case split** relies on the audited reading `D(R) = ∏_{p | 6, inert} p`. Its
   containment clause uses `H_R ⊇ k`, true for ring class fields.
7. `Nat.card` and `Module.finrank` return 0 on infinite inputs. The true sets and fields are
   finite, so nothing is false, but a mis-encoded field of moduli would fail silently.
8. The definitions are **uninhabited in Lean today**: Mathlib cannot construct a nonzero
   abelian variety. So the leaves cannot be tested on an example; sanity theorems
   (`not_qmStr_zero`, the compiled glue) are the tests.
9. An adversarial model review of the statements was run (§6). It is a model review, not a
   human review.

## 6. Review

An adversarial model review ran on 2026-11-12: a subagent, read-only, with no access to this
note's reasoning, given the Lean file and the source notes (h-decomposition, locators,
rv-nocm, bp-qmmoduli, h-trust, rv-h-cm). It was asked to check each leaf for being stronger than
published, false through a definition, vacuous, or wrongly referenced.

**Verdict: no DEFECT.**

- **Checked correct:**
  - `Level3` on `K`-points (81 = `#A[3]`; `M3 K = ∅` when `√−3 ∉ K`, matching `Y(K) = ∅`);
  - the directions in `IsBaseChangeOf` and in the naturality clauses;
  - `stab3`/`stabPair` (closed under inverses, so `Subgroup.closure` and `σ` versus `σ⁻¹` do not
    matter);
  - `ToP1` (exactly a morphism to `P¹_ℤ`);
  - `HasCM*`, `com ≃+* R`, `conductor`, `inertCount6`, `A.dim = 2`, universes;
  - the twist classes are the `W`-orbits (`1 + i` has norm −1);
  - the orbifold orders are not asserted;
  - the Baba–Granath and González–Rotger locators match locators.md.
- **RISKs:**
  - the dependence on bp-qmmoduli §2.2 (§0, §5 item 1);
  - the missing vacuity guard (now added).
- **NOTEs:**
  - the audit's verdict was missing from the R1fp docstring;
  - R1hecke's justification ignored `λ`: the twist changes the Rosati type to `α⁻¹(μ)`. It is
    repaired either by a matching `λ'` defined in families, or by right translation by
    `n ∈ N_B(𝒪)`, which normalizes `K₃`;
  - the CM clauses need Baba–Granath's §3.1 table;
  - `N*(R) = 1`;
  - `Nat.card`/`finrank` are 0 on infinite inputs.

All were applied to the docstrings and to this note. The file recompiles (VERIFIED). This is a
model review, not a human review.
