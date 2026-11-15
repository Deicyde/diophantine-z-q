# shimura-split2: the composite Shimura leaf split into reciprocity on objects and the complex moduli map

Task shimura-split2, 2026-11-15. Base 28ec5c91 (origin/wip/gt-rayclass). Model work; no human review.

Marks: **VERIFIED** = compiled, computed, or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number or locator recalled without a source (this host
has no network).

## 1. Result

**Both GLUE fields `rayClassCMAb` and `shimuraFamilyAb` of `HDec.HSyn.OpenResearchLeaves19` are proved in Lean
without gt-rayclass's composite `RayClassCFT.ShimuraMainThmIDeligneY3AbU`.** The proofs use two new leaves, each
one printed theorem, plus fields the bundles already keep. All the glue is proved. VERIFIED: the file compiles, and
`#discharges` matches both fields with only the standard axioms (§6).

The file is `ZInQKernel/Contrib/OneProof/ShimuraSplit2.lean` (889 lines, 54 KB). It imports only
`ZInQKernel.Contrib.OneProof.RayClassShimura`.

```lean
theorem ShimuraSplit2.rayClassCMAb_of_leaves2 (hR : ShimuraGlue.DeligneComponentsX6PrintedAb)
    (hS : QMReciprocityL3) (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed) :
    ShimuraGlue.Ray.RayClassCMAb
theorem ShimuraSplit2.shimuraFamilyAb_of_leaves2 (hR : ShimuraGlue.DeligneComponentsX6PrintedAb)
    (hH : ShimuraHolModAll) : HDec.QMSplit.Moduli.ShimuraFamilyAb
```

* `hR` is used only for its fine witness, the clause `∃ (Y, Φ), R1fpPropsAb Y Φ` (`witness_of_x6`).
  `deligneComponentsX6PrintedAb` is a LEAF of the added bundle.
* `uniformizationLeafAll`, `gagaMorphism` and `mumfordTorsionAlgClosed` are textbook fields.

**The idea: state reciprocity on objects, not on a map `Ψ`.** gt-rayclass explained (§3 of its report) why its
composite could not be split into "for every `Ψ`" statements: reciprocity holds only for the normalized `Ψ`.
This file avoids `Ψ`. For `τ ∈ ℍ` and `g ∈ (B ⊗ 𝔸_f)^×` let `L_g = B ∩ 𝒪̂g⁻¹`, and let

`T(τ, g) = (ℂ²/ι(L_g)(τ,1)ᵀ, ι, η_g)`, with `η_g(a) = [ι(x)(τ,1)ᵀ/3]` for any `x ∈ B` with `x g ∈ a + 3𝒪̂`.

This is Deligne's moduli description of the point `[τ, g]` of `Sh_{K₃}(B^×, ℍ^±)`. The predicate `MIsAt P τ g` says
that `P : QML3 ℂ` has an analytic uniformization with kernel `ι(L_g)(τ,1)ᵀ` that is compatible with `ι` and carries
the level structure of `T(τ, g)` to `η_P`. The predicate is not vacuous: under the textbook fields every object is
some `T(τ, u)` (`mIsAt_exists`). The reciprocity law then becomes a statement about objects and their Galois
conjugates. It mentions no `Ψ` and no fine witness, so there is nothing left to normalize.

**Net count.** The autofold dry run prints (VERIFIED):

```
strict count: 45/13 on 58 -> 45/13 on 58; strictest 44/14 -> 44/14
```

This is with the honest ratings: `qmReciprocityL3` as kind `consequence` (GLUE) and `shimuraHolModAll` as
`published`, flagged pending reading (GLUE). Two GLUE fields leave and two pending leaves enter, so the count does
not change. If readings clear both leaves, the count is **47/11**. That compares with 45/12 for gt-rayclass's fold,
or 46/11 if its composite were re-rated as published. §3 explains why neither new leaf is stronger than its print.

## 2. Leaf table

| statement | role | rating | status |
|---|---|---|---|
| `rayClassCMAb` (TailZ22) | field, GLUE (consequence) | — | **proved** (`rayClassCMAb_of_leaves2`) |
| `shimuraFamilyAb` (TailZ17) | field, GLUE (consequence) | — | **proved** (`shimuraFamilyAb_of_leaves2`) |
| `ShimuraSplit2.QMReciprocityL3` | **new leaf** | consequence of a printed theorem (main theorem of CM); printed form pending a reading of Shimura 1967 §3 / Deligne 1971 §4 | input |
| `ShimuraSplit2.ShimuraHolModAll` | **new leaf** | printed form (Shimura MT I, complex part), pending reading of the `V_S` → `Y₃` step | input |
| `deligneComponentsX6PrintedAb` | kept LEAF (added bundle) | published | only its witness (R) is used |
| `uniformizationLeafAll`, `gagaMorphism`, `mumfordTorsionAlgClosed` | kept textbook LEAFs | published | used through the chain's `AvSplit.Final.h38`, `h69` |
| `DCRelTransport` | GLUE | — | **proved** (`dcRelTransport_proof`) |
| `UnifDetermines` | GLUE | — | **proved** from `HomLatticeCorr` (`unifDetermines_of`) |
| `ComplexUnifL3` | GLUE | — | **proved** from the chain's `QMComplexUnif` (`complexUnifL3_of`, `complexUnifL3_of_textbook`) |
| ∃-form ⇔ ∀-form of the moduli leaf | GLUE | — | **proved** (`shimuraHolModAll_of_hol`, `shimuraHolFamilyAb_of_all`) |
| rayclass-cft's `QHatIntegral`, `CMBaseChange`, `CMAnalytic`, `RingOfIntegersGen` | GLUE | — | proved (reused from `RayClassShimura.lean`) |
| `ClassNumberOneB`, `MumfordRigidityCore`, the composite | — | — | **not used** |

The composite's clauses map to the new statements as follows:
* (R): taken from an existing leaf.
* Clause 1 (onto, and `DCRel ⇒` equal) and clause U: proved glue (`ComplexUnifL3`, `DCRelTransport`,
  `UnifDetermines`, `vecLat_unit`).
* Clauses 2 and 3 at `g = 1`: `ShimuraHolModAll`.
* Clause 4: `QMReciprocityL3`.
* Not needed: the converse direction of clause 1, and holomorphy at `g ≠ 1`.

## 3. The two leaves and why neither is stronger than its print

### 3.1 `QMReciprocityL3`

```lean
def QMReciprocityL3 : Prop :=
  ∃ (ε : ℤˣ) (δ : Bool),
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 →
    ∀ (κ : K →+* ℂ) (q : K →ₐ[ℚ] LeafQM.B) (z : UpperHalfPlane),
      IsCMPoint q (if δ then κ else (starRingEnd ℂ).comp κ) z →
    ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 K) K), ArtinCondC κ σ s →
    ∀ (g : BAQˣ) (P P' : QML3 ℂ), IsBaseChangeOf (σ : ℂ →+* ℂ) P P' →
      MIsAt P z g → MIsAt P' z (qHatU q s ^ (ε : ℤ) * g)
```

`IsCMPoint`, `ArtinCondC` (Tau Ceti's Artin map) and `qHatU` are shimura-cft's definitions, unchanged.
`IsBaseChangeOf σ P P'` is the kernel's relation "`P'` is the base change of `P` along `σ`". It is the relation that
`R1fpPropsAb`'s naturality clause attaches to `y ↦ y ∘ Spec σ`.

**Derivation from the print** (SPECULATIVE as an argument; the theorem is STANDARD; locators UNVERIFIED). The print
is the main theorem of complex multiplication in adelic form: Shimura–Taniyama; Shimura, *Abelian varieties with
complex multiplication and modular functions* (1998), Thm 18.6; Milne, *Introduction to Shimura varieties* (2005),
Thm 11.2. It says: let `(A, i)` have CM by `E` of type `Φ`, let `σ ∈ Aut(ℂ/E*)`, and let `s` be an idele of `E*`
with `art(s) = σ|E*^ab`. Then for an `E`-linear uniformization `θ : ℂ^Φ/𝔞 → A`, there is
`θ' : ℂ^Φ/N_{Φ*}(s)^{∓1}𝔞 → A^σ` with `σθ(x) = θ'(N_{Φ*}(s)^{∓1}x)`. The derivation for `A = T(z, g)`:
1. `H₁ = L_g` inside `V = B`, with `θ(x) = ι(x)(z,1)ᵀ`.
2. Choose a maximal subfield `F ⊂ B` such that `F ⊗ K` is a field. Then `E = F ⊗ K` acts on `B` by
   `x ↦ f x q(k)`, and `B` is free of rank one over `E`.
3. `IsCMPoint` gives `θ(x q(k)) = κ(k) θ(x)`. So `K` acts on `ℂ²` by the scalars `κ`, and the CM type is the set
   of extensions of `κ`.
4. The reflex field is `κ(K)`, and the reflex norm is `s ↦ 1 ⊗ s`, that is right multiplication by `q̂(s)`.
5. So `A^σ` has `H₁ = B ∩ L̂_g q̂(s)^{∓1}`. This equals `L_{q̂(s)^{±1} g}`, because `L̂_g = 𝒪̂g⁻¹`.
6. The torsion points `θ(x/3)` go to `θ'(x q̂(s)^{∓1}/3)`. If `x g ≡ a` then `(x q̂(s)^{∓1})(q̂(s)^{±1} g) ≡ a`,
   which is the level structure of `T(z, q̂(s)^{±1}g)`.
7. The signs `ε` and `δ` absorb the normalization of `art` and the choice of `κ` versus `κ̄`. The same conventions
   are existential in the composite's clause 4.
8. **`ι`-compatibility of `θ'`** (gap found by the independent review, closed here). The main theorem gives `θ'`
   that is only `E`-linear, hence only `F`-linear on the left, while `MIsAt P'` needs all of `ι(𝒪)`.
   * `θ'` is unique: it is fixed on all torsion by `σθ(x) = θ'(x q̂(s)^{∓1})`, and that formula does not involve `F`.
   * So the same `θ'` is `F`-linear for every admissible `F`.
   * Take `F` real quadratic, `ℚ(i)` and `ℚ(k)` (`k² = 6`). These generate `B`, so `θ'` is `B`-linear.
   * `F = ℚ(j)` would fail for `K = ℚ(√−3)`, since `F ⊗ K` is then not a field.

**Independent review** (one model reviewer, adversarial; no human review). Verdict: true for some `(ε, δ)`, not
stronger than the main theorem of CM, not vacuous, Lean definitions as intended. Its points:
* `δ` is redundant. `q̂(s̄) = q̂(Ns)q̂(s)⁻¹` with `Ns` central in `𝔸_f^× = ℚ_{>0}ℤ̂^×`, and central elements act
  trivially through `DCRel` (`γ = ±r`, `k = ±u ∈ K₃`). So `(ε, false)` is equivalent to `(−ε, true)`.
* `g · q̂(s)` would be wrong: right multiplication changes the level, not the point.
* The expected signs are `(ε, δ) = (+1, true)`, from Tau Ceti's arithmetic-Frobenius normalization and
  `σ(ℂ/𝔞) = ℂ/s⁻¹𝔞` (UNVERIFIED, from memory).
* Non-vacuity: `K = ℚ(√−6)` embeds in `B`, and the fixed point of `q(√−6)` is a CM point.

The conventions are consistent with `DCRel`: `T(γτ, γgk) ≅ T(τ, g)` is proved in Lean (`dcRelTransport_proof`). It
uses the same left action of `B^×` on `g` as the reciprocity law.

**Rating.** `QMReciprocityL3` is a consequence of the printed main theorem of CM (by steps 1-7), not stronger than
it. In the project's strict convention it is kind `consequence`, which counts as GLUE. Shimura 1967 §§2-3 (the
reciprocity law for the QM family, from which Main Theorem I is deduced) or Deligne 1971 §4 may print it in this
form (UNVERIFIED). A reading that finds it there would re-rate it `published`.

**No normalization problem.** The statement quantifies over all objects `P` that are `T(z, g)`. Any two of them are
isomorphic (`UnifDetermines`, proved). So the "for every `Ψ`" counterexample (gt-rayclass §3) has no analogue: the
statement never chooses a point of `Y(ℂ)`.

### 3.2 `ShimuraHolModAll`

```lean
def ShimuraHolModAll : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ →
    ∃ yτ : UpperHalfPlane → (fieldPt ℂ ⟶ Y), HDec.HSyn.G0Split.FibreQM.IsShimuraHolFamily Y Φ yτ
```

This is shimura-split's `ShimuraHolFamily`, with two changes:
* the abelian-scheme clause list `R1fpPropsAb` of route A replaces `R1fpProps`;
* it is stated for every fine witness, with no existence claim. This is the convention the bundle already uses for
  `gonzalezRotgerProp56X6`.

**The ∀ form is not stronger than the ∃ form (VERIFIED, Lean).**
* `shimuraHolModAll_of_hol : ShimuraHolFamilyAb → ShimuraHolModAll`.
  * A fine witness `(Y', Φ')` maps to any other fine witness `(Y, Φ)`. The map comes from the universal property
    `R1univAbProps` of `Y` applied to the universal family of `Y'`, and it is compatible with the moduli
    bijections (`exists_map_of_r1fp`).
  * Holomorphic families compose with morphisms of schemes (`isHolFamily_comp`, from `regVal_comp`:
    `f(h(y)) = (h^*f)(y)`, by Mathlib's `evaluation_naturality` and `descResidueField_stalkClosedPointTo_comp`).
* `shimuraHolFamilyAb_of_all` is the converse, given one fine witness.
* `shimuraHolFamilyAb_of_composite` shows that the ∃ form is gt-rayclass's composite with clauses 1, U, 4 and
  holomorphy at `g ≠ 1` dropped.

**Rating.** This is the printed form of Shimura 1967 Main Theorem I, complex part: a holomorphic
`φ : ℍ → V(ℂ)` with `φ(τ)` the moduli point of `ℂ²/ι(𝒪)(τ,1)ᵀ`. Here it is on the fine moduli scheme `Y₃` over `ℚ`
rather than on Shimura's `V_S` over `ℚ(ζ₃)`. The step from `V_S` to `Y₃` is Deligne 1971 §4 (UNVERIFIED). This is
the "remaining link" that kinds.tsv names for `shimuraFamilyAb`. So it is entered as `published`, flagged pending
reading.
* The independent review points out that holomorphy of the classifying map amounts to "`Y₃^an` classifies analytic
  families". That sits more naturally in Shimura, *On analytic families of polarized abelian varieties and
  automorphic functions*, Ann. of Math. 78 (1963); in Deligne 1971 §4; and in Milne's comparison via Borel's
  extension theorem (all UNVERIFIED). These are the pages to read.
* The review also checks that the genuine `Y₃` satisfies `R1fpPropsAb`, with the family `τ ↦ [T(τ, 1)]`.

## 4. The glue (all proved; VERIFIED, compiled)

* **`vecLat_unit`**: `ι(L_u)(τ,1)ᵀ = Λ_τ` for `u ∈ 𝒪̂^×`, since `L_u = 𝒪` (gt-rayclass's `inO_of_bEmb_mem`).
  Hence `unif_of_mIsAt_unit` is the composite's clause U.
* **`dcRelTransport_proof : DCRelTransport`**: if `(τ', g') = (γτ, γgk)` and `P` is `T(τ', g')`, then `P` is
  `T(τ, g)`. The proof:
  * `ι(γ)(τ,1)ᵀ = j·(γτ,1)ᵀ` with `j = denom(γ, τ) ≠ 0` (`iotaC_mulVec_eq`);
  * `L_{γgk} = L_g γ⁻¹`;
  * the uniformization is precomposed with `z ↦ j⁻¹z` (the chain's `isUniformization_comp`);
  * `k⁻¹ = 1 − 3k⁻¹y₀` keeps the level representatives.
* **`unifDetermines_of : HomLatticeCorr → UnifDetermines`**: two objects that are both `T(τ, g)` are isomorphic.
  * `HomLatticeCorr` comes from `AvSplit.Final.h69` applied to `uniformizationLeafAll` and `gagaMorphism`.
  * The unique homomorphisms lifting `id` in both directions compose to the identity, by uniqueness.
  * Equivariance holds because both `ι_P(a) ≫ f` and `f ≫ ι_Q(a)` lift `ι(a)`.
  * The level structure is preserved because two level representatives differ by `3L_g` (`level_rep_eq`).
* **`complexUnifL3_of : QMComplexUnif → ComplexUnifL3`**: every `P : QML3 ℂ` is `T(τ, u)` with `u ∈ 𝒪̂^×`.
  * `QMComplexUnif` (proved in the chain from the textbook fields) gives an `ι`-compatible uniformization by `Λ_τ`.
  * `η(1) = Φ(v)` with `3v ∈ Λ_τ`, so `η(a) = [ι(ab)(τ,1)ᵀ/3]` for some `b ∈ 𝒪`.
  * `nrd b ≢ 0 mod 3`: otherwise `η(b̄) = 0`, so `b̄ ∈ 3𝒪`, so `η(1) = 0`, contradicting `ker η = 3𝒪`.
  * Every class of `(𝒪/3𝒪)^×` contains a unit `ε` of `𝒪`. There are 72 classes, since `B` is ramified at 3 and
    `𝒪 ⊗ ℤ₃` is the maximal order of a division algebra. The units and their inverses are a table indexed by
    residues, found by `scratch/shimura-split2/py/units.py` (VERIFIED, computed) and checked by `decide +kernel`
    (`tab_spec`).
  * Then `u = ε⁻¹`.
* **`embed_core_obj`**: rayclass-cft's ray-class argument, with the map `Ψ` replaced by objects.
  1. The object `Q` at `ιC^*y` is `T(τ, u)`.
  2. Take `σ` fixing the ray class field. Reciprocity gives that `Q^σ` is `T(τ, q̂(s)^ε u)`.
  3. `DCRelTransport` with gt-rayclass's `dcRel_fix` gives that `Q^σ` is `T(τ, u)`.
  4. `UnifDetermines` gives `Q^σ ≅ Q`.
  5. Then `Φ` is injective, so `σ` fixes `y`.

  No class-number argument is needed: `ComplexUnifL3` supplies `u ∈ 𝒪̂^×` directly.

## 5. Deliverable (contributor kit)

* New file: `ZInQKernel/Contrib/OneProof/ShimuraSplit2.lean`. It imports
  `ZInQKernel.Contrib.OneProof.RayClassShimura`, never `ZInQKernel.OneProof.Main`. No other file under
  `ZInQKernel/` was edited.
* `#discharges`: §6.
* **Autofold change** (`scratch/shimura-split2/autofold-spec.json`): a new generation `OpenResearchLeaves20`.
  * Removed: `rayClassCMAb` and `shimuraFamilyAb`.
  * Added: `qmReciprocityL3 : ShimuraSplit2.QMReciprocityL3` and
    `shimuraHolModAll : ShimuraSplit2.ShimuraHolModAll`.
  * The fields are filled as follows:
    * `rayClassCMAb := ShimuraSplit2.rayClassCMAb_of_leaves2 l.deligneComponentsX6PrintedAb n.qmReciprocityL3 t.uniformizationLeafAll t.gagaMorphism t.mumfordTorsionAlgClosed`
    * `shimuraFamilyAb := ShimuraSplit2.shimuraFamilyAb_of_leaves2 l.deligneComponentsX6PrintedAb n.shimuraHolModAll`
  * The new top theorem is `sixContactMin_of_open27`.
  * The dry run is `scratch/shimura-split2/autofold-dryrun.txt`. It was not applied to `Main.lean`; the
    integrator runs it.
* **Relation to gt-rayclass's fold.** The two folds are alternatives. Both discharge the same two fields of the
  current `Main.lean`, where gt-rayclass's fold has not been applied and both fields are still open. Only one of them
  can be applied.
  * Recommendation (SPECULATIVE): apply this one. Its new leaves are single theorems, and the composite is not
    needed.
  * The new leaves do not imply gt-rayclass's composite field `shimuraMainThmIDeligneY3AbU`. The composite does
    imply the ∃-form moduli leaf (`shimuraHolFamilyAb_of_composite`), but not `QMReciprocityL3`.
  * So if gt-rayclass's fold is applied first, this file cannot replace its field. The swap would be a re-fold of
    the two original fields from generation 19.
* **Alternative spec** with the ∃-form leaf `ShimuraHolFamilyAb` instead of `ShimuraHolModAll`:
  * `rayClassCMAb_of_printed hH hS hUL hG hM` and `shimuraFamilyAb_of_printed hH`, no `deligneComponentsX6PrintedAb`;
  * same count.
* **Rows proposed for `docs/research/locators.md`** (not edited here: other tasks' notes):
  * `QMReciprocityL3`: main theorem of CM, Milne 2005 Thm 11.2 / Shimura 1998 Thm 18.6, read at the adelic form
    with torsion; Shimura 1967 §§2-3 and Deligne 1971 §4 for the QM form (all UNVERIFIED).
  * `ShimuraHolModAll`: Shimura 1967 Main Theorem I; Deligne 1971 §4 (UNVERIFIED).

## 6. Checks (VERIFIED)

* `lake env lean ZInQKernel/Contrib/OneProof/ShimuraSplit2.lean`: 0 errors, about 12 s.
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.ShimuraSplit2`:
  `Build completed successfully (12981 jobs)` (`scratch/shimura-split2/build.txt`). The build tree was replayed from
  a copy of a worktree at c2ad4181, the base of gt-rayclass.
* `#discharges` (`scratch/shimura-split2/Discharges.lean`; full output in `discharges_output.txt`). The lines for
  the theorems the fold uses:

```
DISCHARGES [OpenResearchLeaves19.rayClassCMAb] by ShimuraSplit2.rayClassCMAb_of_leaves2
  still assumes: [ShimuraGlue.DeligneComponentsX6PrintedAb,
 ShimuraSplit2.QMReciprocityL3,
 BPAnalytic.Uniformization.UniformizationLeafAll,
 ZInQ.HomLattice.GAGAMorphism,
 AvSplit.MumfordTorsionAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves19.shimuraFamilyAb] by ShimuraSplit2.shimuraFamilyAb_of_leaves2
  still assumes: [ShimuraGlue.DeligneComponentsX6PrintedAb, ShimuraSplit2.ShimuraHolModAll]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 65 open hypotheses, 1568 theorems checked, 14 discharge one
```

  * The output also lists this file's intermediate forms: `rayClassCMAb_of_printed`, `_of_split`, `_of_witness`,
    `shimuraFamilyAb_of_printed`, `_of_hol`.
  * It also lists the contributions already in the tree: gt-rayclass, gt-grcount, gap-shpair, gt-elkies.
  * `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every theorem listed in `Discharges.lean`,
    including `tab_spec`, `exists_map_of_r1fp` and `isHolFamily_comp`.
* Fold check: `scratch/shimura-split2/FoldCheck.lean` is the dry-run module with line 1 stripped. It compiles, and
  `HDec.HSyn.sixContactMin_of_open27` depends on `[propext, Classical.choice, Quot.sound]`
  (`foldcheck_output.txt`).

## 7. What remains

* **Readings.**
  * `QMReciprocityL3`: is the QM form with level printed (Shimura 1967 §3, Deligne 1971 §4)? Otherwise its
    derivation from the main theorem of CM (§3.1) is the remaining paper glue.
  * `ShimuraHolModAll`: does Deligne 1971 §4 state the moduli scheme `Y₃` with its holomorphic uniformization?
* **Not attempted.** Deriving `QMReciprocityL3` in Lean from the elliptic-curve leaf `T5Glue.ShimuraMainCM` (`hCM`).
  That needs `T(z, g) ≅ E₁ × E₂` as schemes, with `E_i` Weierstrass curves uniformized by `℘`, and the kernel has no
  bridge between the two.
* No statement was changed.
