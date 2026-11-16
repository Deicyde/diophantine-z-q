# composite-out: the composite `shimuraMainThmIDeligneY3AbU` is no longer needed

Task composite-out, 2026-11-15. Base: origin/main 43513d87 with origin/wip/qmrec-printed (a05c57ef, which contains
shimura-split2) and origin/wip/dcy3-used (36240662) merged in. This is model work with no human review.

Marks: **VERIFIED** means compiled, computed or read in a file. **STANDARD** means published, with a reference.
**SPECULATIVE** means a judgement. **UNVERIFIED** means a locator recalled without a source; this host has no
network.

## 1. Result

All three uses of gt-rayclass's composite GLUE field `RayClassCFT.ShimuraMainThmIDeligneY3AbU` are proved in Lean
without it. No new leaf is needed. VERIFIED: the file compiles and every theorem has only the standard axioms.

The three uses are:
* `rayClassCMAb`;
* `shimuraFamilyAb`;
* `HDec.TSHecke.Y3Connected`, read by dcy3-used.

They follow from leaves that other tasks have already proposed:

| input | from | role | rating |
|---|---|---|---|
| `QMRecPrinted.MainTheoremCM` | qmrec-printed | LEAF | published (printed form; locators UNVERIFIED) |
| `ShimuraSplit2.ShimuraHolFamilyAb`, or its ∀-form `ShimuraHolModAll` plus the fine witness of `deligneComponentsX6PrintedAb` | shimura-split2 | leaf | published, pending reading (strict GLUE until read) |
| `uniformizationLeafAll`, `gagaMorphism`, `mumfordTorsionAlgClosed` | textbook bundle | LEAF | kept |
| `mumfordGroupLaw` | research bundle | LEAF | kept |

`ShimuraHolFamilyAb` is itself a consequence of the composite (`ShimuraSplit2.shimuraHolFamilyAb_of_composite`). So
the analytic input that remains is weaker than the composite, and the arithmetic input is the printed main theorem of
complex multiplication.

The file is `ZInQKernel/Contrib/OneProof/CompositeOut.lean` (namespace `CompositeOut`). It imports
`QMRecPrinted` and `DeligneComponentsY3Used`. Its main theorems:

```lean
theorem CompositeOut.compositeUses_of_hol (hH : ShimuraSplit2.ShimuraHolFamilyAb) (hM : QMRecPrinted.MainTheoremCM)
    (hUL : UniformizationLeafAll) (hG : GAGAMorphism) (hMum : MumfordTorsionAlgClosed)
    (hGL : MumfordGroupLaw) :
    ShimuraGlue.Ray.RayClassCMAb ∧ HDec.QMSplit.Moduli.ShimuraFamilyAb ∧ HDec.TSHecke.Y3Connected
theorem CompositeOut.y3ConnectedAb_of_hol   -- dcy3-used's used form Y3ConnectedAb
theorem CompositeOut.y3Connected_of_hol     -- the chain's form
theorem CompositeOut.y3Connected_of_modAll  -- from ShimuraHolModAll + deligneComponentsX6PrintedAb (the queued spec's leaves)
theorem CompositeOut.connected_of_holFamily -- the core: Y is connected
```

**Count** (SPECULATIVE until the integrator applies it):
* `shimuraMainThmIDeligneY3AbU` (composite, strict GLUE) leaves the bundles.
* `mainTheoremCM` (LEAF) and `shimuraHolModAll` (pending reading, so strict GLUE) enter.
* Strict GLUE is unchanged now. It drops by 1 when the reading of `shimuraHolModAll` clears.
* Without this task, removing the composite would have brought back dcy3-used's `deligneComponentsY3PrintedAb`
  (+1 GLUE). With it, dcy3-used's −1 and the qmrec-printed / shimura-split2 route can both be applied.

## 2. (b): `shimuraFamilyAb` needs an analytic leaf

`shimuraFamilyAb` asks for a holomorphic `τ ↦ y_τ ∈ Y(ℂ)`. In `ShimuraSplit.IsHolFamily` this means:
* preimages of Zariski opens are open;
* regular functions pull back to analytic functions.

None of the following says how a point of `Y` depends on `τ` (VERIFIED by reading the definitions):
* `MainTheoremCM`;
* `HomLatticeCorr`;
* `uniformizationLeafAll`, `gagaMorphism`;
* the X6 leaves (`babaGranathRationalAb`, `gonzalezRotgerX6Ab`, `elkiesX6StarPrinted`,
  `deligneComponentsX6PrintedAb`);
* `R1fpPropsAb`.

Each of them speaks of single objects, single points, or algebraic morphisms. So the holomorphy of the moduli map has
to come from a leaf. That it cannot be derived from these fields is a SPECULATIVE judgement, not a theorem. Its
content is Shimura 1967 Main Theorem I, complex part. Equivalently, "`Y₃^an` classifies the analytic family
`ℂ²/ι(𝒪)(τ,1)ᵀ`" (Shimura 1963).

The smallest leaf I found that does (b) is shimura-split2's `ShimuraHolFamilyAb`, or `ShimuraHolModAll` (equivalent
to it given one fine witness, proved by shimura-split2). The holomorphic moduli map is the "remaining link" that
kinds.tsv names for `shimuraFamilyAb`. It is the published statement once one identifies Shimura's `V_S` with a
component of the fine moduli scheme `Y₃` (Deligne 1971 §4). That identification is the pending reading.

The proposed reading targets, all UNVERIFIED:
* Shimura, Ann. of Math. 78 (1963), analytic families;
* Shimura, Ann. of Math. 85 (1967), Main Theorem I and §§2-3;
* Deligne, Sém. Bourbaki 389 (1971), §4;
* Milne, *Introduction to Shimura varieties*, §§8 and 14.

## 3. (a): `Y3Connected` without the composite

dcy3-used read four clauses of the composite, and two of them come from its map `Ψ(τ, g)`:
* openness of preimages of `τ ↦ Ψ(τ, g)`, for every `g`;
* the relation `DCRel` on `Ψ`.

`ShimuraHolFamilyAb` has no `Ψ`. Its family `y_τ` is known only as a QM pair: the level structure of `y_τ` may jump
with `τ`. The proof in `connected_of_holFamily` (VERIFIED, compiled) avoids both clauses:

1. **Level as a global unit** (`levelUnit`). The object at `y_τ` is `T(τ, (c_τ)⁻¹)` for a unit `c_τ ∈ 𝒪^×`. This is
   shimura-split2's `complexUnifL3_of` proof, run on the given uniformization, with the unit kept global.
2. **Families.** For `w ∈ 𝒪^×`, put `A^w_τ = y_τ ≫ e_w`. Here `e_w : Y ≅ Y` right-multiplies the level structure by
   `w` (`R1heckeProps`, from the chain's `heckeOfFine_proof`; it needs `R1fpProps = R1fpPropsAb`, which holds under
   `mumfordGroupLaw`). The object of `A^w_τ` is `T(τ, (w c_τ)⁻¹)` (`mIsAt_rightMul`). Every `ℂ`-point is some
   `A^w_τ`, by `QMComplexUnif` and `levelUnit`.
3. **χ.** For a clopen `U ⊆ Y`, `χ(w) = [A^w_τ ∈ U]` does not depend on `τ` (`tind`: openness, and `ℍ` is
   connected). Three relations hold:
   * **classes:** `χ` depends only on `w mod 3`, by `K₃` and `DCRelTransport`;
   * **reciprocity at `τ₁ = √2 + i`**, the CM point of `q : ℚ(i) → B`, `i ↦ i + j`:
     - `MainTheoremCM` gives `QMReciprocityL3`, which moves `A^w_{τ₁}` by some `σ ∈ Aut(ℂ)` to `A^{w a}_{τ₁}`.
     - Here `a = c₁ c c₁⁻¹` and `c = 1/2 + i − j/2 ≡ (1+i+j)⁻¹ mod 3`. This uses dcy3-used's idele `s₄`, with
       `q̂(s₄) = c⁻¹k`, `k ∈ K₃` (`h4_K3`).
     - `σ` does not move the underlying point (`ptC_galPt`), so `χ(w) = χ(w a)`.
   * **the elliptic point `τ₂ = i√3`** of `ω = (1+j)/2` (order 6, `nrd ω = 1`):
     - the eigenvalue is `(1+i√3)/2` (`heig2`), so `T(τ₂, g) ≅ T(τ₂, ω g)`;
     - hence `χ(w) = χ(w b)` with `b = c₂ ω⁻¹ c₂⁻¹`.
4. **Group theory.**
   * The conjugators `c₁ = c_{τ₁}` and `c₂ = c_{τ₂}` are unknown, so `χ` is right-invariant under one conjugate of
     `c` (order 8 mod 3) and one conjugate of `ω⁻¹` (order 6). After conjugating `χ`, only `v = c₁⁻¹c₂` is unknown.
   * `decide` over `(𝒪/3𝒪)^×` (72 classes, coordinates of `LeafQM.ofInt`, product `ShimuraGlue.mulCoordR`) checks:
     - `inv3_spec`: the inverse formula;
     - `nList_spec`: for every `v`, the square of `v ω̄⁻¹ v⁻¹` is one of 4 classes of order 3;
     - `tab2_spec`: for each of these `n`, every class is the word `n^{e₁}(c n c⁷)^{e₂}c^k`, with a 288-entry table
       from `scratch/composite-out/py/classes.py`.
   * So `χ` is constant (`const_of_inv'`), and `U` is empty or all of `Y`.

Class number one is not used, and neither is any map `Ψ`. The Galois relation is the only arithmetic input, and
`MainTheoremCM` supplies it.

## 4. A variant with a new leaf (superseded)

The first route used a new leaf: `ShimuraHolFamilyL3`, which is `ShimuraHolFamilyAb` with the level structure fixed
(`MIsAt P τ g₀` for one `g₀ ∈ 𝒪̂^×`). It needs no group theory beyond dcy3-used's `decomp3`. That route also compiles
(`scratch/composite-out/CompositeOutWithL3.lean`, 0 errors, standard axioms). It is not used, because §3 does without
the extra clause.

The leaf would have been rated published (Shimura's `φ_S(z)` is the moduli point of `(A_z, ι, C, t_z)` with the level
point `t_z`), pending the same reading as `ShimuraHolModAll`.

## 5. Checks (all VERIFIED)

* `lake env lean ZInQKernel/Contrib/OneProof/CompositeOut.lean`:
  - 0 errors and 0 warnings, about 15 s (`scratch/composite-out/compile3.txt`);
  - `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for `y3ConnectedAb_of_hol`, `y3Connected_of_hol`,
    `y3Connected_of_modAll` and `compositeUses_of_hol`.
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.CompositeOut`:
  "Build completed successfully (12998 jobs)". The build tree was copied from p1-quot3's worktree, which has the same
  shared sources; ShimuraSplit2 and QMRecPrinted were built here.
* `#discharges` (`scratch/composite-out/Discharges-output.txt`): "63 open hypotheses, 2215 theorems checked,
  7 discharge one".
  - No current open field is matched by `CompositeOut`. This is expected: the composite itself is not proved, only its
    three uses, the same situation as dcy3-used.
  - Its uses `rayClassCMAb` and `shimuraFamilyAb` are older-generation fields.
* Bypass fold dry run `scratch/composite-out/BypassFold.lean`, built on dcy3-used's dry run:
  - `OpenResearchLeaves23` is `OpenResearchLeaves22` without `shimuraMainThmIDeligneY3AbU`, with `mainTheoremCM` and
    `shimuraHolModAll`;
  - `openResearchLeaves20_of_23`;
  - dcy3-used's `addedLeaves8_of18`, with `y3Connected := CompositeOut.y3Connected_of_modAll …`;
  - `sixContactMin_of_open31` and `frozenTarget_compositeOut` both depend on `[propext, Classical.choice, Quot.sound]`
    (`BypassFold-output.txt`).
* Autofold spec `scratch/composite-out/autofold.json`:
  - a bypass, because the composite is not proved as stated;
  - the leaves `mainTheoremCM` (published) and `shimuraHolModAll` (published, pending reading), with the same leaf
    rows as qmrec-printed's spec;
  - the three consumer terms.

## 6. What remains

* **Hand fold.** The integrator applies it after dcy3-used's bypass (§5). If qmrec-printed's spec is applied first,
  the same two leaves are already present, and this task adds only the `y3Connected` term.
* **Readings.**
  - `ShimuraHolModAll`: Shimura 1963 / 1967 MT I with Deligne §4 for `Y₃`. Once read, the count drops by 1.
  - `MainTheoremCM`: Shimura 1998 §18 or Milne ISV §11, for the torsion clause.
* **Rows proposed for `docs/research/locators.md`.** Not edited here; they are the rows qmrec-printed and
  shimura-split2 already proposed for these two leaves.
* No statement was changed.
