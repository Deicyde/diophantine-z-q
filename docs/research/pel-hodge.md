# pel-hodge: holfam's PEL family with its fibres in the print's Hodge / H₁ form

Task pel-hodge, 2026-11-16. Base: fork main 60a3fac7 (leaf-fold28b), with origin/wip/unif-topology (dbf043a4,
which contains unif-printed 9c2e1809) and origin/wip/holfam (93220b34) merged in. Both merges were clean. This is
model work and no human has reviewed it.

Marks used below:
* **VERIFIED**: compiled, or read in a file.
* **STANDARD**: published, with a reference.
* **SPECULATIVE**: a judgement.
* **UNVERIFIED**: a locator recalled without a source. This host has no network.

## 1. Result

**holfam's leaf `HolFamilyPrinted.PELHolFamily` is now proved in Lean from a new leaf,
`PELHodge.PELHolFamilyHodge`.** The new leaf states the fibre of Deligne's universal family over `[τ, 1]` in the form
the prints use: `H₁` with its `𝒪`-action and its Hodge structure. The proof also uses the textbook field
`uniformizationLeafAll`. `gagaMorphism` is not used. Every theorem depends only on
`[propext, Classical.choice, Quot.sound]` (VERIFIED).

The converse is proved as well, so the new leaf is not stronger than holfam's, given the textbook field:

```lean
theorem PELHodge.pelHolFamilyHodge_iff (hU : BPAnalytic.Uniformization.UniformizationLeafAll) :
    PELHolFamilyHodge ↔ HolFamilyPrinted.PELHolFamily
```

The only difference between the two leaves is the fibre clause.
* **holfam's clause (lattice coordinates):** an `ι`-compatible analytic uniformization `ℂ² → A(ℂ)` whose kernel is
  `Λ_τ = ι(𝒪)(τ,1)ᵀ`.
* **The new clause (`IsHodgeFibre`):** `H₁(A(ℂ), ℤ)`, with its `𝒪`-action and its Hodge structure, is
  `(Λ_τ, ι, i)`. Equivalently, it is `(𝒪, left multiplication, h_τ)`.

Going from the second to the first is Riemann's `A(ℂ) = Lie A / H₁(A, ℤ)`. Here that step is the Lean proof
`h1Form_iff`, which identifies `H₁(A(ℂ), ℤ)` with the period lattice of the uniformization.

**File:** `ZInQKernel/Contrib/OneProof/PELHodge.lean`, namespace `PELHodge`, about 33 KB. It imports
`ZInQKernel.Contrib.OneProof.HolFamilyPrinted` (which defines the discharged statement) and
`ZInQKernel.Contrib.OneProof.UniformizationPrinted` (for the classical topology).

**Effect on the count** (SPECULATIVE until the integrator applies it):
* With this file, the composite `shimuraMainThmIDeligneY3AbU` (strict GLUE) is replaced by `mainTheoremCM`
  (printed, LEAF; mtcm-polar proves it) and `pelHolFamilyHodge`. I rate `pelHolFamilyHodge` printed form (§4).
* That is **−1 strict GLUE**. The same holds against holfam's fold, where `pelHolFamily` was "pending reading"
  (GLUE) and is now replaced by a printed-form leaf.
* **Caveat:** if the reviewer keeps holfam's separate flag on the analytic clause (holomorphy of `τ ↦ [τ, 1]`, §4),
  the count is unchanged until that reading is done.

## 2. The statements

All definitions are over Mathlib or the repository's own definitions. None is a structure invented for the purpose.

```lean
attribute [local instance] UnifPrinted.classicalTopology   -- the topology of A(ℂ)

/-- H₁(A(ℂ), ℤ) = π₁(A(ℂ), 0)ᵃᵇ (Hurewicz). -/
def H1 (A : AbVar ℂ) : Type := Abelianization (FundamentalGroup (A.Pt ℂ) 1)

def loopClass {A : AbVar ℂ} (lp : Path (1 : A.Pt ℂ) 1) : H1 A :=
  Abelianization.of (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk lp))

/-- Λ is H₁(A, ℤ) inside Lie A, through e = exp_A ∘ L. -/
def H1Form (A : AbVar ℂ) {n : ℕ} (Λ : Submodule ℤ (Fin n → ℂ))
    (e : (Fin n → ℂ) → CPts A (RingHom.id ℂ)) : Prop :=
  IsAnalyticHom (RingHom.id ℂ) e ∧ (∀ v ∈ Λ, e v = 1) ∧
    ∃ lp : Λ → Path (1 : A.Pt ℂ) 1,
      (∀ v (t : unitInterval), lp v t = e (((t : ℝ) : ℂ) • (v : Fin n → ℂ))) ∧
      Function.Bijective (fun v => loopClass (lp v))

def IsHodgeFibre (τ : UpperHalfPlane) (P : QML3 ℂ) : Prop :=
  ∃ e, H1Form P.A (QM.qmLattice τ.im_pos.ne') e ∧ HDec.HSyn.G0Split.FibreQM.IotaCompatible P e

/-- LEAF: holfam's PELHolFamily with IsHodgeFibre as the fibre clause. -/
def PELHolFamilyHodge : Prop :=
  ∃ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom ∧ SmoothOfRelativeDimension 1 S.hom ∧
    ∃ 𝒜 : R1UnivRigid.QMAbScheme S.left,
      (∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ S), ∃ P : QML3 K,
        IsFibreOf 𝒜.toQMFamily s.left P) ∧
      ∃ sτ : UpperHalfPlane → (fieldPt ℂ ⟶ S),
        ShimuraSplit.IsHolFamily (X := S.left) (fun τ => (sτ τ).left) ∧
        ∀ τ : UpperHalfPlane, ∃ P : QML3 ℂ, IsFibreOf 𝒜.toQMFamily (sτ τ).left P ∧ IsHodgeFibre τ P
```

### How the H₁ form reads

**The topology.** `A(ℂ)` carries unif-printed's `classicalTopology`. This is the coarsest topology in which every
`U(ℂ)` is open and every regular function is continuous. unif-topology proves
`classicalTopology_eq_analyticTopology`, the equality with the textbook analytic topology (affine charts in `ℂᵏ`,
glued), for schemes locally of finite type.

**`H₁`.** `H1 A = π₁(A(ℂ), 0)ᵃᵇ` uses Mathlib's `FundamentalGroup` and `Abelianization`. For a path-connected space
this is `H₁(A(ℂ), ℤ)`, by Hurewicz (STANDARD).

**`Lie A`, through `e`.** `e : ℂⁿ → A(ℂ)` is a holomorphic homomorphism (`IsAnalyticHom`). Such a homomorphism is
`exp_A ∘ L` for a unique `ℂ`-linear map `L : ℂⁿ → Lie A` (STANDARD).

**`Λ` is `H₁(A, ℤ)` inside `Lie A`.** The map `λ ↦ [t ↦ exp_A(tλ)]` is the canonical isomorphism
`ker exp_A ≅ π₁(A(ℂ), 0)`. So the bijectivity of `v ↦ [t ↦ e(tv)]` says that `L` maps `Λ` onto `H₁(A, ℤ)` inside
`H₁(A, ℝ) = Lie A`. In other words, `Λ ⊗ ℝ = ℂⁿ` with its complex structure is `H₁(A, ℝ)` with its Hodge structure.

**The `𝒪`-action.** `IotaCompatible P e`, i.e. `e(ι(a) z) = ι_P(a)(e z)`, says that `L` is `𝒪`-linear, so the
isomorphism `Λ_τ ≅ H₁` is `𝒪`-linear.

**What `IsHodgeFibre` says.** `x ↦ ι(x)(τ,1)ᵀ` is an `ℝ`-isomorphism `B ⊗ ℝ → ℂ²` that carries `𝒪` onto `Λ_τ`.
Through it, `IsHodgeFibre τ P` is the print's
"`(H₁(A, ℤ), 𝒪, Hodge structure) ≅ (𝒪, left multiplication, h_τ)`".

**What `H1Form` does not say.** It does not say that `e` is onto, nor that its kernel is exactly `Λ`. Those two facts
are the uniformization theorem.

## 3. The proof (GLUE, all proved)

### `h1Form_iff`

```lean
theorem h1Form_iff (hU : UniformizationLeafAll) {A : AbVar ℂ} {n : ℕ} {Λ : Submodule ℤ (Fin n → ℂ)}
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (e : (Fin n → ℂ) → CPts A (RingHom.id ℂ)) :
    H1Form A Λ e ↔ IsUniformization (RingHom.id ℂ) Λ e
```

The proof uses the uniformization `φ : ℂ^g/Λ' ≃ A(ℂ)` given by `UniformizationLeafAll A`.

**Step 1 (`continuous_phi`, `isOpenMap_phi`, `phiHomeo`).** `φ` is a homeomorphism onto `A(ℂ)` with its classical
topology.
* Continuity: preimages of the basic sets `{P ∈ U(ℂ) : |f(P) − z| < ε}` are open, by clause (i) of the
  uniformization.
* Openness: by clause (iii) and finite intersections of basic sets.

**Step 2 (`isCov`).** `p = φ ∘ proj : ℂ^g → A(ℂ)` is a quotient covering map for the action of `Λ'`. This uses
Mathlib's `IsQuotientMap.isAddQuotientCoveringMap_of_addSubgroup`. So Mathlib's monodromy gives an injective
homomorphism `Θ : π₁(A(ℂ), 0) → Λ'ᵐᵒᵖ` (`fundamentalGroupToMulOpposite`, which is injective because `ℂ^g` is simply
connected).

**Step 3 (`monodromy_line`).** For `w ∈ Λ'`, `Θ` sends the loop `t ↦ p(tw)` to `w`, since its lift is `t ↦ tw`.

**Step 4 (forward direction).** Write `e = p ∘ D` with `D` `ℂ`-linear. This is the existing
`exists_complexLinear_of_analytic_strong`. Then:
* `D(Λ) ⊆ Λ'`.
* `Θ[t ↦ e(tv)] = Dv`.
* Surjectivity of `Λ → H₁` gives `Λ' ⊆ D(Λ)`. Here `Θ` is factored through the abelianization, which is possible
  because `Λ'` is commutative.
* Injectivity of `Λ → H₁`, together with the injectivity of `Θ`, makes `D` injective on `Λ`.
* So `D : Λ ≃ Λ'`, and `ZLattice.rank` gives `2n = 2g`.
* `D` is onto because its range contains the full lattice `Λ'` (`IsZLattice.span_top`). Hence `D` is bijective.
* Therefore `ker e = D⁻¹(Λ') = Λ` and `e` is onto.

**Step 5 (`exists_H1_of_isUniformization`, converse).**
* `D` is injective, because a complex line inside the discrete group `Λ` is zero (`PreconnectedSpace.constant`).
* `D(Λ) = Λ'`.
* Every class in `π₁` is `Θ⁻¹` of some `Dv`.

### PEL-level theorems

| theorem | statement |
|---|---|
| `isHodgeFibre_iff hU τ P` | `IsHodgeFibre τ P ↔` holfam's lattice clause |
| `pelHolFamily_of_hodge hU : PELHolFamilyHodge → HolFamilyPrinted.PELHolFamily` | the discharge |
| `pelHolFamilyHodge_of_pel hU` | the converse |
| `pelHolFamilyHodge_iff hU` | both directions |
| `shimuraHolModAll_of_hodge`, `shimuraFamilyAb_of_hodge`, `y3Connected_of_hodge`, `compositeUses_of_hodge` | holfam's consumers, with `deligneComponentsX6PrintedAb` |
| `witness_of_r1fp`, `witness_of_r1r2`, `witness_of_r1r2Ab`, `witness_of_grX6Ab`, `shimuraHolFamilyAb_of_hodgeW`, `compositeUses_of_hodgeW`, `compositeUses_of_hodge_gr` | the same consumers without `deligneComponentsX6PrintedAb`, as §6 explains |

## 4. The new leaf and its rating

| leaf | kind | printed form? | reason |
|---|---|---|---|
| `PELHodge.PELHolFamilyHodge` | published | **yes** for the fibre clause, which is now the print's `H₁` / Hodge description. The rest is holfam's leaf unchanged. Locators UNVERIFIED. | see below |

**Published statements** (all UNVERIFIED):
* Deligne, *Travaux de Shimura*, Sém. Bourbaki 389 (1971), §§4.9–4.17 and Example 5.8. For a PEL datum
  `(B, *, V, ψ)` and a neat compact open `K`, this gives the moduli scheme `M_K` over the reflex field, with its
  universal abelian scheme. It also gives `M_K(ℂ) = G(ℚ)\X × G(𝔸_f)/K`, where `[h, g]` carries the abelian variety
  `A` with `H₁(A, ℚ) = V` (`B`-linearly), Hodge structure `h` and lattice `H₁(A, ℤ) = gL`.
* Milne, *Introduction to Shimura varieties* (2005), §8 (PEL Shimura varieties as moduli varieties, described in
  terms of `H₁` and Hodge structures) and §14 (the model over the reflex field).

**Why it is a consequence of the print, and not stronger.** Take `B` of discriminant 6, `V = B`, `L = 𝒪`, `G = B^×`,
`K₃ = ker((𝒪⊗ℤ̂)^× → (𝒪/3𝒪)^×)`, `S = M_{K₃}`, `𝒜` its universal family, and `s_τ = [h_τ, 1]`. The leaf then asks
for:
* one family;
* the fibre through `H₁`, with its `𝒪`-action and Hodge structure only, with no polarization and no level clause.

The dictionary used to state this over Mathlib is standard:
* `H₁ = π₁ᵃᵇ` (Hurewicz);
* `Lie A` through holomorphic homomorphisms `ℂⁿ → A(ℂ)`;
* `ker exp_A ≅ π₁` by `λ ↦ [t ↦ exp(tλ)]`.

It is the textbook definition of the Hodge structure of `H₁(A, ℤ)` (`H₁(A, ℝ) = Lie A`). The new leaf is equivalent
to holfam's under the textbook field (`pelHolFamilyHodge_iff`), so it has the same truth value. It is not vacuous:
under the uniformization theorem it holds for the genuine family.

**What changed relative to the review.** The review rated holfam's leaf "consequence" because the prints describe
the fibre in `H₁` / Hodge form, and lattice coordinates need `A(ℂ) = Lie A / H₁(A, ℤ)`. That step is now the Lean
proof `h1Form_iff`, from `UniformizationLeafAll`. unif-printed and unif-topology prove `UniformizationLeafAll` from
Mumford's printed complex-torus theorem over the analytic topology.

**What is still to read.** This is holfam's separate flag, the analytic clause: whether Deligne §4 (or Milne §8)
identifies `M_K(ℂ)` with `G(ℚ)\X × G(𝔸_f)/K` *as complex spaces*, so that `τ ↦ [h_τ, 1]` is holomorphic.
* I flag the leaf "unread". It is a new printed leaf, and the analytic clause is to be checked in the same reading,
  because the print states the identification of `M_K(ℂ)` as that of the analytic Shimura variety. That last point
  is SPECULATIVE until read.
* If the reader finds the analytic statement missing from the cited sections, the leaf should be flagged "pending
  reading" as holfam's was.

**Normalization.** `h_τ` is the complex structure that makes `x ↦ ι(x)(τ,1)ᵀ` `ℂ`-linear. The match between `τ ∈ ℍ`
and the print's `h ∈ X` is a convention, the same as in holfam's leaf. The leaf asserts only that *some* holomorphic
`τ ↦ s_τ` has these fibres.

## 5. Checks (all VERIFIED)

**Build tree.** Lake could not rebuild the fold28b chain here: TailX now imports `ModularEquationGeneric`, so the
667-file FLT port would have to be built, and no worktree on this host has it built. So the build tree was copied
(reflink) from `~/dzq-wt/holfam`, which is fold25: the same sources for every module `PELHodge` and holfam's files
import, except the TailX–TailZ36 bundle files that fold28b changed to remove `igusaGL2`. `UniformizationPrinted`'s
olean was copied from `~/dzq-wt/unif-printed`. So the checks below run on the fold25 build of the imports, which is
the same environment holfam used. The early-chain modules that the glue reads (`TailC`, `TailQ`, `HDecomp/*`,
`UniformizationPrinted`) have identical sources in fold25 and fold28b.

**The file.** `lake env lean ZInQKernel/Contrib/OneProof/PELHodge.lean`: 0 errors, 0 warnings. The olean was
written with `lake env lean -o`.

**`#discharges`** (`scratch/pel-hodge/Discharges.lean`; output in `Discharges-output.txt`):
* It reports "63 open hypotheses, 2304 theorems checked, 9 discharge one". The 9 are the 7 pre-existing
  contributions plus 2 from `UnifPrinted`, which `PELHodge` imports.
* No `PELHodge` theorem matches an open field. This is expected: `pelHolFamily` becomes a field only with holfam's
  fold, and holfam's own `#discharges` matched nothing either.
* `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all 18 listed theorems.

**Bypass dry runs:**
* `scratch/pel-hodge/BypassFold.lean` is holfam's dry run with the field `pelHolFamily` replaced by
  `pelHolFamilyHodge`. `sixContactMin_of_open31` and `frozenTarget_pelHodge` have standard axioms
  (`BypassFold-output.txt`).
* `scratch/pel-hodge/BypassFoldPi0.lean` is the same, with the three consumers taking the fine witness from the
  research field `gonzalezRotgerX6Ab` instead of `deligneComponentsX6PrintedAb`. `frozenTarget_pelHodgePi0` has
  standard axioms. In it, the only remaining reader of `deligneComponentsX6PrintedAb` is `x6Rows_of18`, which is
  pi0-prune's reroute.

**Rerun on the true merged base (fold28b + unif-topology + holfam).** After the checks above, the FLT port, the
fold28b chain and holfam's files were built here.
* `lake build ZInQKernel.Contrib.OneProof.PELHodge`: "Build completed successfully (12904 jobs)", with
  `CompositeOut`, `HolFamilyPrinted` and `PELHodge` built from source. See `scratch/pel-hodge/build-fold28b-tail.txt`.
* `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges`: "Build completed successfully (13667
  jobs)".
* `#discharges` on fold28b (`Discharges-output-fold28b.txt`): "61 open hypotheses, 2702 theorems checked, 8
  discharge one". No `PELHodge` theorem matches an open field, as expected. All 18 `#print axioms` are standard.
* Both bypass dry runs compile on fold28b as well, with standard axioms (`BypassFold-output-fold28b.txt`,
  `BypassFoldPi0-output-fold28b.txt`). They still have holfam's fold25 bundle shape, so they are compile checks of
  the consumer terms, not folds of fold28b.

**Not run.** `autofold.py --dry-run`: `pelHolFamily` is not a field on this base, and holfam's spec is a hand-folded
bypass.

## 6. Fold

**Spec `scratch/pel-hodge/autofold.json`.** It applies after holfam's fold. It discharges `pelHolFamily` by
`_root_.PELHodge.pelHolFamily_of_hodge {t}.uniformizationLeafAll {n}.pelHolFamilyHodge` and adds the leaf
`pelHolFamilyHodge`: kind published, flag "unread: new printed leaf; …analytic clause to be checked in the same
reading", source Deligne 389 §§4.9–4.17, Ex. 5.8 and Milne ISV §§8, 14.

**Spec `scratch/pel-hodge/autofold-bypass.json`.** It replaces holfam's spec: holfam's bypass with `pelHolFamily`
replaced by `pelHolFamilyHodge`. It has two sets of consumer terms:
* `consumers`, with `deligneComponentsX6PrintedAb`; the dry run is `BypassFold.lean`;
* `consumers_pi0`, through `PELHodge.compositeUses_of_hodge_gr {r}.gonzalezRotgerX6Ab …`, for after pi0-prune; the
  dry run is `BypassFoldPi0.lean`.

**pi0-prune.** holfam's consumers read only the fine witness `∃ Y Φ, R1fpPropsAb Y Φ` of
`deligneComponentsX6PrintedAb` (`ShimuraSplit2.witness_of_x6`). The same witness comes from any of these:
* the R1fp clause of `r1r2`: `witness_of_r1r2`, through `R1fpProps = R1fpPropsAb` under `mumfordGroupLaw`
  (`r1fpProps_eq_ab_gl`). pi0-prune's `R1R2fpRepW` destructures to the hypothesis of `witness_of_r1fp` in the same
  way.
* `R1R2fpRepAb`: `witness_of_r1r2Ab`.
* the research field `gonzalezRotgerX6Ab`: `witness_of_grX6Ab`.

The consumers `compositeUses_of_hodgeW` and `compositeUses_of_hodge_gr` take that witness. pi0-prune is not merged
here.

## 7. Proposed row for `docs/research/locators.md` (not edited here)

| leaf | source | status |
|---|---|---|
| `pelHolFamilyHodge` | Deligne, Sém. Bourbaki 389 (1971) §§4.9–4.17, Example 5.8; Milne, ISV (2005) §§8, 14 | UNVERIFIED. To check: (i) the description of the point `[h, g]` by `H₁(A, ℚ) = V`, Hodge structure `h`, lattice `gL` (the fibre clause, now in this form); (ii) `M_K(ℂ) ≅ G(ℚ)\X × G(𝔸_f)/K` as complex spaces (holfam's analytic clause); (iii) the conventions of row R1 shared with clause (R) of `deligneComponentsX6PrintedAb`: lattice `𝒪`, level 3, `E(G, h) = ℚ`. |

## 8. What remains

* The reading in §7.
* The fold: either `autofold.json` after holfam's fold, or `autofold-bypass.json` in place of holfam's spec. Each has
  a compiled dry run.
* No statement was changed. Nothing under `ZInQKernel/` was edited except the new file
  `ZInQKernel/Contrib/OneProof/PELHodge.lean`.

## 9. Statement review (model, read-only, no Lean run)

A read-only adversarial review by a subagent, which read the code but ran no Lean, found no soundness issue.

* **The `H₁` form.** `H1Form` / `IsHodgeFibre` is the Hodge-structure isomorphism.
  * It is not stronger than that: it never requires `e` to be onto or to have kernel exactly `Λ`.
  * It is not vacuous, given `phiHomeo` and `h1Form_iff`.
* **The `𝒪`-action.** `IotaCompatible` and `qmLattice` use the same `iota`. So `𝒪` acts on `Λ_τ` by left
  multiplication.
* **The leaf against the print.** The leaf copies holfam's non-fibre clauses unchanged and drops the polarization
  and level data, so it is weaker than the print. The `h_τ` / `h̄_τ` convention does not matter, because `sτ` is
  existential.
* **The topology.** `H1`, `loopClass` and the `Path` in `H1Form` all elaborate under the same local instance,
  `classicalTopology`. No other `TopologicalSpace` instance on `A.Pt ℂ` exists in the tree (grep).
* **Inherited from holfam, not re-audited:** `IsHolFamily` and the clause "every field fibre is a `QML3`".
