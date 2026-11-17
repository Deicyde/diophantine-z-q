# y3abu-strict: y3abu-print's two leaves under the strict rule

Task y3abu-strict (2026-11-16/17). Base: wip/y3abu-print 579a89bb. origin/main c1e4ed1b is already an ancestor, so
the merge was a no-op. The base already contains grx6ab-print and elkies-print.

Contributor files, both under `ZInQKernel/Contrib/OneProof/`:
* `ShimuraY3Strict.lean` (namespace `Y3ABUStrict`). It imports `…ShimuraY3Print` (y3abu-print's file, which defines
  `Y3FineModuliAb` and imports `…RayClassShimura`, the module that defines the field). It never imports `Main`.
* `ShimuraY3StrictLemmaP.lean` (namespace `Y3ABUStrict.LemmaP`). A helper that imports only
  `ZInQKernel.HDecomp.QM.Polar` and `ZInQKernel.HDecomp.Analytic.QMLattice`.

Neither file has a `sorry`. Scratch: `scratch/y3abu-strict/` (log: `log.md`).

Marks used below:
* VERIFIED: compiled, or read in the tree.
* STANDARD: published, with an exact reference.
* SPECULATIVE.
* UNVERIFIED: a theorem number recalled from memory. This host has no network.

## 1. Result

**(b) is done.** y3abu-print's leaf `DeligneCanonicalModelY3Every` read two printed theorems as one. It is now split
into those two statements, and the glue between them is proved in Lean:

```
Y3ABUStrict.shimuraMainThmIDeligneY3AbU_of_strict :
  Y3ABUPrint.Y3FineModuliAb → Y3ABUStrict.DeligneModuliY3Every → Y3ABUStrict.DeligneReciprocityY3Every →
    RayClassCFT.ShimuraMainThmIDeligneY3AbU
```

* `DeligneModuliY3Every` is the **moduli interpretation**: Milne ISV §8 and Deligne §4. Its moduli clause now pins
  the **level structure** at `𝒪̂^×`. That is what makes the split possible (§3.2).
* `DeligneReciprocityY3Every` is the **canonical-model property**: Milne §14 and Deligne Cor. 5.7 / Ex. 5.8. It says
  that every `Ψ` with that moduli interpretation satisfies Shimura's reciprocity law. It makes no existence claim.
* Each every-witness form is proved equivalent to its form on one witness: `deligneModuliY3Every_of_one` and
  `deligneReciprocityY3Every_of_one`.

**(a) cannot be done as posed, for the same reason sir-printed found.** The polarized printed moduli problem cannot be
stated over genuine Lean definitions:
* Mathlib v4.35 and the tree have no dual abelian scheme over a base, no polarization over a base, and no Weil
  pairing over a base.
* The tree's `PkgI3.WeilPairing.Polarization` exists only over a field, sits over `WeilDual`, and its own docstring
  says it is unsafe outside existential positions. It cannot carry the uniqueness half of Lemma P: `−λ` qualifies,
  and `WeilDual` itself is not unique.

So the passage from the PEL functor to the kernel's polarization-free functor cannot be stated, let alone proved. That
passage is the **relative** Lemma P over the bases `R1univAbProps` quantifies over, the proper smooth curves over `ℚ`.
It also cannot be avoided by restricting to the consumer's bases (§5.1).

**Lemma P is proved here as far as it can be stated, in Riemann-form language, for the kernel's QM tori.** New and
compiled, with standard axioms (§4):
* `lemmaP_lattice_unique`: for every complex structure `j` on `B_ℝ` commuting with `𝒪`, exactly one form is
  alternating, Rosati of type `μ`, principal and positive. It combines rv-qm-polar's pieces, which had not been
  combined before.
* `lemmaP_qmTorus` / `lemmaP_qmTorus_eq`: on `ℂ²/Λ_τ`, `Λ_τ = ι(𝒪)(τ,1)ᵀ`, multiplication by `i` is right
  multiplication by an explicit `j_τ`. The unique principal Riemann form of type `μ` is `E₀ = trd(μ⁻¹xȳ)` for every
  `τ ∈ ℍ`.

What stays out of Lean is Riemann's theorem (polarizations correspond to Riemann forms; there is no dual abelian
variety in Mathlib) and everything over a base.

**Ratings and count.**

| leaf | what it is | printed form? | under the strict rule |
|---|---|---|---|
| `y3FineModuliAb` (y3abu-print, unchanged) | the fine moduli scheme `Y₃` with its universal family | **yes, if read from a polarization-free print** at level `K₃` (Boutot–Carayol, Astérisque 196-197, ch. III §1; Buzzard, Duke 87 (1997) §1; recalled, UNVERIFIED) | LEAF only with that print; from a PEL print, the relative Lemma P is a step that cannot be stated in Lean, so GLUE |
| `deligneModuliY3Every` (new) | `Y₃(ℂ)` with its complex uniformization and level structures | **yes, if read from a polarization-free print** (Boutot–Carayol ch. III §1, recalled) | LEAF only with that print; from the PEL print (Milne §8, Deligne §4), the step is Lemma P over `ℂ` (its Riemann-form core is proved here; Riemann's theorem is missing), so GLUE |
| `deligneReciprocityY3Every` (new) | the Galois action on the CM points of `Y₃` (canonical-model property) | **yes**: a direct specialization of the printed canonical-model property. It uses only the forgetful direction, polarized objects to polarization-free objects, so Lemma P is not needed | LEAF in both readings |

* The autofold dry run, with flags that state only locator issues (§6): strict **16/21 on 37 → 19/20 on 39, −1
  GLUE**. Combined with grx6ab-print and elkies-print: **16/21 on 37 → 22/18 on 40, −3 GLUE**. Both fold checks
  compile with standard axioms.
* **Caveat.** The −1 holds exactly when a reader confirms the polarization-free form in Boutot–Carayol ch. III §1 or
  Buzzard 1997 §1 at level `K₃`. Note that `K₃` is full level 3 at the ramified prime 3, since `disc B = 6`.
* If only PEL prints are confirmed, `y3FineModuliAb` and `deligneModuliY3Every` become "pending reading" (GLUE), and
  the fold would *raise* the strict count by 1. In that case the field should stay unfolded.
* `deligneReciprocityY3Every` rates LEAF either way. It is the one piece of y3abu-print's composite leaf that is now
  strictly printed regardless of the polarization question.

## 2. The field and what the chain reads

These are unchanged from y3abu-print §2 (VERIFIED there). The field is `ShimuraMainThmIDeligneY3AbU := ∃ Y Φ,
R1fpPropsAb Y Φ ∧ ∃ Ψ, DeligneBodyAt Y Φ Ψ ∧ ModuliAtUnits Y Φ Ψ` (`RayClassShimura.lean:1152`).

`DeligneBodyAt` has these clauses:
1. onto;
2. fibres = `DCRel`, stated as an iff;
3. holomorphic in `τ` for every `g`;
4. `IsShimuraHolFamily` at `g = 1`;
5. reciprocity.

`ModuliAtUnits` is the QM torus at every `u ∈ 𝒪̂^×`, without the level structure.

The chain reads clauses 1, 3 (open-preimage half), 4, 5 and `ModuliAtUnits`. It reads only the `⇐` half of clause 2.
`R1fpPropsAb` is carried into the conclusions.

## 3. The split of (b) (`ShimuraY3Strict.lean`, VERIFIED)

### 3.1 Definitions

```lean
def ModuliLevelAtUnits Y Φ Ψ : Prop :=
  ∀ u ∈ OhatU, ∀ τ, ∃ P : QML3 ℂ, Φ ℂ (Ψ τ u) = M3.mk P ∧
    ∃ Φu, IsUniformization (RingHom.id ℂ) (qmLattice τ.im_pos.ne') Φu ∧ IotaCompatible P Φu ∧
      ∃ w : LeafQM.O, (∃ y ∈ OhatQ, bEmb w = (u⁻¹ : BAQ) + 3 * y) ∧
        ∀ a : LeafQM.O, toMul (P.e.eta a) = Φu ((1/3 : ℂ) • (qmMat (a * w)).mulVec ![τ, 1])
def ModuliInterpAt Y Φ Ψ := onto ∧ (fibres ↔ DCRel) ∧ (holomorphic ∀ g) ∧ ModuliLevelAtUnits Y Φ Ψ
def ReciprocityAt Y Ψ := ∃ ε δ, ∀ K κ q z, IsCMPoint … z → ∀ σ s, ArtinCondC κ σ s → ∀ g,
    galPt σ (Ψ z g) = Ψ z (qHatU q s ^ ε * g)            -- the last clause of DeligneBodyAt, verbatim
def DeligneModuliY3Every := ∀ Y Φ, R1fpPropsAb Y Φ → ∃ Ψ, ModuliInterpAt Y Φ Ψ
def DeligneReciprocityY3Every := ∀ Y Φ, R1fpPropsAb Y Φ → ∀ Ψ, ModuliInterpAt Y Φ Ψ → ReciprocityAt Y Ψ
```

The first three clauses of `ModuliInterpAt` and the first two conjuncts of `ModuliLevelAtUnits` are the field's
clauses, copied verbatim. The proved glue is:
* `one_mem_OhatU`;
* `moduliAtUnits_of_level`, which forgets the level structure;
* `body_of_split`, which gives `DeligneBodyAt ∧ ModuliAtUnits` from `ModuliInterpAt ∧ ReciprocityAt`;
* `deligneCanonicalModelY3Every_of_split`, the two leaves to y3abu-print's leaf;
* `shimuraMainThmIDeligneY3AbU_of_strict`, the discharge;
* `moduliInterp_transport`, `reciprocity_transport`, `deligneModuliY3Every_of_one` and
  `deligneReciprocityY3Every_of_one`. These derive the every-witness form from the form on one witness, through
  `Y3ABUPrint.compare_iso_ab`.

### 3.2 Why the level structure is in the moduli leaf, and why `u⁻¹`

Mathematical argument, checked by hand: SPECULATIVE as a reading of the print, STANDARD as mathematics.

* **Without the level structure the split is false.** gt-rayclass §3 and y3abu-print §4.2 give the counterexample.
  `Ψ'(τ, g) = Ψ(τ, g k)` on one geometric component (`k ∈ 𝒪̂^× \ K₃`) keeps onto, fibres, holomorphy and
  `ModuliAtUnits`, but breaks reciprocity. So a reciprocity leaf "for every `Ψ` with the unpinned clauses" would be
  false.
* **The pinned form.** O-linearity forces the level structure at `Ψ(τ,u)` to be `η_w(a) = (1/3)ι(a w)(τ,1)ᵀ mod Λ_τ`
  for some `w ∈ 𝒪` invertible mod 3. The kernel's `Level3.linear` is `η(ab) = ι(a)η(b)`, and the `𝒪`-linear maps
  `𝒪/3𝒪 → (1/3)Λ_τ/Λ_τ ≅ 𝒪/3𝒪` are right multiplications. Then `Level3.ker` holds because `w` is a unit mod 3.
* **Compatibility with the kernel's `DCRel`, `(τ, g) ~ (γτ, γ g k)`.** Let `γ ∈ 𝒪^×` with `nrd γ > 0`. The map
  `v ↦ j(γ,τ)⁻¹ v` is an `ι`-equivariant isomorphism `ℂ²/Λ_τ → ℂ²/Λ_{γτ}`, because `ι(γ)(τ,1)ᵀ = j(γ,τ)(γτ,1)ᵀ`. It
  carries `η_w` to `η_{wγ⁻¹}`. Then:
  * `w(u) = u⁻¹` is consistent, since `(γuk)⁻¹ ≡ u⁻¹γ⁻¹ mod 3`;
  * `w(u) = u` is not.

  This is the inverse in Deligne's moduli map `[τ, g] ↦ (ℂ²/ι(L_g)(τ,1)ᵀ, ι, η ∘ g⁻¹)`, with `L_g = B ∩ 𝒪̂g⁻¹`.
* **The leaf is true for every fine witness.** Define `Ψ(τ, u) := Φ⁻¹[ℂ²/Λ_τ, ι, η_{u⁻¹}]` and extend it by
  `(B⊗𝔸_f)^× = B^×_+ 𝒪̂^×`, which is class number one (`RayClassCFT.classNumberOneB_proof`).
  * Onto: every complex QM surface with level 3 is some `(ℂ²/Λ_τ, ι, η_w)`.
  * Fibres: an `ι`-equivariant isomorphism of QM tori is a scalar `λ` with `λΛ_τ = Λ_τ'`. That forces `τ' = γτ` with
    `γ ∈ 𝒪^×_+`, and the level structures match exactly when `u' ∈ γ u K₃`.
  * Holomorphy comes from the print.
* **The pinned `Ψ` is unique.** Given `(Y, Φ)`, the moduli points `Φ(Ψ(τ,u))` are fixed. Here the reading is the
  convention all the kernel's `IsUniformization`-based moduli clauses already use: "the object at `y` is the torus
  `ℂ²/Λ`" means an algebraic object with that analytic uniformization, and it is unique up to isomorphism by
  Riemann's theorem / GAGA. `DCRel` with class number one then determines `Ψ` on all of `ℍ × (B⊗𝔸_f)^×`. So the
  `∀ Ψ` of `DeligneReciprocityY3Every` ranges over one map: the moduli identification of the print.
* **Possible conventions do not matter.** The only freedom is a constant `c`, `w(u) = c u⁻¹`:
  * `c` central (`±1`) changes `η` by the automorphism `[−1]`, so the moduli point is the same;
  * a global `c ∈ (𝒪/3)^×` is a right translation by `c⁻¹ ∈ 𝒪̂^×`, which normalizes `K₃` and commutes with the left
    action of `q̂(s)`. Reciprocity is unchanged.

  A component-dependent non-central constant does not arise from a uniform formula.

## 4. Lemma P in Lean (`ShimuraY3StrictLemmaP.lean`, VERIFIED, standard axioms)

rv-qm-polar (`ZInQKernel/HDecomp/QM/Polar.lean`) had compiled the pieces: `eq_smul_E0`, `eq_pm_E0_of_principal`,
`riemann_sign` and `lemmaP_lattice`. It listed as not compiled the identification of `E0R` with `E₀ ⊗ ℝ`, the
combination with `eq_smul_E0`, and the transport to `Λ = 𝒪v`. All three are now done for the kernel's tori:

* `realExt E` is the real extension of a `ℚ`-bilinear form on `B`, in coordinates. `realExt_eq` says that if
  `E = c E₀` then `realExt E = c E0R`.
* `lemmaP_lattice_unique (j) (hj : j*j = -1)`: there is exactly one `E : BilinForm ℚ B` that is alternating, has
  `E(ax, y) = E(x, a†y)` (Rosati type `μ`), has `det (E(b_r, b_s)) = 1` on N5's basis of `𝒪` (principal), and has
  `realExt E (x j) x > 0` for every `x ≠ 0` (a Riemann form).
* `iotaR`, the real extension of `BPAnalytic.QM.iota`:
  * `iotaR_mul`: it is multiplicative;
  * `iotaR_ofB`: it extends N5's `ι`;
  * `jτ τ`: an explicit `j_τ = (s√2/2t) i + ((3+|τ|²)/6t) j + ((|τ|²−3)√2/12t) k` for `τ = s + it`;
  * `jτ_sq`: `j_τ² = −1`;
  * `iotaR_jτ`, `iotaC_jτ`: `ι(j_τ)(τ,1)ᵀ = i(τ,1)ᵀ`;
  * `iotaC_mul_jτ`: `ι(x j_τ)(τ,1)ᵀ = i·ι(x)(τ,1)ᵀ`, so multiplication by `i` on `ℂ²` is right multiplication by
    `j_τ` under `B_ℝ ≅ ℂ²`, `x ↦ ι(x)(τ,1)ᵀ`, which carries `𝒪` onto `Λ_τ`;
  * `jτ_imJ_pos`: `imJ(j_τ) = (3+|τ|²)/(6 Im τ) > 0`.
* `lemmaP_qmTorus τ`: the two statements above for `ℂ²/Λ_τ`. `lemmaP_qmTorus_eq`: the unique form is `E₀` for every
  `τ ∈ ℍ`.

This is Lemma P for the QM tori `ℂ²/Λ_τ`, stated with Riemann forms on `H₁(ℂ²/Λ_τ, ℚ) = ℚΛ_τ`. It is everything in
Lemma P over `ℂ` except two facts:
* **Riemann's theorem.** Polarizations of a complex abelian variety are the Riemann forms on `H₁`. It cannot be stated:
  Mathlib has no dual abelian variety.
* **Every complex QM surface is some `ℂ²/Λ_τ`.** This is the QM uniformization: class number one plus the tree's
  `R1(b)(a)` leaf candidate.

Over a base (the relative Lemma P), nothing can be stated (§5.1).

## 5. The leaves, rated

### 5.1 `y3FineModuliAb` (y3abu-print's leaf, unchanged; risk (a))

Lean form: `∃ Y Φ, R1fpPropsAb Y Φ`. The kernel's objects are polarization-free.

* **From a PEL print.** Milne 1979, Boutot–Carayol in PEL form, Deligne Ex. 5.8 and Kottwitz all have general neat
  `K`, which covers `K₃`. Going from such a print to `R1fpPropsAb` needs three things:
  1. Lemma P over every field `K ⊇ ℚ`, for `Φ` to be a bijection onto polarization-free classes.
  2. The level comparison: every `𝒪`-linear level structure respects the pairings up to a scalar. This is
     `eq_smul_E0` over `𝔸_f` and mod 3, as algebra.
  3. **The relative Lemma P over every proper smooth curve `S/ℚ`.** `R1univAbProps` needs a classifying map for
     polarization-free families. The argument: Lemma P at the generic point, extension of homomorphisms of abelian
     schemes over a normal base (Faltings–Chai I.2.7, UNVERIFIED), and local constancy of the polarization type.

  Step 3 cannot be stated in Lean: there is no dual abelian scheme or polarization over a base. The consumer
  restriction of sir-printed does not apply. The field itself asserts `∃ Y Φ, R1fpPropsAb Y Φ` with the full
  `R1univAbProps`, and `R1fpPropsAb` appears in about twenty fields of the chain, so a weaker leaf would need the
  chain regenerated from TailZ16 on. Under the strict rule this reading is therefore **GLUE**, with one step that
  cannot be stated.
* **From a polarization-free print.** Boutot–Carayol ch. III §1 and Buzzard 1997 §1 (bp-qmmoduli §2.2: "Buzzard
  route: one paper, no polarization anywhere"). Then the leaf is a direct instance:
  * the level is `H = K₃`;
  * base change `ℤ[1/…] → ℚ`;
  * the universal property is read on proper smooth curves and on field points;
  * the level structure `η : 𝒪 → A(S)` with `eta_three` and `eta_ker` is the `𝒪`-linear isomorphism
    `(𝒪/3𝒪)_S ≅ A[3]` over `ℚ`-schemes (the `QMAbScheme` docstring).

  The open question is a locator one: whether the print covers full level 3 at `3 | disc B`. bp-qmmoduli §6 item 2
  says N5 reaches level 3 through `V₁(5)` and an `Isom` sheaf, which would suggest Buzzard's Thm 2.1 is for level
  prime to `D`. If so, Boutot–Carayol is the candidate.
* **Rating.** Printed form iff a polarization-free print at level `K₃` is confirmed. The autofold flag says only
  that: "locator UNVERIFIED: the polarization-free form at level K3 … is to be confirmed in Boutot-Carayol ch. III
  §1 or Buzzard 1997 §1".

### 5.2 `deligneModuliY3Every` (new)

* *Print*: the complex points of the moduli scheme are `G(ℚ)\X × G(𝔸_f)/K` via the moduli map. Sources: Milne ISV
  §8 (Thm 8.17 recalled), Deligne §4, Shimura 1967 §§2-3, Boutot–Carayol ch. III §1 (polarization-free). All
  UNVERIFIED.
* *Consequence form*: `ℍ`, `B^×_+` in place of `ℍ^±`, `B^×`; the moduli clause at `𝒪̂^×`, which together with
  `DCRel` and class number one determines `Ψ`; "bijective modulo `DCRel`, holomorphic in `τ`" in place of
  biholomorphic; read through `Φ`. The every-witness form is the one-witness form, proved in Lean.
* *From the PEL print*, one step: **Lemma P over `ℂ`**, existence for "onto" and uniqueness for "fibres". Holomorphy
  needs no step: the forgetful map `M^pol → Y` exists by `Y`'s own universal property (`R1univAbProps` on the proper
  smooth curve `M^pol`), and `Ψ = f ∘ Ψ_print` is holomorphic (`Y3ABUPrint.isHolFamily_comp`). Lemma P over `ℂ`
  is proved here in Riemann-form language (§4); Riemann's theorem and the QM uniformization are missing.
* *Rating*: printed form iff read from the polarization-free print (flag: locator); GLUE from the PEL print.
* *One object*: `Y₃(ℂ)` with its uniformization. No Galois action.

### 5.3 `deligneReciprocityY3Every` (new)

* *Print*: the PEL moduli scheme over the reflex field, with its moduli identification, is the canonical model:
  `σ[x, g] = [x, r(T,x)(s) g]` at special points. Sources: Deligne Cor. 5.7 / Ex. 5.8 (read by the locator audit,
  `locators.md` R1, for `E(G,h)`); Milne §14; Shimura 1967 Main Theorem I.
* *Consequence form*: specialized to the CM points of imaginary quadratic `K` through `q : K → B`
  (`r(T,x)(s) = q̂(s)^{±1}`; `ε`, `δ` existential), and read through `Φ`:

  ```
  Φ(σ Ψ(z,g)) = σ Φ(Ψ(z,g))       -- naturality of Φ, a clause of R1fpPropsAb
              = forget(σ P^pol_{z,g})
              = forget(P^pol_{z,q̂g})
              = Φ(Ψ(z,q̂g))
  ```

  Then injectivity of `Φ` finishes. **Only the forgetful direction is used, so Lemma P is not needed.** The pinning
  (§3.2) identifies the `∀ Ψ` with the print's moduli map, under the uniformization reading the kernel uses
  throughout. The every-witness form is the one-witness form, proved in Lean.
* *Rating*: **printed form** (a direct specialization) in both readings. The flag records only the locator status:
  Cor. 5.7 / Ex. 5.8 were read by the audit, but the specialization to `B`, `K₃` was not checked against the print.
* *One object*: the Galois action on the CM points of `Y₃`. No existence claim.

## 6. Checks (VERIFIED)

* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.ShimuraY3Strict`
  succeeds (14103 jobs). `frozenTarget` uses the standard axioms.
* `#discharges` (`scratch/y3abu-strict/discharges.txt`):

  ```
  DISCHARGES [OpenResearchLeaves28.shimuraMainThmIDeligneY3AbU] by Y3ABUStrict.shimuraMainThmIDeligneY3AbU_of_strict
    still assumes: [Y3ABUPrint.Y3FineModuliAb, Y3ABUStrict.DeligneModuliY3Every, Y3ABUStrict.DeligneReciprocityY3Every]
    axioms: [propext, Classical.choice, Quot.sound]
  #discharges: 45 open hypotheses, 6699 theorems checked, 15 discharge one
  ```

* The new theorems use `[propext, Classical.choice, Quot.sound]` (`discharges.txt`, `axioms-lemmap.txt`).
* `scratch/y3abu-strict/autofold.json` discharges `shimuraMainThmIDeligneY3AbU` by
  `_root_.Y3ABUStrict.shimuraMainThmIDeligneY3AbU_of_strict {n}.y3FineModuliAb {n}.deligneModuliY3Every
  {n}.deligneReciprocityY3Every`. All three leaves are kind `published`, with flags "locator UNVERIFIED: …" that
  state only the locator question.
  * `--dry-run` (`autofold-dryrun.txt`): strict 16/21 on 37 → 19/20 on 39, strictest the same (**−1 GLUE**).
  * `FoldCheck.lean` (the dry run minus line 1) compiles: `sixContactMin_of_open39` uses the standard axioms
    (`foldcheck.txt`).
* `autofold-combined.json` combines this fold with grx6ab-print and elkies-print. In their two specs the argument
  `(Y3ABUPrint.shimuraMainThmIDeligneY3AbU_of_print …)` is replaced by
  `(Y3ABUStrict.shimuraMainThmIDeligneY3AbU_of_strict {n}.y3FineModuliAb {n}.deligneModuliY3Every
  {n}.deligneReciprocityY3Every)`.
  * `--dry-run`: 16/21 on 37 → 22/18 on 40 (**−3 GLUE**).
  * `FoldCheckCombined.lean` compiles with standard axioms (`foldcheck-combined.txt`).
* **For the integrator.** Use this spec in place of y3abu-print's. If a reader finds only PEL prints for
  `y3FineModuliAb` and `deligneModuliY3Every`, change their flags to "pending reading: …". The fold then raises the
  strict count (+1), so keep the field. `deligneReciprocityY3Every` stays LEAF either way.
* New `locators.md` rows are needed for:
  * the polarization-free moduli at `K₃` (Boutot–Carayol ch. III §1; Buzzard §1);
  * the moduli interpretation of `M_{K₃}(ℂ)`;
  * the canonical-model property: the existing R1 row, specialized.

## 7. Status

* Compiled (VERIFIED):
  * the split, the discharge and the every-witness reductions;
  * Lemma P for the QM tori `ℂ²/Λ_τ` in Riemann-form language;
  * `#discharges`;
  * both fold checks.
* Not possible today (reported, not attempted further):
  * the polarized restatement of `Y3FineModuliAb`;
  * the relative Lemma P;
  * Riemann's theorem.

  The tree has no polarization over a base and no dual abelian variety.
* Not done:
  * the locator readings, which need a network;
  * the mod-3 / `𝔸_f` level-compatibility lemma (`eq_smul_E0` over a `ℚ`-algebra), which would close the
    "polarization-compatible level structure" qualification of row R1 at the algebra level.
