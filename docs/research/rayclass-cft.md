# rayclass-cft: `RayClassCM` (Shimura reciprocity in ray-class form) from published-form leaves

Task rayclass-cft, 2026-11-14. Base b5ff0474 (w63), with origin/wip/x6-glue and origin/wip/shimura-cft merged.
Lean: `scratch/rayclass-cft/` (results log `log.md`). No file under `ZInQKernel/`, `blueprint/`, or another
task's notes or scratch was edited. Model work; no human review.

Marks: **VERIFIED** = compiled, computed, or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number or locator recalled without a source (this host
has no network).

## 1. Verdict and main result

**`ShimuraGlue.Ray.RayClassCM` (x6-glue §5.1) is now a Lean theorem from four leaves, with no glue left.**
* Two of the leaves are already in the bundle.
* The other two are consequences of printed theorems:
  * shimura-cft's Deligne leaf with its moduli clause also at `𝒪̂^×`;
  * Eichler's class number one.

VERIFIED: `scratch/rayclass-cft/RayClassCFT.lean` compiles with 0 errors in 1 min 17 s (14.8 GB). All 22
`#print axioms` lines are `[propext, Classical.choice, Quot.sound]`; see `RayClassCFT_result.txt`.

```lean
theorem RayClassCFT.rayClassCM_of_leaves (hL : ShimuraMainThmIDeligneY3AbU)
    (hMR : LeafQM.AV.R1UnivRigid.MumfordRigidityCore) (hCN : ClassNumberOneB)
    (hHL : ZInQ.HomUnify.HomLinearLift) : ShimuraGlue.Ray.RayClassCM
```

The statement `RayClassCM` is x6-glue's, copied verbatim (`RayDefs.lean` = `X6Glue.lean` lines 6587-6745).
So x6-glue's rows `r1r2` and `x6ConicModel` now rest on published-form leaves only, apart from x6-glue's own §5.2
caveat (the fibre clause of `ElkiesEquationsX6`).

**The ray-class form needs more than shimura-cft's Deligne form gives.** As stated,
`ShimuraMainThmIDeligneY3Ab` describes the moduli object at `Ψ(τ, 1)` only. The points `Ψ(τ, 1)` fill only one of
the two geometric components of `Y₃`: `π₀ = ℚ^×_{>0}\𝔸_f^×/nrd K₃ = (ℤ/3)^×`. So for a CM point on the other
component, the leaf says nothing about its object. Its `τ` then cannot be shown to be a CM point, and the
reciprocity clause cannot be applied (§3).

Two printed statements fill the gap:
1. **`ModuliAtUnits`**: the moduli clause at every `u ∈ 𝒪̂^×`, not only at `u = 1`. Only the QM pair is
   described there, not the level structure. It is folded into the Deligne leaf as `ShimuraMainThmIDeligneY3AbU`.
2. **`ClassNumberOneB`**: Eichler's class number one, `(B ⊗ 𝔸_f)^× = B^× · 𝒪̂^×`.

The glue the reduction needed is all proved:
* `QHatIntegral`, for every number field;
* `RingOfIntegersGen`, for the three fields;
* `CMAnalytic`, from the bundle's textbook leaf `HomLinearLift`;
* `CMBaseChange`, from the kernel's proved rigidity;
* the Galois descent of residue fields;
* the kernel of Tau Ceti's Artin map on the ray class field;
* the extension of `Aut(ℚ̄)` to `Aut(ℂ)`.

## 2. The Props

| Prop | kind | statement (short) | source / status |
|---|---|---|---|
| `ShimuraMainThmIDeligneY3AbU` | **LEAF** (consequence of the print) | shimura-cft's `ShimuraMainThmIDeligneY3Ab`, with its moduli clause also at every `u ∈ 𝒪̂^×` (`ModuliAtUnits`) | Shimura, Ann. of Math. 85 (1967), Main Thm I and §§2-3; Deligne, Sém. Bourbaki 389 (1971), §§3-4; Milne, *Introduction to Shimura varieties*, §§12-14 (UNVERIFIED locators). `mainThmI_of_U` drops the new clause. |
| `MumfordRigidityCore` | LEAF (existing; r1univ-rigid, route-a-fold field) | Mumford's rigidity, for `R1fpPropsAb ↔ R1fpProps` | already in the bundle |
| `ClassNumberOneB` | **LEAF** (printed, adelic form) | `∀ g ∈ (B⊗𝔸_f)^×, ∃ γ ∈ B, nrd γ ≠ 0, ∃ u ∈ 𝒪̂^×, g = γu` | Eichler, J. reine angew. Math. 195 (1955); Vignéras LNM 800, Cor. III.5.7; Voight GTM 288, Cor. 28.5.17 with §27.6 (UNVERIFIED numbers) |
| `ZInQ.HomUnify.HomLinearLift` | LEAF (existing; hom-unify, first clause of `HomLatticeCorr`) | every homomorphism of abelian varieties lifts to a `ℂ`-linear map of the uniformizations | Birkenhake–Lange Prop. 1.2.1 (UNVERIFIED) |
| `CMBaseChange` | GLUE, **proved** (`cmBaseChange`) | the CM relations `φ² = −1`, `φ² − φ + 1 = 0`, `φ² = −6` of `P/ℚ̄` pass to an object `Q/ℂ` with `IsBaseChangeOf ιe P Q` | `RayGlueB.lean` |
| `QHatIntegral k` | GLUE, **proved** for every number field (`qHatIntegral`) | `q(𝒪_k) ⊆ 𝒪` ⇒ `q̂` maps the congruence ideles of `3𝒪_k` into `K₃` | `RayGlueI.lean` |
| `RingOfIntegersGen k y` | GLUE, **proved** for `ℚ(i)`, `ℚ(ζ₃)`, `ℚ(√−6)` | `𝒪_k = ℤ[y]` | `RayGlueO.lean` |
| `CMAnalytic` | GLUE, **proved** from `HomLinearLift` (`cmAnalytic_of`) | for `Q/ℂ` uniformized `ι`-compatibly by `Λ_τ`, a ring map `End_𝒪(Q) → 𝒪`, `f ↦ β_f`, with `ι(β_f)(τ,1)ᵀ ∈ ℂ(τ,1)ᵀ` | `RayGlueA.lean` |

**Why the two new leaves are consequences of printed statements, and not stronger (SPECULATIVE, standard
reasons):**
* **`ModuliAtUnits`.** In Deligne's moduli description of `Sh_K(B^×, ℍ^±)`, the point `[τ, g]` is the class of
  `(ℂ²/ι(L_g)(τ,1)ᵀ, ι, η_g)`, with `L_g = B ∩ 𝒪̂g⁻¹`.
  * This convention matches the leaf's clause 1. `L_{γgk} = L_gγ⁻¹`, and `ι(ℓγ⁻¹)(γτ,1)ᵀ` is a scalar multiple
    of `ι(ℓ)(τ,1)ᵀ`, so the torus at `(γτ, γgk)` is isomorphic to the one at `(τ, g)`.
  * It matches clause 3 at `g = 1`.
  * For `u ∈ 𝒪̂^×`, `L_u = 𝒪`, and only the level structure changes.
  * The new clause keeps only the QM pair, through the same `IsUniformization`/`IotaCompatible` predicates as
    clause 3, so it is weaker than the printed statement.
* **`ClassNumberOneB`.** Eichler's theorem gives one class of locally principal left ideals of `𝒪`. Through
  the adelic description `Cls 𝒪 = B^×\(B⊗𝔸_f)^×/𝒪̂^×`, this is exactly the Lean statement. The positive-norm form
  used in the proof (`exists_pos_decomp`) is derived with the unit `1 + i ∈ 𝒪^×`, which has `nrd = −1`.

**Not vacuous.** Both new leaves reuse shimura-cft's objects: `BAQ`, `OhatQ`, `bEmb`, `nrdQ`, the kernel's
predicates.
* The class-number leaf holds trivially for `g ∈ 𝒪̂^×`.
* `ModuliAtUnits` at `u = 1` is clause 3.

## 3. Why the Deligne form alone does not suffice (the missing piece)

`RayClassCM` concerns an arbitrary `ℚ̄`-point `y` whose object `P` has CM by `𝒪_k`. By clause 1,
`y_ℂ = Ψ(z, g)` for some `(z, g)`.
* To use clause 4 at `y`, one needs an embedding `q : k → B` with `IsCMPoint q κ z`, together with
  `q(𝒪_k) ⊆ g𝒪̂g⁻¹`. That is "the dictionary" of x6-glue §5.1 item 2.
* The dictionary comes from comparing `P_ℂ` with the torus at `Ψ(z, g)`. The leaf describes that torus only for
  `g ∈ B^×_{>0}K₃`, i.e. on the component of `Ψ(ℍ, 1)`.
* The other component is reached from the first only through the Galois action. Clause 4 describes that action
  only at points already known to be CM points. Deriving it on the whole component would need a
  Zariski-continuity argument that relates the scheme components of `Y_ℂ` to `Ψ`, and there is none in the
  kernel.

So we add the moduli clause at `u ∈ 𝒪̂^×` and class number one. With them, every point is `Ψ(τ, u)` with
`u ∈ 𝒪̂^×`:
* `g = γu` with `nrd γ > 0`;
* `Ψ(z, γu) = Ψ(γ⁻¹z, u)` by clause 1 (`dcRel_of_decomp`).

The torus at `Ψ(τ, u)` is `ℂ²/ι(𝒪)(τ,1)ᵀ`. The printed alternative is the moduli clause at every `g` with
`L_g = B ∩ 𝒪̂g⁻¹`. It would replace class number one by a local-global lemma: `L_gβ ⊆ L_g ⇒ g⁻¹βg ∈ 𝒪̂`.

## 4. The proof (all VERIFIED, compiled)

`embed_core` (`RayProof3.lean`) works for one imaginary quadratic `k`. Given a `ℚ̄`-point `y` such that at every
representative `(τ, u)`, `u ∈ 𝒪̂^×`, of `y_ℂ = ιC^* y` there is `q : k → B` with `q(𝒪_k) ⊆ 𝒪` and CM point `τ`,
it proves that `ℚ(y)` embeds into `rayClassField (mod3 k)`.
1. Representative: clause 1, then `ClassNumberOneB` gives `g = γu` with `nrd γ > 0` (`exists_pos_decomp`). Then
   `Ψ(z, g) = Ψ(ι(γ⁻¹)z, u)` (`dcRel_of_decomp`).
2. Reflex embedding: `κ` is `κ₀` or `conj ∘ κ₀`, so that clause 4's hypothesis is the CM relation at `τ`.
   * `j' : L → ℂ` extends `κ`; `L = rayClassField (mod3 k)` (`IsAlgClosed.lift`).
   * `j : L → ℚ̄` with `ιC ∘ j = j'` (`exists_lift_ringHom`).
3. Take `σ ∈ Gal(ℚ̄/j(L))`. Extend it to `σ̃ ∈ Aut(ℂ)` (`exists_ringEquiv_extend`, t5-glue's Steinitz argument).
   * `σ̃` fixes `κ(k)`, so `ArtinCondC κ σ̃ s` holds for some idele `s` (shimura-cft's `exists_artinCondC`, from
     t5-glue's surjectivity of the absolute Artin map).
   * `σ̃` fixes `j'(L)`, so `Art(s)|_L = 1`.
   * Tau Ceti gives `ker(ideleClassArtinMap) = N(C_L) = raySubgroup (mod3 k)` (`ker_ideleClassArtinMap`,
     `range_ideleClassNormMap_rayClassField`). So `s = s₀ · c` with `s₀` a congruence idele and `c ∈ k^×`
     (`mk_mem_raySubgroup_iff`, `Subgroup.mem_sup`).
4. Clause 4: `σ̃ Ψ(τ, u) = Ψ(τ, q̂(s)^ε u)`. Here `q̂(s)^ε u = q(c^ε) · u · (u⁻¹ q̂(s₀^ε) u)`, and:
   * `q̂(s₀^ε) ∈ K₃` (`QHatIntegral`);
   * `K₃` is normalized by `𝒪̂^×` (`conj_mem_K3Q`);
   * `q(c^ε)` fixes `τ`, with `nrd q(c^ε) > 0` (`dcRel_fix`, `nrd_pos_of_cm`).
   So the point is unchanged: `σ̃ y_ℂ = y_ℂ`.
5. Descent: `σ̃ y_ℂ = (σ y)_ℂ` (`galPt_fieldMap`), and `ιC^*` is injective (`fieldMap_ιC_inj`), so `σ y = y`.
   Then `σ` fixes `ℚ(y)` pointwise (`residue_fixed`). By infinite Galois theory, `ℚ(y) ⊆ j(L) ≅ L`
   (`residueImage_le`, Mathlib's `InfiniteGalois.fixedField_fixingSubgroup`).

The CM hypothesis of `embed_core` comes from the object (`obj_at`, `cm_data`, `rayClassCM_of`):
1. `R1fpProps` naturality gives `Q/ℂ` with `IsBaseChangeOf ιC P Q`, and `CMBaseChange` gives `Q` the CM of `P`.
2. `ModuliAtUnits` at `Ψ(τ, u) = y_ℂ` gives `P'` uniformized by `Λ_τ`, and `Q ≅ P'`.
3. `CMAnalytic` gives `β ∈ 𝒪` with `β² = −1` (resp. `β² − β + 1 = 0`, `β² = −6`) and `ι(β)(τ,1)ᵀ = λ(τ,1)ᵀ`.
4. `q : y_k ↦ β` and `κ₀ : y_k ↦ λ` (height-glue's `liftQuad`, copied). Then `IsCMPoint q κ₀ τ`, and
   `q(𝒪_k) ⊆ 𝒪` by `RingOfIntegersGen`.

**Glue proofs:**
* **`QHatIntegral`** (`qHatIntegral`, every number field `k`).
  * Integral finite adeles of `k` are `∑ aᵢ ⊗ bᵢ` with `aᵢ ∈ ℤ̂` and `bᵢ` an integral basis
    (`exists_integral_preimage`). This re-proves the integral branch of Tau Ceti's private
    `exists_semilocalHom_sum_tmul_eq` from its public `integralSemilocalEquiv` API.
  * So `q̂(𝒪̂_k) ⊆ 𝒪̂` (`qHat_mem_OhatQ`).
  * A congruence idele is `a = 1 + 3b` with `b = (a − 1)/3` integral, since `v(a − 1) ≤ v(3)`
    (`valued_three`, `cong_sub_one_div_three`).
* **`RingOfIntegersGen`.**
  * `ℚ(i)`, `ℚ(ζ₃)`: Mathlib's `IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton`, plus `adjoin_quad`.
  * `ℚ(√−6)`, by hand:
    * the conjugation `√−6 ↦ −√−6` comes from `liftQuad`;
    * the trace, the norm and `(x − x̄)√−6` are integral rationals, hence integers;
    * then `6 ∣ e`, and parity mod 4.
* **`CMAnalytic`** (`cmAnalytic_of`), from `HomLinearLift`.
  * Lifts are unique: a `ℂ`-subspace of the countable lattice `Λ_τ` is 0 (`linear_eq_zero_of_mem`). So
    `f ↦ M_f` is a ring map.
  * For `f ∈ End_𝒪`, `M_f` commutes with `ι(i) = diag(√2, −√2)` and `ι(j)` (`liftM_comm`, from
    `IotaCompatible`), so it is a scalar `λ_f` (`liftM_scalar`).
  * `λ_f(τ,1)ᵀ ∈ Λ_τ` gives a unique `β_f ∈ 𝒪` (`exists_of_mem_qmLattice`, `iota_eig_inj`). The proof that
    `ι(b)(τ,1)ᵀ = 0 ⇒ b = 0` needs no anisotropy.
* **Smaller lemmas:**
  * `det ι(x) = nrd x` (`det_iota`);
  * a real matrix with eigenvector `(x+iy, 1)ᵀ`, `y ≠ 0`, has `det = (a − cx)² + c²y² ≥ 0` (`det_nonneg_of_eig`),
    and fixes `τ` (`smul_eq_of_eig`);
  * `ι : B → M₂(ℂ)` is a `ℚ`-algebra map (`iotaC`);
  * the three fields are totally complex, of degree 2 (`isTotallyComplex_of_root`, `finrank_K4/K3/K24`).

* **`CMBaseChange`** (`cmBaseChange`, `RayGlueB.lean`).
  * `IsPullback g` gives `bcIso : Q.A.X ≅ (P.A.baseChange L).X` over `L`, via `IsPullback.isoPullback`.
  * It preserves the identity (`bcIso_eta`). This uses the `η`-clause of `IsBaseChangeOf` at `a = 0`, where
    `η(0)` is the unit section (`eta_compat`, `one_pt_left`), and the unit of `Over.pullback` read on the
    pullback projections (`eta_bc_fst`).
  * So `bcIso` and its inverse are homomorphisms, by the kernel's proved rigidity
    `G0FibreSimple.rigidityHom` (`bcIso_isMonHom`).
  * Conjugation by `bcIso` (`conjEnd`) after the kernel's `endBC` is a ring map `End P.A → End Q.A`. It carries
    `ι_P(a)` to `ι_Q(a)` (`bc_iota`, from the `ι`-clause and `pullback.hom_ext`), so it carries `End_𝒪(P)` into
    `End_𝒪(Q)` (`com_map`) and preserves the three polynomial identities.

## 4b. Independent statement review (model, read-only, one pass)

No PROBLEM. One RISK, on sourcing only: `L_g = B ∩ 𝒪̂g⁻¹` is a standard derivation from the PEL description of the
moduli, not a line quoted from a source, and all locators are UNVERIFIED.

The reviewer checked:
* **The copies.** `DeligneBodyAt` is the body of `ShimuraDeligneBody` character for character.
  `RayDefs.lean` is `X6Glue.lean` lines 6587-6745, apart from the placement of the `namespace`/`end` lines.
* **`ModuliAtUnits`.**
  * It is clause 3's moduli conjunct with `Ψ τ u` in place of `Ψ τ 1`, and the level structure is left free.
  * Its convention agrees with clause 1, since `L_{γgk}γ = L_g`.
  * `L_u = 𝒪` under every convention.
  * No convention makes it false while clause 3 holds.
  * It is consistent with clause 4.
  * It adds information exactly on the second geometric component.
* **`ClassNumberOneB`.**
  * It is Eichler's theorem in adelic form.
  * `B` is indefinite, ramified at `{2, 3}`.
  * The order `1, i, (1+j)/2, (i+k)/2` is maximal (reduced discriminant 6).
  * `OhatQ` is `𝒪 ⊗ ℤ̂`.
* **No vacuity, and no hidden conclusion.** No new Prop mentions `rayClassField` or `residueImage`.

## 5. Files and checks (VERIFIED: one Lean process at a time)

| file | content | check |
|---|---|---|
| `Base.lean` | `scratch/shimura-cft/ShimuraCFT.lean`, verbatim | 0 errors, 1 min 47 s |
| `RayDefs.lean` | `scratch/x6-glue/X6Glue.lean` lines 6587-6745 verbatim (`mod3`, `K4`, `K3`, `K24`, `RayClassCM`); x6-glue's last theorem of that section is omitted (its target is not in this import closure) | olean chain |
| `RayProof1.lean` | `ι` algebra, `det_iota`, fixed points, `ιC`, Galois descent of residue fields | olean chain |
| `RayProof2.lean` | the Props (§2), units of `B`/`𝒪̂`, `exists_pos_decomp`, `dcRel_of_decomp`, `dcRel_fix`; t5-glue's `exists_ringEquiv_extend` (copy) | olean chain |
| `RayProof3.lean` | `qHatU_unitEmbedding`, `nrd_pos_of_cm`, **`embed_core`** | olean chain |
| `RayProof4.lean` | height-glue's `liftQuad` (copy), `iotaC`, `eig_rel` | olean chain |
| `RayProof5.lean` | `obj_at`, `RingOfIntegersGen`, `cm_data`, the three fields, **`rayClassCM_of`** | olean chain |
| `RayGlueO.lean` | `RingOfIntegersGen` for the three fields, `rayClassCM_of2` | olean chain |
| `RayGlueI.lean` | `QHatIntegral` for every number field, `rayClassCM_of3` | olean chain |
| `RayGlueA.lean` | `CMAnalytic` from `HomLinearLift`, `rayClassCM_of4` | olean chain |
| `RayGlueB.lean` | `CMBaseChange` (base-change isomorphism, rigidity, conjugation), **`rayClassCM_of_leaves`** | olean chain |
| `RayClassCFT.lean` | all of the above in one file (`mk.py RayGlueB.lean`) | **0 errors, 1 min 17 s, 14.8 GB; 22 axiom lines, all standard** (`RayClassCFT_result.txt`) |

How to check:
* The parts: `scratch/rayclass-cft/chk.sh <file> <olean-name>`. It sets `LEAN_PATH` to lake's path plus
  `/tmp/rc-olean`, and each part imports the previous one.
* The single file: `lake env lean scratch/rayclass-cft/RayClassCFT.lean`.

## 6. For integration

* With `rayClassCM_of_leaves`, x6-glue's leaf field `rayClass : RayClassCM` in `X6Leaves`/`ShimuraGlueLeaves4`
  becomes four leaves:
  * `ShimuraMainThmIDeligneY3AbU`, which implies shimura-cft's leaf (`mainThmI_of_U`);
  * `ClassNumberOneB`;
  * `MumfordRigidityCore` (already a bundle leaf);
  * `HomLinearLift` (already a bundle leaf, through `HomLatticeCorr`).
* If route-a-fold's `shimuraFamilyAb` field is also replaced by shimura-cft's leaf, use
  `ShimuraMainThmIDeligneY3AbU` there too. Then one Deligne leaf serves both rows.
* No kernel edit and no new axiom.
  * The copies (shimura-cft, x6-glue, t5-glue `Field.lean`, height-glue `liftQuad`) are verbatim.
  * Two Tau Ceti lemmas are re-proved for a general base field `K`. For `K = ℚ`,
    `Algebra ℚ (v.adicCompletion ℚ)` has two instances that are not definitionally equal.
* Reusable for other rows:
  * `qHatIntegral` (any number field);
  * `cmAnalytic_of`, the analytic representation `End_𝒪(Q) → 𝒪` of a QM surface;
  * `exists_bc_ringHom`, base change `End P.A → End Q.A` for any `IsBaseChangeOf`;
  * `residueImage_le`, Galois descent of residue fields of `ℚ̄`-points.
