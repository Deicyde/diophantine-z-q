# triage2 agent Y: `deligneComponentsY3PrintedAb` (narrowing), plus `shimuraMainThmIDeligneY3AbU`, `shimuraIntegralModelRep`

Base 9a100aa7 (wip/triage2). Read-only; no Lean run. V = VERIFIED (read at file:line), S = SPECULATIVE.

The live chain (V): `sixContactMin_of_open28` (TailZ34:171) → open27 (TailZ33:121) → … → open18 (TailZ24:835) →
`sixContactMin_of_open17` (TailZ23:811), which jumps to `sixContactMin_of_open11` (TailZ13:73) with
`researchLeaves9_of_open14` / `addedLeaves9_of_open14` (TailZ23). So TailZ22's `sixContactMin_of_open16` and TailZ17's
`addedLeaves9_of_open10` are off the path.

## 1. `deligneComponentsY3PrintedAb`

**Statement (V).** `ShimuraGlue.DeligneComponentsY3PrintedAb` (TailZ17:54) is
`∃ Y Φ, R1fpPropsAb Y Φ ∧ DelignePi0 Y K3`. `DelignePi0` (TailZ12:1297) asks for a bijection
`π₀(Y ×_ℚ ℚ̄) ≃ ℚ^×_{>0}\𝔸_f^×/nrd K₃` under which `σ` acts by the cyclotomic idele raised to a fixed sign.

**Consumers (V, one path).**
1. TailZ23:756-758 `addedLeaves9_of_open14`: `deligneComponentsY3Printed := (deligneComponentsY3Printed_iff_ab
   (mumfordRigidity_of14 r)).mpr l.deligneComponentsY3PrintedAb`.
2. TailZ13:55-56 `addedLeaves8_of_open9`: `y3Connected := ShimuraSplit.y3Connected_of_deligne
   (deligneComponentsY3_of_printed …)`. Here `deligneComponentsY3_of_printed` (TailZ12:1346) composes with
   `pi0K3Equiv` (TailZ12:~995), and `y3Connected_of_deligne` (TailZ12:1207) is the orbit computation.
   This is the only place the field is opened. Afterwards only `y3Connected` travels.
3. `y3Connected` is passed through unchanged: TailZ4:243, TailX:257, TailO:2894/2938, TailN:240, TailO:2596/2626. Its
   only real use is TailK:317, `propTSAll_of_pieces3 … l.y3Connected …` (TailK:78 sig, binder `hconn`).
   (grep of `\.y3Connected` over all of `ZInQKernel`: no other non-pass-through use; no non-H file mentions
   `Y3Connected`, `HeckeIrreducible` or `DeligneComponentsY3`.)
4. From there: `coverModelOfHecke_of_heckeRest` (TailG:11879) → `coverModelOfHecke_of_tsHecke'` (TailG:9318) →
   `coverModelOfHecke_of_tsHecke` (TailG:9297) → `heckeNormalization_of` (TailG:8753) →
   `heckeIrreducible_of_connected` (TailG:8380). That last step gives `HeckeIrreducible` (TailG:3919): every triple
   with R1fp, R1hecke, R2fp has `IrreducibleSpace Y.left`. It then feeds `heckeNormalization_of_irr`
   (TailG:3933), i.e. `NormalizationModel Y π E` with `π⁻¹(𝔸¹) ≅ Spec B`, which needs `Y` integral.

**Weakest statement used (V).** The consumers need only
`TSHecke.Y3Connected := ∃ Y Φ, R1fpProps Y Φ ∧ ConnectedSpace Y.left` (TailG:8352), i.e. one fine witness is
connected over ℚ. They do not need the π₀ count, the Galois action, the field ℚ(ζ₃), or `DelignePi0`. With the
bundle leaf `R1R2fp`, it is equivalent to `HeckeIrreducible` (`connected_of_heckeIrreducible`, TailG:8388).
The same finding is in scratch/gap-triage/agent-A.md:228 and docs/research/gap-triage.md:515 ("b (Y3 connected)").

**Bypass candidates.**
* **(X6) No (S, solid).** `DeligneComponentsX6PrintedAb` (TailZ22:33) gives that `X₆ ×_ℚ ℚ̄` is connected. That
  says nothing about whether Galois swaps the two geometric components of `Y₃` over `X₆`: both components map onto
  `X₆_ℚ̄`. No covering or degree argument on `Y₃ → X₆` (`fY` in `X6Props`) can see the swap. The Hecke automorphisms
  (R1hecke) act over ℚ, so they cannot replace Galois either.
* **(U) Yes, plausible (S; plan below).** The live field `shimuraMainThmIDeligneY3AbU` (OpenResearchLeaves21,
  TailZ34:80) implies `Y3Connected`. The proof needs nothing beyond proved results and finite computations:
  - clause 1 of `DeligneBodyAt` (RayClassShimura.lean:1112): Ψ onto, with fibres given by `DCRel`;
  - the *openness half* of clause 2 (`IsHolFamily`, RayClassShimura.lean:85: `IsOpen {τ | ptC (Ψ τ g) ∈ U}` for
    every Zariski open U);
  - clause 4 (reciprocity at CM points);
  - the proved `classNumberOneB_proof` (RayClassShimura.lean:2851).

  Argument. Suppose `Y.left = U ⊔ V` with U, V clopen and nonempty. Put `F(τ,g) := [ptC(Ψ τ g) ∈ U]`.
  1. F does not depend on τ. Both U and Uᶜ are Zariski open, so `{τ | ∈ U}` is clopen in ℍ, and ℍ is connected
     (Mathlib `ContractibleSpace ℍ`, Analysis/Complex/UpperHalfPlane/Topology.lean:68-70).
  2. F is invariant under `g ↦ γ g k` with nrd γ > 0 and k ∈ K₃ (DCRel, clause 1).
  3. F is invariant under `g ↦ q̂(s)^ε g` at a CM point. `galPt σ y = fieldMap σ ≫ y` (RayClassShimura.lean:400)
     has the same underlying point, so U is preserved trivially, and the reciprocity law plays no role here.
  4. By ClassNumberOneB, `g = γu` with u ∈ 𝒪̂^×. If nrd γ < 0, absorb the unit `1+i` (nrd = −1).
  5. So F factors through `G = (𝒪/3𝒪)^×` (order 72, S). It is invariant under left multiplication by the image of
     𝒪^1 (index-2 subgroup, nrd ≡ 1) and by `q(s₃)` for K = ℚ(i) = `K4`, q(i) = i+j, s supported at 3 with
     residue a non-square of F₉ (nrd ≡ −1 mod 3).
  6. If these generate G (a `decide` over (ZMod 3)^4), F is constant. That contradicts U, V ≠ ∅.

  Notes on step 5.
  - K = ℚ(√−3) or ℚ(√−6) cannot do the swap: 3 ramifies there and local unit norms are ≡ 1 mod 3. ℚ(i) is needed
    (3 is inert).
  - **Choose s first, then σ.** This avoids any norm-compatibility of Artin maps. It needs the converse of
    `exists_artinCondC_of_abs` (RayClassShimura.lean:741): given s, take τ ∈ Gal(Kˢ/K) with ab(τ) = art(s), then
    extend it to σ ∈ Aut ℂ (`T5Glue.exists_ringEquiv_extend`, RingClassLattice.lean:454, used at
    RayClassShimura.lean:1400). Then reuse `globalArtinMap_eq_of_mk_eq_absoluteArtinMap` as in lines 741-762.
  - K4 data already exists: `y4`, `finrank_K4`, `IsTotallyComplex K4`, `ringOfIntegersGen_K4`
    (RayClassShimura.lean:1724-1846).
  - Pick κ to match the existential δ (the CM condition is `∀ κ`).
  - R1fpPropsAb → R1fpProps by `r1fpProps_eq_ab'` (TailZ16:431) with the field `mumfordRigidityCore`
    (TailZ34:101 passes it).

  Fold. `OpenAddedLeaves9` (TailZ13:39) wants the full display, so the fold must be a **bypass** to the
  `OpenAddedLeaves8.y3Connected` generation (TailZ4:128): build `sixContactMin_of_open10`'s bundle directly
  (cf. the memory recipe "fold with a weaker leaf: bypass").

  Risk. The leaf is itself a GLUE composite pending the same reading (§2). If a later task weakens it, the bypass
  moves with it.
* **(C) Consumer restructuring (S).** `FunctionFieldModel`'s own docstring (TailG:126-133) says the cover model is
  true with `E = ℚ(Y⁽¹⁾)` for a ℚ-irreducible component. The proof goes component-wise:
  - the stabilizer of Y⁽¹⁾ in Γ' is transitive on fibres in Y⁽¹⁾;
  - an element g with g(Y⁽¹⁾) = Y⁽²⁾ transfers residue fields;
  - fibre sizes halve together with the degree.

  This removes the need for any Deligne or Shimura input at this consumer. But `HeckeNormalization`, `HeckeDegree`,
  `HeckeBranch` and `HeckeVertWitness` are all stated with `NormalizationModel Y π E` on the whole Y (TailG:3906,
  3940, 10216), so the whole Part C plus the hecke-rest pipeline would have to be redone on a clopen sub-curve.
  Larger than (U).

**Tier.** (U) T3 (3-5 days): about 6 lemmas plus one `decide` plus a bypass fold. The main risks are the
qHatU-at-one-place computation (Tau Ceti base change) and the converse Artin step. (C) T3-T4.
**Verdict.** Narrowing found: only ℚ-connectedness is used. The X6 route fails. The U-leaf route is a real bypass
that would remove the field outright.

## 2. `shimuraMainThmIDeligneY3AbU` (leaf-fold22, kind composite, GLUE)

**Statement (V).** RayClassShimura.lean:1152. It is `∃ Y Φ, R1fpPropsAb Y Φ ∧ ∃ Ψ, DeligneBodyAt Y Φ Ψ ∧
ModuliAtUnits Y Φ Ψ`.
- `DeligneBodyAt` (l.1112) has five parts:
  1. Ψ : ℍ × (B⊗𝔸_f)^× → Y(ℂ) is onto, with fibres `DCRel`;
  2. holomorphy in τ;
  3. the moduli clause at g = 1 (`IsShimuraHolFamily`);
  4. reciprocity `galPt σ (Ψ z g) = Ψ z (q̂(s)^ε g)` at CM points;
  5. signs ε, δ (existential).
- `ModuliAtUnits` (l.1135) is the moduli clause at every u ∈ 𝒪̂^×.

**Consumers (V).**
* TailZ34:84 `shimuraFamilyAb := shimuraFamilyAb_of_U` (RayClassShimura.lean:~1163 `mainThmI_of_U`, then
  `shimuraFamilyAb_of_mainThmI` l.498).
  - Uses only (R) and clauses 2-3 via `isShimuraHolFamily_of_body`.
  - Downstream: TailZ23:775-777 (`shimuraFamily_iff_ab`) → passes TailZ15:97, TailZ9:91, TailZ4:183 →
    TailX:192 `r1b := r1b_of' r.shimuraFamily` (TailU:2273) → TailK:311 `(r.r1b r.r1r2)` in
    `fibreQMPeriod_main_rep`.
  - Weakest: `R1bFamily` for the own triple of `r1r2`, i.e. a family τ ↦ y_τ with object ℂ²/ι(𝒪)(τ,1)ᵀ and
    π∘y holomorphic (TailU:1952 `ShimuraFamily`).
* TailZ34:106 `rayClassCMAb := rayClassCMAb_of_leaves hL t.uniformizationLeafAll t.gagaMorphism`
  (RayClassShimura.lean:3004ff).
  - Uses (R) and clauses 1, 4 and U, plus the proved `ClassNumberOneB`.
  - Downstream: TailZ23:721 (`rayClassCM_iff_ab`) → `X6Leaves.rayClass` (TailZ21:1449) →
    `r1r2_of_published` / `x6ConicModel_of_published` (TailZ21:1429/1437) → only through
    `reciprocityCanonical_of_rayClass` (TailZ21:913) → `R1recProps` (HDecomp/QM/Leaves.lean:179) →
    `r1rec_of_reciprocityCanonical` (TailZ20:1740) → `r1r2fpRep_of_printed` (TailZ20:1856).
  - Weakest: on one fine witness, the residue fields of the ℚ̄-points with CM by discriminant −4, −3 or −24 are
    `UnramifiedAbove5`.
* (S) If §1(U) is done, this field also gives `Y3Connected` through clauses 1, 2-openness and 4.

**Reading that makes it a LEAF with no new Lean.** gt-rayclass §3 (docs/research/gt-rayclass.md:76-128) holds it
GLUE only because it combines three results: (R), the complex moduli interpretation (1-3, U), and reciprocity (4).
- (R) on `R1fpPropsAb` is accepted inside LEAF fields: `deligneComponentsX6PrintedAb` is LEAF on the same clause
  list (TailZ22:33; open_inscope.md:47).
- So it needs one human reading confirming that a single printed theorem states 1-4 and U together. Candidates:
  Deligne, Sém. Bourbaki 389 §4 ("the PEL moduli scheme is the canonical model", with §3's definition of canonical
  model, which contains reciprocity at special points and the description `[τ,g] ↦ (ℂ²/ι(L_g)(τ,1)ᵀ, ι, η_g)`), or
  Milne 2005 §14 with Def. of canonical model in §12/13. All locators are UNVERIFIED.
- This is **the same reading** as the flag on `deligneComponentsY3PrintedAb` ("PEL moduli scheme with its
  uniformization is the canonical model at level K₃": open_inscope.md:3). One reading would clear both.
- Re-rating it as published gives 46/11 (gt-rayclass.md:35-37).

## 3. `shimuraIntegralModelRep` (leaf-fold22, kind consequence, GLUE)

**Statement (V).** Contrib/OneProof/ShimuraGoodReductionNoGuard.lean:94 (`…RepAt` l.56). For every prime p > 324
there is a proper smooth curve 𝒴/ℤ_(p) with a universal `QMAbScheme`: every QM abelian scheme over a locally
noetherian ℤ_(p)-scheme S is the pullback along exactly one S → 𝒴 (`QMFamFibre`, l.46).

**Consumers (V).**
1. TailZ34:161: `shimuraGoodReductionNoGuard := shimuraGoodReductionNoGuard_of_printed n.shimuraIntegralModelRep`.
2. This passes down to TailX:266-267: `shimuraGoodReduction := shimuraGoodReduction_of_noGuard (R1R2fp_of_rep
   r.r1r2) l.shimuraGoodReductionNoGuard` (TailW:744).
3. Then TailN:255 / TailO:2910: `heckeVertWitness := heckeVertWitness_of_leaves5 l.shimuraGoodReduction r.r1r2 …
   g.modelCoordinateResidue l.curveBijIso` (TailN:38).
4. Then `heckeVertWitness_of_curveBijIso` (TailL:2425), then `heckeVertWitness_of_leaves` (TailL:872), then
   `heckeVertWitness_of_maxIdeal` (TailL:864). These use every clause of `IsShimuraModelNoGuard` (TailW:713):
   - proper and smooth;
   - fibres;
   - bijectivity on ℚ̄-points, via `ModelComparison` / `CurveBijIso`;
   - the Hecke automorphisms, for the tame quotient coordinate in `ModelCoordinate` (TailL:789).
5. Then `HeckeVertWitness` (TailG:10216) enters TailK:318 `propTSAll_of_pieces3 … g.heckeVertWitness`, then
   `heckeNoVertRam_of_witness` (TailG:10225), which gives `NoVerticalRam E p` inside `CoverModel`. That is then
   used with `BeckmannSIT` at p > 324.

**Weakest use (V).** For each p > 324 and the Galois cover field E of `Y₃ → P¹_j` (any E with
`NormalizationModel Y π E`): `VertUnramWitness E p`, i.e. one prime of the integral closure of ℤ[X] in E over p is
unramified (TailG:10216-10222). The moduli scheme, the family and the universal property serve only to produce
this witness.

**Reading that makes it a LEAF with no new Lean.** It is flagged at open_inscope.md:19 and in the docstring at
ShimuraGoodReductionNoGuard.lean:90-93. Two ways:
- Read Buzzard 1997 (Duke 87) §§1-4 and confirm that its polarization-free problem (A, ι, level) is representable
  by a smooth proper curve over ℤ_(p) for p ∤ 6·3 with full level 3 at 3 | D. The stated form is weaker: p > 324
  only, locally noetherian S only.
- Or read Kottwitz 1992 §5 (K_p = 𝒪_p^× hyperspecial for p ∤ 6; level at 3 allowed) together with the relative
  Lemma P (Boutot–Carayol III §1) and the comparison of rational to integral level.

Locators UNVERIFIED. sgr-split.md:46-49 says the strict GLUE count drops by 1 when cleared.

**Narrower alternative (S, new statement).** Replace the whole model route by a printed theorem on covers alone:
Grothendieck/Beckmann good reduction of tame G-covers. Beckmann 1989, J. Algebra 125, "Ramified primes in the field
of moduli…"; SGA 1 XIII 2.12; locators UNVERIFIED. Under the hypotheses `BeckmannSIT` already carries (BranchData,
[E:ℚ(X)] < p, branch points p-integral and distinct mod p), it would give `NoVerticalRam E p` directly.
- It would remove `shimuraIntegralModelRep` and the TailL model glue.
- It needs care with the constant-field extension ℚ(ζ₃) ⊂ E, which BeckmannSIT's docstring already handles
  (TailG:103-108).
- It needs one bypass fold to the generation holding `heckeVertWitness` (OpenGlue4) or `HeckeNoVertRam`.
- Tier T2-T3. It is still a printed leaf swap, so it gains only if the new leaf reads cleanly.
