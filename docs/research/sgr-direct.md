# sgr-direct: removing `shimuraIntegralModelRep` by proving its consumer directly

Task sgr-direct, 2026-11-15. Base `43513d87` (leaf-fold25, 56 H fields).

- **Lean** (new; namespace `SGRDirect`):
  - `ZInQKernel/Contrib/OneProof/SGRDirectNV.lean`, which imports `OneProof.H.TailG`;
  - `ZInQKernel/Contrib/OneProof/SGRDirectElkies.lean`, which imports the first and `Contrib.OneProof.ElkiesX6Star`.
- **Scratch** (`scratch/sgr-direct/`):
  - `log.md`;
  - `NV.lean`, `Elkies.lean`: the two Contrib files plus `#print axioms`;
  - `Ram.lean`, `Vert.lean`, `Branch.lean`, `Sqrt.lean`, `SqrtElkies.lean`: the proofs as first compiled;
  - `Discharges.lean` with `Discharges-output.txt`;
  - `autofold.json`.
- **Marks:** **VERIFIED** (read, compiled or computed), **STANDARD** (published, reference given), **SPECULATIVE**.
  No network, so every theorem number recalled from memory is **UNVERIFIED**.

## 1. Result

**The field's consumer is proved from bundle fields plus one new GLUE Prop, with no integral model** (VERIFIED:
`lake build`, standard axioms):

```lean
theorem SGRDirect.heckeVertWitness_of_nvElkies (hRR : R1R2fp) (hT : ObjBridge.TorsionStructure)
    (hA : HeckeRest.QMAutCard) (hS : HeckeRest.SerreRigidity3) (hW : HeckeRest.ALFixedPoints)
    (hL : NVLocalInertia) (hEl : ElkiesX6StarPrinted) : HDec.HeckeRestNV.HeckeVertWitness
```

- **`HeckeVertWitness` is the single consumer** of both `shimuraIntegralModelRep` and `quotientP1Coordinate` (§2,
  VERIFIED by reading the chain).
- **Every hypothesis except `NVLocalInertia` is an existing bundle field:** `r1r2` (as `R1R2fp`), `t5`, `qmAutCard`,
  `serreRigidity3`, `alFixedPoints`, and the research field `elkiesX6StarPrinted`.
- **`NVLocalInertia`** is h-b1's Lemma NV step 3. It is pure commutative algebra of tame covers of `P¹_{ℤ_(p)}`,
  with no Shimura-curve content (§4).
- **The goal "remove the field using only existing fields, every step proved" is reached up to this one Prop.**
- **Counts.** A bypass fold (§5) would replace `shimuraIntegralModelRep` and `quotientP1Coordinate` (GLUE, GLUE) by
  `nvLocalInertia` (GLUE): **−1 GLUE**.
  - Removed from the trust base: the integral model of the Shimura curve. That covers the pending reading of
    Kottwitz/Lan, Lemma P and the level comparison.
  - Also removed: the tame-quotient scheme theory of mcr-quot.
- **What the route uses:**
  - h-b1's Lemma NV, simplified here to one branch point (§4);
  - five intermediate Props, all proved in Lean in this task except `NVLocalInertia`;
  - two new pieces of algebra: Nullstellensatz density, and "`√q` in a field unramified at `p` forces `v_p(q)`
    even".
- **Why the abelian-variety route fails** (§3, argued; SPECULATIVE as an impossibility claim). Good reduction of the
  QM surfaces at the points used (NOS, Raynaud) does not by itself give the consumer's statement. It needs
  characteristic-`p` moduli, which no bundle field supplies. Route NV avoids it.

## 2. The consumer map (VERIFIED, read in `ZInQKernel/OneProof/H/`)

| step | where | what flows |
|---|---|---|
| `shimuraIntegralModelRep` | TailZ34 `openAddedLeaves16_of_OpenAddedLeaves17` | the only use: `shimuraGoodReductionNoGuard := SGRSplit.shimuraGoodReductionNoGuard_of_printed _` |
| `shimuraGoodReductionNoGuard` | TailX l.266 | `shimuraGoodReduction := CurveSplitGR.shimuraGoodReduction_of_noGuard (R1R2fp_of_rep r.r1r2) _` |
| `quotientP1Coordinate` | TailX l.272 | `modelCoordinateResidue := MCRGlue.modelCoordinateResidue_of_quotient' _` (its only use) |
| `shimuraGoodReduction`, `modelCoordinateResidue` | TailN l.255 (`glue4_of_open5`) | `heckeVertWitness := heckeVertWitness_of_leaves5 l.shimuraGoodReduction r.r1r2 (torsionStructure_ofK5 t.t5) g.modelCoordinateResidue l.curveBijIso` (their only use) |
| `heckeVertWitness` | TailK l.318 | `propTSAll_of_pieces3 … g.heckeVertWitness` (TailI l.77) → `HeckeRestAll.coverModelOfHecke_of_heckeRest` → `heckeNoVertRam_of_witness` |
| `HeckeNoVertRam` | TailG | → `CoverModelOfHecke` (Beckmann's hypothesis (d)) → `PropTSAll` → `FibreUnramified` → `fibreCoverExists_of_propTSAll'` → `modularConstituent` |

- The needed range is every prime `p > 324`.
- The points used downstream are the `ℚ̄`-points of `Y₃` over `t = J(u)`, for all `u ∈ ℚ ∖ 𝒞`. These are infinitely
  many fibres, including fibres that meet a branch point mod `p`.
- So the consumer needs the full statement of no vertical ramification.

## 3. Why good reduction of the QM surfaces does not suffice

Take `σ` in an inertia group at `p`. Either `σ` acts on `E` at the Gauss prime, or it acts on `ℚ̄` at a prime over
`p`, for a point `y` over `t`.

- The fibre over `t ∈ ℚ` is one Hecke orbit, so `σ` maps `(A, ι, η)` to a translate `(A, ι∘α, η∘u)`.
- `A` has good reduction (STANDARD):
  - potentially good, since the toric rank is `≤ 2` and `B` cannot act on `ℚ^t`;
  - semistable, by Raynaud with level 3;
  - therefore good, and NOS applies.
- The isomorphism `σ*A ≅ A'` reduces to an `𝒪`-linear automorphism of `Ā`.
- Concluding `σ = 1` needs the `𝒪`-commutant of `Ā` to have units `{±1}`. In characteristic `p` that commutant is an
  imaginary quadratic or definite quaternion order. So this is a statement about the special fibre of the moduli
  problem, i.e. the integral model.
- At the Gauss prime the same issue is non-isotriviality of `Ā`.

SPECULATIVE: no bundle field supplies this, and none supplies the integral model except the field itself.

## 4. Route NV in Lean

**Definitions.**
- `InertiaQ E Q` and `InertiaZ E q`: the `σ ∈ Gal(E/ℚ(X))` with `σ b ∈ B` and `σ b ≡ b mod Q` for every `b` in the
  integral closure of `ℚ[X]`, respectively of `ℤ[X]`.
- These are Mathlib's inertia subgroups, written as sets.
- Everything else is the chain's own: `BranchData`, `vertPrime`, `nY3`, `UnramifiedAt`, `NormalizationModel`,
  `VertUnramWitness`, `HeckeVertWitness`.

**The intermediate Props and their status.**

| Prop | content | status |
|---|---|---|
| `NVLocalInertia` | `E/ℚ(X)` finite Galois of degree `< p`, branch data in `S ∪ {∞}` with `S` `p`-integral and distinct mod `p`, `b ∈ S` with all residue fields over `X = b` unramified at `p`. Then every vertical inertia element has a conjugate in an inertia set over `X − b`. | **open, GLUE** |
| `RamifiedSqrtInertia` | over a prime above `X − b` with `e ∣ 2`, an inertia element fixing `√(c(X − b))` is `1` | **proved** (`ramifiedSqrtInertia`) |
| `VertInertiaTrivial` | degree `< p`, trivial inertia at every vertical prime ⇒ `VertUnramWitness E p` | **proved** (`vertInertiaTrivial`) |
| `HeckeBranchFibreUnram` | residue fields of the Hecke cover over `−16/27` are unramified at `p > 324` | **proved** from `R1R2fp`, T5 (`heckeBranchFibreUnram`) |
| `HeckeSqrtBranchAny` | `E ∋ √(c(27X + 16))` for some `c ∈ ℚ^×` | **proved** from `elkiesX6StarPrinted`, `R1R2fp`, T5 (`heckeSqrtBranchAny_of_elkies`) |
| `HeckeSqrtBranch` | the same with `c = a ∈ ℤ` prime to every `p > 324` | superseded: it implies `HeckeSqrtBranchAny` (`heckeSqrtBranchAny_of_heckeSqrtBranch`) |

**Rating of `NVLocalInertia`, the one new leaf: not printed form; GLUE (project, commutative algebra).**
- It is h-b1 §3 step 3, which rv-h-b1 §3 found "holds as stated".
- It is a consequence of Abhyankar's lemma (SGA 1 XIII 5.3; Grothendieck–Murre, LNM 208) and Zariski–Nagata purity
  (SGA 1 X 3.1). Locators UNVERIFIED.
- Purity in dimension 2 is **proved** in the chain (`PropTSGlue.PurityGlobalDim2`, t-purity3). Abhyankar over a DVR
  (T2) is also proved.
- No published statement has this exact form, so it is not proposed as a LEAF.

**Test cases for `NVLocalInertia` and the composite** (checked by hand; `p` a large prime):

| cover | data used | `NVLocalInertia` | composite |
|---|---|---|---|
| `ℚ(X)(√(pX))` | residue field over `0` is `ℚ`; `I_V = I_{Q_0} = ℤ/2` | true | — |
| `ℚ(√p)(X)` | residue fields over `b` ramified at `p` | hypothesis fails | — |
| h-b1's F1, `y² = p·j(27j+16)` | residue fields over `0` and `−16/27` are `ℚ`; vertical inertia `ℤ/2` (rv-h-b1 R5) | only asserts `I_V ⊆ I_{Q_0}`: true | F1 has no `√(c(27j+16))`, so the composite does not apply |
| `ℚ(j)(√(p(27j+16)))` | contains `√(c(27j+16))` with `c = p`; residue field over `0` is `ℚ(√p)`, ramified | — | `exists_good_sqrt`'s hypothesis fails, so the composite does not apply |

**The composite** (`vertUnramWitness_of_nv`, `heckeVertWitness_of_nvSqrtAny`, `heckeVertWitness_of_nvElkies`):
- `HeckeBranch` and `HeckeDegree` come from the chain (`TSHecke.heckeBranch_of'`, `heckeDegree_of_torsion`).
- `exists_good_sqrt` turns `√(c(27X + 16))` into `√(a(27X + 16))` with `p ∤ a`:
  - the residue fields over `X = 0` are unramified at `p` (`exists_point_zero_unram`, from `R1R2fp` and T5);
  - they contain `√c`;
  - `even_padicValRat_of_sq_mem` then gives `v_p(c)` even.
- `VertInertiaTrivial` reduces the goal to: every `τ` in the inertia set of every vertical prime is `1`.
- For such `τ`:
  - `τ` fixes `s`, else `p ∣ 64a` (`vert_fix`);
  - `NVLocalInertia` at `−16/27`, with the residue fields from `HeckeBranchFibreUnram`, gives `gτg⁻¹` in an inertia
    set over `−16/27`;
  - `gτg⁻¹` fixes `s` (`conj_fix`);
  - `e ∣ 2` there, so `RamifiedSqrtInertia` gives `gτg⁻¹ = 1`.

**The proofs of the four Props.**
- `ramifiedSqrtInertia`. Suppose `σ ≠ 1`.
  - Let `A'` be the ring of integers of the fixed field of `⟨σ⟩`.
  - Its fixing group `H'` is a Galois group for `B/A'` (`IsGaloisGroup.of_isScalarTower`).
  - `σ` lies in the inertia of `Q` in `H'`, so `e(Q|A') = |I_{H'}(Q)| ≥ 2` (`card_inertia_eq_ramificationIdxIn`).
  - The tower gives `e(Q ∩ A' | X − b) = 1`.
  - But `X − b = c⁻¹ s²` with `s ∈ Q ∩ A'`, a contradiction (`ramificationIdx'` as a supremum).
- `vertInertiaTrivial`.
  - `ℤ[X]_{(p)}` is a DVR. Let `S₀` be its integral closure in `E`.
  - The residue extensions are separable, because the degree is `< p`: they have degree `≤ |G|`
    (`sum_ramification_inertia_eq_card`), and `isSeparable_of_finrank_lt` applies.
  - The inertia of a prime `q₂` of `S₀` lies in the inertia set of `q₂ ∩ B_ℤ`, which is trivial. So
    `e(q₂ | R₀) = 1`.
  - Hence `p` generates the maximal ideal of `(S₀)_{q₂}`, and the chain's `vertUnramWitness_of_local` concludes.
- `heckeBranchFibreUnram`.
  - A prime over `X + 16/27` gives a `ℚ̄`-point with `π = −16/27` (`residueImage_comp_openImmersion`,
    `residueImage_specMap`).
  - `sameTripleMor_of_mobius` (`MobiusGlue` from T5) transports it to `R1R2fp`'s witness, keeping the residue field.
  - There `residue_unramified_over_branch` applies, then `unramifiedAt_of_not_dvd_discr`.
- `heckeSqrtBranchAny_of_elkies`.
  - **The coordinate (`elkies_coordinate`).**
    - The QM family on Elkies' witness `Y_E` is classified by `g' : Y_E → Y` (R1(b) universality).
    - `g'` is bijective on `ℚ̄`-points, so it is an isomorphism (`CurveSplit.curveBijIso`); call its inverse `G`.
    - The Möbius map `16(t − 1)/27` (`ShimuraGlue.Mob.good_all`) of Elkies' `t_E` satisfies `R2X6Props`
      (`orbit_iff_twist` and Elkies' CM values). Pulled back along `G`, it satisfies `R2fpProps`.
    - `MobiusGlue` then gives `16(t_E − 1)/27 = π` on `ℚ̄`-points.
  - **The section.**
    - Elkies' chart section `s = φ_U(eS)` satisfies `s² = −t_E`.
    - Pull it back along `m : Spec B → Y → X_E`. `m⁻¹(t_E ≠ ∞)` is everything: every maximal ideal of `B` is the
      kernel of a map to `ℚ̄` (`exists_ringHom_ker_eq`), which lands in `t_E ≠ ∞`; and opens are stable under
      generization.
    - This gives `s₀ ∈ B` with `ψ(s₀)² = −(1 + 27ψ(X)/16)` for every `ψ : B → ℚ̄` (`ev_spec_top`, `ev_res`,
      `ev_comp`).
    - Nullstellensatz density (`eq_zero_of_forall_ringHom_qbar`) gives `s₀² = −(1 + 27X/16)`. So
      `(4s₀)² = −(27X + 16)`.

**Checks (VERIFIED).**
- `lake build +ZInQKernel.Contrib.OneProof.SGRDirectNV +ZInQKernel.Contrib.OneProof.SGRDirectElkies` succeeds.
- `#print axioms` gives `propext, Classical.choice, Quot.sound` for every theorem listed in
  `scratch/sgr-direct/Discharges.lean`.
- No code runs at build time; the files only use `set_option` for heartbeats.
- `#discharges` (`Discharges-output.txt`): "63 open hypotheses, 1869 theorems checked, 7 discharge one". None of the
  seven is from these files, as expected: `HeckeVertWitness` is not itself an open field.

## 5. Fold plan (not executed; `scratch/sgr-direct/autofold.json`)

`autofold.py` discharges a top-level field by a proof of that field. Here neither removed field is proved: they are
bypassed at their consumer.
- `HeckeVertWitness` is a field only at generation `OpenGlue4` (TailK).
- Every generation from TailN up carries `shimuraGoodReduction` (later `NoGuard`, then `IntegralModelRep`) and
  `modelCoordinateResidue` (later `quotientP1Coordinate`).

So the fold has to regenerate the bundles from generation 5 up without those two field families, adding
`nvLocalInertia : SGRDirect.NVLocalInertia`. The TailN conversion `glue4_of_open5` becomes:

```lean
heckeVertWitness := SGRDirect.heckeVertWitness_of_nvElkies (LeafAdopt.R1R2fp_of_rep r.r1r2)
  (torsionStructure_ofK5 t.t5) l.qmAutCard l.serreRigidity3 l.alFixedPoints n.nvLocalInertia
  r.elkiesX6StarPrinted
```

The field names are those of the regenerated bundles.
- `r.r1r2` and `t.t5` are already available at generation 5.
- `elkiesX6StarPrinted` is a field of today's top research bundle, but not of generation 5. The regenerated
  generations have to carry it down, together with `nvLocalInertia`. Alternatively, the integrator can build
  `HeckeSqrtBranchAny` at the top (`heckeSqrtBranchAny_of_elkies`) and carry that Prop down instead.
- The strict count goes 56 → 55 (GLUE −1).

## 6. What remains

1. **`NVLocalInertia`.** The only open piece; commutative algebra. Proof route at the closed point `(p, X − b)` of
   `ℤ_(p)[X]`:
   - Only the divisors `p = 0` and `X = b` can ramify there.
   - Adjoin `(X − b)^{1/m}` and `p^{1/m}` (`m` prime to `p`). The result is a 2-dimensional regular local ring.
   - Over it the cover is unramified in codimension 1, by T2 at both divisors. By purity (proved in the chain) it is
     étale.
   - So, strictly henselian locally, the cover is a quotient of a Kummer cover. The unramified residue fields over
     `b` then force `I_𝔓 = I_{Q_b}`, and `I_q ⊆ I_𝔓`.

   A self-contained target for a commutative-algebra contributor.

   A variant of the last step needs no strict henselization (SPECULATIVE; paper only):
   - Let `A` be the localization of `ℤ_(p)[X]` at `(p, X − b)`, and `A₁ = A[u, w]/(u^m − (X − b), w^m − p)`.
   - Let `B₁` be the normalization of `A₁` in the compositum `E₁`. It is étale over `A₁` (T2 and purity), so the
     inertia `I(𝔓₁ | A₁)` at a closed point is trivial.
   - Hence `I(𝔓₁ | A)` embeds in `Gal(Frac A₁ / Frac A) = μ_m × μ_m`.
   - The inertia groups of the vertical prime, of the prime over `X = b`, and of the residue field over `b` at `p` all
     lie in `I(𝔓₁ | A)`. Their images in `G` satisfy `I_𝔓 = ⟨I_{Q_b}, I_q⟩`, and `I_𝔓 / I_{Q_b}` is the inertia of the
     residue field over `b`.
   - That residue field is unramified, so `I_q ⊆ I_𝔓 = I_{Q_b}`.

   Equivalently, a contributor may prove the converse of the chain's `SpecNonMeeting`:
   - **Statement.** For `E/ℚ(X)` Galois of degree `< p`, one unramified non-meeting fibre forces `NoVerticalRam`.
   - **Application.** Apply it over the subfield `ℚ(s)`, `s = √(a(27X + 16))`. Over it `s = 0` is not a branch point,
     because `e_{−16/27} ∣ 2`.
   - **What it bypasses.** `NVLocalInertia`, `RamifiedSqrtInertia` and the inertia argument altogether.
   - **Cost.** A change of base field that is not compiled here.
2. **The deep fold** (§5).

sir-printed's alternative, the weaker leaf `ShimuraIntegralModelUsed` (wip/sir-printed), keeps the integral model:
it reduces the reading task, not the GLUE count. Route NV removes the integral model and the tame quotient from the
consumer's proof, at the cost of one commutative-algebra Prop.
