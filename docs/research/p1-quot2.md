# p1-quot2: `quotientP1Coordinate` without L1 and without `CMStabObjWeak`

Task p1-quot2, 2026-11-15. Base `wip/p1-quot` (f30ece89), with `origin/wip/cm-stab` (6242b2f9: leaf-fold22 plus
cm-stab) merged cleanly (0e783b9b). Target: the bundle field `HDec.HSyn.OpenGlue7.quotientP1Coordinate`, of type
`HDec.MCRGlue.QuotientP1Coordinate` (`ZInQKernel/OneProof/H/TailW.lean` L202, unchanged). Scratch:
`scratch/p1-quot2/`, with the results log in `log.md`. No statement was changed. No file under `ZInQKernel/` was
edited except the new files under `ZInQKernel/Contrib/OneProof/`.

Marks: **VERIFIED** means compiled, or read in a source file. **STANDARD** means a published theorem with its
reference. **UNVERIFIED** marks a locator recalled from memory; there is no network here.

## 1. Main result

**Two of p1-quot's four strict GLUE inputs are gone.**

- mcr-glue's composite leaf L1 `ProperCurveAF` is replaced by one printed leaf, Lichtenbaum's projectivity theorem
  (`QuotientP1Proof.LichtenbaumProjective`). Every step from that print to what the proof uses is compiled.
- The QM glue `CMStabObjWeak` is proved from cm-stab's `GapGlue.cmStabObj_of`, whose inputs are three textbook
  fields the chain already has.
- What remains: mcr-glue's L3 `TameQuotientSmooth` (a composite) and L4 `SmoothModelOfP1` (a consequence). Neither
  has a printed form I could find (§4).

Strict count of the fold:

| | strict GLUE | strict LEAF |
|---|---|---|
| p1-quot | +3 | |
| after this task | +1 (`autofold --dry-run`: 46/10 on 56 → 49/11 on 60; strictest 45/11 → 48/12) | +3 |

The fold still does not pay: autofold refuses it without `--allow-rise`.

```lean
-- ZInQKernel/Contrib/OneProof/QuotientP1Printed.lean
theorem HDec.MCRQuot.quotientP1Coordinate_of_fields2
    (hL : QuotientP1Proof.LichtenbaumProjective)    -- NEW printed leaf (Lichtenbaum 1968 Thm 2.8; Liu Thm 8.3.16)
    (hQE : FiniteQuotientExists)                    -- mcr-glue L2 (published, special case)
    (hTS : TameQuotientSmooth)                      -- mcr-glue L3 (composite)
    (hP1 : SmoothModelOfP1)                         -- mcr-glue L4 (consequence)
    (hE : EdixhovenFixedSmooth2)                    -- p1-quot's printed leaf (Edixhoven 1992 Prop. 3.4)
    (hMT : AvSplit.MumfordTorsionAlgClosed)         -- textbook field
    (hRC : LeafQM.AV.R1UnivRigid.MumfordRigidityCore)  -- research field
    (hD : ShimuraGlue.DeligneComponentsY3PrintedAb)    -- added field
    (hU : BPAnalytic.Uniformization.UniformizationLeafAll)  -- textbook field
    (hG : ZInQ.HomLattice.GAGAMorphism) :           -- textbook field
    MCRGlue.QuotientP1Coordinate
```

VERIFIED (compiled; outputs in `scratch/p1-quot2/`):

- `lake build +ZInQKernel.Contrib.OneProof.QuotientP1Printed` succeeds on the merged tree. That covers the helper
  `QuotientP1/Lichtenbaum.lean`, p1-quot's modules rebuilt against leaf-fold22, and cm-stab's `CMStab.lean`. There
  is no `sorry` and no `axiom`.
- `#discharges` (`Discharges.lean`, output `discharges_out.txt`) prints
  `DISCHARGES [OpenGlue7.quotientP1Coordinate] by HDec.MCRQuot.quotientP1Coordinate_of_fields2`. It still assumes
  exactly the ten inputs above, with axioms `[propext, Classical.choice, Quot.sound]` (63 open hypotheses, 2141
  theorems checked).
- `topologicalKrullDim_eq_two`, `exists_affine_of_lichtenbaum` and `exists_isAffineOpen_superset_of_isClosedImmersion_spec`
  depend on the standard axioms only (`l1_out.txt`).
- The autofold spec `scratch/p1-quot2/autofold.json` was checked with `--dry-run --allow-rise`. With line 1
  stripped, the generated module (`FoldDry.lean`: `OpenGlue8`, `openGlue7_of_OpenGlue8`, `sixContactMin_of_open29`)
  compiles against TailZ34, and `sixContactMin_of_open29` has standard axioms.

## 2. Step 1: `CMStabObjWeak` from cm-stab (count +3 → +2)

cm-stab (branch `origin/wip/cm-stab`, `ZInQKernel/Contrib/OneProof/CMStab.lean`, which has no report yet) proves:

```lean
GapGlue.cmStabObj_of : BPAnalytic.Uniformization.UniformizationLeafAll → ZInQ.HomLattice.GAGAMorphism →
  AvSplit.MumfordTorsionAlgClosed → ObjBridge.TorsionStructure → GapGlue.CMStabObj
```

- `GapGlue.CMStabObj` is mcr-quot's `CMStabObj`, involution clause included, copied verbatim. It is definitionally
  equal to p1-quot's `HDec.MCRQuot.CMStabObj`: `cMStabObjWeak_of (GapGlue.cmStabObj_of …)` typechecks (VERIFIED).
- T5 comes from the field `mumfordTorsionAlgClosed` (`AvSplit.torsionStructure_of_mumford`).
- So `cMStabObjWeak_of_fields hU hG hMT : CMStabObjWeak`, from the fields `uniformizationLeafAll`, `gagaMorphism`
  and `mumfordTorsionAlgClosed` of `OpenTextbookLeaves11`. No new hypothesis.
- This also settles p1-quot's §4 analysis. cm-stab finds the `ℤ[ζ₃]` and `ℤ[√−6]` stabilizers as semilinear units
  `g = ι(j)⁻¹(2φ−1)` and `g = ι(k)⁻¹φ`, built in `End(A)` through the lattice model, so the Atkin–Lehner-type twist
  is available after all.

## 3. Step 2: L1 → Lichtenbaum's theorem (count +2 → +1)

### 3.1 The new leaf

```lean
/-- Lichtenbaum 1968 Thm 2.8; Liu, AGAC, Thm 8.3.16 (S = Spec R, R a DVR). -/
def QuotientP1Proof.LichtenbaumProjective : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of R)), IsIntegral X → IsProper f → Flat f →
    (∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) → topologicalKrullDim X = 2 →
    ∃ (n : ℕ) (i : X ⟶ ℙ(Fin (n + 1); Spec (CommRingCat.of R))),
      IsClosedImmersion i ∧ i ≫ ℙ(Fin (n + 1); Spec (CommRingCat.of R)) ↘ Spec (CommRingCat.of R) = f
```

Every notion in it is a genuine definition:

- Mathlib's `IsIntegral`, `IsProper`, `Flat`, `IsRegularLocalRing` (Stacks 00KU), `topologicalKrullDim` and
  `IsClosedImmersion`;
- `ℙ(Fin (n+1); S)`, the vendored Jacobian-Challenge relative projective space (CloudW07). It is
  `Proj ℤ[X₀,…,Xₙ] ×_ℤ S`, which is Liu's `ℙⁿ_S`.

"Projective" is Liu's definition: a closed immersion into `ℙⁿ_S` over `S`.

**Rating: printed form (special case).** Source: S. Lichtenbaum, *Curves over discrete valuation rings*, Amer. J.
Math. 90 (1968), 380–405, Thm. 2.8; Q. Liu, *Algebraic Geometry and Arithmetic Curves* (Oxford 2002), Thm. 8.3.16.
Both locators are UNVERIFIED. As remembered, the statement is: for `S` a Dedekind scheme of dimension 1 and `X → S`
proper and flat with `X` integral and regular of dimension 2, `X → S` is projective.

The leaf is that statement for `S = Spec R`, `R` a DVR, in universe 0. Flag it **unread**. A reader should check
two things:

- whether the print states integrality or flatness as hypotheses (stating them here only weakens the leaf);
- the theorem number in Liu.

Proposed row for docs/research/locators.md: `LichtenbaumProjective | Lichtenbaum, Amer. J. Math. 90 (1968) Thm 2.8;
Liu AGAC Thm 8.3.16 | UNVERIFIED`.

### 3.2 From the print to what the proof uses (all compiled; `QuotientP1/Lichtenbaum.lean`)

| step | Lean | how |
|---|---|---|
| EGA II 4.5.4 / Liu Prop. 3.3.36(b): a finite set in a closed subscheme of `ℙ(ι; Spec R)` lies in an affine open | `exists_isAffineOpen_superset_of_isClosedImmersion_spec` | the vendored field case's proof (graded prime avoidance `ProjectiveSpectrum.exists_homogeneous_notMem_of_finset`, then `D₊(f)` affine) uses only that the base is affine |
| fibres of a smooth relative curve have dimension `≤ 1` | `topologicalKrullDim_fiber_le` | Mathlib `Scheme.Hom.fiber`, `fiberToSpecResidueField` (base change keeps `SmoothOfRelativeDimension 1`), `ZInQ.Contrib.Dim.topologicalKrullDim_eq_of_smoothOfRelativeDimension` |
| no strict chain of length 2 inside a fibre | `not_chain_in_fiber` | `fiberHomeo` plus `fiberι` an embedding, so specialization is preserved and reflected |
| every point has coheight `≤ 2` | `coheight_le_two` | a chain `a₀ < a₁ < a₂ < a₃` must cross from the special fibre to the generic one at `a₁ < a₂`. Then `a₁` is maximal in the special fibre, so its stalk is a DVR (vendored FLT `Smooth.isDiscreteValuationRing_stalk_of_forall_specializes`) of dimension 1 = `coheight a₁` (Mathlib `ringKrullDim_stalk_eq_coheight`), against `a₁ < a₂ < a₃` |
| `dim X = 2` for `X` integral, proper and smooth of relative dimension 1 over a DVR | `topologicalKrullDim_eq_two` | `≤`: from the coheights. `≥`: the generic point lies over `⊥` (flat maps are generalizing). The special fibre is nonempty (proper maps are closed) and has dimension 1, so it contains `c₀ < c₁`, and `c₀ < c₁ < η_X` |
| regular stalks | vendored FLT `Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing` | |
| L1 for integral models | `exists_affine_of_lichtenbaum` | Lichtenbaum, then EGA II 4.5.4 |

In the composite (`quotientP1Coordinate_of_printed2`), the model `𝒴` is integral by p1-quot's `isIntegral_model`
(from `CurveBijIso` and `HeckeIrreducible`). Its affine-neighbourhood property is
`exists_affine_of_lichtenbaum hL 𝒴.hom`, and it feeds L2 exactly where L1 did.

mcr-glue's L1 is stated for all proper smooth relative curves, not only integral ones. Only the integral case is
used, so L1 itself is not proved and not needed.

## 4. What remains: L3 and L4, with ratings

| input | kind | printed form? | reason |
|---|---|---|---|
| `LichtenbaumProjective` (new) | published | yes, special case | §3.1; flag **unread** |
| L2 `FiniteQuotientExists` | published | yes, special case | SGA 1 Exp. V Prop. 1.8 with 1.1 (UNVERIFIED); mcr-glue's rating, unchanged |
| `EdixhovenFixedSmooth2` | published | yes, special case | p1-quot's rating (Edixhoven 1992 Prop. 3.4, UNVERIFIED); flag **unread** |
| L3 `TameQuotientSmooth` | composite | no | see below |
| L4 `SmoothModelOfP1` | consequence | no | see below |
| T5, `HeckeIrreducible`, `CMStabObjWeak` | supplied by the chain's fields | — | §2; p1-quot `FromFields.lean` |

**L3** (`𝒴/G` is proper and smooth of relative dimension 1 for `p ∤ |G|`). Its parts and how far each can go
(SPECULATIVE plan, not compiled):

- **Universally closed.** `q` is surjective (integral and injective on sections, so lying over holds), then Mathlib
  `UniversallyClosed.of_comp_surjective`. Lean-provable.
- **Locally of finite type.** On an affine `W`, `Γ(W) ⊆ Γ(q⁻¹W)` is finite (`q` finite), and the larger ring is of
  finite type over `ℤ_(p)`. Artin–Tate is Mathlib `Algebra.fg_of_fg_of_fg`. Lean-provable.
- **Flat.** A subring of a torsion-free `ℤ_(p)`-module is torsion-free, hence flat over the DVR. Lean-provable.
- **Smooth fibres.**
  - Generic fibre: invariants of a normal ring are normal; a normal Noetherian local ring of dimension `≤ 1` is
    regular; then the chain's textbook field `regularSmoothPerfect` (Stacks 00TV).
  - Special fibre: the Reynolds operator `|G|⁻¹ Σ g` gives `Γ(W)/p = (Γ(q⁻¹W)/p)^G`, an elementary computation
    valid because `p ∤ |G|`. So the special fibre is again a quotient of a smooth curve. With the same normality and
    regularity steps, and `regularSmoothPerfect` over `𝔽_p`, the fibre is smooth.
  - Then Mathlib's EGA IV 17.5.1 (`Smooth.of_smooth_fiberToSpecResidueField`) gives `Smooth`.
  - The relative dimension 1 needs the rank of `Ω` along the fibres.
- **Separated.** The standard argument: `𝒴 ×_S 𝒴 → 𝒵 ×_S 𝒵` is integral and surjective, and the preimage of the
  diagonal is the union of the graphs. Lean-provable in principle, but long.

So L3 needs no new printed leaf beyond `regularSmoothPerfect`, which the chain already has. But it is a long Lean
project: by my estimate 1.5–2.5k lines of scheme plumbing (fibres of the quotient, invariant rings of non-domains,
the rank of `Ω`). It was not attempted beyond this plan.

I found no single printed statement "a tame quotient of a smooth proper relative curve over a DVR is smooth" that I
can name with confidence. Candidates that are not checked: Katz–Mazur, *Arithmetic moduli of elliptic curves*,
appendix to Ch. 7 (quotients by finite groups); SGA 1 Exp. V Prop. 1.9 (base change). If such a statement were
found and read, L3 would become one printed leaf and the count would fall to 0.

**L4** (a smooth proper model of `P¹_ℚ` over `ℤ_(p)` is `P¹_{ℤ_(p)}`).

- It is true and standard, but I know no printed theorem with this statement. The known proofs go through:
  - geometric connectedness of the special fibre (Zariski connectedness, `f_*𝒪 = 𝒪_S`);
  - genus 0 of the special fibre (constancy of `χ(𝒪)` in flat proper families, EGA III 7.9.4);
  - a rational point by properness;
  - a lift of the isomorphism `𝒵_s ≅ ℙ¹` (the line bundle of a section with `H¹ = 0`, cohomology and base change,
    EGA III 7.7.5), or Brauer–Severi theory (Grothendieck, *Le groupe de Brauer* I §8, plus the injectivity of
    `Br(ℤ_(p)) → Br(ℚ)`).
- Each of these needs coherent cohomology of schemes over a DVR, which Mathlib v4.35 does not have. The vendored
  Jacobian-Challenge library has curve cohomology only over fields.
- So L4 stays a consequence (mcr-glue's rating), and I see no route to printed form within this project's Lean
  today.

**An alternative route, not pursued.** Replace L1–L4, Edixhoven, C1 and C2 together by:

- good reduction of tame three-point covers (S. Beckmann, *Ramified primes in the field of moduli of branched
  coverings of curves*, J. Algebra 125 (1989); UNVERIFIED). The cover `π : Y → P¹` is Galois with group of order
  dividing 144, branched over `0, ∞, −16/27`, which stay distinct mod `p > 3`;
- uniqueness of smooth proper models in genus `≥ 1` (Liu, AGAC, §9.3 and §10.1, Lichtenbaum–Shafarevich;
  UNVERIFIED).

This trades the quotient machinery for statements about covers. It needs Lean statements of "G-cover with good
reduction" and of the genus of `Y`, neither of which the chain has.

## 5. Deliverables and reproduction

- `ZInQKernel/Contrib/OneProof/QuotientP1Printed.lean`: `cMStabObjWeak_of_fields`, `quotientP1Coordinate_of_printed2`,
  `quotientP1Coordinate_of_fields2`. It imports p1-quot's `QuotientP1/FromFields` (which imports
  `QuotientP1Coordinate` and TailZ17), the new helper and cm-stab's `CMStab`. It never imports `Main`.
- `ZInQKernel/Contrib/OneProof/QuotientP1/Lichtenbaum.lean`: the helper, generated from `scratch/p1-quot2/L1.lean`
  by `scratch/p1-quot2/gen_helper.py`. Namespace `QuotientP1Proof`. It imports Mathlib, CloudW07, Contrib/Dim and
  CloudW03 only.
- `scratch/p1-quot2/autofold.json`: discharges `quotientP1Coordinate` with leaves `lichtenbaumProjective`
  (published), `finiteQuotientExists` (published), `tameQuotientSmooth` (composite), `smoothModelOfP1`
  (consequence) and `edixhovenFixedSmooth2` (published). Flags are left empty, so autofold marks the published ones
  "unread". It uses `{t}`, `{r}` and `{l}` for the five existing fields, so no hand edit is needed: p1-quot's
  fold-note problem is solved.
- Build tree: a copy of `yu-prune-base`'s build (c2ad4181), then `lake build` of the merged tree (31 min for
  LPrefix…TailZ26, QMLattice, CMStab), and `lake build +Main +Discharges` (2 min).

```
lake build +ZInQKernel.Contrib.OneProof.QuotientP1Printed
lake env lean scratch/p1-quot2/L1.lean            # scratch copy of the helper with #print axioms (~45 s)
lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
lake env lean scratch/p1-quot2/Discharges.lean    # #discharges
python3 scripts/one_proof/autofold.py scratch/p1-quot2/autofold.json --dry-run --allow-rise
```
