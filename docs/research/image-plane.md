# image-plane: (G1') `ImagePlaneCurveClosed` is a theorem, and `MobiusGlue` follows from T5 alone

Task image-plane, 2026-11-13. Base f90cf864, merged with `origin/wip/curve-glue` and
`origin/wip/infra-smooth-dim`. Scratch: `scratch/image-plane/` (results log `log.md`). No file
under `ZInQKernel/`, `blueprint/` or another task's directory was edited. This is model work only;
no human has reviewed it.

Marks: **VERIFIED** means compiled, computed, or read in a file. **STANDARD** means published, with
a reference. **UNVERIFIED** means a theorem number recalled without a source (there is no network
here).

## 1. Result

**(G1') `ImagePlaneCurveClosed` is proved in Lean with no hypotheses and no leaf.** The statement
is curve-glue's, copied verbatim. The same file proves the kernel's `MobiusGlue` from the
textbook leaf T5 alone.

`scratch/image-plane/ImagePlaneFinal.lean` compiles with 0 errors (VERIFIED,
`run_ImagePlaneFinal.txt`, about 26 s wall). All eleven theorems below have axioms
`[propext, Classical.choice, Quot.sound]`:

```lean
theorem LeafQM.AV.Pin.imagePlaneCurveClosed : ImagePlaneCurveClosed        -- (G1'), the assigned Prop
theorem LeafQM.AV.Pin.imageClosed : ImageClosed                            -- (IC), was glue
theorem LeafQM.AV.Pin.algDep : AlgDep                                      -- (AD), was glue
theorem LeafQM.AV.Pin.constOrOntoAlgClosed : ConstOrOntoAlgClosed          -- C2K, was derived from leaf (L0)
theorem LeafQM.AV.Pin.imagePlaneCurveIrr : ImagePlaneCurveIrr              -- (G1'')
theorem LeafQM.AV.Pin.imagePlaneCurve : ImagePlaneCurve                    -- (G1)
theorem LeafQM.AV.Pin.ratFactorAlgClosed : RatFactorAlgClosed              -- C3K
theorem LeafQM.AV.Pin.curveFacts : CurveRatFactor ∧ CurveSurj
theorem LeafQM.AV.CurveGlue.mobiusGlue_of_T5 (hT : ObjBridge.TorsionStructure) : MobiusGlue
theorem LeafQM.AV.CurveGlue.mobiusGlueNoCM_of_T5 (hT : ObjBridge.TorsionStructure) (h : R1R2fp) :
    MobiusGlueNoCM
theorem LeafQM.AV.CurveGlue.mobiusGlue_of_t5 (h : PkgI2.TorsionStructure.{0}) : MobiusGlue
```

- `MobiusGlue` is the kernel's definition in `ZInQKernel/HDecomp/QM/Pin.lean`. The file imports
  it and does not redefine it.
- `mobiusGlue_of_t5` takes T5 in the form of the field `t5` of `HSyn.TextbookLeaves`. It goes
  through the kernel's `ObjBridge.torsionStructure_iff`, which is `Iff.rfl`.

**What this changes in the decomposition:**

| item | before (curve-glue) | now |
|---|---|---|
| (IC) `ImageClosed` | glue, open | **proved** from Mathlib (`IsProper → UniversallyClosed`) |
| (AD) `AlgDep` | glue, open | **proved** from C1b (infra-smooth-dim), C2K and (CI) |
| C2K `ConstOrOntoAlgClosed` | from the textbook leaf (L0) `FiniteGlobalSections` | **proved** from (CI) and the closed image; (L0) is not used |
| (G1') `ImagePlaneCurveClosed` | from (L0), (AD), (IC) | **proved** |
| `MobiusGlue` (row 12 of the h-decomposition glue table; field `mobius` of `HSyn.GluePiecesPin`) | from (L0), (AD), (IC), T5 | **from T5 alone**; T5 is already in `TextbookLeaves` (`t5`) |

**Consequence for the bundle.** The field `mobius` of `HSyn.GluePiecesPin` can be filled by
`mobiusGlue_of_t5 t.t5`. Neither the leaf (L0) nor any curve glue needs to be added.

No statement was changed. Every copied declaration is textually identical to its source,
docstring included; the check is `py/verbatim.py`, output `verbatim.txt`, ALL OK (VERIFIED).

## 2. The chain

Each arrow is a compiled Lean theorem. New arrows are marked ★.

```
IsProper f (Mathlib: UniversallyClosed, isClosedMap of pullback.snd) ──★ image_closed──▶ (IC)
(IC) machinery with ρ = σ, (CI) ──★ constOrOntoAlgClosed_of_CI──▶ C2K
C1b (infra-smooth-dim), C2K, (CI), (IC) machinery ──★ algDep_of──▶ (AD)
C2K, (CI), (AD), (IC) ──imagePlaneCurveIrr_of (curve-glue)──▶ (G1'')
(CI), (G1'') ──imagePlaneCurveClosed_of (curve-glue)──▶ (G1')
C2K, (G1') ──imagePlaneCurve_of──▶ (G1) ──ratFactorAlgClosed_of──▶ C3K
C1b, C2K, C3K ──curveFacts_of_leaves (curve-facts)──▶ CurveRatFactor ∧ CurveSurj
CurveRatFactor, CurveSurj, T5 ──mobiusGlue_of_curves (mobius-glue, aut-o-finite)──▶ MobiusGlue
```

(CI) `componentIrreducible` (curve-glue) and C1b `smoothStalkDimOne` (infra-smooth-dim) are proved
theorems in the composite.

## 3. (IC) from properness (`IC.lean.part`, `ImagePlane.image_closed`)

**General statement.** Let `X` be proper over `K = K̄`, let `T ⊆ X` be closed and let
`σ, ρ : ToP1 X`. Then the set of pairs `(σ(p), ρ(p)) ∈ K²`, over the `K`-points `p ∈ T` where both
values are finite, is the common zero set of some `S ⊆ K[x][y]`. Smoothness is not used.

**Proof.**

1. **Setup.** Let `𝔸² = Spec K[x][y]` and `P = X ×_K 𝔸²` (Mathlib's `pullback f g2`).
2. **The graph.** Let `Z ⊆ P` be the complement of the four basic opens
   - `D(f_σ − x)` on `fst⁻¹ U_σ` and `D(x·g_σ − 1)` on `fst⁻¹ V_σ`,
   - and the same for `ρ` with `y`,

   intersected with `fst⁻¹ T`.
   - `Z` is closed with no gluing argument: a basic open is open in `P`.
   - On `K`-points, `Z` is exactly the graph of `(σ, ρ)` over `T` (`not_mem_bad_iff`). Off `U_σ`,
     `g_σ = 0`, so `x·g_σ = 1` fails.
3. **The image is closed.** `C = snd(Z)` is closed in `Spec K[x][y]`. This uses Mathlib's
   `universallyClosed_snd` and `Scheme.Hom.isClosedMap`, with `IsProper → UniversallyClosed`.
4. **The equations.** Take `S = vanishingIdeal C`. For `(t, u) ∈ K²`, let `m = ker(ev_{t,u})`.
   Then `S` vanishes at `(t, u)` iff `m ∈ closure C = C`. This uses
   `zeroLocus_vanishingIdeal_eq_closure` and `ptOf_spec_asIdeal`.
5. **Points of `X` give points of `C`.** A `K`-point `p` gives the point
   `q = pullback.lift p (Spec ev_{t,u})` of `Z` over `m`.
6. **Points of `C` give points of `X`.**
   - `Z ∩ snd⁻¹{m}` is closed and nonempty, and `P` is Jacobson and of finite type over `K`. So
     the set contains a `K`-point `q` (curve-glue's `exists_point_of_isLocallyClosed`).
   - `p = q ≫ fst` is a `K`-point of `X` in `T`.
   - The ring map `Spec.preimage (q ≫ snd) : K[x][y] → K` is a `K`-algebra map with kernel `m`,
     so it sends `x ↦ t` and `y ↦ u` (`eq_of_ker_eq`).
   - Hence `σ(p) = t` and `ρ(p) = u`.

**New value-calculus lemmas:**

| lemma | content |
|---|---|
| `ptOf_comp` | the point of `q ≫ h` is `h(ptOf q)` |
| `ev_comp` | `ev (q ≫ h) s = ev q (h^* s)`, from Mathlib's `stalkClosedPointTo_comp` and `germ_stalkMap_apply` |
| `ev_spec_top` | `ev (Spec φ) Q = φ(Q)` |
| `ptOf_spec_asIdeal` | the point of `Spec φ` is `ker φ` |

## 4. C2K from (CI) (`C2Kproof.lean.part`)

**Step 1: finite or everything** (`image_finite_or_univ`). Apply `image_closed` with `ρ = σ`.
The finite values of `σ` on the `K`-points of `W` are then the zeros of the diagonal polynomials
`Q(x, x)`, for `Q ∈ S` (`eval_diag`). So they form a finite set or all of `K`.

**Step 2: a finite set of values means constant** (`const_of_finite`).

- The loci `{σ = t} = X ∖ (D(f_σ − t) ∪ D(t·g_σ − 1))` are closed (`not_mem_badX_iff`), and so
  is `{σ = ∞} = X ∖ U_σ`.
- Finitely many of them contain every `K`-point of `W`. By Jacobson they cover `W`.
- `W` is irreducible by (CI), so one of them contains `W`.

**Step 3: constant or onto.**

- Apply steps 1 and 2 to `1/σ` as well (`ImagePlane.inv` swaps the charts;
  `val_eq_recip : σ(p) = 1/(1/σ)(p)`).
- If both value sets are all of `K`, then `σ` is onto `P¹(K)`: `∞` is hit where `1/σ = 0`.
- Otherwise `σ` is constant on `W`.

This replaces curve-glue's route through (L0) (finiteness of `Γ(W, 𝒪)`, EGA III 3.2.1). Here,
properness enters only through Mathlib's `UniversallyClosed`.

## 5. (AD) (`AD.lean.part`, `algDep_of`)

**If `σ` is constant on `W`,** take `P = x − c` when the constant value is `c`, or `P = 1` when it
is `∞`.

**Otherwise:**

1. **`σ` is onto** by C2K, so it takes the values `0` and `1` on `W`.
2. **The zero locus of `σ` is a proper closed subset.** `Y = W ∖ V_σ` is closed, since
   `D(f_σ) = U_σ ∩ V_σ`, and its `K`-points are exactly the points where `σ = 0`. The point where
   `σ = 1` lies in `V_σ`, so `Y ≠ W`.
3. **`Y` is finite** (`finite_of_closed_ssubset`).
   - Suppose an irreducible component `Y' ⊊ W` of `Y` contains a closed point `x` other than its
     generic point.
   - Then `x < η(Y') < η(W)` in the specialization order, so `coheight x ≥ 2`.
   - Mathlib's `ringKrullDim_stalk_eq_coheight` (Stacks 02IZ) turns this into
     `dim 𝒪_{X,x} ≥ 2`. This contradicts C1b, which gives `dim 𝒪_{X,x} = 1` (infra-smooth-dim).
4. **Only finitely many `u` have `(0, u)` in the image.** A finite value of `ρ` at a `K`-point
   depends only on the underlying point (`val_eq_of_ptOf_eq`).
5. **Choosing `P`.** `K` is infinite, so pick `u` outside that finite set. Then some `Q ∈ S`
   (from (IC)) has `Q(0, u) ≠ 0`. Hence `Q ≠ 0`, and `Q` vanishes on the image. Take `P = Q`.

## 6. Files and verification

All runs used `lake env lean` on one file, one Lean process at a time. The kernel modules
`ZInQKernel.HDecomp.QM.Pairs`, `.QM.Pin` and `.Textbook.SkolemNoether` were built with
`lake build` for the imports.

| file | content | outcome (VERIFIED) |
|---|---|---|
| `ImageClosed.lean` (`mk_ic.sh`) | `imageClosed`; imports Mathlib and the kernel's `QM.Pairs` only | 0 errors, standard axioms, `run_ImageClosed.txt` |
| `AlgDepProof.lean` (`mk_ad.sh`) | `imageClosed`, `algDep_of`, `constOrOntoAlgClosed_of_CI`, `algDep_of_CI` | 0 errors, standard axioms, `run_AlgDepProof.txt`; warnings only for the `if_pos`/`if_neg` deprecations |
| `ImagePlaneFinal.lean` (`mk_final.py`) | curve-glue's `MobiusFinal.lean` verbatim (without its `#print` lines), then the three parts, then the theorems of §1 | 0 errors, standard axioms for all eleven, `run_ImagePlaneFinal.txt` |
| `IC.lean.part`, `AD.lean.part`, `C2Kproof.lean.part` | the new proofs | compiled inside the files above |
| `ICbase.lean.part`, `ADbase.lean.part` | verbatim copies: value calculus of curve-glue's `C2K.lean`; `evalXY`; the Props | checked by `py/verbatim.py` |

## 7. What remains

- **Nothing remains in the (G1') chain.**
- **`MobiusGlue` needs only T5** (`ObjBridge.TorsionStructure`, Mumford, *Abelian Varieties*
  §4, the existing leaf).
- **Integration.**
  - Add kernel modules containing `ImagePlaneFinal.lean`'s mathematics: infra-smooth-dim's
    dimension theory, curve-facts, curve-glue's C3K/ClauseC/AlgDep/CI sections, mobius-glue and
    aut-o-finite, and the three image-plane parts.
  - Then replace the field `mobius : MobiusGlue` of `HSyn.GluePiecesPin` by
    `mobiusGlue_of_t5 t.t5`.
  - curve-glue's (L0) section and its `FiniteGlobalSections` leaf can be dropped. They are no
    longer used by any theorem of §1.
