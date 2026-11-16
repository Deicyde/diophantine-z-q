# cm-primitive (2026-11-16): result

**Proved in Lean.** The file is `ZInQKernel/Contrib/OneProof/CMPrimitive.lean` (namespace `CMPrimitive`; it imports only
`MainCMPolar`). Every theorem has axioms `[propext, Classical.choice, Quot.sound]` (VERIFIED). The report is
`docs/research/cm-primitive.md`.

The reading risk of mtcm-polar's `MainTheoremCMPol` (is it printed for non-primitive types?) is gone. All consumers now
follow from the leaf restricted to primitive types (`MainTheoremCMPolPrim` / `MainTheoremCMPolMaxPrim`, which add the
hypothesis `IsPrimitiveType Φ`). They also follow from the even weaker restriction to imaginary quadratic `E`, i.e. CM
elliptic curves (`MainTheoremCMPolQuad` / `MainTheoremCMPolMaxQuad`, which add `Module.finrank ℚ E = 2`; Shimura 1971
Thm 5.4). Each new leaf is the mtcm-polar statement with one added hypothesis, and each is printed form: implied by
mtcm-polar's leaf, and the primitive leaf implies the quadratic one.

Glue proved:
* the induced type of `K(√2)` is not primitive, so the gap was real (`not_isPrimitiveType_PhiE`);
* every CM type of an imaginary quadratic field is primitive (`isPrimitiveType_of_finrank_two`);
* `A` of the induced type is isogenous to `B²`, with `B` of type `(K, κ)` (`exists_isogeny_EK`);
* the reflex norm of the induced type is the inclusion composed with that of `(K, κ)` (`reflexNorm_rhoK_eq`);
* the main theorem for `(K, κ)` implies it for `(K(√2), PhiE κ)` on every lattice (`mainTheoremCMEK_of_quad`);
* mtcm-polar's isogeny step holds for any class of CM types (`mainTheoremCMSignOn_of_polar`).

Consumers, with their exact hypotheses:
* `shimuraMainCM_of_polMaxQuad (hP : MainTheoremCMPolMaxQuad) (hX : CMAbVarExists) hWU hWP hWA hUL hG : T5Glue.ShimuraMainCM`;
* `qmReciprocityL3_of_polQuad (hP : MainTheoremCMPolQuad) hX hUL hG : QMReciprocityL3`;
* `rayClassCMAb_of_polQuad`;
* the same three as `…Prim` versions.

**#discharges.** `hCM` is discharged by `shimuraMainCM_of_{arithQuad, arithPrim, polMaxQuad, polMaxPrim}` (61 open,
2712 checked, 13 discharge one; `scratch/cm-primitive/discharges.txt`).

**Fold.** It is manual, because autofold refuses `hCM` as not a bundle field. In Main.lean:65/71, replace `hCM` by the
binders `hP hE hWU hWP hWA` and the term
`CMPrimitive.shimuraMainCM_of_polMaxQuad hP hE hWU hWP hWA t.uniformizationLeafAll t.gagaMorphism`. This is checked in
`scratch/cm-primitive/FoldCheck.lean`. The specs are `scratch/cm-primitive/autofold*.json`.

**Remains.** The general `MainTheoremCM` for every non-primitive type is not re-derived, because no consumer needs it.
hcm-printed's `ε = 1` normalization reading is unchanged.
