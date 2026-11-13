# rv-leaves48: proposed repairs (text only; `scratch/h-decomposition/Leaves.lean` is not edited)

No leaf statement needs a change: no concrete leaf was found OVER-STRONG, VACUOUS or MISSTATED.
The repairs below fix docstrings and one bundle-completeness gap. Line numbers refer to
`scratch/h-decomposition/Leaves.lean` at 01267822.

## P1. Height leaves: "not yet known non-vacuous" is the wrong description (docstring)

Leaves.lean 19181-19182 (bundle field `r19`) and h-decomposition.md lines 260, 340, 758, 773, 783,
821, 881 say that R19-R21 are "not yet known to be non-vacuous (AN3 open)". The value of
`stableFaltingsHeight A` is either `⊤` (exactly when `A` has no `MetrizedModel`; compiled,
`RvLeaves48D.sfh_eq_top_iff`) or the genuine stable Faltings height. The `⊤` case cannot make
R19-R21 false: R19 and R20 become vacuous at `A`, and R21 becomes trivially true there (compiled,
`r19r20_hyp_false_of_empty`, `r21_trivial_of_empty`). An encoding error would show up as a
**false** `H5.StableHeightFinite` (compiled, `H5_forces_metrized_model`). Replacement for the
docstring of `r19`:

```
  /-- R19-R21 over def-faltings' `stableFaltingsHeight`. Its value is `⊤` (no metrized model) or
  the stable Faltings height in Faltings' normalization, so R19-R21 are true for the definition;
  they say something only together with `h5` (`StableHeightFinite`), which is where a defect of
  the definition would surface, as a false leaf (rv-leaves48, `RvLeaves48D`). -/
```

## P2. `X1ModelExists` is in neither bundle (bundle completeness; known glue target)

`r16 : LeafModCurves.R16_EichlerShimuraJ1'` and `t34 : LeafModCurves.DimJ1Genus` quantify over
`J` with `IsJ1 N J`. Such a `J` exists only given `LeafModCurves.X1ModelExists` (16419) together
with T33. leaf-modcurves and h-decomposition.md (line 717) record it as a glue target, but neither
`ResearchLeaves` nor `TextbookLeaves` contains it and no theorem of Leaves.lean proves it. The
glue for C9, E1 and E2 therefore cannot use r16 or t34 until one of these is done:

- prove `X1ModelExists` (MC4 + MC10 of bp-modcurves: the normalization of `ℙ¹_j` in `K_N` with a
  rational cusp), or
- add it as a textbook leaf (Shimura 1971 §6.7, the canonical model of `X₁(N)` with a rational
  cusp; locator UNVERIFIED):

```lean
  /-- T35 (proposed, rv-leaves48): a pointed model of `X₁(N)` over `ℚ` (Shimura 1971 §6.7,
  canonical model with a `ℚ`-rational cusp; or glue MC4 + MC10). Without it `r16`, `t34` are
  vacuous. -/
  t35 : LeafModCurves.X1ModelExists
```

Compiled check (`Probes.lean`, section `RvLeaves48Bundle`): `ResearchLeaves`, `TextbookLeaves` and
`X1ModelExists` give `LeafModCurves.ModCurveLeaves` and `exists_J1`.

## P3. QM leaves: state the premise with its type (docstring)

Leaves.lean 19112 (bundle field `r1r2`) says "polarization exists and is unique". Without the
Rosati type, a principal polarization of `(A, ι)` is **not** unique: there is one for each
`c ∈ 𝒪` with `c² = −6`, up to sign (rv-qm-polar C1). Replacement:

```
  /-- ... Premise (rv-qm-polar Lemma P): for a QM pair `(A, ι)` in characteristic 0 there is
  exactly one principal polarization whose Rosati involution is `x ↦ μ⁻¹x̄μ` on `ι(𝒪)`
  (`μ = 2j + ij`, the type fixed by the PEL datum). Checked by model reviews (rv-qm-polar), no
  human review. -/
```

The same wording applies to the "SPECULATIVE premise" passages at 15294, 15625, 18693 and 18723.
rv-qm-polar has since replaced "SPECULATIVE" with "holds with conditions C1-C4".

## P4. T23 is a consequence, not "Exact" (docstring, 4692)

`T23_FontaineClosure` restates Fontaine's Tannakian closure in matrix form, on `V^∨`. It is a
consequence of the published statement. Replace "Exact." with "Consequence (matrix form of the
published statement)."

## P5. t16b: name the normalization (docstring, 5147-5148)

Replace "the canonical reciprocity map is one such θ" with "the reciprocity map normalized to send
uniformizers to arithmetic Frobenius elements (Serre's convention) is one such θ; its inverse
normalization does not satisfy clause 3". rv-leaves-b (its line 141) says that θ ↦ θ⁻¹
"preserves every clause". That is wrong for clause 3, although the leaf is still true.

## P6. T31: make the `cd Ẑ = 1` citation consistent

h-decomposition.md line 854 cites Serre, *Galois cohomology*, "II §3"; glue-descent.md line 239
cites "I §3". The statement `cd(Ẑ) = 1` is in Ch. I, §3.2 (UNVERIFIED, from memory). Pick one.

## P7. Two `GaloisRep` structures (glue note, not a leaf issue)

`r14`/`r15` use `HSyn.GaloisRep` (18814), while `r13` and `PanFor` use `PkgI4.GaloisRep` (3955).
They are distinct structures with the same fields, so the glue `glueOutputs_of_leaves` must
convert between them (a one-line structure map). Unifying them in the integrated file would remove
the conversion.
