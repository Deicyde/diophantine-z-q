# qm-glue: the glue Props qm-split left (Shimura curve rows H-87, H-88, H-44, H-1/H-43/H-59)

Task qm-glue, 2026-11-14. Base debc37b4 (wip/w56). Lean: `scratch/qm-glue/` (results log `log.md`). No file
under `ZInQKernel/`, `blueprint/`, or another task's notes or scratch was edited. Model work, no human review.

Marks: **VERIFIED** = compiled, computed, or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. Theorem numbers and locators recalled without a source are **UNVERIFIED** (no
network here).

## 1. Main result

* **(b) `GammaStarFromO1` is a theorem** (no leaf, Mathlib only; VERIFIED, compiled, standard axioms):
  `HDec.LeafQCheck.QMglue.gammaStarFromO1_proof : HDec.LeafQCheck.QMSplitVB.GammaStarFromO1`
  (`scratch/qm-glue/GammaStar.lean`; `Valence.lean`'s statement copied verbatim) and the same for `Haupt.lean`'s
  textually identical copy, `HDec.LeafQCheck.HM.QMSplit.gammaStarFromO1_proof`. Shimizu's statement for
  `Γ¹ = ι(𝒪¹)` (cocompact Fuchsian, a fundamental domain of area `2π/3`) gives `Γ*` cocompact Fuchsian with a
  fundamental domain of area `π/6`.
* **Consequently rows H-87 and H-88 rest on published-form leaves only** (VERIFIED, compiled over the
  leaf-fold4 chain, `scratch/qm-glue/HauptGlue.lean`):
  * `valenceFormulaGammaStar_of_leaves : ValenceFormulaCocompactEq → ShimizuCovolumeO1 →
    HDec.LeafQCheck.VB.ValenceFormulaGammaStar` (H-87; also from the inequality leaf `ValenceFormulaCocompact`);
  * `qmHauptmodulBase3_of_leaves : PkgI1.ThetaModularity → ValenceFormulaCocompactEq → ShimizuCovolumeO1 →
    IgusaCMValue24 → QMHauptmodulBase3` (H-88).
* **(a) `ThetaQuotientValue24` is reduced to one explicit numeric statement and to the published value**
  (VERIFIED, compiled, `scratch/qm-glue/ThetaValue24.lean`):
  * the CM point is computed exactly: the only point fixed by `ι(μ)` is `τ₂₄ = i(√6 + √3) = i√(9 + 6√2)`
    (`fixedPoint_eq`), and its period matrix is explicit,
    `Ω(τ₂₄) = Ω₂₄ = [[(−4+3√−6)/14, (−1−√−6)/7], [(−1−√−6)/7, (−4+3√−6)/7]]` (`omega_tau24`);
  * `thetaQuotientValue24_iff : ThetaQuotientValue24 ↔ ThetaValueAtOmega24` (the ten even theta constants at
    `Ω₂₄` satisfy `(Σθ⁸)⁵ ≠ 0` and `3779136(∏θ²)²/(Σθ⁸)⁵ = −16/27`);
  * LEAF `IgusaCMValue24` (Lin–Yang's Igusa vector `J₂ = 12(j+1)λ, J₄ = 6(j²+j+1)λ², J₁₀ = j³λ⁵` at the
    Baba–Granath CM value `j = −16/27`, in Igusa/LNY's theta normalization: the manuscript's own citation,
    l.908-923) with `thetaQuotientValue24_of_igusa` and the converse `igusa_of_thetaQuotientValue24`: the leaf
    is equivalent to the glue, not stronger. The published content used is one number.
  * Not achieved: an exact Lean computation of `−16/27` (see §2.3).
* **(d) the coarse-witness comparison is named and reduced to one smaller glue** (VERIFIED, compiled over the
  chain, `scratch/qm-glue/ModuliCompare.lean`): `CoarseFactor` (a morphism `X → X'` between two coarse
  witnesses over one fine witness, compatible with the moduli bijections) plus model-glue's `CurveBijIso`
  (proved outright by curve-split) give the comparison isomorphism `CoarseCompare`; with it the universal glue
  Props `CoarseX6OfFine`, `HauptmodulOfX6`, `ResidueOfX6`, `ConicOfWitness`, `ConnectedOfFine` of qm-split
  follow from **existential** statements about one witness (the published statements on the canonical model),
  and rows H-1 and H-43 follow (`r1r2fpRep_of_canonical`, `x6ConicModel_of_canonical'`). The uniqueness of the
  normalized Hauptmodul on `X₆` needed for H-43 is proved from the kernel's `MobiusGlue` (which image-plane
  proved from T5). `CoarseFactor` itself (descent along the finite forgetful map) is not proved (§4.3).
* **(c) `ThetaFourthRatiosAlgebraic`: no further Lean reduction over the present definitions** (§5): it is a
  composite of published results (algebraicity of Riemann forms and `NS(A_ℚ̄) = NS(A_ℂ)`; Shimura's algebraicity
  of theta-null ratios at points defined over `ℚ̄`), and the project's `PkgI3.AbVar` has no polarization object
  through which the two parts could be stated separately. Recommendation in §5.

## 2. (a) `ThetaQuotientValue24`

### 2.1 Statement and what is proved

The glue (qm-split `Haupt.lean` l.2287, copied verbatim with `HDec.PkgI1` from `LPrefix.lean` l.227-363 and
`HM.mu`): for `γ ∈ GL₂(ℝ)` with matrix `ι(μ)`, `μ = 2j + ij`, and `τ ∈ ℍ` with `γτ = τ`:
`jDen(Ω(τ)) ≠ 0 ∧ jNum(Ω(τ))/jDen(Ω(τ)) = −16/27`.

| theorem | content |
|---|---|
| `iota_mu`, `det_iota_mu` | `ι(μ) = [[0, −6−3√2], [2−√2, 0]]`, determinant 6 |
| `fixedPoint_eq` | `γτ = τ` forces `τ = i(√6+√3)`; `(√6+√3)² = 9 + 6√2` |
| `Emat_eq`, `F0mat_eq` | closed forms of the two period blocks of §4 of `PkgI1` |
| `omega_tau24` | `Ω(i(√6+√3)) = Ω₂₄` (exact, entries in `ℚ(√−6)`) |
| `gammaMu_fix` | `τ₂₄` is fixed by `γ_μ` (so the glue is not vacuous) |
| `thetaQuotientValue24_iff` | glue `↔ ThetaValueAtOmega24` |
| `thetaQuotientValue24_of_igusa`, `igusa_of_thetaQuotientValue24` | glue `↔` LEAF `IgusaCMValue24` |

### 2.2 Numerics (VERIFIED, `scratch/qm-glue/py/value24.py`, pure-Python double precision)

From the Lean definitions (theta series truncated at `|n_i| ≤ 10`): `j_θ(τ₂₄) = −0.5925925925925931`
(`−16/27 + 6·10⁻¹⁶`), `Ω(τ₂₄)` agrees with `Ω₂₄`, and the ten `|θ_m(Ω₂₄)|` come in five equal pairs (the
principally polarized surface has an extra involution at the elliptic point of order 2, as expected:
`A_τ ≅ A_{wτ}` with `wτ = τ`). Also `jNum = 0` at `√2 + i` (disc −4) and `jDen = 0` at `i√3` (disc −3).

### 2.3 Why the value is not computed in Lean (SPECULATIVE judgement, with reasons)

`j_θ` is a Hauptmodul of `Γ*\ℍ` (proved from the valence formula by qm-split) with zero at the disc −4 point
and pole at the disc −3 point; any such function is `c·s` for the normalized Hauptmodul `s`, so the value at
the third elliptic point is exactly the normalization constant `c`: no symmetry fixes it (unlike `j_θ = 0`
and `∞`, which come from a product polarization and a theta-null sum vanishing). An exact proof needs CM
theory: `A_{τ₂₄}` is isogenous to `E × E` with `E` CM by `ℚ(√−6)` (class number 2), and `−16/27` is an
algebraic identity among theta constants at a CM point (equivalently Baba–Granath's normalization of the
Igusa invariants along the QM curve). Interval arithmetic gives `|j_θ(τ₂₄) + 16/27| < ε`, never the equality,
unless combined with an arithmetic input (e.g. rationality with bounded denominator) that is not printed in
that form. The reduction to an explicit `Ω₂₄` makes the leaf a closed numeric statement about ten theta
series at one matrix in `M₂(ℚ(√−6))`.

## 3. (b) `GammaStarFromO1` proved

Statement (qm-split `Valence.lean` l.177): `ShimizuCovolumeO1 → GammaStarCocompactArea`, i.e. if
`Γ¹ = {γ : matrix ι(x), x ∈ 𝒪, det = 1}` is cocompact Fuchsian with a fundamental domain `s` of area `2π/3`,
then `Γ* = ι(N_B(𝒪)⁺)` is cocompact Fuchsian with a fundamental domain of area `π/6`. All definitions are the
genuine ones of qm-split (`IsCocompactFuchsian`: group, positive determinant, proper discontinuity of the
Möbius maps on compacts, a compact set meeting every orbit; `IsFundDomain`: measurable, meets every orbit,
almost disjoint from its translates by the nontrivial Möbius maps, Mathlib's invariant measure on `ℍ`).

Proof (`GammaStar.lean`, ~1450 lines with the verbatim copies; 16 s after import):

1. **Algebra.** `cover`: every `γ ∈ Γ*` has matrix `ι(q·rᵢ·u)` with `q ∈ ℚ^×`, `rᵢ ∈ {1, x₄, x₆, x₄x₆}`
   (`x₄ = 1+i+j`, `x₆ = (j−3)/2`, norms `1, 2, 3, 6`), `u ∈ 𝒪`, `nrd u = 1`. By induction over the generators
   of `GammaStarGen` (proved by leafq-check; its proof is copied verbatim, qm-split `Haupt.lean` l.20-463), with
   a 16-entry multiplication table `g·rᵢ = r·r_k·u` for `g ∈ {x₄, x₆, x₄⁻¹, x₆⁻¹}` (computed by
   `py/table.py`, emitted by `py/gen_table.py`, each entry checked in Lean). `coset_eq`: the four classes are
   distinct modulo `ℚ^×Γ¹` (a Möbius identity `rⱼ = rᵢh` forces a rational scalar, so `nrd(rᵢ)nrd(rⱼ)` would be
   a square). `conj_g4`: `rᵢΓ¹rᵢ⁻¹ ⊆ Γ¹`. Group laws of `Γ*`.
2. **Cocompact Fuchsian** (`gs_fuchsian`): `γ = rᵢh`, so the Möbius maps of `Γ*` moving `K` to meet itself are
   `rᵢ∘h` with `h(Kᵢ) ∩ Kᵢ ≠ ∅`, `Kᵢ = K ∪ rᵢ⁻¹K` compact: finitely many. Same compact set as `Γ¹`.
3. **Fundamental domain** (`tdom_fund`): `t₀ = {z ∈ s : z ≤_lex γz whenever γ ∈ Γ*, γz ∈ s}` (countable
   intersection; `Γ*` is countable as `B` is), `N` = points whose `Γ*`-orbit misses `t₀`, `t = t₀ ∪ N`.
   `N ⊆ Bad` (off `Bad`, the orbit of `z` meets `s` in at most one point per coset, so finitely many, and the
   lexicographic minimum lies in `t₀`), `Bad` is a countable union of translates of the null sets
   `s ∩ h⁻¹s`. `t₀ ∩ γ⁻¹t₀ ⊆ Fix γ`, finite for a nontrivial Möbius map (`fix_finite`, roots of
   `cz² + (d−a)z − b`), and points are null (`NullSingletonClass` for the measure on `ℍ`, proved).
4. **Area** (`Fdom_fund`, `Fdom_volume`): `F = ⋃ᵢ rᵢ⁻¹t` is a fundamental domain (Mathlib's
   `IsFundamentalDomain`) of the Möbius group of `Γ¹` (as a subgroup of `Perm ℍ`, with the measurability and
   invariance instances proved), so `vol s = vol F` (`IsFundamentalDomain.measure_eq`) and `vol F = 4 vol t`
   (the four pieces are pairwise a.e. disjoint by `coset_eq`). Hence `vol t = π/6`.

So the index-4 covolume transfer and the fundamental-domain comparison are project glue now closed. What
remains for H-87/H-88 is published: the valence formula for a cocompact Fuchsian group (Shimura 1971
Prop. 2.16/Thm 2.20; Rankin Thm 4.1.4) and Shimizu's covolume of `𝒪¹` (Shimura 1971 Prop. 9.2, Shimizu 1965;
Voight Thm 39.1.13), all UNVERIFIED locators, plus `r4` (Igusa) and `IgusaCMValue24` for H-88.

## 4. (d) The coarse-witness comparison (rows H-1, H-43, H-59)

### 4.1 What qm-split left

qm-split split the moduli rows into universal Props over witnesses ("for every witness of `R1fpProps` /
`X6Props`, the published clause holds"), noting that this needs a comparison of witnesses: for fine witnesses
the comparison isomorphism `compare_iso` is compiled; for coarse witnesses (`X₆`) a comparison was missing.

### 4.2 Results (`ModuliCompare.lean` = qm-split's `ModuliSplit.lean` verbatim + additions; 44 s)

| new Prop / theorem | kind | content |
|---|---|---|
| `CoarseFactor` | GLUE (project, AG) | two coarse witnesses `(X, Ψ, fY)`, `(X', Ψ', fY')` over one fine `(Y, Φ)` admit `h : X → X'` with `Ψ'(x ≫ h) = Ψ x` |
| `ModelGlue.CurveBijIso` | proved by curve-split (`CurveSplit.curveBijIso`, no hypothesis) | copied verbatim from `scratch/curve-split/CurveBij.lean` |
| `coarseCompare_of : CoarseFactor → CurveBijIso → CoarseCompare` | proved | `h` is bijective on `ℚ̄`-points (`Ψ'⁻¹ ∘ Ψ`), both curves proper smooth of dimension 1 |
| `x6Props_transport` | proved | `X6Props` along a fine comparison isomorphism |
| `CanonicalCoarseX6`, `BabaGranathX6`, `GonzalezRotgerX6`, `ConicCanonical`, `ConnectedCanonical` | LEAF-forms (existential: the published statement about one witness, the canonical model) | Shimura/Deligne + SGA 1 quotient; Baba–Granath Thm 2.1; González–Rotger Thm 5.12; Kurihara/Elkies; Deligne `π₀` |
| `coarseX6OfFine_of : CanonicalCoarseX6 → CoarseX6OfFine` | proved | only `compare_iso` needed |
| `hauptmodulOfX6_of : BabaGranathX6 → CoarseCompare → HauptmodulOfX6` | proved | `π₆ := π₀ ∘ k` (`ToP1.comp`) |
| `residueOfX6_of : GonzalezRotgerX6 → CoarseCompare → ResidueOfX6` | proved | residue fields unchanged along isomorphisms (chain's `residueImage_comp_iso`) |
| `HauptmodulUniqueX6S` and `hauptmodulUniqueX6S_of : Pin.MobiusGlue → HauptmodulUniqueX6S` | proved from the kernel's `MobiusGlue` | two Hauptmoduln on `X₆` with the R2 clauses agree on `ℚ̄`-points (pull back to `Y` along `fY`, onto `X(ℚ̄)` by `X6Surj`) |
| `conicOfWitness_of' : ConicCanonical → CoarseCompare → HauptmodulUniqueX6S → ConicOfWitness` | proved | |
| `connectedOfFine_of_canonical : ConnectedCanonical → ConnectedOfFine` | proved | `compare_iso` + homeomorphism |
| `r1r2fpRep_of_canonical` (H-1) | proved | from `CanonicalModelY3`, `CanonicalCoarseX6`, `BabaGranathX6`, `GonzalezRotgerX6`, `ReciprocityOfFine`, `CoarseFactor`, `CurveBijIso` |
| `x6ConicModel_of_canonical'` (H-43) | proved | from `r1r2`, `ConicCanonical`, `CoarseFactor`, `CurveBijIso`, `MobiusGlue` |

`MobiusGlue` here is the chain's `LeafQM.AV.Pin.MobiusGlue`, whose text is identical to the kernel's
(`ZInQKernel/HDecomp/QM/Pin.lean`, VERIFIED by diff); image-plane proved it from T5
(`LeafQM.AV.CurveGlue.mobiusGlue_of_t5`). H-59 needs no coarse comparison: its row is already the existential
statement (`ConnectedCanonical` is the row `TSHecke.Y3Connected`).

**Finding.** With the comparison, every per-clause glue Prop of the moduli rows becomes "published statement
about one witness" (existential, the form in which the literature states it) plus one piece of project glue
`CoarseFactor`; the universal Props of qm-split are no longer needed as hypotheses.

### 4.3 What `CoarseFactor` needs (not done)

`fY` is finite and surjective (on `ℚ̄`-points every QM pair has a level-3 structure: `A[3] ≅ 𝒪/3𝒪` as
`𝒪`-modules), `X` is a normal curve, and `fY'` is constant on the fibres of `fY` on `ℚ̄`-points (both are the
forgetful map). In characteristic 0 a morphism constant on the fibres of a finite surjective morphism onto a
normal variety factors through it (`X = Y/G` with `G` the deck group; SGA 1 Exp. V Prop. 1.8, Mumford
*Abelian varieties* §7; UNVERIFIED locators). Equivalently: `K(X') ⊆ K(X)` inside `K(Y)` (an element of `K(Y)`
constant on generic fibres of `fY` is invariant under the Galois closure) and a rational map from a smooth curve
to a proper curve extends. Algebraic geometry of curves; not attempted.

## 5. (c) `ThetaFourthRatiosAlgebraic` (row H-44): analysis

Statement (qm-split `ThetaRatios.lean`): for an abelian surface `A` over a number field, an analytic
uniformization `Φ : ℂ² → A(ℂ)_σ` with kernel `Λ`, any `Ω ∈ 𝔥₂` that is a period matrix of `Λ` and an even
`m₀` with `θ_{m₀}(Ω) ≠ 0`: every `(θ_m(Ω)/θ_{m₀}(Ω))⁴` is algebraic.

Its proof is a composite of two published steps: (1) the principal polarization `(Im Ω)⁻¹` of `ℂ²/Λ` is
algebraic (Appell–Humbert, Lefschetz, GAGA) and defined over `ℚ̄` (`NS(A_ℚ̄) = NS(A_ℂ)`), so `Ω` is a period
matrix of a principally polarized abelian surface over `ℚ̄`; (2) theta-null ratios (here fourth powers) of a
principally polarized abelian variety over `ℚ̄` are algebraic (Shimura, Duke 43 (1976); Faltings–Chai Ch. V;
for genus 2 Thomae's formula and Weil's dichotomy). Over the present definitions the only link between `Ω` and
`A` is the analytic uniformization: `PkgI3.AbVar` carries no polarization or line bundle, so step (2) cannot be
stated as a separate Prop without restating the whole glue, and step (1) cannot be stated at all. **Verdict:**
`ThetaFourthRatiosAlgebraic` is a composite LEAF candidate (a consequence of published results), not reducible
further in Lean today. Recommendation (SPECULATIVE): if a published-form split is wanted, add a polarization
to the abelian-variety layer (an ample class or a polarization isogeny `A → A^∨`), state (1) as
"every Riemann form of `ℂ²/Λ` is the analytic class of a polarization of `A_ℚ̄`" and (2) as Shimura's theorem for
period matrices of polarized `A/ℚ̄`.

## 6. Files and checks

| file | content | check |
|---|---|---|
| `ThetaValue24.lean` | (a) | `lake env lean`, `import Mathlib`, ~10 s after import |
| `GammaStar.lean` | (b) | `lake env lean`, `import Mathlib`, ~16 s after import |
| `HauptGlue.lean` | qm-split `Haupt.lean` verbatim + (a), (b); rows H-87, H-88 from leaves | `chk.sh` (chain), 32 s |
| `ModuliCompare.lean` | qm-split `ModuliSplit.lean` verbatim + (d) | `chk.sh` (chain), 45 s |
| `py/value24.py`, `py/table.py`, `py/gen_table.py`, `py/ocoords.py` | numerics, coset table, structure constants of `𝒪` | `python3` |

`chk.sh` runs `lean` over leaf-fold4's olean chain as compiled by leaf-fold6, copied (with leaf-fold6's kernel
and `z_in_q` oleans) to `~/qmg-olean`; qm-split's `Haupt.lean` and `ModuliSplit.lean` compile unchanged over it
(VERIFIED). Every file ends with `#print axioms` lines: `[propext, Classical.choice, Quot.sound]`.

## 7. Counts and what remains

New LEAF statements (published form; locators UNVERIFIED): `IgusaCMValue24` (Lin–Yang (2),(14) at the
Baba–Granath value; equivalent to the old glue), and the existential forms `CanonicalCoarseX6`,
`BabaGranathX6`, `GonzalezRotgerX6`, `ConicCanonical`, `ConnectedCanonical` (each the published statement about
the canonical model).

Glue closed (proved in Lean): `GammaStarFromO1` (both copies), the five universal moduli Props of qm-split
modulo `CoarseFactor` (`CoarseX6OfFine` outright from its existential form; `HauptmodulOfX6`, `ResidueOfX6`,
`ConicOfWitness` via `CoarseCompare`; `ConnectedOfFine` outright), and the X₆-level Hauptmodul uniqueness from
`MobiusGlue` (T5).

Glue remaining: `CoarseFactor` (§4.3; one statement, AG of curves). `ThetaFourthRatiosAlgebraic` stays a
composite LEAF candidate (§5). `ThetaQuotientValue24` is now a published value (`IgusaCMValue24`), not glue;
an exact Lean computation would need CM theory (§2.3).

Rows after this task: H-87 and H-88 are theorems from published-form leaves only (`ValenceFormulaCocompactEq`,
`ShimizuCovolumeO1`, and for H-88 `r4` and `IgusaCMValue24`); H-1 rests on the existential leaves,
`ReciprocityOfFine`, `CoarseFactor` and `CurveBijIso` (proved by curve-split); H-43 on `r1r2`,
`ConicCanonical`, `CoarseFactor`, `CurveBijIso`, `MobiusGlue` (proved from T5 by image-plane); H-59 is its own
existential leaf; H-44 unchanged (qm-split's split with the composite `ThetaFourthRatiosAlgebraic`).

Integration notes: `GammaStar.lean` and `ThetaValue24.lean` need only Mathlib (self-contained copies of the
definitions); `HauptGlue.lean` and `ModuliCompare.lean` are over leaf-fold4's chain (the constants of qm-split's
rows), so a fold must identify the copied constants as qm-split's report already notes.
