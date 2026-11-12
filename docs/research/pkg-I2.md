# pkg-I2: the reduction-theory package of Theorem 4.1, as Lean leaves

Status: research note (task pkg-I2, 2026-11-11). Package I2 of `docs/research/wk-h.md` §2
(steps A5, A6, A8, C6, C10, D2 of `docs/research/h-trust.md`). Drafts:
`scratch/pkg-I2/I2.lean` (one file, compiled); log: `scratch/pkg-I2/log.md`. No file under
`ZInQKernel/`, `blueprint/` or other notes was edited.

Marks: **VERIFIED** (read in a source in the repository, computed, or compiled), **STANDARD**
(published, reference given), **SPECULATIVE**. There was no network. Every theorem number below is
from memory or from h-trust/h-b1, and is **UNVERIFIED** unless marked otherwise.

## Summary

1. **Every I2 input that the proof uses can be stated faithfully in Lean today, over genuine
   Mathlib objects (VERIFIED: compiles).** This corrects the I2 row of wk-h §3.2 ("statable: no";
   it named Néron models and Tate modules as missing). Neither object is needed in the
   *statements*:
   - An abelian variety is a group object of `Over (Spec K)` (Mathlib's `Grp`), proper, smooth and
     geometrically integral. Its torsion points are morphisms `Spec K̄ ⟶ A` over `Spec K`, with
     Mathlib's group law on `X ⟶ G` (`MonObj.Hom.group`). The Galois group acts by precomposition.
     Inertia is Mathlib's `ValuationSubring.inertiaSubgroup`.
   - Good reduction is an abelian scheme over the DVR, i.e. a group object of `Over (Spec O)` that
     is proper, smooth and has geometrically connected fibres, whose base change
     (`(Over.pullback _).mapGrp`) is isomorphic to `A` in `Grp (Over (Spec K))`.
   - Tate-module statements are replaced by equivalent statements about the finite levels
     `A(K̄)[ℓⁿ]`.
   - Statements about the special fibre of a Néron model are replaced by their published Galois
     consequences (Grothendieck's criterion SGA 7 IX 3.5). The Néron mapping property is used only
     in the abelian-scheme case.
   - Purity and Abhyankar's lemma are ring-theoretic statements over `IsRegularLocalRing`,
     `Algebra.IsEtaleAt`, `Algebra.IsUnramifiedAt`, `Algebra.QuasiFiniteAt` and
     `Ideal.ramificationIdx`.
2. **Eleven leaf Props compile** (§2; no `sorry`, no `axiom` in any leaf).
3. **Glue proved from the leaves (VERIFIED: compiles; `#print axioms` gives only `propext`,
   `Classical.choice`, `Quot.sound`):**
   - C6/A8: good reduction ⇒ inertia trivial on `A[ℓⁿ]` (from NOS);
   - D2: an inertia element of `p`-power order fixes `A[ℓⁿ]`, under Raynaud's hypothesis (from
     Raynaud's criterion).

   A6 (Lemma PR(ii)) is stated over the leaves with a full outline. Its body is `sorry`.
4. **A simpler route for A6 (SPECULATIVE until formalized; argument in §4.2).** The good reduction
   of the QM surface at `v ∤ 3` follows from three inputs: Raynaud's criterion at `m = 3`,
   Néron–Ogg–Shafarevich, and the structure of `A[3ⁿ]`. The proof uses that `B ⊗ ℚ₃` is a division
   algebra. This route drops three inputs that h-b1 uses for A6:
   - SGA 7 IX 3.6 (semistable reduction theorem);
   - the toric-part argument with the general Néron mapping property (Morita);
   - Serre–Tate Thm 2.

   Raynaud's criterion is already needed for D2, so the package shrinks to **six core leaves**:
   purity, Abhyankar, NOS, Raynaud, the Néron property for abelian schemes, and reduction of
   prime-to-`p` torsion. Three Mumford leaves sit on the boundary with I3.
5. **Strict henselization (A5) is avoidable in Lean (SPECULATIVE).** Prop. TS of h-b1 uses
   `R = ℤ_(p)^{sh}`, which Mathlib lacks. Any strictly henselian DVR unramified over `ℤ_(p)` does the
   same job. Mathlib has `𝕎(𝔽̄_p)`: `WittVector.isDiscreteValuationRing` and `IsAdicComplete` (p-adic
   completeness) (VERIFIED by grep).
6. **Biggest obstacle (§6).** The leaves are not the problem; the glue is.
   - A5's glue (Prop. TS, Lemma NV) sits on I1 (the cover `Y₃ → P¹_j`, the canonical model,
     Shimura reciprocity), which cannot be stated.
   - The glue for A6, C10 and A8 needs an API that Mathlib lacks for points of group schemes:
     finiteness of torsion, `T_ℓ` as a `ℤ_ℓ`-module, continuity of the Galois action, Frobenius
     morphisms, and Weil restriction (A8).
   - Formalizing the leaves themselves is a multi-year project (Néron models, SGA 7).

## 1. Where I2 enters the proof

| Step | N5 lines | What is used | I2 leaves (§2) | Other inputs |
| --- | --- | --- | --- | --- |
| A5 (Lemma PR(i)) | 443-528 (replaced by h-b1 §§1.2-4) | Prop. TS (tame specialization) and Lemma NV (no vertical ramification) | I2-P, I2-AbDVR (or I2-AbSGA) | I1: `Y₃ → P¹_j` over ℚ with group of order dividing 144, branch data, Shimura reciprocity at CM points; scripts of h-b1 |
| A6 (Lemma PR(ii)) | 529-530; reused 556-559, 752-754, 781, 849-850 | good reduction of `A` and its conjugates at `v ∤ 3` | Raynaud route: I2-Ray, I2-NOS, I2-Tors. h-b1 route: I2-SS, Néron model of `A` (not statable), I2-ST2, I2-NOS | I1/A4: `A[3] ⊂ A(K)`, `ι: 𝒪 → End_K(A)` |
| A8 | 544-563 | Hom field `L` unramified outside `T` | I2-NOS (⇒), I2-Rank | Weil restriction `Res_{K/ℚ} A` (absent from Mathlib); Minkowski's lemma |
| C6 | 752-754 | `r_ℓ` unramified outside `T ∪ {ℓ}` | I2-NOS (⇒) | A5, A6, A8, B3 |
| C10 | 776-795 | reduction of `μ_σ`; Frobenius; independence of `ℓ` | I2-NMP, I2-Red, I2-Char | Chebotarev, Brauer–Nesbitt (I6); Faltings Satz 3 for `A_f` (I3) |
| D2 | 813-823 | semistability over `F = L_v(A[3])` (`A[5]` at `p = 3`); wild inertia trivial on `V_ℓ` | I2-Ray | wild inertia is pro-`p` (Serre, *Corps locaux* IV §2; I6) |

The N5 line numbers are those of h-trust and h-b1 (VERIFIED by reading N5 L540-563 and L745-830
in this task).

## 2. The leaves

Common definitions (in `scratch/pkg-I2/I2.lean` §2; all VERIFIED to compile):

- `specOver K L`, i.e. `Spec L` over `Spec K`;
- `IsAbelianVariety A` (proper, smooth, geometrically integral `A : Grp (Over (Spec K))`);
- `IsAbelianScheme 𝒜` (proper, smooth, geometrically connected, `𝒜 : Grp (Over (Spec O))`; Mumford,
  GIT, Def. 6.1);
- `Pts A L := specOver K L ⟶ A.X` and `torsion A L m := {x | x ^ m = 1}`;
- `galAct A σ x := galHom σ ≫ x`, the action of `σ ∈ Aut(L/K)` on points (it acts on coordinates
  by `σ ∘ x^*`);
- `IsInertia w σ` (Mathlib's inertia subgroup of the valuation ring `w ⊂ K̄`);
- `HasGoodReduction A O`;
- `InertiaTrivialOn A w m`;
- `UnipSq A σ x`, which says `(σ − 1)² x = 0`, written multiplicatively;
- `baseChange`, `toW`, `IsReductionOf`.

In every leaf, `K` is a field, `O ⊂ K` is a valuation subring that is a DVR, and `w` is a
valuation subring of `K̄ = AlgebraicClosure K` with `w ∩ K = O`. The residue characteristic `p` is
expressed as "`m` invertible in `O`".

### I2-P. Zariski–Nagata purity of the branch locus (`PurityBranchLocus`)

- **Published statement.** SGA 1, Exp. X, Thm 3.4 ("théorème de pureté"; Thm 3.1 per h-b1; number
  UNVERIFIED). Stacks Tag 0BMB (from memory, consistent with the prereq-survey's record of Axiom's
  `etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne`): let `f: X → Y` be a morphism of
  locally Noetherian schemes, `x ↦ y`, with
  - `O_{X,x}` normal and `O_{Y,y}` regular;
  - `f` quasi-finite at `x`;
  - `dim O_{X,x} = dim O_{Y,y} ≥ 1`;
  - `f` unramified at every generization `x'` of `x` with `dim O_{X,x'} = 1`.

  Then `f` is étale at `x`.
- **Used in.** A5, Prop. TS (h-b1 §1.2: étale off `D`), and the reduction of Abhyankar's lemma
  to its DVR form (§3).
- **Leaf.** The ring form: `R → S` of finite type, `R` Noetherian, `q ⊂ S` prime. Assume:
  - `R_{q∩R}` is regular, `S_q` is a normal domain, and `S` is quasi-finite at `q`;
  - the dimensions are equal and `≥ 1`;
  - `S` is unramified over `R` at every prime `q' ⊆ q` of height 1.

  Then `S` is étale over `R` at `q`. This is the special case `X = Spec S`, `Y = Spec R`, so it is
  a consequence.
- **Faithfulness (VERIFIED by reading the Mathlib docstrings).**
  - `Algebra.IsEtaleAt R q` means `S_q` is formally étale over `R`. For `S` finitely presented
    (here: finite type over Noetherian) this is étaleness at `q`.
  - `Algebra.QuasiFiniteAt R q` means `S_q` is quasi-finite over `R`. For finite type this is
    "`q` isolated in its fibre".
  - `Algebra.IsUnramifiedAt` means `S_{q'}` is formally unramified.
- **Exists in Lean.** Proved in Axiom's StacksFrontier (unreviewed), and in Tau Ceti for
  dimension ≤ 2 (prereq-survey, A5 row). Matching their statements to this Prop is a citation
  task. They are built on other bases.

### I2-AbDVR. Abhyankar's lemma for DVRs (`AbhyankarDVR`)

- **Published statement.** SGA 1, Exp. X, Lemme 3.6 (UNVERIFIED). Also: Stichtenoth, *Algebraic
  function fields and codes*, Thm 3.9.1 (function fields; Tau Ceti has
  `TauCeti.Place.ramificationIdx_restrict_sup`). Let `R` be a DVR with fraction field `K` and
  uniformizer `π`, and `L/K` finite separable and tamely ramified over `R`. Let `n` be invertible
  in `R` and divisible by every ramification index. Then `L·K(π^{1/n})` is unramified over
  `K(π^{1/n})` above `R`.
- **Leaf.** `S` is the integral closure of `R` in `L`. Every prime `Q ⊂ S` over `𝔪_R` has the
  following properties:
  - `e(Q)` is invertible in `R`;
  - `e(Q) ∣ n`;
  - `S/Q` is separable over `R/𝔪`.

  Let `M = L(t)` with `tⁿ = π`. Then every prime of the integral closure of `R` in `M` over `𝔪_R`
  has ramification index exactly `n` and a separable residue extension. This is equivalent to the
  published conclusion, since `K(t)/K` is totally ramified of degree `n` (Eisenstein).
- **Lean objects.**
  - `Ideal.ramificationIdx` is the new length definition, which agrees with the usual one for
    Dedekind domains (Mathlib docstring).
  - `Ideal.LiesOver`, `integralClosure`, `IntermediateField.adjoin` and `Algebra.IsSeparable`.
  - All exist.

### I2-AbSGA. Abhyankar's lemma, SGA form (not drafted; glue from I2-P and I2-AbDVR)

- **Published statement.** SGA 1, Exp. XIII, 5.2-5.3 (h-trust: 5.3; UNVERIFIED); Grothendieck–Murre,
  LNM 208. Set-up:
  - `X = Spec A`, with `A` a regular local ring;
  - `D = ∑ div(fᵢ)`, with `f₁, …, f_r` part of a regular system of parameters;
  - `V` finite étale over `X − D` and tamely ramified along `D`;
  - `nᵢ` invertible, divisible by the ramification indices;
  - `A' = A[Tᵢ]/(Tᵢ^{nᵢ} − fᵢ)`.

  Conclusion: `V ×_X Spec A'` extends to a finite étale `A'`-scheme. Over a strictly henselian `A`,
  this gives h-b1's étale-local Kummer structure.
- **Reduction to the two drafted leaves (SPECULATIVE; I believe this is SGA's own proof, not
  checked).** Let `C` be the normalization of `A'` in `V ⊗ Frac A'`.
  1. `C` is finite over `A'`: the extension is separable.
  2. `A'` is regular local, and the height-one primes containing `∏ fᵢ` are the `(Tᵢ)`.
  3. At `(Tᵢ)`, apply I2-AbDVR over the DVR `A_{(fᵢ)}`. Adjoining `f_j^{1/n_j}` for `j ≠ i` is
     unramified there: a Kummer extension of a unit, with `n_j` invertible.
  4. So `C` is étale in codimension one, and I2-P makes it étale.
- **Status.** Drafting it as a separate leaf is optional. h-b1 Lemma NV step 3 uses the
  two-branch case (`z` and `p`) in dimension 2.

### I2-NOS. Néron–Ogg–Shafarevich (`NeronOggShafarevich`)

- **Published statement.** Serre–Tate, *Good reduction of abelian varieties*, Ann. of Math. 88
  (1968), Thm 1 (UNVERIFIED locator; the statement is classical). For `K` with a discrete
  valuation and `A/K` an abelian variety, the following are equivalent:
  - (a) `A` has good reduction;
  - (b) `A_m` is unramified for all `m` prime to `p`;
  - (c) the same holds for infinitely many such `m`;
  - (d) `T_ℓ A` is unramified for some `ℓ ≠ p`.
- **Leaf.** (a) ⟺ (b), and (a) ⟺ (c). Here "unramified" means `InertiaTrivialOn A w m`. (d) is
  (c) with `m = ℓⁿ`.
- **Faithfulness.**
  - Serre–Tate work with `K_s` and allow any discretely valued `K`, complete or not. Here
    `K̄ = AlgebraicClosure K`. For `m` invertible in `O`, `A(K̄)[m] = A(K_s)[m]` and
    `Aut(K̄/K) = Gal(K_s/K)`, so nothing changes (STANDARD).
  - "Abelian scheme" includes geometrically connected fibres, as in Serre–Tate §1.
- **Used in.** A6 ((c) ⇒ (a)), and A8, C6 ((a) ⇒ (b)). The glue `inertiaTrivial_of_goodReduction`
  is proved.

### I2-ST2. Potential good reduction (`SerreTatePotentialGood`; h-b1 route for A6 only)

- **Published statement.** Serre–Tate 1968, Thm 2 (UNVERIFIED): `A` has potentially good reduction
  iff the image of inertia in `Aut(T_ℓ A)` is finite.
- **Leaf.** For a prime `ℓ` invertible in `O`, two conditions are equivalent:
  - there is a finite `K' ⊂ K̄` such that `A_{K'}` has good reduction at `w ∩ K'`;
  - there is a finite `K'` such that the inertia elements fixing `K'` act trivially on every
    `A(K̄)[ℓⁿ]`.

  The second condition says that the kernel is open in `I`, i.e. the image is finite.

### I2-SS. Grothendieck's semistable reduction, monodromy form (`GrothendieckMonodromy`; h-b1 route only)

- **Published statements.**
  - SGA 7 I, Exp. IX, Thm 3.6: `A` acquires semistable reduction over a finite extension.
  - SGA 7 I, Exp. IX, Prop. 3.5, direction ⇒: semistable reduction implies that inertia acts on
    `T_ℓ` unipotently of echelon ≤ 2.
  - Numbers from h-trust and h-b1, UNVERIFIED.
- **Leaf (consequence of the two).** There is a finite `K' ⊂ K̄` such that every inertia element
  fixing `K'` satisfies `(σ − 1)² = 0` on every `A(K̄)[ℓⁿ]` with `ℓ` invertible in `O`.
  - The finite-level form is equivalent to `(σ − 1)² = 0` on `T_ℓ`, because `T_ℓ → A[ℓⁿ]` is onto
    (`A(K̄)` is divisible).
  - Semistable reduction itself is a property of the Néron model, which cannot be stated. Only
    this Galois form is used.

### I2-Ray. Raynaud's criterion, Galois form (`RaynaudCriterion`)

- **Published statements.**
  - SGA 7 I, Exp. IX, Prop. 4.7 (UNVERIFIED): if `m ≥ 3` is prime to `p` and the points of `A[m]`
    are rational over `K`, then `A` has semistable reduction. Also Silverberg–Zarhin, Ann. Inst.
    Fourier 45 (1995), Thm 3.5, `n ≥ 3` (ASTRA-READ per h-trust D2).
  - Combined with SGA 7 IX 3.5 (⇒).
- **Leaf.** Under that hypothesis, every inertia element `σ` satisfies `(σ − 1)² = 0` on every
  `A(K̄)[ℓⁿ]`, `ℓ` invertible in `O`.
- **Used in.** D2 at `F = L_v(A[3])` (`A[5]` at `p = 3`). In the Lean formulation `F` is the
  number field `L(A[3])` with `w ∩ F`; the completion is not needed. A6 also uses it on the
  Raynaud route (§4.2). The glue `D2_fixed_of_raynaud` is proved.

### I2-NMP. Néron mapping property, abelian-scheme case (`NeronMappingAbelianScheme`)

- **Published statement.** Bosch–Lütkebohmert–Raynaud, *Néron models* (1990), §1.2, Def. 1 and
  Prop. 8 (UNVERIFIED): an abelian scheme over a DVR is the Néron model of its generic fibre.
- **Leaf (consequence).** For abelian schemes `𝒜, ℬ` over the DVR `O`, restriction to the generic
  fibre `Hom_O(𝒜, ℬ) → Hom_K(𝒜_K, ℬ_K)` is a bijection. The Néron property is applied with
  `Y_R = 𝒜`, which is smooth.
- **Used in.** C10: the isogeny `μ_σ` between `σA` and `A` extends to the good-reduction models
  (A6 for both) and reduces mod `v`.
- **Not statable.** The general Néron mapping property for a Néron model that is not an abelian
  scheme. Only h-b1's toric-part argument for A6 uses it, and the Raynaud route avoids that
  argument.

### I2-Red. Reduction of prime-to-`p` torsion (`ReductionTorsionBijective`)

- **Published statement.** Serre–Tate 1968, §1, in the proof of Thm 1, (a) ⇒ (b) (UNVERIFIED): at
  good reduction, reduction `A_m → Ã_m` is an isomorphism for `m` prime to `p`.
- **Leaf.** `IsReductionOf 𝒜 e w hw x y` holds iff some `x̃ ∈ 𝒜(w)` restricts to `x` at the
  generic point (through `e: 𝒜_K ≅ A`) and to `y ∈ 𝒜(κ(w))` at the closed point. On `m`-torsion
  this relation is the graph of a bijection.
- **Used in.** C10: the comparison `V_ℓ(A) ≅ V_ℓ(Ā_v)` under which `σ` acts as Frobenius. The
  equivariance follows from the definition by naturality (glue).

### Boundary leaves (Mumford, *Abelian varieties*, 1970; locators UNVERIFIED)

These are drafted because the I2 glue needs them. They may belong to I3.

- **I2-Tors (`TorsionStructure`), §4, Application 2 / §6.**
  `A(K̄)[n] ≅ (ℤ/n)^{2g}` for `n` invertible in `K`. The dimension is
  `topologicalKrullDim A.X.left`.
- **I2-Char (`CharpolyIndependentOfEll`), §19, Thm 4.** For `φ ∈ End(B)` there is a monic
  `P ∈ ℤ[X]` of degree `2g` that is the characteristic polynomial of `φ` on `B(k̄)[ℓⁿ]` in every
  `ℤ/ℓⁿ`-basis, for every `ℓ ≠ char k` and every `n`. C10 needs this.
- **I2-Rank (`HomRankBound`), §19, Thm 3.** Any `4gg' + 1` homomorphisms `A → B` are `ℤ`-dependent.
  A8 needs this.

## 3. What exists in Lean

| Object | Mathlib v4.35.0 (VERIFIED by grep of `.lake/packages/mathlib`) | Other libraries (prereq-survey) |
| --- | --- | --- |
| group schemes, base change of group objects | `Grp (Over X)`, `GrpObj`, `(Over.pullback f).mapGrp`, `CartesianMonoidalCategory (Over S)` for schemes (`AlgebraicGeometry/Pullbacks.lean`) | — |
| abelian varieties | the four morphism classes; commutativity theorem `isCommMonObj_of_isProper_of_geometricallyIntegral` | Tau Ceti `AbelianVariety` (definitions, rigidity) |
| points and Galois action | `MonObj.Hom.group`, `comp_mul`, `comp_inv`, `comp_pow` (so `galAct σ` is a group hom, proved here) | — |
| inertia | `ValuationSubring.decompositionSubgroup`, `.inertiaSubgroup` (no higher ramification groups) | Tau Ceti upper numbering |
| regular, étale, unramified, quasi-finite at a prime | `IsRegularLocalRing`, `Algebra.IsEtaleAt`, `IsUnramifiedAt`, `QuasiFiniteAt` | Stacks (Axiom): purity, Abhyankar (unreviewed proofs) |
| strictly henselian DVR | no strict henselization; `HenselianLocalRing`; `𝕎 k` is a DVR and `p`-adically complete | — |
| Cohen–Macaulay, miracle flatness | absent (no `IsCohenMacaulay`) | — |
| Néron models, Tate modules, semistable reduction, Frobenius on abelian varieties, Weil restriction | absent | Anthropic FLT: Néron models (special case); Tau Ceti: NOS for elliptic curves |

## 4. Glue

### 4.1 Proved (VERIFIED: compiles; standard axioms only)

- `galAct_mul/inv/pow/one`: the Galois action on points is a group action by homomorphisms.
- `inertiaTrivial_of_goodReduction` (C6, A8): from I2-NOS.
- `fixed_of_unipSq_of_iterate`: in the commutative group of points, `(σ − 1)² x = 0`,
  `ℓⁿ x = 0` and `σ^{pᵃ} x = x` with `gcd(p, ℓ) = 1` give `σ x = x`. Proof: `σ^k x = x + kNx`.
- `D2_fixed_of_raynaud` (D2): from I2-Ray. It remains to apply it to wild inertia. Wild inertia
  is pro-`p`, and the action on a point factors through a finite quotient, because each
  `K̄`-point is defined over a finite extension. Both facts are I6 or elementary glue.

### 4.2 A6 by Raynaud (`goodReduction_of_QM_rational3`, statement compiles, body `sorry`)

Hypotheses:
- `A/K` is an abelian surface;
- `I, J ∈ End_K(A)` satisfy `I² = 2`, `J² = −3` and `IJ = −JI` on `K̄`-points. They come from
  `ι: 𝒪 → End_K(A)` (A4), with `ℤ⟨i, j⟩ ⊂ 𝒪`;
- `A[3]` is rational over `K` (A4);
- `3` is invertible in `O`.

Conclusion: `HasGoodReduction A O`. Proof outline:

1. I2-Ray (`m = ℓ = 3`) gives `N = σ − 1` with `N² = 0` on `A[3ⁿ]`, for `σ ∈ I_w`.
2. Set `Λ = ℤ⟨i, j⟩`.
   - Its reduced discriminant is `24`, so `Λ ⊗ ℤ₃` is the maximal order of the quaternion
     division algebra over `ℚ₃`. `(2, −3)₃ = −1`, since `2` is a non-square unit mod 3.
   - `Λ₃` has uniformizer `Π` with `Π² ∈ 3Λ₃ˣ` and residue field `𝔽₉`.
   - I2-Tors gives `A[3ⁿ] ≅ (ℤ/3ⁿ)⁴`. A finite `Λ₃`-module is `⊕ Λ₃/Π^{aᵢ}`, and the
     cardinality `3^{4n}` with exponent `3ⁿ` forces `A[3ⁿ] ≅ Λ/3ⁿ`, free of rank one.
3. `N` commutes with `I` and `J`, which are defined over `K`. So `N` is right multiplication by
   some `c ∈ Λ/3^{2k}`.
   - `N² = 0` gives `c² ≡ 0`. Since `nrd = x² − 2y² + 3z² − 6w²` is anisotropic mod 3, this forces
     `c ∈ 3ᵏΛ`.
   - Then `N(3ᵏ A[3^{2k}]) = 0`, and `3ᵏ A[3^{2k}] = A[3ᵏ]`.
4. I2-NOS (c) with `m = 3ᵏ`, `k ≥ 1`, gives good reduction.

This applies to every `v ∤ 3`, including `v | 2` (where `ℓ = 3 ≠ p`). h-b1's route uses I2-SS, the
Néron model of `A` with toric-part functoriality (not statable), the general Néron mapping
property, I2-ST2, I2-NOS and the torsion-freeness of `1 + 3M₄(ℤ₃)`. The Raynaud route needs none of
these beyond I2-NOS. Status: SPECULATIVE (my argument, unreviewed). The algebra in step 2
(classifying finite `Λ₃`-modules) is standard (Vignéras II; Reiner, *Maximal orders*, §§12-14;
UNVERIFIED).

### 4.3 Not drafted (described)

- **A5 (Prop. TS and Lemma NV).** Prop. TS is statable over Mathlib: a finite Galois extension of
  `RatFunc ℚ`, primes of integral closures, residue fields, ramification indices. Its proof needs:
  - I2-P, and I2-AbDVR (through I2-AbSGA);
  - a strictly henselian base, e.g. `𝕎(𝔽̄_p)`;
  - finiteness of normalization (separable, so `IsIntegralClosure.isNoetherian`);
  - miracle flatness (Matsumura, Thm 23.1), which Mathlib lacks; it is used for going-down in
    Lemma NV step 3.

  Lemma NV also needs I1: Shimura reciprocity at the CM points and the `W`-cover `X₆ → P¹_j`.
  A5 therefore cannot be completed without I1, but its I2 part is fully specified.
- **A8.** I2-NOS (⇒) and I2-Rank on `W₀ = Res_{K/ℚ} A`. Mathlib has no Weil restriction.
  Alternative (SPECULATIVE): work with the conjugates `σA` and the group `⊕ Hom(σA, τA)` directly.
- **C10.** Needs four ingredients beyond the leaves:
  - I2-NMP, to reduce `μ_σ`;
  - the relative Frobenius of `Ā_v` (Mathlib has no Frobenius morphism API for abelian varieties
    in this form);
  - I2-Char, for independence of `ℓ`;
  - I2-Red, for the `G`-equivariant comparison.

  Then Chebotarev and Brauer–Nesbitt (I6).

## 5. Faithfulness and vacuity

- Every leaf is a `def … : Prop` over Mathlib definitions. No structure was invented: the
  classes `IsAbelianVariety` and `IsAbelianScheme` are conjunctions of Mathlib morphism classes.
- Each leaf is the published statement, or a consequence of one or two published statements.
  The finite-level forms are equivalent to the `T_ℓ` forms through standard facts (divisibility
  of `A(K̄)`).
- **Not checked in Lean: non-vacuity.** No instance of `IsAbelianVariety` with positive dimension
  is constructed. Mathlib has no elliptic curve as a group object in `Over (Spec K)`. The
  definitions are the standard ones, so non-vacuity rests on reading. A cheap next check is that
  the trivial group `Over.mk (𝟙 (Spec K))` satisfies `IsAbelianVariety`.
- The hypotheses `[IsCommMonObj B.X]` in I2-Rank, and `[IsDiscreteValuationRing O]` throughout,
  are true or intended. The first is a Mathlib theorem for abelian varieties.

## 6. Biggest obstacle

The statements are done. Using them is what is hard.

1. **A5 depends on I1.** The I2 leaves are only applied to the cover `Y₃ → P¹_j`, which needs the
   canonical model of the Shimura curve. That cannot be stated in Lean.
2. **No API for points of group schemes.** Mathlib has the definitions and the group law, but
   none of the following:
   - finiteness of `A(K̄)[m]`;
   - `T_ℓ` as a `ℤ_ℓ`-module;
   - continuity of the Galois action (points defined over finite extensions);
   - the action of `End(A)` as a ring;
   - Frobenius;
   - Weil restriction.

   Every glue proof beyond C6 and D2 needs some of these (A6: about 1-2k lines, SPECULATIVE).
3. **Formalizing the leaves themselves.** NOS, Raynaud and SGA 7 IX need Néron models and the
   theory of semiabelian schemes. That is years of work, comparable to the FLT projects'
   abelian-variety layers.

## Changelog

- 2026-11-11, task pkg-I2: first version.
