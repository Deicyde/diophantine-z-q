# Integral stages and common-factor comparison


## Shipped edition and a blocker found on re-reading (2026-11-18)

The shipped sources are the files below; they are the checked sources with the trailing `#check` and `#print axioms` lines removed (the printed types and axioms are in `TheoremStatements.md` and the receipts). The JSON manifests mentioned below are not shipped.

- `IntegralLattice.lean`: 10316 bytes, SHA-256 `fc4c2ebf69bc951d7e1cdc2d682231ac385a81b38664c743db6a696c33eb4395`
- `CommonFactor.lean`: 13547 bytes, SHA-256 `4eb8039bcf5ff4880ebdfac610fe770e59bdc482b10e337ae623e9172715d520`
- `GenuineModel.lean`: 19107 bytes, SHA-256 `f12d2c0a9eb9ca34611148eb5fe22cf9e8d2b50869e67c4e0ebe09b385a5b2a1`
- `TorsionObstruction.lean`: 10533 bytes, SHA-256 `0ecc9f3608b45de54f468222ce17ab7caf44a793e105b6c98fdd1bda48616fac`

**Blocker for direct wiring.** `CloudB3RC53/UniformSwitch/Regularity.lean` requires `∃ i, ρ ((stage S).z i) ≠ 0`, while `GenuineModel.lean` retains the actual class rather than a separately chosen primitive kernel vector (the manuscript distinguishes them at tex 4992–4995 and 5145–5152). Minimality and generic nonvanishing do not give primitiveness: the stage `[A —0→ A]` with `z = w = π` has nonzero generic coordinate and residue-fibre dimension one, but its class reduces to zero. A separate primitive-kernel witness or positive-fibre certificate is needed, and the `primitive` field cannot be filled by primitive-kernel existence without changing the retained class. `genuineStage` still accepts an arbitrary closed functional; its identification with the paired functional of the same actual class remains an arithmetic obligation. These results are conditional partial results, not the genuine arithmetic instance of `StageConeComparison`.

The genuine arithmetic instance of `StageConeComparison` remains open. The four source files prove conditional integral realizations and comparison criteria, construct the existing `CoordStep` consumer from a relative common-factor comparison, and prove an algebraic obstruction to replacing that comparison by two separate unit certificates.

All four files passed individual Lean 4.35.0 checks with zero warnings. The checks cover every declared result: 48 theorems and 82 declarations in total. No printed leaf was added. All mathematical hypotheses remain explicit in the theorem types.

## Files and verification

All source paths are relative to the repository:

- `ZInQKernel/Contrib/RC53Assist/StageCone/IntegralLattice.lean` — 11,072 bytes; SHA-256 `dd25b340281c71cd84cc6aebb2877902005814da7183869f1042618fbbff52e4`.
- `ZInQKernel/Contrib/RC53Assist/StageCone/CommonFactor.lean` — 14,639 bytes; SHA-256 `cd98912b035c102c238dece99ef4df383076ae8c3d3d6ac2556a63fdf772177f`.
- `ZInQKernel/Contrib/RC53Assist/StageCone/GenuineModel.lean` — 21,543 bytes; SHA-256 `d21f1fe090e90c44497a5ca7b5d113e104bdb08098eb86756b515f0d60b6e5e1`.
- `ZInQKernel/Contrib/RC53Assist/StageCone/TorsionObstruction.lean` — 11,769 bytes; SHA-256 `91078c9269a2705f1003b53a62eb124e17ff0d0bf91b4a91de35e4cf6c621789`.

The interface edition supplied for this work was commit `6ea158a404343c90a445c129cd0d1f3a0d4b8ddc`. No existing project file was edited, no commit was made, and no dependency build or update was run. Verification used individual-file `lake env lean` invocations with six threads, the prescribed CPU affinity and priority, and a heartbeat limit of 800,000.

[TheoremStatements.md](TheoremStatements.md) contains the exact printed type and exact `#print axioms` output of **every one of the 48 theorems**, including helpers. The complete receipts additionally cover all 82 declarations:

- [IntegralLattice receipt](receipts/IntegralLattice.txt)
- [CommonFactor receipt](receipts/CommonFactor.txt)
- [GenuineModel receipt](receipts/GenuineModel.txt)
- [TorsionObstruction receipt](receipts/TorsionObstruction.txt)

Of the 48 theorems, 47 report `[propext, Classical.choice, Quot.sound]`; `map_vector_ne_zero` reports only `[Quot.sound]`. Across all 82 declarations, 77 report the three standard axioms, three report `[propext, Quot.sound]`, and two report `[Quot.sound]`. Universe annotations in the original outputs are retained in the receipts. The source hashes were unchanged between the pre-check snapshot and the final audit.

[Manifest.json](Manifest.json) records the declaration inventory, source and receipt hashes, sizes, and verification results. [SourceAudit.json](SourceAudit.json) records the 165-module in-tree import closure, its 44,496 source lines, source hashes, and the documentation inputs. Both `StageCone` files and the named realization/duality/model areas were examined; the dependency closure was enumerated rather than inferred from module titles. The documentation audit includes `DAG.md` and all twelve `docs/research/rc-*.md` files.

## What the target actually requires

Let `ι : A → F` be the coefficient-ring map to a field. A stage has an integral square differential `D : A^N → A^N`, integral vectors `z,w`, and a field coordinate `u`, satisfying

\[
D z=0,\qquad wD=0,\qquad \iota(z)\otimes\iota(w)=u\,\operatorname{adj}(\iota(D)).
\]

Here `N = S.n + 1`. These data alone do not identify the complex with any Selmer complex.

A `StageMap` to a plane model `(M,z₀,l₀)` has degree-one and degree-two components `p₁,p₂` with

\[
M p_1=p_2\iota(D),\qquad p_1\iota(z)=z_0,\qquad l_0p_2=\iota(w).
\]

It induces a map of augmented complexes `[F → F^N → F^N → F]`, with class and functional as the outer differentials and identity maps on the two added lines. `coneTorsion` is the torsion of its based augmented cone in the orientation fixed by the existing comparison interface.

Write

\[
s_S=(-1)^{N+1},\qquad T_g=s_S\,\tau(\operatorname{Cone}(\operatorname{aug}(g))).
\]

Then the literal requirement is

\[
\texttt{IntegralUnit}(g)\quad\Longleftrightarrow\quad
\exists c\in A^\times,\ T_g=\iota(c).
\]

In the nondegenerate scope the existing cone identity gives `u_S = u₀ / T_g`. Thus the integral-unit condition says the comparison changes the class-functional determinant coordinate by an integral unit, not merely by a nonzero field scalar.

The old and new plane models are

\[
M_F=\begin{pmatrix}0&0\\\varepsilon v_1&-\varepsilon v_0\end{pmatrix},\qquad
M_S=\begin{pmatrix}\sigma\varepsilon(Jv)_1&-\sigma\varepsilon(Jv)_0\\0&0\end{pmatrix},
\]

with classes `v,Jv` and functionals `e₀*,e₁*`. Their coordinates are `-ε⁻¹` and `(σε)⁻¹`. `StageConeComparison` asks for a `StageMap` to **each** plane and an **individual** `IntegralUnit` certificate for each map. It does not merely ask that the two comparison torsions have a unit ratio.

## Which objects are genuine

The genuine global and local objects are the continuous inhomogeneous cochain complexes `contCochains`, extended from natural degrees to integer degrees by `natCx`. They contain the actual continuous functions from powers of the profinite group to the coefficient module; they are not finite matrices or complexes truncated by declaration.

For actual Galois groups these are assembled by

```text
selCx (galoisSelData K S A M Delta).
```

For finite support this is the continuous-cochain Selmer cone

\[
\operatorname{Cone}\!\left(
C^\bullet_{\rm cont}(G_{K,S},M)\oplus\bigoplus_v U_v
\longrightarrow\bigoplus_v C^\bullet_{\rm cont}(G_{K_v},M)
\right)[-1].
\]

The definitions live in `OneProof/RC/SelmerComplex/{Cochains,Selmer,Galois}.lean`. `OneProof/RC/CoefModules/Selmer.lean` specializes them as `actualSelData` for the actual finite coefficient module `Mcoef` over `Acoef i`. The Selmer cone on that datum is genuine at that finite coefficient stage.

A `TwoTermStage`, a based matrix complex, or a clearing-complex record is not by itself such a realization. A comparison to the specified continuous-cochain cone is required. `ClearingComplex/GenuineIdentification.lean` correctly carries its family comparisons and quasi-isomorphy as fields, rather than deriving them from the sizes of matrices. The earlier degreewise tame-model identifications cannot be used for raw continuous cochains, whose nonnegative-degree terms need not vanish; the appropriate comparison is a quasi-isomorphism.

At derivative primes, the strict condition in the manuscript retains `D⁰`; it is not the zero condition. The relaxed derivative condition omits `D²[-2]`; it is not the full local complex. The genuine condition diagram must retain these distinctions.

## Proved realization and comparison results

The exact universally quantified statements and their axiom outputs are in the theorem inventory. The following explains their construction and use.

### `GenuineModel.lean`

`exists_twoTermRealization_of_boundedFree` constructs a based minimal two-term realization of a **specified** complex `C`, over a local ring `A`, from:

1. a bounded cochain complex `K` of finite free `A`-modules;
2. a quasi-isomorphism `K → C.toCC`;
3. residual cohomology dimensions `n+1,n+1` in degrees one and two, and zero in every other degree.

It uses the already proved `ResidualTransfer.minimalModelsExist_proof`, not an assumed minimal-model leaf. Its conclusion retains `R.n = n` and the minimality condition `d(R) ⊆ 𝔪 R`. The based model is then converted back to relation-indexed differentials, and its map to `C` is proved quasi-isomorphic. This removes the need to supply an already two-term model or its bases, once the weaker bounded presentation and residual data are available.

`cycle_lift_one` and `cycle_lift_two` lift actual cycles through an integral quasi-isomorphism. In degree one they give an integral lift `x` and an actual integral boundary witness `b`, with

\[
dx=0,\qquad f(x)=z+db.
\]

`stageOfRealization` constructs the integral matrix, lifted class, pulled-back functional and generic coordinate. The functional is pulled back without a normalization change. Its rank-one input is exactly `det(ιD)=0` and `adj(ιD)≠0`. `stageOfRealization_class` and `stageOfRealization_functional` prove the retained class and functional identities. `stageOfRealization_ne_zero` derives coordinate nonvanishing from an actual nonboundary class and a functional nonzero on actual degree-two cycles, assuming `ι` injective.

`genuineStage` specializes this constructor to the specified Galois continuous-cochain Selmer cone. It is a conditional construction of that stage; this contribution does not construct the initial bounded presentation or the actual paired functional from the arithmetic parameters.

Finally, `isEmpty_ringHom_acoef_charZero` proves

```text
∀ i, ∀ F [Field F] [CharZero F], IsEmpty (Acoef i →+* F).
```

The reason is `2^i = 0` in the finite coefficient ring. The characteristic-zero stage therefore cannot be obtained by declaring the finite stages to embed into its fraction field. The limit and scalar-change comparison must be constructed.

### `IntegralLattice.lean`

`tau_baseChange` and `torsion_baseChange` prove compatibility with entrywise scalar extension when an integral contraction is supplied. The torsion statement takes domain hypotheses.

`integralUnit_of_contractibleLift` proves the literal `IntegralUnit` predicate from a based integral lift of the augmented comparison cone with an actual integral contraction. The lift identifies, after scalar extension, with the actual based cone used by the interface. This is a sufficient integral certificate; it is not claimed to follow from generic acyclicity.

`exists_stageMap` constructs a generic comparison for every nondegenerate stage when the target row is nonzero and the stated cycle/closed-row equations hold. This comparison is not asserted to preserve the integral lattice.

`stageConeComparison_iff_links` proves, for nonzero old/new coordinates and adjugates, nonzero `ε,σ,v,Jv`, that `StageConeComparison` is equivalent to the conjunction of the two existing `StageModelLink` predicates. It proves comparison existence as well as the equivalence.

`stageConeComparison_of_identification` turns the existing `StageConeIdentification` input into the literal `StageConeComparison` under the same nondegeneracy hypotheses. It can then be passed to the original `coordStep_of_coneComparison` consumer. It is a theorem from an identification input, not a construction of an arithmetic instance of that input.

### `CommonFactor.lean`

`stage_coord_eq_normalized` proves `u_S = u₀ / T_g`, and `integralUnit_iff_normalized` proves the unit-valued characterization above.

`RelativeConeUnit g g'` is the strictly weaker condition

\[
\exists c\in A^\times,\quad T_{g'}=\iota(c)T_g.
\]

`relativeConeUnit_of_commonFactor` proves it from

\[
T_g=\theta\iota(a),\qquad T_{g'}=\theta\iota(b),\qquad a,b\in A^\times.
\]

There is no unit or integrality hypothesis on `θ`. `relativeConeUnit_of_integralUnits` proves that the two stronger individual certificates imply this relative certificate.

`coordStep_of_relativeConeUnit` constructs the **existing** `CoordStep` from this relative condition and the usual nondegenerate plane data: `ε≠0`, `σ²=1`, `J²=1`, `det J=-1`, `v≠0`, and nonzero stage coordinates and adjugates. It retains `ε,σ,J,v`, puts the nonunit factor into the strict volume form, and leaves the two normalization factors integral units. `coordStep_of_commonFactor` supplies the same consumer directly from the two common-factor equalities.

The volume computation is explicit:

\[
u_F=\frac{\mu_F}{\varepsilon\theta},\qquad
u_S=-\frac{\mu_S}{\sigma\varepsilon\theta}.
\]

The common-summand results retain the complete torsion of any generic acyclic strict summand. `planeCoordWithSummand_eq` multiplies the plane coordinate by that summand's torsion; `commonSummand_switch_relation` proves the switch sign relation with the same summand on both sides, without any assertion that its torsion is an integral unit.

### `TorsionObstruction.lean`

This is an algebraic example, **not** a claimed arithmetic Selmer example. For `ι : A ↪ F` and `ι(a)≠0`, append the same disk with differential `a` in degrees one and two to both plane models. The two integral stage matrices are

\[
D_F=\begin{pmatrix}0&0&0\\0&-1&0\\0&0&a\end{pmatrix},\qquad
D_S=\begin{pmatrix}0&-1&0\\0&0&0\\0&0&a\end{pmatrix}.
\]

The classes and functionals are integral and primitive, and the constructed generic comparison maps are nonempty. The stage coordinates are `-(ιa)⁻¹` and `(ιa)⁻¹`.

`oldComparison_torsion` and `newComparison_torsion` prove that **every** corresponding generic comparison to the bare plane has cone torsion `ι(a)`. `oldIntegralUnit_iff` therefore proves that its individual unit certificate is equivalent to `IsUnit a`. `not_stageConeComparison_of_nonunit` disproves the sharpened comparison for a nonunit `a`, while `commonDiskCoordStep` constructs the original coordinate-step consumer with strict volume `ι(a)` and integral unit normalizations.

Thus retaining a common strict factor does not imply that either separate comparison to a bare plane has unit torsion.

## Manuscript check and the exact remaining obligations

The principal manuscript passages are:

- `(4.3)`, lines 3458–3467: the actual Selmer cone and coefficient-valued trace;
- lines 4637–4640: integral unit-disk cancellation and minimal-model ranks;
- `ex:limits-derivative-switch`, lines 4834–4907: the retained derivative conditions and the two strict-to-plane triangles;
- lines 4931–4940 and 4976–4995: reduction to the integral two-term stage and the residual/generic rank data;
- lines 4900–4906 and 5148–5152: the common strict determinant factor, fractional complements when localization is divisible, and retention of all strict torsion.

The common-factor argument in the last two passages is weaker than the two individual unit certificates demanded by the current `StageConeComparison` definition. The algebraic obstruction establishes this distinction without claiming an error in the manuscript.

What remains for the genuine arithmetic target is precisely:

1. **The characteristic-zero realization.** For the actual scalar/limit coefficient ring and coefficient module, construct the bounded finite-free graded presentation `K → selCx(galoisSelData ...).toCC`, prove quasi-isomorphy and the residual support/ranks used by `exists_twoTermRealization_of_boundedFree`, and establish the generic rank-one determinant/adjugate data. The finite `Acoef i` stages cannot substitute for this presentation through an embedding into a characteristic-zero field.
2. **Retained arithmetic data and fibers.** Instantiate the constructor with the actual class and its actual paired functional, prove their nonvanishing hypotheses, and supply the scalar-change/limit and fiber comparisons that identify the model's residual cohomology with the genuine coefficient-specialized Selmer groups. An integral quasi-isomorphism gives the derived tensor model, but does not by itself identify a raw coefficient-specialized continuous-cochain cone. The primitive kernel vector used to choose a detecting prime must not replace the actual class.
3. **The genuine switch determinant comparison.** Construct or identify the old/new plane comparisons from the retained strict/relaxed Selmer diagrams, with the actual localizations `v,Jv` and their paired functionals. Prove that their normalized augmented-cone torsions have the common strict factor up to integral units, i.e. the `RelativeConeUnit` condition. The generic `StageMap` existence theorem alone does not prove this arithmetic determinant comparison. Once this is established, the new constructor supplies the existing `CoordStep`; the remaining family, dimension and detection fields of the switching process still have to be instantiated.
4. **The stronger literal target, if retained.** To obtain `StageConeComparison` itself, establish the additional individual unit conditions. Compatible integral contractible lifts of both augmented cones are sufficient. Equivalently, in the common-factor description the shared factor must also be unit-valued, not just common. This is additional arithmetic content and is not supplied by the cited common-factor paragraphs. Comparing while retaining the common strict factor avoids that extra demand and already suffices for the existing coordinate-step consumer.

No original consumer or identification definition was changed, and none of these remaining inputs was hidden in a new printed proposition.
