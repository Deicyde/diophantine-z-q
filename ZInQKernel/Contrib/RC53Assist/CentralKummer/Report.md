# Central Kummer comparison: input (1) pinned to the genuine objects

## Result

Input (1) of `centralSelmerComparisonOfSpecializedModel` (a complex `K` of `ℚ₂`-vector spaces, a
cochain map `i : K ⟶ CU ⊗_A ℚ₂` with `[QuasiIsoAt i 1]`, and `CU.d 0 1 = 0`) is now stated and
analysed for genuine objects:

* `K₀` is the genuine ordinary rational Kummer complex `rationalKummerComplex S W hFull`: the
  Selmer complex (4.3) of the genuine Galois Selmer data `galoisSelData` over `ℤ₂`, with
  coefficients the `2`-adic Tate module `T₂E = lim E(K_S)[2^n]` and the `2`-adic Kummer condition
  at every place of `S`, tensored with `ℚ₂`. For a base-zero leaf model it is
  `leafKummerComplex M S hFull` (the curve `E_ℓ` over the leaf's field `K = ℚ(√k)`).
* `CU` is the two-term base model `twoTermModel Dm = [A^{m+1} --Dm--> A^{m+1}]` (degrees one and
  two) of the leaf's matrix; `CU.d 0 1 = 0` and the coordinates are proved. For the leaf's own
  model complex, `CU.d 0 1 = 0` follows from a zero degree-zero term.

Main theorems.

1. Over a field, a degree-one quasi-isomorphism `K ⟶ C` exists exactly when
   `H¹(K) ≃ H¹(C)`; every such isomorphism is induced by an explicit cochain map concentrated in
   degree one (`comparisonMap`, `homologyMap_comparisonMap`, `nonempty_quasiIsoAt_one_iff`).
2. Hence input (1) for the genuine `K₀` and the base model holds exactly when
   `H¹(K₀) ≃ ker ρ(Dm)` (`genuine_input_one_iff`, `curve_input_one_iff`, `leaf_input_one_iff`),
   and for finite-dimensional `H¹(K₀)` exactly when the dimensions agree
   (`genuine_input_one_iff_finrank`). The map `i` and its degree-one quasi-isomorphism instance are
   constructed from such an identification (`genuineKummerModelMap`, `KummerInputOne.map`).
3. Given the universal-coefficient and descent data and full Selmer corank one, input (1) is
   equivalent to `rank ρ(Dm) = m` (`input_one_iff_hcentral`, `nonempty_kummerInputOne_iff`); every
   existing leaf model yields pinned input (1) (`nonempty_leafKummerInputOne`); the replacement of
   the field `central` by pinned input (1) is lossless (`KummerInputOne.central_cmp_apply`,
   `KummerInputOne.central_ofCentral`).
4. Properties of the genuine `2`-adic Kummer condition: cocycle identity and continuity;
   independence of the division towers up to continuous coboundaries; additivity up to
   coboundaries; `H⁰` equal to local `H⁰` and `H¹` injecting into local `H¹`; reduction modulo
   `2^n` gives the finite-level Kummer cocycle of the division point, which lies in the
   finite-level Kummer condition; the data are genuine Galois Selmer data for finite `S`;
   `Hⁿ(K₀) ≅ Hⁿ(C_K) ⊗_{ℤ₂} ℚ₂` by flat base change.
5. The finite-level Kummer Selmer complexes cannot serve as `K₀`: there is no ring homomorphism
   `A_i → ℚ₂` (`isEmpty_ringHom_acoef`), and the rationalization `ℚ₂ ⊗_ℤ C` of any complex over a
   ring in which a nonzero integer vanishes is zero (`isZero_integralRationalization_X`). So input
   (1) from the rationalized finite-level Kummer complex `selCx (kummerSelData …)` is refuted
   whenever `rank ρ(Dm) = m` (`finiteLevel_kummer_input_one_refuted`), in particular for every
   base-zero core under full Selmer corank one (`baseZeroCoreText_finiteLevel_refuted`).

## Supplying input (1) of the constructor

`KummerInputOne ℓ K hE Dm` consists of a finite set `S` of finite places, the full `2`-power
torsion hypothesis `hFull` over `K_S`, and `φ : H¹(K₀) ≃ ker ρ(Dm)`. From it,
`KummerInputOne.central k eK j hj f hf` is
`centralSelmerComparisonOfSpecializedModel Dm (twoTermModel Dm) (twoTermModelE1 Dm)
(twoTermModelE2 Dm) (twoTermModel_d_zero_one Dm) (twoTermModel_hd Dm) K₀ I.map eK j hj f hf`,
with the instance `KummerInputOne.quasiIsoAt_map`. For a leaf model `M`, `leafCentral M I eK j hj
f hf` has exactly the type of the field `central` of the leaf's core.

## What remains open

The identification `φ : H¹(K₀) ≃ ker ρ(Dm)` itself; equivalently, when `H¹(K₀)` is
finite-dimensional, `dim H¹(K₀) = dim ker ρ(Dm)`. In the manuscript it is the composite of the
comparison `i : K₀ → R₀` with the central fibre of the actual primitive complex (lines 3952--3962)
and of the identification of the base model with that complex after cancelling unit disks (lines
4353--4360). The leaf's matrix `Dm` is a free field: no primitive complex over `Λ_(t)` and no
identification of `Dm` with it is constructed in the project, so `φ` cannot be derived here. By
theorem 3, `φ` is, in the presence of inputs (2) and (3) and full Selmer corank one, equivalent to
the original field `hcentral`; the gain is that it is now a statement about the genuine rational
Kummer complex rather than a free existential.

## Hypotheses and sources

No printed statement is assumed. The only hypothesis on the arithmetic side is the full `2`-power
torsion of `E_ℓ` over `K_S` (`hFull`), the existing Néron--Ogg--Shafarevich input of the
finite-level Kummer maps; it is a parameter, not a new leaf.

## Verification

Both modules elaborate as single files with exit status zero and no errors or warnings. Every
declaration depends only on `propext`, `Classical.choice` and `Quot.sound`
(`apply_trans_symm_symm` and `tensor_eq_zero_of_divisible_of_torsion` use only `propext` and
`Quot.sound`). The file `CheckOutput.txt` records the elaborated
statements of the main declarations and the axiom report of every declaration. No proof
placeholders, new axioms, evaluation commands, custom notation or syntax, or option changes are
used.
