# Shimura quotient: results log

- VERIFIED (Lean): `ShimuraQuotientHecke.lean` and `HeckeAxioms.lean` compile. The six theorems have only `propext`, `Classical.choice`, `Quot.sound`.
- VERIFIED (Lean): `comp0_tmul` computes rational composition on pure tensors; `hom0Inclusion_injective` uses `hom_nsmul_eq_zero`; `hom0_exists_positive_denominator` and `hom0_nsmul_cancel` give existence and cancellation.
- VERIFIED (Lean): `heckeCompat_iff_rational` is the equivalence in the genuine tensor product; `cleared_hecke_iff` gives it for every positive denominator and numerator representing the same rational endomorphism, hence independence of the pair.
