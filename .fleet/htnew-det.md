# htnew-det (fleet note)

**Verdict: the determinant argument does not remove `eigenformHTNew`. The field stays; field, GLUE and leaf counts
are unchanged; no new leaf.** The Pan∘Berger twist `ψ` in `G0Galois.g12` is an arbitrary continuous character, and
`g12` derives its finiteness (`twist_finite`) only after `G12Weight`, which reads `r13`, has given `k = 2`. So
"compare det at Frobenius" is circular. The chain's determinant, trace and DS 9.6.5 Frobenius-polynomial identities,
together with `(det r₅)² = χ²` on `G_K` (Weil pairing), are all invariant under
`(k, ψ, a_q) ↦ (k+2m, ψχ^{−m}, q^m a_q)`. These are the Frobenius data of `θ^m f`, a `p`-adic but non-classical
eigenform of weight `2+2m`. Excluding them needs classicality, i.e. the Hodge–Tate weights of `ρ_g` (Kato).

**Compiles** (`ZInQKernel/Contrib/OneProof/HTNewDet.lean`, standard axioms, discharges no field as expected):
- `twist_sq_mul_cyc_finite`: the weight-`k` determinant data give exactly that `ψ²χ^{k−2}` is finite.
- `det_data_weight_shift`, `frobPoly_weight_shift`, `charpoly_smul_fin_two`, `traceTwist_weight_shift` and
  `twist_shift_not_finite`: the data are sharp.
- `NoHighWeightTwist5` is the smallest missing input: GLUE, not printed form (Kato + Sen + Chebotarev/BN). With it,
  `g12Weight_of_noHighWeight` proves `G12Weight` without `r13`. `noHighWeightTwist5_of_g12Weight` shows the current
  route implies it.
- `#discharges` output: `scratch/htnew-det/Discharges-output.txt` (36 open).
- Verbatim `G12Weight` copy checked by `rfl`: `scratch/htnew-det/G12WeightCopy.lean`.

**Remains:** the field. The closest printed-form target is ht-bypass's `EigenformHTNew5Ge3` (Kato at `ℓ = 5`,
`k ≥ 3`). The alternative is ser-ell's strong-Serre route, which avoids Pan∘Berger and `eigenformHTNew`; it is
unchecked. Report: `docs/research/htnew-det.md`.
