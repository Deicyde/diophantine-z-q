# redei-amb log

## Step A (compiled)
Redei/Ambiguous.lean: ambig_smul_smul, ambig_smul_span, ambig_smul_ne_zero, ambig_normZ_eq,
ambig_hilbert90 (Hilbert 90: uses ideal norms, absNorm_smul, normZ_nonneg; nu = σx(x+y) or 1),
ambigClass (class of 𝔭_p if its square is 1, else 1: makes psi a hom for every n),
ambigClass_sq, ambigClass_eq (n odd squarefree), psi, psi_apply, psi_sq,
psi_single (NOTE: needs hn hsq, unlike the probe), mk0_prod_ramIdeal, psi_ones.
Fixes: Decidable for the ite in a def -> `open Classical in`; (1 : ZMod 2).val = 1 by rfl.
