# redei-amb log

## Step A (compiled)
Redei/Ambiguous.lean: ambig_smul_smul, ambig_smul_span, ambig_smul_ne_zero, ambig_normZ_eq,
ambig_hilbert90 (Hilbert 90: uses ideal norms, absNorm_smul, normZ_nonneg; nu = σx(x+y) or 1),
ambigClass (class of 𝔭_p if its square is 1, else 1: makes psi a hom for every n),
ambigClass_sq, ambigClass_eq (n odd squarefree), psi, psi_apply, psi_sq,
psi_single (NOTE: needs hn hsq, unlike the probe), mk0_prod_ramIdeal, psi_ones.
Fixes: Decidable for the ite in a def -> `open Classical in`; (1 : ZMod 2).val = 1 by rfl.

## Step B (compiled)
ambig_two_mem_ramSet, ambig_exists_dvd (peel: pO split/inert, 𝔭_p ramified), mem_range_psi_of_conj_eq
(strong induction on absNorm), range_psi, card_ker_sq_le (needs 1 < n).
Fixes: `▸` inside a subtype literal timed out -> prove IsPrincipal of the coercion and use mk0_eq_one_iff _;
passing `⟨span ν, _⟩ * I` inline timed out (whnf) -> `let J` plus a `show ... from rfl` rewrite.
