# redei-amb report: Rédei step 3, ambiguous classes (G1)

Module: `ZInQKernel/RouteK/Redei/Ambiguous.lean` (namespace `ZInQ.RouteK.Redei`), imported by the root
`ZInQKernel/RouteK/Redei.lean`. There is no `sorry`. The axioms of `range_psi`, `card_ker_sq_le`, `psi_ones`
and `psi_single` are `propext, Classical.choice, Quot.sound`. `lake build ZInQKernel.RouteK.Redei` and
`lake build ZInQKernel` succeed.

## What is proved
Setting: `K = QNeg n`, `O = 𝓞 K`, `σ ≠ 1`. "n odd squarefree" means the hypotheses `hn : Odd n` and
`hsq : Squarefree n`.

- Action of σ: `ambig_smul_smul` (σσx = x), `ambig_smul_span` (σ•span{x} = span{σ•x}), `ambig_smul_ne_zero`.
- Hilbert 90 for ideals:
  - `ambig_normZ_eq n σ (hI : I ≠ ⊥) (h : span{x} * σ•I = span{y} * I) : norm ℤ x = norm ℤ y`.
    The proof takes ideal norms (`absNorm_smul`, `Ideal.absNorm_span_singleton`) and uses `normZ_nonneg`.
    This is shorter than the plan's argument with rational units.
  - `ambig_hilbert90 n σ hσ hI (hx : x ≠ 0) h : ∃ ν ≠ 0, σ • (span{ν} * I) = span{ν} * I`, with
    `ν = σx (x + y)`, or `ν = 1` when `x + y = 0`.
- `ambigClass n p` is the class of `𝔭_p` if its square is 1, and 1 otherwise. Lemmas:
  `ambigClass_sq`, and `ambigClass_eq hn hsq p : ambigClass n p = mk0 ⟨ramIdeal n p, _⟩`.
- `psi n : Multiplicative (ramSet n → ZMod 2) →* ClassGroup O`, with
  `psi_apply : psi n e = ∏ p, ambigClass n p ^ (toAdd e p).val`, and `psi_sq`.
- `psi_single n hn hsq p : psi n (ofAdd (Pi.single p 1)) = mk0 ⟨ramIdeal n p, ramIdeal_mem n p⟩`.
- `mk0_prod_ramIdeal` (the product of the classes is the class of the product), and
  `psi_ones n hn hsq` (statement as in the Probe, via `span_omega`).
- `ambig_two_mem_ramSet`, and `ambig_exists_dvd`: a nonzero proper σ-invariant ideal has a proper
  σ-invariant divisor whose class lies in im ψ. That divisor is pO when p is split or inert, and 𝔭_p
  when p is ramified (p ∈ ramSet by `dvd_of_ramified`, and the divisor equals 𝔭_p by
  `eq_ramIdeal_of_liesOver`).
- `mem_range_psi_of_conj_eq n σ hσ hn hsq I hI` (statement as in the Probe), by strong induction on `absNorm`.
- `range_psi n hn hsq : (psi n).range = (powMonoidHom 2).ker` (statement as in the Probe). The proof:
  `mul_conj_ideal` gives [σI] = [I]⁻¹ = [I]; `ClassGroup.mk0_eq_mk0_iff` and Hilbert 90 then give a
  σ-invariant ideal νI in the same class.
- Corollary `card_ker_sq_le n hn hsq (h1 : 1 < n) :
  Nat.card (powMonoidHom 2 : ClassGroup O →* _).ker ≤ 2 ^ ((ramSet n).card - 1)`. It uses
  `Subgroup.card_ker_mul_card_range`, and the kernel of ψ contains the vector of `(√−n)`, which is nonzero.

## Deviations from the Probe statements (for the siblings)
- `psi_single` takes `(hn : Odd n) (hsq : Squarefree n)`. Without them, `[𝔭_p]² = 1` can fail, and then
  `psi` could not be a homomorphism equal to `[𝔭_p]` on basis vectors. `psi` itself has no hypotheses:
  it uses `ambigClass`, which equals `[𝔭_p]` when n is odd squarefree (`ambigClass_eq`). For
  `chi_psi`, use `psi_apply` together with `ambigClass_eq`, or `psi_single` and `map_mul`.
- `card_ker_sq_le` also assumes `1 < n`. For n = 1 the vector of (√−n) is 0, so the bound would need
  Cl(ℚ(i)) = 1. In the application n = d_B ≥ 3.
- As redei-fp did, `n` is explicit in the theorems (`variable (n) in`).

## What is left
Nothing in step 3. Steps 4–6 and 8 belong to the sibling tasks.

## Lean notes
- An `ite` inside a `def` needs `open Classical in`.
- A `▸` inside a subtype literal of `(Ideal O)⁰`, and an inline `⟨span{ν}, _⟩ * I` argument, both hit
  whnf timeouts. The fixes: state `IsPrincipal` of the coercion and apply `ClassGroup.mk0_eq_one_iff _`,
  and bind the element with `let J` plus a `show … from rfl` rewrite.
