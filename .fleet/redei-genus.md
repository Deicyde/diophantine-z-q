# redei-genus report: steps 4 and 5 of docs/research/redei-plan.md §3.2

Status: **done**. Both modules are free of `sorry`, and `lake build ZInQKernel` passes.
`#print axioms` on every main result lists only propext, Classical.choice and Quot.sound.

Files (namespace `ZInQ.RouteK.Redei`), both imported by the root module `ZInQKernel/RouteK/Redei.lean`:
- `ZInQKernel/RouteK/Redei/Genus.lean` (294 lines; plan estimate 400)
- `ZInQKernel/RouteK/Redei/Dirichlet.lean` (191 lines; plan estimate 350)

The Probe statements of §3.4 and §3.5 keep their form, with `n` explicit (as in redei-fp).

## Step 4 (Genus.lean)
- `exists_mk0_coprime n q hq c`: every class contains an integral ideal whose norm is prime to `q`
  (`q` any prime). Proof: Mathlib's `IsDedekindDomain.exists_sup_span_eq` applied to `J(q) ≤ J`, for
  `J` in the inverse class, gives `(a) = J M` with `M + (q) = O`. Then
  `not_dvd_absNorm_of_sup_span_eq_top` (from `Ideal.exists_isMaximal_dvd_of_dvd_absNorm'`) shows
  `q ∤ N M`.
- `isSquare_normZ_mod hsq hq x`: for `q ∣ n` (`n` squarefree), **every** `x : O` has `N(x)` a square
  mod `q`. Proof: `σ` acts trivially on `O/𝔭_q` (`sub_conj_mem`), and `x ≡ m (mod 𝔭_q)` for an
  integer `m`, so `N x − m² = x(σx − x) + (x−m)(x+m) ∈ 𝔭_q`. The plan's condition `α ∉ 𝔭_q` is not
  needed.
- `legBit_absNorm_span` (`[N(x)/q] = 0`), `legBit_absNorm_mul`, `not_dvd_absNorm_mul`,
  `intCast_natCast_zmod_ne_zero`.
- `legBit_absNorm_eq_of_mk0_eq` (well-definedness): take `𝔠` prime to `q` in the inverse class. Then
  `𝔞𝔠` and `𝔟𝔠` are principal, so `[N𝔞/q] = [N𝔠/q] = [N𝔟/q]`.
- `chiBit n q c` (the bit of a chosen representative prime to `q`), `chiBit_mk0`, `chiBit_mul`.
- `chi n q : ClassGroup O →* Multiplicative (ZMod 2)`: `MonoidHom.mk'` when `Squarefree n`, and
  `1` otherwise. The `dite` is needed because the homomorphism property needs `n` squarefree.
- `chi_mk0 n hn hsq q I hI` (the Probe statement).
- `chi_ramIdeal_self`: `χ_q([𝔭_q]) = [(n/q)/q]`, via `𝔭_q · Π_{p≠q} 𝔭_p = (√−n)` (`span_omega`)
  and `N(Π_{p≠q} 𝔭_p) = n/q`.
- **`chi_ramIdeal n hn hsq q p`**: `chi n q (mk0 ⟨ramIdeal n p, ramIdeal_mem n p⟩) =
  ofAdd (redeiEntry n q p)` for every `p : ramSet n`, covering the cases `p = 2`, `p = q` and
  `p ≠ q`.
- **`chi_prod_ramIdeal n hn hsq q e`**: `toAdd (χ_q(Π_p [𝔭_p]^{(e p).val})) = Σ_p R_{qp} e_p`. This is
  `chi_psi` without `psi`.

## Step 5 (Dirichlet.lean)
- General helpers: `prod_ite_bit_eq` (`Π (−1)^{f i} = (−1)^{Σ f i}`) and
  `jacobiSym_finsetProd_right`.
- `exists_absNorm_eq_of_isSquare n hp hp2 hpn hsq` (the Probe statement). The proof splits by
  `prime_trichotomy`:
  - ramified: excluded by `dvd_of_ramified`;
  - inert: `(m+ω)(m−ω) ∈ pO`, and `pO` is σ-stable, so both factors lie in `pO`. Then `p ∣ 2m`, so
    `p ∣ m` and `p ∣ n`, a contradiction.
- `ne_two_of_mem_primeFactors`.
- `exists_chi_eq n hn hsq ε hε` (the Probe statement). It reuses the existing slot lemma
  `ZInQ.RouteK.exists_prime_slot_bits` (`RouteK/Slots/Dirichlet.lean`: residues via
  `FiniteField.exists_nonsquare`, CRT, `Nat.forall_exists_prime_gt_and_zmodEq`):
  - choose `ℓ ∉ primes(n)` with `[ℓ/q] = ε_q` and `ℓ ≡ 1 (mod 8)` if `Σε = 0`, `ℓ ≡ 3 (mod 8)`
    otherwise;
  - then `J(−n|ℓ) = χ₄(ℓ)·J(ℓ|n) = (−1)^{Σε}·(−1)^{Σε} = 1`, by `jacobiSym.neg` and
    `jacobiSym.quadratic_reciprocity_one_mod_four(')`. When `Σε ≠ 0`, `hε` forces `n ≡ 1 (mod 4)`;
  - a prime of norm `ℓ` then has the prescribed characters.

## chi_psi (for the next task)
The Probe's `chi_psi` follows directly from redei-amb's `psi`. I checked this in a scratch file
(deleted) against `origin/wip/redei-amb` at commit 07213a89 (`Ambiguous.lean`), where it compiles:
```lean
theorem chi_psi (hn : Odd n) (hsq : Squarefree n) (q : n.primeFactors) (e : ramSet n → ZMod 2) :
    Multiplicative.toAdd (chi n q (psi n (Multiplicative.ofAdd e))) =
      ∑ p, redeiEntry n q p * e p := by
  rw [psi_apply, ← chi_prod_ramIdeal n hn hsq q e]
  simp only [toAdd_ofAdd, ambigClass_eq hn hsq]
```
It belongs in a module that imports both Genus and Ambiguous, for example step 6, FourRank.

## Notes and pitfalls
- `chi_mk0` keeps the Probe's `hn : Odd n` argument (named `_hn`) although only `hsq` is used.
- Building a subtype `⟨span {a}, by rw [hM]; exact (J * M).2⟩ : (Ideal O)⁰` timed out in `isDefEq`.
  Instead use `ClassGroup.mk0_eq_one_iff (J * M).2` and rewrite the coercion with
  `Submonoid.coe_mul`.
- `legendreSym.to_jacobiSym` is `jacobiSym.legendreSym.to_jacobiSym`.
- Do not `rw` with `n = ∏ q ∈ n.primeFactors, q` when the goal contains terms indexed by
  `n.primeFactors`: the motive breaks. Use `congrArg`.
- The root module `Redei.lean` does not import `Redei/Kernel.lean`. `ZInQKernel.lean` imports
  `RouteK.RedeiKernel` separately. I left that as it was.
- I did not touch `scripts/print_axioms.lean`, because this task names no lines in it.

## Left
- Nothing is left for steps 4 and 5. `chi_psi` needs `psi`; see the corollary above.
