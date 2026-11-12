# glue-sqrt-disj (final note)

**Main result.** B2's local square-root criterion is proved in Lean over the genuine Galois groups
`Gal(ℚ_p(μ_N)/ℚ_p)` for every prime `p`, including 2. That includes the disjointness and the level change
glue-sqrt-local left open. It is also instantiated on the fields `adjoin ℚ_p {x | x^n = 1} ⊆ PadicAlgCl p`
that leaf I6.3 (`LocalKroneckerWeber`) produces. No `sorry`; `#print axioms` shows only `propext`,
`Classical.choice`, `Quot.sound`. Report: `docs/research/glue-sqrt-disj.md`; log:
`scratch/glue-sqrt-disj/log.md`.

What compiles (`lake env lean scratch/glue-sqrt-disj/Disj.lean`, 2026-11-12 00:57 PST, re-checked 01:15 PST; self-contained):
- `totient_mul_orderOf_le_finrank`: `φ(p^k)·ord_m(p) ≤ [L:ℚ_p]` for any finite Galois `L ∋ ζ_{p^k}, ζ_m`.
  It comes from Mathlib's Galois fundamental identity `g·e·f = |G|`, with `e ≥ φ(p^k)` (`p ∈ Q^φ(p^k)`)
  and `f ≥ ord_m(p)` (roots of unity in the residue field).
- **Disjointness:** `galEquivProd : Gal(ℚ_p(μ_{p^k m})/ℚ_p) ≃* (ℤ/p^k)ˣ × ⟨p⟩`;
  `finrank_eq_totient_mul_orderOf`; `galToProd_restrict` (restriction becomes reduction).
- **Level change:** `orderOf_unit_pow_sub_one` (`ord_{p^n−1}(p) = n`), `dvd_pow_orderOf_sub_one`.
- **`sqrt_criterion_level`** (every `p`): for `K = ℚ_p(μ_{p^k m}) ⊆ L = ℚ_p(μ_{p^{k+1} m'})`
  with `ord_{m'}(p) = 2 ord_m(p)`, a character `χ` of `Gal(K/ℚ_p)` inflated to `L` is `2ψ` iff
  `χ(τ₋₁) = 0`. `sqrt_criterion_level_pow` is the case `m' = p^{2f} − 1`.
- **On I6.3's fields:**
  - `isCyclotomicExtension_muField`;
  - `le_muField_of_lkw`: I6.3 implies every finite abelian `M ⊆ \bar ℚ_p` lies in `ℚ_p(μ_{p^k m})`, `p ∤ m`;
  - `sqrt_criterion_muField`.

What remains (not proved):
1. The last plumbing step over `G_{ℚ_p} = Gal(\bar ℚ_p/ℚ_p)`:
   - descend `χ` from `G_{ℚ_p}` to `Gal(ℚ_p(μ_{p^k m})/ℚ_p)` (kernel ⊇ `Gal(\bar ℚ_p/M)`, `M ≤ K`);
   - inflate `ψ` back;
   - match `τ₋₁ ∈ G_{ℚ_p}` with `τ`;
   - for the converse, apply I6.3 to `ker ψ`.

   An uncompiled draft of the "if" direction is in `scratch/glue-sqrt-disj/AbsoluteAttempt.lean.txt`
   (not claimed). It is blocked by a kernel deterministic timeout in
   `restrictNormal_muField_trans`, the transitivity of restriction through the `muField` inclusion.
   SPECULATIVE: 150-250 lines; no arithmetic input beyond I6.3.
2. Discharging the instance hypothesis `[NeZero (p^{2f}−1)]` in the two `_pow`/`muField` statements (trivial).
