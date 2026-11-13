# rv-jac-ext (fleet note)

**Verdict: ABSORBED.** Axiom's Jacobians need a degree-one divisor. The extension this requires
fits inside Theorem 4.1's existing bounds: F₀, D, QM and H₆ are unchanged. Details:
docs/research/rv-jac-ext.md.

- **The curve.** The genus-2 curve C with (Jac C, θ) ≅ (A, λ) exists over the fibre field K
  itself. This uses Torelli and Weil descent, or Serre's appendix to Lauter 2001 (UNVERIFIED
  locators); this is leaf N1. Mestre's obstruction applies over the field of moduli ℚ and does not
  arise.
- **The divisor.** A degree-one divisor over K is not guaranteed. Exact computation: G_K acts on
  A[2] = 𝒪/2𝒪 through (𝒪/2𝒪)^* ≅ A₄. When the image is V₄ or A₄, the Weierstrass orbits are
  [2,2,2] or [6]. When it is 1, C₂ or C₃ there is an odd orbit.
- **The fix.** Take K̃ = K(σA[2] : σ), the compositum of the 2-torsion fields of the conjugates.
  - It is Galois over ℚ and unramified outside T, because A6 gives good reduction away from 3, by
    Néron–Ogg–Shafarevich, and 2, 3 ∈ T.
  - [K̃:K] ≤ 12^k, where k = [K:ℚ].
  - C has six rational Weierstrass points over K̃.
  - [K̃:ℚ] ≤ 324·12^324 ≤ 324! = F₀.
  - So A_{K̃} meets A5-A6's conclusions with the same constants, A8 gives the same D, and B3 the
    same QM. Every step after A8 uses only d = [L:ℚ] ≤ D (checked against N5 L524-905).
- **One requirement.** [K:ℚ] ≤ 324. It follows from A3 plus the free action of Γ' on the fibre,
  or from h-b1 M3's 144. N5's printed 324! is too weak, so G2 should output ≤ 324.
- **Backup (route L).** Use L(A[2]) with [L(A[2]):L] ≤ 12. This needs 12·[L:ℚ] ≤ D, which holds.
- **J₁(N).** Confirmed: X₁(N)/ℚ has a ℚ-rational cusp, so no extension is needed, over ℚ or over L'.

**What compiles.** `scratch/rv-jac-ext/JacExt.lean` (Mathlib only; axioms propext,
Classical.choice, Quot.sound):
- `perm_eq_one_of_fixes_pairs` (core of "the Weierstrass points are rational over K(J[2])");
- `finrank_finset_sup_le` (degree of a compositum);
- `routeW_finrank` (324·12^324 ≤ 324! and the tower law);
- `routeL_degree` and `routeL_degree_noCM`.

Compiled with `lean` and LEAN_PATH, because `lake env` on this branch tries to fetch Mordell.
Exact scripts: `weier2.py` (orbits), `autcheck.py` (Aut(A,λ) = ±1), `bounds.py`.

**What remains.**
- Leaf N1 must be stated once polarizations exist in our layer (WP4).
- N2's geometry (the g¹₂, h⁰ = 1) needs Riemann–Roch on curves.
- Base change AbVar K → AbVar K̃ (WP4).
- G2's strengthening to [K:ℚ] ≤ 324 in Lean.
- The text change in A5.
- None of this is instantiated on the actual A (needs R1).
