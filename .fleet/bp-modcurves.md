# bp-modcurves (fleet summary)

**Main result.** `docs/research/bp-modcurves.md` is the blueprint for `X₁(N)`, `J₁(N)`, the Hecke
algebra, `A_f` and the Belyi degree (the objects that block R16, R18, G13, G17, E2). Verdict: the
project uses these objects in only three ways: `ρ_{f,ℓ} ⊂ V_ℓ(J₁(N))`, `g = dim J₁(N) ≤ N²`, and a
Belyi map of degree `≤ N²`. The cheapest faithful route is algebraic:
- `X₁(N)` is Mathlib's relative normalization of the `j`-line in `ℚ(j)(x(P))`;
- `J₁(N)` is an Albanese predicate over the repository's `AbVar`, with existence as a leaf
  (Weil/Milne);
- R16 is stated existentially (`J₁(N) ↠ A`, `K_f ↪ End⁰ A`, traces `a_p`), so Hecke
  correspondences on `J₁(N)` are avoidable;
- the genus and Belyi bounds come from `deg j ≤ N²/2` plus Riemann–Hurwitz for Belyi maps
  (`g ≤ (d−1)/2`).

The Picard-scheme and complex-torus routes are compared and rejected for the critical path.
There is a dependency graph of 18 nodes with a size tier and cheapest route for each, Mathlib v4.35
inventory (grep-verified), and work packages.

**What compiles** (`scratch/bp-modcurves/`, 6 files, about 1 700 lines; each `lake env lean` exit 0,
no warnings, no `sorry`, axioms ⊆ {propext, Classical.choice, Quot.sound}):
- `Gamma1Genus.lean`: Belyi degree `μ`, `ν₂`, `ν₃`, `ν∞`, and genus of `Γ₁(N)` over Mathlib's
  `SL(2,ℤ)`/`Gamma1`. `ν₂ = 0` (N ≥ 3), `ν₃ = 0` (N ≥ 4), `g = 1 + μ/12 − ν∞/2`, `μ ≤ N²`,
  `g ≤ N²`. `SL(2,ℤ) ⧸ Γ₁(N) ≃` primitive vectors of `(ℤ/N)²` (lifting lemma), and
  `2μ = #PrimVec N ≤ N²`.
- `TateNormalForm.lean`: existence and uniqueness of Tate normal form; `Δ(b,c)`.
- `PointTransport.lean`: transport of points under `VariableChange`, which Mathlib lacks; it is
  additive, injective and order-preserving. **`y1PointsEquivTate : Y₁(N)(K) ≃ {(b,c)}`** for
  `N ≥ 4`, the moduli interpretation at the level of points over any field.
- `AnalyticModuli.lean`: `(ℂ/Λ_{τ'}, 1/N) ≅ (ℂ/Λ_τ, 1/N)` iff `τ' ∈ Γ₁(N)τ`; every primitive
  level-`N` point is equivalent to `1/N`.
- `Jacobian.lean`: `IsJacobian` (Albanese property), the leaf statement `JacobianExists`, and
  `IsJacobian.unique` (proved).
- `ModularCurveDefs.lean`: `E_j` (`j(E_j) = j` proved), `fieldX1 = ℚ(j)(x(P))`, and `Y1j` (relative
  normalization of `Spec ℚ[j]`); the degree statements are open `Prop`s.
- Ground truth: `genus_check.py` (genus of `X₁(N)` for `N ≤ 30`, from the `S, ST, T` action,
  matches the closed forms and the table) and `tate_check.py` (Kubert families `N = 4..10`).

**What remains** (unproved):
- `#E[N] ≤ N²` (MC3a) and `[K_N:ℚ(j)] ≤ N²/2` (MC1).
- The proper smooth geometrically connected `X₁(N)` (MC4, large) and the Belyi property and
  degree of `j` (MC5).
- The cusp count and `nuInf = #CuspOrbits` (MC0c), and `#PrimVec N = J₂(N)`.
- Leaf statements to write: Riemann–Hurwitz (needs a genus definition; Mathlib has no `Ω¹` on
  schemes), MC1' (Igusa/Shimura irreducibility), and R16 existential over `IsJacobian`.
- The Faltings height (WP10) is out of scope, so R18 still cannot be stated.
