# nt-prop0 log

## Step 0 (sources read)
- CR3: ZInQKernel/Hypotheses/CertifiedRank.lean (`ZInQ.CertifiedRank`), system in
  ZInQKernel/RouteK/System/Selmer.lean (`Config.IsSol`, `E1`, `E2`, `D`, `twoAdicRows`),
  configuration of d in RouteK/Assembly/Realize.lean (`natConfig`, `natClass`, `primeCfg`),
  `legBit p a = if IsSquare (a : ZMod p) then 0 else 1` (RouteK/Slots/Symbols.lean:17).
- Prop 0: descent-alt §4.1; referee proof rv-slot-k-descent §1.1-1.5 (place 2 by x = 1/4, all 4
  classes); slot-k §2.1, §4.1, §4.3 (estimate "months", SPECULATIVE).
- Mathlib: same rev 56a0058 as ~/dzq-wt/cr3-check/.lake/packages/mathlib; grep there (no fetch).

## Step 1 (design of the definition; restart after interruption)
- Mathlib at ~/dzq/.lake/packages/mathlib (rev 56a0058 = manifest rev). Inventory delegated, output
  to scratch/nt-prop0/mathlib-inventory.md.
- Definition chosen: projective 2-covering D_{a,b}: a z1² − b z2² = d w², a z1² − ab z3² = −d w²
  (z ≠ 0) over a field K. Sel₂(d) := {(a,b) squarefree integers : D_{a,b}(ℝ) ≠ ∅ ∧ ∀ p, D_{a,b}(ℚ_p) ≠ ∅}.
- Field-generic lemma K (VERIFIED on paper): (a,b) ∈ δ_K(E(K)) ⟺ D_{a,b}(K) ≠ ∅, with explicit
  points (1,1,1,0), (0,1,1,1), (1,0,1,1), (1,1,0,1) for the four torsion classes; w = 0 ⟺ trivial class.
- Local analysis plan: p | d odd by valuation of x (cases v<0, v=0, v=1 with t≡±1, v≥2); ∞ by sign of x;
  2 for d≡5 by v(x) and x mod 8 (8 classes; non-torsion ones need √(1−16d²) ∈ ℚ₂);
  p ∤ 2d: necessity by valuations, sufficiency needs δ_{F_p} surjective (group law + halving) + Hensel.
