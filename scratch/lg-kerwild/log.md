# lg-kerwild results log

## Step 0 (09:03-09:15 PST): setup
- Merged origin/wip/local-glue (KerWild, DescentPts, localGlue_of_unramRoots, descentPts_baseChange,
  kerWild_of_g7Data with ι : ℂˣ →* ℚ̄_ℓˣ injective).
- Read (VERIFIED): g14-trace's `G14Bridge.TateBridge35` (scratch/g14-trace/part_bridge.lean l.44-72)
  carries `∃ ιC : ℚ̄ →ₐ[ℚ] ℂ, ∀ g, ιC (βQ g) = β g` and outputs G7Out with `β' = j_ℓ ∘ βQ`;
  g0-mod-field's `TateBridge` (ModField.lean) has no such clause; g0-assemble2's GLUE field 39
  `LinkedTateLocal` (parts/a85_linked.lean l.2142) has neither the ιC clause nor KerWild.
- G7Data clause 9: `∀ σ, σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1`, `GQL L = L.fixingSubgroup`
  (ZInQKernel/HDecomp/Descent/B3Assembly.lean l.36).
- g0-dim's `G0Dim.pkgI3_dim_baseChange` (scratch/g0-dim/Dim.lean l.341): `(A.baseChange L).dim = A.dim`.
- build.sh: KerWild.lean = LocalGlue.lean body + G14Bridge.lean body + Dim.lean slice + part_kerwild.lean.
- `lake build` of the 24 imported ZInQKernel modules: success.
