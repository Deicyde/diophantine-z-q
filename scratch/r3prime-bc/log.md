# r3prime-bc results log

## 2026-11-17 10:51 start
- Base: wip/r3prime-etale at 3fd6159ef (r3prime-etale final). VERIFIED (git log).
- Imports ZInQKernel.Contrib.OneProof.HolChartSerre + ZInQKernel.Contrib.CloudB3W17Hodge.Bridge together:
  no clash (Probe.lean compiles, VERIFIED).

## 11:05 scratch/r3prime-bc/R3BC.lean compiles (VERIFIED, `lake env lean`, no errors/warnings;
## axioms propext, Classical.choice, Quot.sound for all five headline declarations)
- `bc 𝒢 τ : Over (Spec ℂ)` := Over.mk (pullback.fst (Spec τ|𝓞_L) 𝒢.G.hom), i.e. 𝒢 ×_{𝓞_L,τ} Spec ℂ.
- `ptsEquivBC : 𝒢.Pts τ ≃ CPt (bc 𝒢 τ)`, p ↦ (id, p).
- `xevalAt_toBC`: XevalAt (pr⁻¹U) (pr^*s) (toBC p) = 𝒢.evalAt p U s.
- `bc_formula`: every section σ of bc near toBC q is σ·(Σ v_j c_j)^N = Σ u_j c_j with c_j regular on 𝒢
  (r3prime-etale's exists_tensor_formula with X = Spec ℂ, a = id).
- `anTop_eq_induced`: anTop 𝒢 τ = induced toBC (classicalTopology (bc 𝒢 τ)).
- `ptsHomeomorph : (𝒢.Pts τ, anTop) ≃ₜ (CPt bc, classicalTopology)`; `ptsHomeomorphPort` (to the port's
  Point ℂ with analyticTopology); `chartedSpacePts` (vendored atlas transported, if bc smooth of rel. dim d).
- `BCHolAt X h P`: Serre's sheaf of a ℂ-scheme X from X's own regular functions (classical topology).
- `bcHolAt_iff : BCHolAt bc k (toBC q) ↔ AnHolAt 𝒢 τ (k ∘ toBC) q`; `anHolAt_iff_bcHolAt`.
- `IsBCSerreChart`, `pullChart`, `pushChart`, `isSerreChart_pullChart_iff`,
  `isHolChart_iff_isBCSerreChart (hT35) : IsHolChart φ ↔ IsBCSerreChart bc (pushChart φ)`,
  `isBCSerreChart_iff_isHolChart`, `exists_bcSerreChart_at`.
- `bcHolAt_chartAt`, `unitGermChart_bc`: unit-germ chart coordinates are BCHolAt; pushed IsHolChart
  charts are BC Serre charts.
- Reading note (a) of r3prime-etale is now a theorem; no new leaf, no new hypothesis besides T35.

## 11:10 checks
- Contrib HolChartBC.lean clean; lake build Main+Discharges+HolChartBC OK (16217 jobs); #discharges: 19 pre-existing
  lines, none by ZInQ.R3BC; 7 headline axioms standard (VERIFIED). Report docs/research/r3prime-bc.md.
