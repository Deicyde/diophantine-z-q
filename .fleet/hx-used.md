# hx-used: `hX` removed. The consumers' needs now come from `hCM` plus one explicit θ–℘ identity

**Proved** (compiled; axioms `[propext, Classical.choice, Quot.sound]`; no sorry). The contributor file is
`ZInQKernel/Contrib/OneProof/X0ModuliUsed.lean`, with helper `X0ModuliUsed/EtaRoute.lean`.

- **Consumers.** `hX` reaches `frozenTarget` only through `shimuraReciprocityModFn_of_printed hCM hX`. Every consumer
  of that statement uses it at `N = 32` and `g ∈ {X0.xC, X0.yC}` only, at Heegner points (report §3, file and line
  for each instance).
- **Eta route (recommended).** `X0EtaRoute.srAt_x` and `srAt_y : XEtaWeierstrass → ShimuraMainCM →
  ShimuraReciprocityModFnAt 32 _`. Building on these:
  - `xEtaWeierstrass_of_theta : ThetaWeierstrass8 → XEtaWeierstrass`;
  - `X0ModuliUsed.tyzThm35ReadingA_of_theta h11 h29 hCM hT h33`;
  - `X0ModuliUsed.frozenTarget_of_theta r t l g h11 h29 hCM (hT : X0EtaRoute.ThetaWeierstrass8) h33 hFH hL3 :
    ZInQ.FrozenTarget`. This is `frozenTarget` with `hX` replaced by `hT`.
  - `ThetaWeierstrass8`: `∀ w : ℍ, θ(0;w)/(e^{πiw/4}θ(w/2;w)) = 1 − 2(℘(1/2) − ℘(1/2+w/8))/(℘(3w/8) − ℘(1/2+w/8))`,
    with `℘` of `⟨1, w⟩` and Mathlib's `jacobiTheta₂`.
  - Rating: GLUE, not printed (no source located). Numerically verified at 12 random points, worst error 5e-41.
    Provable in principle via Jacobi's θ/σ relations and Liouville. The route needs no canonical model or moduli
    input.
- **Used form (alternative).** `X0ModuliGaloisX0_32` is `X0ModuliGalois` at `N = 32`, `g ∈ {x, y}`, at Heegner points.
  - `x0ModuliGaloisX0_32_of : X0ModuliGalois → X0ModuliGaloisX0_32` (never stronger than `hX`).
  - `frozenTarget_of_used` proves the target with it in place of `hX`.
  - Rating: consequence, GLUE, not printed.
- **`#discharges`** (`scratch/hx-used/discharges.txt`): `63 open hypotheses, 1987 theorems checked, 7 discharge one`.
  All seven are existing contributions. None comes from this file, because `hX` is replaced, not proved.
- **Fold.** Manual; `autofold.py` does not apply because `hX` is a plain argument of `frozenTarget`. In Main.lean:
  - add `import ZInQKernel.Contrib.OneProof.X0ModuliUsed`;
  - l.64: binder `(hT : X0EtaRoute.ThetaWeierstrass8)`;
  - l.70: term `(X0ModuliUsed.tyzThm35ReadingA_of_theta h11 h29 hCM hT h33)`.

  This equals the compiled `frozenTarget_of_theta`. The strict GLUE count is unchanged, 1 → 1.

**What remains:** a Lean proof of `ThetaWeierstrass8` (route in report §5). Report: `docs/research/hx-used.md`.
