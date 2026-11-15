# x0-moduli (2026-11-15)

**Verdict.** `hX = T5Glue.X0ModuliGalois` cannot be split into printed leaves over genuine definitions today:
the three results it glues (coarse moduli scheme `Y₀(N)_ℚ`, `q`-expansion principle on the Tate curve, the
comparison `Y₀(N)(ℂ) ≅ Γ₀(N)\ℍ`) are scheme-theoretic. Mathlib has no moduli problems, coarse moduli or Tate
curve, so stating them would need structures invented for the purpose.

**Main result (VERIFIED, compiled, standard axioms; `#discharges` shows `[hX]` discharged):**
`X0Moduli.x0ModuliGalois_of_leaves : WeierstrassGroupLaw → VeluCyclic → RatX0Rep →
X0ModuliGaloisNonIsolated → T5Glue.X0ModuliGalois` in `ZInQKernel/Contrib/OneProof/X0ModuliGalois.lean`
(copy in `scratch/x0-moduli/X0Moduli.lean`).
* The moduli and uniformization step `σ(j(Nτ)) = j(Nτ')` (`JNConj`) is a Lean proof from two textbook
  statements about Mathlib's `℘`: the chord-and-tangent law (`WeierstrassGroupLaw`) and Vélu's formulas for
  `⟨1/N⟩` (`VeluCyclic`). Both were checked numerically with PARI.
* At isolated points of the plane model `(j, j_N)`, the kernel's `RatX0Rep` (`ℚ(X₀(N)) = ℚ(j, j_N)`, the
  `q`-expansion part) finishes the proof.
* The canonical-model content is left only at the non-isolated points (`X0ModuliGaloisNonIsolated`). These are
  finitely many CM orbits for each `N`, and the TYZ consumers need them (class-7 forms, `n = 7, 15, 47, …`).

**Count.** The split raises the strict GLUE count (1 → 4: composite, consequence, composite, consequence), so it
is a refinement, not a fold. `autofold.py` also refuses the spec because `hX` is a plain argument
(`scratch/x0-moduli/autofold.json`). No statement was changed, and none was found false or vacuous. An independent model review of the new Props found all of them true and non-vacuous; its one attribution fix is applied.

**Remains.** `X0ModuliGaloisNonIsolated`: a route through Fricke symmetric functions is sketched in report §4.
`RatX0Rep` (no modular polynomials in Lean). `VeluCyclic` (a lattice-sum identity Mathlib could prove).
`WeierstrassGroupLaw` (needs Liouville for elliptic functions). Report: `docs/research/x0-moduli.md`; log:
`scratch/x0-moduli/log.md`.
