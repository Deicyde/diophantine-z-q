# gz-moduli results log

Task: make `ZInQ.GZHL3.GrossZagierFormulaCd` printed (moduli form of Gross–Zagier I.6.3 / V.2.1).
Base: 60a3fac7 + merge of wip/gz-weil ad22e947 (commit 6cf5853f).

## Statements (VERIFIED, read in the tree)
- Target: `ZInQ.GZHL3.GrossZagierFormulaCd` (ZInQKernel/Contrib/OneProof/GrossZagierHeegner/Cd.lean)
  = ∀ d ≡ 5 (8) squarefree, `GrossZagierFormulaAt (shortCurve (-(d:ℚ)^2))`
  (`GrossZagierFormulaAt` in ZInQKernel/Contrib/OneProof/GrossZagierHeegner.lean:185). Verbatim copy:
  scratch/gz-moduli/Target.lean.
- Tools available (VERIFIED, read): Heegner.lean (gz-heegner) proves `isRatModFnMero_coords`
  (x∘φ, y∘φ ∈ ℚ(X₀(N)) as `IsRatModFnMero`), `paramRegular`, `paramCuspGrowth`, `paramQExpansion`,
  `pairHom_of_equiv`, `equiv_of_pairHom` (homothety of (⟨1,τ⟩,⟨1/N,τ⟩) ⇔ Γ₀(N)-equivalence).

## Plan (design decisions)
- X₀(N)_ℚ is not in Mathlib; a ℚ-morphism X₀(N) → E is a point of E(ℚ(X₀(N))), and ℚ(X₀(N)) is the
  field of Γ₀(N)-modular functions with rational q-expansion (canonical model; gz-heegner's
  `IsRatModFnMero`). So φ = (X, Y) with X, Y ∈ ℚ(X₀(N)), Weierstrass equation, ‖X‖ → ∞ at i∞
  (φ(∞) = O, φ nonconstant). No GAGA needed: the analytic φ's coordinates are proved to lie in ℚ(X₀(N)).
- Heegner points: lattice model of Y₀(N)(ℂ): pairs Λ₁ ⊂ Λ₂ with Λ₂/Λ₁ cyclic of order N,
  End(Λ₁) = End(Λ₂) = O_D, n = (N, (−β+√D)/2) kills Λ₂/Λ₁; complete set of homothety classes.
- φ at a point: via limits in punctured neighbourhoods (independent of junk values).
- Target.lean: verbatim copy, `rfl` against the original: COMPILED (VERIFIED).

## Lean results (ZInQKernel/Contrib/OneProof/GrossZagierModuli.lean), all `lake env lean`, COMPILED (VERIFIED)
- §1 objects + leaf `GrossZagierModuliAt` / `GrossZagierModuli` / `GrossZagierModuliCd`, `grossZagierModuliCd_of`.
- §2 lattice algebra: `latEnd_span_root` (End⟨1,σ⟩ = O_D), `isHeegnerPair_of_form`, `exists_coprime_lift`,
  `normalize_pair` (adapted basis), `form_of_normalized`, `exists_rep`, `isHeegnerPointReps_of`.
- §3 analysis: `frequently_zPar_notMem`, `not_tendsto_xPar`, `modPt_eq`, `tendsto_norm_xPar`, `isModularParam_of`.
- §4 `grossZagierFormulaAt_of_moduli`, `grossZagierFormula_of_moduli`, `grossZagierFormulaCd_of_moduli`.
- NonVacuous.lean: `exists_heegnerPointReps`, `exists_modularParam_cd` (written; compile pending).
- Finding: GAGA (`gagaMorphism`) is not needed: algebraicity of φ = coordinates in ℚ(X₀(N)), proved by gz-heegner.
- lake build (13703 jobs) OK; Check.lean standard axioms; MainEdit frozenTarget_gzmoduli standard axioms; #discharges: [hL3] by GZModuli.grossZagierHeegner_of_moduli (VERIFIED).
