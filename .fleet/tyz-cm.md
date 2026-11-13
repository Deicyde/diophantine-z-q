# tyz-cm — fleet report (2026-11-13)

**Main result.** cm-points' CM leaf `CM.CMFieldOfDefinition ringClassFieldD` (hence
`Package.CMFieldOfDefinitionTYZ`) is reduced to ONE textbook leaf:

```lean
theorem ZInQ.Contrib.TYZGenus.Shimura.cmFieldOfDefinition_of_cmValueRingClass
    (hV : Shimura.CMValueRingClass) : CM.CMFieldOfDefinition RingClass.ringClassFieldD
```

`CMValueRingClass` (ShimuraMain.lean): for every `g ∈ ℚ(X₀(N))` regular on `ℍ` (`IsRatModFn N g`:
`Γ₀(N)`-invariant, meromorphic at all cusps, rational `q`-expansion) and every Heegner form `Q` of
level `N`, discriminant `D`, `g(τ_Q) ∈ ringClassFieldD D` (main theorem of CM + rational structure
of `X₀(N)`; Shimura 1971 Thm. 5.7/Prop. 6.9, Gross 1984 §1–3, Cox Thm. 11.1; numbers UNVERIFIED;
refereed). No Heegner condition needed. It does not mention x0-32's eta model.

**Also proved (all axioms `propext, Classical.choice, Quot.sound`; `lake build
ZInQKernel.Contrib.TYZGenus.ShimuraTheta` OK):**
* `etaModelInvariant : X0.EtaModelInvariant` — **x0-32's leaf, now a theorem** (via the eta
  identity `xC_eq_even : x = η(16τ)⁶/(η(8τ)²η(32τ)⁴)` from Jacobi's triple product, and
  `etaSqExp_closed`: gz-theta's `η²` multiplier exponent ≡ Petersson's polynomial mod 12).
* `yC_gamma0`, `xC_sub_two_sq_gamma0`, `etaModelInvariant_of_equation`.
* `etaCuspGrowth : EtaCuspGrowth`, `xQExpRational`, `yQExpRational` (x, y meromorphic at all cusps,
  rational q-expansions).
* `cmValueRingClass_of_modFn : ShimuraReciprocityModFn → CMValueRingClass`;
  `shimuraReciprocityPic_of_shimuraModFn : ShimuraReciprocityModFn → ShimuraReciprocityPic`;
  `cmFieldOfDefinition_of_shimuraModFn`; `cmFieldTYZ_of_cmValueRingClass`;
  `tyzThm35ReadingA_of_cmValueRingClass` (TYZ Thm 3.5 reading A from the 3 𝓛-leaves,
  `CMValueRingClass`, `TYZSigmaFixesZn`, `Lemma318Literal`, `GenusPointLeafCM`).

**For cm-numeric (TYZSigmaFixesZn, not continued here):** `ShimuraZn.lean` (earlier run, unchanged)
proves `tyzSigmaFixesZn_of : ShimuraReciprocityPic → X0.EtaModelFricke → TYZSigmaFixesZn` (all
TYZ-specific lattice/Fricke steps); with `shimuraReciprocityPic_of_shimuraModFn` this gives
`TYZSigmaFixesZn` from `ShimuraReciprocityModFn ∧ X0.EtaModelFricke`.

**Remains:** the textbook leaf `CMValueRingClass` (or the stronger Gross-form
`ShimuraReciprocityModFn`). Caveats: TYZ reading A not refereed; TYZ arXiv v1 only;
`z_n = (1 − [i])f₀(P_n)` from tyz-t1 (AI-derived, numerically checked).

Files (new): `ZInQKernel/Contrib/TYZGenus/Shimura{Recip,Zn,Field,ModFn,QExp,Cusp,Main,EtaInv,Theta}.lean`.
Report: `docs/research/tyz-cm.md`; log: `scratch/tyz-cm/log.md`.
