# tyz-cm — fleet report (2026-11-13)

**Main result.** cm-points' CM leaf `CM.CMFieldOfDefinition ringClassFieldD` (hence
`Package.CMFieldOfDefinitionTYZ`) is reduced to ONE textbook leaf:

```lean
theorem ZInQ.Contrib.TYZGenus.Shimura.cmFieldOfDefinition_of_cmValueRingClass
    (hV : Shimura.CMValueRingClass) : CM.CMFieldOfDefinition RingClass.ringClassFieldD
```

`CMValueRingClass` (ShimuraMain.lean): for every `g ∈ ℚ(X₀(N))` regular on `ℍ` (`IsRatModFn N g`:
`Γ₀(N)`-invariant, meromorphic at all cusps, rational `q`-expansion) and every Heegner form `Q` of
level `N` and discriminant `D`, `g(τ_Q) ∈ ringClassFieldD D`. Source: main theorem of CM plus the
rational structure of `X₀(N)` (Shimura 1971 Thm. 5.7, Prop. 6.9; Gross 1984 §1–3; Cox Thm. 11.1;
theorem numbers UNVERIFIED; refereed). No Heegner condition is needed, and the leaf does not
mention x0-32's eta model. Checked numerically for `g = x` at D = −28, −60, −320.

**Also proved.** All axioms are `propext, Classical.choice, Quot.sound`;
`lake build ZInQKernel.Contrib.TYZGenus.ShimuraFricke` OK.
* x0-32's leaves **`X0.EtaModelInvariant`** (`etaModelInvariant`), **`X0.EtaModelEquation`**
  (`etaModelEquation`) and **`X0.EtaModelFricke`** (`etaModelFricke`). Ingredients: the eta
  identity `xC_eq_even : x = η(16τ)⁶/(η(8τ)²η(32τ)⁴)` (from gz-theta's Jacobi triple product),
  `etaSqExp_closed` (gz-theta's η² multiplier is Petersson's polynomial mod 12), and the theta
  duplication formulas `theta_dup_zero`, `theta_dup_half`, `theta_dup_half_sign`.
* `etaCuspGrowth`, `xQExpRational`, `yQExpRational`: x and y are meromorphic at every cusp and
  have rational q-expansions.
* `cmValueRingClass_of_modFn : ShimuraReciprocityModFn → CMValueRingClass`;
  `shimuraReciprocityPic_of_shimuraModFn : ShimuraReciprocityModFn → ShimuraReciprocityPic`;
  `cmFieldTYZ_of_cmValueRingClass`; `tyzThm35ReadingA_of_cmValueRingClass` (TYZ Thm 3.5 reading A
  from the three 𝓛-leaves, `CMValueRingClass`, `TYZSigmaFixesZn`, `Lemma318Literal` and
  `GenusPointLeafCM`).

**For cm-numeric (TYZSigmaFixesZn; not continued here).** `ShimuraZn.lean` (an earlier run of this
task, unchanged) proves `tyzSigmaFixesZn_of : ShimuraReciprocityPic → X0.EtaModelFricke →
TYZSigmaFixesZn`. With this run's results,
`fun hS => tyzSigmaFixesZn_of (shimuraReciprocityPic_of_shimuraModFn hS) etaModelFricke :
ShimuraReciprocityModFn → TYZSigmaFixesZn` type-checks (`scratch/tyz-cm/ax9.lean`). It is not
added to a Contrib file because that target now belongs to cm-numeric.

**Remains unproved.** The textbook leaf `CMValueRingClass` (or the stronger Gross-form
`ShimuraReciprocityModFn`). Caveats: TYZ's reading A is not refereed; TYZ was read in arXiv v1
only; `z_n = (1 − [i])f₀(P_n)` comes from tyz-t1 (AI-derived, numerically checked).

New files: `ZInQKernel/Contrib/TYZGenus/Shimura{Recip,Zn,Field,ModFn,QExp,Cusp,Main,EtaInv,Theta,
ThetaDup,Fricke}.lean`. Report: `docs/research/tyz-cm.md`. Log: `scratch/tyz-cm/log.md`.
