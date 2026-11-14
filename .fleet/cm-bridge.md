# cm-bridge (2026-11-13)

**Headline (compiles, standard axioms only; `scratch/cm-bridge/Bridge.lean`, 0 errors):**

```lean
theorem tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First_lemma321Five
    (h11 : TYZThm11Integral) (h1 : TYZLcalOne) (h29 : TYZLemma29Mod2)
    (hS : Shimura.ShimuraReciprocityModFn)
    (h318 : Lemma318Literal HHprime) (h35 : ∀ ℓ, IsTYZLcal ℓ → Thm35First ℓ tyzZ)
    (h5 : Lemma321Five) : ZInQ.Literature.TYZThm35ReadingA
```

So TYZ reading A rests on: the three 𝓛-leaves, **one textbook CM leaf** (tyz-cm's `ShimuraReciprocityModFn`,
the main theorem of CM for modular-function values at Heegner points), and three TYZ results (Lemma `torsion2`,
Thm 3.3/3.5 for the pinned genus points, Lemma 3.21(1)). This needs tyz-cm's branch, which is merged here
(0ad48a7d). It proves EtaModelFricke/Invariant/Equation and derives CMFieldOfDefinition, TYZSigmaFixesZn,
ShimuraReciprocityPic and CMValueRingClass from ShimuraReciprocityModFn.

**New in this task:**
- cm-numeric's file rewired to ring-class. `IInH4`, `HprimeNormal`, `IInHprime`, `CMFieldOfDefinitionTYZ`,
  `CMFieldOfDefinition7` and `TYZSigmaFixesZn` are gone.
- **`GenusFieldLeLni` proved**, via Bauer + genus characters + QR.
- **TYZ Lemma 3.21(4) derived from TYZ Thm 3.6(3)**. All glue is proved: the genus field is K(√p*) (Bauer);
  Artin symbols act on √p* by the genus characters (`artinPstarChi`); N𝔭₂ = 2.
- **TYZ Thm 3.6(3) derived** (`tyzThm36Seven_of`) from ShimuraReciprocityPic + EtaModelFricke + CMAlgebraic.
  The ingredients are Gross-style lattice identities with J = 𝔭̄₂^5 = (32, ū), Q' = [32, δ, (n+δ²)/128], and the
  Fricke step. `cmAlgebraic_of_cmValue` derives CMAlgebraic from tyz-cm's CMValueRingClass.

**Review finding (fixed).** An independent review found that the first TYZThm36Seven used an unoriented 𝔭₂,
so it depended on the arbitrary `embed n` and was false for one orientation. 𝔭₂ is now oriented through ιC.
Numerics: `thm36_7.out` (12/12 pass; the wrong sign fails 7), `plan36.out` (8/8).

**Remaining / not done.**
- `Lemma321Five` would need: a β₁-lift existence glue (Kummer theory), genus theory for H'_n (genus characters
  on Pic(𝒪_{n,4})), and a pinned TYZ 3.6(1).
- `Lemma318Literal` would need division-field ramification and supersingular reduction mod p.
- `Thm35First`, and the 𝓛-leaves.

Final check: Bridge.lean 0 errors, 32 audited declarations all standard axioms (`audit-out.txt`).
Report: `docs/research/cm-bridge.md`; log: `scratch/cm-bridge/log.md`.
