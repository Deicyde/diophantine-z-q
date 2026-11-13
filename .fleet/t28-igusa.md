# t28-igusa (fleet summary)

**Main result.** Leaf T28 (`PkgI1.IgusaClebschSeparation`, copied verbatim) is **not closed**,
but it is now reduced in Lean to two concrete statements. In `scratch/t28-igusa/Igusa.lean`
(sorry-free; `#print axioms` = `propext, Classical.choice, Quot.sound` for every theorem below):

- `igusa_forward`: the `⇒` direction (transformation law `J_{2k}(e·f|M) = (e·det M³)^{2k}J_{2k}(f)`)
  over any field of characteristic 0. Method: explicit action, cocycle identity, Bruhat
  decomposition into diag/swap/translations, and for translations the derivation trick
  (`d/dt J(f(x+t)) = (DJ)(f(x+t))`, `DJ = 0` by `ring`).
- `igusaClebschSeparation_iff`: T28 ⇔ `IgusaSeparationEq` (equal invariants, no weighted scaling).
- `T28SO3.so3`: `SO(3) = PGL(2)` for binary quadratics.
- `mestre_abstract`: Mestre's separation step without the reconstruction identity.
- `separation_generic`, `igusaClebschSeparation_of : M3Identities → SeparationSpecial → T28`.
- M3 (the Gram matrix of Clebsch's covariants `y₁, y₂, y₃` and `p6 f (yᵢyⱼyₖ)` as polynomials in
  `J₂..J₁₀`): found by computer algebra (interpolation on 45 sextics, 15 fresh checks), and
  eight of the sixteen (all six Gram entries, `a₁₁₁`, `a₁₁₂`) proved in Lean by `ring`.

**Route chosen for `⇐`:** Mestre 1991 + Cardona–Quer 2005 (constructive, no GIT); comparison with
Igusa's GIT route and the Rosenhain/Galois route in `docs/research/t28-igusa.md` §2.

**What remains.** (R1) the rest of `M3Identities` (eight cubic identities `a₁₁₃ … a₃₃₃`, too large for direct `ring`; plan: covariance of `yv` by the
same generator technique, then check on a 3-parameter normal form); (R2) `SeparationSpecial`, the
`⇐` statement on the locus `det yv = 0` (curves with an extra involution; Bolza 1888,
Cardona–Quer 2005): unproved, the main open part. Recommendation: list `SeparationSpecial` in
place of T28, plus `M3Identities` as glue.

Files: `docs/research/t28-igusa.md`, `scratch/t28-igusa/` (`Igusa.lean`: full check 8m47, no errors; `log.md`; CAS scripts).
