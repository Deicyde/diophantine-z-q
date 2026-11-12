# pkg-I4: modularity package (h-trust C3-C5, C7-C9, D5) — fleet report

Note: `docs/research/pkg-I4.md`. Lean: `scratch/pkg-I4/I4.lean` (about 1450 lines; Mathlib only;
compiles with `lake env lean`; **no `sorry`**; every `#print axioms` gives `propext`,
`Classical.choice`, `Quot.sound`). Log: `scratch/pkg-I4/log.md`.

**Main result.** p-adic Hodge theory no longer blocks stating I4. Over Mathlib v4.35 the file
builds two predicates that wk-h and hdec-faithful had rated "large":
- **Hodge–Tate weights.** `G_{ℚ_p}` acts on `ℂ_[p]`; multiplicities are computed with Tate–Sen
  `(ℂ_p(i) ⊗ V)^G`, in N5's and Pan's convention.
- **de Rham.** The `G_{ℚ_p}`-action on Mathlib's `BDeRham 𝓞_ℂ_[p] p` comes from functoriality,
  with `ℚ_p ⊆ B_dR` fixed. Inputs proved along the way:
  - `𝓞_ℂ_[p]` is `p`-adically complete (the instance was missing, so `BDeRham` did not typecheck
    before);
  - `untilt` and Fontaine's `θ` are natural;
  - maps of adic completions exist, and generators of `ker θ` go to generators.
  Then `D_dR` and `IsDeRham`, with versions over `G_F` for finite `F/ℚ_p`. About 420 lines.
- **Conditional sanity checks (proved).** Given Tate's theorem, `ℚ_p(1)` has weight exactly `−1`.
  Given `B_dR^G = ℚ_p`, the trivial representation is de Rham.

**Leaves statable now (8, `def … : Prop`, compiled; none proved).**
- `PanBerger`: Pan 2022 Thm 1.0.4 with "de Rham" in place of "pst", a consequence of Pan with
  Berger. No `B_st` needed. The conclusion is in trace form, which is implied in either
  Frobenius normalization.
- `DeRhamComparison` (C3): `V_p(A)` is de Rham with HT weights `0^g, (−1)^g`. Stated over
  pkg-I3's abelian varieties and Tate modules, copied into the file.
- `EigenformHT`: weights `{0, 1−k}` at every level.
- `EigenformRepExists`, `DeligneSerreFinite`, `EigenformTwist`.
- `NewformOfEigenform` (Li): newforms defined through the old space.
- `CarayolUnramified`.

**Templates (not leaves).** `PanFor IsPst`, `BergerDR IsPst`, `CarayolFor a`. Glue proved: the C8
weight arithmetic in both normalizations.

**Not statable.**
- C5: the Betti comparison.
- Shimura's `A_f`, which needs `J₁(N)` over `ℚ`.
- The general Carayol, which needs the `ℓ`-adic Artin conductor; glue-conductor's L8 needs it
  too.

**Corrections to earlier notes.**
- Pan assumes *potentially semistable*, not de Rham.
- HT and de Rham are cheap over Mathlib, not "large".

**Coarse alternative (Ribet + Pyle + Khare–Wintenberger).** Sound for modularity; it removes C3-C5,
C7 and half of C8 from the trust base. It gives no level bound: B1-B3, D1-D5 and C9 stay. It is
not more statable than Pan's route now. Its statements are recalled, not read.

**Biggest obstacle.** `J₁(N)` as an abelian variety over `ℚ` (C9, then E1), and the `ℓ`-adic
conductor (D5). Also unchecked: that `ker θ` is principal (a Mathlib TODO), which makes `BdR` the
classical `B_dR`. If it failed, the predicate would mean something else, and the leaves would no
longer state what they are meant to.
