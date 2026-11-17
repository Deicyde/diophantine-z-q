# pb-bypass: the research field `r11r12` (`PkgI4.PanBerger`) split into Pan's and Berger's printed theorems

Task pb-bypass, 2026-11-15. Base 9a100aa7 (leaf-fold22). Lean: `ZInQKernel/Contrib/OneProof/PanBerger.lean`
(the contribution), `scratch/pb-bypass/FontainePst.lean` (its first version), `scratch/pb-bypass/Weakest.lean`
(the weakest consumer form). Results log: `scratch/pb-bypass/log.md`. Fold spec: `scratch/pb-bypass/autofold.json`.
Model work, no human review.

Marks: **VERIFIED** (compiled here, or read in a named file), **STANDARD** (published, exact reference),
**UNVERIFIED** (a theorem number or locator from memory or from earlier reports; this host has no network).

## 1. Result

**`r11r12` is a theorem from two published-form leaves.** The field was rated composite GLUE, "not
splittable: no `B_st` in Mathlib" (hodge-split). This task defines Fontaine's period rings `A_cris`,
`B_cris^+`, `B_cris`, `B_st` over Mathlib's `A_inf = W(𝓞_ℂ_p♭)` and Fontaine's `θ`, with the action of
`G_{ℚ_p}`, and Fontaine's potentially semistable representations (`LocalIsPst`). With them, pkg-I4's two
templates become genuine statements and compose:

```lean
theorem HDec.PkgI4.PanBergerSplit.panBerger_of_printed
    (hP : PanPrinted) (hB : BergerPrinted) : HDec.PkgI4.PanBerger
```

* `PanPrinted := PanFor LocalIsPst`: Pan, J. Amer. Math. Soc. 35 (2022), Theorem 1.0.4, `p ≥ 5`
  (statement read in arXiv:1901.07166v2 by h-a011 §1.1 and the locator audit; JAMS number UNVERIFIED).
* `BergerPrinted := BergerDR LocalIsPst`: Berger, Invent. Math. 148 (2002), Théorème 0.7 (read in the
  author copy of the published version by the locator audit; = arXiv v3 Thm 0.6 = Thm 5.19).

`lake env lean ZInQKernel/Contrib/OneProof/PanBerger.lean` compiles with no error and no warning; the axioms
of `panBerger_of_printed` and of the sanity theorem `isPst_trivial` are `propext`, `Classical.choice`,
`Quot.sound` (VERIFIED). `#discharges` reports `DISCHARGES [OpenResearchLeaves21.r11r12] by
HDec.PkgI4.PanBergerSplit.panBerger_of_printed`, still assuming exactly the two leaves (§5). Counts if folded
(autofold spec `scratch/pb-bypass/autofold.json`, dry run VERIFIED: its TailZ35 compiles): strict
**46/10 → 48/9**, strictest **45/11 → 47/10** (the composite GLUE row `r11r12` leaves; two published rows
enter, flagged unread).

**The field cannot be removed by other fields (§3), and its only consumer uses it at `p = 5` (§2).**

## 2. Consumers and instances (VERIFIED by grep and reading)

* Every occurrence of `.r11r12` in `ZInQKernel/` is a bundle-to-bundle assignment except one:
  `HDec.G0Galois.g8_g12_of_leaves3` (`OneProof/H/TailD.lean` l. 139) passes it to `g8_g12`
  (`TailA.lean` l. 2255), which passes it to `g12` (`TailA.lean` l. 2211). `g8_g12_of_leaves3` is called once,
  by `HSyn.G0AssembleMod.afterG7_of3` (TailD l. 171), on the route to `sixContactMin_of_open28` and
  `ZInQ.OneProof.frozenTarget`.
* `g12` applies it once (TailA l. 2220): `hPB 5 (le_refl 5) r hirr (finitelyRamified_of_g11 h11) h9.1 h10
  ⟨0, -1, _, h9.2⟩`. So the only instance is **`p = 5`**, `ρ = r₅ : GaloisRep 5 2`, the 2-dimensional
  constituent of the QM abelian surface `A` over the descent field `L'` (`L'/ℚ` Galois, `dim A = 2`,
  `V₅(A) ⊗ ℚ̄₅ ≅ r₅|_{G_{L'}} ⊕ r₅|_{G_{L'}}`; h-trust C1, C7). Its hypotheses come from G8 (irreducible),
  G11 (finitely ramified), G9 (`LocalIsDeRham`, Hodge–Tate weights `{0, −1}`) and G10 (odd).
* **Weakest needed form:** `G0Galois.PanBerger5` (scratch/pb-bypass/Weakest.lean), `PanBerger` at `p = 5`;
  `g12_of_panBerger5` is `g12` verbatim with `hPB : PanBerger5`, and `panBerger5_of_panBerger` is the
  restriction (both compile, standard axioms; VERIFIED). Pan's theorem has no residual proviso at `p = 5`. The weaker form is
  not used in the fold: the split proves the field as stated, which keeps the fold mechanical (autofold) and the
  leaves in their printed generality (`p ≥ 5`).

## 3. Why no other field gives it (STANDARD)

The fields that could be combined are Faltings (R9a/b), the de Rham comparison (R10), Néron–Ogg–Shafarevich
(R7a), Eichler–Shimura (R16 / `R16CoreY`), Raynaud (R6) and the Tate-module and CM leaves. All of them go from
modular forms to Galois representations or describe local properties; none gives the modularity of a
2-dimensional representation of `G_ℚ`, which is what Pan supplies. `r₅` is not induced from a Hecke character:
the route is on the NoCM branch, `End⁰(A_Q̄) = B` is the indefinite quaternion division algebra of
discriminant 6, so Hecke's theorem does not apply. The instance does not make the field vacuous either: every
hypothesis of Pan is met by `r₅` (h-a011 §3, h-trust C7). The other modularity route (route K,
Khare–Wintenberger with Ribet or Kisin 2009 Cor. 0.3; h-decomposition §1) replaces more than this field and
needs Weil restriction of abelian varieties, which the project cannot construct today.

## 4. The definitions (`ZInQKernel/Contrib/OneProof/PanBerger.lean`, namespace `HDec.PkgI4.PanBergerSplit`)

Sources: Fontaine, Astérisque 223 (1994), Exp. II §§2-3; Brinon–Conrad, CMI notes (2009), §§9.1-9.2 and §6.1
(numbers UNVERIFIED). Every object is built from Mathlib's `PreTilt`, `WittVector`, `fontaineTheta`,
`AdicCompletion`, `Localization`, `Polynomial` and pkg-I4's `oAct`, `DR.locMap`, `DR.adicMap`, `qpToLoc`.

| object | Lean | definition |
| --- | --- | --- |
| `A_inf`, `A_inf[1/p]`, `θ` | `Ainf`, `AinfP`, `theta` | `W(𝓞_ℂ_p♭)`, `Localization.Away p`, `WittVector.fontaineTheta` |
| `γ_n(x) = x^n/n!` | `dpow` | `qpToLoc (n!)⁻¹ · x^n` in `A_inf[1/p]` |
| `A_cris^0` | `Acris0` | `Subring.closure (A_inf ∪ {γ_n(x) : θ x = 0})` in `A_inf[1/p]` (the divided power envelope) |
| `A_cris` | `Acris` | `AdicCompletion (span {p}) Acris0` |
| `B_cris^+` | `BcrisPlus` | `Localization.Away (p : Acris)` |
| `log [ε]` | `logT` | the `p`-adic limit of `Σ_{1≤j≤N} (-1)^{j+1}(j-1)! γ_j([ε]-1)`: the `n`-th component is the partial sum to `p^n`; the remaining terms lie in `p^n A_cris^0` since `p^n ∣ (j-1)!` (`logPartial_cauchy`, proved) |
| `B_cris = B_cris^+[1/t]` | `Bcris` | localization at the monoid generated by all `log [ε]`, `ε^♯ = 1`, `ε ≠ 1` (each is `a·t`, `a ∈ ℤ_p ∖ 0`; `p` is a unit; no choice of `t`) |
| `B_st = B_cris[u]` | `Bst` | `Polynomial Bcris` |
| `G_{ℚ_p}` on `A_cris^0`, `A_cris`, `B_cris^+`, `B_cris` | `acris0Act`, `acrisAct`, `bcrisPlusAct`, `bcrisAct` | by functoriality from `oAct σ` on `𝓞_ℂ_p`; proved: `A_cris^0` is stable (`θ` natural), `σ(log [ε]) = log [σ♭ ε]` (`acrisAct_logT`), the `t`-generators are permuted (`tMonoid_le_comap`), `ℚ_p` is fixed (`bcrisAct_qp`) |
| `G_{ℚ_p}` on `B_st` | `stAct` | coefficients by `bcrisAct`, `σ(u) = u + log [u_σ]`, `u_σ = σ(p♭)/p♭` (so `σ(u) = u + c(σ)t`, `c` the Kummer cocycle); `p♭` a chosen element with `(p♭)^♯ = p` |
| `D_st,K(V^∨)` | `dstSpace K ρ` | `G_K`-equivariant `ℚ_p`-linear maps `E^n → B_st` (the convention of pkg-I4's `ddrSpace`) |
| `K_0 = B_st^{G_K}` | `bstInv K` | the `G_K`-invariants of `B_st` |
| semistable over `K` | `IsSemistableOver K ρ` | `dim_ℚp D_st,K = dim_ℚp K_0 · n[E:ℚ_p]` |
| potentially semistable | `IsPst ρ`, `LocalIsPst p n ρ` | semistable over some finite `K ⊆ ℚ̄_p`; `ℚ̄_p`-valued: values in a finite `E`, as `LocalIsDeRham` |

Checks. Proved unconditionally: the trivial representation is semistable over every `K`
(`isSemistableOver_trivial`, `D_st,K(ℚ_p) ≅ B_st^{G_K}`) and potentially semistable (`isPst_trivial`). Not
proved, as for pkg-I4's `IsDeRham`: `B_st^{G_K} = K_0`, `B_cris ≠ 0`, the action being a group action. A
definitional slip that made `B_cris` the zero ring would make every representation potentially semistable and
`PanPrinted` stronger than Pan's theorem, so the statement check of the two leaves should read the definitions
of §4 against Fontaine's (pages-wanted).

Two choices are made with `Classical.epsilon`: `p♭` and `u_σ`. Both exist (`ℂ_p` is algebraically closed;
`𝓞_ℂ_p♭` is a domain and `(σ(p♭)/p♭)^♯ = 1`), and a different `p♭` gives an isomorphic `G_{ℚ_p}`-ring
(`u ↦ u + log [p♭'/p♭]`). `logU` takes the value 0 if `u_σ^♯ ≠ 1`, which does not occur.

## 5. The leaves and their rating

| leaf (bundle field) | Lean type | printed form? | reason |
| --- | --- | --- | --- |
| `panPrinted` | `PkgI4.PanBergerSplit.PanPrinted` | **yes** (consequence of the printed statement, applied to `ρ^∨`) | Pan Thm 1.0.4 for `p ≥ 5` with Fontaine's pst; the conventions are those of `PanBerger` itself: `LocalIsPst`, `LocalIsDeRham` and `DistinctHTWeights` are computed on `Hom_G(V, B)`, i.e. on `V^∨`, so the leaf is Pan's theorem for `ρ^∨` (whose underlying `ℚ_p`-representation is `V^∨`; irreducible, finitely ramified and odd exactly when `ρ` is) and the trace-form conclusion transfers by `ρ ≅ ρ^∨ ⊗ det ρ` (pkg-I4 note §2.1, h-trust C8). JAMS number UNVERIFIED. |
| `bergerPrinted` | `PkgI4.PanBergerSplit.BergerPrinted` | **yes** | Berger Thm 0.7 (no dimension, oddness or residual hypothesis), applied to `V^∨`; a `ℚ̄_p`-valued `ρ` with values in `GL_n(E)` is the `ℚ_p`-representation `E^n` (locators.md R11: "finite coefficient-field extension needs restriction of scalars", which `LocalIsPst` does). Springer pagination UNVERIFIED. |

Both are flagged "unread: new printed leaf over pb-bypass's B_cris/B_st definitions".

`#discharges` (VERIFIED, `scratch/pb-bypass/discharges-output.txt`; the other five lines it prints are
contributions already in the tree):

```
DISCHARGES [OpenResearchLeaves21.r11r12] by HDec.PkgI4.PanBergerSplit.panBerger_of_printed
  still assumes: [HDec.PkgI4.PanBergerSplit.PanPrinted, HDec.PkgI4.PanBergerSplit.BergerPrinted]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 63 open hypotheses, 1716 theorems checked, 6 discharge one
```

## 6. Reproduce

```
lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.PanBerger
lake env lean scratch/pb-bypass/Discharges.lean
python3 scripts/one_proof/autofold.py scratch/pb-bypass/autofold.json --dry-run   # strip line 1, lake env lean it
```

## 7. What remains

* A statement check of `panPrinted` and `bergerPrinted` against the print, including the definitions of §4.
* Optional sanity theorems: `B_cris ≠ 0` (e.g. through `A_cris → B_dR^+`), the action property of `stAct`.
* The fold itself (integrator).
