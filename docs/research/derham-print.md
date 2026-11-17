# derham-print: `deRhamH1AbVarT` from printed leaves, and the `B_dR^+[1/t]` dictionary in Lean

Task derham-print, 2026-11-16/17, base `origin/main` `c1e4ed1b8` (leaf-fold32 blueprint; `origin/wip/integrate-w82`
already contained). Log: `scratch/derham-print/log.md`.

## Verdict

The research field `deRhamH1AbVarT` (`ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT`, rated *consequence*, GLUE) is
**proved in Lean** from two printed-form leaves and the existing textbook field `mumfordTorsionAlgClosed`:

```
DeRhamPrint.deRhamH1AbVarT_of_leaves
  (hdR : DeRhamPrint.DeRhamVpAbVarPrinted)    -- Fontaine: V_p(A) is de Rham (printed D_dR)
  (hB  : DeRhamPrint.BdRInvariantsPrinted)    -- Fontaine: B_dR^{G_K} = K (dimension form)
  (hM  : AvSplit.MumfordTorsionAlgClosed)     -- textbook field already in the bundle (only for dim V_p A < ∞)
  : ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
```

Effect of the fold (`scratch/derham-print/autofold.json`): GLUE −1 (strict and strictest), leaf count +1 (the
field becomes two leaves).

The task also asked for the dictionary from the printed period ring to the kernel's `B_dR`. OPEN.md's kernel-wide
B_dR reading left one gap: a print that defines `B_dR = B_dR^+[1/t]`, `t = log[ε]`, could not be matched,
because `t` was not constructed and `t ≠ 0` was not proved. This task closes that gap in Lean
(`ZInQKernel/Contrib/OneProof/DeRhamPrintTDict.lean`, no `sorry`, standard axioms):

* `TDict.tt p Z`: Fontaine's `t = log[ε]` in the kernel's `B_dR^+`. It is the `ξ`-adic sum of
  `Σ_{n≥1} (-1)^{n+1}([ε]-1)^n/n` (`logPlus`). The limit exists by bdr-kertheta's completeness and is unique
  (`logPlus_unique`). This holds for every compatible system `ε` of `p`-power roots of unity with `ζ_p ≠ 1`
  (`RootSystem`), and such a system exists (`rootSystem`).
* `TDict.tt_eq_varpi_mul_unit`: **`t = ξ · unit`**, so `t ≠ 0`.
* `TDict.bdREquivAwayT`: **`B_dR ≅ B_dR^+[1/t]` as `B_dR^+`-algebras**. With it, `ext_of_extends` and
  `transport_extends` show that the Galois action on `B_dR^+[1/t]` (the extension of the action on `B_dR^+`) is
  the transport of the kernel's action.

So all three printed definitions of `B_dR` (`Frac(B_dR^+)`, `B_dR^+[1/ξ]`, `B_dR^+[1/t]`) are now matched to the
kernel's `B_dR` by proved lemmas. The last sentence of OPEN.md's B_dR reading ("a statement read through that
definition is GLUE") can be dropped.

The printed theorems the task names for this row (Faltings 1989, Tsuji 1999, Scholze 2013 Cor. 1.8) **cannot be
stated over genuine definitions in Lean today**: Mathlib has no étale cohomology, no algebraic de Rham cohomology
and no rigid-analytic spaces (§2). The new leaf is therefore Fontaine's theorem in its Tate-module form, which is
printed (Berger 2004, §I.3, as h-leaves records it) and needs neither `H¹_ét` nor rigid spaces. Duality is the
price, and it is paid by a Lean proof plus the second leaf `B_dR^{G_K} = K`.

## 1. What the consumers need (VERIFIED, grep and reading)

* The field is read in exactly one place: `TailX.lean:195`, `deRhamComparisonHT_of_leavesT r.hodgeTateDecompAbVar
  l.tateTwistInvariants l.axSenTate r.deRhamH1AbVarT`. All other occurrences are bundle-to-bundle copies in
  `TailZ*`.
* `deRhamComparisonHT_of_leavesT` (TailS l. 2059) converts it, by hodge-split's `isDeRhamOver_iff_tensor_dual`,
  to `IsDeRhamOver p (A.galRep p)`, i.e. `dim_{ℚ_p} Hom_{G_F}(V_p A, B_dR) = [F:ℚ_p] · dim V_p A`. This is the
  de Rham clause of R10 (`DeRhamComparisonHT`).
* Downstream, `PkgI4.DeRhamComparison` is the argument `hR10` of `G9GlueNoT23` (TailA l. 2017). Its output
  `G9Out` contains `LocalIsDeRham` (TailA l. 1948), so the clause is genuinely consumed: G9 needs `r₅` de Rham at
  5, for Pan's theorem through Berger.
* So the consumers need **only the dimension of `D_dR`**: no Hodge filtration and no identification of `D_dR` with
  `H¹_dR`. The leaves state only that. `DeRhamPrint.isDeRhamOver_of_leaves` gives the consumer's form directly.
* No overlap with other tasks. hodgetate-from-dr consumes `hodgeTateDecompAbVar`, not this field, and
  claims.tsv has no row for it. dict-galois (`origin/wip/dict-galois` 81d1f67f) had proved the field from the
  same two statements. Leaf-fold32 did not fold that part (it took only r7a), and the B_dR reading added after
  it made a `[1/t]` print a step. This task reuses dict-galois's generic duality proof unchanged (credited in the
  file header) and supplies the missing dictionary.

## 2. The printed theorems, and the steps from each print to the field

| print | statement (as printed) | steps to the field | statable in Lean today? |
| --- | --- | --- | --- |
| Scholze, Forum Math. Pi 1 (2013), Cor. 1.8 (wording VERIFIED by h-leaves §3.1 in arXiv:1205.3463) | proper smooth **rigid-analytic** `X/k`: `H^i(X_ét, ℚ_p)` is de Rham, with filtered `H^i_dR(X)` | (S1) `A^an` is proper smooth rigid; (S2) `H¹((A^an)_ét) = H¹_ét(A_{F̄})` (algebraic–analytic comparison, Scholze Thms 9.1/9.3 or Huber); (S3) `H¹_ét(A_{F̄}, ℚ_p) = Hom(V_p A, ℚ_p)` (Milne 1986 Thm 15.1(a), UNVERIFIED); (S4) dimension count; (S5) `B_dR` dictionary | no (no rigid spaces, no étale cohomology) |
| Faltings 1989 (Johns Hopkins volume), de Rham comparison | proper smooth `X/K`: `H^i_ét(X_{K̄}, ℚ_p)` de Rham, `D_dR = H^i_dR(X/K)` | S3, S4, S5 | no (no étale cohomology, no `H_dR`) |
| Tsuji, Invent. Math. 137 (1999) | `C_st` for semistable `X` | de Jong alterations, `C_st ⇒ C_pst ⇒ C_dR`, then S3–S5 | no |
| **Fontaine (Berger 2004 §I.3)** | the Tate module `V_p(A)` of an abelian variety is de Rham | S5 (proved here), `dim_F → dim_{ℚ_p}`, then **duality** `V → V^∨` (Lean proof + leaf `B_dR^{G_K}=K`) | **yes**: `DeRhamVpAbVarPrinted` |

Every step of the last row is proved in Lean or is definition-level:

1. **Period ring** (S5). Berger's `B_dR = B_dR^+[1/t]` is matched by `TDict.bdREquivAwayT`. Fontaine's
   `Frac(B_dR^+)` is matched by `isFractionRing_BDeRham` (bdr-kertheta), and a `B_dR^+[1/ξ]` print by
   `bdREquivAway`. The construction of `B_dR^+` itself is the print's: OPEN.md, definition-level.
2. **Galois action on the period ring.** The print's action on `B_dR^+[1/t]` extends the action on `B_dR^+`. It is
   the transport of the kernel's action (`ext_of_extends`, `transport_extends`), because pkg-I4's `bdrAct σ` is
   by definition `IsLocalization.map (bdrPlusMap σ)` (I4Layer l. 403, l. 1000). The one-line instantiation
   at `bdrAct` does not elaborate, because pkg-I4's `DR.genMonoid` is a `def` while KerTheta's `genMonoid` is an
   `abbrev` (instance search fails across the two). The generic lemma is proved and the instantiation is
   definitional.
3. **`G_K` versus `G_F`.** The print takes `K ⊆ ℚ̄_p` and `G_K ⊆ G_{ℚ_p}`. The kernel takes any finite `F/ℚ_p`
   with `G_F` acting through `gfToGqp`, whose image is `G_{F'}` for `F' ⊆ ℚ̄_p` the image of `F`
   (`HodgeSplit.range_gfToGqp_eq`, proved). This is the pkg-I4 convention, already used by every p-adic Hodge
   leaf of the bundle.
4. **`dim_K` versus `dim_{ℚ_p}`.** `D_dR(V)` is a `K`-space and `dim_{ℚ_p} D_dR = [K:ℚ_p] · dim_K D_dR`. The leaf
   states the right-hand side as an equation in `ℚ_p`-dimensions (hodge-split's `IsDeRhamTensorOver`).
5. **Duality** (`V_p(A)` de Rham ⇒ `V_p(A)^∨` de Rham). This is the Lean proof `Gen.finrank_Hsp`, for any field
   `B` with a semilinear action and `dim B^G = d > 0` (dict-galois), instantiated at `B_dR` (a field,
   bdr-kertheta) with `d = [F:ℚ_p]` from the leaf `BdRInvariantsPrinted`. hodge-split's
   `isDeRhamOver_iff_tensor_dual` then gives the field's tensor form.
6. **`dim V_p(A) < ∞`**, from T26 (proved from `mumfordTorsionAlgClosed` through `AvSplit.Final.h25` and
   `T5Torsion.TateFree`).

## 3. The new leaves and their ratings

| leaf (bundle `OpenResearchLeaves`) | Lean | rating | reason |
| --- | --- | --- | --- |
| `deRhamVpAbVarPrinted` | `DeRhamPrint.DeRhamVpAbVarPrinted`: `∀ p F A, IsDeRhamTensorOver p (A.galRep p)` | **printed form** (unread) | Fontaine's statement "the Tate modules of abelian varieties are de Rham". The printed `D_dR(V) = (B_dR ⊗ V)^{G_K}` is used, read through `dim_{ℚ_p} = [K:ℚ_p] dim_K`. Berger's `B_dR^+[1/t]` is matched by a proved iso. Locator: Berger 2004 §I.3 (wording recorded by h-leaves §3.2, VERIFIED there); primary Fontaine, Ann. of Math. 115 (1982) / LNM 1016 (1983), statement numbers UNVERIFIED. Not stronger than the print: it is the print for every `F` and `A`. |
| `bdRInvariantsPrinted` | `DeRhamPrint.BdRInvariantsPrinted`: `∀ p F, finrank ℚ_p (bdrFix p F) = [F:ℚ_p]` | **printed form, dimension** (unread) | A consequence of the printed equality `B_dR^{G_K} = K`, obtained by taking `ℚ_p`-dimensions, so no embedding `F → B_dR` is needed to state it. Locator: Fontaine, Astérisque 223 (1994) Exp. II; Brinon–Conrad CMI notes §4.3–4.4. Both UNVERIFIED (no source on this host). |

The two statements are, word for word, dict-galois's `DeRhamDict.DeRhamVpAbVarT` and
`DeRhamDict.BdRInvariantsOver`, so one statement check covers both. Proposed rows for `docs/research/locators.md`
(not added: the file belongs to the locator audit):

* `deRhamVpAbVarPrinted`: Berger, *An introduction to the theory of p-adic representations*, Geometric aspects of
  Dwork theory (de Gruyter 2004), §I.3; Fontaine, Ann. of Math. 115 (1982), 529–577; Fontaine, LNM 1016 (1983),
  86–108. Numbers UNVERIFIED.
* `bdRInvariantsPrinted`: Fontaine, *Le corps des périodes p-adiques*, Astérisque 223 (1994), Exp. II;
  Brinon–Conrad, *CMI summer school notes on p-adic Hodge theory* (2009), §4.3–4.4. Numbers UNVERIFIED.

## 4. The dictionary proof (`DeRhamPrintTDict.lean`)

* `mkSeq`, `untilt_mkSeq`: an element of `𝓞_ℂ_p♭` from a compatible sequence, with `x♯ = z₀` (generalizing
  bdr-kertheta's `untilt_pFlat`).
* `norm_p_le`: `‖p‖ ≤ ‖1 - ζ_{p²}‖^{p(p-1)}`, from `Φ_{p²}(1) = p`, the product over primitive roots, and
  `‖1 - ζ^k‖ ≤ ‖1 - ζ‖`.
* `norm_untilt_pow_ge`, `pFlat_dvd`: `p♭ = (ε^{1/p} - 1)^{p-1} · d` in the tilt. This uses
  `root(ε^{1/p}-1, 1) ≡ ζ_{p²} - 1 (mod p)` with `‖ζ_{p²} - 1‖ > ‖p‖`, and `dvd_of_norm_le` (bdr-kertheta's
  `dvd_of_coeff_zero` generalized). Level 1 is used, not level 0, so that `p = 2` is included.
* `ker_theta_eq_omega`: `ker θ = (ω)`, `ω = Σ_{i<p} [ε^{1/p}]^i`, by bdr-kertheta's Nakayama criterion
  `ker_eq_span_of_mod_p`, since `[(ε^{1/p}-1)^{p-1}] ≡ ω (mod p)` (`Σ e^i = (e-1)^{p-1}` in characteristic `p`).
* In `B_dR^+`: `[ε] - 1 = ω · ([ε^{1/p}] - 1)`, where `[ε^{1/p}] - 1` is a unit (`θ = ζ_p - 1 ≠ 0`) and
  `ω ∉ (ξ²)` (because `ξ ∈ (ω)` in `W(𝓞♭)`). Hence `[ε] - 1 ∈ (ξ) \ (ξ²)`. Then `log(1+x) - x ∈ (ξ²)` gives
  `t ∈ (ξ) \ (ξ²)`, i.e. `t = ξ · unit`.
* `isFractionRing_away_tt` and `bdREquivAwayT`: `B_dR^+[1/t]` is the fraction field of the DVR `B_dR^+`, so it is
  isomorphic to the kernel's `B_dR` over `B_dR^+`.

`σ(t) = χ(σ) t` is not proved and is not needed for the dictionary: the action on `B_dR^+[1/t]` is determined by
the action on `B_dR^+`. Proving it would also remove the second leaf, via `V^∨ ≅ V(-1)` (Weil pairing) and
multiplication by `t`. That needs `σ[ε] = [ε]^{χ(σ)}` and `log([ε]^a) = a log[ε]` for `a ∈ ℤ_p`, which is
future work.

## 5. Checks

* Both Contrib files compile with `lake env lean` (VERIFIED, no errors). The file contains no `notation`,
  `#eval`, `run_cmd` or macros (the scratch development used `local notation`; the Contrib copy writes the terms
  out).
* `scratch/derham-print/Statement.lean`: the verbatim copy of `DeRhamH1AbVarT`, `ddrTensorOver` and
  `IsDeRhamTensorOver`, with `Iff.rfl`/`rfl` against the originals (VERIFIED, compiles).
* Axioms (`scratch/derham-print/Axioms-output.txt`, VERIFIED): `deRhamH1AbVarT_of_leaves`, `isDeRhamOver_of_leaves`,
  `TDict.bdREquivAwayT`, `TDict.tt_eq_varpi_mul_unit`, `TDict.ker_theta_eq_omega`, `TDict.ext_of_extends`,
  `TDict.transport_extends`, `TDict.logPlus_unique` and `TDict.rootSystem` all depend only on `[propext,
  Classical.choice, Quot.sound]`.
* Autofold dry run (`python3 scripts/one_proof/autofold.py scratch/derham-print/autofold.json --dry-run`, VERIFIED):
  "strict count: 16/21 on 37 -> 18/20 on 38; strictest 16/21 -> 18/20", so **GLUE goes from 21 to 20** in both
  columns. The generated module (`scratch/derham-print/FoldDryRun.lean`, with the count line stripped) compiles
  and gives `HDec.HSyn.sixContactMin_of_open39 (r : OpenResearchLeaves29) (t : OpenTextbookLeaves13)
  (l : OpenAddedLeaves19)` with only the standard axioms.

## 6. `#discharges` output

Built with `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
+ZInQKernel.Contrib.OneProof.DeRhamPrint` (14103 jobs, success), then `lake env lean
scratch/derham-print/Discharges.lean` (full output: `scratch/derham-print/Discharges-output.txt`; VERIFIED):

```
DISCHARGES [OpenResearchLeaves28.deRhamH1AbVarT] by DeRhamPrint.deRhamH1AbVarT_of_leaves
  still assumes: [DeRhamPrint.DeRhamVpAbVarPrinted, DeRhamPrint.BdRInvariantsPrinted, AvSplit.MumfordTorsionAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves28.deRhamH1AbVarT] by DeRhamPrint.deRhamH1AbVarT_of_printed
  still assumes: [DeRhamPrint.DeRhamVpAbVarPrinted, DeRhamPrint.BdRInvariantsPrinted,
    ∀ p F A, FiniteDimensional ℚ_[p] (A.V p)]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 45 open hypotheses, 6813 theorems checked, 15 discharge one
```

(`AvSplit.MumfordTorsionAlgClosed` is the textbook field `mumfordTorsionAlgClosed`. The autofold proof passes
`{t}.mumfordTorsionAlgClosed`.)

## 7. What remains

* Statement checks of the two new leaves against the prints. They are flagged unread, and every locator is
  UNVERIFIED: no source on this host.
* Optional: remove `bdRInvariantsPrinted` by proving `σ(t) = χ(σ) t` (see §4); `V^∨ ≅ V(-1)` would then come from the
  Weil pairing.
* OPEN.md's kernel-wide B_dR paragraph can be updated at the next regeneration: the `[1/t]` case is now
  definition-level (`DeRhamPrint.TDict.bdREquivAwayT`).
