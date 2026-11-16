# dict-galois: four p-adic Hodge / Galois rows restated as printed leaves, consumers re-derived in Lean

Task dict-galois, 2026-11-16, base origin/main `e22df37cd` (leaf-fold30). Log: `scratch/dict-galois/log.md`.

## Verdict

All four rows the 11-16 dictionary pass rated *consequence* are replaced by statements in printed form, and each old
field is **proved in Lean** from the new leaves (plus, for two of them, the existing textbook field
`mumfordTorsionAlgClosed`). No `sorry`; every theorem has only the axioms `propext`, `Classical.choice`,
`Quot.sound`. `#discharges` reports all four fields discharged. The autofold dry run compiles and gives
`HDec.HSyn.sixContactMin_of_open35` with standard axioms: GLUE stays at 8 (strict) and 9 (strictest), and the
leaf count rises by one (48 to 49 fields, because `deRhamH1AbVarT` becomes two leaves).

| old field (bundle) | new leaf(s) | how the old statement is proved | file |
| --- | --- | --- | --- |
| `tateTwistInvariants` (added) | `TateTwistDict.TateTwistInvariantsPrinted` | or-elimination; in the general-character case, `χ^i(G_K ∩ I_{ℚ_p})` is infinite for `i ≠ 0` (proved) | `ZInQKernel/Contrib/OneProof/TateTwistInvariants.lean` |
| `hodgeTateDecompAbVar` (research) | `HodgeTateDict.HodgeTateDecompAbVarPrinted` | `b = g` from `dim V_p A = 2g` (T26, from `mumfordTorsionAlgClosed`) | `ZInQKernel/Contrib/OneProof/HodgeTateDecompAbVar.lean` |
| `deRhamH1AbVarT` (research) | `DeRhamDict.DeRhamVpAbVarT`, `DeRhamDict.BdRInvariantsOver` | the dual of a de Rham representation is de Rham (proved from `B_dR` a field and `B_dR^{G_F} = F`) | `ZInQKernel/Contrib/OneProof/DeRhamH1AbVarT.lean` |
| `r7a` (research) | `NOSSepDict.NeronOggShafarevichSep` | `A(K̄)[m] = A(K^s)[m]` and inertia of `K̄` ↔ inertia of `K^s` (proved) | `ZInQKernel/Contrib/OneProof/NeronOggShafarevichSep.lean` |

`#discharges` output (scratch/dict-galois/Discharges-output.txt; VERIFIED):

```
DISCHARGES [OpenAddedLeaves17.tateTwistInvariants] by TateTwistDict.tateTwistInvariants_of_printed
  still assumes: [TateTwistDict.TateTwistInvariantsPrinted]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves26.hodgeTateDecompAbVar] by HodgeTateDict.hodgeTateDecompAbVar_of_printed
  still assumes: [HodgeTateDict.HodgeTateDecompAbVarPrinted, AvSplit.MumfordTorsionAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves26.deRhamH1AbVarT] by DeRhamDict.deRhamH1AbVarT_of_leaves
  still assumes: [DeRhamDict.DeRhamVpAbVarT, DeRhamDict.BdRInvariantsOver, AvSplit.MumfordTorsionAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves26.r7a] by NOSSepDict.neronOggShafarevich_of_sep
  still assumes: [NOSSepDict.NeronOggShafarevichSep]
  axioms: [propext, Classical.choice, Quot.sound]
```

(`AvSplit.MumfordTorsionAlgClosed` is the textbook field `mumfordTorsionAlgClosed`; the autofold proofs pass
`{t}.mumfordTorsionAlgClosed`.)

## 1. `deRhamH1AbVarT`: `V_p(A)` is de Rham, and the dual by a Lean proof

Old leaf (`ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT`, TailS l. 1992): `IsDeRhamTensorOver p (A.galRep p).dual`,
"`Hom(V_p A, ℚ_p)` is de Rham". That module is `H¹_ét` only through Milne 1986, Thm 15.1(a).

New leaves:

* `DeRhamVpAbVarT`: `∀ p F A, IsDeRhamTensorOver p (A.galRep p)`, i.e. `dim_{ℚ_p} (B_dR ⊗ V_p A)^{G_F} =
  [F:ℚ_p] · dim V_p A`. This is `V_p(A)` de Rham with the printed `D_dR(V) = (B_dR ⊗ V)^{G_K}`, as Fontaine's statement is
  recorded in Berger 2004, I.3 (the lead's locator).
* `BdRInvariantsOver`: `∀ p F, finrank ℚ_p (B_dR^{G_F}) = finrank ℚ_p F` (`bdrFix p F` is the set of `x` with
  `bdrAct (gfToGqp σ) x = x` for all `σ ∈ G_F`). This is Fontaine's `B_dR^{G_K} = K` (Astérisque 223, Exp. II; Brinon–Conrad §4.4)
  in dimension form, so that no embedding `F → B_dR` is needed (pkg-I4 has none).

Glue proved (`DeRhamDict.Gen.finrank_Hsp`, for any field `B` with a `K`-linear action of a group `G` by ring
automorphisms): suppose `dim_K B^G = d > 0` and `dim_K (B ⊗ V)^G = d · dim V`. Then a `B`-basis of `span_B D` taken
inside `D = (B ⊗ V)^G` has invariant coordinates, so `D ≅ (B^G)^r` and `r = dim V`. Hence `D` contains a `B`-basis
`β` of `B ⊗ V`, and `φ ↦ (φ̃(βᵢ))ᵢ` is a `K`-isomorphism `Hom_G(V, B) ≅ (B^G)^n`, where `φ̃` is the `B`-linear
extension of `φ`. Instantiated at `B = B_dR` (a field: the kernel's `BdrKer.Cp.isField_BDeRham`), this gives
`IsDeRhamOver p ρ`, i.e. hodge-split's Hom form of "`V^∨` is de Rham". hodge-split's `isDeRhamOver_iff_tensor_dual`
converts that to the old tensor form. `V_p(A)` is finite-dimensional by T26 (from `mumfordTorsionAlgClosed`).

Ratings:

* `DeRhamVpAbVarT`: **printed form** (unread here: no source on this host). It is the de Rham property of `V_p(A)`
  with the printed `D_dR`. The only translation is `dim_{ℚ_p} D_dR = [F:ℚ_p] dim_F D_dR`, since `D_dR` is a vector space
  over `B_dR^{G_F} = F`. Locator Berger 2004 I.3 per the lead, UNVERIFIED.
* `BdRInvariantsOver`: **printed form, in dimension form**: it is a consequence of `B_dR^{G_K} = K` obtained by taking
  `ℚ_p`-dimensions. Locator UNVERIFIED.

Lean note (VERIFIED). With a local `Field (BdR p)` instance, `sub_smul` and `LinearMap.ker_eq_bot` on `B_dR ⊗ V`
fail to unify, because the Semiring instance on `B_dR` can be reached by two paths. The fix was to prove the
algebra for an abstract field `B` and instantiate it once, with explicit instances (`@Gen.finrank_Hsp … (bdrField p)
(inferInstance : Algebra ℚ_[p] (BdR p))`).

## 2. `tateTwistInvariants`: the disjunction of the two wordings

Old leaf (`TateTwistInvariants`, TailS l. 69): `ℂ_p(i)^{G_K} = 0` for `i ≠ 0`.

New leaf: `TateTwistInvariantsPrinted := TateTwistInvariants ∨ TateTwistInvariantsChar` (the lead's 11-16 ruling).
`TateTwistInvariantsChar` reads: for `K` finite over `ℚ_p` in `ℚ̄_p`, a continuous `ψ : G_K →* ℤ_p^×` with
`ψ(G_K ∩ I_{ℚ_p})` infinite, and `x ∈ ℂ_p` with `ψ(σ) σ(x) = x` for all `σ ∈ G_K`, we have `x = 0`.
Here `I_{ℚ_p}` is Tau Ceti's `inertiaSubgroup ℚ_[p] = Gal(ℚ̄_p/ℚ_p^ur)` (vendored in `ZInQKernel/Contrib/TauCeti`).

Proved (`TateTwistDict.infinite_chiPowK_inertia`): `χ^i(G_K ∩ I_{ℚ_p})` is infinite for `i ≠ 0` (Serre, *Local
Fields*, IV §4).
* `χ(I_{ℚ_p}) = ℤ_p^×`: a lift of `Art(u⁻¹)` lies in inertia and has `χ = u`. This uses Tau Ceti's
  `mem_inertiaSubgroup_of_mk_eq_artinMap` and `localCyclotomicCharacter_artinMap_padic`.
* `G_K` has finite index (`finrank_eq_fixingSubgroup_index`), so its normal core `N` does too. Then
  `σ^{[G:N]} ∈ N ⊆ G_K` for every `σ ∈ I_{ℚ_p}`, so the image contains every `u^{[G:N]·i}`.
* `u ↦ u^k` has finite fibres on `ℤ_p^×` (roots of unity), and `ℤ_p^×` is infinite.

Continuity of `χ` is Mathlib's `cyclotomicCharacter.continuous`, via Tau Ceti. `cyc p σ` and Tau Ceti's
`localCyclotomicCharacter p ℚ_[p] σ` are definitionally equal (VERIFIED).

Rating: **printed form, by or-introduction**, under either wording. The general-character disjunct uses
`G_K ∩ I_{ℚ_p}` in place of Tate's `I_K`. The inclusion `G_K ∩ I_{ℚ_p} ⊆ I_K` holds (an element of `G_K` that fixes
`ℚ_p^ur` acts trivially on the residue field of `ℚ̄_p`, which is generated by the prime-to-`p` roots of unity), so
the hypothesis "`ψ(G_K ∩ I_{ℚ_p})` infinite" implies Tate's "`ψ(I_K)` infinite". The disjunct is therefore a
consequence of the print, never stronger. (Equality holds, since `K^ur = K·ℚ_p^ur`.) The new leaf is also implied by
the old leaf (its first disjunct). Locator Tate 1967 §3.3 Thm 2, UNVERIFIED (from memory, no network).

## 3. `r7a`: Néron–Ogg–Shafarevich over a separable closure

Old leaf (`PkgI2.NeronOggShafarevich.{0}`, `HDecomp/Objects.lean` l. 861) states the criterion with a valuation
ring `w` of `AlgebraicClosure K` and `A(K̄)[m]`.

New leaf `NeronOggShafarevichSep`: the same statement with `AlgebraicClosure K` replaced by any `Ks` with
`[IsSepClosure K Ks]`, `w` a valuation ring of `Ks` over `O`, and `A(Ks)[m]`.

Proved (`NOSSepDict.neronOggShafarevich_of_sep`). Apply the leaf to `Ks = separableClosure K K̄` and
`w' = w ∩ K^s`. Then for `m` invertible in `O`, `InertiaTrivialOn A w m ↔ InertiaTrivialOn A w' m`
(`inertiaTrivialOn_sep_iff`):
* `K̄ ⇒ K^s`: extend `τ ∈ I(w')` to `σ = τ.liftNormal K̄`. Then `σ ∈ I(w)` by `isInertia_extend` (new, proved): for
  `y ∈ K̄`, some `y^{q^n}` lies in `K^s` (`K̄/K^s` purely inseparable). Valuation rings and maximal ideals are
  closed under `q^n`-th roots, and `(σy − y)^{q^n} = τ(y^{q^n}) − y^{q^n}`. Then use `A(K^s) ↪ A(K̄)` and
  Galois-equivariance (`extPt_injective`, `extPt_galAct`).
* `K^s ⇒ K̄`: every point of `A(K̄)[m]` comes from `A(K^s)` because `[m]` is étale (`torsion_from_sepClosure` with
  the proved `mulEtaleAbelianScheme_proof`, fork PR #19), and `σ ∈ I(w)` restricts into `I(w')`
  (`inertiaRestrict'`). Both are gt-unip / unipotent-b lemmas, in `UnipotentForward.lean`.

Rating: **printed form**. Serre–Tate, Ann. of Math. 88 (1968), §1 Thm 1, is stated over `K_s` with any extension `\bar v`
of `v` and its inertia group. The Lean form keeps the chain's reading of good reduction (an abelian scheme over `O`
with generic fibre `A`) and of "prime to the residue characteristic" (`IsUnit (m : O)`). It drops clause (d) (the `T_ℓ`
clause), so it is weaker. Numbering from memory, UNVERIFIED.

## 4. `hodgeTateDecompAbVar`: second exponent unnamed

Old leaf (`HodgeTateDecompAbVar`, TailS l. 347): a `G_F`-equivariant `ℂ_p ⊗ V_p(A) ≅ ℂ_p(1)^g × ℂ_p^g`. The second
exponent is `dim_F t*_{A'}`, which equals `g` only through the dual abelian variety.

New leaf `HodgeTateDecompAbVarPrinted`: the same, with `ℂ_p(1)^g × ℂ_p^b` for some `b`.

Proved (`HodgeTateDict.hodgeTateDecompAbVar_of_printed`). `T_p(A)` is free of rank `2 dim A` over `ℤ_p`
(`T5Torsion.TateFree.tateModuleFree_of_torsionStructure (AvSplit.Final.h25 hM)`, from the textbook field
`mumfordTorsionAlgClosed`; `p ≠ 0` in `F` since `F ⊇ ℚ_p`). So `dim_{ℂ_p} ℂ_p ⊗ V = 2g = g + b`, which gives
`b = g`. This takes the task's option of restating the leaf without coordinates on the `t*_{A'}` factor. No
dual-abelian-variety statement is used.

Rating: **printed form, with bases chosen**. Fontaine 1982 (Théorème principal; Tate 1967 §4; Faltings 1988) prints
`(ℂ_p(1) ⊗_F t_A) ⊕ (ℂ_p ⊗_F t*_{A'})`. The leaf picks bases. It uses `dim_F t_A = dim A = g` (the tangent space of a
smooth group variety of dimension `g`; STANDARD) and leaves `dim t*_{A'}` unnamed. It is weaker than the old leaf.
Locators UNVERIFIED.

## What compiles, and what to do at the fold

* Four contribution files under `ZInQKernel/Contrib/OneProof/` (`lake build` OK, about 25 s on top of the built
  chain). They import TailS / TailQ / LF4T5 / AbVarBC / UnipotentForward / MulEtale / Tau Ceti modules, never `Main`,
  and contain no `notation`, `#eval`, macros or `run_cmd`.
* `scratch/dict-galois/`: development copies (`TateTwist.lean`, `HodgeTate.lean`, `DeRham.lean`, `NOSSep.lean`),
  `OldStatements.lean` (the four chain statements copied verbatim, each `Iff.rfl` to the original), `Discharges.lean`
  and its output, `autofold.json`, `autofold-dryrun.txt`, and `AutofoldDry.lean` (the dry-run module; it compiles,
  `sixContactMin_of_open35` standard axioms).
* Not done here, since only my own files may be edited: rows in `docs/research/locators.md` for the five new
  leaves. Proposed rows:
  * Tate 1967 §3.3 Thm 2 (either wording).
  * Fontaine 1982 Théorème principal (second exponent unnamed).
  * Berger 2004 I.3 (`V_p(A)` de Rham).
  * Fontaine, Astérisque 223, Exp. II (`B_dR^{G_K} = K`).
  * Serre–Tate 1968 Thm 1 over `K_s`.

  All are unread on this host, so each enters kinds.tsv flagged unread (autofold's default flag).
* The autofold spec gives each new leaf the bundle of the field it replaces (research for three, added for
  `tateTwistInvariantsPrinted`).
