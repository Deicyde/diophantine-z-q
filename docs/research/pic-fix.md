# pic-fix: `phiAmpleIsogeny` folded for −1, `picZeroAbVar` down to one GLUE

Task pic-fix. Base: wip/pic-dict 4e95795b with origin/main (2880fef1e) merged. The rows are fields of
`HDec.HSyn.OpenAddedLeaves17`, and their statements are in `ZInQKernel/OneProof/H/TailZ24.lean`.

## 1. Result

| row | result | leaves | GLUE change (dry run on this base) |
|---|---|---|---|
| `phiAmpleIsogeny` | **replaced by 2 printed leaves + Lean glue** | Mumford §6 App. 1 in its printed form (`MumfordKLFiniteSectionAC`, new); Mumford §8 Thm 1 (`MumfordPhiSurjectiveAC`, rated LEAF by the review) | **−1**: `34/11 on 45 -> 36/10 on 46; strictest 34/11 -> 36/10` |
| `picZeroAbVar` | **reduced to 3 printed leaves + 1 pending leaf, glue proved** | Kleiman 9.4.8 / BLR 8.2 Thm 3 (`PicLocFinType`); SGA 3 VI_A 2.4 (`IdentityComponentLFT`); Kleiman 9.5.4 in its printed form (`KleimanPicZeroProper`, new); `PicZeroSmooth` (flagged pending reading, counted GLUE) | 0. `PicZeroSmooth` is now its only GLUE |

Both rows in one fold: `34/11 on 45 -> 39/10 on 49; strictest 34/11 -> 39/10`, still −1 in total, with no
`--allow-rise`.

Everything below is VERIFIED: it compiled, and `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.

### Files

* `ZInQKernel/Contrib/OneProof/PhiAmpleIsogeny.lean` (namespace `PicFix`). It imports only
  `ZInQKernel.Contrib.OneProof.PicDictionary`, which imports `ZInQKernel.OneProof.H.TailZ24`, the module that
  defines the statement.
* `ZInQKernel/Contrib/OneProof/PicZeroAbVar.lean` (namespace `PicFix`). It imports `PicDictionary` and the vendored
  `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime`
  (which imports all of Mathlib).
* No `sorry`, no code that runs at build time. Neither file imports `ZInQKernel.OneProof.Main`.
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.PhiAmpleIsogeny
  +ZInQKernel.Contrib.OneProof.PicZeroAbVar` succeeds (13701 jobs).

### Main results

```lean
theorem PicFix.phiAmpleIsogeny_of_printed (hKL : MumfordKLFiniteSectionAC) (h8 : MumfordPhiSurjectiveAC) :
    PhiAmpleIsogeny
theorem PicFix.picZeroAbVar_of_printed (h1 : PicLocFinType) (h2 : IdentityComponentLFT) (h3a : PicZeroSmooth)
    (h3b : KleimanPicZeroProper) : PicZeroAbVar
```

### `#discharges`

`scratch/pic-fix/Discharges.lean`; the full output is in `scratch/pic-fix/discharges.txt`. The two new lines:

```
DISCHARGES [OpenAddedLeaves17.phiAmpleIsogeny] by PicFix.phiAmpleIsogeny_of_printed
  still assumes: [PicFix.MumfordKLFiniteSectionAC, PicDict.MumfordPhiSurjectiveAC]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenAddedLeaves17.picZeroAbVar] by PicFix.picZeroAbVar_of_printed
  still assumes: [PicDict.PicLocFinType,
 PicDict.IdentityComponentLFT,
 PicDict.PicZeroSmooth,
 PicFix.KleimanPicZeroProper]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 56 open hypotheses, 3080 theorems checked, 19 discharge one
```

### Autofold

* `scratch/pic-fix/autofold.json` (**recommended**): `phiAmpleIsogeny` alone, with the leaves
  `mumfordKLFiniteSectionAC` and `mumfordPhiSurjectiveAC`. Both are flagged "unread: …; locator UNVERIFIED" and
  counted LEAF.
* `scratch/pic-fix/autofold-both.json`: the same, plus `picZeroAbVar` with four leaves:
  * `picLocFinType`, `identityComponentLFT` and `kleimanPicZeroProper`, flagged unread and counted LEAF;
  * `picZeroSmooth`, whose flag begins "pending reading: …", so autofold counts it GLUE.
* Both dry runs print a module (line 1 stripped: `scratch/pic-fix/FoldDryRun.lean`, `FoldDryRunBoth.lean`). It
  compiles against the built `TailZ42` to `HDec.HSyn.sixContactMin_of_open36` with the standard axioms.

## 2. (1) `K(L)` finite: printed form and the ample case

**Why the old leaf was GLUE.** `PicDict.MumfordKLFiniteAC` asserts that `K(L)` is finite for every ample `L`.
Mumford §6 Application 1 is printed for `L = 𝒪_X(D)` with `D` effective.

**New leaf** (in `PhiAmpleIsogeny.lean`):

```lean
def MumfordKLFiniteSectionAC : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (X : AbVar k) (c₀ : X.X.left.Pic), IsAmple X.X.left c₀ →
    (∃ s : 𝟙_ X.X.left.Modules ⟶ AC.modX c₀, s ≠ 0) →
    {x : AC.Kpt X | AC.phi c₀ x = 1}.Finite
```

That is: `L` ample with a nonzero global section `s` implies that `K(L) = {x ∈ X(k) : t_x^*L ≅ L}` is finite.

**Glue, proved** (`PicFix.mumfordKLFiniteAC_of_section : MumfordKLFiniteSectionAC → MumfordKLFiniteAC`):

* `mk_tensorPow`: `[M^{⊗n}] = [M]^n` in `Pic`.
* `support_tensorPowSection`: `Z(s^{⊗m})` and `Z(s)` have the same support for `m > 0`. On an affine open where
  `M` has a free generator `e` and `s(1) = f·e`, the vendored `exists_tensorPowSectionOne_eq_pow_smul` and
  `Hom.ideal_zeroLocus` give the ideals `(f^m)` and `(f)`. Mathlib's `basicOpen_pow` finishes.
* `isAmple_pow`: if `IsAmple c` then `IsAmple (c^n)` for `n > 0`. This is the lemma "ample ⇒ powers ample"
  (Stacks 01PT, UNVERIFIED), proved for the project's `IsAmple`. The section `s^{⊗n}` of `(L^{⊗m})^{⊗n}` is moved
  to `(L^n)^{⊗m}` through an isomorphism that comes from equality of Picard classes; the support is unchanged.
* `exists_pow_section`: an ample class on a nonempty scheme has a power `c^m` (`m > 0`) with a nonzero section.
  At a point of `D(s)`, the zero scheme is not everything, so `s ≠ 0` by the vendored `zeroLocus_eq_bot_iff`.
* `phi_pow`: `φ_{L^n}(x) = φ_L(x)^n`, hence `K(L) ⊆ K(L^n)`. `Pic.map` is a homomorphism, so the theorem of the
  square is not needed (the brief suggested `MumfordSquareAC`; it is not used).

**`picZeroPtsTranslInv`.** The restatement does not remove the need for it, and it was never an assumption of the
fold:

* It is used for surjectivity: Mumford §8 Thm 1 is applied to the class `M_y`, which must be translation-invariant.
  It is not used for finiteness.
* It is a theorem in `PicDictionary.lean`: `picZeroPtsTranslInv_of_leaves`, whose two inputs
  `pushforwardUnitUniversal` and `geomIntegralProd` are proved.
* So `phiAmpleIsogeny_of_printed` assumes exactly the two leaves above, as `#discharges` confirms.

**Note for a later `weilPairingMumford` fold** (that row is left alone here). `weilPairingMumford_final` takes
`MumfordKLFiniteAC`. Composing with `PicFix.mumfordKLFiniteAC_of_section` replaces it by the printed form.

## 3. (2) `picZeroAbVar`

**New leaf** (in `PicZeroAbVar.lean`):

```lean
def IsNormalScheme : ObjectProperty Scheme.{0} :=
  fun X => ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)
def KleimanPicZeroProper : Prop :=
  ∀ (K : Type) [Field K] (X : Over (Spec (CommRingCat.of K))), IsProper X.hom →
    geometrically IsNormalScheme X.hom →
    ∀ (P : Over (Spec (CommRingCat.of K))) (rep : (picardFunctor X.hom).obj.RepresentableBy P)
      (V : P.left.Opens),
      letI := picardFunctorCommGrpObj X.hom rep
      (V : Set P.left) = identityComponent P → IsProper (V.ι ≫ P.hom)
```

* `IsNormalScheme` is Stacks 033H: every local ring is a normal domain.
* Geometric normality uses Mathlib's `geometrically`: `X ×_K Spec K'` is normal for every field `K'` over `K`.
  This is Stacks 038O's definition.

**Glue, proved:**

* `isNormalScheme_of_smooth_field`: a scheme smooth over a field is normal. On an affine open `U ∋ z`, `Γ(U)` is
  smooth over `L` (via `appLE`, as in `PicDict.isReduced_of_smooth_field`). The stalk is
  `Γ(U)_{𝔭}` (Mathlib's `IsAffineOpen.isLocalization_stalk`). The vendored
  `Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime` applies with `R = L`, a UFD.
* `geometricallyNormal_of_smooth`: smoothness is stable under base change.
* `picZeroProper_of_kleiman : KleimanPicZeroProper → PicDict.PicZeroProper`: an abelian variety is proper and
  smooth.

**The other three leaves are unchanged** (the defs are in `PicDictionary.lean`):

* `PicLocFinType` is LEAF. The spec cites BLR, *Néron models*, 8.2 Thm 3 / Murre 1964, Oort 1962 first (`Pic_{X/k}`
  exists and is locally of finite type for `X` proper over a field). Kleiman 9.4.8 comes second, for `X`
  projective; an abelian variety is projective by the vendored
  `GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral`.
* `IdentityComponentLFT` is LEAF.
* `PicZeroSmooth` stays pending a reading. Its flag now begins "pending reading", so autofold counts it GLUE. One
  former step is gone: Stacks 00TV (regular ⇒ smooth over a perfect field) is proved on main
  (`ZInQ.Contrib.OneProof.RegularSmoothPerfect.regularSmoothPerfect_proof : CurveSplit.RegularSmoothPerfect`).
  What remains combined:
  * Mumford §13's `dim T₀ = g` over `K̄`;
  * the identification of Mumford's `Â` with the identity component of the fppf `Pic`;
  * descent from `K̄` to `K`.

  A single print over an arbitrary field would clear it: BLR 8.4, FGA Explained 9.5 or Milne 1986 §10, still to be
  read.

## 4. New leaves: printed form?

All locators are UNVERIFIED (no copy of Mumford, Kleiman or BLR on the host). Each new leaf needs a row in
`docs/research/locators.md` with verdict UNVERIFIED.

| leaf | source | printed form? | reason |
|---|---|---|---|
| `mumfordKLFiniteSectionAC` | Mumford, *Abelian varieties*, §6 Application 1, (iv) ⇒ (ii) | **yes** (equivalent restatement) | Mumford: `D` effective, `L = 𝒪(D)` ample ⇒ `K(L)` finite. On the integral scheme `X`, a nonzero section `s` gives the effective Cartier divisor `D = Z(s)` with `L ≅ 𝒪(D)` (vendored `Hom.isInvertible_zeroLocus`, `Hom.nonempty_iso_dual_toModules_tensorObj`). Conversely `𝒪(D)` has the section `1_D`. Ampleness is the EGA/Stacks notion, which equals Mumford's on a complete variety. `K(L)` is taken on `k`-points (`AC.phi c₀ x = 1` ⟺ `t_x^*L ≅ L`). |
| `mumfordPhiSurjectiveAC` | Mumford §8 Thm 1 | yes (unchanged from pic-dict; rated LEAF by the review) | — |
| `kleimanPicZeroProper` | Kleiman, *The Picard scheme*, Thm 9.5.4 | **yes** | `X` proper and geometrically normal over a field ⇒ `Pic⁰_{X/K}` proper. It is stated for every representing scheme of the fppf sheaf `Pic_{(X/K)(fppf)}` (`picardFunctor`) and every open on the identity component, which are unique up to unique isomorphism. The existence hypotheses of the print become quantifiers. |
| `picLocFinType` | BLR 8.2 Thm 3 / Murre–Oort; Kleiman 9.4.8 | yes (unchanged) | a consequence for every representing object by Yoneda |
| `identityComponentLFT` | SGA 3 VI_A 2.4; Stacks 0B7R | yes (unchanged) | — |
| `picZeroSmooth` | Mumford §13 + identification + descent | **no, pending reading** | no one-statement print over `K` located yet |

## 5. What remains

* `PicZeroSmooth`: a reading of BLR 8.4, FGA Explained 9.5 or Milne 1986 §10 for one print over an arbitrary field.
  Once it is cleared, `autofold-both.json` gives −2.
* Readings of the locators in §4, in particular:
  * that Kleiman 9.5.4 needs only "proper and geometrically normal";
  * that Mumford's Application 1 includes the direction ample ⇒ `K(L)` finite for effective `D`.
* Not done (out of scope): the four Weil-pairing leaves of pic-dict's `weilPairingMumford` specs are flagged
  "unread" in `scratch/pic-dict/autofold*.json`. If the review keeps them GLUE pending readings, their flags should
  begin "pending reading" before any fold of that row. That row was left alone.
