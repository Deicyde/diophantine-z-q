# phi-ample: `mumfordKLFiniteSectionAC` removed — `K(L)` is finite for every ample `L`, proved (−1, no new leaf)

Task phi-ample. Base origin/main c1e4ed1b8 (top `sixContactMin_of_open38`). The two added fields were
`mumfordKLFiniteSectionAC : PicFix.MumfordKLFiniteSectionAC` (Mumford §6 Application 1) and
`mumfordPhiSurjectiveAC : PicDict.MumfordPhiSurjectiveAC` (Mumford §8 Thm 1) of `HDec.HSyn.OpenAddedLeaves19`
(`ZInQKernel/OneProof/H/TailZ45.lean`).

## 1. Result

**`mumfordKLFiniteSectionAC` is a Lean theorem, given two fields of the same bundle.** Route (a) of the brief:
Mumford's proof that `K(L)` is finite for `L` ample, written over any field.

| field | result | new leaves | fold (autofold dry run) |
|---|---|---|---|
| `mumfordKLFiniteSectionAC` | **proved** from `picRepresentableAbVar` and `picZeroAbVar` (L1, L2), both fields of `OpenAddedLeaves19` | none | main: `strict count: 16/21 on 37 -> 15/21 on 36; strictest 16/21 -> 15/21`; leaf-fold33b: `15/20 on 35 -> 14/20 on 34; strictest 15/20 -> 14/20` |
| `mumfordPhiSurjectiveAC` | not removed (§4) | — | — |

So the count goes down by one hypothesis, with no new leaf and no rise in either GLUE column. The row removed was
counted LEAF (a printed Mumford statement), so the change shows in the LEAF column (16 → 15).

Everything in this section is VERIFIED: it compiled on this host, and `#print axioms` gives
`[propext, Classical.choice, Quot.sound]`.

### The file

`ZInQKernel/Contrib/OneProof/MumfordKLFinite.lean` (namespace `PhiAmple`, 443 lines, 24 KB; a copy is in
`scratch/phi-ample/MumfordKLFinite.lean`).

* It imports `ZInQKernel.Contrib.OneProof.PicDictionary` (which imports `ZInQKernel.OneProof.H.TailZ24`, where
  `PhiAmpleIsogeny` and L1, L2 are defined) and `ZInQKernel.Contrib.OneProof.PhiAmpleIsogeny` (where
  `MumfordKLFiniteSectionAC` is defined). It also imports three vendored modules: `Modules.ZeroLocusTensor`,
  `Modules.Endomorphism` and FLT's `Scheme.isIntegral_subscheme_vanishingIdeal`.
* It does not import `ZInQKernel.OneProof.Main`.
* There is no `sorry`, and no code that runs at build time (`#eval`, `run_cmd`, `syntax`, `notation`, macros):
  checked by grep.

Main results:

```lean
theorem PhiAmple.mumfordKLFiniteSectionAC_of_open (h1 : T09Pic.PicRepresentableAbVar)
    (h2 : T09Pic.PicZeroAbVar) : PicFix.MumfordKLFiniteSectionAC        -- the theorem for the fold
theorem PhiAmple.mumfordKLFiniteAC_of_open (h1 : T09Pic.PicRepresentableAbVar)
    (h2 : T09Pic.PicZeroAbVar) : PicDict.MumfordKLFiniteAC              -- pic-dict's form, for every ample L
theorem PhiAmple.phiAmpleIsogeny_of_phiSurjective (h8 : PicDict.MumfordPhiSurjectiveAC) :
    T09Pic.PhiAmpleIsogeny                                             -- the old field, from §8 Thm 1 alone
theorem PhiAmple.finite_ker_pts ... :                                   -- the core, over any field
    {x : A.Pt (AlgebraicClosure K) | x ≫ lam = 1}.Finite
```

`finite_ker_pts` takes a field `K`, an abelian variety `A`, a representation `rep` of `Pic_{A/K}` by `P`, its
identity component `(B, j)` with `IsPicZero rep B j`, an ample `L` and `lam : A → B` with `lam ≫ j = phiL rep L`.
This is exactly the context of `PhiAmpleIsogeny`. So `phiAmpleIsogeny_of_phiSurjective` needs no L1/L2
hypothesis.

### Checks

* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.MumfordKLFinite`:
  `Build completed successfully (14102 jobs)`.
* `#discharges` (`scratch/phi-ample/Discharges.lean`; full output in `scratch/phi-ample/discharges.txt`):

  ```
  DISCHARGES [OpenAddedLeaves19.mumfordKLFiniteSectionAC] by PhiAmple.mumfordKLFiniteSectionAC_of_open
    still assumes: [T09Pic.PicRepresentableAbVar, T09Pic.PicZeroAbVar]
    axioms: [propext, Classical.choice, Quot.sound]
  #discharges: 45 open hypotheses, 6704 theorems checked, 14 discharge one
  ```

  The two remaining assumptions are the fields `picRepresentableAbVar` and `picZeroAbVar` of the same bundle
  `OpenAddedLeaves19`, so nothing new enters.
* `#print axioms` of `phiAmpleIsogeny_of_phiSurjective` and `finite_ker_pts`: standard
  (`scratch/phi-ample/axioms.txt`).

### Fold spec: `scratch/phi-ample/autofold.json`

```json
{"field": "mumfordKLFiniteSectionAC",
 "proof": "_root_.PhiAmple.mumfordKLFiniteSectionAC_of_open {n}.picRepresentableAbVar {n}.picZeroAbVar",
 "leaves": []}
```

**On main (c1e4ed1b8).**
* `--dry-run` gives `16/21 on 37 -> 15/21 on 36` (`scratch/phi-ample/autofold-dryrun.txt`).
* The printed module, with line 1 stripped, is `scratch/phi-ample/FoldDryRun.lean.txt`. It is renamed `.txt` so
  that its `HDec.HSyn` copies are not a Lean target.
* It compiles against the built `TailZ45` to `HDec.HSyn.sixContactMin_of_open39` with the standard axioms.
* The new bundle `OpenAddedLeaves20` has the four fields `picRepresentableAbVar`, `picZeroAbVar`,
  `weilPairingMumford` and `mumfordPhiSurjectiveAC`.

**On origin/wip/leaf-fold33b (3091ccc77)**, after poincare-proof's fold:
* I used a temporary worktree with leaf-fold33b's build tree and the new file added. The worktree has been
  removed.
* The same spec gives `15/20 on 35 -> 14/20 on 34`.
* The printed module (`scratch/phi-ample/FoldDryRunLF33.lean.txt`) compiles to `sixContactMin_of_open40` with the
  standard axioms.
* The new `TailZ46` consumer (`poincareComplement_of_open … (PicFix.phiAmpleIsogeny_of_printed
  l.mumfordKLFiniteSectionAC l.mumfordPhiSurjectiveAC)`) is unaffected: the conversion theorem fills the field
  `mumfordKLFiniteSectionAC` of the old generation with the theorem.

**For the integrator.** You could instead switch the conversion term to
`PhiAmple.phiAmpleIsogeny_of_phiSurjective n.mumfordPhiSurjectiveAC`, which needs no L1/L2. That is a hand fold
(it edits an existing conversion), and it gives the same count. The autofold spec above is enough.

## 2. The proof (Mumford §6 Application 1, irreducible-subset form)

Notation: `K` is any field, `L` is ample on `A`, and `λ = lam : A → B ⊆ P = Pic_{A/K}` is the lift of `φ_L`.

**Core lemma: `subsingleton_of_lam_const`.** Let `i : Z → A` be a closed immersion from an integral scheme, with
`i ≫ λ` constant equal to `0` (that is, `i ≫ λ = g ≫ η_B`). Then `Z` is one point. The proof:

1. `i ≫ φ_L = const η_P`, since `j` is a homomorphism. By `comp_classify` and `homEquiv_symm_one`, the classes
   `(1 × i)^*Λ(L)` and `1` have the same image in the Picard sheaf over `Z`.
2. `(1 × i)^*Λ(L)` is normalized along the zero section: `Λ(L)|_{0 × A} = L · (str^*0^*L)⁻¹ · L⁻¹ = 1`, because
   `Pic(Spec K)` is trivial.
3. Kleiman 9.2.5 (the vendored `picardFunctorNormalizedIso`, through pic-dict's `Θ_inj` and the proved
   `pushforwardUnitUniversal`) then gives `(1 × i)^*Λ(L) = 1` in `Pic(A ×_K Z)`. No fppf-local argument is needed.
4. Restrict along the section `z ↦ (−z, z)`. Here `m ∘ (−i, i) = 0` (`GrpObj.left_inv`), so
   `i^*L · i^*(−1)^*L = 1` in `Pic(Z)`.
5. Both factors are ample (`isAmple_pullback` along the closed immersion `i`, and along the automorphism `ι`).
   `Γ(Z, 𝒪)` is a field (Mathlib `isField_of_universallyClosed`: `Z` is integral and proper over `K`).
6. `isAffine_of_ample_mul_eq_one`: take sections `s` of `c^n` and `t` of `d^m` that do not vanish at `x`, with
   `D(s)` affine. Then `u = s^{⊗m} ⊗ t^{⊗n}`, moved to `𝒪` through `(cd)^{nm} = 1`, is a global function with
   `x ∈ D(u)`.
   * `D(ψ ≫ φ) ⊇ D(ψ) ∩ D(φ)` is the new local lemma `notMem_support_comp`.
   * `u = (λ⁻¹ ≫ 𝟙 ◁ T) ≫ (S ▷ Q ≫ e)`, so `u` is a unit (vendored `exists_eq_smulHom`, since `Γ` is a field).
     Hence `Z(u) = ∅`, so `Z(s) ⊆ Z(u)` (vendored `zeroLocus_comp_le`) is empty.
   * So `D(s) = Z` is affine.
7. An affine scheme whose `Γ` is a field has one point (`subsingleton_of_isAffine_of_isField`).

**Finiteness: `finite_ker_pts`.**
* The scheme-theoretic kernel `pullback λ η_B` is a closed subscheme of `A`, since `η_B` is a closed immersion (a
  section of a separated morphism). So it is a noetherian space (`LocallyOfFiniteType.isLocallyNoetherian` plus
  `IsInducing.noetherianSpace`).
* Each irreducible closed subset `Z` of the kernel, with its reduced induced structure, is integral (vendored
  `isIntegral_subscheme_vanishingIdeal`). It satisfies the hypothesis of the core lemma by `pullback.condition`, so
  it is a point.
* Hence `k ↦ irreducibleComponent k` is injective into a finite set, so the kernel is finite, and its points are
  closed.
* A `K̄`-point of `ker λ` lifts through the kernel, so it lies over one of these points. Over each closed point
  there are finitely many `K̄`-points (pic-dict's `finite_pts_over`).

**From `K̄`-points to the field.**
* `phiAmpleIsogeny_of_phiSurjective` is pic-dict's `phiAmpleIsogeny_of_printed`, with `finite_ker_pts` in place of
  `MumfordKLFinite`.
  * Finiteness comes from the proved `finiteOfFiniteKerPts`.
  * Surjectivity is unchanged: `mumfordPhiSurjective_of_ac`, `ampleBaseChangeAlgClosure` and
    `picZeroPtsTranslInv_of_leaves pushforwardUnitUniversal geomIntegralProd`.
* `mumfordKLFiniteAC_of_open`: over `k = k̄`, take `rep` from L1, `(B, j)` from L2 and `λ` from
  `exists_hom_comp_eq_phiL`.
  * A `k`-point `x` with `φ_L(x) = 1` has `x ≫ λ = 0`. The new lemma `map_mumfordBundle_kpt` says
    `Λ(L)|_{A × x} = pr₁^*φ_L(x)`; then use `comp_classify` and `cancel_mono j`.
  * `X(k) ↪ X(k̄)`, by composing with the epimorphism `Spec k̄ → Spec k` (flat and surjective).
* The printed-form field follows (its nonzero-section hypothesis is not used).

The theorem of the square, the seesaw and cohomology are not needed (pic-fix had already noted that the theorem of
the square is not needed for this half). The family argument goes through the tree's representation of the Picard
sheaf and Kleiman 9.2.5, which is already proved in the vendored library.

## 3. Consumers

On main, `mumfordKLFiniteSectionAC` feeds only `PicFix.phiAmpleIsogeny_of_printed` (TailZ45:123). On leaf-fold33b
it also feeds TailZ46's `poincareComplement` (through the same theorem). Both consumers keep receiving
`PhiAmpleIsogeny` unchanged, since the fold only fills the field.

No narrowing was needed: the theorem holds over every field, for every ample `L`. So route (c) (fields embeddable
in `ℂ`) was not used.

## 4. What remains: `mumfordPhiSurjectiveAC`

Not removed. Mumford §8 Thm 1 says `λ_L` is onto `Pic⁰`.

* With the kernel now finite, onto is equivalent to `dim B ≤ dim A`, that is `dim Pic⁰ = g`.
* Mumford gets this from cohomology: Thm 1 uses the vanishing of `H^*(A, M)` for nontrivial `M ∈ Pic⁰` and the
  Künneth/Leray spectral sequences. `dim Pic⁰ = h¹(𝒪_A) = g` is §13.
* Neither is in the tree.
* A route through the field `weilPairingMumford` (perfectness gives `#B[n] = #A[n]`) would be circular: weil-proof's
  discharge of that field takes `PhiAmpleIsogeny` as input.
* The consumers need surjectivity. Poincaré's complement applies Milne's quasi-inverse to `ψ ∘ i`, which must be an
  isogeny. So the field cannot be narrowed away.

It stays a leaf, unchanged from pic-dict: printed form, yes (Mumford §8 Thm 1 over an algebraically closed field,
with `Pic⁰` the translation-invariant classes; locator UNVERIFIED).

## 5. New leaves and their rating

None. The fold adds no leaf, so no row is needed in `locators.md`.

## 6. Files

* `ZInQKernel/Contrib/OneProof/MumfordKLFinite.lean`: the contribution.
* In `scratch/phi-ample/`:
  * `MumfordKLFinite.lean` (copy), `Discharges.lean`, `discharges.txt`, `axioms.txt`;
  * `autofold.json`, `autofold-dryrun.txt`, `FoldDryRun.lean.txt`;
  * `autofold-dryrun-lf33.txt`, `FoldDryRunLF33.lean.txt`;
  * `log.md`.
