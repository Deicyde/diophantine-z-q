# smooth-regular: smooth = regular = geometrically regular over a field; the 00TV leaf proved

Task smooth-regular (2026-11-16), base e22df37c (fork main after leaf-fold30). Scratch: `scratch/smooth-regular/`
(results log `log.md`). Contributions (new files only):

* `ZInQKernel/Contrib/OneProof/RegularSmoothPerfect.lean` — closes the open field `regularSmoothPerfect`;
* `ZInQKernel/Contrib/OneProof/PicZeroAbVarNonsingular.lean` — the nonsingular form of `picZeroAbVar`;
* `ZInQKernel/Contrib/OneProof/SmoothRegular/Basic.lean` — the scheme-level theorems and the abelian-variety
  dictionary (helper module, imported by both).

## 1. Result

1. **The open hypothesis `regularSmoothPerfect` is proved outright, with no new leaf** (VERIFIED: compiled,
   axioms `propext`, `Classical.choice`, `Quot.sound`):

   ```lean
   theorem ZInQ.Contrib.SmoothRegular.regularSmoothPerfect : CurveSplit.RegularSmoothPerfect
   ```

   `CurveSplit.RegularSmoothPerfect` (field `HDec.HSyn.OpenTextbookLeaves11.regularSmoothPerfect`, Stacks 00TV ⇐)
   says: over a perfect field `k`, if `S` is a finite type `k`-algebra and `S_q` is regular, then some `g ∉ q`
   has `S_g` smooth over `k`. Proof (five lines):
   * `Algebra.FormallySmooth.localization_of_isRegularLocalRing` (the Jacobian criterion; from the vendored
     Jacobian-Challenge library, `ZInQKernel/Contrib/CloudW07JacobiansCurves/Jacobian/RingTheory/Smooth/RegularLocalRing.lean`):
     if `S_q` is regular and its residue field is formally smooth over `k`, then `S_q` is formally smooth over `k`;
   * Mathlib's `Algebra.FormallySmooth.of_perfectField`: that residue field is essentially of finite type over the
     perfect field `k`, so it is formally smooth over `k`;
   * Mathlib's `Algebra.IsSmoothAt.exists_notMem_smooth`: the smooth locus is open, which gives `g`.

   The converse in the same algebraic form, over any field, is proved too:
   `isRegularLocalRing_of_smooth : Algebra.Smooth k S → IsRegularLocalRing (Localization.AtPrime q)`.

2. **Scheme-level theorems** (`SmoothRegular/Basic.lean`; VERIFIED, standard axioms). Here `f : X ⟶ Spec K` is
   locally of finite type, and `X` is in universe `u` with `K : Type u`:

   | theorem | field | statement |
   | --- | --- | --- |
   | `smooth_iff_isRegularLocalRing_stalk` | perfect | `Smooth f ↔ ∀ x, IsRegularLocalRing 𝒪_{X,x}` |
   | `smooth_iff_nonsingular` | perfect | `Smooth f ↔ Nonsingular f` (regular local rings at the closed points) |
   | `smooth_iff_geometricallyRegular` | any | `Smooth f ↔ ∀ L/K, X_L regular` |
   | `smooth_iff_regularAfter_algebraicClosure` | any | `Smooth f ↔ X_{K̄}` regular |
   | `smooth_iff_nonsingularAfter_algebraicClosure` | any | `Smooth f ↔ X_{K̄}` nonsingular |
   | `smooth_tfae_perfect` | perfect | smooth, regular and geometrically regular are equivalent |

   How the directions are proved:
   * **smooth ⇒ regular:** the vendored `Smooth.isRegularLocalRing_stalk`, which is proved there from the étale
     local structure over `𝔸ⁿ`.
   * **regular at a point ⇒ that point is in the smooth locus** (perfect field): the Jacobian criterion and the
     perfect-field step above, on an affine open.
   * **closed points suffice:** the smooth locus is open and `X` is a Jacobson space.
   * **any field:** a statement about `X_{K̄}` gives smoothness over the perfect field `K̄`, and Mathlib's
     `MorphismProperty.of_pullback_snd_of_descendsAlong` descends it along the fpqc cover `Spec K̄ → Spec K`.

   Definitions: `Nonsingular f` (the local rings at closed points are regular), `NonsingularAfter f L` and
   `RegularAfter f L` (the same for `X ×_K L`, with `L` a field over `K`), `GeometricallyRegular f`
   (`RegularAfter f L` for every field `L` over `K` in `Type u`).

3. **Dictionary for abelian varieties.**
   * `abVarOfNonsingular` (over a perfect field) and `abVarOfNonsingularAfter` (over any field) package a proper,
     geometrically integral group scheme as a `PkgI3.AbVar`, given that it is nonsingular (over `K`, resp. over
     `K̄`).
   * `exists_abVar_iff_nonsingular` and `exists_abVar_iff_nonsingularAfter` show that `∃ A : PkgI3.AbVar K, Q A` is
     equivalent to the same existential over nonsingular complete group varieties.
   * Only the scheme `X` and its group law are data in `PkgI3.AbVar`; the other fields are propositions.
     Accordingly, `abVarOfNonsingular_self : abVarOfNonsingular A.X _ = A` holds by `rfl` after `cases`.

4. **Variants of the existence-form abelian-variety leaves** with the print's hypothesis ("nonsingular") in place of
   Mathlib's `Smooth`, each proved equivalent to the original (both directions compiled):

   | original | where | variant | proved | rating |
   | --- | --- | --- | --- | --- |
   | `T09Pic.PicZeroAbVar` (open field `picZeroAbVar`) | base, `TailZ24.lean` | `ZInQ.Contrib.SmoothRegular.PicZeroAbVarNonsingular` | `picZeroAbVar_of_nonsingular` (+ converse), Contrib file | composite, nonsingular hypothesis in printed form (see §3) |
   | `HcmPrinted.WeierstrassAbVar` | origin/wip/hcm-g1 (not on base) | `HcmPrinted.WeierstrassAbVarNonsingular` | `weierstrassAbVar_of_nonsingular` (+ converse), `scratch/smooth-regular/T4.lean` | printed (see §3) |
   | `MainCMPolar.CMAbVarExists` | origin/wip/cm-primitive (not on base) | `MainCMPolar.CMAbVarExistsNonsingular` | `cmAbVarExists_of_nonsingular` (+ converse), `T4.lean` | printed up to Riemann's theorem (see §3) |

   `WeierstrassAbVar` and `CMAbVarExists` are not on the base, so their variants are checked in scratch against
   verbatim copies of their statements (`verbatim_check.py` compares the copies with the branch files). A
   contribution file for them belongs on top of those branches once they are merged. The proofs are one line each,
   by `exists_abVar_iff_nonsingular` at `K = ℂ`.

## 2. Statements

```lean
/-- Stacks 00TV ⇐ (open field), proved. -/
theorem regularSmoothPerfect : CurveSplit.RegularSmoothPerfect

def Nonsingular {K : Type u} [Field K] {X : Scheme.{u}} (_f : X ⟶ Spec (.of K)) : Prop :=
  ∀ x : X, IsClosed ({x} : Set X) → IsRegularLocalRing (X.presheaf.stalk x)

def NonsingularAfter {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (L : Type u) [Field L] [Algebra K L] : Prop :=
  Nonsingular (pullback.snd f (specMap K L))

def PicZeroAbVarNonsingular : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P),
    ∃ (B : Over (Spec (CommRingCat.of K))) (_ : GrpObj B) (_ : IsProper B.hom)
      (_ : GeometricallyIntegral B.hom), NonsingularAfter B.hom (AlgebraicClosure K) ∧
      ∃ j : B ⟶ P, letI := picardFunctorCommGrpObj A.X.hom rep
        IsOpenImmersion j.left ∧ Set.range j.left = T09Pic.identityComponent P ∧ IsMonHom j

theorem picZeroAbVar_of_nonsingular (h : PicZeroAbVarNonsingular) : T09Pic.PicZeroAbVar
theorem picZeroAbVarNonsingular_of_picZeroAbVar (h : T09Pic.PicZeroAbVar) : PicZeroAbVarNonsingular
```

`PicZeroAbVarNonsingular` is `PicZeroAbVar` with `IsPicZero rep B j` unfolded. The data `B : PkgI3.AbVar K` is
replaced by a group scheme `B` that is proper, geometrically integral and nonsingular over `K̄`; nothing else
changes.

## 3. Rating of the new leaves

* **`PicZeroAbVarNonsingular` — published, composite as before; the nonsingularity clause is now in printed form.**
  * Mumford, *Abelian varieties*, works over an algebraically closed field. There an abelian variety is a complete
    group variety, and §4 proves that group varieties are nonsingular (locators UNVERIFIED).
  * So "`B_{K̄}` is a nonsingular complete group variety" is what §13 (`Pic⁰ = Â` is an abelian variety) gives over
    `K̄`. Nonsingular means regular local rings at closed points (classical points over `K̄`).
  * Descent to `K` (Kleiman 9.5.1 and 9.5.3) and the geometric connectedness of the identity component
    (SGA 3 VI_A 2.4) are unchanged from the original leaf.
  * So the leaf is still a composite of three prints, exactly like `picZeroAbVar` (flag kept: "combines …"). What
    changes is that no step "nonsingular ⇒ smooth" is hidden in it: that step is now Lean glue
    (`smooth_of_nonsingularAfter_algebraicClosure`).
  * It is not stronger than the original: the converse `picZeroAbVarNonsingular_of_picZeroAbVar` is proved.
* **`WeierstrassAbVarNonsingular` — printed.**
  * `E_Λ : y²z = 4x³ − g₂xz² − g₃z³` with `Δ ≠ 0` is a nonsingular projective cubic (Silverman III.1.4, VI.3.6(a)).
  * It is an elliptic curve with its group law (III.2–3), uniformized by `z ↦ [℘(z), ℘'(z), 1]` (VI.3.6(b)).
  * Silverman's hypothesis is "nonsingular", which the variant states as regular local rings at closed points over
    `ℂ`. Numbers UNVERIFIED.
* **`CMAbVarExistsNonsingular` — printed up to Riemann's theorem.**
  * Shimura (1998 §6.2 Thm 4; Shimura–Taniyama 1961) gives an abelian variety `A` with `ℂ^g/Φ(𝔞) ≅ A(ℂ)`.
  * His abelian varieties are complete group varieties in Weil's sense, nonsingular by Mumford §4. Riemann's theorem
    (Mumford §3) gives the torus as a complete nonsingular projective variety.
  * The nonsingular hypothesis is the print's; the rest of the leaf is unchanged (its "weaker than the print" note
    still applies).
* **No new leaf for `regularSmoothPerfect`:** the field is discharged outright.

## 4. Checks

* `lake build ZInQKernel.Contrib.OneProof.RegularSmoothPerfect ZInQKernel.Contrib.OneProof.PicZeroAbVarNonsingular`:
  see `scratch/smooth-regular/log.md`.
* `#discharges` output: `scratch/smooth-regular/discharges-output.txt`, and §5 below.
* `scratch/smooth-regular/T4.lean` (Weierstrass and CM variants) compiles; axioms are standard.
* Autofold spec: `scratch/smooth-regular/autofold.json`. It discharges `regularSmoothPerfect` with no leaf and swaps
  `picZeroAbVar` for `picZeroAbVarNonsingular`. Dry-run output is in §5.

## 5. Outputs

(filled in below from the runs)
