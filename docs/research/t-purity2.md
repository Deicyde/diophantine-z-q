# t-purity2: leaves T1, T2, T14, T15 (continuation of t-brauer-purity)

Status: research note (task t-purity2, 2026-11-13). Lean companion: `scratch/t-purity2/` (results
log `log.md`). Base 883c4ddf (origin/wip/integrate-w35c). No file under `ZInQKernel/`,
`blueprint/`, or another task's notes or scratch was edited.

Marks: **VERIFIED** (read in a source named here, computed, or compiled), **STANDARD** (published,
with reference), **SPECULATIVE** (an assessment). There is no network on this host, so theorem
numbers given from memory are **UNVERIFIED**.

## 1. Verdict

All Lean claims below are VERIFIED: compiled with `lake env lean`, no `sorry`, axioms
`[propext, Classical.choice, Quot.sound]`. Each kernel form imports the kernel module and uses the
kernel's own definition; nothing is copied except proofs.

1. **T2 (Abhyankar, `PkgI2.AbhyankarDVR`) is proved, and the proof still compiles at this base.**
   The task brief says only the case `L = K` and the lower half are proved. That is out of date:
   t-brauer-purity proved the whole leaf. I rebuilt `ZInQKernel.HDecomp.Objects` and recompiled
   `scratch/t-brauer-purity/T2Kernel.lean` here: `TBrauerPurityT2K.abhyankarDVR : PkgI2.AbhyankarDVR.{0}`
   and `abhyankarDVR_objBridge` compile with standard axioms. **T2 can move from leaf to glue.**
2. **T15 (and T14) no longer involve topology.** I proved that continuous `ℤ/2`-cochains on a
   compact, zero-dimensional group (in particular every `Field.absoluteGaloisGroup K` with
   `char K = 0`) are exactly the cochains inflated from a finite quotient `G/N`, `N` open normal,
   and the same for coboundaries (`ProfiniteCochains.lean`). Over the kernel's definitions
   (`ProfiniteKernel.lean`):
   * `TPurity2K.localH2CardC_iff_fin : PkgI6.LocalH2CardC ↔ (∀ p, H2TwoClassesFin G_{ℚ_p}) ∧ H2TwoClasses G_ℝ`.
     The real conjunct is already a theorem (t-brauer-purity, `TBrauerPurityK.h2TwoClasses_real`).
   * `TPurity2K.brauerHasse2C_iff_fin : PkgI6.BrauerHasse2C ↔ BrauerHasse2Fin`
   * `TPurity2K.brauerReciprocity2C_iff_fin : PkgI6.BrauerReciprocity2C ↔ BrauerReciprocity2Fin`

   The finite-place content of T15 (`|Br(ℚ_p)[2]| = 2`, local class field theory) is **not
   proved**, and neither is T14 (§4).
3. **T1 (Zariski–Nagata, `PkgI2.PurityBranchLocus`) is equivalent to a narrower leaf T1′.**
   T1′ = `TPurity2K.PurityBranchLocusFiniteGe2`: the same statement for a **module-finite** `R → S`,
   with `dim S_q = dim R_p ≥ 2` and no quasi-finiteness hypothesis. Two glue steps are proved:
   * **dimension one** (`purity_dim_one`). In dimension one, quasi-finiteness and Nakayama make
     `R_p → S_q` injective, so `R_p` is a DVR, `S_q` is torsion-free and hence flat, and
     flat + unramified ⇒ étale. Mathlib has the last step only under global flatness; I proved a
     local version, `isEtaleAt_of_isUnramifiedAt_of_flat_local`.
   * **reduction to finite algebras** (`purityBranchLocus_of_finite`), via Mathlib's Zariski Main
     Theorem: `S'[1/r] ≅ S[1/r]` with `S' ⊆ S` module-finite and `r ∉ q`. Every hypothesis
     transfers along `S'_{q∩S'} ≅ S_q`, and the primes below `q` correspond.

   Kernel form (`T1Kernel.lean`): `TPurity2K.purityBranchLocus_of_finiteGe2 :
   PurityBranchLocusFiniteGe2.{0} → PkgI2.PurityBranchLocus.{0}`, the `ObjBridge` version, and the
   converse `finiteGe2_of_purityBranchLocus`. So T1 ⇔ T1′. The theorem left in T1′ is the classical
   Zariski–Nagata purity for a finite cover of a regular local ring by a normal one, in dimension
   ≥ 2 (Nagata 1959, Illinois J. Math. 3; SGA 1 X 3.1/3.4; Auslander 1962 for dimension 2;
   STANDARD, locators UNVERIFIED). It is not proved; §4 says what is missing.

**Recommendations for the announcement.**
* (i) T2 is glue: fill `t2` with `TBrauerPurityT2K.abhyankarDVR`.
* (ii) Announce T1 as T1′ (`PurityBranchLocusFiniteGe2`). It is a special case of the published
  statement, closer to the textbook form (finite covers), and its proof is provably equivalent to
  T1's.
* (iii) Announce T15 as its finite-place uniqueness half. Glue uses only that half
  (`leafLocalTwo_of_T15`, WP3.lean:231, VERIFIED read). The `…Fin` forms give a contributor a
  statement free of topology. The existence half and the real place are not needed; the real
  place is proved anyway.
* (iv) Announce T14 in either form; `brauerHasse2C_iff_fin` and `brauerReciprocity2C_iff_fin` make
  the two forms interchangeable.

## 2. Statement audit of the new forms

**T1′ `PurityBranchLocusFiniteGe2`.** These are T1's binders with three changes:
`[Algebra.FiniteType R S]` becomes `[Module.Finite R S]`, `Algebra.QuasiFiniteAt R q` is dropped,
and `1 ≤ dim` becomes `2 ≤ dim`. Module-finite implies finite type (an instance) and quasi-finite
at every prime (`QuasiFinite` of a finite algebra, then of a localization; instances, VERIFIED by
the proof of `finiteGe2_of_purityBranchLocus`). So T1′ is an instance of T1 and hence of the
published theorem. It is not vacuous: `S = R` regular of dimension 2 satisfies all hypotheses. The
hypotheses `IsIntegrallyClosed S_q` and `IsRegularLocalRing R_p` are both still needed. With
`S_q` not normal, the conclusion fails: for example `R = k[x,y]` and `S = R[z]/(z² − x²y)` give a
branch locus that is not pure (the classical counterexample, SPECULATIVE recollection). Note that
the dimension-one proof does not use normality.

**`H2TwoClassesFin`, `IsCocycle2Fin`, `IsCoboundary2Fin`, `BrauerHasse2Fin`,
`BrauerReciprocity2Fin`.** Each is the kernel Prop with `Continuous` replaced by "invariant under
right multiplication by some open normal subgroup" (two-sided for `ε`). The `_iff_fin` theorems
prove them equivalent to the kernel Props, so the audit of t-brauer-purity §2 carries over
unchanged.

## 3. Lean results (`scratch/t-purity2/`)

| File | Main declarations | Status |
|---|---|---|
| `EtaleLocal.lean` (Mathlib only) | `isEtaleAt_of_isUnramifiedAt_of_flat_local`: `R → S` finitely presented, `S_q` flat over `R_p`, unramified at `q` ⇒ `IsEtaleAt R q` | compiles |
| `T1Dim1.lean` (Mathlib only; `PkgI2.PurityBranchLocus` copied verbatim) | `eq_bot_of_isPrime_of_ne_maximalIdeal` (Nakayama), `purity_dim_one`, `PurityBranchLocusGe2`, `purityBranchLocus_of_ge2`, `ge2_of_purityBranchLocus` | compiles |
| `T1Finite.lean` (Mathlib only) | `exists_pow_mul_mem`, `isLocalization_atPrime_of_pow`, `locEquiv : S'_{P∩S'} ≃ₐ[R] S_P`, `PurityBranchLocusFinite`, `purityBranchLocus_of_finite` | compiles |
| `T1Reduced.lean` (Mathlib only; copies of the two above) | `PurityBranchLocusFiniteGe2`, `purityBranchLocus_of_finiteGe2`, `finiteGe2_of_purityBranchLocus` | compiles |
| **`T1Kernel.lean`** (imports `ZInQKernel.HDecomp.Objects`) | **`TPurity2K.purityBranchLocus_of_finiteGe2`**, `objBridge_purityBranchLocus_of_finiteGe2`, `finiteGe2_of_purityBranchLocus` | compiles |
| `ProfiniteCochains.lean` (Mathlib only; I6Base defs copied verbatim) | `exists_nhds_one_invariant`, `exists_openNormalSubgroup_invariant(₂)`, `continuous_of_invariant(₂)`, `isCocycle2_iff`, `isCoboundary2_iff`, `compactSpace_absoluteGaloisGroup`, `zeroDimensionalSpace_absoluteGaloisGroup` (char 0), `h2TwoClasses_iff_fin`, `localH2CardC_finite_iff_fin` | compiles |
| **`ProfiniteKernel.lean`** (imports `ZInQKernel.HDecomp.Conductor.I6Base`) | **`TPurity2K.localH2CardC_iff_fin`, `brauerHasse2C_iff_fin`, `brauerReciprocity2C_iff_fin`** | compiles |
| `scratch/t-brauer-purity/T2Kernel.lean` (t-brauer-purity's file, recompiled unchanged) | `TBrauerPurityT2K.abhyankarDVR : PkgI2.AbhyankarDVR.{0}` | compiles at this base |

**How the dimension-one case is proved.** Let `p = q ∩ R`. The hypotheses give `dim S_q = 1`, so
`q` has height one (`IsLocalization.AtPrime.ringKrullDim_eq_height`) and `R → S` is unramified at
`q`.
1. `R_p` is regular of dimension one, so `finrank 𝔪/𝔪² = 1` and its maximal ideal is principal
   (`finrank_cotangentSpace_le_one_iff`).
2. Let `P = ker(R_p → S_q)`. This is prime because `S_q` is a domain. Suppose `P = 𝔪`. Then `⊥`
   and the maximal ideal of `S_q` both lie over `p`, so they are equal by
   `QuasiFinite.eq_of_le_of_under_eq`, and `S_q` would be a field of dimension 0, a contradiction.
   Hence `P ≠ 𝔪`, so `x ∉ P` where `𝔪 = (x)`, and `P = xP`. Nakayama
   (`Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`) then gives `P = 0`.
3. So `R_p ↪ S_q`, which makes `R_p` a domain and hence a DVR (`IsDiscreteValuationRing.TFAE`).
   `S_q` is torsion-free over it, and therefore flat.
4. Flatness plus unramifiedness gives étaleness. `isEtaleAt_of_isUnramifiedAt_of_flat_local` adapts
   Mathlib's `IsSmoothAt.of_formallySmooth_fiber`: global flatness is replaced by `S_q` flat over
   `R_p`, and the fibre `κ(p) ⊗ S_q` is formally étale (`FormallyEtale.of_formallyUnramified_of_field`).
   Then `FormallySmooth.of_formallySmooth_residueField_tensor` applies with `P = S_p`.

**How the reduction to finite algebras is proved.** Mathlib's
`Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective` gives a module-finite
`S' ⊆ S` and an element `r ∈ S' \ q` with `S'[1/r] → S[1/r]` bijective. Hence every `x ∈ S` has
`r^N x ∈ S'` (`exists_pow_mul_mem`). For a prime `P ∌ r` of `S`, `S_P` is the localization of `S'`
at `P ∩ S'` (`isLocalization_atPrime_of_pow`, checking the three localization axioms directly), so
`locEquiv : S'_{P∩S'} ≃ₐ[R] S_P`. Each hypothesis then transfers:
* regularity of the base: `(q∩S')∩R = q∩R`;
* domain, normality, dimension: along `locEquiv` at `q`;
* unramifiedness at a height-one prime `q'' ≤ q∩S'`: lift `q''` to `P = ψ⁻¹(𝔪)`, where
  `ψ : S → S[1/r] ≅ S'[1/r] → S'_{q''}`. Then `P ∩ S' = q''`, `r ∉ P`, `P ≤ q`, and `ht P = 1`
  (via `locEquiv` at `P`). Unramifiedness at `P` is a hypothesis, and it transports back.

The conclusion transports along `locEquiv` at `q` (`FormallyEtale.of_equiv`).

**How the cochain results are proved.** A continuous map `H → ZMod 2` on a compact group `H` (take
`H = G × G`) has clopen fibres `F_c`. `compact_open_separated_mul_right` gives `V_c ∈ 𝓝 1` with
`F_c · V_c ⊆ F_c`, and `V = ⋂ V_c` makes the map right-`V`-invariant. Choose a box inside `V`, and
then an open normal subgroup inside the box (`ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one`,
which needs zero-dimensionality). Conversely, invariance under an open subgroup gives local
constancy and hence continuity. For `G_K` with `char K = 0`, `IsGalois K K^al` holds, so
`CompactSpace Gal(K^al/K)` follows from Mathlib's instance. The instance must be stated at the type
`Gal(…)` because `absoluteGaloisGroup` is a `def`. Zero-dimensionality follows from T2 plus totally
disconnected plus compact.

## 4. What remains

* **T1′ (dimension ≥ 2, finite).** The classical proof has two parts. *Dimension 2* (Auslander):
  `S_q` normal of dimension 2 is Cohen–Macaulay (Serre's criterion), so it is free over `R_p` by
  Auslander–Buchsbaum, and the branch locus of a finite free map is the discriminant divisor.
  *Dimension ≥ 3*: either Nagata's reduction or Grothendieck's purity (SGA 2 X 3.4, UNVERIFIED).
  Mathlib v4.35 has depth and regular sequences but neither Serre's criterion nor
  Auslander–Buchsbaum (t-brauer-purity §4, VERIFIED by grep there). The consumer of T1 is Prop. TS
  for the degree-324! cover over a 2-dimensional base (`ℙ¹_ℤ`-type). It needs only dimension
  `≤ 2`, so in practice it needs only the dimension-2 case of T1′ (SPECULATIVE: the consumer is not
  in Lean yet; h-decomposition.md G2, WP3).
* **T15 at `ℚ_p` and T14.** Both need class field theory and the Kummer bridge
  `H²(G_K, ℤ/2) ≅ Br(K)[2]` (t-brauer-purity §4). The finiteness conjunct of T14 is elementary
  modulo local field theory, by the following argument. A cocycle inflated from `Gal(L/ℚ)`
  restricts, at `p` unramified in `L`, to an inflation from the cyclic decomposition group, and it
  dies on `G_{ℚ_p}` because `G_{ℚ_p} → D` factors through `Gal(ℚ_p^{(2|D|)}/ℚ_p) ≅ ℤ/2|D|`, where
  inflation `H²(ℤ/n, ℤ/2) → H²(ℤ/2n, ℤ/2)` is zero. This needs the unramified extensions of `ℚ_p`
  and Frobenius compatibility, which are not in Mathlib (SPECULATIVE assessment; not attempted).

## 5. Reproduction

```
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
lake build ZInQKernel.HDecomp.Objects ZInQKernel.HDecomp.Conductor.I6Base   # oleans for kernel forms
lake env lean scratch/t-purity2/EtaleLocal.lean
lake env lean scratch/t-purity2/T1Dim1.lean
lake env lean scratch/t-purity2/T1Finite.lean
lake env lean scratch/t-purity2/T1Reduced.lean
lake env lean scratch/t-purity2/T1Kernel.lean
lake env lean scratch/t-purity2/ProfiniteCochains.lean
lake env lean scratch/t-purity2/ProfiniteKernel.lean
lake env lean scratch/t-brauer-purity/T2Kernel.lean
```
Each file ends with `#print axioms`, which reports `[propext, Classical.choice, Quot.sound]`.
Each takes about 1–2 minutes.
