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
2. **T14 and T15 narrow to two weaker Props, which can be stated without topology.**
   * *Narrowing.* The only consumer of the bundle fields `t14a`, `t14b`, `t15` is
     `GlueWP3.b3_degree_le_QM_of_T14_T15` (WP3.lean:290-307, VERIFIED read and grep). It feeds
     glue-descent's `LeafHasse` and `LeafLocalTwo`, and reciprocity enters only to supply the real
     place, which `LeafHasse` (finite places only) does not need. `T14Narrow.lean` proves the
     following over the kernel's definitions:
     * `BrauerHasseFin2C`: a `ℤ/2` cocycle of `G_ℚ` that is a coboundary at every finite prime is a
       coboundary. It is a consequence of T14 (`brauerHasseFin2C_of_T14`) and is equivalent to
       `LeafHasse` (`leafHasse_iff_brauerHasseFin2C`).
     * `LocalTwo2C`: the finite-place uniqueness half of T15 (`localTwo2C_of_T15`,
       `leafLocalTwo_iff_localTwo2C`).
     * `leaves_of_narrow : BrauerHasseFin2C → LocalTwo2C → LeafHasse ∧ LeafLocalTwo`.

     So the three Props T14a (Hasse with the real place), T14b (reciprocity with finiteness and
     parity) and T15 (existence and uniqueness, all places) can be announced as two weaker Props.
     The real place of T15 is a theorem anyway (t-brauer-purity).
   * *Topology-free.* Continuous `ℤ/2`-cochains on a compact, zero-dimensional group (every
     `Field.absoluteGaloisGroup K` with `char K = 0`) are exactly the cochains inflated from a
     finite quotient `G/N` with `N` open normal, and likewise for coboundaries
     (`ProfiniteCochains.lean`). Over the kernel's definitions (`ProfiniteKernel.lean`):
     * `TPurity2K.localH2CardC_iff_fin`
     * `brauerHasse2C_iff_fin`
     * `brauerReciprocity2C_iff_fin`

     `T14T15Final.lean` combines the two directions into one file:
     * `BrauerHasseFin2Fin`, `LocalTwo2Fin`: the narrowed Props, stated without topology;
     * `leaves_of_narrow_fin : BrauerHasseFin2Fin → LocalTwo2Fin → LeafHasse ∧ LeafLocalTwo`;
     * `narrow_fin_of_T14_T15`: both are consequences of T14 and T15.

   The arithmetic content is **not proved**: the Hasse principle for `Br(ℚ)[2]`, and
   `|Br(ℚ_p)[2]| ≤ 2` from local class field theory (§4).
3. **T1 (Zariski–Nagata, `PkgI2.PurityBranchLocus`) is equivalent to Nagata's form T1″.**
   T1″ = `TPurity2K.PurityBranchLocusLocal`, stated over a regular **local** ring `R` with
   `[Module.Finite R S]` and a prime `q` of `S` over `𝔪_R`, such that `S_q` is a normal domain,
   `dim S_q = dim R ≥ 2`, and `R → S` is unramified at every height-one `q' ≤ q`. The conclusion is
   `Algebra.IsEtaleAt R q`. There is no quasi-finiteness hypothesis and no localization of the base.
   Three glue steps are proved:
   * **dimension one** (`purity_dim_one`). In dimension one, quasi-finiteness and Nakayama make
     `R_p → S_q` injective, so `R_p` is a DVR, `S_q` is torsion-free and hence flat, and
     flat + unramified ⇒ étale. Mathlib has the last step only under global flatness; I proved a
     local version, `isEtaleAt_of_isUnramifiedAt_of_flat_local`.
   * **reduction to finite algebras** (`purityBranchLocus_of_finite`), via Mathlib's Zariski Main
     Theorem: `S'[1/r] ≅ S[1/r]` with `S' ⊆ S` module-finite and `r ∉ q`. Every hypothesis
     transfers along `S'_{q∩S'} ≅ S_q`, and the primes below `q` correspond. Together with the
     first step this gives T1′ = `PurityBranchLocusFiniteGe2` (finite, `dim ≥ 2`, base not yet
     local).
   * **reduction to a local base** (`finiteGe2_of_local`): localize at `p = q ∩ R`. Then `S_p` is
     finite over `R_p`, `Q = qS_p` lies over `𝔪_{R_p}`, `(S_p)_Q ≅ S_q`, height-one primes
     correspond, and étale over `R_p` implies étale over `R`.

   Kernel form (`T1Kernel.lean`):
   * `TPurity2K.purityBranchLocus_of_local : PurityBranchLocusLocal.{u} → PkgI2.PurityBranchLocus.{u}`;
   * the converse `local_of_purityBranchLocus`;
   * the same pair for T1′ (`purityBranchLocus_of_finiteGe2`, `finiteGe2_of_purityBranchLocus`);
   * the `ObjBridge` versions.

   So **T1 ⇔ T1′ ⇔ T1″**, all proved. The theorem left in T1″ is the classical Zariski–Nagata
   purity of the branch locus for a finite cover of a regular local ring by a normal one, in
   dimension ≥ 2 (Nagata 1959, Illinois J. Math. 3; Auslander 1962 for dimension 2; SGA 1 X 3.1;
   STANDARD, locators UNVERIFIED). It is not proved; §4 says what is missing.

**Recommendations for the announcement.**
* (i) T2 is glue: fill `t2` with `TBrauerPurityT2K.abhyankarDVR`.
* (ii) Announce T1 as T1″ (`PurityBranchLocusLocal`). It is a special case of the published
  statement, it is Nagata's own form (regular local base, finite normal cover), and it is
  provably equivalent to T1 in Lean.
* (iii) Announce T14 as the single Prop `BrauerHasseFin2C`, a consequence of
  Albert–Brauer–Hasse–Noether with reciprocity: a class in `H²(G_ℚ, ℤ/2)` that is trivial at
  every prime is trivial. Announce T15 as `LocalTwo2C`, a consequence of `Br(ℚ_p)[2] ≅ ℤ/2`. These
  are glue-descent's `LeafHasse` and `LeafLocalTwo` in cochain form. If topology-free statements
  are preferred, use `BrauerHasseFin2Fin` and `LocalTwo2Fin` (`T14T15Final.lean`). The
  three-Prop forms remain available, and Lean proves they imply the narrowed ones.

## 2. Statement audit of the new forms

**T1′ `PurityBranchLocusFiniteGe2`.** These are T1's binders with three changes:
`[Algebra.FiniteType R S]` becomes `[Module.Finite R S]`, `Algebra.QuasiFiniteAt R q` is dropped,
and `1 ≤ dim` becomes `2 ≤ dim`. Module-finite implies finite type (an instance) and quasi-finite
at every prime (`QuasiFinite` of a finite algebra, then of a localization; instances, VERIFIED by
the proof of `finiteGe2_of_purityBranchLocus`). So T1′ is an instance of T1 and hence of the
published theorem. It is not vacuous: `S = R` regular of dimension 2 satisfies all hypotheses. The
hypotheses `IsIntegrallyClosed S_q` and `IsRegularLocalRing R_p` remain. The classical proof uses
both: normality for Serre's criterion, regularity for Auslander–Buchsbaum. The dimension-one proof
here does not use normality.

**T1″ `PurityBranchLocusLocal`.** This is T1′ over a base with `[IsRegularLocalRing R]` (which
supplies Noetherian and local), with `q ∩ R = 𝔪_R`, `dim S_q = dim R` and `2 ≤ dim R`. It is the
case `p = 𝔪` of T1′ once `R_𝔪 ≅ R` (`equivAtMaximal`), and `local_of_finiteGe2` proves this.
`S = R` of dimension 2 shows it is not vacuous.

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
| `T1Local.lean` (Mathlib only) | `PurityBranchLocusLocal`, `locLocEquiv : (S_p)_Q ≃ₐ[R] S_{Q∩S}`, `equivAtMaximal`, `finiteGe2_of_local`, `local_of_finiteGe2` | compiles |
| `T1Reduced.lean` (Mathlib only; copies of the three above) | `PurityBranchLocusFiniteGe2`, `PurityBranchLocusLocal`, `purityBranchLocus_of_finiteGe2`, `finiteGe2_of_purityBranchLocus`, `purityBranchLocus_of_local`, `local_of_purityBranchLocus` | compiles |
| **`T1Kernel.lean`** (imports `ZInQKernel.HDecomp.Objects`) | **`TPurity2K.purityBranchLocus_of_local`**, `local_of_purityBranchLocus`, `purityBranchLocus_of_finiteGe2`, `finiteGe2_of_purityBranchLocus`, `objBridge_purityBranchLocus_of_local`, `objBridge_purityBranchLocus_of_finiteGe2` | compiles |
| `ProfiniteCochains.lean` (Mathlib only; I6Base defs copied verbatim) | `exists_nhds_one_invariant`, `exists_openNormalSubgroup_invariant(₂)`, `continuous_of_invariant(₂)`, `isCocycle2_iff`, `isCoboundary2_iff`, `compactSpace_absoluteGaloisGroup`, `zeroDimensionalSpace_absoluteGaloisGroup` (char 0), `h2TwoClasses_iff_fin`, `localH2CardC_finite_iff_fin` | compiles |
| **`ProfiniteKernel.lean`** (imports `ZInQKernel.HDecomp.Conductor.I6Base`) | **`TPurity2K.localH2CardC_iff_fin`, `brauerHasse2C_iff_fin`, `brauerReciprocity2C_iff_fin`** | compiles |
| **`T14Narrow.lean`** (imports `ZInQKernel.HDecomp.Descent.WP3`) | `BrauerHasseFin2C`, `LocalTwo2C`, `brauerHasseFin2C_of_T14`, `brauerHasse2C_of_fin`, `leafHasse_iff_brauerHasseFin2C`, `localTwo2C_of_T15`, `leafLocalTwo_iff_localTwo2C`, **`leaves_of_narrow`** | compiles |
| **`T14T15Final.lean`** (imports Mathlib and `…Descent.WP3`; the two above concatenated) | `BrauerHasseFin2Fin`, `LocalTwo2Fin`, `brauerHasseFin2C_iff_fin`, `localTwo2C_iff_fin`, **`leaves_of_narrow_fin`**, **`narrow_fin_of_T14_T15`** | compiles |
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

* **T1″ (dimension ≥ 2, finite, local base).** The classical proof has two parts. *Dimension 2* (Auslander):
  `S_q` normal of dimension 2 is Cohen–Macaulay (Serre's criterion), so it is free over `R_p` by
  Auslander–Buchsbaum, and the branch locus of a finite free map is the discriminant divisor.
  *Dimension ≥ 3*: either Nagata's reduction or Grothendieck's purity (SGA 2 X 3.4, UNVERIFIED).
  Mathlib v4.35 has depth and regular sequences but neither Serre's criterion nor
  Auslander–Buchsbaum (t-brauer-purity §4, VERIFIED by grep there). The consumer of T1 is Prop. TS
  for the degree-324! cover over a 2-dimensional base (`ℙ¹_ℤ`-type). It needs only dimension
  `≤ 2`, so in practice it needs only the dimension-2 case of T1″ (SPECULATIVE: the consumer is not
  in Lean yet; h-decomposition.md G2, WP3).
* **T15 at `ℚ_p` and T14 (now `LocalTwo2C`, `BrauerHasseFin2C`).** Both need class field theory and the Kummer bridge
  `H²(G_K, ℤ/2) ≅ Br(K)[2]` (t-brauer-purity §4). The finiteness conjunct of T14b is no longer needed (narrowing above). For the record, it is
  elementary modulo local field theory, by the following argument. A cocycle inflated from `Gal(L/ℚ)`
  restricts, at `p` unramified in `L`, to an inflation from the cyclic decomposition group, and it
  dies on `G_{ℚ_p}` because `G_{ℚ_p} → D` factors through `Gal(ℚ_p^{(2|D|)}/ℚ_p) ≅ ℤ/2|D|`, where
  inflation `H²(ℤ/n, ℤ/2) → H²(ℤ/2n, ℤ/2)` is zero. This needs the unramified extensions of `ℚ_p`
  and Frobenius compatibility, which are not in Mathlib (SPECULATIVE assessment; not attempted).

## 5. Reproduction

```
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
lake build ZInQKernel.HDecomp.Objects ZInQKernel.HDecomp.Descent.WP3   # oleans for kernel forms
lake env lean scratch/t-purity2/EtaleLocal.lean
lake env lean scratch/t-purity2/T1Dim1.lean
lake env lean scratch/t-purity2/T1Finite.lean
lake env lean scratch/t-purity2/T1Local.lean
lake env lean scratch/t-purity2/T1Reduced.lean
lake env lean scratch/t-purity2/T1Kernel.lean
lake env lean scratch/t-purity2/ProfiniteCochains.lean
lake env lean scratch/t-purity2/ProfiniteKernel.lean
lake env lean scratch/t-purity2/T14Narrow.lean
lake env lean scratch/t-purity2/T14T15Final.lean
lake env lean scratch/t-brauer-purity/T2Kernel.lean
```
Each file ends with `#print axioms`, which reports `[propext, Classical.choice, Quot.sound]`.
Each takes about 1–2 minutes.
