# rv-leaves48, agent A: the I2 / I3 / T9 cluster (17 leaves)

Read-only review. No Lean was run. Line numbers refer to `scratch/h-decomposition/Leaves.lean`.

## Summary table

There are no non-OK verdicts, so the table cannot be sorted worst first. It follows the order of the file.

| leaf | Lean name (line) | verdict | reason |
|---|---|---|---|
| r6 | `PkgI2.RaynaudCriterion` (1474) | OK (locator caveat) | Hypotheses: `m ≥ 3`, `m ∈ O^×`, and every `σ ∈ Aut(K̄/K)` fixes `A(K̄)[m]` (this is `A[m]` rational). Conclusion: `(σ−1)² = 0` on `A[ℓⁿ]` for every inertia `σ`, every `ℓ ∈ O^×` and every `n`. This is SGA 7 IX 4.7 plus 3.5(⇒). Semistability does not depend on `ℓ`, so "all `ℓ`" is correct. The `m = 3` threshold is STANDARD ("n ≥ 3 premier à p"), but the locator is still UNVERIFIED (locators.md) |
| r7a | `PkgI2.NeronOggShafarevich` (1416) | OK | (a)⇔(b)⇔(c) of Serre–Tate Thm 1 (number UNVERIFIED). `IsUnit (m:O)` is "p ∤ m", and it covers residue characteristic 0. Inertia in `Aut(K̄/K)` at `w ⊂ K̄` restricts isomorphically to inertia in `Gal(K_s/K)` at `w ∩ K_s`, because `K̄/K_s` is purely inseparable |
| r7b | `PkgI2.SerreTatePotentialGood` (1437) | OK | One `K'` before `∀σ ∀n`. Both sides are equivalent, for the **same** `K'`, by NOS(c) over `K'` with `m = ℓⁿ`. `w ∩ K'` is automatically a DVR, and `I_w ∩ G_{K'}` is the inertia of `w` over `K'`. It is a consequence of Thm 1 / Thm 2 |
| r8 | `PkgI2.GrothendieckMonodromy` (1457) | OK | SGA 7 IX 3.6 + 3.5(⇒). One `K'` serves every `ℓ`, because semistability does not depend on `ℓ`. The finite level follows from `T_ℓ ↠ A[ℓⁿ]`. Identical to `LeafPush.R08_GrothendieckMonodromy` (11801) |
| t1 | `PkgI2.PurityBranchLocus` (1322) | OK | Matches Stacks 0BMB (normal, regular, quasi-finite at x, `dim = dim ≥ 1`, unramified at the codimension-1 generizations `q' ⊆ q`). Mathlib's `Algebra.IsEtaleAt R q` is `FormallyEtale R S_q` (VERIFIED, `RingTheory/Etale/Locus.lean:35`). This follows from étale at `q` in the usual sense, so the conclusion is no stronger. `QuasiFiniteAt` is `QuasiFinite R S_q`, which for finite type is "isolated in its fibre" (VERIFIED docstring, `QuasiFinite/Basic.lean:368`). `IsUnramifiedAt` is formally unramified at `S_{q'}` (VERIFIED) |
| t2 | `PkgI2.AbhyankarDVR` (1565) | OK | `Q.ramificationIdx R` is Mathlib's new length-based index `length_{S_Q}(S_Q / m_R S_Q)` (VERIFIED, `RingTheory/RamificationInertia/Ramification.lean:53`). It is the usual `e` here because both integral closures are Dedekind: `M/K` is separable, since `n ∈ R^×` forces `char ∤ n`. `X^n − π` is Eisenstein, so `[K(t):K] = n` with total ramification. Abhyankar makes `M/K(t)` unramified, so `e = n` and the residue extension is separable. The scalar-tower data is consistent (`R→M = R→L→M` follows from the three towers) |
| t3 | `PkgI2.NeronMappingAbelianScheme` (1492) | OK | BLR 1.2 Prop. 8 (UNVERIFIED). `ℬ` is the Néron model of `ℬ_K`; apply it with the smooth test scheme `Y = 𝒜`. All `O`-morphisms are allowed, and that is correct. `K = Frac O` holds automatically for a valuation subring |
| t4 | `PkgI2.ReductionTorsionBijective` (1530) | OK | Part 1: `x'` exists by the valuative criterion for an arbitrary valuation ring `w`, and is unique by separatedness (`w → K̄` injective). Reduction is a homomorphism, so `y^m = 1`. Part 2: `𝒜[m]` is finite étale over `O` (`m ∈ O^×`), and `w` is strictly henselian (normal local domain with algebraically closed fraction field), so `𝒜[m](w) ≅ 𝒜[m](κ(w))`. Checked `IsReductionOf` (1513): composites and `pullback.fst` are correct |
| t5 | `PkgI2.TorsionStructure` (1548) | OK | `A(K̄)[n] ≅ (ℤ/n)^{2g}` as groups, for `n ∈ K^×` and `g = topologicalKrullDim`. Mumford §4 over `K̄`, and `A(K̄) = A_{K̄}(K̄)` |
| t9 | `LeafPush.T09_WeilPairing` (11839) | OK | Take `e n x y = e_n(x, λy)`, where `λ = φ_L` for an ample `L` over `K` (abelian varieties are projective over any field, STANDARD), and `d = deg λ` (`ψλ = [d]`). Checked the compatibility exponent (see below): `e_n(x^m, y^m) = e_{mn}(x,y)^m` is correct (`^m`, not `^{m²}`). Alternation `e^L_n(x,x)=1` for `λ = φ_L` is STANDARD (Mumford §23, UNVERIFIED locator). Equivariance has the correct left-action convention |
| r9a | `PkgI3.FaltingsSemisimple` (2784) | OK | `IsSemisimpleRepresentation ρ` is `IsSemisimpleModule k[G] ρ.asModule` (VERIFIED, `RepresentationTheory/Semisimple.lean:34`). For a finite-dimensional `V_ℓ`, abstract and continuous semisimplicity coincide (every subspace is closed) |
| r9b | `PkgI3.FaltingsTate` (2791) | OK | The integral `ℤ_ℓ ⊗ Hom → Hom_{G_K}(T_ℓA, T_ℓB)` is bijective (Faltings Satz 4 / Kor. 1, UNVERIFIED pages). Number field, all `ℓ` |
| t6 | `PkgI3.HomFreeFinite` (2805) | OK | Mumford §19 Thm 3 over `k̄`, carried down to `k`: `Hom_k ⊆ Hom_{k̄}` (faithful base change), and `ℤ_ℓ` is flat. `ℓ ≠ char k` is kept for injectivity. `WithBot ℕ∞` arithmetic on finite dimensions is harmless |
| t7 | `PkgI3.CharPolyIndepOfEll` (2814) | OK | Degree not stated, so the leaf is weaker than Mumford §19 Thm 4. `ℓ ≠ char k`. Any finite `ℚ_ℓ`-basis of `V_ℓ` |
| t8 | `PkgI3.PoincareReducibility` (2827) | OK | Char 0. `EndDivision A` is equivalent to k-simple in char 0. `ker(f)°` is an abelian subvariety, so `f` is an isogeny onto its image `A'`. A Poincaré complement `Z ⊆ J` gives `(f, incl)` surjective with finite kernel, hence finite. Parse: `(fst≫f)*(snd≫g)` (infixr 80 vs infixl 70). The citation repair from rv-leaves-b (Milne 1986 Prop. 12.1) is applied in the docstring |
| t26 | `PkgI3.TateModuleFree` (2798) | OK | `T_ℓ ≅ ℤ_ℓ^{2g}` for `ℓ ≠ char k`. The zero abelian variety gives rank 0 = 2·0 |
| t27 | `PkgI3.QMDichotomyYu` (2845) | OK | rv-loc-leaves (i) repair applied: `QuatIndefinite a b` is now a hypothesis (2843, `0<a ∨ 0<b`, which is `B⊗ℝ ≅ M₂(ℝ)`). Char 0, `k = k̄`. Yu's "ℚ(√d) splits B" is dropped (weaker). Albert check: a non-simple `A ~ E²` with `E` non-CM gives `M₂(ℚ)`, which cannot contain a division `B`. Products of non-isogenous curves give fields. A CM quartic field contains no quaternion algebra. So only the two stated cases remain |

**Verdict: no leaf in this cluster is OVER-STRONG, VACUOUS or MISSTATED.** Two caveats concern locators, not Lean: R6 at `m = 3`, and R7/R8/R9 are originals not read.

## Changes since rv-leaves-b (VERIFIED by a textual diff, script run 2026-11-12)

- All nine I2 leaves and their helpers (`IsInertia`, `HasGoodReduction`, `IsReductionOf`, `InertiaTrivialOn`, `UnipSq`, `torsion`, `toW`, `specOver`) are byte-identical to `scratch/pkg-I2/I2.lean`.
- The six I3 leaves `FaltingsSemisimple`, `FaltingsTate`, `TateModuleFree`, `HomFreeFinite`, `CharPolyIndepOfEll`, `PoincareReducibility`, and the helpers `EndDivision`, `galT`, `galRep`, `tateHomZl`, `homGroup`, are byte-identical to `scratch/pkg-I3/I3.lean`.
- `T09_WeilPairing` is byte-identical to `scratch/leaf-push/Push.lean`.
- Only T27 changed: `QMDichotomy` became `QMDichotomyYu` (rv-loc-leaves repair (i)), and the bundle field `t27` (19183) now points to `QMDichotomyYu`.
- rv-leaves-b repair 2 (T8 citation) is present in the docstring (2820-2826).
- rv-leaves-b repairs 3 and 4 (I6, conductor) are outside this cluster.

## Object layer, checked independently

- **Inertia** (`IsInertia`, 1381). `decompositionSubgroup K w` is the stabilizer of `w` under the pointwise action (VERIFIED: `RamificationGroup.lean:29`, `ValuationSubring.lean:782-807`, `g • S` = image subring). `inertiaSubgroup` is the kernel of `toRingAut` on `ResidueField w` (VERIFIED, `:49`). This is the genuine inertia group.
- **Geometric conditions.** `GeometricallyIntegral` and `GeometricallyConnected` quantify over fields `K : Type u` in the scheme universe (VERIFIED, `Geometrically/Basic.lean:46`). At `.{0}` this is the usual notion. Fibres of a group scheme are nonempty, so `ConnectedSpace`'s nonemptiness requirement causes no trouble.
- **Galois action** (`galAct`, `galHom`). `σ·x = Spec(σ) ≫ x` acts on coordinates by `σ`. It is a left action, which is the convention T9's equivariance clause needs.
- **`UnipSq`** (1406). `σ²x·(σx)⁻¹·(σx)⁻¹·x = 1` is `(σ−1)²x = 0`, because the point group is commutative (Mathlib, commutativity of proper geometrically integral group schemes).
- **Junk-value traps.** I looked for them and found none:
  - `ramificationIdx` is 0 only for non-prime `Q`, and the leaf's `Q` are prime.
  - `topologicalKrullDim` is finite for varieties.
  - `finrank` occurs only together with `Module.Finite`, which is a conjunct (T26) or holds automatically (T6, finite rank asserted in the same conjunction).
  - There is no Nat subtraction or division.
  - No instance argument is quantified freely. All `[Algebra …]` / `[IsScalarTower …]` data in T2 is consistent, and T1 has only the instances it needs.
- **Universes.** At `.{0}`, every quantified field, scheme and DVR is in `Type`. No statement depends on the universe.

## Detail: the T9 compatibility exponent (the only clause I could not settle at a glance)

Model: `A[N] ≅ (ℤ/N)²` with `e_N((a,b),(c,d)) = ζ_N^{ad−bc}`.
1. Silverman III.8.1(e) (number UNVERIFIED) gives `e_{mn}(P, T) = e_n(mP, T)` for `T ∈ A[n]`.
2. Take `T = mQ`. Then `e_n(mP, mQ) = e_{mn}(P, mQ) = e_{mn}(P, Q)^m`.

The Lean clause `e n (x^m) (y^m) = e (m*n) x y ^ m` (11878-11881) is therefore correct. A `^(m²)` form would have been wrong.

## Lean probes (optional sanity checks; append to a copy of Leaves.lean)

None of them tests a suspected defect. They confirm three parse and definition facts this review relies on.

```lean
section RvLeaves48AgentA
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Quaternion

-- P1: T27's quaternion notation is (a,b)_ℚ, i² = a, j² = b.
example (a b : ℚ) : ℍ[ℚ, a, b] = QuaternionAlgebra ℚ a 0 b := rfl

-- P2: T8's map parses as (fst ≫ f) * (snd ≫ g).
example {k : Type} [Field k] (A Z J : PkgI3.AbVar k) (f : PkgI3.AbVar.Hom A J)
    (g : PkgI3.AbVar.Hom Z J) :
    (fst A.X Z.X ≫ f.hom * snd A.X Z.X ≫ g.hom) = (fst A.X Z.X ≫ f.hom) * (snd A.X Z.X ≫ g.hom) :=
  rfl

-- P3: G_K is Aut(K̄/K), as used by galT / FaltingsTate.
example (K : Type) [Field K] :
    Field.absoluteGaloisGroup K = (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) := rfl

-- P4: T2's index is the length-based `Ideal.ramificationIdx` (look at the elaborated term).
#check @Ideal.ramificationIdx_def
#print PkgI2.AbhyankarDVR

end RvLeaves48AgentA
```

## Residual caveats (locators, not Lean)

- R6 at `m = 3`: SGA 7 IX 4.7 was not read. STANDARD that it says `n ≥ 3`.
- R7 (Serre–Tate 1968), R8 (SGA 7 IX 3.5/3.6, "Prop." vs "Thm" 3.6), R9 (Faltings 1983 Satz 3/4): originals not read (locators.md). Statement numbers are UNVERIFIED.
- T9: the locators for "`e^L_n(x,x)=1`" (Mumford §23) and for compatibility (§20) are UNVERIFIED. The content is STANDARD.
- T3 (BLR 1.2/8), T1 (Stacks 0BMB hypothesis list): recalled from memory, content STANDARD, numbering UNVERIFIED.
