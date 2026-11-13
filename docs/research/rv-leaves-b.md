# rv-leaves-b: adversarial review of the object layer and the leaves of I2, I3, I6 and the conductor cluster

## Verdict

**No leaf is WRONG, STRONGER THAN PUBLISHED or VACUOUS.** Of the 35 `def … : Prop` leaves
reviewed (11 in `scratch/pkg-I2/I2.lean`, 7 in `scratch/pkg-I3/I3.lean`, 16 in
`scratch/pkg-I6/I6.lean` counting the cochain variants, 2 in `scratch/glue-conductor/Breaks.lean`),
all are FAITHFUL as Lean statements. Most are a published theorem or a direct consequence of one.
A few rest on several published results or need a citation correction before the announcement
(below). The object layer agrees with the standard objects (§1–§2). I2's and I3's abelian varieties
are **the same object**: a compiled bridge is in `scratch/rv-leaves-b/Repairs.lean`.

Repairs to make before the announcement (citations, not Lean text):
1. **I3.Q `QMDichotomy`**: true, but it combines Mumford §19 Thm 1, Cor. 2, §21 (`[D:ℚ] ∣ 2g` in
   characteristic 0) and Silverman AEC III.9.4. No single locator exists (pkg-I3 §7 says the
   same). Either cite all of them or announce it as glue over those leaves. I first suspected that
   definite `B` needs Shimura's exclusion of type III; that was WRONG (retracted): for a simple
   `A`, `End⁰ A = B` follows from `[D:ℚ] ∣ 4`, and the conclusion allows that case. A narrower
   optional form with `0 < a` (the application has `(2, −3)`) compiles as `RvLeavesB.QMDichotomyIndef`.
2. **I3.M3 `PoincareReducibility`**: it is stated over any field `k` of characteristic 0.
   Mumford §19 Thm 1 is over `k̄`. Cite Milne, *Abelian varieties* (Cornell–Silverman 1986),
   Prop. 12.1 (UNVERIFIED), as pkg-I3 §2 already proposes. The same base-change remark covers
   I3.M0–M2 and I2-Tors/Char/Rank (Mumford over `k̄` implies them over `k`, because `Hom_k ⊆ Hom_k̄`,
   `ℤ_ℓ` is flat over `ℤ`, and `T_ℓ A = T_ℓ A_k̄`). They are consequences, not stronger.
3. **I6.2a–c over Mathlib's `continuousCohomology`**: mathematically this is the classical group.
   Mathlib defines it with homogeneous cochains in iterated `C(G, C(G, …))`, and for a profinite
   `G` with discrete `M` currying identifies these with `C(Gⁿ⁺¹, M)`. But Mathlib does not yet prove
   the comparison with inhomogeneous cochains: it is a TODO in the file header (VERIFIED). The
   cochain forms I6.2a′–c′ are literally Serre's definition. **Recommend announcing the primed
   forms.**
4. **glue-conductor's two leaves** are the local theorems (Serre CL III §6, IV §1) moved to a
   Galois number field. They need the facts that the different localizes and that the global
   `G_i = (P^{i+1}).inertia` equals the local `G_i` (by density of `𝓞_L` in `𝓞_{L_P}`; Serre CL
   III §4, I §7, UNVERIFIED). Both facts are standard, but cite them. I6.6/I6.7 state the same
   leaves locally and can replace them.

## 1. The object layer (VERIFIED by reading the definitions, the `ZMod` topology and the quaternion notation in Mathlib)

| Object | Definition | Agrees with the standard object? |
|---|---|---|
| abelian variety (I2 `IsAbelianVariety` on `Grp (Over (Spec K))`; I3 `AbVar`) | group object in `Over (Spec K)`, structure morphism `IsProper`, `Smooth`, `GeometricallyIntegral` | **Yes.** Commutativity is Mathlib's `isCommMonObj_of_isProper_of_geometricallyIntegral`. The two packages require exactly the same three conditions on the same data |
| abelian scheme (I2) | group object in `Over (Spec O)`, proper, smooth, `GeometricallyConnected` | Yes (Mumford GIT Def. 6.1) |
| good reduction (I2) | ∃ abelian scheme `𝒜/O` with `𝒜_K ≅ A` in `Grp (Over (Spec K))` | Yes (Serre–Tate §1) |
| points `A(L)` | `Spec L ⟶ A.X` over `Spec K`, group via `MonObj.Hom.group` | Yes |
| Galois action | `σ·P = Spec(σ) ≫ P` | Yes. It is a **left** action: `galHom (στ) = galHom σ ≫ galHom τ` (I3 `galHom_mul`, compiled), and the coordinates are transformed by `σ` |
| `G_K` | `Field.absoluteGaloisGroup K = Aut(K̄/K)`, `K̄ = AlgebraicClosure K` | Yes. In characteristic `p` it equals `Aut(K^sep/K)`, and `A[ℓⁿ](K̄) = A[ℓⁿ](K^sep)` for `ℓ ≠ p` |
| torsion | I2: `{x \| x^m = 1}`; I3: inside `T_ℓ` | Yes |
| `T_ℓ` (I3) | sequences `x₀ = 0`, `ℓ·x_{n+1} = x_n` in `A(K̄)`, so `x_n ∈ A[ℓⁿ]`; `ℤ_ℓ` acts through `ℤ/ℓⁿ` | Yes: `lim A[ℓⁿ](K̄)` with multiplication by `ℓ` as transition map |
| `V_ℓ`, `ρ_ℓ` (I3) | `ℚ_ℓ ⊗_{ℤ_ℓ} T_ℓ`; `Representation` of the abstract group `G_K` | Yes. **Continuity is not part of the definition.** None of the I3 leaves needs it: a `G_K`-stable subspace of a finite-dimensional `ℚ_ℓ`-space is automatically closed, so semisimplicity and equivariance mean the same thing abstractly. C10 (Chebotarev density together with Brauer–Nesbitt) needs continuous traces. That continuity is GLUE, provable: each `K̄`-point factors through a finite extension, so stabilizers are open |
| `Hom`, `End`, `End⁰` (I3) | morphisms with `IsMonHom`, as a subgroup of the commutative group `A.X ⟶ B.X`; `End⁰ = ℚ ⊗_ℤ End` | Yes. By rigidity, maps preserving the identity are the same as group homomorphisms |
| dimension | `topologicalKrullDim A.X.left` | Yes for a variety over a field |
| inertia (I2) | `σ ∈ w.decompositionSubgroup K` and `∈ w.inertiaSubgroup K` for a valuation ring `w ⊂ K̄` over `O` | Yes: the inertia group at `w` (Mathlib: `decompositionSubgroup` = stabilizer of `w`, `inertiaSubgroup` = kernel of the action on the residue field; VERIFIED, RingTheory/Valuation/RamificationGroup.lean:29,49). Here `w` has rank 1 and is nontrivial because `w ∩ K = O` is a DVR. `K` need not be complete; Serre–Tate allow any discretely valued `K` |
| lower `G_i` (I6) | `(𝔪_B^{i+1}).inertia (B ≃ₐ[A] B)` | Yes: Serre IV §1, `v_B(σx − x) ≥ i+1`. `B ≃ₐ[A] B = Gal(L/K)` because `B` is the integral closure |
| real lower numbering, `φ`, upper numbering (I6) | `G_u = G_{⌈u⌉}` (`G` for `u ≤ −1`); `φ(u) = ∫₀ᵘ \|G_t\|/\|G_0\|`; `G^v = G_{ψ(v)}` with `ψ(v) = sInf{u ≥ −1 \| v ≤ φ(u)}` | Yes (Serre IV §3). `φ(u) = u` on `[−1, 0]`; `ψ` is the inverse of `φ` because `φ` is a continuous increasing bijection when `G` is finite |
| Artin conductor (I6) | `∑ᶠ (\|G_i\|/\|G_0\|) codim V^{G_i}` | Yes (Serre VI §2) |
| `H²(G_ℚ, ℤ/2)` (I6) | Mathlib `continuousCohomology 2` of the trivial `TopRep ℤ` on `ZMod 2`; the topology on `ZMod 2` is `⊥`, i.e. discrete (VERIFIED, `Topology/Instances/ZMod.lean:24`) | Yes (repair 3 of the Verdict). The cochain variant: continuous `ε : G×G → ℤ/2` with the inhomogeneous cocycle and coboundary formulas for the trivial action. These are correct, and continuity is a genuine condition because the topology is discrete |
| localization maps (I6) | `ContinuousCohomology.map` along `Field.absoluteGaloisGroup.map (algebraMap ℚ F)` for `F = ℚ_p, ℝ` | Yes. The map depends on a choice of embedding of `K̄`, but conjugation acts trivially on cohomology, so the map on `H²` does not (and the leaves only use whether a class is zero) |
| quaternions | `ℍ[ℚ, a, b] = QuaternionAlgebra ℚ a 0 b`, `i² = a`, `j² = b` (VERIFIED, `Algebra/Quaternion.lean:83`) | Yes |

**Can a leaf be vacuous?** The leaves quantify over every abelian variety, every field and every
DVR. None of their hypotheses is unsatisfiable. They are not trivially true either: no definition
collapses (the continuity conditions are genuine, the action is not trivial, `T_ℓ` is the true
limit). One caveat, already noted by pkg-I3 (VERIFIED there): **Mathlib v4.35 can build no nonzero
abelian variety.** Applying the leaves to Glazer's `A`, `J₁(N)` and `A_f` needs those objects,
supplied by I1/I4 leaves or constructed. The real faithfulness risk sits there, not in these
packages.

## 2. Do I2's and I3's abelian varieties agree? Which should the shared layer use?

They agree. `RvLeavesB.ofGrp` (compiled) turns an I2 abelian variety into an I3 `AbVar` with the
same `X` and the same group structure. `RvLeavesB.homOfGrp` sends a morphism `A ⟶ B` in `Grp` to
I3's `Hom` with the same underlying morphism (`homOfGrp_hom : … = f.hom.hom := rfl`).

The packages differ in four ways, none of them mathematical:
- **Universes.** I2's leaves are polymorphic (`.{u}`); I3 and I6 use `Type`.
- **Points.** I2's points are over a `CommRing L`, I3's over a `Field L`.
- **Hom.** I3 has a ℤ-module `Hom` and an `End` ring. I2 uses the categorical `A ⟶ B` and writes
  products in `A.X ⟶ B.X`.
- **Base change.** I2 has `baseChange` via `Functor.mapGrp`; I3's `baseChange` is for `Type` only.

**Recommendation for the shared layer:**
- **Object:** I2's `Grp (Over (Spec K))` with `[IsAbelianVariety A]`. This is Mathlib's own
  category: base change is `mapGrp`, morphisms are `Grp` morphisms, and the Néron property and
  reduction are stated with it.
- **Derived constructions:** take I3's `homGroup`/`Hom`/`End`/`End0` and `Tate.T`/`V`/`galRep`
  through `ofGrp`.
- **Universe:** fix one for the announcement (`Type` suffices).
- **Points:** one definition of points and of `galAct`, which today is duplicated with identical
  text.

## 3. Verdict per leaf

Hypotheses checked for each leaf: residue characteristic and `ℓ ≠ p`, number field or local field,
finite or `ℓ`-adic level. All locators are UNVERIFIED (no network) unless the source report records
a read.

### pkg-I2 (`scratch/pkg-I2/I2.lean`)

| Leaf | Published source | Hypotheses checked | Verdict |
|---|---|---|---|
| I2-P `PurityBranchLocus` | Stacks 0BMB / SGA 1 X 3.4 | finite type over Noetherian `R`; `R_p` regular, `S_q` normal; quasi-finite at `q`; `dim S_q = dim R_p ≥ 1`; unramified at every height-1 `q' ⊆ q`, i.e. at codimension-1 specializations | FAITHFUL |
| I2-NOS `NeronOggShafarevich` | Serre–Tate 1968 Thm 1 | `K` any field with a DVR `O`; "m invertible in `O`" is "`p ∤ m`", and covers residue characteristic 0; (a)⇔(b)⇔(c) | FAITHFUL |
| I2-ST2 `SerreTatePotentialGood` | Serre–Tate Thm 2 / Cor. 2, plus NOS over `K'` | one prime `ℓ ≠ p`; `w ∩ K'` is a DVR for finite `K'/K`; inertia of `w` over `K'` is `I ∩ G_{K'}` | FAITHFUL (consequence) |
| I2-SS `GrothendieckMonodromy` | SGA 7 IX 3.6 + 3.5 (⇒) | `K'` independent of `ℓ`; all `ℓ ≠ p`; finite level | FAITHFUL (consequence) |
| I2-Ray `RaynaudCriterion` | SGA 7 IX 4.7 + 3.5 (⇒) | `m ≥ 3`, `p ∤ m`, `A[m]` rational over `K` | FAITHFUL (consequence) |
| I2-NMP `NeronMappingAbelianScheme` | BLR §1.2 Prop. 8 | all `O`-morphisms (not only homomorphisms); `𝒜` smooth, so the Néron property applies with `Y = 𝒜` | FAITHFUL |
| I2-Red `ReductionTorsionBijective` | Serre–Tate §1, Lemma 2 | `w ⊂ K̄` is a non-Noetherian valuation ring. The valuative criterion of properness still gives `x'`, `κ(w) = k̄`, and `w` is henselian. `p ∤ m` | FAITHFUL |
| I2-Tors `TorsionStructure` | Mumford §4 (over `k̄`; base change) | `n` invertible in `K`; `e` respects the group law | FAITHFUL |
| I2-AbDVR `AbhyankarDVR` | SGA 1 X 3.6 | `L/K` tame (`e(Q)` a unit, residue extension separable), `e(Q) ∣ n`, `n` a unit. `X^n − π` is Eisenstein, so `[K(t):K] = n` even if `t ∈ L`, and then `e = n` | FAITHFUL |
| I2-Char `CharpolyIndependentOfEll` | Mumford §19 Thm 4 (finite level) | `ℓ ≠ char k`. `M` is the matrix of `φ` on `B[ℓⁿ]`. Holds because `T_ℓ → B[ℓⁿ]` is onto | FAITHFUL (consequence) |
| I2-Rank `HomRankBound` | Mumford §19 Thm 3 | `4gg' + 1` homomorphisms are ℤ-dependent | FAITHFUL (consequence) |

### pkg-I3 (`scratch/pkg-I3/I3.lean`)

| Leaf | Published source | Hypotheses checked | Verdict |
|---|---|---|---|
| I3.F1 `FaltingsSemisimple` | Faltings 1983 Satz 3 | number field; every `ℓ`; continuity not needed | FAITHFUL |
| I3.F2 `FaltingsTate` | Faltings Satz 4, Kor. 1 | number field; `ℤ_ℓ ⊗ Hom → Hom_{G_K}(T_ℓ A, T_ℓ B)` is bijective; the "⊆" half is proved in the file | FAITHFUL |
| I3.M0 `TateModuleFree` | Mumford §4 / §18 | `ℓ ≠ char k`; rank `2 dim A` | FAITHFUL (consequence) |
| I3.M1 `HomFreeFinite` | Mumford §19 Thm 3; Milne 1986 §12 | rank `≤ 4 dim A dim B`; injectivity only for `ℓ ≠ char k` | FAITHFUL (base-change consequence) |
| I3.M2 `CharPolyIndepOfEll` | Mumford §19 Thm 4 | `ℓ ≠ char k`; any finite basis; degree not stated, so the leaf is weaker than published | FAITHFUL |
| I3.M3 `PoincareReducibility` | Milne 1986 Prop. 12.1, not Mumford §19 Thm 1 | characteristic 0, `k` arbitrary. `EndDivision` means "every nonzero endomorphism is finite and surjective", which is `k`-simplicity. `(f, g)` parses as `(fst ≫ f) * (snd ≫ g)` | FAITHFUL AFTER REPAIRS (citation) |
| I3.Q `QMDichotomy` | Mumford §19, §21 + Silverman III.9.4 (composite) | `k` algebraically closed of characteristic 0; `dim A = 2`; `B` a division algebra | FAITHFUL AFTER REPAIRS (citation; there is no single locator). Optional narrower Lean text: `QMDichotomyIndef` |

### pkg-I6 (`scratch/pkg-I6/I6.lean`)

| Leaf | Published source | Hypotheses checked | Verdict |
|---|---|---|---|
| I6.1 `SkolemNoether` | Reiner Thm 7.21 / Farb–Dennis 3.14 | `A` central simple and finite-dimensional, `B` simple and finite-dimensional. Not in Mathlib (VERIFIED by grep) | FAITHFUL |
| I6.2a `BrauerHasse2` | ABHN + Kummer (`Br[2] ≅ H²(μ₂)`, `μ₂ ≅ ℤ/2`) | all places including `∞` | FAITHFUL (cite the comparison, repair 3 of the Verdict) |
| I6.2b `BrauerReciprocity2` | `∑ inv_v = 0` | finitely many places; even number including `∞` | FAITHFUL (same) |
| I6.2c `LocalH2Card` | `Br ℚ_p[2] ≅ ℤ/2`, `Br ℝ ≅ ℤ/2` | applied to the restricted (still trivial) module | FAITHFUL (same) |
| I6.2a′–c′ (cochain forms) | the same theorems, with Serre's *Cohomologie galoisienne* definitions | discrete `ℤ/2`, continuous cochains | FAITHFUL (**recommended forms**) |
| I6.3 `LocalKroneckerWeber` | Neukirch V (1.10) | finite abelian `L ⊆ ℚ̄_p` | FAITHFUL |
| I6.4 `ChebotarevExists` | Neukirch VII (13.4) | `IsArithFrobAt ℤ σ Q` is the arithmetic Frobenius; `p ∉ S` and unramified | FAITHFUL (consequence) |
| I6.5 `BrauerNesbittChar0` | Lang, *Algebra* XVII Cor. 3.8 | characteristic 0; semisimple; finite-dimensional; any group (traces extend to `k[G]`) | FAITHFUL |
| I6.6 `DifferentBound` | Serre CL III §6, remark after Prop. 13 | complete DVR, perfect residue field, separable. If `e = 0` in `B`, the right side is `⊥` and the leaf is trivially true, which matches `v(e) = ∞` | FAITHFUL |
| I6.7 `HilbertDifferentFormula` | Serre CL IV §1 Prop. 4 | Galois; residue extension separable (perfect residue field) | FAITHFUL |
| I6.8 `HerbrandQuotient` | Serre CL IV §3 Prop. 14 | `r` is forced to be restriction (`C → B` is injective: torsion-free domain) | FAITHFUL |
| I6.9 `HerbrandTransitivity` | Serre CL IV §3 Prop. 15 | `C/A` Galois; `u ≥ −1` | FAITHFUL |
| I6.10 `LocalReciprocityUpper` | Serre CL XIII §4, XV §2 Thm 1 + Hasse–Arf V §7 | finite abelian; finite residue field. The ∃-form does not depend on the Frobenius normalization: replacing `θ` by `θ⁻¹` is a homomorphism on an abelian group and preserves every clause. For real `v`, `G^v = G^{⌈v⌉}` because the jumps are integers | FAITHFUL |

### glue-conductor (`scratch/glue-conductor/Breaks.lean`)

| Leaf | Published source | Verdict |
|---|---|---|
| `HilbertDifferentFormula` (global: Galois `L/ℚ`, `P ≠ ⊥`, exact power of `P` in `𝔇_{𝓞_L/ℤ}`) | Serre CL IV §1 Prop. 4, moved to `L` | FAITHFUL (cite localization, repair 4 of the Verdict) |
| `SerreDifferentBound` (any number field, `P ∣ p`, `v_P(𝔇) ≤ e − 1 + e·v_p(e)`) | Serre CL III §6, using `v_P(e) = e·v_p(e)` | FAITHFUL (same) |

## 4. Glue with `sorry` met in these files (not leaves; listed so integration does not count them proved)

- `PkgI2.goodReduction_of_QM_rational3` (A6, Lemma PR(ii)). Statement checked: `hJ` encodes
  `J² = −3`, `hIJ` encodes `IJ = −JI` (composition order `(x ≫ I) ≫ J = J(I x)`), and `(2, −3)` is
  ramified at 3. Status: outline only.
- `PkgI6.artinConductor_le_of_upper` (D4). Statement correct
  (`f(V) = codim V^{G_0} + ∫_0^∞ codim V^{G^v} dv ≤ dim V (1 + U)`). Status: unproved.
- `PkgI6.sq_principalUnits` (D3). Statement correct. Proved in `scratch/glue-conductor/Dyadic.lean`.
- Continuity of `ρ_ℓ` (I3 `galRep`): not defined, needed for C10. Provable glue.

## 5. Files

- `scratch/rv-leaves-b/Repairs.lean`: COMPILES (`lake env lean`, no errors, no warnings, no
  `sorry`; VERIFIED 2026-11-11). Contents: I3's definitions (verbatim), I2's `IsAbelianVariety`,
  the bridge `ofGrp`/`homOfGrp`/`homOfGrp_hom`, and the optional `QMDichotomyIndef`.
- `scratch/rv-leaves-b/log.md`: results log.
