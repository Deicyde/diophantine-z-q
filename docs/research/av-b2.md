# av-b2: group B of leaf-fold3 — T9 and Serre's lemma become glue, `DivisiblePoints` reduced to char p

Task av-b2, 2026-11-13. Base: fork main 8ec80711 with origin/wip/leaf-fold3 (f7951690) merged. Lean:
`ZInQKernel/Contrib/AVB2/SerreLemma.lean` (new, Mathlib only) and `scratch/av-b2/` (part file
`olean/AVB2Main.lean`, compiled on leaf-fold3's olean chain; flat single-file check `AVB2Flat.lean` built by
`assemble.sh`). Results log: `scratch/av-b2/log.md`. No existing file of the project was edited.

Marks: **VERIFIED** = compiled, or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number recalled without a source (no network).

## 1. Main result

Four group-B fields are discharged or reduced. All four theorems compile on leaf-fold3's olean chain
(`import TailI`, so each Prop is leaf-fold3's own definition and not a copy). All four have no `sorry` and
only the three standard axioms (VERIFIED, §3).

```lean
-- scratch/av-b2/olean/AVB2Main.lean (namespace HDec)
theorem HDec.AVB2.t9_of_leaves3 (h9 : WeilPairing.T09_SymmIsogenyExists)
    (hQ : WeilPairing.IsogenyQuasiInverse) : LeafPush.T09_WeilPairing.{0}
theorem HDec.AVB2.serreRigidity3_of_T35 (hU : ZInQ.LeafPush2.UniformizationExists)
    (hC : HomUnify.HomLatticeCorr) : HeckeRest.SerreRigidity3
theorem HDec.AVB2.divisiblePoints_of_posChar (hP : MulIsogenyPosChar) : WeilPairing.DivisiblePoints
theorem HDec.AVB2.t11b_of_exists (h : T11bExists) : ZInQ.LeafPush2.T11b_Rigidity
theorem HDec.HSyn.sixContactMin_of_openB2 (r : OpenResearchLeaves2) (t : OpenTextbookLeavesB2)
    (l : OpenAddedLeavesB2) (g : OpenGlue3) : _root_.ZInQ.SixContactMin
```

`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all five.

What this does to the field list:
- **`t9` (T9) is glue.** It follows from two fields that are already in the list, `t09SymmIsogenyExists` and
  `isogenyQuasiInverse`. The proof is weil-pairing's `oldT9_of_symmIsogeny`. Lean accepts that proof at the
  field's own type, so weil-pairing's copy `OldT9.T09_WeilPairing` is definitionally `LeafPush.T09_WeilPairing.{0}`.
- **`serreRigidity3` (Serre's lemma at level 3) is glue.** It follows from T35 (`t35`) and `HomLatticeCorr`
  (`homLatticeCorr`), which are both fields already; only clause 1, `HomLinearLift`, is used. The proof also uses
  g9-abvarbc's proved `MulIsogeny` and Mathlib. This answers the t5-torsion question: one more group-B leaf
  falls to T35.
- **`divisiblePoints` is replaced by the smaller leaf `MulIsogenyPosChar`.** That leaf says `[n]` is finite and
  surjective in positive characteristic. Characteristic 0 is the proved `MulIsogeny`.
- **`t11b` (T11(b)) is replaced by its existence half `T11bExists`.** Uniqueness is proved
  (`baseChange_map_injective`).

`sixContactMin_of_openB2` is leaf-fold3's `sixContactMin_of_open3` with these substitutions made:
- `OpenTextbookLeavesB2`: `OpenTextbookLeaves3` without `t9`, and with `t11b` replaced by `t11bExists`.
- `OpenAddedLeavesB2`: `OpenAddedLeaves3` without `serreRigidity3`, and with `divisiblePoints` replaced by
  `mulIsogenyPosChar`.

**Count: 68 → 66 named Props** (26 research + 19 textbook + 15 added + 6 glue). Of these, 60 are leaves
(was 62), and two of those leaves are now smaller than before.

New file under `ZInQKernel/Contrib/AVB2/`, `SerreLemma.lean` (Mathlib only; `lake build
ZInQKernel.Contrib.AVB2.SerreLemma` succeeds):
```lean
theorem ZInQ.Contrib.AVB2.eq_one_of_pow_eq_one {R : Type*} [Ring R] (htf : ∀ r : R, 3 * r = 0 → r = 0)
    (hsep : ∀ r : R, (∀ k : ℕ, ∃ s, r = 3 ^ k * s) → r = 0)
    {x y : R} (hxy : x = 1 + 3 * y) {m : ℕ} (hm : 0 < m) (hxm : x ^ m = 1) : x = 1
theorem ZInQ.Contrib.AVB2.lattice_serre {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hΛ : IsZLattice ℝ Λ) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hMΛ : ∀ z ∈ Λ, M z ∈ Λ)
    (h3 : ∀ z ∈ Λ, (3⁻¹ : ℂ) • (M z - z) ∈ Λ) {m : ℕ} (hm : 0 < m)
    (hfin : ∀ z, (M ^ m) z - z ∈ Λ) : M = 1
```

### 1.1 The two new leaves (exact text, `scratch/av-b2/olean/AVB2Main.lean`)

```lean
/-- Leaf: Mumford, Abelian varieties, §4 Application 2 and §6; Milne (Cornell–Silverman 1986) Thm 8.2
(locators UNVERIFIED); degree dropped. -/
def MulIsogenyPosChar : Prop :=
  ∀ (k : Type) [Field k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 → ringChar k ≠ 0 →
    PkgI3.AbVar.IsIsogenyMor ((n : PkgI3.AbVar.End A).hom)

/-- Leaf: Conrad, Chow's K/k-image and K/k-trace, Enseign. Math. 52 (2006), §3; Milne 1986 §20
(locators UNVERIFIED). T11b_Rigidity without its uniqueness clause. -/
def T11bExists : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (L : Type) [Field L] [Algebra k L]
    (A B : PkgI3.AbVar k) (ψ : (A.baseChange L).X ⟶ (B.baseChange L).X), IsMonHom ψ →
    ∃ φ : A.X ⟶ B.X, IsMonHom φ ∧
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map φ = ψ
```

Both are STANDARD consequences of the cited theorems, and neither is stronger than them:
- `MulIsogenyPosChar` is `G0FibreSimple.MulIsogeny` (g9-abvarbc's leaf, proved in characteristic 0) with
  `CharZero` replaced by `ringChar k ≠ 0`.
- `T11bExists` is `T11b_Rigidity` with `∃!` weakened to `∃`.


## 2. Field by field

| field | outcome | how |
|---|---|---|
| `t9 : LeafPush.T09_WeilPairing.{0}` | **proved from fields already present** | `t9_of_leaves3` (VERIFIED) |
| `serreRigidity3 : HeckeRest.SerreRigidity3` | **proved from `t35` + `homLatticeCorr`** | `serreRigidity3_of_T35` (VERIFIED) |
| `divisiblePoints : WeilPairing.DivisiblePoints` | **reduced** to `MulIsogenyPosChar` | `divisiblePoints_of_posChar` (VERIFIED) |
| `t11b : ZInQ.LeafPush2.T11b_Rigidity` | **reduced** to `T11bExists` | `t11b_of_exists` (VERIFIED) |
| `t09SymmIsogenyExists` | leaf, confirmed | §2.4 |
| `isogenyQuasiInverse` | leaf, confirmed | §2.5 |
| `t10 : T10Etale.T10_TateDuality` | leaf, confirmed | §2.6 |
| `t4 : PkgI2.ReductionTorsionBijective.{0}` | leaf, confirmed | §2.7 |

### 2.1 `serreRigidity3`: the proof

`SerreRigidity3` states: for `A : AbVar ℚ̄` and `φ ∈ End(A)` with `φ^m = 1` (`m > 0`) and `x ≫ φ = x` for
every `x ∈ A(ℚ̄)` with `x³ = 1`, we have `φ = 1`. The proof (`scratch/av-b2/olean/AVB2Main.lean`):

1. Embed `σ : ℚ̄ → ℂ` (`IsAlgClosed.lift`) and take `g = dim A` (`PkgI3.AbVar.dim_finite`).
   - T35 gives a uniformization `Φ : ℂ^g → A(ℂ)_σ`, with kernel a discrete full lattice `Λ`.
   - `HomLatticeCorr`, clause 1, gives a `ℂ`-linear `M` with `Φ(Mz) = Φ(z) ≫ φ`.
2. Three properties of `M`:
   - `M Λ ⊆ Λ`.
   - `Φ(M^k z) = Φ(z) ≫ φ^k`, so `M^m z − z ∈ Λ` for all `z`.
   - `M ≡ 1 (mod 3Λ)`. For `z ∈ Λ`, the point `Φ(z/3)` is `3`-torsion in `A(ℂ)`. It comes from a `3`-torsion
     point of `A(ℚ̄)` (`cpt_torsion_descends`):
     - `[3]` is finite by the proved `MulIsogeny`.
     - The kernel fibre is a finite `ℚ̄`-scheme.
     - g9-abvarbc's `exists_lift_of_isFinite` applies with `Ω = ℚ̄`.

     `φ` fixes that point, so `Φ(M(z/3)) = Φ(z/3)`.
3. `lattice_serre` (Contrib/AVB2) gives `M = 1`. The steps:
   - `M^m = 1`, by discreteness.
   - `M|_Λ ∈ End_ℤ(Λ)` is `1 + 3y`. This ring has no `3`-torsion and is `3`-adically separated (discreteness again).
   - The ring form of Serre's lemma, `eq_one_of_pow_eq_one`, applies. Its proof reduces to prime order `p`, then
     shows `x = 1 + 3^k c ⇒ 3 ∣ c`: use the geometric sum, Bezout when `p ≠ 3`, and the explicit cube when `p = 3`.
   - Then `M = 1` on `Λ`, and `Λ` spans `ℂ^g` over `ℝ`.
4. Finish:
   - `φ` fixes `A(ℂ)_σ`, since `Φ` is onto.
   - So `φ` fixes `A(ℚ̄)`, because `Spec σ` is an epimorphism.
   - So `φ = 1`: `hom_ext_of_pts`, which is hom-unify's `hom_ext_of_cpts` with an algebraically closed `K` in place
     of `ℂ` (Mathlib's `ext_of_apply_eq`).

### 2.2 `divisiblePoints`

Proof of `exists_lift_pt`: let `z ∈ A(K̄)`.
- The fibre `P = pullback([n], z)` is finite and surjective over `Spec K̄`, by base change.
- So `P` is nonempty and compact, and it has a closed point (`IsClosed.exists_closed_singleton`).
- That closed point is a `K̄`-point (`pointOfClosedPoint`), which gives `w` with `w ≫ [n] = z`.
- `comp_natCast_hom` turns this into `n • w = z`.

The isogeny property of `[n]` comes from:
- the proved `MulIsogeny` in characteristic 0;
- `MulIsogenyPosChar` otherwise.

t5-torsion found that the only use of `divisiblePoints` on the main chain is at number fields, and that it can be
removed by rewiring `tatePairingZl_of_leaves` (t5-torsion §0 item 5). With that rewiring `MulIsogenyPosChar` is not
needed either. Not done here: it would edit copied text.

### 2.3 `t11b`

`baseChange_map_injective`: let `k` be algebraically closed. If two `k`-morphisms `φ, φ' : A → B` have equal
base changes along `k → L`, they agree on every `k`-point `p`:
- Lift `Spec L → Spec k → A` to `A_L`.
- `Over.pullback_map_left` and `pullback.lift_fst` give `Spec L ≫ p ≫ φ = Spec L ≫ p ≫ φ'`.
- `Spec L → Spec k` is an epimorphism.

So `φ = φ'` by `hom_ext_of_pts`. This holds in any characteristic and for any `L`. The existence half (descent of
homomorphisms) is the leaf `T11bExists`.

### 2.4 `t09SymmIsogenyExists` (leaf, not stronger than published)

The field is `∀ K A, Nonempty (SymmIsogeny A)`:
- `SymmIsogeny A`: a `WeilDual` `D` and an isogeny `λ : A → D.dual` with every `e^λ_n` alternating.
- `WeilDual`: a dual with perfect, Galois-equivariant, compatible pairings `e_n : A[n] × Â[n] → μ_n` for
  `n ∈ K^×`, and duals of endomorphisms.

The witness is `D = Pic⁰` with the Weil pairing, and `λ = φ_L` for an ample `L` over `K`. Sources (STANDARD,
section numbers UNVERIFIED):
- Mumford, *Abelian varieties*, §6 Application 1 (projectivity, `φ_L` an isogeny for ample `L`);
- §8 (`Â`);
- §20 (`e_n`: perfect, Galois-equivariant, `e_{mn}(x, y) = e_n(mx, y)` for `y ∈ Â[n]`, `e_n(x, f^∨y) = e_n(fx, y)`);
- §23 (`e^L_n(x, x) = 1`).

The compatibility field `compat` has the standard form (as `e_{mn}(P, Q) = e_n(mP, Q)` for elliptic curves). The
field is existential in `D`, so it is a consequence of these theorems.

Not provable here: Mathlib has no line bundles, so neither `Pic⁰` nor `φ_L` can be built.

### 2.5 `isogenyQuasiInverse` (leaf)

The field: for an isogeny `f : A → B` (finite and surjective) there are `d ≥ 1` and `g : B → A` with
`f g = [d]`, `g f = [d]`, required only on `K̄`-points.

Source: Mumford §7 (quotients by finite subgroup schemes; `ker f ⊆ A[deg f]`) and §8 (UNVERIFIED); Milne 1986,
Rem. 8.4 (UNVERIFIED). Take `d = deg f`. Stated on points only, it is a consequence and never stronger.

Not reducible here:
- It needs the quotient `A/ker f ≅ B` and the factorization of `[d]` through `f`.
- T35 would give it only over subfields of `ℂ`, and only analytically (an algebraic `g` would need GAGA,
  i.e. `HomLatticeCorr`'s realization clause, which is over `ℂ` only).

### 2.6 `t10` (leaf)

`T10Etale.T10_TateDuality` is stated over Mathlib's pro-étale `Scheme.EllAdicCohomology` (Bhatt–Scholze Def. 6.8.1;
`Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean:76`), with the `ℤ_ℓ`-module structure and Galois transport
built by t10-etale (VERIFIED, read). The statement is `H¹(A_K̄, ℤ_ℓ) ≅ Hom(T_ℓ A, ℤ_ℓ)`, Galois-equivariantly. Its
sources are Milne 1986 Thm 15.1(a) plus the pro-étale/étale comparison (Bhatt–Scholze §5.6; both UNVERIFIED, as in
the field's docstring).

Mathlib has no computation of étale or pro-étale cohomology of abelian varieties, so neither a proof nor a
reduction to smaller statements over existing definitions is possible here.

The Galois convention (`galH σ` is transport along `1 × Spec(σ⁻¹)`, compared with the contragredient
`f ↦ f ∘ σ⁻¹`) was not re-derived here (SPECULATIVE that it matches the intended left actions; t10-etale's report
discusses it).

### 2.7 `t4` (leaf)

`PkgI2.ReductionTorsionBijective` states: for a DVR `O ⊂ K`, a valuation ring `w` of `K̄` over `O`, an abelian
scheme `𝒜/O` with generic fibre `A`, and `m ∈ O^×`, reduction `A(K̄)[m] → 𝒜(κ(w))[m]` is bijective.

Source: Serre–Tate, *Good reduction of abelian varieties*, Ann. of Math. 88 (1968), §1 (proof of Thm 1;
UNVERIFIED locator). Standard proof:
- `𝒜[m]` is finite étale over `O`.
- `w` is henselian, with algebraically closed residue field.
- Points over `K̄` extend to `w` by properness.

`w` need not be discrete, but the valuative criterion holds for any valuation ring, so the statement is not
stronger than the published one. Not reducible to Mathlib (no étaleness of `[m]` for abelian schemes, no Hensel
lifting for schemes).


## 3. Checks

__CHECKS__
