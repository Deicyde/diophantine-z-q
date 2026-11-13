# inertia-homs: the inertia input of G4, corrected and proved from two leaves

## Main result

**g4-weilres's input `InertiaFixesHoms` is false as stated. A corrected form,
`InertiaFixesHomsMon`, is proved in Lean from two existing leaves.** G4 now rests on
`HomFreeFinite`, `MorphismsDescend` and `NeronOggShafarevich` (all leaves), plus the hypotheses
from other glue steps (`hK` from G2, `hgood` from G3, `hdim`).

- **File:** `scratch/inertia-homs/InertiaHoms.lean`, 2095 lines, no `sorry`, no `axiom`.
  - Lines 1-6 are G4.lean's imports and lines 7-28 a new module docstring.
  - Lines 29-1476 are `scratch/g4-weilres/G4.lean` lines 7-1454 verbatim (VERIFIED by `diff`).
  - The new part starts at `section NewConj`, line 1478.
- **Axioms.** Every printed theorem depends only on `propext`, `Classical.choice` and
  `Quot.sound`. VERIFIED by `#print axioms` at the end of the file.

Headlines:

- `G4WeilRes.inertiaFixesHomsMon_of_leaves :
  PkgI2.NeronOggShafarevich.{0} → PkgI3.HomFreeFinite → InertiaFixesHomsMon`.
  - NOS is Serre–Tate 1968, Thm 1 (locator UNVERIFIED).
  - `HomFreeFinite` is Mumford, *Abelian varieties*, §19 Thm 3 (locator UNVERIFIED).
- `G4WeilRes.conjAction_inertia'`: G4's inertia hypothesis `hinert`, derived from
  `InertiaFixesHomsMon`, `hK` and `hgood`. It has the same signature as g4-weilres's
  `conjAction_inertia`; only the type of `hI` changes.
- `G4WeilRes.homField_of_model_leaves'`: **G4 from `HomFreeFinite`, `MorphismsDescend` and
  `NeronOggShafarevich`**. The conclusion and the other hypotheses are as in
  `homField_of_model_leaves`.

## 1. Finding: `InertiaFixesHoms` is false as stated

This was VERIFIED by reading the definition (G4.lean L1318; L1340 of InertiaHoms.lean). The argument below is mathematical.
It cannot be refuted in Lean, because no nonzero `AbVar` can be constructed there.

**The flaw.** `InertiaFixesHoms` quantifies over every morphism
`φ : A ×_{K,e₁} ℚ̄ → B ×_{K,e₂} ℚ̄` in `Over (Spec ℚ̄)`, not only over homomorphisms.

**The counterexample.**

1. Take `K = ℚ`, `A = B = E` with `E : y² = x³ - x`, a prime `p ≠ 2` of good reduction, and a
   place `w | p`.
2. Take the point `b = (√p, y) ∈ E(ℚ̄)`.
3. `ℚ(√p)/ℚ` is ramified at `p`, so some `s ∈ I_w` moves `√p` (STANDARD). Hence `s·b ≠ b`.
4. The constant morphism `c_b` is a morphism over `ℚ̄`. Its conjugate is `c_{s^{±1}·b} ≠ c_b`.

**Why the error did not propagate.** The only consumer, `conjAction_inertia`, applies the input
to homomorphisms only.

**The corrected input** `InertiaFixesHomsMon` (L1925) makes two changes:

- It quantifies over homomorphisms `φ : AbVar.Hom (bcAlong A e₁) (bcAlong B e₂)` only, and the
  conclusion concerns `φ.hom`.
- It adds the hypotheses `p.Prime` and `LiesOver w p`. `conjAction_inertia` has both available.

Otherwise it is the same statement: the same objects, `PkgI2.HasGoodReduction` at
`w.comap e₁` and `w.comap e₂`, `s ∈ inertiaGQ w`, and the conclusion
`G4Conj.conj A.X B.X (specGal s) hf hg φ.hom = φ.hom`.

## 2. The proof (all compiled)

Fix `s ∈ I_w` with `w | p`, an auxiliary prime `ℓ ∈ {2, 3}` with `ℓ ≠ p`, and `ψ = conj_s φ`.

**1. Equivariance on test points** (`G4Conj.conj_agree`, generic category theory).
- Suppose a test point `Q : Z → X_f` and its image `Q ≫ φ` are both fixed by conjugation, for
  some lift `s'` of `s`.
- Then `Q ≫ ψ = Q ≫ φ`.
- The proof is pullback extensionality together with `conj_cmp`.

**2. Fixed sections** (`G4Conj.cmp_fixed_of_fst`). A section `Q` of `X_f` is fixed iff its
`X`-component `Q ≫ fst` is fixed by `s`.

**3. Torsion transfers to `K`-points** (`G4Conj.secFst`, `secFstHom`, `secFst_pow`).
- `Q ↦ Q ≫ fst` is a monoid homomorphism from the sections of `(Over.pullback f).obj X` to the
  points `Over.mk f ⟶ X`.
- It is built from `mul_left_fst` and `one_left_fst` of g4-weilres.

**4. NOS on the conjugate** (`G4WeilRes.point_fixed`). Suppose `q : Spec ℚ̄ → A` lies over
`Spec e` and `q^m = 1`, with `m` a unit at `w`. Then `Spec s ≫ q = q`. The proof:
1. `ℚ̄` is an algebraic closure of `K` through `e`. This gives a ring isomorphism `ι : K̄ ≃ ℚ̄`
   extending `e` (`InertiaHoms.exists_closure_equiv`, via `IsAlgClosure.equivOfEquiv`).
2. Set `σ = ι⁻¹ s ι ∈ Aut_K(K̄)` and `w' = w.comap ι`. Then `w'` lies over `w ∩ e(K)`.
3. `PkgI2.IsInertia w' σ` holds. Two lemmas give it:
   - `InertiaHoms.isInertia_iff`: Mathlib's decomposition and inertia subgroups, rewritten
     elementwise by membership only;
   - `InertiaHoms.inertia_transport`: the elementwise conditions transport along `ι`.
4. `x = Spec(ι⁻¹) ≫ q` is an `m`-torsion point of `A(K̄)`.
5. NOS (a)⇒(b) gives `galHom σ ≫ x = x`. Transport back to `Spec s ≫ q = q`.

**5. Side conditions** (proved).
- `InertiaHoms.isUnit_prime_of_liesOver`: `ℓ ≠ p` is a unit of `w ∩ F`.
- `InertiaHoms.comap_isDVR`: `w ∩ F` is a DVR for every number field `F` and every `w | p`.
  1. `𝓞_F ⊆ w ∩ F`.
  2. `P = 𝔪 ∩ 𝓞_F` is a nonzero prime, since `p ∈ P`.
  3. Mathlib's `HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer` shows that the `P`-adic
     valuation subring, a DVR, lies in `w ∩ F`.
  4. `ValuationSubring.eq_of_le_of_ne_top` (Krull dimension 1) gives equality.

**6. Assembly** (`G4WeilRes.inertiaFixesHomsMon`).
1. A point `P` of `A₁ = bcAlong A e₁` with values in `AlgebraicClosure ℚ̄` factors as
   `ptIso.hom ≫ Q`, with `Q` a section over `Spec ℚ̄`, because `ℚ̄ → AlgebraicClosure ℚ̄` is
   bijective.
2. If `P` is `ℓⁿ`-torsion, so are `Q` and `Q ≫ φ`. Steps 2-4, applied to `A` at `e₁` and to `B`
   at `e₂`, make both fixed.
3. Step 1 then gives `P ≫ ψ = P ≫ φ`. So `T_ℓ(ψ) = T_ℓ(φ)`.
4. `tateHom_injective` (from `HomFreeFinite`, g4-weilres) gives `ψ = φ`.

## 3. Compile

```
lake build ZInQKernel.HDecomp.B3Unram.B3b ZInQKernel.HDecomp.Repo.TorsionFree \
  ZInQKernel.HDecomp.Repo.Numerics ZInQKernel.HDecomp.Descent.B3Assembly ZInQKernel.HDecomp.Objects
lake env lean scratch/inertia-homs/InertiaHoms.lean
```

The file checks in about 40 s, with 0 errors (VERIFIED, 2026-11-13). The remaining warnings are
linter or deprecation warnings inherited from G4.lean.

## 4. What remains

- **G4's remaining non-leaf hypotheses** are unchanged and outside this task:
  - `hdim`: the dimension of a base change, missing from Mathlib;
  - `hK`: G2's output;
  - `hgood`: G3's output.
- **`InertiaFixesHomsMon` is glue, not a leaf.** It is now a theorem from the leaves NOS and
  `HomFreeFinite`.
- **For the integrator**, the h-decomposition row G4 should read:

  > G4: proved from `HomFreeFinite`, `MorphismsDescend`, `NeronOggShafarevich`, with `hK` (G2),
  > `hgood` (G3), `hdim` (`G4WeilRes.homField_of_model_leaves'`, inertia-homs).
  >
  > g4-weilres's `InertiaFixesHoms` was false (it covered all morphisms). It is replaced by
  > `InertiaFixesHomsMon`, proved by `inertiaFixesHomsMon_of_leaves`.

## 5. Labels

- **VERIFIED (compiled, standard axioms):** every declaration listed in §2 and the three
  headlines.
- **VERIFIED (read):** the definitions of `InertiaFixesHoms`, `PkgI2.NeronOggShafarevich`,
  `PkgI2.IsInertia`, `PkgI2.HasGoodReduction`, `PkgI3.HomFreeFinite`, `PkgI3.AbVar.T` and
  `inertiaGQ`.
- **STANDARD:** the counterexample of §1. It uses only that `ℚ(√p)` is ramified at `p` and that
  `I_w` surjects onto the inertia group of a finite subextension.
- **UNVERIFIED locators:** Serre–Tate 1968 Thm 1; Mumford §19 Thm 3.
