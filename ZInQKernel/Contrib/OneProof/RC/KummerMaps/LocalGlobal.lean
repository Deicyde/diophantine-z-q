import ZInQKernel.Contrib.OneProof.RC.CoefModules.KummerAt

/-!
# Lane RC29 (Kummer maps), part 2: local and global torsion along the decomposition embedding

Manuscript `diophantine_zq.tex` (11/5), (4.3) at tex 3455–3463 (the Selmer cone compares
`RΓ(G_{K,S}, M_i)` with `⊕_v RΓ(K_v, M_i)`, i.e. `M_i` is restricted to the decomposition groups)
and Lemma `ex:arith-local-kummer` (tex 3413–3438: the local condition of `B = E^{(h)}` over
`F = K_v` is carried into `RΓ(K_v, M_i)`). The coefficient module `M_i` is built on
`E(K_S)[2^i]` with the global Galois action (lane RC28's `TorsS`), while the local Kummer
condition lives on `B(K̄_v)[2^i]` with the local Galois action (lane RC28's `TorsAlg`); comparing
them needs an embedding `K_S → K̄_v`, and the localization `G_{K_v} → G_{K,S}` of lane RC26
(`locMap`, Nekovář 5.1, p. 113: "for every `v ∈ S` an embedding `K^sep ↪ K_v^sep` is fixed") is
built from one particular embedding of algebraic closures (Mathlib's
`Field.absoluteGaloisGroup.map`, through `IsAlgClosed.lift`).

* `exists_decompEmbedding`: **the embedding used by `decompMap`**: a ring map
  `j : K̄ → K̄_v` extending `K → K_v → K̄_v` with `j ∘ decompMap(σ) = σ ∘ j` for all `σ ∈ G_{K_v}`
  (PROVED by unfolding Mathlib's definition); `decompEmb`: a choice of it, as a `K`-algebra map.
* `embS`: the induced `K_S → K̄_v`; `embS_locMap`: `j(p_v(σ) x) = σ(j x)` for `x ∈ K_S`, i.e. the
  decomposition group acts on `K_S` through `locMap` compatibly with the local action (PROVED).
* `compPt`, `compTors`: the point maps `E(K_S) → E(K̄_v)` and `E(K_S)[N] → E(K̄_v)[N]` along `j`
  (with `E(K̄_v)` the points of `W_v = W ×_K K_v` over `K̄_v`, lane RC28's `PtAlg`/`TorsAlg`);
  `compTors_smul`: **`G_{K_v}`-equivariance** `j(p_v(σ) P) = σ j(P)` (PROVED); `compTors_injective`;
  `compTors_bijective` under lane RC28's `FullTorsion K S W N` (`E[N] ⊂ E(K_S)`; GLUE
  Néron–Ogg–Shafarevich there); `compTorsEquiv`: the resulting isomorphism
  `E(K_S)[N] ≃+ E(K̄_v)[N]` (PROVED from `FullTorsion`).

Kinds: definitions and PROVED; the only hypothesis is RC28's `FullTorsion` (GLUE, kept explicit).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open NumberField IsDedekindDomain WeierstrassCurve ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.RankCounts (unramifiedOutside resAbs resAbs_apply_coe)

variable (K : Type) [Field K] [NumberField K]

/-! ### The embedding behind the decomposition map -/

/-- PROVED (Nekovář 5.1, p. 113, the fixed embedding `K^sep ↪ K_v^sep`). **The embedding behind
lane RC26's `decompMap`**: Mathlib's `Field.absoluteGaloisGroup.map (algebraMap K K_v)` is the
restriction along a ring map `j : K̄ → K̄_v` extending `K → K_v → K̄_v`, so that
`j (decompMap σ y) = σ (j y)` for `σ ∈ G_{K_v}`, `y ∈ K̄`. -/
theorem exists_decompEmbedding (v : HeightOneSpectrum (𝓞 K)) :
    ∃ g : AlgebraicClosure K →+* AlgebraicClosure (v.adicCompletion K),
      (∀ x : K, g (algebraMap K _ x) =
        algebraMap (v.adicCompletion K) _ (algebraMap K (v.adicCompletion K) x)) ∧
      ∀ (σ : Gloc K v) (y : AlgebraicClosure K),
        g ((decompMap K v σ).toAlgHom y) = σ.toAlgHom (g y) := by
  let i1 : Algebra K (v.adicCompletion K) := (algebraMap K (v.adicCompletion K)).toAlgebra
  let g : AlgebraicClosure K →ₐ[K] AlgebraicClosure (v.adicCompletion K) := IsAlgClosed.lift
  let i2 : Algebra (AlgebraicClosure K) (AlgebraicClosure (v.adicCompletion K)) := g.toAlgebra
  refine ⟨g.toRingHom, fun x => ?_, fun σ y => ?_⟩
  · exact g.commutes x
  · exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) (AlgebraicClosure K) y

/-- Definition (Nekovář 5.1, p. 113). **The fixed embedding `j : K̄ → K̄_v`** of the localization
`G_{K_v} → G_K` (a choice of the map of `exists_decompEmbedding`), as a `K`-algebra map. -/
def decompEmb (v : HeightOneSpectrum (𝓞 K)) :
    AlgebraicClosure K →ₐ[K] AlgebraicClosure (v.adicCompletion K) :=
  { (Classical.choose (exists_decompEmbedding K v)) with
    commutes' := fun x => (Classical.choose_spec (exists_decompEmbedding K v)).1 x }

/-- PROVED. **`j ∘ decompMap(σ) = σ ∘ j`** on `K̄`. -/
theorem decompEmb_decompMap (v : HeightOneSpectrum (𝓞 K)) (σ : Gloc K v)
    (y : AlgebraicClosure K) :
    decompEmb K v ((decompMap K v σ).toAlgHom y) = σ.toAlgHom (decompEmb K v y) :=
  (Classical.choose_spec (exists_decompEmbedding K v)).2 σ y

variable (S : Set (HeightOneSpectrum (𝓞 K)))

/-- Definition. **The embedding `K_S → K̄_v`**, `j` restricted to `K_S ⊂ K̄`. -/
def embS (v : HeightOneSpectrum (𝓞 K)) : KS K S →ₐ[K] AlgebraicClosure (v.adicCompletion K) :=
  (decompEmb K v).comp (inclS K S)

/-- PROVED. The localization `p_v : G_{K_v} → G_{K,S}` acts on `K_S ⊂ K̄` through `decompMap`. -/
theorem coe_locMap_apply (v : HeightOneSpectrum (𝓞 K)) (σ : Gloc K v) (x : KS K S) :
    ((galS K S (locMap K S v σ) x : KS K S) : AlgebraicClosure K) =
      (decompMap K v σ).toAlgHom (x : AlgebraicClosure K) :=
  resAbs_apply_coe K S (decompMap K v σ) x

/-- PROVED (tex 3455–3463: the restriction of `M_i` to the decomposition group). **`j(p_v(σ) x) =
σ(j x)`** for `x ∈ K_S`, `σ ∈ G_{K_v}`. -/
theorem embS_locMap (v : HeightOneSpectrum (𝓞 K)) (σ : Gloc K v) (x : KS K S) :
    embS K S v (galS K S (locMap K S v σ) x) = σ.toAlgHom (embS K S v x) := by
  change decompEmb K v ((galS K S (locMap K S v σ) x : KS K S) : AlgebraicClosure K) =
    σ.toAlgHom (decompEmb K v (x : AlgebraicClosure K))
  rw [coe_locMap_apply, decompEmb_decompMap]

/-- PROVED. `embS` is injective. -/
theorem embS_injective (v : HeightOneSpectrum (𝓞 K)) : Function.Injective (embS K S v) :=
  (embS K S v).toRingHom.injective

/-! ### Points and torsion -/

/-- PROVED. Two affine points with equal coordinates are equal (whatever the nonsingularity
proofs). -/
theorem some_eq_some {R : Type*} [CommRing R] {V : WeierstrassCurve.Affine R} {x y x' y' : R}
    (hx : x = x') (hy : y = y') (h : V.Nonsingular x y) (h' : V.Nonsingular x' y') :
    Affine.Point.some x y h = Affine.Point.some x' y' h' := by
  subst hx
  subst hy
  rfl

variable {K S}

/-- Definition (tex 3455–3463, 3413–3438). **The point map `E(K_S) → E(K̄_v)`** along `j`, with
`E(K̄_v)` the points of `W_v = W ×_K K_v` over `K̄_v` (lane RC28's `PtAlg`; the base change of
`W_v` to `K̄_v` is the base change of `W`, definitionally). -/
def compPt (W : WeierstrassCurve K) (v : HeightOneSpectrum (𝓞 K)) :
    (W.baseChange (KS K S)).toAffine.Point →+ PtAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K)) :=
  Affine.Point.map (W' := W) (embS K S v)

/-- PROVED. `compPt` on coordinates. -/
theorem compPt_some (W : WeierstrassCurve K) (v : HeightOneSpectrum (𝓞 K)) {x y : KS K S}
    (hxy : (W.baseChange (KS K S)).toAffine.Nonsingular x y) :
    compPt W v (.some x y hxy) =
      ptEquiv (v.adicCompletion K) (W.baseChange (v.adicCompletion K))
        (.some (embS K S v x) (embS K S v y)
          ((W.toAffine.baseChange_nonsingular (embS K S v).injective x y).mpr hxy)) :=
  rfl

/-- PROVED. `compPt` is injective. -/
theorem compPt_injective (W : WeierstrassCurve K) (v : HeightOneSpectrum (𝓞 K)) :
    Function.Injective (compPt (S := S) W v) :=
  Affine.Point.map_injective (embS K S v)

/-- PROVED (tex 3455–3463). **`G_{K_v}`-equivariance of the point map**: `j(p_v(σ) P) = σ j(P)`. -/
theorem compPt_smul (W : WeierstrassCurve K) (v : HeightOneSpectrum (𝓞 K)) (σ : Gloc K v)
    (P : (W.baseChange (KS K S)).toAffine.Point) :
    compPt W v (Affine.Point.map (galS K S (locMap K S v σ)).toAlgHom P) = σ • compPt W v P := by
  rcases P with _ | ⟨x, y, hxy⟩
  · rw [← Affine.Point.zero_def, map_zero, map_zero, smul_zero]
  · rw [Affine.Point.map_some, compPt_some, compPt_some, smul_ptEquiv]
    congr 1
    change _ = Affine.Point.some (σ.toAlgHom (embS K S v x)) (σ.toAlgHom (embS K S v y)) _
    exact some_eq_some (embS_locMap K S v σ x) (embS_locMap K S v σ y) _ _

variable (W : WeierstrassCurve K) (N : ℕ)

/-- Definition (tex 3455–3463, 3413–3438). **The torsion comparison `E(K_S)[N] → E(K̄_v)[N]`**
along `j` (lane RC28's `TorsS` and `TorsAlg`). -/
def compTors (v : HeightOneSpectrum (𝓞 K)) :
    TorsS K S W N →+ TorsAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K)) N where
  toFun P := ⟨compPt W v (P : (W.baseChange (KS K S)).toAffine.Point), by
    rw [AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.1 P.2,
      map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add (compPt W v) _ _)

/-- PROVED. `compTors` on underlying points. -/
theorem coe_compTors (v : HeightOneSpectrum (𝓞 K)) (P : TorsS K S W N) :
    (compTors W N v P : PtAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K))) =
      compPt W v (P : (W.baseChange (KS K S)).toAffine.Point) :=
  rfl

/-- PROVED. `compTors` is injective. -/
theorem compTors_injective (v : HeightOneSpectrum (𝓞 K)) :
    Function.Injective (compTors (S := S) W N v) := fun _ _ h =>
  Subtype.ext (compPt_injective W v (congrArg Subtype.val h))

/-- PROVED (tex 3455–3463). **The torsion comparison is `G_{K_v}`-equivariant**:
`j(p_v(σ) • P) = σ • j(P)` for `σ ∈ G_{K_v}` (lane RC28's actions on `TorsS` and `TorsAlg`). -/
theorem compTors_smul (v : HeightOneSpectrum (𝓞 K)) (σ : Gloc K v) (P : TorsS K S W N) :
    compTors W N v (locMap K S v σ • P) = σ • compTors W N v P := by
  apply Subtype.ext
  rw [coe_compTors, coe_smul_torsS, compPt_smul, coe_smul_torsAlg, coe_compTors]

/-- PROVED. `E(K̄_v)[N]` has `N²` points (`N ≠ 0`, characteristic zero; vendored Tau Ceti
`WeierstrassCurve.natCard_torsionBy`). -/
theorem natCard_torsAlg_adic [W.IsElliptic] [NeZero N] (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card (TorsAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K)) N) = N ^ 2 := by
  classical
  have hN : ((N : ℤ) : AlgebraicClosure (v.adicCompletion K)) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero.2 (NeZero.ne N) : ((N : ℕ) : AlgebraicClosure (v.adicCompletion K)) ≠ 0)
  have h := ((W.baseChange (v.adicCompletion K)).baseChange
    (AlgebraicClosure (v.adicCompletion K))).natCard_torsionBy (n := (N : ℤ)) hN
  rw [Int.natAbs_natCast] at h
  exact h

/-- PROVED from GLUE (`FullTorsion`, Néron–Ogg–Shafarevich). **Under `E[N] ⊂ E(K_S)` the torsion
comparison is bijective**: `E(K_S)[N] = E(K̄_v)[N]` along `j`. -/
theorem compTors_bijective [W.IsElliptic] [NeZero N] (hW : FullTorsion K S W N)
    (v : HeightOneSpectrum (𝓞 K)) : Function.Bijective (compTors (S := S) W N v) :=
  (compTors_injective W N v).bijective_of_nat_card_le (by rw [natCard_torsAlg_adic, hW])

/-- Definition (tex 3413–3438, 3455–3463). **The identification `E(K_S)[N] ≃+ E(K̄_v)[N]`**
along the fixed embedding `j`, under `FullTorsion`; `G_{K_v}`-equivariant by `compTors_smul`. -/
def compTorsEquiv [W.IsElliptic] [NeZero N] (hW : FullTorsion K S W N)
    (v : HeightOneSpectrum (𝓞 K)) :
    TorsS K S W N ≃+ TorsAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K)) N :=
  AddEquiv.ofBijective (compTors W N v) (compTors_bijective W N hW v)

/-- PROVED. `compTorsEquiv` is `compTors`. -/
theorem compTorsEquiv_apply [W.IsElliptic] [NeZero N] (hW : FullTorsion K S W N)
    (v : HeightOneSpectrum (𝓞 K)) (P : TorsS K S W N) :
    compTorsEquiv W N hW v P = compTors W N v P :=
  rfl

/-- PROVED (tex 3413–3438, 3455–3463). **The inverse identification is `G_{K_v}`-equivariant**:
`j⁻¹(σ • t) = p_v(σ) • j⁻¹(t)`. -/
theorem compTorsEquiv_symm_smul [W.IsElliptic] [NeZero N] (hW : FullTorsion K S W N)
    (v : HeightOneSpectrum (𝓞 K)) (σ : Gloc K v)
    (t : TorsAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K)) N) :
    (compTorsEquiv W N hW v).symm (σ • t) = locMap K S v σ • (compTorsEquiv W N hW v).symm t := by
  apply (compTorsEquiv W N hW v).injective
  rw [AddEquiv.apply_symm_apply, compTorsEquiv_apply, compTors_smul, ← compTorsEquiv_apply W N hW,
    AddEquiv.apply_symm_apply]

end ZInQ.Manuscript.RC.KummerMaps
