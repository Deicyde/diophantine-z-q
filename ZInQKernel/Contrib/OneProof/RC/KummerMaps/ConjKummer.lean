import ZInQKernel.Contrib.OneProof.RC.KummerMaps.KummerImage
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.ConjTransport

/-!
# Lane RC29, round 2, item (3a): Kummer conditions under the conjugate transport

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality` (tex 2761–2830), tex
2810–2813:

> At a split place `v`, the dual local condition is transported from the conjugate place `τv`. At a
> fixed place it is transported by the actual local representative of conjugation. Kummer
> conditions at `2N` are preserved by this transport.

Setting: lane RC28's `C : ActualConj K S` with `W.map κ = W` (`hW`) and `κ h = h` (`hκh`), a place
`v` and `w = τv` (`hvw`), and the cochain transport `conjTransport` of `ConjTransport.lean` for any
inner element `g` with `p_w(φ_v σ) = g c(p_v σ) g⁻¹` (`hg`). `Ē = locConjBar : K̄_v ≃ K̄_w`.

* **Points** (`conjKPt`, `conjKTors`, `conjKBase`): `Ē` and `e = locConjCompletion` carry the
  points of `B_v` to those of `B_w` when `B_v.map e = B_w`, compatibly with the Galois actions
  along `φ_v` (`conjKTors_smul`) and with the chosen division points (`conjKPt_basePt`).
* **Kummer cocycles go to Kummer cocycles up to coboundaries** (`conjK_kummerCocycle_sub_mem`):
  `T(κ_{ι_w}(e_* P)) − κ_{ι^τ}(P)` is the coboundary of a constant, for the transported coefficient
  map `ι^τ = g⁻¹ · ι_w ∘ Ē_*` (`conjKIotaAt`, equivariant by `conjKIotaAt_smul`).
* **The cleanest correct statement** is an isomorphism of local conditions, not an equality (the
  transported condition is a subcomplex of the `G_{K_w}`-cochains, the Kummer condition at `v` one
  of the `G_{K_v}`-cochains; `ConjKCondIso`, with `range_eq`, `range_homology`, `isInjective`,
  `trans`, `coef`, and non-vacuity `ConjKCondIso.refl`):
  `conjKTransportKummerIso : ConjKCondIso (conjTransport C g hvw hg (kummerAt w B_w m ι_w _))
  (kummerAt v B_v m ι^τ _)` for any equivariant `ι_w`; the actual case `conjKActualIso` at
  `B_v = localTwist W h v` (`conjK_localTwist_map`) and `ι_{τv} = kummerIota … τv`, with the
  canonical inner element at the conjugate place `conjKActualConjPlaceIso`.
* **`H¹` images**: `conjKActual_range_H1` (the `A_i`-span of the Kummer image of `B_v(K_v)`
  through `ι^τ`) and `conjKActual_range_H1_transport` (the span of the transport of lane RC29's
  local Kummer image at `τv`, `actualKummerAt_range_eq_span`).
* **`ι^τ` against `ι_v`** (`conjKActualIota_eq`): for the comparison element `h̄` of lane RC29's
  decomposition embeddings `decompEmb` at `v`, `τv` (`conjK_exists_comp_of`; note that `decompEmb`
  is a choice, not lane RC26's `decompLift`, so the comparison element is constructed for it,
  `conjK_decompMap_of`), the inner element `g = c(h̄)⁻¹` satisfies `hg` and
  `ι^τ(t) = α(h̄)⁻¹ · ε · ρ_T(τ)(ι_v(t))` with `ε = ±1`. **The square-root sign**:
  `Ē(j_v(s)) = ± j_{τv}(s)` (`conjK_localSqrt_sign`), the sign of `τ(h̄⁻¹ s) = ±s`, which the
  data do not determine; `φ_{−q} = −φ_q` (`conjK_twistPt_neg`) turns it into the unit `ε`. Read in `M_i(α⁻¹)` through
  lane RC28's `conjToInv`, `ι^τ` is `ι_v` up to the unit `α(h̄)⁻¹ε`.
* **The dual version on `M_i^*(1)`** (`conjKActualDualIso`): the dual condition `conjTransportDual`
  of the actual Kummer condition at `τv` is isomorphic to the Kummer condition of `B_v` with
  coefficients in `M_i^*(1)` through `conjDualEquiv ∘ ι^τ` (`conjKActualDualIota`); its `H¹` image
  is the span of that Kummer image (`conjKActualDual_range_H1`), and the coefficient map is the
  Weil pairing against `ι_v` up to the unit (`conjKActualDualIota_eq`).

Kinds: DEF and PROVED; no PRINT. Hypotheses: `hW` (lane RC28's DEPARTURE 3), `hκh` (ELLIOT: the
twist datum `h` is defined over the fixed field, as `hW`; non-vacuous `conjK_hκh_nonvacuous`),
`hFull` (GLUE, lane RC28), `hαw` (lane RC29's local triviality of the moving character at `τv`),
`hαc` (ELLIOT tex 2786–2795, PROVED by RC28 for the actual `α_i`), `hvw` (DEF), `hg` (PROVED
satisfiable: `conjTransportElt_spec`, `conjK_locMap_of_decompMap`). The structure `ConjKCondIso`
is non-vacuous (`ConjKCondIso.refl`).

DEPARTURES (form): the statement is an isomorphism of local conditions (see above); the explicit
comparison `conjKActualIota_eq` is for the inner element adapted to `decompEmb` (for another `g`
with `hg` the two coefficient maps differ by an element centralizing `c(p_v(G_{K_v}))`); DEPARTURE
D4 of `ConjTransport.lean` (orthogonality `U^⊥` not proved) applies to the dual version.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open CategoryTheory NumberField IsDedekindDomain WeierstrassCurve TensorProduct
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Contrib.CloudB3RC53.RankCounts (resAbs resAbs_apply_coe resAbs_surjective)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (GCx GHom)
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (ghomComp idGHom zeroGHom GHom.toCC GHom.toCC_f_apply
  GHom.toCC_comp)

section Points

variable {F F' : Type} [Field F] [Field F'] (e : F ≃+* F')
  (Ē : AlgebraicClosure F ≃+* AlgebraicClosure F')
  (hĒ : ∀ a : F, Ē (algebraMap F (AlgebraicClosure F) a) =
    algebraMap F' (AlgebraicClosure F') (e a))
  (B : WeierstrassCurve F) (B' : WeierstrassCurve F') (hB : B.map (e : F →+* F') = B')

include hĒ hB in
/-- PROVED. Along `e : F ≃+* F'` and `Ē : F̄ ≃+* F̄'` extending it (`hĒ`), `B.map e = B'` gives
`(B_{F̄}).map Ē = B'_{F̄'}`. -/
theorem conjK_map_baseChange :
    (B.baseChange (AlgebraicClosure F)).map (Ē : AlgebraicClosure F →+* AlgebraicClosure F') =
      B'.baseChange (AlgebraicClosure F') := by
  rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_map, ← hB, WeierstrassCurve.baseChange,
    WeierstrassCurve.map_map]
  congr 1
  exact RingHom.ext hĒ

include hĒ hB in
/-- PROVED. `Ē` preserves nonsingular points: `(x, y)` on `B_{F̄}` gives `(Ē x, Ē y)` on `B'_{F̄'}`.
-/
theorem conjK_nonsingular {x y : AlgebraicClosure F}
    (h : (B.baseChange (AlgebraicClosure F)).toAffine.Nonsingular x y) :
    (B'.baseChange (AlgebraicClosure F')).toAffine.Nonsingular (Ē x) (Ē y) :=
  conjK_map_baseChange e Ē hĒ B B' hB ▸
    (Affine.map_nonsingular (B.baseChange (AlgebraicClosure F)).toAffine
      (Ē : AlgebraicClosure F →+* AlgebraicClosure F').injective x y).mpr h

open scoped Classical in
/-- DEF. **The point map along the local conjugation**, `B(F̄) → B'(F̄')`, `(x, y) ↦ (Ē x, Ē y)`
(Tau Ceti `mapAlong` composed with the curve identification of `conjK_map_baseChange`). -/
def conjKPt : PtAlg F B →+ PtAlg F' B' :=
  (ptEquiv F' B').toAddMonoidHom.comp <|
    (AddEquiv.cast (M := fun V : WeierstrassCurve (AlgebraicClosure F') => V.toAffine.Point)
      (conjK_map_baseChange e Ē hĒ B B' hB)).toAddMonoidHom.comp <|
    (AddMonoidHom.mk' (Affine.Point.mapAlong (Ē : AlgebraicClosure F →+* AlgebraicClosure F')
      (Ē : AlgebraicClosure F →+* AlgebraicClosure F').injective)
      (Affine.Point.mapAlong_add _ _)).comp (ptEquiv F B).symm.toAddMonoidHom

open scoped Classical in
/-- PROVED. `conjKPt (x, y) = (Ē x, Ē y)`. -/
theorem conjKPt_some {x y : AlgebraicClosure F}
    (h : (B.baseChange (AlgebraicClosure F)).toAffine.Nonsingular x y) :
    conjKPt e Ē hĒ B B' hB (ptEquiv F B (.some x y h)) =
      ptEquiv F' B' (.some (Ē x) (Ē y) (conjK_nonsingular e Ē hĒ B B' hB h)) := by
  change ptEquiv F' B' ((AddEquiv.cast (M := fun V : WeierstrassCurve (AlgebraicClosure F') =>
      V.toAffine.Point) (conjK_map_baseChange e Ē hĒ B B' hB))
      (Affine.Point.mapAlong (Ē : AlgebraicClosure F →+* AlgebraicClosure F')
        (Ē : AlgebraicClosure F →+* AlgebraicClosure F').injective (.some x y h))) = _
  rw [Affine.Point.mapAlong_some, AddEquiv.cast_apply,
    Affine.Point.cast_some (conjK_map_baseChange e Ē hĒ B B' hB)]
  rfl

open scoped Classical in
/-- PROVED. `conjKPt 0 = 0`. -/
theorem conjKPt_zero : conjKPt e Ē hĒ B B' hB 0 = 0 := map_zero _

open scoped Classical in
/-- PROVED. `conjKPt` is bijective (`Ē` is a ring isomorphism). -/
theorem conjKPt_bijective : Function.Bijective (conjKPt e Ē hĒ B B' hB) := by
  have h1 : Function.Bijective (Affine.Point.mapAlong (W := B.baseChange (AlgebraicClosure F))
      (Ē : AlgebraicClosure F →+* AlgebraicClosure F')
      (Ē : AlgebraicClosure F →+* AlgebraicClosure F').injective) :=
    ⟨Affine.Point.mapAlong_injective _ _,
      Affine.Point.mapAlong_surjective _ _
        (Ē : AlgebraicClosure F →+* AlgebraicClosure F').surjective⟩
  exact (ptEquiv F' B').bijective.comp ((AddEquiv.cast (M := fun V : WeierstrassCurve
    (AlgebraicClosure F') => V.toAffine.Point) (conjK_map_baseChange e Ē hĒ B B' hB)).bijective.comp
    (h1.comp (ptEquiv F B).symm.bijective))

open scoped Classical in
/-- PROVED. **`conjKPt` intertwines the Galois actions**: `conjKPt (σ Q) = σ' (conjKPt Q)` when `σ'
= Ē σ Ē⁻¹` (hypothesis `hσ`; for the local conjugation `σ' = φ_v σ`, `locConjGal_apply`). -/
theorem conjKPt_smul (σ : Field.absoluteGaloisGroup F) (σ' : Field.absoluteGaloisGroup F')
    (hσ : ∀ y, σ'.toAlgHom y = Ē (σ.toAlgHom (Ē.symm y))) (P : PtAlg F B) :
    conjKPt e Ē hĒ B B' hB (σ • P) = σ' • conjKPt e Ē hĒ B B' hB P := by
  obtain ⟨P, rfl⟩ := (ptEquiv F B).surjective P
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Affine.Point.zero_def, map_zero, smul_zero, map_zero, smul_zero]
  · rw [smul_ptEquiv, Affine.Point.map_some, conjKPt_some, conjKPt_some, smul_ptEquiv,
      Affine.Point.map_some]
    congr 1
    refine some_eq_some ?_ ?_ _ _
    · rw [hσ, RingEquiv.symm_apply_apply]
    · rw [hσ, RingEquiv.symm_apply_apply]

open scoped Classical in
/-- DEF. **`Ē_*` on `m`-torsion**, `B(F̄)[m] → B'(F̄')[m]` (the restriction of `conjKPt`). -/
def conjKTors (m : ℕ) : TorsAlg F B m →+ TorsAlg F' B' m where
  toFun t := ⟨conjKPt e Ē hĒ B B' hB (t : PtAlg F B), by
    rw [AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.1 t.2,
      map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' s t := Subtype.ext (map_add (conjKPt e Ē hĒ B B' hB) (s : PtAlg F B) t)

open scoped Classical in
/-- PROVED. `conjKTors` on underlying points is `conjKPt`. -/
theorem coe_conjKTors (m : ℕ) (t : TorsAlg F B m) :
    (conjKTors e Ē hĒ B B' hB m t : PtAlg F' B') = conjKPt e Ē hĒ B B' hB (t : PtAlg F B) :=
  rfl

open scoped Classical in
/-- PROVED. `conjKTors (σ t) = σ' (conjKTors t)` for `σ' = Ē σ Ē⁻¹` (hypothesis `hσ`). -/
theorem conjKTors_smul (m : ℕ) (σ : Field.absoluteGaloisGroup F)
    (σ' : Field.absoluteGaloisGroup F') (hσ : ∀ y, σ'.toAlgHom y = Ē (σ.toAlgHom (Ē.symm y)))
    (t : TorsAlg F B m) :
    conjKTors e Ē hĒ B B' hB m (σ • t) = σ' • conjKTors e Ē hĒ B B' hB m t :=
  Subtype.ext (conjKPt_smul e Ē hĒ B B' hB σ σ' hσ (t : PtAlg F B))

include hB in
/-- PROVED. `e` preserves nonsingular points of `B` over the base fields. -/
theorem conjK_base_nonsingular {x y : F} (h : B.toAffine.Nonsingular x y) :
    B'.toAffine.Nonsingular (e x) (e y) :=
  hB ▸ (Affine.map_nonsingular B.toAffine (e : F →+* F').injective x y).mpr h

variable [DecidableEq F] [DecidableEq F']

/-- DEF. **The point map on rational points**, `B(F) → B'(F')`, `(x, y) ↦ (e x, e y)`. -/
def conjKBase : B.toAffine.Point →+ B'.toAffine.Point :=
  (AddEquiv.cast (M := fun V : WeierstrassCurve F' => V.toAffine.Point) hB).toAddMonoidHom.comp
    (AddMonoidHom.mk' (Affine.Point.mapAlong (e : F →+* F') (e : F →+* F').injective)
      (Affine.Point.mapAlong_add _ _))

/-- PROVED. `conjKBase (x, y) = (e x, e y)`. -/
theorem conjKBase_some {x y : F} (h : B.toAffine.Nonsingular x y) :
    conjKBase e B B' hB (.some x y h) = .some (e x) (e y) (conjK_base_nonsingular e B B' hB h) := by
  change (AddEquiv.cast (M := fun V : WeierstrassCurve F' => V.toAffine.Point) hB)
      (Affine.Point.mapAlong (e : F →+* F') (e : F →+* F').injective (.some x y h)) = _
  rw [Affine.Point.mapAlong_some, AddEquiv.cast_apply, Affine.Point.cast_some hB]
  rfl

/-- PROVED. `conjKBase` is surjective (`e` is an isomorphism). -/
theorem conjKBase_surjective : Function.Surjective (conjKBase e B B' hB) := by
  have h1 : Function.Surjective (Affine.Point.mapAlong (W := B) (e : F →+* F')
      (e : F →+* F').injective) :=
    Affine.Point.mapAlong_surjective _ _ (e : F →+* F').surjective
  exact (AddEquiv.cast (M := fun V : WeierstrassCurve F' => V.toAffine.Point) hB).surjective.comp h1

open scoped Classical in
/-- PROVED. **The two point maps are compatible**: `Ē_*` of the image of a rational point `P` in
`B(F̄)` is the image of `e_* P`. -/
theorem conjKPt_basePt (P : B.toAffine.Point) :
    conjKPt e Ē hĒ B B' hB (basePt F B P) = basePt F' B' (conjKBase e B B' hB P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Affine.Point.zero_def, map_zero, map_zero, map_zero, map_zero]
  · have hns : (B.baseChange (AlgebraicClosure F)).toAffine.Nonsingular
        (algebraMap F (AlgebraicClosure F) x) (algebraMap F (AlgebraicClosure F) y) :=
      (B.toAffine.baseChange_nonsingular (Algebra.ofId F (AlgebraicClosure F)).injective x y).2 h
    calc conjKPt e Ē hĒ B B' hB (basePt F B (.some x y h))
        = conjKPt e Ē hĒ B B' hB (ptEquiv F B (.some _ _ hns)) := by rw [basePt_some]
      _ = ptEquiv F' B' (.some _ _ (conjK_nonsingular e Ē hĒ B B' hB hns)) :=
          conjKPt_some e Ē hĒ B B' hB hns
      _ = basePt F' B' (conjKBase e B B' hB (.some x y h)) := by
          rw [conjKBase_some, basePt_some]
          congr 1
          exact some_eq_some (hĒ x) (hĒ y) _ _

end Points

/-! ### Cochain isomorphisms and cocycle conditions -/

section CocycleIso

variable {k : Type} [CommRing k] {G G' : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  {N N' : Type} [AddCommGroup N] [Module k N] [DistribMulAction G N] [SMulCommClass G k N]
  [TopologicalSpace N] [ContinuousAdd N] [ContinuousConstSMul k N] [ContinuousSMul G N]
  [AddCommGroup N'] [Module k N'] [DistribMulAction G' N'] [SMulCommClass G' k N']
  [TopologicalSpace N'] [ContinuousAdd N'] [ContinuousConstSMul k N'] [ContinuousSMul G' N']
  (T : contCochains k G' N' ≅ contCochains k G N)

/-- The degree-one component of a cochain isomorphism, as a map of continuous `1`-cochains. -/
abbrev conjKOne : contCochain k G' N' 1 →ₗ[k] contCochain k G N 1 :=
  (T.hom.f 1).hom

/-- PROVED. A cochain isomorphism commutes with `d⁰`. -/
theorem conjK_comm_d0 (c : contCochain k G' N' 0) :
    conjKOne T (contD k G' N' 0 c) = contD k G N 0 ((T.hom.f 0).hom c) := by
  have h := congrArg (fun φ => φ.hom c) (T.hom.comm 0 1)
  simp only [ModuleCat.hom_comp] at h
  exact h.symm

/-- PROVED. **A cochain isomorphism maps coboundaries `B¹` to coboundaries.** -/
theorem conjK_map_contB1 {x : contCochain k G' N' 1} (hx : x ∈ contB1 k G' N') :
    conjKOne T x ∈ contB1 k G N := by
  obtain ⟨c, rfl⟩ := hx
  exact ⟨(T.hom.f 0).hom c, (conjK_comm_d0 T c).symm⟩

/-- PROVED. `T⁻¹ (T x) = x` degreewise. -/
theorem conjK_inv_hom_apply (n : ℕ) (x : (contCochains k G' N').X n) :
    (T.inv.f n).hom ((T.hom.f n).hom x) = x := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← HomologicalComplex.comp_f, T.hom_inv_id]
  rfl

/-- PROVED. `T⁻¹ (T x) = x` on `1`-cochains. -/
theorem conjKOne_symm_apply (x : contCochain k G' N' 1) : conjKOne T.symm (conjKOne T x) = x :=
  conjK_inv_hom_apply T 1 x

/-- PROVED. `T⁻¹ (T y) = y` on the `ℤ`-indexed complexes. -/
theorem conjK_natHom_inv_hom (n : ℤ) (y : (natCx (contCochains k G' N')).X n) :
    (natHom T.inv).f n n rfl ((natHom T.hom).f n n rfl y) = y := by
  refine (natHom_comp_apply T.hom T.inv n y).symm.trans ?_
  rw [Iso.hom_inv_id]
  rcases n with n | n <;> rfl

variable (Z' : Submodule k (contCochain k G' N' 1)) (hZ' : ∀ z ∈ Z', contD k G' N' 1 z = 0)
  (Z : Submodule k (contCochain k G N 1)) (hZ : ∀ z ∈ Z, contD k G N 1 z = 0)

/-- PROVED. **A cochain isomorphism maps the cocycle condition `[C⁰ → Z' ⊔ B¹ → 0]` into `[C⁰ → Z ⊔
B¹ → 0]`** when it maps `Z' ⊔ B¹` into `Z ⊔ B¹` (hypothesis `h1`). -/
theorem conjK_condP_map
    (h1 : ∀ x ∈ Z' ⊔ contB1 k G' N', conjKOne T x ∈ Z ⊔ contB1 k G N) :
    ∀ (n : ℕ) (x : (contCochains k G' N').X n), x ∈ (condSubCx Z' hZ').P n →
      (T.hom.f n).hom x ∈ (condSubCx Z hZ).P n
  | 0, _, _ => trivial
  | 1, x, hx => h1 x hx
  | n + 2, x, hx => by
      have hx0 : x = 0 := (Submodule.mem_bot k).1 hx
      subst hx0
      rw [map_zero]
      exact zero_mem _

/-- DEF. The map of cocycle conditions induced by `T` (lane RC28's `cocycleCondition`), given `h1`.
-/
def conjKCondHom (h1 : ∀ x ∈ Z' ⊔ contB1 k G' N', conjKOne T x ∈ Z ⊔ contB1 k G N) :
    GHom (cocycleCondition Z' hZ') (cocycleCondition Z hZ) :=
  natHom ((condSubCx Z' hZ').map (condSubCx Z hZ) T.hom (conjK_condP_map T Z' hZ' Z hZ h1))

/-- PROVED. `conjKCondHom` is compatible with the inclusions into the local cochains and with `T`.
-/
theorem conjKCondHom_comm
    (h1 : ∀ x ∈ Z' ⊔ contB1 k G' N', conjKOne T x ∈ Z ⊔ contB1 k G N) (n : ℤ)
    (x : (cocycleCondition Z' hZ').X n) :
    (cocycleConditionι Z hZ).f n n rfl ((conjKCondHom T Z' hZ' Z hZ h1).f n n rfl x) =
      (natHom T.hom).f n n rfl ((cocycleConditionι Z' hZ').f n n rfl x) := by
  have h := congrArg (fun φ => (natHom φ).f n n rfl x)
    (SubCx.map_ι (condSubCx Z' hZ') (condSubCx Z hZ) T.hom (conjK_condP_map T Z' hZ' Z hZ h1))
  exact (natHom_comp_apply _ _ n x).symm.trans (h.trans (natHom_comp_apply _ _ n x))

/-- PROVED. The maps of `T` and `T⁻¹` are mutually inverse (one direction). -/
theorem conjKCondHom_inv_hom
    (h1 : ∀ x ∈ Z' ⊔ contB1 k G' N', conjKOne T x ∈ Z ⊔ contB1 k G N)
    (h2 : ∀ x ∈ Z ⊔ contB1 k G N, conjKOne T.symm x ∈ Z' ⊔ contB1 k G' N') (n : ℤ)
    (x : (cocycleCondition Z' hZ').X n) :
    (conjKCondHom T.symm Z hZ Z' hZ' h2).f n n rfl ((conjKCondHom T Z' hZ' Z hZ h1).f n n rfl x) =
      x := by
  apply cocycleConditionι_injective Z' hZ' n
  rw [conjKCondHom_comm T.symm Z hZ Z' hZ' h2, conjKCondHom_comm T Z' hZ' Z hZ h1]
  exact conjK_natHom_inv_hom T n _

/-- PROVED. The maps of `T` and `T⁻¹` are mutually inverse (other direction). -/
theorem conjKCondHom_hom_inv
    (h1 : ∀ x ∈ Z' ⊔ contB1 k G' N', conjKOne T x ∈ Z ⊔ contB1 k G N)
    (h2 : ∀ x ∈ Z ⊔ contB1 k G N, conjKOne T.symm x ∈ Z' ⊔ contB1 k G' N') (n : ℤ)
    (x : (cocycleCondition Z hZ).X n) :
    (conjKCondHom T Z' hZ' Z hZ h1).f n n rfl ((conjKCondHom T.symm Z hZ Z' hZ' h2).f n n rfl x) =
      x := by
  apply cocycleConditionι_injective Z hZ n
  rw [conjKCondHom_comm T Z' hZ' Z hZ h1, conjKCondHom_comm T.symm Z hZ Z' hZ' h2]
  exact conjK_natHom_inv_hom T.symm n _

end CocycleIso

/-! ### Kummer cocycles along the local conjugation -/

section KummerTransport

variable {F F' : Type} [Field F] [Field F'] (e : F ≃+* F')
  (Ē : AlgebraicClosure F ≃+* AlgebraicClosure F')
  (hĒ : ∀ a : F, Ē (algebraMap F (AlgebraicClosure F) a) =
    algebraMap F' (AlgebraicClosure F') (e a))
  (B : WeierstrassCurve F) (B' : WeierstrassCurve F') (hB : B.map (e : F →+* F') = B') (m : ℕ)
  {k : Type} [CommRing k] {N N' : Type} [AddCommGroup N] [Module k N] [AddCommGroup N']
  [Module k N'] (ψ : N' ≃ₗ[k] N) (ι' : TorsAlg F' B' m →+ N')

open scoped Classical in
/-- DEF. **The transported coefficient map** `ψ ∘ ι' ∘ Ē_*` (`Ē_* = conjKTors`). -/
def conjKIota : TorsAlg F B m →+ N :=
  (ψ : N' →ₗ[k] N).toAddMonoidHom.comp (ι'.comp (conjKTors e Ē hĒ B B' hB m))

open scoped Classical in
/-- PROVED. The value of `conjKIota`. -/
theorem conjKIota_apply (t : TorsAlg F B m) :
    conjKIota e Ē hĒ B B' hB m ψ ι' t = ψ (ι' (conjKTors e Ē hĒ B B' hB m t)) :=
  rfl

variable [DistribMulAction (Field.absoluteGaloisGroup F) N]
  [DistribMulAction (Field.absoluteGaloisGroup F') N']
  (φ : Field.absoluteGaloisGroup F ≃ₜ* Field.absoluteGaloisGroup F')
  (hφ : ∀ (σ : Field.absoluteGaloisGroup F) y, (φ σ).toAlgHom y = Ē (σ.toAlgHom (Ē.symm y)))
  (hψ : ∀ (σ : Field.absoluteGaloisGroup F) (n : N'), ψ (φ σ • n) = σ • ψ n)
  (hι' : ∀ (σ' : Field.absoluteGaloisGroup F') (t : TorsAlg F' B' m), ι' (σ' • t) = σ' • ι' t)

include hφ hψ hι' in
open scoped Classical in
/-- PROVED. **The transported coefficient map is equivariant** for `G_F`: from `hφ` (`φ σ = Ē σ
Ē⁻¹`), `hψ` (compatibility of `ψ` along `φ`) and `hι'`. -/
theorem conjKIota_smul (σ : Field.absoluteGaloisGroup F) (t : TorsAlg F B m) :
    conjKIota e Ē hĒ B B' hB m ψ ι' (σ • t) = σ • conjKIota e Ē hĒ B B' hB m ψ ι' t := by
  rw [conjKIota_apply, conjKIota_apply, conjKTors_smul e Ē hĒ B B' hB m σ (φ σ) (hφ σ), hι', hψ]

variable [CharZero F] [CharZero F'] [DecidableEq F] [DecidableEq F'] [B.IsElliptic]
  [B'.IsElliptic] [NeZero m]
  [SMulCommClass (Field.absoluteGaloisGroup F) k N] [TopologicalSpace N] [DiscreteTopology N]
  [ContinuousSMul (Field.absoluteGaloisGroup F) N]
  [SMulCommClass (Field.absoluteGaloisGroup F') k N'] [TopologicalSpace N'] [DiscreteTopology N']
  [ContinuousSMul (Field.absoluteGaloisGroup F') N']

include hφ hι' in
open scoped Classical in
/-- PROVED (tex 2812–2813: Kummer cocycles go to Kummer cocycles). **`T(a κ_{ι'}(e_* P)) − a
κ_{ι^τ}(P)` is a coboundary**, the coboundary of the constant `a ψ ι'(Q' − Ē_* Q)` with `Q, Q'` the
chosen `m`-th roots of `P`, `e_* P` (their difference is `m`-torsion). -/
theorem conjK_kummerCocycle_sub_mem (a : k) (P : B.toAffine.Point) :
    conjKOne (locConjPairIso φ ψ continuous_of_discreteTopology continuous_of_discreteTopology
        hψ) (kummerCocycleIn ι' a (conjKBase e B B' hB P)) -
      kummerCocycleIn (conjKIota e Ē hĒ B B' hB m ψ ι') a P ∈
      contB1 k (Field.absoluteGaloisGroup F) N := by
  have hT0 : divPt F' B' m (conjKBase e B B' hB P) - conjKPt e Ē hĒ B B' hB (divPt F B m P) ∈
      AddSubgroup.torsionBy (PtAlg F' B') (m : ℤ) := by
    rw [AddSubgroup.torsionBy.nsmul_iff, nsmul_sub, ← map_nsmul, nsmul_divPt, nsmul_divPt,
      conjKPt_basePt, sub_self]
  refine (mem_contB1_iff _).2 ⟨constCochain (a • ψ (ι' ⟨_, hT0⟩)), ?_⟩
  apply Subtype.ext
  funext g
  refine (cfun_contD_constCochain (k := k) (G := Field.absoluteGaloisGroup F) (M := N) _ g).trans
    ?_
  have key : kummerFun F' B' m (conjKBase e B B' hB P) (φ (g 0)) =
      (φ (g 0) • (⟨_, hT0⟩ : TorsAlg F' B' m) - ⟨_, hT0⟩) +
        conjKTors e Ē hĒ B B' hB m (kummerFun F B m P (g 0)) := by
    apply Subtype.ext
    change φ (g 0) • divPt F' B' m (conjKBase e B B' hB P) - divPt F' B' m (conjKBase e B B' hB P) =
      (φ (g 0) • (divPt F' B' m (conjKBase e B B' hB P) -
          conjKPt e Ē hĒ B B' hB (divPt F B m P)) -
        (divPt F' B' m (conjKBase e B B' hB P) - conjKPt e Ē hĒ B B' hB (divPt F B m P))) +
        conjKPt e Ē hĒ B B' hB (g 0 • divPt F B m P - divPt F B m P)
    rw [map_sub, conjKPt_smul e Ē hĒ B B' hB (g 0) (φ (g 0)) (hφ (g 0)), smul_sub]
    abel
  change g 0 • (a • ψ (ι' ⟨_, hT0⟩)) - a • ψ (ι' ⟨_, hT0⟩) =
    ψ (a • ι' (kummerFun F' B' m (conjKBase e B B' hB P) (φ (g 0)))) -
      a • ψ (ι' (conjKTors e Ē hĒ B B' hB m (kummerFun F B m P (g 0))))
  rw [key, map_add, map_sub, hι', smul_add, map_add, map_smul, map_smul, map_sub, hψ, smul_sub,
    smul_comm (g 0) a]
  abel

include hφ hι' in
open scoped Classical in
/-- PROVED. **The transport maps the Kummer span `Z' ⊔ B¹` at `w` into the transported Kummer span
at `v`.** -/
theorem conjK_kummerZ_map (x : contCochain k (Field.absoluteGaloisGroup F') N' 1)
    (hx : x ∈ kummerZ' k ι' ⊔ contB1 k (Field.absoluteGaloisGroup F') N') :
    conjKOne (locConjPairIso φ ψ continuous_of_discreteTopology continuous_of_discreteTopology hψ)
        x ∈ kummerZ' k (conjKIota e Ē hĒ B B' hB m ψ ι') ⊔
          contB1 k (Field.absoluteGaloisGroup F) N := by
  set T := locConjPairIso φ ψ continuous_of_discreteTopology continuous_of_discreteTopology hψ
  have hle : kummerZ' k ι' ⊔ contB1 k (Field.absoluteGaloisGroup F') N' ≤
      (kummerZ' k (conjKIota e Ē hĒ B B' hB m ψ ι') ⊔
        contB1 k (Field.absoluteGaloisGroup F) N).comap (conjKOne T) := by
    refine sup_le (Submodule.span_le.2 ?_) fun y hy => ?_
    · rintro _ ⟨⟨a, P'⟩, rfl⟩
      obtain ⟨P, rfl⟩ := conjKBase_surjective e B B' hB P'
      rw [SetLike.mem_coe, Submodule.mem_comap]
      refine Submodule.mem_sup.2 ⟨kummerCocycleIn (conjKIota e Ē hĒ B B' hB m ψ ι') a P,
        Submodule.subset_span ⟨(a, P), rfl⟩, _,
        conjK_kummerCocycle_sub_mem e Ē hĒ B B' hB m ψ ι' φ hφ hψ hι' a P, ?_⟩
      exact add_sub_cancel _ _
    · exact Submodule.mem_sup_right (conjK_map_contB1 T hy)
  exact hle hx

include hφ hι' in
open scoped Classical in
/-- PROVED. The inverse transport maps the Kummer span at `v` back into the one at `w`. -/
theorem conjK_kummerZ_map_inv (x : contCochain k (Field.absoluteGaloisGroup F) N 1)
    (hx : x ∈ kummerZ' k (conjKIota e Ē hĒ B B' hB m ψ ι') ⊔
      contB1 k (Field.absoluteGaloisGroup F) N) :
    conjKOne (locConjPairIso φ ψ continuous_of_discreteTopology continuous_of_discreteTopology
        hψ).symm x ∈ kummerZ' k ι' ⊔ contB1 k (Field.absoluteGaloisGroup F') N' := by
  set T := locConjPairIso φ ψ continuous_of_discreteTopology continuous_of_discreteTopology hψ
  have hle : kummerZ' k (conjKIota e Ē hĒ B B' hB m ψ ι') ⊔
      contB1 k (Field.absoluteGaloisGroup F) N ≤
      (kummerZ' k ι' ⊔ contB1 k (Field.absoluteGaloisGroup F') N').comap (conjKOne T.symm) := by
    refine sup_le (Submodule.span_le.2 ?_) fun y hy => ?_
    · rintro _ ⟨⟨a, P⟩, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      have hb := conjK_map_contB1 T.symm
        (conjK_kummerCocycle_sub_mem e Ē hĒ B B' hB m ψ ι' φ hφ hψ hι' a P)
      refine Submodule.mem_sup.2 ⟨kummerCocycleIn ι' a (conjKBase e B B' hB P),
        Submodule.subset_span ⟨(a, conjKBase e B B' hB P), rfl⟩, _, neg_mem hb, ?_⟩
      rw [map_sub, conjKOne_symm_apply]
      abel
    · exact Submodule.mem_sup_right (conjK_map_contB1 T.symm hy)
  exact hle hx

end KummerTransport

/-! ### Isomorphisms of local conditions -/

section CondIso

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {k : Type} [CommRing k] {M : Type} [AddCommGroup M] [Module k M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
  [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul (GKS K S) M] {v : Places K S}

/-- **An isomorphism of local conditions** at `v`: mutually inverse maps of the condition complexes
compatible with the two maps into the local cochains. Kind: DEF (structure); non-vacuous
(`ConjKCondIso.refl`). The transported condition and the Kummer condition at `v` live on different
complexes, so the statement of tex 2812–2813 is an isomorphism of this kind, not an equality
(DEPARTURE, form). -/
structure ConjKCondIso (c c' : CondAt K S k M v) where
  hom : GHom c.U c'.U
  inv : GHom c'.U c.U
  inv_hom : ∀ (n : ℤ) (x : c.U.X n), inv.f n n rfl (hom.f n n rfl x) = x
  hom_inv : ∀ (n : ℤ) (x : c'.U.X n), hom.f n n rfl (inv.f n n rfl x) = x
  comm : ∀ (n : ℤ) (x : c.U.X n), c'.i.f n n rfl (hom.f n n rfl x) = c.i.f n n rfl x

/-- DEF. The identity isomorphism (non-vacuity of `ConjKCondIso`). -/
def ConjKCondIso.refl (c : CondAt K S k M v) : ConjKCondIso c c where
  hom := idGHom _
  inv := idGHom _
  inv_hom _ _ := rfl
  hom_inv _ _ := rfl
  comm _ _ := rfl

variable {c c' : CondAt K S k M v}

/-- PROVED. The inverse map is compatible with the inclusions. -/
theorem ConjKCondIso.comm_inv (I : ConjKCondIso c c') (n : ℤ) (x : c'.U.X n) :
    c.i.f n n rfl (I.inv.f n n rfl x) = c'.i.f n n rfl x := by
  rw [← I.comm, I.hom_inv]

/-- PROVED. **Isomorphic conditions have the same image in the local cochains**, in every degree. -/
theorem ConjKCondIso.range_eq (I : ConjKCondIso c c') (n : ℤ) :
    LinearMap.range (c.i.f n n rfl) = LinearMap.range (c'.i.f n n rfl) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨I.hom.f n n rfl x, I.comm n x⟩
  · rintro ⟨x, rfl⟩
    exact ⟨I.inv.f n n rfl x, I.comm_inv n x⟩

/-- PROVED. Injectivity of the condition transfers along an isomorphism. -/
theorem ConjKCondIso.isInjective (I : ConjKCondIso c c') (hc : c.IsInjective) :
    c'.IsInjective := by
  intro n x y hxy
  have h : I.inv.f n n rfl x = I.inv.f n n rfl y :=
    hc n (by rw [I.comm_inv, I.comm_inv, hxy])
  rw [← I.hom_inv n x, h, I.hom_inv]

/-- PROVED. The inclusion of `c` factors through that of `c'`. -/
theorem ConjKCondIso.toCC_eq (I : ConjKCondIso c c') :
    GHom.toCC c.i = GHom.toCC I.hom ≫ GHom.toCC c'.i := by
  ext n x
  exact (I.comm n x).symm

/-- PROVED. The inclusion of `c'` factors through that of `c`. -/
theorem ConjKCondIso.toCC_eq_inv (I : ConjKCondIso c c') :
    GHom.toCC c'.i = GHom.toCC I.inv ≫ GHom.toCC c.i := by
  ext n x
  exact (I.comm_inv n x).symm

/-- PROVED. **Isomorphic conditions have the same image in local cohomology** `Hⁿ`. -/
theorem ConjKCondIso.range_homology (I : ConjKCondIso c c') (n : ℤ) :
    LinearMap.range (HomologicalComplex.homologyMap (GHom.toCC c.i) n).hom =
      LinearMap.range (HomologicalComplex.homologyMap (GHom.toCC c'.i) n).hom := by
  apply le_antisymm
  · rw [I.toCC_eq, HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp]
    exact LinearMap.range_comp_le_range _ _
  · rw [I.toCC_eq_inv, HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp]
    exact LinearMap.range_comp_le_range _ _

/-- DEF. Composition of isomorphisms of local conditions. -/
def ConjKCondIso.trans {c'' : CondAt K S k M v} (I : ConjKCondIso c c')
    (J : ConjKCondIso c' c'') : ConjKCondIso c c'' where
  hom := ghomComp I.hom J.hom
  inv := ghomComp J.inv I.inv
  inv_hom n x := by
    change I.inv.f n n rfl (J.inv.f n n rfl (J.hom.f n n rfl (I.hom.f n n rfl x))) = x
    rw [J.inv_hom, I.inv_hom]
  hom_inv n x := by
    change J.hom.f n n rfl (I.hom.f n n rfl (I.inv.f n n rfl (J.inv.f n n rfl x))) = x
    rw [I.hom_inv, J.hom_inv]
  comm n x := by
    change c''.i.f n n rfl (J.hom.f n n rfl (I.hom.f n n rfl x)) = c.i.f n n rfl x
    rw [J.comm, I.comm]

/-- DEF. Equal conditions are isomorphic. -/
def ConjKCondIso.ofEq (h : c = c') : ConjKCondIso c c' :=
  h ▸ ConjKCondIso.refl c

end CondIso

/-! ### The transport of a Kummer condition from the conjugate place -/

section TransportKummer

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (C : ActualConj K S) (k : Type) [CommRing k] {M : Type} [AddCommGroup M] [Module k M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
  [DiscreteTopology M] [ContinuousAdd M] [ContinuousSMul (GKS K S) M]
  (g : GKS K S) {v w : Places K S}
  (hvw : w.1.asIdeal = v.1.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K))
  (hg : ∀ σ : Gloc K v.1,
    locMap K S w.1 (locConjGal C.κ hvw σ) = g * C.conj (locMap K S v.1 σ) * g⁻¹)
  (Bv : WeierstrassCurve (v.1.adicCompletion K)) (Bw : WeierstrassCurve (w.1.adicCompletion K))
  (hB : Bv.map (locConjCompletion C.κ hvw : v.1.adicCompletion K →+* w.1.adicCompletion K) = Bw)
  (m : ℕ) (ιw : TorsAlg (w.1.adicCompletion K) Bw m →+ ResMod (locMap K S w.1) M)

/-- PROVED (`locConjGal_apply`). The local conjugation `φ_v` is `σ ↦ Ē σ Ē⁻¹`. -/
theorem conjK_locConjGal_apply (σ : Gloc K v.1) (y : AlgebraicClosure (w.1.adicCompletion K)) :
    (locConjGal C.κ hvw σ).toAlgHom y =
      locConjBar C.κ hvw (σ.toAlgHom ((locConjBar C.κ hvw).symm y)) :=
  locConjGal_apply C.κ hvw σ y

/-- DEF (tex 2812–2813). **The transported coefficient map at `v`**: `t ↦ g⁻¹ · ι_w(Ē_* t)` into
`τ^*M` (`conjTransportEquiv`, `conjKTors` along `locConjBar`). -/
def conjKIotaAt :
    TorsAlg (v.1.adicCompletion K) Bv m →+ ResMod (locMap K S v.1) (PullMod C.conj M) :=
  conjKIota (locConjCompletion C.κ hvw) (locConjBar C.κ hvw) (locConjBar_algebraMap C.κ hvw) Bv
    Bw hB m (conjTransportEquiv C k M g v.1 w.1) ιw

omit [TopologicalSpace M] [DiscreteTopology M] [ContinuousAdd M] [ContinuousSMul (GKS K S) M] in
/-- PROVED. The value of `conjKIotaAt`. -/
theorem conjKIotaAt_apply (t : TorsAlg (v.1.adicCompletion K) Bv m) :
    conjKIotaAt C k g hvw Bv Bw hB m ιw t =
      conjTransportEquiv C k M g v.1 w.1 (ιw (conjKTors (locConjCompletion C.κ hvw)
        (locConjBar C.κ hvw) (locConjBar_algebraMap C.κ hvw) Bv Bw hB m t)) :=
  rfl

variable (hιw : ∀ (σ : Gloc K w.1) (t : TorsAlg (w.1.adicCompletion K) Bw m), ιw (σ • t) = σ • ιw t)

omit [TopologicalSpace M] [DiscreteTopology M] [ContinuousAdd M] [ContinuousSMul (GKS K S) M] in
include hg hιw in
/-- PROVED. `conjKIotaAt` is `G_{K_v}`-equivariant (from `hg` and `hιw`). -/
theorem conjKIotaAt_smul (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) Bv m) :
    conjKIotaAt C k g hvw Bv Bw hB m ιw (σ • t) = σ • conjKIotaAt C k g hvw Bv Bw hB m ιw t :=
  conjKIota_smul (locConjCompletion C.κ hvw) (locConjBar C.κ hvw) (locConjBar_algebraMap C.κ hvw)
    Bv Bw hB m (conjTransportEquiv C k M g v.1 w.1) ιw (locConjGal C.κ hvw)
    (conjK_locConjGal_apply C hvw) (conjTransportEquiv_compat C k M g hvw hg) hιw σ t

variable [DecidableEq (v.1.adicCompletion K)] [DecidableEq (w.1.adicCompletion K)] [Bv.IsElliptic]
  [Bw.IsElliptic] [NeZero m]

/-- PROVED (tex 2812–2813: "Kummer conditions at `2N` are preserved by this transport"). **The
transport (`conjTransport`, any `g` with `hg`) of the Kummer condition `kummerAt w B_w m ι_w` at `w
= τv` is isomorphic, compatibly with the cochain isomorphism, to the Kummer condition `kummerAt v
B_v m ι^τ` at `v`** for `ι^τ = conjKIotaAt`, whenever `B_v.map e = B_w` (`hB`). Hypotheses: `hvw`
(DEF), `hg` (PROVED satisfiable, `conjTransportElt_spec`), `hB` (PROVED for the actual twists,
`conjK_localTwist_map`), `hιw` (the equivariance of `ι_w`, PROVED for the actual `ι_w`,
`kummerIota_smul`). -/
def conjKTransportKummerIso :
    ConjKCondIso (conjTransport C g hvw hg (kummerAt (k := k) w Bw m ιw hιw))
      (kummerAt (k := k) v Bv m (conjKIotaAt C k g hvw Bv Bw hB m ιw)
        (conjKIotaAt_smul C k g hvw hg Bv Bw hB m ιw hιw)) where
  hom := conjKCondHom (conjTransportIso C k M g hvw hg) (kummerZ' k ιw) (kummerZ'_cocycle k ιw hιw)
    (kummerZ' k (conjKIotaAt C k g hvw Bv Bw hB m ιw))
    (kummerZ'_cocycle k _ (conjKIotaAt_smul C k g hvw hg Bv Bw hB m ιw hιw))
    (conjK_kummerZ_map (locConjCompletion C.κ hvw) (locConjBar C.κ hvw)
      (locConjBar_algebraMap C.κ hvw) Bv Bw hB m (conjTransportEquiv C k M g v.1 w.1) ιw
      (locConjGal C.κ hvw) (conjK_locConjGal_apply C hvw) (conjTransportEquiv_compat C k M g hvw hg)
      hιw)
  inv := conjKCondHom (conjTransportIso C k M g hvw hg).symm
    (kummerZ' k (conjKIotaAt C k g hvw Bv Bw hB m ιw))
    (kummerZ'_cocycle k _ (conjKIotaAt_smul C k g hvw hg Bv Bw hB m ιw hιw))
    (kummerZ' k ιw) (kummerZ'_cocycle k ιw hιw)
    (conjK_kummerZ_map_inv (locConjCompletion C.κ hvw) (locConjBar C.κ hvw)
      (locConjBar_algebraMap C.κ hvw) Bv Bw hB m (conjTransportEquiv C k M g v.1 w.1) ιw
      (locConjGal C.κ hvw) (conjK_locConjGal_apply C hvw) (conjTransportEquiv_compat C k M g hvw hg)
      hιw)
  inv_hom := conjKCondHom_inv_hom _ _ _ _ _ _ _
  hom_inv := conjKCondHom_hom_inv _ _ _ _ _ _ _
  comm := conjKCondHom_comm _ _ _ _ _ _

/-- PROVED. The transported Kummer condition and the Kummer condition of `ι^τ` have the same image
in the local cochains. -/
theorem conjKTransportKummer_range (n : ℤ) :
    LinearMap.range ((conjTransport C g hvw hg (kummerAt (k := k) w Bw m ιw hιw)).i.f n n rfl) =
      LinearMap.range ((kummerAt (k := k) v Bv m (conjKIotaAt C k g hvw Bv Bw hB m ιw)
        (conjKIotaAt_smul C k g hvw hg Bv Bw hB m ιw hιw)).i.f n n rfl) :=
  (conjKTransportKummerIso C k g hvw hg Bv Bw hB m ιw hιw).range_eq n

/-- PROVED. **The `H¹` image of the transported Kummer condition is the `k`-span of the Kummer image
of `B_v(K_v)` through `ι^τ`** (lane RC29's `range_homologyMap_kummerConditionIn`). -/
theorem conjKTransportKummer_range_H1 :
    LinearMap.range (HomologicalComplex.homologyMap
      (GHom.toCC (conjTransport C g hvw hg (kummerAt (k := k) w Bw m ιw hιw)).i) 1).hom =
      Submodule.span k (Set.range (kummerMapIn k (conjKIotaAt C k g hvw Bv Bw hB m ιw)
        (conjKIotaAt_smul C k g hvw hg Bv Bw hB m ιw hιw))) :=
  ((conjKTransportKummerIso C k g hvw hg Bv Bw hB m ιw hιw).range_homology 1).trans
    (range_homologyMap_kummerConditionIn k _ _)

end TransportKummer

/-! ### The actual local twist at the conjugate place -/

section ActualTwist

variable {K : Type} [Field K] [NumberField K] (κ : K ≃+* K) {v w : HeightOneSpectrum (𝓞 K)}
  (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K))
  (W : WeierstrassCurve K) (hW : W.map (κ : K →+* K) = W)

include hW in
/-- PROVED. `W.map κ = W` (hypothesis `hW`, RC28 DEPARTURE 3) gives `(W_{K_v}).map e = W_{K_w}` for
`e = locConjCompletion`. -/
theorem conjK_baseChange_map :
    (W.baseChange (v.adicCompletion K)).map
        (locConjCompletion κ hvw : v.adicCompletion K →+* w.adicCompletion K) =
      W.baseChange (w.adicCompletion K) := by
  rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
  have : (locConjCompletion κ hvw : v.adicCompletion K →+* w.adicCompletion K).comp
      (algebraMap K (v.adicCompletion K)) =
        (algebraMap K (w.adicCompletion K)).comp (κ : K →+* K) :=
    RingHom.ext fun a => locConjCompletion_algebraMap κ hvw a
  rw [this, ← WeierstrassCurve.map_map, hW]
  rfl

include hW in
/-- PROVED. **The local twists correspond**: `(localTwist W h v).map e = localTwist W h w` from
`W.map κ = W` and `κ h = h` (hypothesis `hκh`: ELLIOT, the quadratic twist datum is defined over the
fixed field of `κ`, as `hW`; non-vacuous, `conjK_hκh_nonvacuous`). -/
theorem conjK_localTwist_map {h : K} (hκh : κ h = h) :
    (localTwist W h v).map (locConjCompletion κ hvw : v.adicCompletion K →+* w.adicCompletion K) =
      localTwist W h w := by
  rw [localTwist, TwistDictionary.twistK_map, conjK_baseChange_map κ hvw W hW]
  change TwistDictionary.twistK _
    (locConjCompletion κ hvw (algebraMap K (v.adicCompletion K) h)) = _
  rw [locConjCompletion_algebraMap, hκh]

end ActualTwist

/-! ### The image in `H¹` of a transported condition -/

section TransportH1

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (C : ActualConj K S) {k : Type} [CommRing k] {M : Type} [AddCommGroup M] [Module k M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
  [DiscreteTopology M] [ContinuousAdd M] [ContinuousSMul (GKS K S) M]
  (g : GKS K S) {v w : Places K S}
  (hvw : w.1.asIdeal = v.1.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K))
  (hg : ∀ σ : Gloc K v.1,
    locMap K S w.1 (locConjGal C.κ hvw σ) = g * C.conj (locMap K S v.1 σ) * g⁻¹)

/-- PROVED. **The `Hⁿ` image of a transported condition is the image of the `Hⁿ` image at `w` under
the transport isomorphism.** -/
theorem conjTransport_range_H1 (c : CondAt K S k M w) (n : ℤ) :
    LinearMap.range (HomologicalComplex.homologyMap (GHom.toCC (conjTransport C g hvw hg c).i)
      n).hom = (LinearMap.range (HomologicalComplex.homologyMap (GHom.toCC c.i) n).hom).map
        (HomologicalComplex.homologyMap (GHom.toCC (conjTransportGHom C g hvw hg)) n).hom := by
  change LinearMap.range (HomologicalComplex.homologyMap
    (GHom.toCC (ghomComp c.i (conjTransportGHom C g hvw hg))) n).hom = _
  rw [← GHom.toCC_comp, HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp,
    LinearMap.range_comp]

end TransportH1

/-! ### The actual Kummer condition at the conjugate place -/

section ActualKummer

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (C : ActualConj K S) (W : WeierstrassCurve K) [W.IsElliptic]
  (hW : W.map (C.κ : K →+* K) = W) (i : ℕ) (s : KS K S) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (hκh : C.κ h = h)
  (α : GKS K S →* (Acoef i)ˣ) [IsOpenKer α] (hFull : FullTorsion K S W (2 ^ i))
  (g : GKS K S) {v w : Places K S}
  (hvw : w.1.asIdeal = v.1.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K))
  (hg : ∀ σ : Gloc K v.1,
    locMap K S w.1 (locConjGal C.κ hvw σ) = g * C.conj (locMap K S v.1 σ) * g⁻¹)
  (hαw : IsLocallyQuadAt i α (quadChar s hs hs0) w.1)

/-- DEF. **The transported coefficient map of the actual Kummer condition**: `conjKIotaAt` at
`ι_{τv} = kummerIota … w`. -/
def conjKActualIota :
    TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i) →+
      ResMod (locMap K S v.1) (PullMod C.conj (Mcoef K S W i α)) :=
  conjKIotaAt C (Acoef i) g hvw (localTwist W h v.1) (localTwist W h w.1)
    (conjK_localTwist_map C.κ hvw W hW hκh) (2 ^ i) (kummerIota W i s hs hs0 α hFull w.1)

omit [IsOpenKer α] in
include hg hαw in
/-- PROVED. `conjKActualIota` is `G_{K_v}`-equivariant (hypotheses `hg`, `hαw`). -/
theorem conjKActualIota_smul (σ : Gloc K v.1)
    (t : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i)) :
    conjKActualIota C W hW i s hs hs0 hκh α hFull g hvw (σ • t) =
      σ • conjKActualIota C W hW i s hs hs0 hκh α hFull g hvw t :=
  conjKIotaAt_smul C (Acoef i) g hvw hg _ _ _ _ _ (kummerIota_smul W i s hs hs0 α hFull w.1 hαw) σ t

open scoped Classical in
/-- DEF. **The Kummer condition at `v` for `τ^*M_i` through the transported coefficient map**
(`kummerAt v (localTwist W h v) (2^i) ι^τ`). -/
def conjKActualKummerAt : CondAt K S (Acoef i) (PullMod C.conj (Mcoef K S W i α)) v :=
  haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  kummerAt v (localTwist W h v.1) (2 ^ i) (conjKActualIota C W hW i s hs hs0 hκh α hFull g hvw)
    (conjKActualIota_smul C W hW i s hs hs0 hκh α hFull g hvw hg hαw)

open scoped Classical in
/-- PROVED (tex 2812–2813). **The transport of the actual Kummer condition at `τv` (lane RC29's
`actualKummerAt`) is isomorphic, compatibly with the cochain isomorphism, to the Kummer condition of
`B_v = localTwist W h v` at `v` through `ι^τ`.** Hypotheses: `hW` (RC28 DEPARTURE 3), `hκh`
(ELLIOT), `hFull` (GLUE, RC28), `hαw` (lane RC29's local triviality at `τv`), `hvw`, `hg`. -/
def conjKActualIso :
    ConjKCondIso (conjTransport C g hvw hg (actualKummerAt W i s hs hs0 α hFull w hαw))
      (conjKActualKummerAt C W hW i s hs hs0 hκh α hFull g hvw hg hαw) :=
  haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) w.1
  conjKTransportKummerIso C (Acoef i) g hvw hg (localTwist W h v.1) (localTwist W h w.1)
    (conjK_localTwist_map C.κ hvw W hW hκh) (2 ^ i) (kummerIota W i s hs hs0 α hFull w.1)
    (kummerIota_smul W i s hs hs0 α hFull w.1 hαw)

/-- PROVED. The two conditions have the same image in the local cochains. -/
theorem conjKActual_range (n : ℤ) :
    LinearMap.range ((conjTransport C g hvw hg (actualKummerAt W i s hs hs0 α hFull w hαw)).i.f
      n n rfl) =
      LinearMap.range ((conjKActualKummerAt C W hW i s hs hs0 hκh α hFull g hvw hg hαw).i.f
        n n rfl) :=
  (conjKActualIso C W hW i s hs hs0 hκh α hFull g hvw hg hαw).range_eq n

/-- PROVED. `conjKActualKummerAt` is a subcomplex. -/
theorem conjKActual_isInjective :
    (conjKActualKummerAt C W hW i s hs hs0 hκh α hFull g hvw hg hαw).IsInjective :=
  (conjKActualIso C W hW i s hs hs0 hκh α hFull g hvw hg hαw).isInjective
    (conjTransport_isInjective C g hvw hg _ (actualKummerAt_isInjective W i s hs hs0 α hFull w hαw))

open scoped Classical in
/-- PROVED. **The `H¹` image of the transported actual Kummer condition is the `A_i`-span of the
Kummer image of `B_v(K_v)` through `ι^τ`.** -/
theorem conjKActual_range_H1 :
    haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
    LinearMap.range (HomologicalComplex.homologyMap
      (GHom.toCC (conjTransport C g hvw hg (actualKummerAt W i s hs hs0 α hFull w hαw)).i) 1).hom =
      Submodule.span (Acoef i) (Set.range (kummerMapIn (Acoef i)
        (conjKActualIota C W hW i s hs hs0 hκh α hFull g hvw)
        (conjKActualIota_smul C W hW i s hs hs0 hκh α hFull g hvw hg hαw))) := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) w.1
  exact conjKTransportKummer_range_H1 C (Acoef i) g hvw hg (localTwist W h v.1) (localTwist W h w.1)
    (conjK_localTwist_map C.κ hvw W hW hκh) (2 ^ i) (kummerIota W i s hs hs0 α hFull w.1)
    (kummerIota_smul W i s hs hs0 α hFull w.1 hαw)

/-- PROVED. **It is also the `A_i`-span of the transport of the local Kummer image at `τv`** (lane
RC29's `actualKummerAt_range_eq_span`). -/
theorem conjKActual_range_H1_transport :
    LinearMap.range (HomologicalComplex.homologyMap
      (GHom.toCC (conjTransport C g hvw hg (actualKummerAt W i s hs hs0 α hFull w hαw)).i) 1).hom =
      Submodule.span (Acoef i)
        ((HomologicalComplex.homologyMap (GHom.toCC (conjTransportGHom C g hvw hg)) 1).hom ''
          Set.range (actualKummerMap W i s hs hs0 α hFull w hαw)) := by
  rw [conjTransport_range_H1, actualKummerAt_range_eq_span, Submodule.map_span]

end ActualKummer

/-- PROVED. Non-vacuity of `hκh`: `κ 1 = 1` (with `1 ≠ 0`). -/
theorem conjK_hκh_nonvacuous {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} (C : ActualConj K S) : ∃ h : K, h ≠ 0 ∧ C.κ h = h :=
  ⟨1, one_ne_zero, map_one _⟩

section ActualKummerConjPlace

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (C : ActualConj K S) (W : WeierstrassCurve K) [W.IsElliptic]
  (hW : W.map (C.κ : K →+* K) = W) (i : ℕ) (s : KS K S) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (hκh : C.κ h = h)
  (α : GKS K S →* (Acoef i)ˣ) [IsOpenKer α] (hFull : FullTorsion K S W (2 ^ i)) (v : Places K S)
  (hα : IsLocallyQuadAt i α (quadChar s hs hs0) (locConjPlaceS C v).1)

open scoped Classical in
/-- PROVED (tex 2810–2813, split places). The statement of `conjKActualIso` at the conjugate place
`τv = locConjPlaceS C v` with the canonical inner element (`conjTransportConjPlace`). -/
def conjKActualConjPlaceIso :
    ConjKCondIso (conjTransportConjPlace C v (actualKummerAt W i s hs hs0 α hFull
        (locConjPlaceS C v) hα))
      (conjKActualKummerAt C W hW i s hs hs0 hκh α hFull
        (conjTransportElt C (locConjPlaceS_asIdeal C v)) (locConjPlaceS_asIdeal C v)
        (conjTransportElt_spec C (locConjPlaceS_asIdeal C v)) hα) :=
  conjKActualIso C W hW i s hs hs0 hκh α hFull _ _
    (conjTransportElt_spec C (locConjPlaceS_asIdeal C v)) hα

end ActualKummerConjPlace

/-! ### Comparison of two decomposition embeddings along the local conjugation -/

section EmbCompare

variable {K : Type} [Field K] [NumberField K] (κ : K ≃+* K)
  (τ : AlgebraicClosure K ≃+* AlgebraicClosure K)
  (hτ : ∀ x : K, τ (algebraMap K (AlgebraicClosure K) x) =
    algebraMap K (AlgebraicClosure K) (κ x))
  {v w : HeightOneSpectrum (𝓞 K)}
  (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K))
  (jv : AlgebraicClosure K →ₐ[K] AlgebraicClosure (v.adicCompletion K))
  (jw : AlgebraicClosure K →ₐ[K] AlgebraicClosure (w.adicCompletion K))

/-- DEF. The `K`-embedding `J ∘ j_w ∘ τ : K̄ → K̄_v` (`J = locConjLift`) for a `K`-embedding `j_w :
K̄ → K̄_w`. -/
def conjKAlgOf : AlgebraicClosure K →ₐ[K] AlgebraicClosure (v.adicCompletion K) :=
  ⟨(locConjLift κ hvw).comp
      ((jw : AlgebraicClosure K →+* AlgebraicClosure (w.adicCompletion K)).comp
      (τ : AlgebraicClosure K →+* AlgebraicClosure K)),
    fun c => by
      change locConjLift κ hvw (jw (τ (algebraMap K (AlgebraicClosure K) c))) = _
      rw [hτ, jw.commutes, IsScalarTower.algebraMap_apply K (w.adicCompletion K)
          (AlgebraicClosure (w.adicCompletion K)), locConjLift_algebraMap,
        locConjCompletion_symm_algebraMap, ← IsScalarTower.algebraMap_apply]⟩

include hτ in
/-- PROVED (Mathlib `AlgHom.exists_comp_eq_of_normal`). **Two `K`-embeddings differ by an
automorphism**: `j_v ∘ h = J ∘ j_w ∘ τ` for some `h ∈ Gal(K̄/K)`. -/
theorem conjK_exists_comp_of :
    ∃ h : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∀ x : AlgebraicClosure K,
      jv (h x) = locConjLift κ hvw (jw (τ x)) := by
  obtain ⟨h, hh⟩ := AlgHom.exists_comp_eq_of_normal jv (conjKAlgOf κ τ hτ hvw jw)
  exact ⟨h, fun x => DFunLike.congr_fun hh x⟩

/-- PROVED. **For any intertwining embeddings `j_v`, `j_w`** (hypotheses `hjv`, `hjw`: PROVED for
lane RC29's `decompEmb`, `decompEmb_decompMap`), `d_w(φ_v σ) = c_h(h⁻¹ d_v(σ) h)` for the comparison
element `h`. -/
theorem conjK_decompMap_of
    (hjv : ∀ (σ : Gloc K v) (y : AlgebraicClosure K),
      jv (@id (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (decompMap K v σ) y) =
        @id (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
          AlgebraicClosure (v.adicCompletion K)) σ (jv y))
    (hjw : ∀ (σ : Gloc K w) (y : AlgebraicClosure K),
      jw (@id (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (decompMap K w σ) y) =
        @id (AlgebraicClosure (w.adicCompletion K) ≃ₐ[w.adicCompletion K]
          AlgebraicClosure (w.adicCompletion K)) σ (jw y))
    (h : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hh : ∀ x, jv (h x) = locConjLift κ hvw (jw (τ x))) (σ : Gloc K v) :
    decompMap K w (locConjGal κ hvw σ) =
      conjAbs K κ τ hτ (h⁻¹ * @id (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
        (decompMap K v σ) * h) := by
  apply AlgEquiv.ext
  intro y
  apply (jw : AlgebraicClosure K →+* AlgebraicClosure (w.adicCompletion K)).injective
  apply (locConjLift κ hvw).injective
  set sg := @id (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (decompMap K v σ) with hsg
  have e1 : locConjLift κ hvw (jw
      (@id (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (decompMap K w (locConjGal κ hvw σ)) y)) =
      @id (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
        AlgebraicClosure (v.adicCompletion K)) σ (locConjLift κ hvw (jw y)) := by
    rw [hjw, locConjLift_locConjGal]
  have e2 : (conjAbs K κ τ hτ (h⁻¹ * sg * h)) y = τ (h.symm (sg (h (τ.symm y)))) := rfl
  have e3 : jv (sg (h (τ.symm y))) =
      @id (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
        AlgebraicClosure (v.adicCompletion K)) σ (jv (h (τ.symm y))) :=
    hjv σ _
  change locConjLift κ hvw (jw
      (@id (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (decompMap K w (locConjGal κ hvw σ)) y)) =
    locConjLift κ hvw (jw ((conjAbs K κ τ hτ (h⁻¹ * sg * h)) y))
  rw [e1, e2, ← hh, AlgEquiv.apply_symm_apply, e3, hh, RingEquiv.apply_symm_apply]

/-- PROVED. `Ē(j_v y) = j_w(τ(h⁻¹ y))` for the comparison element `h` (from `hh`). -/
theorem conjK_bar_of (h : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hh : ∀ x, jv (h x) = locConjLift κ hvw (jw (τ x))) (y : AlgebraicClosure K) :
    locConjBar κ hvw (jv y) = jw (τ (h.symm y)) := by
  have := hh (h.symm y)
  rw [AlgEquiv.apply_symm_apply] at this
  rw [this, locConjBar_locConjLift]

end EmbCompare

section EmbCompareS

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (C : ActualConj K S) {v w : HeightOneSpectrum (𝓞 K)}
  (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K))

/-- PROVED. The inner element `g = c(h̄)⁻¹` of the comparison element `h` satisfies `hg`. -/
theorem conjK_locMap_of_decompMap (h : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hd : ∀ σ : Gloc K v, decompMap K w (locConjGal C.κ hvw σ) =
      conjAbs K C.κ C.τ C.hτ (h⁻¹ * @id (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
        (decompMap K v σ) * h))
    (σ : Gloc K v) :
    locMap K S w (locConjGal C.κ hvw σ) =
      (C.conj (resAbs K S h))⁻¹ * C.conj (locMap K S v σ) * (C.conj (resAbs K S h))⁻¹⁻¹ := by
  have e1 : locMap K S w (locConjGal C.κ hvw σ) =
      resAbs K S (decompMap K w (locConjGal C.κ hvw σ)) := rfl
  have e2 : locMap K S v σ = resAbs K S (decompMap K v σ) := rfl
  rw [e1, hd σ, resAbs_conjAbs K C.κ C.τ C.hτ S C.hS, e2, inv_inv]
  rw [map_mul (resAbs K S), map_mul (resAbs K S), map_inv (resAbs K S)]
  show C.conj ((@id (GKS K S) (resAbs K S h))⁻¹ * @id (GKS K S) (resAbs K S (decompMap K v σ)) *
    @id (GKS K S) (resAbs K S h)) = _
  rw [map_mul, map_mul, map_inv]
  rfl

variable (W : WeierstrassCurve K) (hW : W.map (C.κ : K →+* K) = W) (N : ℕ)
  (h : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
  (hbar : ∀ y, locConjBar C.κ hvw (decompEmb K v y) = decompEmb K w (C.τ (h.symm y)))

include hbar in
open scoped Classical in
/-- PROVED. **`Ē_*` on the images of `E(K_S)[N]`**: `Ē_*(j_v P) = j_w(ρ_T(τ)(h̄⁻¹ P))` (hypothesis
`hbar`, from `conjK_bar_of`). -/
theorem conjK_compTors (P : TorsS K S W N) :
    conjKTors (locConjCompletion C.κ hvw) (locConjBar C.κ hvw) (locConjBar_algebraMap C.κ hvw)
        (W.baseChange (v.adicCompletion K)) (W.baseChange (w.adicCompletion K))
        (conjK_baseChange_map C.κ hvw W hW) N (compTors W N v P) =
      compTors W N w (conjTors C W hW N (@id (GKS K S) (resAbs K S h⁻¹) • P)) := by
  apply Subtype.ext
  rw [coe_conjKTors, coe_compTors, coe_compTors, coe_conjTors, coe_smul_torsS]
  obtain ⟨P, hP⟩ := P
  rcases P with _ | ⟨x, y, hxy⟩
  · change conjKPt _ _ _ _ _ _ (compPt W v 0) = compPt W w (conjPt C W hW
      (Affine.Point.map (galS K S (@id (GKS K S) (resAbs K S h⁻¹))).toAlgHom 0))
    rw [map_zero, map_zero, map_zero, conjPt_zero, map_zero]
  · have p1 : ((W.baseChange (v.adicCompletion K)).baseChange
        (AlgebraicClosure (v.adicCompletion K))).toAffine.Nonsingular (embS K S v x)
          (embS K S v y) :=
      (W.toAffine.baseChange_nonsingular (embS K S v).injective x y).mpr hxy
    have ex : ∀ z : KS K S, locConjBar C.κ hvw (embS K S v z) =
        embS K S w (C.tau (galS K S (@id (GKS K S) (resAbs K S h⁻¹)) z)) := by
      intro z
      change locConjBar C.κ hvw (decompEmb K v (z : AlgebraicClosure K)) =
        decompEmb K w ((C.tau (galS K S (@id (GKS K S) (resAbs K S h⁻¹)) z) : KS K S) :
          AlgebraicClosure K)
      rw [hbar, C.coe_tau]
      exact congrArg (fun t => decompEmb K w (C.τ t)) (resAbs_apply_coe K S h⁻¹ z).symm
    calc conjKPt (locConjCompletion C.κ hvw) (locConjBar C.κ hvw) (locConjBar_algebraMap C.κ hvw)
          (W.baseChange (v.adicCompletion K)) (W.baseChange (w.adicCompletion K))
          (conjK_baseChange_map C.κ hvw W hW) (compPt W v (.some x y hxy))
        = conjKPt (locConjCompletion C.κ hvw) (locConjBar C.κ hvw) (locConjBar_algebraMap C.κ hvw)
          (W.baseChange (v.adicCompletion K)) (W.baseChange (w.adicCompletion K))
          (conjK_baseChange_map C.κ hvw W hW) (ptEquiv _ _ (.some _ _ p1)) := rfl
      _ = ptEquiv _ _ (.some _ _ (conjK_nonsingular (locConjCompletion C.κ hvw)
          (locConjBar C.κ hvw) (locConjBar_algebraMap C.κ hvw) _ _
          (conjK_baseChange_map C.κ hvw W hW) p1)) := conjKPt_some _ _ _ _ _ _ p1
      _ = compPt W w (conjPt C W hW (Affine.Point.map
          (galS K S (@id (GKS K S) (resAbs K S h⁻¹))).toAlgHom (.some x y hxy))) := by
        rw [Affine.Point.map_some, conjPt_some, compPt_some]
        congr 1
        exact some_eq_some (ex x) (ex y) _ _

end EmbCompareS

/-! ### The twist identification along the local conjugation -/

section TwistCompare

variable {F F' : Type} [Field F] [Field F'] (e : F ≃+* F')
  (Ē : AlgebraicClosure F ≃+* AlgebraicClosure F')
  (hĒ : ∀ a : F, Ē (algebraMap F (AlgebraicClosure F) a) =
    algebraMap F' (AlgebraicClosure F') (e a))
  (V : WeierstrassCurve F) (V' : WeierstrassCurve F') (hV : V.map (e : F →+* F') = V') (d : F)

include hV in
/-- PROVED. The twisted curve along `e`: `(twistK V d).map e = twistK V' d'` for `e d = d'`. -/
theorem conjK_twistK_map {d' : F'} (hd : e d = d') :
    (TwistDictionary.twistK V d).map (e : F →+* F') = TwistDictionary.twistK V' d' := by
  rw [TwistDictionary.twistK_map, hV, ← hd]
  rfl

include hĒ in
/-- PROVED. `(Ē q)² = d'` for `q² = d`, `e d = d'`. -/
theorem conjK_sq_bar {d' : F'} (hd : e d = d') {q : AlgebraicClosure F}
    (hqh : q ^ 2 = algebraMap F (AlgebraicClosure F) d) :
    Ē q ^ 2 = algebraMap F' (AlgebraicClosure F') d' := by
  rw [← map_pow, hqh, hĒ, hd]

include e in
/-- PROVED. `2 ≠ 0` transfers along `e`. -/
theorem conjK_two_ne_zero (h2 : (2 : F) ≠ 0) : (2 : F') ≠ 0 := by
  rw [← map_ofNat e 2]
  exact (map_ne_zero e).2 h2

open scoped Classical in
/-- PROVED. **The twist identification commutes with `Ē`**: `Ē_*(φ_q R) = φ_{Ē q}(Ē_* R)` (lane
RC29's `twistPt`). -/
theorem conjK_twistPt (h2 : (2 : F) ≠ 0) {d' : F'} (hd : e d = d') {q : AlgebraicClosure F}
    (hq : q ≠ 0) (hqh : q ^ 2 = algebraMap F (AlgebraicClosure F) d)
    (R : PtAlg F (TwistDictionary.twistK V d)) :
    conjKPt e Ē hĒ V V' hV (twistPt V d h2 hq hqh R) =
      twistPt V' d' (conjK_two_ne_zero e h2) ((map_ne_zero Ē).2 hq)
        (conjK_sq_bar e Ē hĒ d hd hqh)
        (conjKPt e Ē hĒ (TwistDictionary.twistK V d) (TwistDictionary.twistK V' d')
          (conjK_twistK_map e V V' hV d hd) R) := by
  obtain ⟨R, rfl⟩ := (ptEquiv F (TwistDictionary.twistK V d)).surjective R
  rcases R with _ | ⟨x, y, hxy⟩
  · rw [← Affine.Point.zero_def, map_zero, map_zero, map_zero, map_zero, map_zero]
  · rw [twistPt_some', conjKPt_some, conjKPt_some, twistPt_some']
    congr 1
    have ha₁ : Ē (algebraMap F (AlgebraicClosure F) V.a₁) =
        algebraMap F' (AlgebraicClosure F') V'.a₁ := by
      rw [hĒ, ← hV]
      rfl
    have ha₃ : Ē (algebraMap F (AlgebraicClosure F) V.a₃) =
        algebraMap F' (AlgebraicClosure F') V'.a₃ := by
      rw [hĒ, ← hV]
      rfl
    refine some_eq_some ?_ ?_ _ _
    · simp only [map_mul, map_pow, map_inv₀]
    · simp only [map_add, map_mul, map_pow, map_inv₀, map_div₀, map_neg, map_ofNat, ha₁, ha₃]

open scoped Classical in
/-- PROVED. `φ_q` depends only on `q`. -/
theorem conjK_twistPt_congr (h2 : (2 : F) ≠ 0) {q₁ q₂ : AlgebraicClosure F} (heq : q₁ = q₂)
    (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0) (hqh₁ : q₁ ^ 2 = algebraMap F (AlgebraicClosure F) d)
    (hqh₂ : q₂ ^ 2 = algebraMap F (AlgebraicClosure F) d)
    (R : PtAlg F (TwistDictionary.twistK V d)) :
    twistPt V d h2 hq₁ hqh₁ R = twistPt V d h2 hq₂ hqh₂ R := by
  subst heq
  rfl

open scoped Classical in
/-- PROVED. **`φ_{−q} = −φ_q`** (the sign of the square root). -/
theorem conjK_twistPt_neg (h2 : (2 : F) ≠ 0) {q : AlgebraicClosure F} (hq : q ≠ 0)
    (hqh : q ^ 2 = algebraMap F (AlgebraicClosure F) d) (R : PtAlg F (TwistDictionary.twistK V d)) :
    twistPt V d h2 (neg_ne_zero.2 hq) (by rw [neg_sq]; exact hqh) R = -twistPt V d h2 hq hqh R := by
  obtain ⟨R, rfl⟩ := (ptEquiv F (TwistDictionary.twistK V d)).surjective R
  rcases R with _ | ⟨x, y, hxy⟩
  · rw [← Affine.Point.zero_def, map_zero, map_zero, map_zero, neg_zero]
  · rw [twistPt_some', twistPt_some', ← map_neg (ptEquiv F V), Affine.Point.neg_some]
    congr 1
    have h2' : (2 : AlgebraicClosure F) ≠ 0 := by
      rw [← map_ofNat (algebraMap F (AlgebraicClosure F)) 2]
      exact (map_ne_zero _).2 h2
    refine some_eq_some ?_ ?_ _ _
    · simp only [inv_neg, even_two, Even.neg_pow]
    · simp only [Affine.negY, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
        WeierstrassCurve.map_a₃]
      field_simp
      ring

end TwistCompare

/-! ### The transported coefficient map against the coefficient map at `v` -/

section ActualCompare

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (C : ActualConj K S)

/-- PROVED. **The square root sign**: `τ(h⁻¹ s) = ± s` for `s² = h`, `κ h = h`. -/
theorem conjK_sqrt_sign (s : KS K S) {h : K} (hs : s ^ 2 = algebraMap K (KS K S) h)
    (hκh : C.κ h = h) (h₀ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    C.τ (h₀.symm (inclS K S s)) = inclS K S s ∨ C.τ (h₀.symm (inclS K S s)) = -inclS K S s := by
  have hs' : (inclS K S s) ^ 2 = algebraMap K (AlgebraicClosure K) h := by
    rw [← map_pow, hs, AlgHom.commutes]
  have hsq : (C.τ (h₀.symm (inclS K S s))) ^ 2 = (inclS K S s) ^ 2 := by
    rw [← map_pow C.τ, ← map_pow h₀.symm, hs', AlgEquiv.commutes, C.hτ, hκh]
  exact sq_eq_sq_iff_eq_or_eq_neg.1 hsq

variable (W : WeierstrassCurve K) (hW : W.map (C.κ : K →+* K) = W) (s : KS K S) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (hκh : C.κ h = h)
  {v w : HeightOneSpectrum (𝓞 K)}
  (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K))
  (h₀ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
  (hbar : ∀ y, locConjBar C.κ hvw (decompEmb K v y) = decompEmb K w (C.τ (h₀.symm y)))

include hs hκh hbar in
/-- PROVED (tex 2812–2813, the square-root sign). **`Ē(j_v(s)) = ± j_{τv}(s)`**: the local square
roots at `v` and `τv` correspond up to the sign `±1`. -/
theorem conjK_localSqrt_sign :
    locConjBar C.κ hvw (localSqrt s v) = localSqrt s w ∨
      locConjBar C.κ hvw (localSqrt s v) = -localSqrt s w := by
  have e1 : locConjBar C.κ hvw (localSqrt s v) =
      decompEmb K w (C.τ (h₀.symm (inclS K S s))) := hbar (inclS K S s)
  rcases conjK_sqrt_sign C s hs hκh h₀ with h1 | h1
  · left
    rw [e1, h1]
    rfl
  · right
    rw [e1, h1, map_neg]
    rfl

include hbar in
open scoped Classical in
/-- PROVED. `φ_{q_w}(Ē_* t) = ε Ē_*(φ_{q_v} t)` with `ε = ±1` from `conjK_localSqrt_sign`. -/
theorem conjK_twistTors_sign (m : ℕ) :
    ∃ ε : ℤˣ, ∀ t : TorsAlg (v.adicCompletion K) (localTwist W h v) m,
      twistTors (W.baseChange (w.adicCompletion K)) (algebraMap K (w.adicCompletion K) h)
          two_ne_zero (localSqrt_ne_zero s hs0 w) (localSqrt_sq s hs w) m
          (conjKTors (locConjCompletion C.κ hvw) (locConjBar C.κ hvw)
            (locConjBar_algebraMap C.κ hvw) (localTwist W h v) (localTwist W h w)
            (conjK_localTwist_map C.κ hvw W hW hκh) m t) =
        (ε : ℤ) • conjKTors (locConjCompletion C.κ hvw) (locConjBar C.κ hvw)
          (locConjBar_algebraMap C.κ hvw) (W.baseChange (v.adicCompletion K))
          (W.baseChange (w.adicCompletion K)) (conjK_baseChange_map C.κ hvw W hW) m
          (twistTors (W.baseChange (v.adicCompletion K)) (algebraMap K (v.adicCompletion K) h)
            two_ne_zero (localSqrt_ne_zero s hs0 v) (localSqrt_sq s hs v) m t) := by
  have hd : locConjCompletion C.κ hvw (algebraMap K (v.adicCompletion K) h) =
      algebraMap K (w.adicCompletion K) h := by
    rw [locConjCompletion_algebraMap, hκh]
  have key := conjK_twistPt (locConjCompletion C.κ hvw) (locConjBar C.κ hvw)
    (locConjBar_algebraMap C.κ hvw) (W.baseChange (v.adicCompletion K))
    (W.baseChange (w.adicCompletion K)) (conjK_baseChange_map C.κ hvw W hW)
    (algebraMap K (v.adicCompletion K) h) two_ne_zero hd (localSqrt_ne_zero s hs0 v)
    (localSqrt_sq s hs v)
  rcases conjK_localSqrt_sign C s hs hκh hvw h₀ hbar with hsg | hsg
  · refine ⟨1, fun t => ?_⟩
    apply Subtype.ext
    rw [Units.val_one, one_smul, coe_twistTors, coe_conjKTors, coe_conjKTors, coe_twistTors, key]
    exact conjK_twistPt_congr _ _ _ hsg.symm _ _ _ _ _
  · refine ⟨-1, fun t => ?_⟩
    apply Subtype.ext
    rw [Units.val_neg, Units.val_one, neg_smul, one_smul, AddSubgroup.coe_neg, coe_twistTors,
      coe_conjKTors, coe_conjKTors, coe_twistTors, key]
    have hsg' : localSqrt s w = -locConjBar C.κ hvw (localSqrt s v) := by
      rw [hsg, neg_neg]
    have hq' : -locConjBar C.κ hvw (localSqrt s v) ≠ 0 :=
      neg_ne_zero.2 ((map_ne_zero _).2 (localSqrt_ne_zero s hs0 v))
    have hqh' : (-locConjBar C.κ hvw (localSqrt s v)) ^ 2 =
        algebraMap (w.adicCompletion K) (AlgebraicClosure (w.adicCompletion K))
          (algebraMap K (w.adicCompletion K) h) := by
      rw [neg_sq]
      exact conjK_sq_bar (locConjCompletion C.κ hvw) (locConjBar C.κ hvw)
        (locConjBar_algebraMap C.κ hvw) (algebraMap K (v.adicCompletion K) h) hd
        (localSqrt_sq s hs v)
    rw [conjK_twistPt_congr _ _ _ hsg' _ hq' _ hqh', conjK_twistPt_neg]

include hbar in
open scoped Classical in
/-- PROVED. `j_w⁻¹ φ_{q_w}(Ē_* t) = ε ρ_T(τ)(h̄⁻¹ j_v⁻¹ φ_{q_v}(t))`. -/
theorem conjK_compTorsEquiv_sign (m : ℕ) [W.IsElliptic] [NeZero m]
    (hFull : FullTorsion K S W m) :
    ∃ ε : ℤˣ, ∀ t : TorsAlg (v.adicCompletion K) (localTwist W h v) m,
      (compTorsEquiv W m hFull w).symm
          (twistTors (W.baseChange (w.adicCompletion K)) (algebraMap K (w.adicCompletion K) h)
            two_ne_zero (localSqrt_ne_zero s hs0 w) (localSqrt_sq s hs w) m
            (conjKTors (locConjCompletion C.κ hvw) (locConjBar C.κ hvw)
              (locConjBar_algebraMap C.κ hvw) (localTwist W h v) (localTwist W h w)
              (conjK_localTwist_map C.κ hvw W hW hκh) m t)) =
        (ε : ℤ) • conjTors C W hW m (@id (GKS K S) (resAbs K S h₀⁻¹) •
          (compTorsEquiv W m hFull v).symm
            (twistTors (W.baseChange (v.adicCompletion K)) (algebraMap K (v.adicCompletion K) h)
              two_ne_zero (localSqrt_ne_zero s hs0 v) (localSqrt_sq s hs v) m t)) := by
  obtain ⟨ε, hε⟩ := conjK_twistTors_sign C W hW s hs hs0 hκh hvw h₀ hbar m
  refine ⟨ε, fun t => ?_⟩
  apply (compTorsEquiv W m hFull w).injective
  rw [AddEquiv.apply_symm_apply, map_zsmul, compTorsEquiv_apply,
    ← conjK_compTors C hvw W hW m h₀ hbar, ← compTorsEquiv_apply W m hFull v,
    AddEquiv.apply_symm_apply, hε]

end ActualCompare

section ActualCompareS

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (C : ActualConj K S) (W : WeierstrassCurve K) [W.IsElliptic]
  (hW : W.map (C.κ : K →+* K) = W) (i : ℕ) (s : KS K S) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (hκh : C.κ h = h)
  (α : GKS K S →* (Acoef i)ˣ) (hFull : FullTorsion K S W (2 ^ i)) {v w : Places K S}
  (hvw : w.1.asIdeal = v.1.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K))

/-- PROVED (tex 2812–2813). **The transported coefficient map against `ι_v`**: for the comparison
element `h̄` of lane RC29's `decompEmb` at `v`, `τv`, the inner element `g = c(h̄)⁻¹` satisfies
`hg`, and for a sign `ε = ±1` (the square-root sign), `ι^τ(t) = α(h̄)⁻¹ · ε · (id ⊗ ρ_T(τ))(ι_v(t))`
in `A_i ⊗ E(K_S)[2^i]`. Hypothesis `hαc : α(c σ) = α(σ)⁻¹` (ELLIOT tex 2786–2795, PROVED by RC28 for
the actual `α_i`). -/
theorem conjKActualIota_eq (hαc : ∀ σ, α (C.conj σ) = (α σ)⁻¹) :
    ∃ (hb : GKS K S) (ε : ℤˣ),
      (∀ σ : Gloc K v.1, locMap K S w.1 (locConjGal C.κ hvw σ) =
        (C.conj hb)⁻¹ * C.conj (locMap K S v.1 σ) * (C.conj hb)⁻¹⁻¹) ∧
      ∀ t : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i),
        (show Acoef i ⊗[ℤ] TorsS K S W ((2 ^ i : ℕ) : ℤ) from
          conjKActualIota C W hW i s hs hs0 hκh α hFull (C.conj hb)⁻¹ hvw t) =
        (((α hb)⁻¹ : (Acoef i)ˣ) : Acoef i) • ((ε : ℤ) • conjBC C W hW (Acoef i)
          (show Acoef i ⊗[ℤ] TorsS K S W ((2 ^ i : ℕ) : ℤ) from
            kummerIota W i s hs hs0 α hFull v.1 t)) := by
  obtain ⟨h₀, hh⟩ := conjK_exists_comp_of C.κ C.τ C.hτ hvw (decompEmb K v.1) (decompEmb K w.1)
  have hd := conjK_decompMap_of C.κ C.τ C.hτ hvw (decompEmb K v.1) (decompEmb K w.1)
    (fun σ y => decompEmb_decompMap K v.1 σ y) (fun σ y => decompEmb_decompMap K w.1 σ y) h₀ hh
  have hbar := conjK_bar_of C.κ C.τ hvw (decompEmb K v.1) (decompEmb K w.1) h₀ hh
  obtain ⟨ε, hε⟩ := conjK_compTorsEquiv_sign C W hW s hs hs0 hκh hvw h₀ hbar (2 ^ i) hFull
  refine ⟨@id (GKS K S) (resAbs K S h₀), ε, conjK_locMap_of_decompMap C hvw h₀ hd, fun t => ?_⟩
  have hinv : @id (GKS K S) (resAbs K S h₀⁻¹) = (@id (GKS K S) (resAbs K S h₀))⁻¹ :=
    map_inv (resAbs K S) h₀
  set P := (compTorsEquiv W (2 ^ i) hFull v.1).symm
    (twistTors (W.baseChange (v.1.adicCompletion K)) (algebraMap K (v.1.adicCompletion K) h)
      two_ne_zero (localSqrt_ne_zero s hs0 v.1) (localSqrt_sq s hs v.1) (2 ^ i) t) with hP
  have e1 : (show Acoef i ⊗[ℤ] TorsS K S W ((2 ^ i : ℕ) : ℤ) from
      kummerIota W i s hs hs0 α hFull v.1 t) = (1 : Acoef i) ⊗ₜ P := rfl
  have e2 : (show Acoef i ⊗[ℤ] TorsS K S W ((2 ^ i : ℕ) : ℤ) from
      conjKActualIota C W hW i s hs hs0 hκh α hFull (C.conj (@id (GKS K S) (resAbs K S h₀)))⁻¹
        hvw t) =
      (show Acoef i ⊗[ℤ] TorsS K S W ((2 ^ i : ℕ) : ℤ) from
        ((C.conj (@id (GKS K S) (resAbs K S h₀)))⁻¹)⁻¹ •
          oneTmul (Acoef i) α (TorsS K S W ((2 ^ i : ℕ) : ℤ))
            ((ε : ℤ) • conjTors C W hW ((2 ^ i : ℕ) : ℤ)
              (@id (GKS K S) (resAbs K S h₀⁻¹) • P))) := by
    rw [← hε t]
    rfl
  have e3 : ((C.conj (@id (GKS K S) (resAbs K S h₀)))⁻¹)⁻¹ •
      oneTmul (Acoef i) α (TorsS K S W ((2 ^ i : ℕ) : ℤ))
        ((ε : ℤ) • conjTors C W hW ((2 ^ i : ℕ) : ℤ) (@id (GKS K S) (resAbs K S h₀⁻¹) • P)) =
      CoefMod.equiv (Acoef i) α (TorsS K S W ((2 ^ i : ℕ) : ℤ))
        ((ε : ℤ) • (((((α (@id (GKS K S) (resAbs K S h₀)))⁻¹ : (Acoef i)ˣ) : Acoef i) * 1) ⊗ₜ
          conjTors C W hW ((2 ^ i : ℕ) : ℤ) P)) := by
    rw [inv_inv, map_zsmul, smul_comm, oneTmul_apply, CoefMod.smul_tmul, hαc, ← conjTors_smul,
      hinv, smul_inv_smul, map_zsmul]
  rw [e2, e3, e1, conjBC_tmul, mul_one]
  change (ε : ℤ) • ((((α (@id (GKS K S) (resAbs K S h₀)))⁻¹ : (Acoef i)ˣ) : Acoef i) ⊗ₜ[ℤ]
      conjTors C W hW ((2 ^ i : ℕ) : ℤ) P) =
    (((α (@id (GKS K S) (resAbs K S h₀)))⁻¹ : (Acoef i)ˣ) : Acoef i) •
      ((ε : ℤ) • ((1 : Acoef i) ⊗ₜ[ℤ] conjTors C W hW ((2 ^ i : ℕ) : ℤ) P))
  rw [smul_comm (((α (@id (GKS K S) (resAbs K S h₀)))⁻¹ : (Acoef i)ˣ) : Acoef i) (ε : ℤ),
    TensorProduct.smul_tmul' (((α (@id (GKS K S) (resAbs K S h₀)))⁻¹ : (Acoef i)ˣ) : Acoef i)
      (1 : Acoef i), smul_eq_mul, mul_one]

end ActualCompareS

/-! ### Kummer conditions under a change of coefficients -/

section CoefKummer

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {k : Type} [CommRing k] {M M' : Type} [AddCommGroup M] [Module k M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
  [DiscreteTopology M] [ContinuousAdd M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup M'] [Module k M']
  [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) k M'] [TopologicalSpace M']
  [DiscreteTopology M'] [ContinuousAdd M'] [ContinuousSMul (GKS K S) M']
  (ψ : M ≃ₗ[k] M') (hψ : ∀ (σ : GKS K S) (m : M), ψ (σ • m) = σ • ψ m) {v : Places K S}

/-- DEF. An isomorphism of conditions induces one of the conditions pushed along a coefficient
isomorphism (`conjTransportCoef`). -/
def ConjKCondIso.coef {c c' : CondAt K S k M v} (I : ConjKCondIso c c') :
    ConjKCondIso (conjTransportCoef ψ hψ c) (conjTransportCoef ψ hψ c') where
  hom := I.hom
  inv := I.inv
  inv_hom := I.inv_hom
  hom_inv := I.hom_inv
  comm n x := congrArg (fun y => (natHom (conjTransportCoefIso ψ hψ v.1).hom).f n n rfl y)
    (I.comm n x)

/-- PROVED. `B.map id = B`. -/
theorem conjK_map_refl {F : Type} [Field F] (B : WeierstrassCurve F) :
    B.map ((RingEquiv.refl F : F ≃+* F) : F →+* F) = B :=
  B.map_id

/-- PROVED. The identity extends the identity. -/
theorem conjK_refl_algebraMap {F : Type} [Field F] (a : F) :
    (RingEquiv.refl (AlgebraicClosure F)) (algebraMap F (AlgebraicClosure F) a) =
      algebraMap F (AlgebraicClosure F) ((RingEquiv.refl F) a) :=
  rfl

open scoped Classical in
/-- PROVED. `Ē_* = id` for `Ē = id`. -/
theorem conjKTors_refl {F : Type} [Field F] (B : WeierstrassCurve F) (m : ℕ)
    (t : TorsAlg F B m) :
    conjKTors (RingEquiv.refl F) (RingEquiv.refl (AlgebraicClosure F)) conjK_refl_algebraMap B B
      (conjK_map_refl B) m t = t := by
  apply Subtype.ext
  change conjKPt (RingEquiv.refl F) (RingEquiv.refl (AlgebraicClosure F)) conjK_refl_algebraMap B
    B (conjK_map_refl B) (t : PtAlg F B) = (t : PtAlg F B)
  obtain ⟨R, hR⟩ := (ptEquiv F B).surjective (t : PtAlg F B)
  rw [← hR]
  rcases R with _ | ⟨x, y, hxy⟩
  · rw [← Affine.Point.zero_def, map_zero, map_zero]
  · rw [conjKPt_some]
    congr 1

variable (B : WeierstrassCurve (v.1.adicCompletion K)) (m : ℕ)
  (ι : TorsAlg (v.1.adicCompletion K) B m →+ ResMod (locMap K S v.1) M)

omit [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
  [DiscreteTopology M] [ContinuousAdd M] [ContinuousSMul (GKS K S) M]
  [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) k M'] [TopologicalSpace M']
  [DiscreteTopology M'] [ContinuousAdd M'] [ContinuousSMul (GKS K S) M'] in
open scoped Classical in
/-- PROVED. For the identity conjugation, `conjKIota` is `ψ ∘ ι`. -/
theorem conjKIota_refl :
    conjKIota (RingEquiv.refl (v.1.adicCompletion K))
        (RingEquiv.refl (AlgebraicClosure (v.1.adicCompletion K))) conjK_refl_algebraMap B B
        (conjK_map_refl B) m (conjTransportCoefEquiv (S := S) ψ v.1) ι =
      ((conjTransportCoefEquiv (S := S) ψ v.1).toLinearMap.toAddMonoidHom.comp ι) := by
  ext t
  rw [conjKIota_apply, conjKTors_refl]
  rfl

variable (hι : ∀ (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) B m), ι (σ • t) = σ • ι t)

omit [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M] [ContinuousAdd M]
  [ContinuousSMul (GKS K S) M] [SMulCommClass (GKS K S) k M'] [TopologicalSpace M']
  [DiscreteTopology M'] [ContinuousAdd M'] [ContinuousSMul (GKS K S) M'] in
include hψ hι in
/-- PROVED. `ψ ∘ ι` is equivariant for an equivariant `ψ` (`hψ`) and equivariant `ι` (`hι`). -/
theorem conjKCoefIota_smul (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) B m) :
    ((conjTransportCoefEquiv (S := S) ψ v.1).toLinearMap.toAddMonoidHom.comp ι) (σ • t) =
      σ • ((conjTransportCoefEquiv (S := S) ψ v.1).toLinearMap.toAddMonoidHom.comp ι) t := by
  change ψ (ι (σ • t)) = _
  rw [hι]
  exact hψ (locMap K S v.1 σ) (ι t)

variable [DecidableEq (v.1.adicCompletion K)] [B.IsElliptic] [NeZero m]

open scoped Classical in
/-- PROVED. **A Kummer condition pushed along an equivariant coefficient isomorphism `ψ` is
isomorphic to the Kummer condition of `ψ ∘ ι`** (the case `φ = id` of `conjK_kummerZ_map`). -/
def conjKCoefKummerIso :
    ConjKCondIso (conjTransportCoef ψ hψ (kummerAt (k := k) v B m ι hι))
      (kummerAt (k := k) v B m
        ((conjTransportCoefEquiv (S := S) ψ v.1).toLinearMap.toAddMonoidHom.comp ι)
          (conjKCoefIota_smul ψ hψ B m ι hι)) where
  hom := conjKCondHom (conjTransportCoefIso ψ hψ v.1) (kummerZ' k ι) (kummerZ'_cocycle k ι hι)
    _ (kummerZ'_cocycle k _ (conjKCoefIota_smul ψ hψ B m ι hι)) (fun x hx => by
      have := conjK_kummerZ_map (RingEquiv.refl (v.1.adicCompletion K))
        (RingEquiv.refl (AlgebraicClosure (v.1.adicCompletion K))) conjK_refl_algebraMap B B
        (conjK_map_refl B) m (conjTransportCoefEquiv (S := S) ψ v.1) ι (ContinuousMulEquiv.refl _)
        (fun _ _ => rfl) (fun σ n => hψ (locMap K S v.1 σ) n) hι x hx
      rwa [conjKIota_refl] at this)
  inv := conjKCondHom (conjTransportCoefIso ψ hψ v.1).symm _
    (kummerZ'_cocycle k _ (conjKCoefIota_smul ψ hψ B m ι hι)) (kummerZ' k ι)
    (kummerZ'_cocycle k ι hι) (fun x hx => by
      rw [← conjKIota_refl ψ B m ι] at hx
      exact conjK_kummerZ_map_inv (RingEquiv.refl (v.1.adicCompletion K))
        (RingEquiv.refl (AlgebraicClosure (v.1.adicCompletion K))) conjK_refl_algebraMap B B
        (conjK_map_refl B) m (conjTransportCoefEquiv (S := S) ψ v.1) ι (ContinuousMulEquiv.refl _)
        (fun _ _ => rfl) (fun σ n => hψ (locMap K S v.1 σ) n) hι x hx)
  inv_hom := conjKCondHom_inv_hom _ _ _ _ _ _ _
  hom_inv := conjKCondHom_hom_inv _ _ _ _ _ _ _
  comm := conjKCondHom_comm _ _ _ _ _ _

end CoefKummer

/-! ### The transported dual Kummer condition on `M_i^*(1)` -/

section ActualDual

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (C : ActualConj K S) (W : WeierstrassCurve K) [W.IsElliptic]
  (hW : W.map (C.κ : K →+* K) = W) (i : ℕ) (s : KS K S) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (hκh : C.κ h = h)
  (α : GKS K S →* (Acoef i)ˣ) [IsOpenKer α] (hFull : FullTorsion K S W (2 ^ i))
  (hμ : HasRootsOfUnity K S (2 ^ i)) [ContinuousSMul (GKS K S) (DualM W hμ (Acoef i) α)]
  (hα : ∀ σ, α (C.conj σ) = (α σ)⁻¹)
  (g : GKS K S) {v w : Places K S}
  (hvw : w.1.asIdeal = v.1.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K))
  (hg : ∀ σ : Gloc K v.1,
    locMap K S w.1 (locConjGal C.κ hvw σ) = g * C.conj (locMap K S v.1 σ) * g⁻¹)
  (hαw : IsLocallyQuadAt i α (quadChar s hs hs0) w.1)

/-- DEF (tex 2810–2813). **The dual transported coefficient map** into `M_i^*(1)`: `conjDualEquiv ∘
ι^τ` (lane RC28's `τ^*M_i ≃ M_i^*(1)`). -/
def conjKActualDualIota :
    TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i) →+
      ResMod (locMap K S v.1) (DualM W hμ (Acoef i) α) :=
  (conjTransportCoefEquiv (S := S) (conjDualEquiv C W hW hμ (Acoef i) α hFull)
    v.1).toLinearMap.toAddMonoidHom.comp (conjKActualIota C W hW i s hs hs0 hκh α hFull g hvw)

omit [IsOpenKer α] [ContinuousSMul (GKS K S) (DualM W hμ (Acoef i) α)] in
include hα hg hαw in
/-- PROVED. The dual transported coefficient map is `G_{K_v}`-equivariant (hypothesis `hα`). -/
theorem conjKActualDualIota_smul (σ : Gloc K v.1)
    (t : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i)) :
    conjKActualDualIota C W hW i s hs hs0 hκh α hFull hμ g hvw (σ • t) =
      σ • conjKActualDualIota C W hW i s hs hs0 hκh α hFull hμ g hvw t :=
  conjKCoefIota_smul (conjDualEquiv C W hW hμ (Acoef i) α hFull)
    (conjDualEquiv_smul C W hW hμ (Acoef i) α hFull hα) (localTwist W h v.1) (2 ^ i)
    (conjKActualIota C W hW i s hs hs0 hκh α hFull g hvw)
    (conjKActualIota_smul C W hW i s hs hs0 hκh α hFull g hvw hg hαw) σ t

open scoped Classical in
/-- DEF. **The Kummer condition at `v` with coefficients `M_i^*(1)`** through `conjKActualDualIota`.
-/
def conjKActualDualKummerAt : CondAt K S (Acoef i) (DualM W hμ (Acoef i) α) v :=
  haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  kummerAt v (localTwist W h v.1) (2 ^ i)
    (conjKActualDualIota C W hW i s hs hs0 hκh α hFull hμ g hvw)
    (conjKActualDualIota_smul C W hW i s hs hs0 hκh α hFull hμ hα g hvw hg hαw)

open scoped Classical in
/-- PROVED (tex 2810–2813). **The dual condition `conjTransportDual` of the actual Kummer condition
at `τv` is isomorphic, compatibly with the cochain isomorphisms, to the Kummer condition of `B_v` at
`v` with coefficients in `M_i^*(1)` through `conjKActualDualIota`.** DEPARTURE D4 of
`ConjTransport.lean`: that this is the orthogonal complement `U_v^⊥` is not proved. -/
def conjKActualDualIso :
    ConjKCondIso (conjTransportDual C W hW hμ (Acoef i) α hFull hα g hvw hg
        (actualKummerAt W i s hs hs0 α hFull w hαw))
      (conjKActualDualKummerAt C W hW i s hs hs0 hκh α hFull hμ hα g hvw hg hαw) :=
  haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  ((conjKActualIso C W hW i s hs hs0 hκh α hFull g hvw hg hαw).coef
    (conjDualEquiv C W hW hμ (Acoef i) α hFull)
    (conjDualEquiv_smul C W hW hμ (Acoef i) α hFull hα)).trans
    (conjKCoefKummerIso (conjDualEquiv C W hW hμ (Acoef i) α hFull)
      (conjDualEquiv_smul C W hW hμ (Acoef i) α hFull hα) (localTwist W h v.1) (2 ^ i)
      (conjKActualIota C W hW i s hs hs0 hκh α hFull g hvw)
      (conjKActualIota_smul C W hW i s hs hs0 hκh α hFull g hvw hg hαw))

/-- PROVED. `conjKActualDualKummerAt` is a subcomplex. -/
theorem conjKActualDual_isInjective :
    (conjKActualDualKummerAt C W hW i s hs hs0 hκh α hFull hμ hα g hvw hg hαw).IsInjective :=
  (conjKActualDualIso C W hW i s hs hs0 hκh α hFull hμ hα g hvw hg hαw).isInjective
    (conjTransportDual_isInjective C W hW hμ (Acoef i) α hFull hα g hvw hg _
      (actualKummerAt_isInjective W i s hs hs0 α hFull w hαw))

open scoped Classical in
/-- PROVED. **The `H¹` image of the transported dual Kummer condition is the `A_i`-span of the
Kummer image of `B_v(K_v)` through `conjKActualDualIota`.** -/
theorem conjKActualDual_range_H1 :
    haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
    LinearMap.range (HomologicalComplex.homologyMap (GHom.toCC (conjTransportDual C W hW hμ
      (Acoef i) α hFull hα g hvw hg (actualKummerAt W i s hs hs0 α hFull w hαw)).i) 1).hom =
      Submodule.span (Acoef i) (Set.range (kummerMapIn (Acoef i)
        (conjKActualDualIota C W hW i s hs hs0 hκh α hFull hμ g hvw)
        (conjKActualDualIota_smul C W hW i s hs hs0 hκh α hFull hμ hα g hvw hg hαw))) := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  exact ((conjKActualDualIso C W hW i s hs hs0 hκh α hFull hμ hα g hvw hg hαw).range_homology
    1).trans (range_homologyMap_kummerConditionIn (Acoef i) _ _)

omit [IsOpenKer α] [ContinuousSMul (GKS K S) (DualM W hμ (Acoef i) α)] in
include hα in
/-- PROVED. **The dual coefficient map through the Weil pairing**: for the inner element of
`conjKActualIota_eq`, `conjKActualDualIota(t) = α(h̄)⁻¹ ε · e(·, ι_v(t))` (`e = weilPairingM`,
`ι_v(t)` read in `M_i(α⁻¹)`): the transported dual Kummer condition is the Kummer condition of `B_v`
mapped into `M_i^*(1)` by the Weil pairing against `ι_v`, up to the unit `α(h̄)⁻¹ ε`. -/
theorem conjKActualDualIota_eq :
    ∃ (hb : GKS K S) (ε : ℤˣ),
      (∀ σ : Gloc K v.1, locMap K S w.1 (locConjGal C.κ hvw σ) =
        (C.conj hb)⁻¹ * C.conj (locMap K S v.1 σ) * (C.conj hb)⁻¹⁻¹) ∧
      ∀ (t : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i))
        (x : CoefMod (Acoef i) α (TorsS K S W ((2 ^ i : ℕ) : ℤ))),
        (show CoefMod (Acoef i) α (TorsS K S W ((2 ^ i : ℕ) : ℤ)) →ₗ[Acoef i]
            Tate1 (Acoef i) hμ from
          conjKActualDualIota C W hW i s hs hs0 hκh α hFull hμ (C.conj hb)⁻¹ hvw t) x =
        (((α hb)⁻¹ : (Acoef i)ˣ) : Acoef i) • ((ε : ℤ) • weilPairingM W hμ (Acoef i) α x
          (show CoefMod (Acoef i) (charInv α) (TorsS K S W ((2 ^ i : ℕ) : ℤ)) from
            kummerIota W i s hs hs0 α hFull v.1 t)) := by
  obtain ⟨hb, ε, hg, h⟩ := conjKActualIota_eq C W hW i s hs hs0 hκh α hFull hvw hα
  refine ⟨hb, ε, hg, fun t x => ?_⟩
  change weilPairingM W hμ (Acoef i) α x (conjBC C W hW (Acoef i)
    (show Acoef i ⊗[ℤ] TorsS K S W ((2 ^ i : ℕ) : ℤ) from
      conjKActualIota C W hW i s hs hs0 hκh α hFull (C.conj hb)⁻¹ hvw t)) = _
  rw [h t, map_smul, map_zsmul, conjBC_conjBC]
  have e1 := (weilPairingM W hμ (Acoef i) α x).map_smul (((α hb)⁻¹ : (Acoef i)ˣ) : Acoef i)
    ((ε : ℤ) • (show CoefMod (Acoef i) (charInv α) (TorsS K S W ((2 ^ i : ℕ) : ℤ)) from
      kummerIota W i s hs hs0 α hFull v.1 t))
  rw [map_zsmul] at e1
  exact e1

end ActualDual

end ZInQ.Manuscript.RC.KummerMaps
