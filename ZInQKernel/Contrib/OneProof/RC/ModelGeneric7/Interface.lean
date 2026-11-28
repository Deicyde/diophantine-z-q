import ZInQKernel.Contrib.OneProof.RC.ModelGeneric6.CharFreeSeamTwo
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric6.Cyclicity
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric5.Extension
import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.Y0LevelPoints
import ZInQKernel.Contrib.OneProof.RC.GoodRowWire.SamePlace

/-! **The INTERFACE block of the special-fibre Atkin–Lehner lane** (rc-model-generic7, piece (a)).

`atkinLevelAlg` is the integral Atkin–Lehner ring map `ModelGeneric5.atkinLevel` (the restriction
of the rational `atkinRat` to the pinned level algebra) as a `LocalIntegers ell`-algebra map, from
`ModelGeneric5.atkinLevel_algebraMap`. `PointW` is the `point_W` field of
`GoodRowWire.SamePlaceData` (`RC/GoodRowWire/SamePlace.lean`) as a named Prop of a point map; it
is not proved here. Both declarations are placed exactly as written in the INTERFACE block; the
theorem `atkinLevel_moduli_special` of that block belongs to rc-model-generic8.

Outside the block: `Wint_left` (the underlying scheme map of `ModelGeneric5.Wint` is `Spec` of
the ring map of `atkinLevelAlg`, under the instance `ModelGeneric5.levelCommRing` that `Wint` is
built with), and `smulSubgroup_cyclic` (the subgroup `C_Q = (N/Q) • C` of a cyclic `C` of order
`N = Q * (N/Q)` is cyclic of order `Q`; the hypothesis `hH` of `ModelGeneric6.exists_quotientSeam`
at `H = C_Q`). -/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Manuscript.RC.ModelGeneric7

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.ModelTorsion
  WeierstrassCurve.ModelLevels
open scoped TauCeti.ExactDivisor

/-- `ModelGeneric5.atkinLevel` as a `LocalIntegers ell`-algebra map. -/
def atkinLevelAlg {ell N : ℕ} [Fact ell.Prime] [NeZero N] (h₅ : 5 ≤ ell)
    (htame : ¬ ell ∣ N * N.totient) (h₂ : 2 ≤ N) {Q : ℕ} (hQ : Q ∥ N) :
    Pinned.Y0LevelAlgebra h₅ htame h₂ →ₐ[LocalIntegers ell] Pinned.Y0LevelAlgebra h₅ htame h₂ :=
  { ModelGeneric5.atkinLevel h₅ htame h₂ hQ with
    commutes' := ModelGeneric5.atkinLevel_algebraMap h₅ htame h₂ hQ }

open AlgebraicGeometry CategoryTheory in
/-- **The `point_W` field of `GoodRowWire.SamePlaceData`, as a named Prop of a point map.** The
same-place lane assembles `SamePlaceData` with this Prop as a hypothesis, and the point_W
assembly proves it for the same-place lane's point map. -/
def PointW {ell N : ℕ} [Fact ell.Prime] [NeZero N] (h₅ : 5 ≤ ell)
    (htame : ¬ ell ∣ N * N.totient) (h₂ : 2 ≤ N) {K : Type} [Field K] [Algebra (ZMod ell) K]
    {X : PMAdelic.CoarseFibre}
    (point : X.Point → (PMQuotient.residueSource ell K ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (ModelNeron.closed ell)))).obj
        (Pinned.Y0Level h₅ htame h₂))) : Prop :=
  ∀ (q : ℕ) (_hq : q.Prime) (_he : 0 < N.factorization q) (x : X.Point),
    point (X.W q x) = point x ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (ModelNeron.closed ell)))).map
        (ModelGeneric5.Wint h₅ htame h₂ (TauCeti.Nat.isExactDivisor_primePow (N := N) (p := q)))

end ZInQ.Manuscript.RC.ModelGeneric7

namespace ZInQ.Manuscript.RC.ModelGeneric7

open AlgebraicGeometry CategoryTheory WeierstrassCurve.ModelTorsion WeierstrassCurve.ModelLevels
open scoped TauCeti.ExactDivisor

section WintLemma

attribute [local instance 2000] ModelGeneric5.levelCommRing

/-- **`Wint` is `Spec` of the ring map of `atkinLevelAlg`.** Stated under
`ModelGeneric5.levelCommRing`, the `CommRing` instance on `Pinned.Y0LevelAlgebra` that `Wint` is
built with (`RC/ModelGeneric5/Extension.lean`). `ModelGeneric5.Wint` is `Over.homMk` of
`Spec.map (CommRingCat.ofHom (atkinLevel hQ))`, and the ring map of `atkinLevelAlg` is
`atkinLevel` by definition. -/
theorem Wint_left {ell N : ℕ} [Fact ell.Prime] [NeZero N] (h₅ : 5 ≤ ell)
    (htame : ¬ ell ∣ N * N.totient) (h₂ : 2 ≤ N) {Q : ℕ} (hQ : Q ∥ N) :
    (ModelGeneric5.Wint h₅ htame h₂ hQ).left =
      Spec.map (CommRingCat.ofHom (atkinLevelAlg h₅ htame h₂ hQ : _ →+* _)) :=
  rfl

/-- The ring map of `atkinLevelAlg` is `ModelGeneric5.atkinLevel`. -/
theorem atkinLevelAlg_toRingHom {ell N : ℕ} [Fact ell.Prime] [NeZero N] (h₅ : 5 ≤ ell)
    (htame : ¬ ell ∣ N * N.totient) (h₂ : 2 ≤ N) {Q : ℕ} (hQ : Q ∥ N) :
    (atkinLevelAlg h₅ htame h₂ hQ : _ →+* _) = ModelGeneric5.atkinLevel h₅ htame h₂ hQ :=
  rfl

end WintLemma

section Cyclic

variable {A : Type*} [AddCommGroup A]

/-- **`C_Q = M • C` is cyclic of order `Q`.** For a cyclic subgroup `C` of order `N = Q * M`
with `M ≠ 0`, the subgroup `ModelGeneric6.smulSubgroup M C` (the image of `C` under
multiplication by `M`) is cyclic of order `Q`. This is the hypothesis `hH` of
`ModelGeneric6.exists_quotientSeam` at `H = C_Q`. -/
theorem smulSubgroup_cyclic {Q M N : ℕ} (hN : N = Q * M) (hM0 : M ≠ 0)
    (C : AddSubgroup A) (hC : IsAddCyclic C ∧ Nat.card C = N) :
    IsAddCyclic (ModelGeneric6.smulSubgroup M C) ∧
      Nat.card (ModelGeneric6.smulSubgroup M C) = Q := by
  haveI := hC.1
  obtain ⟨⟨c, hcC⟩, hc⟩ := IsAddCyclic.exists_generator (α := C)
  have hCc : C = AddSubgroup.zmultiples c := by
    ext y
    constructor
    · intro hy
      obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (hc ⟨y, hy⟩)
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, congrArg Subtype.val hn⟩
    · intro hy
      obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
      exact C.zsmul_mem hcC n
  have hoc : addOrderOf c = N := by
    rw [← hC.2, hCc, Nat.card_zmultiples]
  have hmap : ModelGeneric6.smulSubgroup M C = AddSubgroup.zmultiples (M • c) := by
    rw [ModelGeneric6.smulSubgroup, hCc, AddMonoidHom.map_zmultiples]
    rfl
  rw [hmap]
  refine ⟨inferInstance, ?_⟩
  rw [Nat.card_zmultiples, addOrderOf_nsmul' (x := c) hM0, hoc, hN,
    Nat.gcd_mul_left_left, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hM0)]

/-- `smulSubgroup_cyclic` at `M = N / Q` for `Q ∣ N`, `N ≠ 0`: the form used with
`C : CyclicSubgroups _ N` and an exact divisor `Q ∥ N`. -/
theorem smulSubgroup_div_cyclic {Q N : ℕ} (hQ : Q ∣ N) (hN0 : N ≠ 0)
    (C : AddSubgroup A) (hC : IsAddCyclic C ∧ Nat.card C = N) :
    IsAddCyclic (ModelGeneric6.smulSubgroup (N / Q) C) ∧
      Nat.card (ModelGeneric6.smulSubgroup (N / Q) C) = Q :=
  smulSubgroup_cyclic (Nat.mul_div_cancel' hQ).symm
    (Nat.div_ne_zero_iff_of_dvd hQ |>.mpr ⟨hN0, fun h => hN0 (by subst h; simpa using hQ)⟩) C hC

end Cyclic

end ZInQ.Manuscript.RC.ModelGeneric7

#print axioms ZInQ.Manuscript.RC.ModelGeneric7.atkinLevelAlg
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.PointW
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.Wint_left
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.atkinLevelAlg_toRingHom
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.smulSubgroup_cyclic
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.smulSubgroup_div_cyclic
