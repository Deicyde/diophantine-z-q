/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.Dictionary.InterfaceD9D10

/-!
# D8: transport of the ORIGINAL kernel fibre datum along an actual QML3 isomorphism

Original W01/Metamate proof with agentcloud assistance, 2026-11-15.
Ownership agreed with W13 before writing. No Root/Interfaces/provider/D0-D7/
D9-D10 source is changed. This helper proves actual geometry/data transport,
not H119 or a desired model Fact. Original family maps and both original
abelian varieties/group/action/level-point structures remain literal.
-/

noncomputable section
namespace ZInQ.Contrib.CloudB2Shimura.Dictionary.D8
open CategoryTheory AlgebraicGeometry Limits
open LeafQM.AV

/-- The source-side scheme isomorphism Q → P of an ORIGINAL I : P.Iso Q.
Its map is literally I.ψ.hom.left, not an independently chosen model map. -/
def inverseSchemeIso {K : Type} [Field K] {P Q : QML3 K} (I : QML3.Iso P Q) :
    Q.A.X.left ≅ P.A.X.left where
  hom := I.ψ.hom.left
  inv := I.φ.hom.left
  hom_inv_id := congrArg (fun f => f.left) I.right
  inv_hom_id := congrArg (fun f => f.left) I.left

@[simp] theorem inverseSchemeIso_hom {K : Type} [Field K] {P Q : QML3 K}
    (I : QML3.Iso P Q) : (inverseSchemeIso I).hom = I.ψ.hom.left := rfl

/-- Preserve the FULL ORIGINAL IsFibreOf proposition. For I:P→Q and a fibre map
P→family, the returned map is Q→P→family through I.ψ. Both action and ALL level
points are transported, not only the underlying cartesian square. -/
theorem isFibreOf_of_iso {S : Scheme.{0}} (𝒜 : QMFamily S) {K : Type} [Field K]
    {y : Spec (CommRingCat.of K) ⟶ S} {P Q : QML3 K}
    (I : QML3.Iso P Q) (hP : IsFibreOf 𝒜 y P) : IsFibreOf 𝒜 y Q := by
  obtain ⟨g, hpb, hiota, heta⟩ := hP
  let j := inverseSchemeIso I
  refine ⟨I.ψ.hom.left ≫ g, ?_, ?_, ?_⟩
  · apply hpb.of_iso' j (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp only [j, inverseSchemeIso, Iso.refl_hom, Category.comp_id]
    · simpa only [j, inverseSchemeIso, Iso.refl_hom, Category.comp_id] using Over.w I.ψ.hom
    · simp
    · simp
  · intro a
    have hc := congrArg (fun f => f.left) (I.symm.equivariant a)
    change (Q.q.iota a).hom.left ≫ I.ψ.hom.left =
      I.ψ.hom.left ≫ (P.q.iota a).hom.left at hc
    rw [← Category.assoc, hc, Category.assoc, hiota a, ← Category.assoc]
  · intro a
    have hc := congrArg (fun x => (Additive.toMul x).left) (I.symm.level a)
    change (Additive.toMul (Q.e.eta a)).left ≫ I.ψ.hom.left =
      (Additive.toMul (P.e.eta a)).left at hc
    rw [← Category.assoc, hc, heta a]

/-- Fibre data depend on the ORIGINAL M3 isomorphism class, by actual quotient
soundness/exactness and the geometric/data transport above, not a class-label map. -/
theorem isFibreOf_of_class_eq {S : Scheme.{0}} (𝒜 : QMFamily S) {K : Type} [Field K]
    {y : Spec (CommRingCat.of K) ⟶ S} {P Q : QML3 K}
    (hPQ : M3.mk P = M3.mk Q) (hP : IsFibreOf 𝒜 y P) : IsFibreOf 𝒜 y Q := by
  obtain ⟨I⟩ := Quotient.exact hPQ
  exact isFibreOf_of_iso 𝒜 I hP

/-- Both orientations of fibre transport, using the same actual isomorphism. -/
theorem isFibreOf_iso_iff {S : Scheme.{0}} (𝒜 : QMFamily S) {K : Type} [Field K]
    {y : Spec (CommRingCat.of K) ⟶ S} {P Q : QML3 K} (I : QML3.Iso P Q) :
    IsFibreOf 𝒜 y P ↔ IsFibreOf 𝒜 y Q :=
  ⟨isFibreOf_of_iso 𝒜 I, isFibreOf_of_iso 𝒜 I.symm⟩

#print axioms isFibreOf_of_iso
#print axioms isFibreOf_of_class_eq

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D8
