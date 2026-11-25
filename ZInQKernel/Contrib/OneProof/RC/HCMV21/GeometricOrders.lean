import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.OneProof.RC.Eichler.Order

/-! The geometric objects used before any class-set comparison. The
torsion-form level-one maximal endomorphism order statement here is a
proposition with no asserted provider; it is derived from the printed
Theorem 42.1.9 candidate and a GLUE bridge in `HCMV21/DeuringRankFour.lean`. -/

noncomputable section

namespace ZInQ.Manuscript.RC.HCMV21

open CategoryTheory CartesianMonoidalCategory
open PkgI3.AbVar
open scoped CategoryTheory.MonObj

universe u

variable {k : Type u} [Field k]

/-- Endomorphisms of an enhanced elliptic curve are the endomorphisms of
the underlying group scheme that preserve the specified geometric level
subgroup. The level is prime to the characteristic in the application,
so the subgroup can be specified by its geometric points. -/
def levelEnd (A : PkgI3.AbVar k) (C : Subgroup (A.Pt k)) : Subring A.End where
  carrier := {f | ∀ P ∈ C, P ≫ f.hom ∈ C}
  one_mem' := fun P hP => by simpa [show (1 : A.End).hom = 𝟙 _ from rfl]
  mul_mem' {f g} hf hg P hP := by
    change P ≫ (g.hom ≫ f.hom) ∈ C
    rw [← Category.assoc]
    exact hf _ (hg P hP)
  zero_mem' := fun P _ => by
    rw [Hom.hom_zero, MonObj.comp_one]
    exact C.one_mem
  add_mem' {f g} hf hg P hP := by
    rw [Hom.hom_add, MonObj.comp_mul]
    exact C.mul_mem (hf P hP) (hg P hP)
  neg_mem' {f} hf P hP := by
    change P ≫ f.hom⁻¹ ∈ C
    rw [GrpObj.comp_inv]
    exact C.inv_mem (hf P hP)

/-- Integral homomorphisms between two enhanced curves. This is the
additive lattice whose completion is used in the Deuring comparison. -/
def levelHom {L : Type u} [Field L] [Algebra k L] {A B : PkgI3.AbVar k}
    (C : Subgroup (A.Pt L)) (D : Subgroup (B.Pt L)) : AddSubgroup (Hom A B) where
  carrier := {f | ∀ P ∈ C, P ≫ f.hom ∈ D}
  zero_mem' := fun P _ => by
    rw [Hom.hom_zero, MonObj.comp_one]
    exact D.one_mem
  add_mem' {f g} hf hg P hP := by
    rw [Hom.hom_add, MonObj.comp_mul]
    exact D.mul_mem (hf P hP) (hg P hP)
  neg_mem' {f} hf P hP := by
    change P ≫ f.hom⁻¹ ∈ D
    rw [GrpObj.comp_inv]
    exact D.inv_mem (hf P hP)

/-- The level condition cuts out a subring whose additive quotient is
killed by the level integer. In particular imposing level does not
change the completion at a prime outside the level. -/
theorem nsmul_mem_levelEnd (A : PkgI3.AbVar k) (C : Subgroup (A.Pt k))
    (N : ℕ) (hC : ∀ P ∈ C, P ^ N = 1) (f : A.End) :
    N • f ∈ levelEnd A C := by
  intro P hP
  change P ≫ (f.hom ^ N) ∈ C
  rw [MonObj.comp_pow, ← MonObj.pow_comp, hC P hP, MonObj.one_comp]
  exact C.one_mem

/-- The actual geometric level subring and full endomorphism ring have
the same span in any integral realization where the level is invertible,
in particular in the detector completion. -/
theorem span_levelEnd_eq_span_end {S M : Type*} [CommRing S]
    [AddCommGroup M] [Module S M] (A : PkgI3.AbVar k) (C : Subgroup (A.Pt k))
    (N : ℕ) (hC : ∀ P ∈ C, P ^ N = 1) (hN : IsUnit (N : S)) (φ : A.End →+ M) :
    Submodule.span S (φ '' (levelEnd A C : Set A.End)) =
      Submodule.span S (Set.range φ) := by
  apply le_antisymm
  · apply Submodule.span_mono
    rintro _ ⟨f, _, rfl⟩
    exact ⟨f, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨f, rfl⟩
    have hmem : φ (N • f) ∈ Submodule.span S (φ '' (levelEnd A C : Set A.End)) :=
      Submodule.subset_span ⟨_, nsmul_mem_levelEnd A C N hC f, rfl⟩
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul S] at hmem
    have hinv : (↑hN.unit⁻¹ : S) * (N : S) = 1 :=
      (congrArg ((↑hN.unit⁻¹ : S) * ·) hN.unit_spec.symm).trans (Units.inv_mul hN.unit)
    change φ f ∈ Submodule.span S (φ '' (levelEnd A C : Set A.End))
    simpa only [smul_smul, hinv, one_smul] using
      (Submodule.span S (φ '' (levelEnd A C : Set A.End))).smul_mem (↑hN.unit⁻¹ : S) hmem

/-- The geometric kernel of a map on the chosen algebraically closed
field, before reading the quotient in ideal-class coordinates. -/
def geometricKernel {L : Type u} [Field L] [Algebra k L]
    {A B : PkgI3.AbVar k} (f : Hom A B) : Subgroup (A.Pt L) :=
  (ptMap f).ker

/-- The integral left ideal of endomorphisms killing a subgroup of the
source. Postcomposition preserves the vanishing condition. -/
def kernelAnnihilator {L : Type u} [Field L] [Algebra k L]
    (A : PkgI3.AbVar k) (H : Subgroup (A.Pt L)) : Ideal A.End where
  carrier := {f | ∀ P ∈ H, P ≫ f.hom = 1}
  zero_mem' := fun P _ => by rw [Hom.hom_zero, MonObj.comp_one]
  add_mem' {f g} hf hg P hP := by
    rw [Hom.hom_add, MonObj.comp_mul, hf P hP, hg P hP, one_mul]
  smul_mem' g f hf P hP := by
    change P ≫ (f.hom ≫ g.hom) = 1
    rw [← Category.assoc, hf P hP, MonObj.one_comp]

/-- Precomposition by an actual curve map. Its image consists of the
endomorphisms that admit a geometric factorization through that map. -/
def precomposeCurveMap {A B : PkgI3.AbVar k} (f : Hom A B) : Hom B A →+ A.End where
  toFun g := Hom.mk' (f.hom ≫ g.hom)
  map_zero' := Hom.ext' (by rw [Hom.hom_mk', Hom.hom_zero, MonObj.comp_one, Hom.hom_zero])
  map_add' g g' := Hom.ext' (by
    simp only [Hom.hom_mk', Hom.hom_add, MonObj.comp_mul])

/-- The easy direction of the geometric ideal dictionary: any factorization
kills the kernel. The reverse needs descent through the scheme quotient;
point-module factorization alone cannot supply it. -/
theorem range_precomposeCurveMap_le_annihilator {L : Type u} [Field L] [Algebra k L]
    {A B : PkgI3.AbVar k} (f : Hom A B) :
    Set.range (precomposeCurveMap f) ⊆
      (kernelAnnihilator A (geometricKernel (L := L) f) : Set A.End) := by
  rintro _ ⟨g, rfl⟩ P hP
  have h : P ≫ f.hom = 1 := hP
  change P ≫ (f.hom ≫ g.hom) = 1
  rw [← Category.assoc, h, MonObj.one_comp]

/-- For a prime-to-characteristic quotient the label of the level is
carried by the image of the actual subgroup. An intertwining pair of
endomorphisms carries preservation of the source level to preservation
of the target level, even before any Tate lattice is chosen. -/
theorem levelEnd_map_of_intertwines {A B : PkgI3.AbVar k} (u : Hom A B)
    (C : Subgroup (A.Pt k)) {f : A.End} {g : B.End}
    (h : f.hom ≫ u.hom = u.hom ≫ g.hom) (hf : f ∈ levelEnd A C) :
    g ∈ levelEnd B (C.map (ptMap u)) := by
  rintro _ ⟨P, hP, rfl⟩
  refine ⟨P ≫ f.hom, hf P hP, ?_⟩
  change (P ≫ f.hom) ≫ u.hom = (P ≫ u.hom) ≫ g.hom
  simp only [Category.assoc, h]

/-- **Torsion-form Deuring statement; no longer the printed candidate.**
The endomorphism ring of a one-dimensional abelian variety over an
algebraically closed field of characteristic `q` with no nonidentity
geometric `q`-torsion is a maximal order in a quaternion algebra ramified
exactly at `q` and `∞`. Its hypothesis is Voight's Prop. 42.1.7(ii),
`E[p](F^al) = {0}`, not the rank hypothesis of Theorem 42.1.9. The printed
candidate is `VoightThm4219` (Voight, *Quaternion Algebras*, GTM 288,
Theorem 42.1.9, p. 784), and `deuringSupersingularEndOrder_of_rankFour`
derives this statement from it and the GLUE bridge
`SupersingularTorsionRankFour` (both in
`ZInQKernel/Contrib/OneProof/RC/HCMV21/DeuringRankFour.lean`). -/
def DeuringSupersingularEndOrder : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k q]
    (A : PkgI3.AbVar k), A.dim = 1 → (∀ P : A.Pt k, P ^ q = 1 → P = 1) →
    ∃ a b : ℚ, AppF.RamifiedExactlyAtEll0Infty q a b ∧
      ∃ R : Eichler.Order a b, Nonempty (A.End ≃+* R.ring) ∧
        ∀ S : Eichler.Order a b, R.ring ≤ S.ring → S.ring ≤ R.ring

end ZInQ.Manuscript.RC.HCMV21
