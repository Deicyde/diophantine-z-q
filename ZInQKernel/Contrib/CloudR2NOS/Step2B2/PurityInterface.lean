/-
H5 lane3 Step 2, B2.d sub-obligation (d.2) `PurityTranslateEquality`: EXACT consumer Prop, frozen
for its producer C5 (lead decision 04:45Z). 2026-11-17. New file. SOURCE-ONLY, UNCOMPILED; it
states a Prop only. Universe u.

Consumer: lane3's B2.d case assembly (case `B_k` with `m` in case `A`). There, `φ` is the
reflection `a ↦ 2c₀ − a` (inversion followed by a translation) or a translation; both are scheme
automorphisms of `A`.

Truth sketch (lead 04:45Z; C6 to audit):
* Locally `D = (f)` with `f` a nonzerodivisor. By Krull's Hauptidealsatz, every minimal prime over
  `(f)` has height exactly 1, so every irreducible component of `supp D` has codimension 1.
* An automorphism `φ` preserves codimension, so `φ⁻¹ E` is a codimension-1 component of
  `supp(D.comap φ)`.
* If `φ⁻¹ E ⊊ F` with both irreducible and closed, prepending `φ⁻¹ E` to a chain from `F` gives
  `codim (φ⁻¹ E) ≥ codim F + 1 = 2`, a contradiction. No catenarity is needed.
* Hence `φ⁻¹ E = F`.
-/
import Step2DelegatedInterfaces

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.Step2B2

/-- (d.2), TRUE (Krull PIT purity). The automorphic image of one support component that lies in
another support component equals it. -/
def PurityTranslateEquality : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (D : A.X.left.IdealSheafData), D.IsInvertible →
    ∀ (φ : A.X.left ⟶ A.X.left) [IsIso φ] (E F : Set A.X.left),
      Maximal (fun Z : Set A.X.left => Z ⊆ (D.support : Set A.X.left) ∧ IsIrreducible Z) E →
      Maximal (fun Z : Set A.X.left => Z ⊆ (D.support : Set A.X.left) ∧ IsIrreducible Z) F →
      φ ⁻¹' E ⊆ F → φ ⁻¹' E = F

end ZInQ.Contrib.CloudR2NOS.Step2B2
