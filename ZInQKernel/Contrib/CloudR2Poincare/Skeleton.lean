import ZInQKernel.Contrib.AVB1.Poincare

/-!
# H-72 (`ZInQ.Contrib.AVB1.PoincareComplement`): the lead's decomposition into three obligations

Round 2, lead session c96b9ca0 (task cloud-r2-h72), 2026-11-14. Fixed statement:
`ZInQ.Contrib.AVB1.PoincareComplement` (`ZInQKernel/Contrib/AVB1/Poincare.lean` line 42 at fork `main`
`cba8157f7d5d09a4a3c8462aba2f3245494a870e`, unchanged at the round-2 base `df98652a`).

This file states the three obligations into which the lead splits the proof. It also proves the
**glue** `poincareComplement_of_obligations`, which derives `PoincareComplement` from them. The
obligations themselves are **not** assumed anywhere as facts. The final theorem
`PoincareComplement_proof` will exist only once each obligation is proved (`…_proof` theorems).

Mathematical plan (Mumford, *Abelian varieties*, §19 Thm 1; Milne 1986 Prop. 12.1):
* `PolarizationRetract`: for `i : B ↪ J` there is a homomorphism `φ : J → D` with `φ ∘ i : B → D`
  an isogeny and `dim D ≤ dim B`. With the dual abelian variety one takes `D = B^∨` and
  `φ = i^∨ ∘ φ_L` for `L` ample on `J`: `φ ∘ i = φ_{i^*L}` is an isogeny because `K(i^*L)` is finite.
  This is the only place where the dual abelian variety / polarizations enter.
* `KernelComplement`: for `φ : J → D` the reduced identity component `Z = (ker φ)⁰_red` is an
  abelian subvariety, `g : Z ↪ J`, `φ ∘ g = 0`, `dim J ≤ dim Z + dim D`.
* `ComplementIsogeny`: then `B × Z → J`, `(b, z) ↦ b + z`, is finite and surjective. Its kernel lies
  in `ker(φ ∘ i) × g⁻¹(i(ker(φ ∘ i)))`, which is finite, and its dimension count is
  `dim B + dim Z ≥ dim D + dim Z ≥ dim J`.

The `1` below is the neutral element of the group of morphisms into a group object
(`toUnit _ ≫ η`), i.e. the zero homomorphism.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare

/-- **Obligation P (lanes L1, L2, L5).** A homomorphism out of `J` that restricts to an isogeny on
the abelian subvariety `B`, with target of dimension at most `dim B`. True by Mumford §§6, 8, 19
(`D = B^∨`, `φ = i^∨ ∘ φ_L`). -/
def PolarizationRetract : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (J B : _root_.PkgI3.AbVar k)
    (i : _root_.PkgI3.AbVar.Hom B J), IsClosedImmersion i.hom.left →
    ∃ (D : _root_.PkgI3.AbVar k) (φ : _root_.PkgI3.AbVar.Hom J D),
      _root_.PkgI3.AbVar.IsIsogenyMor (i.hom ≫ φ.hom) ∧ D.dim ≤ B.dim

/-- **Obligation K (lane L3).** The reduced identity component of the kernel of a homomorphism
`φ : J → D` is an abelian subvariety `g : Z ↪ J` killed by `φ`, with `dim J ≤ dim Z + dim D`
(Cartier's theorem in characteristic `0`, identity components, dimension of fibres). -/
def KernelComplement : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (J D : _root_.PkgI3.AbVar k)
    (φ : _root_.PkgI3.AbVar.Hom J D),
    ∃ (Z : _root_.PkgI3.AbVar k) (g : _root_.PkgI3.AbVar.Hom Z J),
      g.hom ≫ φ.hom = 1 ∧ IsClosedImmersion g.hom.left ∧ J.dim ≤ Z.dim + D.dim

/-- **Obligation C (lane L4).** With `i`, `g` closed immersions, `φ ∘ g = 0`, `φ ∘ i` an isogeny and
the dimension inequalities, the sum map `B × Z → J` is finite and surjective. -/
def ComplementIsogeny : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (J B Z D : _root_.PkgI3.AbVar k)
    (i : _root_.PkgI3.AbVar.Hom B J) (g : _root_.PkgI3.AbVar.Hom Z J)
    (φ : _root_.PkgI3.AbVar.Hom J D),
    IsClosedImmersion i.hom.left → IsClosedImmersion g.hom.left → g.hom ≫ φ.hom = 1 →
    _root_.PkgI3.AbVar.IsIsogenyMor (i.hom ≫ φ.hom) → J.dim ≤ Z.dim + D.dim → D.dim ≤ B.dim →
    _root_.PkgI3.AbVar.IsIsogenyMor (fst B.X Z.X ≫ i.hom * snd B.X Z.X ≫ g.hom)

/-- **The glue:** the three obligations give `PoincareComplement`. -/
theorem poincareComplement_of_obligations (hP : PolarizationRetract) (hK : KernelComplement)
    (hC : ComplementIsogeny) : ZInQ.Contrib.AVB1.PoincareComplement := by
  intro k _ _ J B i hi
  obtain ⟨D, φ, hφ, hD⟩ := hP k J B i hi
  obtain ⟨Z, g, hg, hgi, hdim⟩ := hK k J D φ
  exact ⟨Z, g, hC k J B Z D i g φ hi hgi hg hφ hdim hD⟩

end ZInQ.Contrib.CloudR2Poincare
