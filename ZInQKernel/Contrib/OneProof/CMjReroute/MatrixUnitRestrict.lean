import ZInQKernel.Contrib.OneProof.CMFibreSplit.Curve
import ZInQKernel.Contrib.OneProof.CMjReroute.Restrict

/-!
# Central endomorphisms of `A` act on the matrix-unit curve `E`

`FibreSplit.matrixUnit_isogeny` produces, from `n`-scaled matrix units `f i j` of `End(A)` (an abelian
surface over a number field `L`), the curve `E` = image of `f 0 0`, with a closed immersion
`i : E → A` and `h : A → E`, `h ≫ i = f 0 0`, `i ≫ h = [n]`. Here:

* `h` is surjective, because `i ≫ h = [n]` is;
* every central endomorphism `r` of `A` restricts to `E` (`exists_restrict`), and the restriction
  `ρ : Z(End A) → End E` is an injective ring homomorphism (`eq_zero_of_mul_unit_eq_zero`, `End A`
  having no additive torsion);
* composing with the base change `End E → End E_{L̄}` (injective) and with an isomorphism
  `End E_{L̄} ≅ R` (`IsCMBy E k R`), every subring of the centre of `End(A)` becomes a subring of `R`,
  isomorphic to it (`exists_le_of_center`).
-/

noncomputable section

namespace HDec.CMBranch.CMjReroute

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open HDec.CMBranch.FibreSplit
open HSyn.G0Split

variable {L : Type} [Field L] [NumberField L]

/-- `End(A)` has no additive torsion: `[n]` is surjective, hence an epimorphism. -/
theorem end_eq_zero_of_natCast_mul (A : PkgI3.AbVar L) {n : ℕ} (hn : 0 < n)
    {x : PkgI3.AbVar.End A} (h : (n : PkgI3.AbVar.End A) * x = 0) : x = 0 := by
  have hs := (_root_.ZInQ.Contrib.AbVarBC.mulIsogeny L A ((n : ℕ) : ℤ)
    (by exact_mod_cast hn.ne')).2
  apply cancel_surj (((n : ℕ) : ℤ) : PkgI3.AbVar.End A) hs
  rw [cmp_intCast_left, cmp_zero_right, zsmul_eq_mul, Int.cast_natCast, h]

/-- **The matrix-unit curve with the restriction of central endomorphisms.** -/
theorem matrixUnit_restrict (A : PkgI3.AbVar L) (hA : A.dim = 2) (n : ℕ) (hn : 0 < n)
    (f : Fin 2 → Fin 2 → PkgI3.AbVar.End A) (hf : IsScaledMatrixUnits n f) :
    ∃ (E : PkgI3.AbVar L) (i : PkgI3.AbVar.Hom E A) (h : PkgI3.AbVar.Hom A E)
      (Pr : ZInQ.DefFaltings.AbVar L)
      (ρ : Subring.center (PkgI3.AbVar.End A) →+* PkgI3.AbVar.End E),
      Function.Injective ρ ∧ (∀ r, cmp (ρ r) i = cmp i (r : PkgI3.AbVar.End A)) ∧
      cmp h i = f 0 0 ∧ cmp i h = (n : PkgI3.AbVar.End E) ∧ IsClosedImmersion i.hom.left ∧
      E.dim = 1 ∧ Pr.dim = (2 : ℕ) ∧ IsProductOf Pr.X E.X E.X ∧
      ∃ φ : Pr.X ⟶ A.X, ZInQ.DefFaltings.IsIsogeny (A := Pr) (B := A) φ := by
  obtain ⟨E, i, h, Pr, hF, hih, hci, hE1, hPr, hprod, φ, hφ⟩ := matrixUnit_isogeny L A hA n hn f hf
  -- `h` is surjective
  have hsn := (_root_.ZInQ.Contrib.AbVarBC.mulIsogeny L E ((n : ℕ) : ℤ)
    (by exact_mod_cast hn.ne')).2
  rw [Int.cast_natCast, ← hih, cmp_hom, Over.comp_left] at hsn
  have hs : Surjective h.hom.left := Surjective.of_comp i.hom.left h.hom.left
  -- the centre lies in the centralizer of `e = f 0 0`
  have hcen : Subring.center (PkgI3.AbVar.End A) ≤
      Subring.centralizer ({imgEnd i h} : Set (PkgI3.AbVar.End A)) := by
    intro x hx
    rw [Subring.mem_centralizer_iff]
    rintro _ rfl
    exact (Subring.mem_center_iff.mp hx _)
  let ρ : Subring.center (PkgI3.AbVar.End A) →+* PkgI3.AbVar.End E :=
    (restrictHom i h hci hs).comp (Subring.inclusion hcen)
  have hρ : ∀ r : Subring.center (PkgI3.AbVar.End A),
      (ρ r).hom ≫ i.hom = i.hom ≫ (r : PkgI3.AbVar.End A).hom := fun r =>
    restrictHom_spec i h hci hs (Subring.inclusion hcen r)
  refine ⟨E, i, h, Pr, ρ, ?_, fun r => PkgI3.AbVar.Hom.ext' (hρ r), hF, hih, hci, hE1, hPr, hprod,
    φ, hφ⟩
  rw [injective_iff_map_eq_zero]
  intro r hr0
  -- `i ≫ r = 0`, so `r f₀₀ = 0`
  have h1 : i.hom ≫ (r : PkgI3.AbVar.End A).hom = 1 := by
    rw [← hρ r, hr0, PkgI3.AbVar.Hom.hom_zero, MonObj.one_comp]
  have h0 : (r : PkgI3.AbVar.End A) * f 0 0 = 0 := by
    apply PkgI3.AbVar.Hom.ext'
    rw [← hF]
    show (h.hom ≫ i.hom) ≫ (r : PkgI3.AbVar.End A).hom = 1
    rw [Category.assoc, h1, MonObj.comp_one]
  obtain ⟨hrel, hsum⟩ := hf
  have hz := eq_zero_of_mul_unit_eq_zero n (fun x hx => end_eq_zero_of_natCast_mul A hn hx) f
    hrel hsum (r : PkgI3.AbVar.End A) (fun x => Subring.mem_center_iff.mp r.2 x) h0
  exact Subtype.ext hz

omit [NumberField L] in
/-- **Subrings of the centre of `End(A)` inside the CM order of `E`.** If moreover
`End(E_{L̄}) ≅ R ⊆ k`, every subring `Z'` of the centre of `End(A)` is isomorphic to a subring
`R₀ ≤ R`. -/
theorem exists_le_of_center (A : PkgI3.AbVar L) {E : PkgI3.AbVar L}
    (ρ : Subring.center (PkgI3.AbVar.End A) →+* PkgI3.AbVar.End E) (hρ : Function.Injective ρ)
    {k : Type} [Field k] (R : Subring k)
    (e : PkgI3.AbVar.End (E.baseChange (AlgebraicClosure L)) ≃+* R)
    (Z' : Subring (PkgI3.AbVar.End A)) (hZ' : Z' ≤ Subring.center (PkgI3.AbVar.End A)) :
    ∃ R₀ : Subring k, R₀ ≤ R ∧ Nonempty (Z' ≃+* R₀) := by
  let bc := G0ModField.KernelField.endBC E (AlgebraicClosure L)
  have hbc : Function.Injective bc := G0ModField.KernelField.endBC_injective E (AlgebraicClosure L)
  let χ : Z' →+* k :=
    R.subtype.comp (e.toRingHom.comp ((bc : PkgI3.AbVar.End E →+* _).comp
      (ρ.comp (Subring.inclusion hZ'))))
  have hχ : Function.Injective χ := by
    intro a b hab
    have h1 : e (bc (ρ (Subring.inclusion hZ' a))) = e (bc (ρ (Subring.inclusion hZ' b))) :=
      Subtype.ext (by simpa [χ] using hab)
    exact Subring.inclusion_injective hZ' (hρ (hbc (e.injective h1)))
  refine ⟨χ.range, ?_, ⟨RingEquiv.ofBijective χ.rangeRestrict
    ⟨fun a b h => hχ (by simpa using congrArg Subtype.val h), χ.rangeRestrict_surjective⟩⟩⟩
  rintro _ ⟨z, rfl⟩
  exact (e (bc (ρ (Subring.inclusion hZ' z)))).2

end HDec.CMBranch.CMjReroute
