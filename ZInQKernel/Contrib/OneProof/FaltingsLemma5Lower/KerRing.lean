import ZInQKernel.Contrib.OneProof.FaltingsLemma5Lower.Ker

/-! faltings5-lower, part 12: points of the kernel of a finite homomorphism `φ : X → Y` of group schemes over
a field `K`, with values in an arbitrary `K`-algebra `Λ` (given by `s : K → Λ`), are the `K`-algebra maps out of
`R = Γ(ker φ)` (`ringOf`, `ptOf`), naturally in `Λ`. -/

set_option linter.style.haveILetI false

namespace GapHeight

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings

section KerRing

variable {K : Type} [Field K] {X Y : Over (Spec (CommRingCat.of K))} [MonObj X] [MonObj Y]

/-- `Spec Λ` over `K` through `s : K → Λ`. -/
noncomputable def pt' {Λ : CommRingCat.{0}} (s : CommRingCat.of K ⟶ Λ) : Over (Spec (CommRingCat.of K)) :=
  Over.mk (Spec.map s)

/-- `Spec σ` over `K`. -/
noncomputable def sh' {Λ Λ' : CommRingCat.{0}} {s : CommRingCat.of K ⟶ Λ} {s' : CommRingCat.of K ⟶ Λ'}
    (σ : Λ ⟶ Λ') (h : s ≫ σ = s') : pt' s' ⟶ pt' s :=
  Over.homMk (Spec.map σ) (by
    show Spec.map σ ≫ Spec.map s = Spec.map s'
    rw [← Spec.map_comp, h])

theorem sh'_comp {Λ Λ' Λ'' : CommRingCat.{0}} {s : CommRingCat.of K ⟶ Λ}
    {s' : CommRingCat.of K ⟶ Λ'} {s'' : CommRingCat.of K ⟶ Λ''} (σ : Λ ⟶ Λ') (σ' : Λ' ⟶ Λ'')
    (h : s ≫ σ = s') (h' : s' ≫ σ' = s'') :
    sh' σ' h' ≫ sh' σ h = sh' (σ ≫ σ') (by rw [← Category.assoc, h, h']) := by
  apply Over.OverMorphism.ext
  show Spec.map σ' ≫ Spec.map σ = Spec.map (σ ≫ σ')
  rw [Spec.map_comp]

theorem sh'_id {Λ : CommRingCat.{0}} {s : CommRingCat.of K ⟶ Λ} :
    sh' (𝟙 Λ) (Category.comp_id s) = 𝟙 (pt' s) := by
  apply Over.OverMorphism.ext
  show Spec.map (𝟙 Λ) = 𝟙 _
  rw [Spec.map_id]

theorem one_left'' {Λ : CommRingCat.{0}} (s : CommRingCat.of K ⟶ Λ) :
    (1 : pt' s ⟶ Y).left = Spec.map s ≫ e0 Y := by
  rw [Hom.one_def, Over.comp_left]
  rfl

/-- The underlying morphism of a point, with source `Spec Λ`. -/
noncomputable def pL {Λ : CommRingCat.{0}} {s : CommRingCat.of K ⟶ Λ} (P : pt' s ⟶ X) :
    Spec Λ ⟶ X.left := P.left

theorem pL_sh' {Λ Λ' : CommRingCat.{0}} {s : CommRingCat.of K ⟶ Λ} {s' : CommRingCat.of K ⟶ Λ'}
    (σ : Λ ⟶ Λ') (h : s ≫ σ = s') (P : pt' s ⟶ X) : pL (sh' σ h ≫ P) = Spec.map σ ≫ pL P := rfl

variable (φ : X ⟶ Y) [IsFinite φ.left]

theorem ker_cond {Λ : CommRingCat.{0}} {s : CommRingCat.of K ⟶ Λ} (P : pt' s ⟶ X)
    (hP : P ≫ φ = 1) : pL P ≫ φ.left = Spec.map s ≫ e0 Y := by
  have h := congrArg Over.Hom.left hP
  rw [Over.comp_left, one_left''] at h
  exact h

/-- The point of the kernel scheme. -/
noncomputable def kgOf {Λ : CommRingCat.{0}} {s : CommRingCat.of K ⟶ Λ} (P : pt' s ⟶ X)
    (hP : P ≫ φ = 1) : Spec Λ ⟶ kerSch φ :=
  pullback.lift (pL P) (Spec.map s) (ker_cond φ P hP)

/-- **The ring map of a kernel point.** -/
noncomputable def ringOf {Λ : CommRingCat.{0}} {s : CommRingCat.of K ⟶ Λ} (P : pt' s ⟶ X)
    (hP : P ≫ φ = 1) : Γ(kerSch φ, ⊤) ⟶ Λ :=
  Spec.preimage (kgOf φ P hP ≫ (kerSch φ).isoSpec.hom)

theorem specMap_ringOf {Λ : CommRingCat.{0}} {s : CommRingCat.of K ⟶ Λ} (P : pt' s ⟶ X)
    (hP : P ≫ φ = 1) :
    Spec.map (ringOf φ P hP) ≫ (kerSch φ).isoSpec.inv = kgOf φ P hP := by
  rw [ringOf, Spec.map_preimage, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- `Spec R → ker φ → Spec K` is `Spec` of `K → R`. -/
theorem isoSpec_inv_snd :
    (kerSch φ).isoSpec.inv ≫ pullback.snd φ.left (e0 Y) = Spec.map (kerAlg φ) := by
  rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, kerAlg, Spec.map_comp]

theorem ringOf_cond {Λ : CommRingCat.{0}} {s : CommRingCat.of K ⟶ Λ} (P : pt' s ⟶ X)
    (hP : P ≫ φ = 1) : kerAlg φ ≫ ringOf φ P hP = s := by
  apply Spec.map_injective
  rw [Spec.map_comp, ← isoSpec_inv_snd, ← Category.assoc, specMap_ringOf, kgOf]
  exact pullback.lift_snd _ _ _

/-- **The kernel point of a ring map.** -/
noncomputable def ptOf {Λ : CommRingCat.{0}} {s : CommRingCat.of K ⟶ Λ} (ρ : Γ(kerSch φ, ⊤) ⟶ Λ)
    (hρ : kerAlg φ ≫ ρ = s) : pt' s ⟶ X :=
  Over.homMk (Spec.map ρ ≫ (kerSch φ).isoSpec.inv ≫ pullback.fst φ.left (e0 Y)) (by
    show (Spec.map ρ ≫ (kerSch φ).isoSpec.inv ≫ pullback.fst φ.left (e0 Y)) ≫ X.hom = Spec.map s
    rw [← Over.w φ]
    simp only [Category.assoc]
    rw [pullback.condition_assoc, e0_hom, Category.comp_id, isoSpec_inv_snd, ← Spec.map_comp, hρ])

theorem ptOf_left {Λ : CommRingCat.{0}} {s : CommRingCat.of K ⟶ Λ} (ρ : Γ(kerSch φ, ⊤) ⟶ Λ)
    (hρ : kerAlg φ ≫ ρ = s) :
    pL (ptOf φ ρ hρ) = Spec.map ρ ≫ (kerSch φ).isoSpec.inv ≫ pullback.fst φ.left (e0 Y) := rfl

theorem ptOf_ker {Λ : CommRingCat.{0}} {s : CommRingCat.of K ⟶ Λ} (ρ : Γ(kerSch φ, ⊤) ⟶ Λ)
    (hρ : kerAlg φ ≫ ρ = s) : ptOf φ ρ hρ ≫ φ = 1 := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, one_left'']
  show pL (ptOf φ ρ hρ) ≫ φ.left = Spec.map s ≫ e0 Y
  rw [ptOf_left]
  simp only [Category.assoc]
  rw [pullback.condition, ← Category.assoc ((kerSch φ).isoSpec.inv), isoSpec_inv_snd,
    ← Category.assoc, ← Spec.map_comp, hρ]

theorem ptOf_ringOf {Λ : CommRingCat.{0}} {s : CommRingCat.of K ⟶ Λ} (P : pt' s ⟶ X)
    (hP : P ≫ φ = 1) : ptOf φ (ringOf φ P hP) (ringOf_cond φ P hP) = P := by
  apply Over.OverMorphism.ext
  show pL (ptOf φ (ringOf φ P hP) (ringOf_cond φ P hP)) = pL P
  rw [ptOf_left, ← Category.assoc, specMap_ringOf, kgOf]
  exact pullback.lift_fst _ _ _

theorem ringOf_injective {Λ : CommRingCat.{0}} {s : CommRingCat.of K ⟶ Λ} {P Q : pt' s ⟶ X}
    (hP : P ≫ φ = 1) (hQ : Q ≫ φ = 1) (h : ringOf φ P hP = ringOf φ Q hQ) : P = Q := by
  rw [← ptOf_ringOf φ P hP, ← ptOf_ringOf φ Q hQ]
  congr 1

theorem ringOf_ptOf {Λ : CommRingCat.{0}} {s : CommRingCat.of K ⟶ Λ} (ρ : Γ(kerSch φ, ⊤) ⟶ Λ)
    (hρ : kerAlg φ ≫ ρ = s) : ringOf φ (ptOf φ ρ hρ) (ptOf_ker φ ρ hρ) = ρ := by
  apply Spec.map_injective
  rw [← cancel_mono (kerSch φ).isoSpec.inv, specMap_ringOf]
  apply pullback.hom_ext
  · rw [kgOf, pullback.lift_fst, ptOf_left, Category.assoc]
  · rw [kgOf, pullback.lift_snd, Category.assoc, isoSpec_inv_snd, ← Spec.map_comp, hρ]

/-- **Naturality in `Λ`.** -/
theorem ringOf_sh' {Λ Λ' : CommRingCat.{0}} {s : CommRingCat.of K ⟶ Λ}
    {s' : CommRingCat.of K ⟶ Λ'} (σ : Λ ⟶ Λ') (h : s ≫ σ = s') (P : pt' s ⟶ X) (hP : P ≫ φ = 1)
    (hQ : (sh' σ h ≫ P) ≫ φ = 1) :
    ringOf φ (sh' σ h ≫ P) hQ = ringOf φ P hP ≫ σ := by
  apply Spec.map_injective
  rw [← cancel_mono (kerSch φ).isoSpec.inv, specMap_ringOf, Spec.map_comp,
    Category.assoc (Spec.map σ), specMap_ringOf]
  apply pullback.hom_ext
  · rw [kgOf, kgOf, pullback.lift_fst, Category.assoc, pullback.lift_fst, pL_sh']
  · rw [kgOf, kgOf, pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Spec.map_comp, h]

end KerRing

end GapHeight
