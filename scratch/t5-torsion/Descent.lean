import ZInQKernel.Contrib.AbVarBC.Main
import ZInQKernel.HDecomp.LeafPush2.T

/-!
# t5-torsion, part 3: torsion points along `K̄ → Ω₂` (characteristic 0)
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace T5Torsion

open ZInQ.Contrib.AbVarBC

section Desc

variable {K : Type} [Field K] (A : PkgI3.AbVar K)
  {Ω Ω₂ : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Field Ω₂] [Algebra K Ω₂]

/-- **Lifting `N`-torsion points along `κ : Ω → Ω₂`** when `[N]` is finite (adapted from
`ZInQ.Contrib.AbVarBC.torsionDescends_of_isFinite`). -/
theorem exists_extPt_eq (κ : Ω →ₐ[K] Ω₂) (N : ℕ)
    (hfin : IsFinite ((((N : ℤ)) : PkgI3.AbVar.End A).hom.left))
    (q : A.Pt Ω₂) (hq : q ^ N = 1) : ∃ p : A.Pt Ω, extPt A κ p = q := by
  have h1 : q ≫ ((N : ℤ) : PkgI3.AbVar.End A).hom = 1 := by rw [comp_natCast_hom, hq]
  let fN : A.X.left ⟶ A.X.left := ((N : ℤ) : PkgI3.AbVar.End A).hom.left
  let e : Spec (CommRingCat.of K) ⟶ A.X.left := η[A.X].left
  have hq0 : q.left ≫ fN = Spec.map (CommRingCat.ofHom (algebraMap K Ω₂)) ≫ e := by
    have h2 := congrArg (fun f => f.left) h1
    simp only [Over.comp_left, Hom.one_def] at h2
    exact h2
  have hfN : IsFinite fN := hfin
  let z : Spec (CommRingCat.of Ω₂) ⟶ pullback fN e :=
    pullback.lift q.left (Spec.map (CommRingCat.ofHom (algebraMap K Ω₂))) hq0
  obtain ⟨p0, hp0, hp0g⟩ :=
    exists_lift_of_isFinite κ (pullback.snd fN e) z (pullback.lift_snd _ _ _)
  have hfst : pullback.fst fN e ≫ A.X.hom = pullback.snd fN e := by
    have hw : fN ≫ A.X.hom = A.X.hom := Over.w ((N : ℤ) : PkgI3.AbVar.End A).hom
    have he : e ≫ A.X.hom = 𝟙 _ := Over.w η[A.X]
    rw [← hw, ← Category.assoc, pullback.condition, Category.assoc, he, Category.comp_id]
  let p : A.Pt Ω := Over.homMk (p0 ≫ pullback.fst fN e) (by
    change (p0 ≫ pullback.fst fN e) ≫ A.X.hom = _
    rw [Category.assoc, hfst, hp0g]
    rfl)
  refine ⟨p, ?_⟩
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂)) ≫ p0 ≫ pullback.fst fN e = q.left
  rw [← Category.assoc, hp0]
  exact pullback.lift_fst _ _ _

/-- **`#A(Ω)[n] = #A(Ω₂)[n]`** in characteristic `0`, for `Ω` algebraically closed. -/
theorem natCard_torsion_eq_of_ext [CharZero K] (κ : Ω →ₐ[K] Ω₂) (n : ℕ) (hn : 0 < n) :
    Nat.card {p : A.Pt Ω // p ^ n = 1} = Nat.card {q : A.Pt Ω₂ // q ^ n = 1} := by
  have hfin : IsFinite ((((n : ℤ)) : PkgI3.AbVar.End A).hom.left) :=
    (mulIsogeny K A (n : ℤ) (by exact_mod_cast hn.ne')).1
  let f : {p : A.Pt Ω // p ^ n = 1} → {q : A.Pt Ω₂ // q ^ n = 1} := fun p =>
    ⟨extPt A κ p.1, by rw [← map_pow, p.2, map_one]⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p p' h => Subtype.ext (extPt_injective A κ (congrArg Subtype.val h)), ?_⟩
    rintro ⟨q, hq⟩
    obtain ⟨p, hp⟩ := exists_extPt_eq A κ n hfin q hq
    refine ⟨⟨p, extPt_injective A κ ?_⟩, Subtype.ext hp⟩
    rw [map_pow, hp, hq, map_one]
  exact Nat.card_congr (Equiv.ofBijective f hf)

end Desc

end T5Torsion

#print axioms T5Torsion.natCard_torsion_eq_of_ext
