import ZInQKernel.Contrib.OneProof.TateSemisimplicity
import ZInQKernel.Contrib.OneProof.TateRationalHom
import ZInQKernel.Contrib.OneProof.H.TailP

/-! # Algebraicity from the graph of a rational Tate homomorphism -/

noncomputable section

open CategoryTheory AlgebraicGeometry PkgI3.AbVar
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace ZInQ.Contrib.TateFiniteApproximation

/-- An algebraic endomorphism with graph image gives an algebraic map
into that graph over its first coordinate. -/
theorem exists_graph_section_of_range
    {F V X Y R : Type*} [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
    [Ring R] [IsSemisimpleRing R]
    (a : R →+* Module.End F V) (i : X →ₗ[F] V) (p : V →ₗ[F] X)
    (q : V →ₗ[F] Y) (f : X →ₗ[F] Y) (e r : R)
    (hi : p.comp i = LinearMap.id)
    (he : ∀ v, a e v = i (p v))
    (hr : LinearMap.range (a r) = LinearMap.ker (q - f.comp p))
    (hs : ∀ x, ∃ v, p v = x ∧ q v = f x) :
    ∃ u : R, q.comp ((a u).comp i) = f := by
  obtain ⟨s, hsr⟩ := exists_innerInverse_of_semisimple (e * r)
  refine ⟨r * s, LinearMap.ext fun x => ?_⟩
  obtain ⟨v, hv, hv'⟩ := hs x
  have hvm : v ∈ LinearMap.range (a r) := by
    rw [hr, LinearMap.mem_ker]
    change q v - f (p v) = 0
    simp [hv, hv']
  obtain ⟨w, hw⟩ := hvm
  have hei : a (e * r) w = i x := by
    rw [map_mul, Module.End.mul_apply, he, hw, hv]
  have hfix : a (e * r) (a s (i x)) = i x := by
    have h := LinearMap.congr_fun (congrArg a hsr) w
    simpa only [map_mul, Module.End.mul_apply, ← hei] using h
  have hp : p (a (r * s) (i x)) = x := by
    have h := congrArg p hfix
    rw [map_mul, Module.End.mul_apply, he] at h
    have hh (z : X) : p (i z) = z := LinearMap.congr_fun hi z
    simp only [hh, map_mul, Module.End.mul_apply] at h ⊢
    exact h
  have hq : a (r * s) (i x) ∈ LinearMap.ker (q - f.comp p) := by
    rw [← hr]
    exact ⟨a s (i x), by simp only [map_mul, Module.End.mul_apply]⟩
  have hh : q (a (r * s) (i x)) - f (p (a (r * s) (i x))) = 0 := hq
  exact (sub_eq_zero.mp hh).trans (congrArg f hp)

section Varieties

variable {K : Type} [Field K] (ℓ : ℕ) [Fact ℓ.Prime]

private def homComp {A B C : PkgI3.AbVar K} (f : Hom A B) (g : Hom B C) : Hom A C :=
  Hom.mk' (f.hom ≫ g.hom)

private theorem homT_homComp {A B C : PkgI3.AbVar K} (f : Hom A B) (g : Hom B C) :
    homT (ℓ := ℓ) (homComp f g) = (homT g).comp (homT f) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  change Additive.ofMul (Additive.toMul (x.1 n) ≫ (f.hom ≫ g.hom)) =
    Additive.ofMul ((Additive.toMul (x.1 n) ≫ f.hom) ≫ g.hom)
  rw [Category.assoc]

/-- The product abelian variety on which the graph is realized. -/
def tateProduct (A B : PkgI3.AbVar K) : PkgI3.AbVar K :=
  AVGlue.prodAbVar A B

private def fstHom (A B : PkgI3.AbVar K) : Hom (tateProduct A B) A := by
  change Hom (AVGlue.prodAbVar A B) A
  exact Hom.mk' (fst A.X B.X)

private def sndHom (A B : PkgI3.AbVar K) : Hom (tateProduct A B) B := by
  change Hom (AVGlue.prodAbVar A B) B
  exact Hom.mk' (snd A.X B.X)

private def inlHom (A B : PkgI3.AbVar K) : Hom A (tateProduct A B) := by
  change Hom A (AVGlue.prodAbVar A B)
  exact Hom.mk' (lift (𝟙 A.X) ((0 : Hom A B).hom))

private def inrHom (A B : PkgI3.AbVar K) : Hom B (tateProduct A B) := by
  change Hom B (AVGlue.prodAbVar A B)
  exact Hom.mk' (lift ((0 : Hom B A).hom) (𝟙 B.X))

private abbrev homV {A B : PkgI3.AbVar K} (f : Hom A B) :
    A.V ℓ →ₗ[ℚ_[ℓ]] B.V ℓ := (homT (ℓ := ℓ) f).baseChange ℚ_[ℓ]

private theorem homV_homComp {A B C : PkgI3.AbVar K} (f : Hom A B) (g : Hom B C) :
    homV ℓ (homComp f g) = (homV ℓ g).comp (homV ℓ f) := by
  rw [homV, homT_homComp, LinearMap.baseChange_comp]

private theorem homV_galRep {A B : PkgI3.AbVar K} (f : Hom A B)
    (σ : Field.absoluteGaloisGroup K) (x : A.V ℓ) :
    homV ℓ f (A.galRep ℓ σ x) = B.galRep ℓ σ (homV ℓ f x) := by
  have h : homT (ℓ := ℓ) f ∘ₗ A.galT σ = B.galT σ ∘ₗ homT f :=
    LinearMap.ext (PkgI3.homT_galT f σ)
  exact LinearMap.congr_fun (by
    change (homT (ℓ := ℓ) f).baseChange ℚ_[ℓ] ∘ₗ (A.galT σ).baseChange ℚ_[ℓ] =
      (B.galT σ).baseChange ℚ_[ℓ] ∘ₗ (homT f).baseChange ℚ_[ℓ]
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, h]) x

private theorem homV_one (A : PkgI3.AbVar K) : homV ℓ (1 : End A) = LinearMap.id := by
  rw [homV, R16Split.homT_one, LinearMap.baseChange_id]

private theorem homV_zero (A B : PkgI3.AbVar K) : homV ℓ (0 : Hom A B) = 0 := by
  change (tateHom ℓ A B 0).baseChange ℚ_[ℓ] = 0
  rw [map_zero, LinearMap.baseChange_zero]

private theorem homV_fst_inl (A B : PkgI3.AbVar K) :
    (homV ℓ (fstHom A B)).comp (homV ℓ (inlHom A B)) = LinearMap.id := by
  rw [← homV_homComp, show homComp (inlHom A B) (fstHom A B) = 1 from Hom.ext' (by
    change lift (𝟙 A.X) (1 : A.X ⟶ B.X) ≫ fst A.X B.X = 𝟙 A.X
    simp), homV_one]

private theorem homV_snd_inl (A B : PkgI3.AbVar K) :
    (homV ℓ (sndHom A B)).comp (homV ℓ (inlHom A B)) = 0 := by
  rw [← homV_homComp, show homComp (inlHom A B) (sndHom A B) = 0 from Hom.ext' (by
    change lift (𝟙 A.X) (1 : A.X ⟶ B.X) ≫ snd A.X B.X = 1
    simp), homV_zero]

private theorem homV_fst_inr (A B : PkgI3.AbVar K) :
    (homV ℓ (fstHom A B)).comp (homV ℓ (inrHom A B)) = 0 := by
  rw [← homV_homComp, show homComp (inrHom A B) (fstHom A B) = 0 from Hom.ext' (by
    change lift (1 : B.X ⟶ A.X) (𝟙 B.X) ≫ fst A.X B.X = 1
    simp), homV_zero]

private theorem homV_snd_inr (A B : PkgI3.AbVar K) :
    (homV ℓ (sndHom A B)).comp (homV ℓ (inrHom A B)) = LinearMap.id := by
  rw [← homV_homComp, show homComp (inrHom A B) (sndHom A B) = 1 from Hom.ext' (by
    change lift (1 : B.X ⟶ A.X) (𝟙 B.X) ≫ snd A.X B.X = 𝟙 B.X
    simp), homV_one]

private theorem exists_sandwich (A B C : PkgI3.AbVar K) (i : Hom A C) (p : Hom C B)
    (u : ℚ_[ℓ] ⊗[ℤ] End C) :
    ∃ v : ℚ_[ℓ] ⊗[ℤ] Hom A B,
      tateHomQl ℓ A B v = (homV ℓ p).comp ((rationalEndAction ℓ C u).comp (homV ℓ i)) := by
  induction u using TensorProduct.inductionOn with
  | add u v hu hv =>
    obtain ⟨u', hu'⟩ := hu
    obtain ⟨v', hv'⟩ := hv
    exact ⟨u' + v', by rw [map_add, hu', hv', map_add, LinearMap.add_comp, LinearMap.comp_add]⟩
  | tmul a f =>
    refine ⟨a ⊗ₜ[ℤ] homComp (homComp i f) p, ?_⟩
    rw [tateHomQl_tmul, rationalEndAction_tmul, LinearMap.smul_comp, LinearMap.comp_smul]
    change a • homV ℓ (homComp (homComp i f) p) =
      a • (homV ℓ p).comp ((homV ℓ f).comp (homV ℓ i))
    rw [homV_homComp, homV_homComp]

private def graphSubrepresentation
    {F G V X Y : Type*} [Field F] [Monoid G]
    [AddCommGroup V] [Module F V] [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
    (ρV : Representation F G V) (ρX : Representation F G X) (ρY : Representation F G Y)
    (p : V →ₗ[F] X) (q : V →ₗ[F] Y) (f : X →ₗ[F] Y)
    (hp : ∀ σ x, p (ρV σ x) = ρX σ (p x))
    (hq : ∀ σ x, q (ρV σ x) = ρY σ (q x))
    (hf : ∀ σ x, f (ρX σ x) = ρY σ (f x)) : Subrepresentation ρV where
  toSubmodule := LinearMap.ker (q - f.comp p)
  apply_mem_toSubmodule σ x hx := by
    have hx' : q x = f (p x) := sub_eq_zero.mp hx
    change q (ρV σ x) - f (p (ρV σ x)) = 0
    rw [hp, hq, hf, hx', sub_self]

set_option maxHeartbeats 1000000 in
/-- Every equivariant rational map of Tate spaces is algebraic, given range
realization and semisimplicity of the endomorphism algebra of the product. -/
theorem exists_tateHomQl_of_endomorphism_ranges (A B : PkgI3.AbVar K)
    [IsSemisimpleRing (ℚ_[ℓ] ⊗[ℤ] End (tateProduct A B))]
    (hrange : ∀ U : Subrepresentation ((tateProduct A B).galRep ℓ),
      ∃ r, LinearMap.range (rationalEndAction ℓ (tateProduct A B) r) = U.toSubmodule)
    (f : A.V ℓ →ₗ[ℚ_[ℓ]] B.V ℓ)
    (hf : ∀ σ x, f (A.galRep ℓ σ x) = B.galRep ℓ σ (f x)) :
    f ∈ Set.range (tateHomQl ℓ A B) := by
  let C := tateProduct A B
  let i := homV ℓ (inlHom A B)
  let j := homV ℓ (inrHom A B)
  let p := homV ℓ (fstHom A B)
  let q := homV ℓ (sndHom A B)
  let U := graphSubrepresentation (C.galRep ℓ) (A.galRep ℓ) (B.galRep ℓ) p q f
    (homV_galRep ℓ (fstHom A B)) (homV_galRep ℓ (sndHom A B)) hf
  obtain ⟨r, hr⟩ := hrange U
  let e : ℚ_[ℓ] ⊗[ℤ] End C := 1 ⊗ₜ[ℤ] homComp (fstHom A B) (inlHom A B)
  have he (x : C.V ℓ) : rationalEndAction ℓ C e x = i (p x) := by
    simp only [e, rationalEndAction_tmul, one_smul]
    exact LinearMap.congr_fun (homV_homComp ℓ (fstHom A B) (inlHom A B)) x
  have hs (x : A.V ℓ) : ∃ v, p v = x ∧ q v = f x := by
    refine ⟨i x + j (f x), ?_, ?_⟩
    · rw [map_add]
      change ((homV ℓ (fstHom A B)).comp (homV ℓ (inlHom A B))) x +
        ((homV ℓ (fstHom A B)).comp (homV ℓ (inrHom A B))) (f x) = x
      rw [homV_fst_inl, homV_fst_inr, LinearMap.id_apply, LinearMap.zero_apply, add_zero]
    · rw [map_add]
      change ((homV ℓ (sndHom A B)).comp (homV ℓ (inlHom A B))) x +
        ((homV ℓ (sndHom A B)).comp (homV ℓ (inrHom A B))) (f x) = f x
      rw [homV_snd_inl, homV_snd_inr, LinearMap.id_apply, LinearMap.zero_apply, zero_add]
  obtain ⟨u, hu⟩ := exists_graph_section_of_range (rationalEndAction ℓ C).toRingHom i p q f e r
    (homV_fst_inl ℓ A B) he hr hs
  obtain ⟨v, hv⟩ := exists_sandwich ℓ A B C (inlHom A B) (sndHom A B) u
  exact ⟨v, hv.trans hu⟩

end Varieties

end ZInQ.Contrib.TateFiniteApproximation

#print axioms ZInQ.Contrib.TateFiniteApproximation.exists_tateHomQl_of_endomorphism_ranges
