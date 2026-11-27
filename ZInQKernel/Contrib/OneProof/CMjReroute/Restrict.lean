import ZInQKernel.HDecomp.Objects
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Restricting an endomorphism to the image of an endomorphism

Let `A`, `E` be abelian varieties over a field `K`, `i : E → A` a homomorphism which is a closed
immersion, and `h : A → E` a surjective homomorphism, so that `e = i ∘ h` is an endomorphism of `A`
whose image is `E`. Every endomorphism `r` of `A` commuting with `e` maps `E` into itself: there is a
unique endomorphism `r_E` of `E` with `i ∘ r_E = r ∘ i` (`exists_restrict`, `restrict`).

*Proof.* `E` is integral, hence reduced, and `h` is surjective and quasi-compact, so `h` is
scheme-theoretically dominant: the ideal sheaf of `i` is the kernel of `e`. The kernel of `e` is
contained in the kernel of `e ∘ r = r ∘ e`, which is the kernel of `r ∘ i`. So `r ∘ i` factors through
the closed immersion `i`; the factor is a morphism over `K`, and it respects the group law because `i`
is a monomorphism and a homomorphism.

The restriction is a ring homomorphism on the centralizer of `e` (`restrictHom`). When `e` is the
first of a family of scaled matrix units (`f i j f k l = δ_{jk} n f i l`, `f 0 0 + f 1 1 = n`, `n ≥ 1`)
in a ring without additive torsion, a central element restricting to `0` is `0`
(`eq_zero_of_mul_unit_eq_zero`): the restriction is injective on the centre.

This is the only subvariety statement the matrix-unit curve needs: no general theory of abelian
subvarieties is used, only the closed immersion and the surjection that exhibit `E` as an image.
-/

noncomputable section

namespace HDec.CMBranch.CMjReroute

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-! ## 1. Schemes: an endomorphism commuting with `h ≫ i` maps the closed subscheme into itself -/

section Scheme

/-- A closed immersion `i : E → A`, a scheme-theoretically dominant `h : A → E`, and `r : A → A`
commuting with `h ≫ i`: then `i ≫ r` factors through `i`. -/
theorem exists_lift_of_comm {A E : Scheme} (i : E ⟶ A) [IsClosedImmersion i] (h : A ⟶ E)
    [IsSchemeTheoreticallyDominant h] (r : A ⟶ A) (hr : (h ≫ i) ≫ r = r ≫ (h ≫ i)) :
    ∃ rE : E ⟶ E, rE ≫ i = i ≫ r := by
  have hker : i.ker ≤ (i ≫ r).ker := by
    have h1 : (h ≫ i).ker = i.ker := by
      rw [Scheme.Hom.ker_comp, h.ker_eq_bot, Scheme.IdealSheafData.map_bot]
    have h2 : (h ≫ (i ≫ r)).ker = (i ≫ r).ker := by
      rw [Scheme.Hom.ker_comp, h.ker_eq_bot, Scheme.IdealSheafData.map_bot]
    calc i.ker = (h ≫ i).ker := h1.symm
      _ ≤ (r ≫ (h ≫ i)).ker := Scheme.Hom.le_ker_comp _ _
      _ = (h ≫ (i ≫ r)).ker := by rw [← hr, Category.assoc]
      _ = (i ≫ r).ker := h2
  exact ⟨IsClosedImmersion.lift i (i ≫ r) hker, IsClosedImmersion.lift_fac _ _ _⟩

end Scheme

/-! ## 2. Abelian varieties -/

section AbVar

variable {K : Type} [Field K]

/-- The underlying scheme of an abelian variety is integral (geometrically integral over a field). -/
theorem isIntegral_left (A : PkgI3.AbVar K) : IsIntegral A.X.left :=
  GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.X.hom

attribute [local instance] isIntegral_left

theorem isReduced_left (A : PkgI3.AbVar K) : IsReduced A.X.left :=
  isReduced_of_isIntegral _

attribute [local instance] isReduced_left

/-- A surjective homomorphism of abelian varieties is scheme-theoretically dominant. -/
theorem isSchemeTheoreticallyDominant_of_surjective {A E : PkgI3.AbVar K}
    (h : PkgI3.AbVar.Hom A E) (hs : Surjective h.hom.left) :
    IsSchemeTheoreticallyDominant h.hom.left := by
  have : QuasiCompact (h.hom.left ≫ E.X.hom) := by rw [Over.w h.hom]; infer_instance
  have : QuasiCompact h.hom.left := QuasiCompact.of_comp h.hom.left E.X.hom
  have := hs
  exact (isSchemeTheoreticallyDominant_iff_isDominant _).mpr inferInstance

/-- A homomorphism whose underlying morphism of schemes is a monomorphism is a monomorphism over
`K`. -/
theorem mono_hom_of_mono_left {A E : PkgI3.AbVar K} (i : PkgI3.AbVar.Hom E A)
    [Mono i.hom.left] : Mono i.hom :=
  (Over.forget _).mono_of_mono_map (by simpa using (inferInstance : Mono i.hom.left))

/-- **Restriction to the image of `e = i ∘ h`.** For a closed immersion `i : E → A` and a surjective
`h : A → E`, every endomorphism `r` of `A` commuting with `e` (`e ≫ r = r ≫ e` on the underlying
morphisms, with `e = h ≫ i` in diagram order) restricts to an endomorphism `r_E` of `E`:
`r_E ≫ i = i ≫ r`. -/
theorem exists_restrict {A E : PkgI3.AbVar K} (i : PkgI3.AbVar.Hom E A) (h : PkgI3.AbVar.Hom A E)
    (hi : IsClosedImmersion i.hom.left) (hs : Surjective h.hom.left) (r : PkgI3.AbVar.End A)
    (hr : (h.hom ≫ i.hom) ≫ r.hom = r.hom ≫ (h.hom ≫ i.hom)) :
    ∃ rE : PkgI3.AbVar.End E, rE.hom ≫ i.hom = i.hom ≫ r.hom := by
  have := hi
  have := isSchemeTheoreticallyDominant_of_surjective h hs
  have hr' : (h.hom.left ≫ i.hom.left) ≫ r.hom.left = r.hom.left ≫ (h.hom.left ≫ i.hom.left) := by
    simpa only [Over.comp_left] using congrArg CommaMorphism.left hr
  obtain ⟨g, hg⟩ := exists_lift_of_comm i.hom.left h.hom.left r.hom.left hr'
  have hw : g ≫ E.X.hom = E.X.hom := by
    rw [← Over.w i.hom, ← Category.assoc, hg, Category.assoc, Over.w r.hom]
  let G : E.X ⟶ E.X := Over.homMk g hw
  have hGi : G ≫ i.hom = i.hom ≫ r.hom := by
    apply Over.OverMorphism.ext
    simpa [G] using hg
  have : Mono i.hom := mono_hom_of_mono_left i
  have : IsMonHom G := by
    constructor
    · rw [← cancel_mono i.hom, Category.assoc, hGi, ← Category.assoc, IsMonHom.one_hom,
        IsMonHom.one_hom]
    · rw [← cancel_mono i.hom, Category.assoc, hGi, ← Category.assoc, IsMonHom.mul_hom,
        Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom, ← Category.assoc,
        ← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
        MonoidalCategory.tensorHom_comp_tensorHom, hGi]
  exact ⟨PkgI3.AbVar.Hom.mk' G, hGi⟩

/-- The restriction is unique (`i` is a monomorphism). -/
theorem restrict_unique {A E : PkgI3.AbVar K} (i : PkgI3.AbVar.Hom E A)
    (hi : IsClosedImmersion i.hom.left) {s s' : PkgI3.AbVar.End E}
    (h : s.hom ≫ i.hom = s'.hom ≫ i.hom) : s = s' := by
  have := hi
  have : Mono i.hom := mono_hom_of_mono_left i
  exact PkgI3.AbVar.Hom.ext' ((cancel_mono i.hom).mp h)

end AbVar

/-! ## 3. The restriction as a ring homomorphism on the centralizer of `e` -/

section Ring

variable {K : Type} [Field K] {A E : PkgI3.AbVar K} (i : PkgI3.AbVar.Hom E A)
  (h : PkgI3.AbVar.Hom A E) (hi : IsClosedImmersion i.hom.left) (hs : Surjective h.hom.left)

/-- `e = i ∘ h` as an element of `End A` (multiplication is composition, `f * g = f ∘ g`). -/
def imgEnd : PkgI3.AbVar.End A := PkgI3.AbVar.Hom.mk' (h.hom ≫ i.hom)

theorem commute_iff (r : PkgI3.AbVar.End A) :
    Commute r (imgEnd i h) ↔ (h.hom ≫ i.hom) ≫ r.hom = r.hom ≫ (h.hom ≫ i.hom) := by
  constructor
  · intro hc
    have := congrArg PkgI3.AbVar.Hom.hom hc.eq
    exact this
  · intro hc
    exact PkgI3.AbVar.Hom.ext' hc

/-- The restriction of an endomorphism commuting with `e`. -/
def restrict (r : Subring.centralizer ({imgEnd i h} : Set (PkgI3.AbVar.End A))) :
    PkgI3.AbVar.End E :=
  (exists_restrict i h hi hs r.1
    ((commute_iff i h r.1).mp (Subring.mem_centralizer_iff.mp r.2 _ rfl).symm)).choose

theorem restrict_spec (r : Subring.centralizer ({imgEnd i h} : Set (PkgI3.AbVar.End A))) :
    (restrict i h hi hs r).hom ≫ i.hom = i.hom ≫ r.1.hom :=
  (exists_restrict i h hi hs r.1
    ((commute_iff i h r.1).mp (Subring.mem_centralizer_iff.mp r.2 _ rfl).symm)).choose_spec

theorem restrict_eq_iff (r : Subring.centralizer ({imgEnd i h} : Set (PkgI3.AbVar.End A)))
    (s : PkgI3.AbVar.End E) : restrict i h hi hs r = s ↔ s.hom ≫ i.hom = i.hom ≫ r.1.hom := by
  constructor
  · rintro rfl; exact restrict_spec i h hi hs r
  · intro hsr
    exact restrict_unique i hi ((restrict_spec i h hi hs r).trans hsr.symm)

/-- **The restriction is a ring homomorphism** on the centralizer of `e`. -/
def restrictHom : Subring.centralizer ({imgEnd i h} : Set (PkgI3.AbVar.End A)) →+*
    PkgI3.AbVar.End E where
  toFun := restrict i h hi hs
  map_one' := by
    rw [restrict_eq_iff]
    show 𝟙 _ ≫ i.hom = i.hom ≫ 𝟙 _
    simp
  map_mul' r s := by
    rw [restrict_eq_iff]
    show ((restrict i h hi hs s).hom ≫ (restrict i h hi hs r).hom) ≫ i.hom =
      i.hom ≫ (s.1.hom ≫ r.1.hom)
    rw [Category.assoc, restrict_spec, ← Category.assoc, restrict_spec, Category.assoc]
  map_zero' := by
    rw [restrict_eq_iff]
    show (1 : E.X ⟶ E.X) ≫ i.hom = i.hom ≫ (1 : A.X ⟶ A.X)
    rw [MonObj.one_comp, MonObj.comp_one]
  map_add' r s := by
    rw [restrict_eq_iff]
    show ((restrict i h hi hs r).hom * (restrict i h hi hs s).hom) ≫ i.hom =
      i.hom ≫ (r.1.hom * s.1.hom)
    rw [MonObj.mul_comp, MonObj.comp_mul, restrict_spec, restrict_spec]

theorem restrictHom_spec (r : Subring.centralizer ({imgEnd i h} : Set (PkgI3.AbVar.End A))) :
    (restrictHom i h hi hs r).hom ≫ i.hom = i.hom ≫ r.1.hom :=
  restrict_spec i h hi hs r

end Ring

/-! ## 4. Injectivity on the centre, for scaled matrix units -/

section MatrixUnits

/-- In a ring without additive `n`-torsion, with `n`-scaled matrix units `f`, a central element `r`
with `r f₀₀ = 0` is `0`: `n² f₁₁ r = f₁₀ f₀₀ f₀₁ r = f₁₀ (r f₀₀) f₀₁ = 0`, so `f₁₁ r = 0` and
`n r = (f₀₀ + f₁₁) r = 0`. -/
theorem eq_zero_of_mul_unit_eq_zero {M : Type*} [Ring M] (n : ℕ)
    (htf : ∀ x : M, (n : M) * x = 0 → x = 0) (f : Fin 2 → Fin 2 → M)
    (hrel : ∀ i j k l, f i j * f k l = if j = k then (n : M) * f i l else 0)
    (hsum : f 0 0 + f 1 1 = (n : M)) (r : M) (hr : ∀ x : M, x * r = r * x)
    (h0 : r * f 0 0 = 0) : r = 0 := by
  have e1 : f 1 0 * f 0 0 = (n : M) * f 1 0 := by simpa using hrel 1 0 0 0
  have e2 : f 1 0 * f 0 1 = (n : M) * f 1 1 := by simpa using hrel 1 0 0 1
  have hn2 : ((n : M) * (n : M)) * (f 1 1 * r) = 0 := by
    calc ((n : M) * (n : M)) * (f 1 1 * r) = (n : M) * ((n : M) * f 1 1) * r := by
          simp only [_root_.mul_assoc]
      _ = (n : M) * (f 1 0 * f 0 1) * r := by rw [e2]
      _ = ((n : M) * f 1 0) * f 0 1 * r := by simp only [_root_.mul_assoc]
      _ = (f 1 0 * f 0 0) * f 0 1 * r := by rw [e1]
      _ = f 1 0 * f 0 0 * (f 0 1 * r) := by simp only [_root_.mul_assoc]
      _ = f 1 0 * f 0 0 * (r * f 0 1) := by rw [hr]
      _ = f 1 0 * (f 0 0 * r) * f 0 1 := by simp only [_root_.mul_assoc]
      _ = f 1 0 * (r * f 0 0) * f 0 1 := by rw [hr (f 0 0)]
      _ = 0 := by rw [h0]; simp
  have h11 : f 1 1 * r = 0 := htf _ (htf _ (by rw [← _root_.mul_assoc]; exact hn2))
  have h00 : f 0 0 * r = 0 := by rw [hr (f 0 0)]; exact h0
  apply htf
  rw [← hsum, add_mul, h00, h11, add_zero]

end MatrixUnits

end HDec.CMBranch.CMjReroute

