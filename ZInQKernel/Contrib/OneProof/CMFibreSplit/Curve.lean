import ZInQKernel.Contrib.OneProof.CMFibreSplit.Reduction
import ZInQKernel.Contrib.OneProof.CartierSmooth
import ZInQKernel.Contrib.Dim.IntegralHom

/-! # cm-fibre-split: the curve `E` and the isogeny `E² → A` from multiples of matrix units
(manuscript L583-585); geometry only -/

set_option maxHeartbeats 1000000

noncomputable section

namespace HDec
namespace CMBranch
namespace FibreSplit

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct

/-- `f` are matrix units scaled by `n`. -/
def IsScaledMatrixUnits {R : Type*} [Ring R] (n : ℕ) (f : Fin 2 → Fin 2 → R) : Prop :=
  (∀ i j k l, f i j * f k l = if j = k then (n : R) * f i l else 0) ∧ f 0 0 + f 1 1 = (n : R)

section Hom

variable {K : Type} [Field K]

/-- Composition of homomorphisms (diagram order). -/
def cmp {X Y Z : PkgI3.AbVar K} (g : PkgI3.AbVar.Hom X Y) (f : PkgI3.AbVar.Hom Y Z) :
    PkgI3.AbVar.Hom X Z :=
  PkgI3.AbVar.Hom.mk' (g.hom ≫ f.hom)

@[simp] theorem cmp_hom {X Y Z : PkgI3.AbVar K} (g : PkgI3.AbVar.Hom X Y) (f : PkgI3.AbVar.Hom Y Z) :
    (cmp g f).hom = g.hom ≫ f.hom := rfl

theorem cmp_assoc {X Y Z W : PkgI3.AbVar K} (g : PkgI3.AbVar.Hom X Y) (f : PkgI3.AbVar.Hom Y Z)
    (e : PkgI3.AbVar.Hom Z W) : cmp (cmp g f) e = cmp g (cmp f e) :=
  PkgI3.AbVar.Hom.ext' (Category.assoc _ _ _)

/-- `g ↦ g ∘ f`, additive. -/
def cmpR {X Y Z : PkgI3.AbVar K} (f : PkgI3.AbVar.Hom Y Z) :
    PkgI3.AbVar.Hom X Y →+ PkgI3.AbVar.Hom X Z where
  toFun g := cmp g f
  map_zero' := PkgI3.AbVar.Hom.ext' (by
    change (1 : X.X ⟶ Y.X) ≫ f.hom = 1
    exact MonObj.one_comp _)
  map_add' g g' := PkgI3.AbVar.Hom.ext' (by
    change (g.hom * g'.hom) ≫ f.hom = g.hom ≫ f.hom * g'.hom ≫ f.hom
    exact MonObj.mul_comp _ _ _)

/-- `f ↦ g ∘ f`, additive. -/
def cmpL {X Y Z : PkgI3.AbVar K} (g : PkgI3.AbVar.Hom X Y) :
    PkgI3.AbVar.Hom Y Z →+ PkgI3.AbVar.Hom X Z where
  toFun f := cmp g f
  map_zero' := PkgI3.AbVar.Hom.ext' (by
    change g.hom ≫ (1 : Y.X ⟶ Z.X) = 1
    exact MonObj.comp_one _)
  map_add' f f' := PkgI3.AbVar.Hom.ext' (by
    change g.hom ≫ (f.hom * f'.hom) = g.hom ≫ f.hom * g.hom ≫ f'.hom
    exact MonObj.comp_mul _ _ _)

theorem cmp_add_left {X Y Z : PkgI3.AbVar K} (g g' : PkgI3.AbVar.Hom X Y) (f : PkgI3.AbVar.Hom Y Z) :
    cmp (g + g') f = cmp g f + cmp g' f := (cmpR f).map_add g g'
theorem cmp_add_right {X Y Z : PkgI3.AbVar K} (g : PkgI3.AbVar.Hom X Y) (f f' : PkgI3.AbVar.Hom Y Z) :
    cmp g (f + f') = cmp g f + cmp g f' := (cmpL g).map_add f f'
theorem cmp_zsmul_left {X Y Z : PkgI3.AbVar K} (m : ℤ) (g : PkgI3.AbVar.Hom X Y)
    (f : PkgI3.AbVar.Hom Y Z) : cmp (m • g) f = m • cmp g f := map_zsmul (cmpR f) m g
theorem cmp_zsmul_right {X Y Z : PkgI3.AbVar K} (m : ℤ) (g : PkgI3.AbVar.Hom X Y)
    (f : PkgI3.AbVar.Hom Y Z) : cmp g (m • f) = m • cmp g f := map_zsmul (cmpL g) m f
@[simp] theorem cmp_zero_left {X Y Z : PkgI3.AbVar K} (f : PkgI3.AbVar.Hom Y Z) :
    cmp (0 : PkgI3.AbVar.Hom X Y) f = 0 := (cmpR f).map_zero
@[simp] theorem cmp_zero_right {X Y Z : PkgI3.AbVar K} (g : PkgI3.AbVar.Hom X Y) :
    cmp g (0 : PkgI3.AbVar.Hom Y Z) = 0 := (cmpL g).map_zero
@[simp] theorem cmp_one_left {X Y : PkgI3.AbVar K} (f : PkgI3.AbVar.Hom X Y) :
    cmp (1 : PkgI3.AbVar.End X) f = f := PkgI3.AbVar.Hom.ext' (Category.id_comp _)
@[simp] theorem cmp_one_right {X Y : PkgI3.AbVar K} (g : PkgI3.AbVar.Hom X Y) :
    cmp g (1 : PkgI3.AbVar.End Y) = g := PkgI3.AbVar.Hom.ext' (Category.comp_id _)

/-- In `End`, `f * g = g ≫ f`. -/
theorem mul_eq_cmp {X : PkgI3.AbVar K} (f g : PkgI3.AbVar.End X) : f * g = cmp g f := rfl

theorem intCast_eq_zsmul {X : PkgI3.AbVar K} (m : ℤ) : (m : PkgI3.AbVar.End X) = m • 1 := by
  rw [zsmul_eq_mul, _root_.mul_one]

theorem cmp_intCast_left {X Y : PkgI3.AbVar K} (m : ℤ) (f : PkgI3.AbVar.Hom X Y) :
    cmp (m : PkgI3.AbVar.End X) f = m • f := by
  rw [intCast_eq_zsmul, cmp_zsmul_left, cmp_one_left]

theorem cmp_intCast_right {X Y : PkgI3.AbVar K} (m : ℤ) (f : PkgI3.AbVar.Hom X Y) :
    cmp f (m : PkgI3.AbVar.End Y) = m • f := by
  rw [intCast_eq_zsmul, cmp_zsmul_right, cmp_one_right]

theorem cmp_nsmul_left {X Y Z : PkgI3.AbVar K} (m : ℕ) (g : PkgI3.AbVar.Hom X Y)
    (f : PkgI3.AbVar.Hom Y Z) : cmp (m • g) f = m • cmp g f := map_nsmul (cmpR f) m g
theorem cmp_nsmul_right {X Y Z : PkgI3.AbVar K} (m : ℕ) (g : PkgI3.AbVar.Hom X Y)
    (f : PkgI3.AbVar.Hom Y Z) : cmp g (m • f) = m • cmp g f := map_nsmul (cmpL g) m f

theorem natCast_eq_nsmul {X : PkgI3.AbVar K} (m : ℕ) : (m : PkgI3.AbVar.End X) = m • 1 := by
  rw [nsmul_eq_mul, _root_.mul_one]

theorem cmp_natCast_left {X Y : PkgI3.AbVar K} (m : ℕ) (f : PkgI3.AbVar.Hom X Y) :
    cmp (m : PkgI3.AbVar.End X) f = m • f := by
  rw [natCast_eq_nsmul, cmp_nsmul_left, cmp_one_left]

theorem cmp_natCast_right {X Y : PkgI3.AbVar K} (m : ℕ) (f : PkgI3.AbVar.Hom X Y) :
    cmp f (m : PkgI3.AbVar.End Y) = m • f := by
  rw [natCast_eq_nsmul, cmp_nsmul_right, cmp_one_right]

/-- A closed immersion is a monomorphism of homomorphisms. -/
theorem cancel_closedImm {X Y Z : PkgI3.AbVar K} (i : PkgI3.AbVar.Hom Y Z)
    (hi : IsClosedImmersion i.hom.left) {g g' : PkgI3.AbVar.Hom X Y} (h : cmp g i = cmp g' i) :
    g = g' := by
  apply PkgI3.AbVar.Hom.ext'
  apply Over.OverMorphism.ext
  have e := congrArg (fun k => k.hom.left) h
  simp only [cmp_hom, Over.comp_left] at e
  exact (cancel_mono i.hom.left).mp e

/-- A surjective homomorphism is an epimorphism (`Y` reduced, targets separated). -/
theorem cancel_surj {X Y Z : PkgI3.AbVar K} (h : PkgI3.AbVar.Hom X Y)
    (hs : Surjective h.hom.left) {g g' : PkgI3.AbVar.Hom Y Z} (e : cmp h g = cmp h g') : g = g' := by
  apply PkgI3.AbVar.Hom.ext'
  apply Over.OverMorphism.ext
  have e' := congrArg (fun k => k.hom.left) e
  simp only [cmp_hom, Over.comp_left] at e'
  exact ext_of_isDominant_of_isSeparated Z.X.hom ((Over.w g.hom).trans (Over.w g'.hom).symm)
    h.hom.left e'

end Hom

theorem withBot_eq_one_of_add_self (x : WithBot ℕ∞) (h : x + x = 2) : x = 1 := by
  induction x using WithBot.recBotCoe with
  | bot => simp at h
  | coe y =>
    induction y using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe m =>
      have h2 : (((m + m : ℕ) : ℕ∞) : WithBot ℕ∞) = (((2 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        push_cast; exact h
      have h3 : m + m = 2 := Nat.cast_injective (WithBot.coe_injective h2)
      have hm : m = 1 := by omega
      subst hm; rfl

/-! ## The curve and the isogeny (manuscript L583-585) -/

open HSyn.G0Split in
/-- **Multiples of matrix units give `E` and an isogeny `E² → A`** (manuscript L583-585, the geometric half).
For `n`-scaled matrix units `f i j` in `End_L(A)`, `A` an abelian surface over a number field `L`:
`E` = the image of `f 0 0` (an abelian subvariety, `ImageFactorization` from Cartier's theorem, proved),
`i : E → A` its inclusion and `h : A → E` with `h ≫ i = f 0 0`, `i ≫ h = [n]`; `Pr = E × E`; the isogeny
`φ(x, y) = i x + f 1 0 (i y)` with quasi-inverse `ψ(a) = (h(n² a), h(f 0 1 a))`, `φψ = [n³]`, `ψφ = [n³]`;
`dim E = 1` because `φ` is finite and surjective (dimension preserved) and `dim E² = 2 dim E`. -/
theorem matrixUnit_isogeny (L : Type) [Field L] [NumberField L] (A : PkgI3.AbVar L) (hA : A.dim = 2)
    (n : ℕ) (hn : 0 < n) (f : Fin 2 → Fin 2 → PkgI3.AbVar.End A) (hf : IsScaledMatrixUnits n f) :
    ∃ (E : PkgI3.AbVar L) (i : PkgI3.AbVar.Hom E A) (h : PkgI3.AbVar.Hom A E)
      (Pr : ZInQ.DefFaltings.AbVar L),
      cmp h i = f 0 0 ∧ cmp i h = (n : PkgI3.AbVar.End E) ∧ IsClosedImmersion i.hom.left ∧
      E.dim = 1 ∧ Pr.dim = (2 : ℕ) ∧ IsProductOf Pr.X E.X E.X ∧
      ∃ φ : Pr.X ⟶ A.X, ZInQ.DefFaltings.IsIsogeny (A := Pr) (B := A) φ := by
  obtain ⟨E, h, i, hsurj, hci, hfac⟩ :=
    AVGlue.imageFactorization_of_cartier _root_.ZInQ.Contrib.OneProof.CartierSmooth.cartierSmooth_proof
      L A A (f 0 0)
  have hF : cmp h i = f 0 0 := PkgI3.AbVar.Hom.ext' hfac.symm
  obtain ⟨hrel, hsum⟩ := hf
  have r : ∀ a b c d, cmp (f c d) (f a b) = if b = c then (n : PkgI3.AbVar.End A) * f a d else 0 :=
    fun a b c d => (mul_eq_cmp _ _).symm.trans (hrel a b c d)
  -- `i ≫ h = [n]`
  have hih : cmp i h = (n : PkgI3.AbVar.End E) := by
    apply cancel_closedImm i hci
    apply cancel_surj h hsurj
    calc cmp h (cmp (cmp i h) i) = cmp (cmp h i) (cmp h i) := by simp only [cmp_assoc]
      _ = cmp (f 0 0) (f 0 0) := by rw [hF]
      _ = (n : PkgI3.AbVar.End A) * f 0 0 := by rw [r]; simp
      _ = n • f 0 0 := by rw [mul_eq_cmp, cmp_natCast_right]
      _ = n • cmp h i := by rw [hF]
      _ = cmp h (n • i) := by rw [cmp_nsmul_right]
      _ = cmp h (cmp (n : PkgI3.AbVar.End E) i) := by rw [cmp_natCast_left]
  -- vanishing compositions
  have hz1 : cmp (cmp i (f 1 0)) h = 0 := by
    apply cancel_closedImm i hci
    rw [cmp_zero_left, cmp_assoc, cmp_assoc, hF, r]
    simp
  have hz2 : cmp i (f 0 1) = 0 := by
    apply cancel_surj h hsurj
    rw [cmp_zero_right, ← cmp_assoc, hF, r]
    simp
  -- the product
  obtain ⟨P, ⟨p₁, p₂, hp₁, hp₂, hiso⟩, hPd⟩ := G0Product.productExists L E E
  let q₁ : PkgI3.AbVar.Hom P E := PkgI3.AbVar.Hom.mk' p₁
  let q₂ : PkgI3.AbVar.Hom P E := PkgI3.AbVar.Hom.mk' p₂
  let l : P.X ⟶ E.X ⊗ E.X := lift p₁ p₂
  have hl1 : inv l ≫ p₁ = fst E.X E.X := by
    rw [← lift_fst p₁ p₂, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have hl2 : inv l ≫ p₂ = snd E.X E.X := by
    rw [← lift_snd p₁ p₂, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have hη : ∀ (a b : PkgI3.AbVar.Hom A E), η[A.X] ≫ (lift a.hom b.hom ≫ inv l) = η[P.X] := by
    intro a b
    rw [← cancel_mono l, Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, IsMonHom.one_hom, l]
    · simp only [Category.assoc, lift_snd, IsMonHom.one_hom, l]
  let pr : PkgI3.AbVar.Hom A E → PkgI3.AbVar.Hom A E → PkgI3.AbVar.Hom A P := fun a b =>
    @PkgI3.AbVar.Hom.mk' L _ A P (lift a.hom b.hom ≫ inv l)
      (G0FibreSimple.rigidityHom L A P _ (hη a b))
  have pr1 : ∀ a b, cmp (pr a b) q₁ = a := fun a b => PkgI3.AbVar.Hom.ext' (by
    change (lift a.hom b.hom ≫ inv l) ≫ p₁ = a.hom
    rw [Category.assoc, hl1, lift_fst])
  have pr2 : ∀ a b, cmp (pr a b) q₂ = b := fun a b => PkgI3.AbVar.Hom.ext' (by
    change (lift a.hom b.hom ≫ inv l) ≫ p₂ = b.hom
    rw [Category.assoc, hl2, lift_snd])
  have extP : ∀ g g' : PkgI3.AbVar.Hom P P, cmp g q₁ = cmp g' q₁ → cmp g q₂ = cmp g' q₂ → g = g' := by
    intro g g' e1 e2
    apply PkgI3.AbVar.Hom.ext'
    rw [← cancel_mono l]
    apply CartesianMonoidalCategory.hom_ext
    · simpa [l, q₁, PkgI3.AbVar.Hom.hom_mk'] using congrArg PkgI3.AbVar.Hom.hom e1
    · simpa [l, q₂, PkgI3.AbVar.Hom.hom_mk'] using congrArg PkgI3.AbVar.Hom.hom e2
  let ψ : PkgI3.AbVar.Hom A P := pr ((n * n) • h) (cmp (f 0 1) h)
  let φ : PkgI3.AbVar.Hom P A := cmp q₁ i + cmp (cmp q₂ i) (f 1 0)
  have e01 : f 0 0 * f 0 1 = (n : PkgI3.AbVar.End A) * f 0 1 := by simpa using hrel 0 0 0 1
  have e10 : f 1 0 * f 0 1 = (n : PkgI3.AbVar.End A) * f 1 1 := by simpa using hrel 1 0 0 1
  have e01' : f 0 1 * f 1 0 = (n : PkgI3.AbVar.End A) * f 0 0 := by simpa using hrel 0 1 1 0
  have hψφ : cmp ψ φ = ((n * n * n : ℕ) : PkgI3.AbVar.End A) := by
    simp only [φ, cmp_add_right, ← cmp_assoc, pr1, pr2, ψ]
    rw [cmp_nsmul_left, hF, cmp_assoc (f 0 1) h i, hF, ← mul_eq_cmp, ← mul_eq_cmp, e01,
      ← _root_.mul_assoc, ← Nat.cast_comm, _root_.mul_assoc, e10, nsmul_eq_mul, ← _root_.mul_assoc,
      ← Nat.cast_mul, ← mul_add, hsum, ← Nat.cast_mul]
  have hφψ : cmp φ ψ = ((n * n * n : ℕ) : PkgI3.AbVar.End P) := by
    apply extP
    · rw [cmp_assoc, pr1, cmp_nsmul_right, cmp_natCast_left]
      simp only [φ, cmp_add_left, cmp_assoc, hih, hz1, cmp_zero_right, add_zero, cmp_natCast_right]
      rw [smul_smul]
    · rw [cmp_assoc, pr2, cmp_natCast_left]
      simp only [φ, cmp_add_left]
      rw [cmp_assoc, ← cmp_assoc i (f 0 1) h, hz2, cmp_zero_left, cmp_zero_right, zero_add,
        cmp_assoc, cmp_assoc, ← cmp_assoc (f 1 0) (f 0 1) h, ← mul_eq_cmp, e01', mul_eq_cmp,
        cmp_natCast_right, cmp_nsmul_left, ← hF, cmp_assoc]
      simp only [hih, cmp_natCast_right, cmp_nsmul_right, smul_smul]
  have hm0 : ((n * n * n : ℕ) : ℤ) ≠ 0 := by positivity
  have hmA := _root_.ZInQ.Contrib.AbVarBC.mulIsogeny L A ((n * n * n : ℕ) : ℤ) hm0
  have hmP := _root_.ZInQ.Contrib.AbVarBC.mulIsogeny L P ((n * n * n : ℕ) : ℤ) hm0
  rw [Int.cast_natCast] at hmA hmP
  have hsurjφ : Surjective φ.hom.left := by
    have hs := hmA.2
    rw [← hψφ, cmp_hom, Over.comp_left] at hs
    exact Surjective.of_comp ψ.hom.left φ.hom.left
  have hfinφ : IsFinite φ.hom.left := by
    have hf' := hmP.1
    rw [← hφψ, cmp_hom, Over.comp_left] at hf'
    haveI : IsSeparated ψ.hom.left := by
      haveI : IsSeparated (ψ.hom.left ≫ P.X.hom) := by rw [Over.w ψ.hom]; infer_instance
      exact IsSeparated.of_comp ψ.hom.left P.X.hom
    exact IsFinite.of_comp φ.hom.left ψ.hom.left
  have hdimP : P.dim = A.dim :=
    _root_.ZInQ.Contrib.Dim.topologicalKrullDim_eq_of_finite_surjective φ.hom.left
  have hE1 : E.dim = 1 := by
    apply withBot_eq_one_of_add_self
    rw [← hPd, hdimP, hA]
  refine ⟨E, i, h, P, hF, hih, hci, hE1, by rw [hdimP, hA]; rfl, ⟨p₁, p₂, hp₁, hp₂, hiso⟩, φ.hom,
    ⟨inferInstance, hfinφ, hsurjφ⟩⟩

/-! ## Scaled matrix units from `End⁰ ≅ M₂(k)` (pure algebra) -/

/-- **Multiples of matrix units exist in `M`** when `ℚ ⊗ M ≅ M₂(k)` and `M` is torsion-free
(`M → ℚ ⊗ M` injective): clear the denominators of `e⁻¹(E_ij)`. -/
theorem exists_scaledMatrixUnits {M : Type*} [Ring M] {k : Type*} [CommRing k] [Algebra ℚ k]
    (e : ℚ ⊗[ℤ] M ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) k)
    (hinj : ∀ m : M, (1 : ℚ) ⊗ₜ[ℤ] m = 0 → m = 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ f : Fin 2 → Fin 2 → M, IsScaledMatrixUnits n f := by
  classical
  let u : Fin 2 × Fin 2 → ℚ ⊗[ℤ] M := fun p => e.symm (Matrix.single p.1 p.2 1)
  have hu : ∀ i j k l, u (i, j) * u (k, l) = if j = k then u (i, l) else 0 := by
    intro i j k l
    simp only [u]
    rw [← map_mul]
    split_ifs with h
    · subst h; rw [Matrix.single_mul_single_same, _root_.mul_one]
    · rw [Matrix.single_mul_single_of_ne (h := h), map_zero]
  have hsum : u (0, 0) + u (1, 1) = 1 := by
    simp only [u, ← map_add]
    rw [show (Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : k) + Matrix.single 1 1 1) = 1 from by
      ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.single, Matrix.one_apply]]
    exact map_one _
  let tm := TensorProduct.mk ℤ ℚ M 1
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) tm :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ tm).mpr
      (TensorProduct.isBaseChange (R := ℤ) (M := M) (S := ℚ))
  have hs : ∀ p, ∃ (x : M) (s : ℤ), s ≠ 0 ∧ (1 : ℚ) ⊗ₜ[ℤ] x = s • u p := by
    intro p
    obtain ⟨⟨x, s⟩, h⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ) tm (u p)
    refine ⟨x, s, nonZeroDivisors.coe_ne_zero s, ?_⟩
    rw [Submonoid.smul_def] at h; exact h.symm
  choose x s hs0 hxs using hs
  let m : ℤ := ∏ p, s p
  have hm0 : m ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p _ => hs0 p
  have hc : ∀ p, ∃ c : ℤ, m = s p * c := fun p => Finset.dvd_prod_of_mem s (Finset.mem_univ p)
  choose c hcm using hc
  let y : Fin 2 × Fin 2 → M := fun p => c p • x p
  have hy : ∀ p, (1 : ℚ) ⊗ₜ[ℤ] y p = m • u p := by
    intro p
    simp only [y, TensorProduct.tmul_smul, hxs, hcm p, smul_smul, mul_comm]
  have hmul1 : ∀ a b : M, (1 : ℚ) ⊗ₜ[ℤ] (a * b) = ((1 : ℚ) ⊗ₜ[ℤ] a) * ((1 : ℚ) ⊗ₜ[ℤ] b) := by
    intro a b; rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
  have hint : ∀ z : ℤ, (1 : ℚ) ⊗ₜ[ℤ] (z : M) = (z : ℚ ⊗[ℤ] M) := fun z =>
    map_intCast (Algebra.TensorProduct.includeRight : M →ₐ[ℤ] ℚ ⊗[ℤ] M) z
  have key : ∀ a b : M, (1 : ℚ) ⊗ₜ[ℤ] a = (1 : ℚ) ⊗ₜ[ℤ] b → a = b := by
    intro a b h
    exact sub_eq_zero.mp (hinj _ (by rw [TensorProduct.tmul_sub, h, sub_self]))
  have hrel : ∀ i j k l, y (i, j) * y (k, l) = if j = k then (m : M) * y (i, l) else 0 := by
    intro i j k l
    apply key
    rw [hmul1, hy, hy, smul_mul_smul_comm, hu]
    split_ifs with h
    · rw [hmul1, hint, hy, ← zsmul_eq_mul, smul_smul]
    · simp
  have hsum' : y (0, 0) + y (1, 1) = (m : M) := by
    apply key
    rw [TensorProduct.tmul_add, hy, hy, ← smul_add, hsum, hint, zsmul_eq_mul, _root_.mul_one]
  refine ⟨(m * m).natAbs, Int.natAbs_pos.mpr (mul_ne_zero hm0 hm0),
    fun i j => m • y (i, j), ?_, ?_⟩
  · intro i j k l
    have hn : (((m * m).natAbs : ℕ) : M) = ((m * m : ℤ) : M) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg (mul_self_nonneg m)]
    rw [hn, smul_mul_smul_comm, hrel]
    split_ifs
    · simp only [zsmul_eq_mul, Int.cast_mul, _root_.mul_assoc]
    · simp
  · have hn : (((m * m).natAbs : ℕ) : M) = ((m * m : ℤ) : M) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg (mul_self_nonneg m)]
    rw [hn, ← smul_add, hsum', zsmul_eq_mul, Int.cast_mul]


/-! ## The remaining glue and the reduction of `CMMatrixUnitSplit` -/

/-- **Glue (on-the-spot; manuscript L584-586, "an elliptic curve `E/L` with complex multiplication", "the
full geometric endomorphism order of `E`").** Let `A/L` be an abelian surface over a number field with
`End⁰(A_Ω) ≅ M₂(ℚ(√d))`, `d < 0` (`A` an abelian surface), and let `E/L` be an elliptic curve with homomorphisms `i : E → A`,
`h : A → E`, `h ∘ i = [n]`, `n ≥ 1` (an isogeny factor of `A`, e.g. the image of `n e₁₁`). Then the geometric
endomorphism ring of `E` is an order `R` of an imaginary quadratic field `k`. *Sketch:* `g ↦ i g h` embeds
`End⁰(E_Ω)` as the corner `e End⁰(A_Ω) e`, `e = (1/n) i h` a nonzero idempotent which is not `1` (`dim E = 1
< 2`), so of rank one in `M₂(k)`, whose corner is `k`; `End(E)` is a finitely generated subring, an order;
`End(E_{L̄}) ≅ End(E_Ω)` because both are algebraic closures of `L` (rigidity). -/
def CMCurveOrder : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (A : PkgI3.AbVar L), A.dim = 2 →
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra L Ω] [Algebra.IsAlgebraic L Ω] (d : ℚ), d < 0 →
    Nonempty (PkgI3.AbVar.End0 (A.baseChange Ω) ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) (Kd d)) →
    ∀ (E : ZInQ.DefFaltings.AbVar L), E.dim = 1 →
    ∀ (i : PkgI3.AbVar.Hom E A) (h : PkgI3.AbVar.Hom A E) (n : ℕ), 0 < n →
      cmp i h = (n : PkgI3.AbVar.End E) →
      ∃ (k : Type) (_ : Field k) (_ : NumberField k) (R : Subring k),
        IsImagQuadOrder k R ∧ IsCMBy E k R

/-- **`CMMatrixUnitSplit` from `CMCurveOrder`.** `End(A) ≅ End(A_Ω)` (`endBC` injective, and onto by
hypothesis), so `End⁰(A) ≅ M₂(ℚ(√d))`; `End(A)` is torsion-free (`[s]` is surjective, hence an epimorphism),
so scaled matrix units exist in `End(A)` (`exists_scaledMatrixUnits`); `matrixUnit_isogeny` gives `E`,
`E²` and the isogeny; `CMCurveOrder` gives the order. -/
theorem cmMatrixUnitSplit_of (hCO : CMCurveOrder) : CMMatrixUnitSplit := by
  intro L _ _ A hA Ω _ _ _ _ hsurj d hd ⟨e⟩
  let β := RingEquiv.ofBijective (G0ModField.KernelField.endBC A Ω)
    ⟨G0ModField.KernelField.endBC_injective A Ω, hsurj⟩
  let e' : PkgI3.AbVar.End0 A ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) (Kd d) :=
    (Algebra.TensorProduct.congr AlgEquiv.refl β.toIntAlgEquiv).trans e
  let tm := TensorProduct.mk ℤ ℚ (PkgI3.AbVar.End A) 1
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) tm :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ tm).mpr
      (TensorProduct.isBaseChange (R := ℤ) (M := PkgI3.AbVar.End A) (S := ℚ))
  have hinj : ∀ m : PkgI3.AbVar.End A, (1 : ℚ) ⊗ₜ[ℤ] m = 0 → m = 0 := by
    intro m hm
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ) tm).mp hm
    rw [Submonoid.smul_def] at hs
    have hs0 : (s : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero s
    have hsurjs := (_root_.ZInQ.Contrib.AbVarBC.mulIsogeny L A (s : ℤ) hs0).2
    apply cancel_surj ((s : ℤ) : PkgI3.AbVar.End A) hsurjs
    rw [cmp_intCast_left, hs, cmp_zero_right]
  obtain ⟨n, hn, f, hf⟩ := exists_scaledMatrixUnits e' hinj
  obtain ⟨E, i, h, Pr, -, hih, -, hE1, hPr, hprod, φ, hφ⟩ := matrixUnit_isogeny L A hA n hn f hf
  obtain ⟨k, i1, i2, R, hR, hcm⟩ := hCO L A hA Ω d hd ⟨e⟩ E hE1 i h n hn hih
  exact ⟨E, Pr, k, i1, i2, R, hE1, hPr, hprod, ⟨φ, hφ⟩, hR, hcm⟩


end FibreSplit
end CMBranch
end HDec

