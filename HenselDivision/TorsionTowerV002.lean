import HenselDivision.TorsionSpecializationV002

/-!
# Compatible `ℓ`-power torsion towers over a henselian local ring

`G` a group scheme over `Spec R`, `R` henselian local. If multiplication by `ℓ` is étale on `G`,
then so is multiplication by every `ℓ^n` (`[ℓ^n]` is the `n`-fold composite of `[ℓ]`), and every
compatible system of residual torsion points `x_n ∈ G(s)`, `x_0 = 1`, `x_{n+1}^ℓ = x_n`, lifts to a
unique compatible system of integral points `f_n ∈ G(S)` with `f_n|_s = x_n`. The lift at each
level is the unique Hensel lift on the étale torsion scheme `G[ℓ^n]`; compatibility of the lifts is
forced by uniqueness at the lower level, not assumed. No commutativity and no finiteness of
`G[ℓ^n]` are used.

Edition V002: direction of one rewrite. Statements as in V001.
-/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
  IsLocalRing
open scoped MonObj

namespace HenselDivision

universe v w u

lemma powHom_mul {C : Type w} [Category.{v} C] [CartesianMonoidalCategory C] (G : C) [MonObj G]
    (a b : ℕ) : powHom G (a * b) = powHom G a ≫ powHom G b := by
  rw [comp_powHom, powHom, powHom, pow_mul]

/-- `[ℓ]` étale implies `[ℓ^n]` étale for every `n`. -/
lemma etale_powHom_pow {S : Scheme.{u}} (G : Over S) [GrpObj G] (ℓ : ℕ)
    (h : Etale (powHom G ℓ).left) : ∀ n : ℕ, Etale (powHom G (ℓ ^ n)).left
  | 0 => by
    rw [pow_zero, powHom, pow_one, Over.id_left]
    infer_instance
  | n + 1 => by
    rw [pow_succ, powHom_mul, Over.comp_left]
    have := etale_powHom_pow G ℓ h n
    infer_instance

variable {R : Type u} [CommRing R] [HenselianLocalRing R]

lemma pow_pow_eq_one_of_tower {M : Type*} [Monoid M] (ℓ : ℕ) (x : ℕ → M) (hx0 : x 0 = 1)
    (hx : ∀ n, x (n + 1) ^ ℓ = x n) : ∀ n, x n ^ (ℓ ^ n) = 1
  | 0 => by rw [pow_zero, pow_one, hx0]
  | n + 1 => by rw [pow_succ', pow_mul, hx n, pow_pow_eq_one_of_tower ℓ x hx0 hx n]

/-- **Unique integral lift of a compatible residual torsion tower.** -/
theorem compatible_lift_existsUnique (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (ℓ : ℕ)
    (hℓ : Etale (powHom G ℓ).left) (x : ℕ → (closedObj R ⟶ G)) (hx0 : x 0 = 1)
    (hx : ∀ n, x (n + 1) ^ ℓ = x n) :
    ∃! f : ℕ → (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G),
      f 0 = 1 ∧ (∀ n, f (n + 1) ^ ℓ = f n) ∧ ∀ n, toUnit (closedObj R) ≫ f n = x n := by
  have hxt := pow_pow_eq_one_of_tower ℓ x hx0 hx
  have B : ∀ n, _ := fun n => torsion_restrict_bijective G (ℓ ^ n) (etale_powHom_pow G ℓ hℓ n)
  -- uniqueness of integral `ℓ^n`-torsion points with given restriction
  have uniq : ∀ n (g g' : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G), g ^ (ℓ ^ n) = 1 →
      g' ^ (ℓ ^ n) = 1 → toUnit (closedObj R) ≫ g = toUnit (closedObj R) ≫ g' → g = g' := by
    intro n g g' hg hg' h
    have := (B n).1 (a₁ := ⟨g, hg⟩) (a₂ := ⟨g', hg'⟩) (Subtype.ext h)
    exact congrArg Subtype.val this
  choose F hF using fun n => (B n).2 ⟨x n, hxt n⟩
  let f : ℕ → (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G) := fun n => (F n).1
  have hfres : ∀ n, toUnit (closedObj R) ≫ f n = x n := fun n => congrArg Subtype.val (hF n)
  have hft : ∀ n, f n ^ (ℓ ^ n) = 1 := fun n => (F n).2
  have hf0 : f 0 = 1 := by
    have := hft 0
    rwa [pow_zero, pow_one] at this
  have hfs : ∀ n, f (n + 1) ^ ℓ = f n := by
    intro n
    apply uniq n
    · rw [← pow_mul, ← pow_succ']; exact hft (n + 1)
    · exact hft n
    · rw [MonObj.comp_pow, hfres, hfres, hx]
  refine ⟨f, ⟨hf0, hfs, hfres⟩, ?_⟩
  rintro f' ⟨h0, hs, hres⟩
  funext n
  apply uniq n
  · exact pow_pow_eq_one_of_tower ℓ f' h0 hs n
  · exact hft n
  · rw [hres, hfres]

end HenselDivision

#check @HenselDivision.etale_powHom_pow
#check @HenselDivision.compatible_lift_existsUnique
#print axioms HenselDivision.etale_powHom_pow
#print axioms HenselDivision.compatible_lift_existsUnique
