import Mathlib

/-!
# Integral maps of finite cyclotomic group rings (K10), (E.2)

A weighted pushforward on group bases. The construction works on integral coefficients
and modulo every power of two. It uses neither an idempotent nor an averaged trace.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AppEK1

variable {R A B C : Type*} [CommRing R] [Group A] [Group B] [Group C]

/-- The map `[s] ↦ χ(s)[b(s)]`, with scalar and deck conventions separated. -/
def weightedMap (b : A →* B) (χ : A →* Rˣ) :
    MonoidAlgebra R A →ₐ[R] MonoidAlgebra R B :=
  MonoidAlgebra.lift R _ A
    { toFun := fun s => (χ s : R) • MonoidAlgebra.of R B (b s)
      map_one' := by simp only [map_one, Units.val_one, one_smul]
      map_mul' := by intro s t; simp only [map_mul, Units.val_mul, smul_mul_smul_comm] }

/-- Images of basis vectors, including their coefficients. -/
@[simp]
theorem weightedMap_single (b : A →* B) (χ : A →* Rˣ) (s : A) (r : R) :
    weightedMap b χ (MonoidAlgebra.single s r) = MonoidAlgebra.single (b s) (r * (χ s : R)) := by
  rw [weightedMap, MonoidAlgebra.lift_single]
  change r • ((χ s : R) • MonoidAlgebra.single (b s) 1) = _
  rw [smul_smul, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]

/-- Under inverse deck action a quadratic weight gives the *same* character in the
target action, on every group-ring element. -/
theorem weightedMap_invDeck (b : A →* B) (χ : A →* Rˣ) (hχ : ∀ g, χ g * χ g = 1)
    (g : A) (v : MonoidAlgebra R A) :
    weightedMap b χ (MonoidAlgebra.single g⁻¹ 1 * v) =
      MonoidAlgebra.single (b g)⁻¹ (χ g : R) * weightedMap b χ v := by
  rw [map_mul, weightedMap_single, one_mul, map_inv, map_inv,
    inv_eq_of_mul_eq_one_right (hχ g)]

/-- Composition of weighted coefficient maps. This gives both specialization by
a character and commutation with a deck quotient on compatible characters. -/
theorem weightedMap_comp (b : A →* B) (c : B →* C) (χ : A →* Rˣ) (η : B →* Rˣ) :
    (weightedMap c η).comp (weightedMap b χ) =
      weightedMap (c.comp b) (χ * η.comp b) := by
  apply (MonoidAlgebra.lift R (MonoidAlgebra R C) A).symm.injective
  ext s
  simp

/-- The family map (K10). The real cyclotomic quotient and the binary group are separate
factors of the target group. -/
abbrev familyMap {G : Type*} [Group G] (bar : A →* B) (ψ : A →* G) (χ₀ : A →* Rˣ) :
    MonoidAlgebra R A →ₐ[R] MonoidAlgebra R (B × G) :=
  weightedMap (bar.prod ψ) χ₀

/-- Evaluating the family at `x` gives the constituent map with its full weight.
In particular, no further sign projection is used in (E.2). -/
theorem specialize_familyMap {G : Type*} [Group G] (bar : A →* B) (ψ : A →* G)
    (χ₀ : A →* Rˣ) (x : G →* Rˣ) :
    (weightedMap (MonoidHom.fst B G) (x.comp (MonoidHom.snd B G))).comp (familyMap bar ψ χ₀) =
      weightedMap bar (χ₀ * x.comp ψ) := by
  rw [familyMap, weightedMap_comp]
  rfl

/-- Weighted pushforward commutes with passing to a smaller group-ring level when the
character already factors through the smaller level. -/
theorem weightedMap_quotient {D : Type*} [Group D]
    (p : A →* B) (q : C →* D) (bar₁ : A →* C) (bar₀ : B →* D) (χ : B →* Rˣ)
    (h : q.comp bar₁ = bar₀.comp p) :
    (weightedMap q (1 : C →* Rˣ)).comp (weightedMap bar₁ (χ.comp p)) =
      (weightedMap bar₀ χ).comp (weightedMap p (1 : A →* Rˣ)) := by
  rw [weightedMap_comp, weightedMap_comp, h]
  congr 1
  ext s
  simp

/-- The full character at a level divisible by both conductor parts. The input
on the dyadic factor is independent of the odd input; it can be nontrivial, in
particular at conductor `4`. -/
def fullWeight {a d m : ℕ} (h₂ : 2 ^ a ∣ m) (ho : d ∣ m)
    (χ₂ : (ZMod (2 ^ a))ˣ →* Rˣ) (χodd : (ZMod d)ˣ →* Rˣ) : (ZMod m)ˣ →* Rˣ :=
  χ₂.comp (Units.map (ZMod.castHom h₂ (ZMod (2 ^ a))).toMonoidHom) *
    χodd.comp (Units.map (ZMod.castHom ho (ZMod d)).toMonoidHom)

/-- Formula (E.2) on finite coefficients, with both character factors visible.
The conductor divides the source level, not necessarily the real quotient. -/
theorem weightedMap_fullWeight_single {a d m : ℕ} (h₂ : 2 ^ a ∣ m) (ho : d ∣ m)
    (χ₂ : (ZMod (2 ^ a))ˣ →* Rˣ) (χodd : (ZMod d)ˣ →* Rˣ)
    (bar : (ZMod m)ˣ →* B) (s : (ZMod m)ˣ) :
    weightedMap bar (fullWeight h₂ ho χ₂ χodd) (MonoidAlgebra.single s 1) =
      MonoidAlgebra.single (bar s)
        ((χ₂ (Units.map (ZMod.castHom h₂ (ZMod (2 ^ a))).toMonoidHom s) : R) *
          (χodd (Units.map (ZMod.castHom ho (ZMod d)).toMonoidHom s) : R)) := by
  simp [fullWeight, Units.val_mul]

end ZInQ.Manuscript.RC.AppEK1
