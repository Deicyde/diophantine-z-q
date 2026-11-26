import ZInQKernel.Contrib.OneProof.EllAdic.PadicCoefficientEquivV1

set_option autoImplicit false

namespace RC53.EllAdic

/-- The actual transition in the tower of finite p-power residues. -/
def padicResidueProjection (p : ℕ) {m n : ℕ} (h : m ≤ n) :
    ZMod (p ^ n) →+* ZMod (p ^ m) :=
  ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))

lemma padicResidueProjection_refl (p n : ℕ) :
    padicResidueProjection p (le_refl n) = RingHom.id (ZMod (p ^ n)) :=
  ZMod.castHom_self

lemma padicResidueProjection_comp (p : ℕ) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (padicResidueProjection p hmn).comp (padicResidueProjection p hnk) =
      padicResidueProjection p (hmn.trans hnk) :=
  ZMod.castHom_comp (pow_dvd_pow p hmn) (pow_dvd_pow p hnk)

lemma padicResidueProjection_surjective (p : ℕ) {m n : ℕ} (h : m ≤ n) :
    Function.Surjective (padicResidueProjection p h) :=
  ZMod.ringHom_surjective _

/-- Sections of the locally constant residue presheaves lift across the actual
finite transition, even though a set-theoretic section need not be additive. -/
theorem locallyConstantResidue_lift (p : ℕ) {m n : ℕ} (h : m ≤ n)
    {U : Type*} [TopologicalSpace U] (r : U → ZMod (p ^ m)) (hr : IsLocallyConstant r) :
    ∃ s : U → ZMod (p ^ n), IsLocallyConstant s ∧
      ∀ x, padicResidueProjection p h (s x) = r x := by
  let lift (a : ZMod (p ^ m)) : ZMod (p ^ n) :=
    Classical.choose (padicResidueProjection_surjective p h a)
  refine ⟨lift ∘ r, hr.comp lift, ?_⟩
  intro x
  exact Classical.choose_spec (padicResidueProjection_surjective p h (r x))

/-- The succession condition in `CompatibleResidues` gives the compatibility
for every order arrow, using the same actual continuous lift. -/
lemma compatibleResidues_cast_eq {p : ℕ} [Fact p.Prime] {U : Type*} [TopologicalSpace U]
    (r : CompatibleResidues p U) {m n : ℕ} (h : m ≤ n) (x : U) :
    padicResidueProjection p h (r.1 n x) = r.1 m x := by
  change (ZMod.cast (r.1 n x) : ZMod (p ^ m)) = r.1 m x
  rw [← reduce_continuousResidueLift r n x, PadicInt.cast_toZModPow m n h,
    reduce_continuousResidueLift r m x]

end RC53.EllAdic
