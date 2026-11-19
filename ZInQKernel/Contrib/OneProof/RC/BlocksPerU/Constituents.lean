import ZInQKernel.Contrib.OneProof.RC.BlocksPerU.Diamond
import ZInQKernel.Contrib.OneProof.RC.O12Formwise.Attachment
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.DiamondOperators

/-! The characteristic-zero decomposition is a spanning statement at the
intrinsic level and character of a form. The resulting coordinates retain
the dilation even when the form is viewed at the common level. -/

noncomputable section

namespace ZInQ.Manuscript.RC.BlocksPerU

open ThetaCoeff TraceLimits AddressGenuine PrintsArith
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators Classical MatrixGroups

variable {I J K L : Type} [Fintype I] [Field K] [AddCommGroup L] {ε : L →+ ZMod 2}

def IntrinsicGood (T : TypeData L ε) (m q : ℕ) : Prop := T.Good q ∧ q.Coprime m

/-- The finite inventory of normalized sources and their dilation labels,
independent of the stage's theta series. The common diamond characters
belong to the sources. -/
structure Inventory (I J K : Type) [Fintype I] [Field K] (T : TypeData L ε) (N : ℕ) where
  sourceLevel : J → ℕ
  source : ∀ s, EigenSource K (IntrinsicGood T (sourceLevel s))
  origin : I → J
  degree : I → ℕ
  degree_pos : ∀ i, 0 < degree i
  level_dvd : ∀ i, sourceLevel (origin i) * degree i ∣ N
  χ : J → (ZMod N)ˣ →* Kˣ
  χ_good : ∀ s q (hq : q.Coprime N),
    (χ s (ZMod.unitOfCoprime q hq) : K) = (source s).χ q
  independent : Function.Injective fun v : I → K => fun n : ℕ =>
    ∑ i, v i * Odd.divCoeff (source (origin i)).a (degree i) n

variable {T : TypeData L ε} {N : ℕ} {avoid : Finset ℕ} (X : Inventory I J K T N)

def Inventory.level (i : I) : ℕ := X.sourceLevel (X.origin i) * X.degree i

def Inventory.expansion (i : I) : ℕ → K :=
  Odd.divCoeff (X.source (X.origin i)).a (X.degree i)

def restrictSource {P Q : ℕ → Prop} (h : ∀ q, Q q → P q) :
    EigenSource K P → EigenSource K Q
  | .cusp a χ hz hr => .cusp a χ hz fun q hq => hr q (h q hq)
  | .eis α β => .eis α β

@[simp] theorem restrictSource_a {P Q : ℕ → Prop} (h : ∀ q, Q q → P q)
    (s : EigenSource K P) : (restrictSource h s).a = s.a := by cases s <;> rfl

@[simp] theorem restrictSource_χ {P Q : ℕ → Prop} (h : ∀ q, Q q → P q)
    (s : EigenSource K P) : (restrictSource h s).χ = s.χ := by cases s <;> rfl

variable (hc : ∀ q, Test T avoid q → q.Coprime N)

def Inventory.baseAt (i : I) : EigenSource K (Test T avoid) :=
  restrictSource (fun q hq =>
    ⟨hq.1, (hc q hq).of_dvd_right ((dvd_mul_right _ _).trans (X.level_dvd i))⟩)
      (X.source (X.origin i))

@[simp] theorem Inventory.baseAt_a (i : I) :
    (X.baseAt hc i).a = (X.source (X.origin i)).a := by
  unfold Inventory.baseAt
  cases X.source (X.origin i) <;> rfl

@[simp] theorem Inventory.baseAt_χ (i : I) :
    (X.baseAt hc i).χ = (X.source (X.origin i)).χ := by
  unfold Inventory.baseAt
  cases X.source (X.origin i) <;> rfl

def Inventory.toBasis : Basis I K (ZMod N)ˣ (Test T avoid) where
  base := X.baseAt hc
  degree := X.degree
  degree_pos := X.degree_pos
  prime _ hq := hq.1.1
  degree_coprime i q hq :=
    ((hc q hq).of_dvd_right ((dvd_mul_left _ _).trans (X.level_dvd i))).symm
  χ i := X.χ (X.origin i)
  atPrime q := ZMod.unitOfCoprime q.val (hc q.val q.property)
  χ_good i q := by simpa using X.χ_good (X.origin i) q.val (hc q.val q.property)
  independent := by simpa only [Inventory.baseAt_a] using X.independent

/-- A genuine complex weight-two modular form with a specified pulled-back
character and the indicated positive Fourier expansion. The zero slot is
unused here. The comparison map is algebraic, with no continuity requirement. -/
def HasWeightTwoExpansion (κ : K →+* ℂ) {m : ℕ} (hm : m ∣ N)
    (χ : (ZMod N)ˣ →* Kˣ) (a : ℕ → K) : Prop :=
  ∃ (ξ : (ZMod m)ˣ →* ℂˣ) (f : ModularForm ((Gamma1 m).map (mapGL ℝ)) 2),
    ξ.comp (ZMod.unitsMap hm) = (Units.map κ).comp χ ∧
    f ∈ modFormCharSpace 2 ξ ∧
    ∀ n ≠ 0, (qExpansion 1 (⇑f)).coeff n = κ (a n)

/-- The common inventory spans the positive expansions at each lower level
and character, over the chosen coefficient field. This is the usual
characterwise oldform and Eisenstein spanning assertion expressed in Fourier
coefficients. It is independent of the theta source and of Galois attachments. -/
def SpansAt (κ : K →+* ℂ) : Prop :=
  ∀ (m : ℕ) (hm : m ∣ N) (χ : (ZMod N)ˣ →* Kˣ) (a : ℕ → K),
    a 0 = 0 → HasWeightTwoExpansion κ hm χ a →
    a ∈ Submodule.span K {c | ∃ i, X.level i ∣ m ∧ X.χ (X.origin i) = χ ∧ X.expansion i = c}

theorem coordinates_of_span {m : ℕ} {χ : (ZMod N)ˣ →* Kˣ} {a : ℕ → K}
    (ha : a ∈ Submodule.span K
      {c | ∃ i, X.level i ∣ m ∧ X.χ (X.origin i) = χ ∧ X.expansion i = c}) :
    ∃ v : I → K, (∀ n, (X.toBasis hc).eval n v = a n) ∧
      ∀ i, v i ≠ 0 → X.level i ∣ m ∧ X.χ (X.origin i) = χ := by
  classical
  induction ha using Submodule.span_induction with
  | mem c h =>
    obtain ⟨i, hm, hχ, rfl⟩ := h
    refine ⟨fun j => if j = i then 1 else 0, ?_, ?_⟩
    · intro n
      simp [Basis.eval, Inventory.toBasis, Inventory.expansion, Finset.sum_ite_eq']
    · intro j hj
      by_cases hji : j = i
      · subst j; exact ⟨hm, hχ⟩
      · exact (hj (ite_eq_right hji)).elim
  | zero => exact ⟨0, by simp, fun i hi => (hi rfl).elim⟩
  | add x y _ _ hx hy =>
    obtain ⟨v, hev, hv⟩ := hx
    obtain ⟨w, hew, hw⟩ := hy
    refine ⟨v + w, fun n => by rw [map_add, hev, hew]; rfl, ?_⟩
    intro i hi
    by_cases hvi : v i = 0
    · apply hw i
      simpa [Pi.add_apply, hvi] using hi
    · exact hv i hvi
  | smul c x _ hx =>
    obtain ⟨v, he, hv⟩ := hx
    refine ⟨c • v, fun n => by rw [map_smul, he]; rfl, ?_⟩
    intro i hi
    exact hv i (fun hz => hi (by simp [Pi.smul_apply, hz]))

theorem diamond_of_coordinates {v : I → K} {χ : (ZMod N)ˣ →* Kˣ}
    (h : ∀ i, v i ≠ 0 → X.χ (X.origin i) = χ) (u : (ZMod N)ˣ) :
    (X.toBasis hc).diamond u v = (χ u : K) • v := by
  funext i
  change (X.χ (X.origin i) u : K) * v i = (χ u : K) * v i
  by_cases hi : v i = 0
  · rw [hi, mul_zero, mul_zero]
  · rw [h i hi]

#print axioms restrictSource_a
#print axioms restrictSource_χ
#print axioms Inventory.baseAt_a
#print axioms Inventory.baseAt_χ
#print axioms Inventory.toBasis
#print axioms coordinates_of_span
#print axioms diamond_of_coordinates

end ZInQ.Manuscript.RC.BlocksPerU
