import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.NumberTheory.Padics.RingHoms
import ZInQKernel.Contrib.OneProof.EllAdic.PadicAddEquivLinearV1

set_option autoImplicit false

namespace RC53.EllAdic

universe u v

variable {p : ℕ} [Fact p.Prime]
variable {A : ℕ → Type u} [∀ n, AddCommGroup (A n)]

/-- Pull back the canonical `ZMod (p^n)`-module of an annihilated group along
 the actual p-adic residue homomorphism. -/
@[instance_reducible]
noncomputable def padicResidueDepthModule (kill : ∀ n (x : A n), (p ^ n : ℕ) • x = 0)
    (n : ℕ) : Module ℤ_[p] (A n) :=
  letI : Module (ZMod (p ^ n)) (A n) := AddCommGroup.zmodModule (kill n)
  Module.compHom (A n) (PadicInt.toZModPow n)

/-- Any natural representative of the residue has the same action. -/
theorem padicResidueDepth_smul_eq_nsmul
    (kill : ∀ n (x : A n), (p ^ n : ℕ) • x = 0)
    (n r : ℕ) (a : ℤ_[p]) (x : A n)
    (hr : (r : ZMod (p ^ n)) = PadicInt.toZModPow n a) :
    letI := padicResidueDepthModule (p := p) kill n
    a • x = r • x := by
  let : Module (ZMod (p ^ n)) (A n) := AddCommGroup.zmodModule (kill n)
  change (PadicInt.toZModPow n a) • x = r • x
  rw [← hr, Nat.cast_smul_eq_nsmul]

/-- Additive transitions commute with the canonical actions on successive
levels. The representative is chosen only at the deeper level. -/
theorem padicResidueDepth_transition_smul
    (kill : ∀ n (x : A n), (p ^ n : ℕ) • x = 0)
    (n : ℕ) (d : A (n + 1) →+ A n) (a : ℤ_[p]) (x : A (n + 1)) :
    letI : ∀ k, Module ℤ_[p] (A k) := padicResidueDepthModule (p := p) kill
    d (a • x) = a • d x := by
  let : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let r := (PadicInt.toZModPow (n + 1) a).val
  have hd : (r : ZMod (p ^ (n + 1))) = PadicInt.toZModPow (n + 1) a :=
    ZMod.natCast_zmod_val _
  let c : ZMod (p ^ (n + 1)) →+* ZMod (p ^ n) :=
    ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) _
  have low : (r : ZMod (p ^ n)) = PadicInt.toZModPow n a := by
    calc
      _ = c (r : ZMod (p ^ (n + 1))) := (map_natCast c r).symm
      _ = c (PadicInt.toZModPow (n + 1) a) := congrArg c hd
      _ = _ := PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n) a
  exact (congrArg d (padicResidueDepth_smul_eq_nsmul kill (n + 1) r a x hd)).trans
    ((map_nsmul d r x).trans (padicResidueDepth_smul_eq_nsmul kill n r a (d x) low).symm)

/-- The literal additive kernel of the difference map is stable under the
pointwise residue action. Its carrier is not redefined by an isomorphism. -/
def padicResidueKernelSubmodule
    (kill : ∀ n (x : A n), (p ^ n : ℕ) • x = 0)
    (d : ∀ n, A (n + 1) →+ A n)
    (δ : (∀ n, A n) →+ (∀ n, A n))
    (hδ : ∀ (x : ∀ n, A n) (n : ℕ), δ x n = x n - d n (x (n + 1))) :
    letI : ∀ n, Module ℤ_[p] (A n) := padicResidueDepthModule (p := p) kill
    Submodule ℤ_[p] (∀ n, A n) := by
  letI : ∀ n, Module ℤ_[p] (A n) := padicResidueDepthModule (p := p) kill
  refine { δ.ker.toAddSubmonoid with smul_mem' := ?_ }
  intro a x hx
  change δ (a • x) = 0
  have hx0 : δ x = 0 := hx
  funext n
  rw [hδ]
  have hxn := sub_eq_zero.mp ((hδ x n).symm.trans (congrFun hx0 n))
  change a • x n - d n (a • x (n + 1)) = 0
  exact sub_eq_zero.mpr ((congrArg (fun z : A n => a • z) hxn).trans
    (padicResidueDepth_transition_smul kill n (d n) a (x (n + 1))).symm)

/-- The submodule has exactly the original kernel as its additive subgroup. -/
theorem padicResidueKernelSubmodule_toAddSubgroup
    (kill : ∀ n (x : A n), (p ^ n : ℕ) • x = 0)
    (d : ∀ n, A (n + 1) →+ A n)
    (δ : (∀ n, A n) →+ (∀ n, A n))
    (hδ : ∀ (x : ∀ n, A n) (n : ℕ), δ x n = x n - d n (x (n + 1))) :
    (padicResidueKernelSubmodule (p := p) kill d δ hδ).toAddSubgroup = δ.ker := by
  ext x
  rfl

end RC53.EllAdic
