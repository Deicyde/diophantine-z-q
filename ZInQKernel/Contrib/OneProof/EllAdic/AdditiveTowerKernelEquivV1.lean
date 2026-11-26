import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Pi.Lemmas

set_option autoImplicit false

namespace RC53.EllAdic

universe u v

section AdditiveTowers

variable {A : ℕ → Type u} {B : ℕ → Type v}
  [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)]
variable (rA : ∀ n, A (n+1) →+ A n) (rB : ∀ n, B (n+1) →+ B n)
variable (dA : (∀ n, A n) →+ (∀ n, A n)) (dB : (∀ n, B n) →+ (∀ n, B n))
variable (hdA : ∀ x n, dA x n = x n - rA n (x (n+1)))
variable (hdB : ∀ x n, dB x n = x n - rB n (x (n+1)))
variable (f : ∀ n, A n →+ B n)
variable (natural : ∀ n x, rB n (f (n+1) x) = f n (rA n x))

include hdA in
private theorem compatible_of_mem_diffKer (x : ↥dA.ker) (n : ℕ) : rA n (x.val (n+1)) = x.val n := by
  have h : dA x.val = 0 := AddMonoidHom.mem_ker.mp x.property
  have h' : dA x.val n = 0 := congrArg (fun v : ∀ j, A j => v n) h
  exact (sub_eq_zero.mp ((hdA x.val n).symm.trans h')).symm

include hdA in
private theorem mem_diffKer_of_compatible {x : ∀ n, A n}
    (h : ∀ n, rA n (x (n+1)) = x n) : x ∈ dA.ker := by
  apply AddMonoidHom.mem_ker.mpr
  exact funext (fun n => (hdA x n).trans (sub_eq_zero.mpr (h n).symm))

/-- The map between the concrete kernels uses the actual finite maps. -/
def additiveTowerKernelMap : ↥dA.ker →+ ↥dB.ker where
  toFun x := ⟨fun n => f n (x.val n), mem_diffKer_of_compatible rB dB hdB fun n =>
    (natural n (x.val (n+1))).trans (congrArg (f n) (compatible_of_mem_diffKer rA dA hdA x n))⟩
  map_zero' := Subtype.ext (funext fun n => (f n).map_zero)
  map_add' x y := Subtype.ext (funext fun n => (f n).map_add (x.val n) (y.val n))

/-- Coordinatewise bijectivity and the actual adjacent squares suffice. -/
theorem additiveTowerKernelMap_bijective (hf : ∀ n, Function.Bijective (f n)) :
    Function.Bijective (additiveTowerKernelMap rA rB dA dB hdA hdB f natural) := by
  constructor
  · intro x y h
    apply Subtype.ext
    funext n
    apply (hf n).1
    exact congrArg (fun z : ↥dB.ker => z.val n) h
  · intro y
    let e (n : ℕ) := AddEquiv.ofBijective (f n) (hf n)
    let x (n : ℕ) := (e n).symm (y.val n)
    have hx (n : ℕ) : f n (x n) = y.val n := (e n).apply_symm_apply _
    have hc (n : ℕ) : rA n (x (n+1)) = x n := by
      apply (hf n).1
      exact (natural n (x (n+1))).symm.trans
        ((congrArg (rB n) (hx (n+1))).trans
          ((compatible_of_mem_diffKer rB dB hdB y n).trans (hx n).symm))
    exact ⟨⟨x, mem_diffKer_of_compatible rA dA hdA hc⟩, Subtype.ext (funext hx)⟩

/-- The kernel comparison is an additive equivalence with the same coordinate maps. -/
noncomputable def additiveTowerKernelEquiv (hf : ∀ n, Function.Bijective (f n)) : ↥dA.ker ≃+ ↥dB.ker :=
  AddEquiv.ofBijective (additiveTowerKernelMap rA rB dA dB hdA hdB f natural)
    (additiveTowerKernelMap_bijective rA rB dA dB hdA hdB f natural hf)

/-- Applying the actual finite map to a coordinate of the inverse recovers
that coordinate, without unfolding any underlying additive group. -/
theorem additiveTowerKernelEquiv_symm_coordinate (hf : ∀ n, Function.Bijective (f n))
    (y : ↥dB.ker) (n : ℕ) :
    f n (((additiveTowerKernelEquiv rA rB dA dB hdA hdB f natural hf).symm y).val n) = y.val n :=
  congrArg (fun z : ↥dB.ker => z.val n)
    ((additiveTowerKernelEquiv rA rB dA dB hdA hdB f natural hf).apply_symm_apply y)

end AdditiveTowers

end RC53.EllAdic
