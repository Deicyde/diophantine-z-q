/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_PDivisibleGroup_CharacterDifferential
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_PDivisibleGroup_CartierDuality
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_PDivisibleGroup_Dimension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

noncomputable section

open Coalgebra Bialgebra
open scoped TensorProduct

namespace PDivisibleGroup

variable {R : Type} [CommRing R] {p h : ℕ}

section CotangentClass

variable (G : PDivisibleGroup R p h)

def cotangentClass (v : ℕ) : G.level v →ₗ[R] G.Cotangent v where
  toFun a := (G.augIdeal v).toCotangent
    ⟨a - algebraMap R (G.level v) (counit (R := R) a), Hopf.sub_algebraMap_counit_mem_augIdeal R _ a⟩
  map_add' a b := by
    rw [← map_add]
    congr 1
    ext
    change a + b - algebraMap R (G.level v) (counit (R := R) (a + b)) =
      (a - algebraMap R (G.level v) (counit (R := R) a)) + (b - algebraMap R (G.level v) (counit (R := R) b))
    rw [map_add, map_add]
    abel
  map_smul' r a := by
    rw [RingHom.id_apply, ← LinearMap.map_smul_of_tower]
    congr 1
    ext
    change r • a - algebraMap R (G.level v) (counit (R := R) (r • a)) =
      r • (a - algebraMap R (G.level v) (counit (R := R) a))
    rw [map_smul, smul_sub, Algebra.smul_def r (algebraMap R (G.level v) _), ← map_mul, smul_eq_mul]

theorem cotangentClass_apply (v : ℕ) (a : G.level v) :
    G.cotangentClass v a = (G.augIdeal v).toCotangent
      ⟨a - algebraMap R (G.level v) (counit (R := R) a),
        Hopf.sub_algebraMap_counit_mem_augIdeal R _ a⟩ := rfl

theorem cotangentClass_of_mem (v : ℕ) (a : G.augIdeal v) :
    G.cotangentClass v a = (G.augIdeal v).toCotangent a := by
  rw [cotangentClass_apply]
  congr 1
  ext
  change (a : G.level v) - algebraMap R (G.level v) (counit (R := R) (a : G.level v)) = a
  rw [(G.mem_augIdeal_iff v a).mp a.2, map_zero, sub_zero]

@[simp] theorem cotangentClass_one (v : ℕ) : G.cotangentClass v 1 = 0 := by
  rw [cotangentClass_apply, ← map_zero (G.augIdeal v).toCotangent]
  congr 1
  ext
  change (1 : G.level v) - algebraMap R (G.level v) (counit (R := R) (1 : G.level v)) = 0
  rw [Bialgebra.counit_one, map_one, sub_self]

@[simp] theorem cotangentClass_algebraMap (v : ℕ) (r : R) :
    G.cotangentClass v (algebraMap R (G.level v) r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, cotangentClass_one, smul_zero]

end CotangentClass

namespace CartierDuality

variable {G G' : PDivisibleGroup R p h} (D : CartierDuality G G')
variable (S : Type) [CommRing S] [Algebra R S]

def charElem (v : ℕ) (ψ : G'.Point S v) : S ⊗[R] G.level v :=
  ∑ i, Point.toAlgHom ψ ((D.toDualEquiv v).symm ((Module.Free.chooseBasis R (G.level v)).coord i)) ⊗ₜ[R]
    Module.Free.chooseBasis R (G.level v) i

theorem charElem_def (v : ℕ) (ψ : G'.Point S v) :
    D.charElem S v ψ = ∑ i, Point.toAlgHom ψ ((D.toDualEquiv v).symm
      ((Module.Free.chooseBasis R (G.level v)).coord i)) ⊗ₜ[R] Module.Free.chooseBasis R (G.level v) i :=
  rfl

def charDiff (v : ℕ) (ψ : G'.Point S v) : S ⊗[R] G.Cotangent v :=
  (G.cotangentClass v).lTensor S (D.charElem S v ψ)

theorem charDiff_def (v : ℕ) (ψ : G'.Point S v) :
    D.charDiff S v ψ = (G.cotangentClass v).lTensor S (D.charElem S v ψ) := rfl

theorem charDiff_eq_sum (v : ℕ) (ψ : G'.Point S v) :
    D.charDiff S v ψ = ∑ i, Point.toAlgHom ψ ((D.toDualEquiv v).symm
      ((Module.Free.chooseBasis R (G.level v)).coord i)) ⊗ₜ[R]
        G.cotangentClass v (Module.Free.chooseBasis R (G.level v) i) := by
  rw [charDiff_def, charElem_def, map_sum]
  rfl

end CartierDuality

end PDivisibleGroup

end
