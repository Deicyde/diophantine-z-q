import ZInQKernel.Contrib.OneProof.EllAdic.PadicEtaleHOneAssemblyV2
import ZInQKernel.Contrib.OneProof.EllAdic.PadicEtaleHOneGeometryFiniteMapsV1
import ZInQKernel.Contrib.OneProof.EllAdic.EtaleConstantResidueHOneTorsionV1
import ZInQKernel.Contrib.OneProof.EllAdic.PadicResidueKernelLinearV1

/-!
# Integral étale cohomology as compatible families, and its pullback

`(etaleResidueHOneSubShift S p).ker` is the group of compatible families of classes in
`H¹(S_et, ℤ/pⁿ)` on the small étale site of `S`, i.e. `lim_n H¹(S_et, ℤ/pⁿ)`. This file

* gives it its `ℤ_p`-module structure (`etaleHOneKernelModule`: at depth `n`, `a ∈ ℤ_p` acts
  through its residue mod `pⁿ`; the same recipe as `etaleResidueHOneKernelModule`);
* proves that the finite pullback `etaleResidueHOne_rebase σ p n` along a scheme isomorphism
  commutes with the reductions (`etaleResidueHOne_rebase_reduction`), and so defines the pullback
  of compatible families (`etaleResidueHOneKernel_rebase`).

This file uses no vendored source.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped RC53.EllAdic.FiniteAbDictionary

namespace RC53.EllAdic

universe u

local instance kernelRebaseEtaleEquivalence {S T : Scheme.{u}} (σ : S ≅ T) :
    (etaleAbRebasePullback σ).IsEquivalence :=
  inferInstanceAs (etaleAbRebaseEquivalence σ).functor.IsEquivalence

local instance kernelRebaseEtaleAdditive {S T : Scheme.{u}} (σ : S ≅ T) :
    (etaleAbRebasePullback σ).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- `ℤ_p` acts on compatible étale families through the residues mod `pⁿ` at depth `n`. -/
@[instance_reducible]
noncomputable def etaleHOneKernelModule (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] :
    Module ℤ_[p] ↥(etaleResidueHOneSubShift S p).ker :=
  padicResidueKernelModule (p := p) (fun n x => etaleConstantResidue_hOne_nsmul_eq_zero S p n x)
    (etaleResidueHOneReduction S p) (etaleResidueHOneSubShift S p) (fun _ _ => rfl)

/-- The finite étale pullback commutes with the reduction `ℤ/pⁿ⁺¹ → ℤ/pⁿ`. -/
theorem etaleResidueHOne_rebase_reduction {S T : Scheme.{u}} (σ : S ≅ T) (p n : ℕ)
    (y : etaleResidueHOne T p (n + 1)) :
    etaleResidueHOneReduction S p n (etaleResidueHOne_rebase σ p (n + 1) y) =
      etaleResidueHOne_rebase σ p n (etaleResidueHOneReduction T p n y) :=
  extOneTransport_postcomp (etaleAbRebasePullback σ)
    ((etaleConstantRebaseIso σ).hom.app FiniteAbDictionary.zCoeff)
    ((etaleConstantRebaseIso σ).inv.app (liftedResidueCoefficient.{u} p (n + 1)))
    ((etaleConstantRebaseIso σ).inv.app (liftedResidueCoefficient.{u} p n))
    ((constantSheaf T.smallEtaleTopology Ab.{u+1}).map
      (liftedResidueCoefficientTransition.{u} p (Nat.le_succ n)))
    ((constantSheaf S.smallEtaleTopology Ab.{u+1}).map
      (liftedResidueCoefficientTransition.{u} p (Nat.le_succ n)))
    ((etaleConstantRebaseIso σ).inv.naturality
      (liftedResidueCoefficientTransition.{u} p (Nat.le_succ n))) y

/-- The coordinatewise pullback of a compatible family is compatible. -/
theorem etaleResidueHOne_rebase_mem_ker {S T : Scheme.{u}} (σ : S ≅ T) (p : ℕ)
    (y : ↥(etaleResidueHOneSubShift T p).ker) :
    (fun n => etaleResidueHOne_rebase σ p n (y.1 n)) ∈ (etaleResidueHOneSubShift S p).ker := by
  rw [AddMonoidHom.mem_ker]
  funext n
  have hy : y.1 n - etaleResidueHOneReduction T p n (y.1 (n + 1)) = 0 :=
    congrFun (AddMonoidHom.mem_ker.mp y.2) n
  change etaleResidueHOne_rebase σ p n (y.1 n) -
      etaleResidueHOneReduction S p n (etaleResidueHOne_rebase σ p (n + 1) (y.1 (n + 1))) = 0
  rw [etaleResidueHOne_rebase_reduction, sub_eq_zero.mp hy, sub_self]

/-- The pullback of compatible étale families along `σ : S ≅ T`, coordinatewise. -/
noncomputable def etaleResidueHOneKernel_rebase {S T : Scheme.{u}} (σ : S ≅ T) (p : ℕ) :
    ↥(etaleResidueHOneSubShift T p).ker →+ ↥(etaleResidueHOneSubShift S p).ker where
  toFun y := ⟨fun n => etaleResidueHOne_rebase σ p n (y.1 n), etaleResidueHOne_rebase_mem_ker σ p y⟩
  map_zero' := by
    apply Subtype.ext
    funext n
    exact map_zero (etaleResidueHOne_rebase σ p n)
  map_add' y y' := by
    apply Subtype.ext
    funext n
    exact map_add (etaleResidueHOne_rebase σ p n) (y.1 n) (y'.1 n)

theorem etaleResidueHOneKernel_rebase_coordinate {S T : Scheme.{u}} (σ : S ≅ T) (p : ℕ)
    (y : ↥(etaleResidueHOneSubShift T p).ker) (n : ℕ) :
    (etaleResidueHOneKernel_rebase σ p y).1 n = etaleResidueHOne_rebase σ p n (y.1 n) :=
  rfl

end RC53.EllAdic
