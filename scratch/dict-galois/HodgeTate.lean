import ZInQKernel.OneProof.H.TailS
import ZInQKernel.OneProof.H.TailQ
import ZInQKernel.OneProof.H.LF4T5
import ZInQKernel.Contrib.AbVarBC.G9Instance

/-!
# dict-galois (4): `hodgeTateDecompAbVar` without the dimension of `t*_{A'}`

The chain's field `hodgeTateDecompAbVar : ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar` (`TailS.lean`) writes the
Hodge–Tate decomposition `ℂ_p ⊗ V_p(A) ≅ (ℂ_p(1) ⊗_F t_A) ⊕ (ℂ_p ⊗_F t*_{A'})` in coordinates
`ℂ_p(1)^g ⊕ ℂ_p^g`; the second exponent is `dim_F t*_{A'} = dim A' = g`, a statement about the dual abelian
variety. The new leaf `HodgeTateDecompAbVarPrinted` leaves that exponent unnamed (`ℂ_p(1)^g ⊕ ℂ_p^b`, some `b`),
and the field follows from `dim V_p(A) = 2g`, which the chain has: T26 (`T_p A` free of rank `2 dim A`) is proved
from the textbook field `mumfordTorsionAlgClosed` (`AvSplit.Final.h25`, `T5Torsion.TateFree`).
-/

set_option linter.style.longLine false

namespace HodgeTateDict

open ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
open scoped TensorProduct

noncomputable section

/-- **LEAF (Hodge–Tate decomposition of the Tate module of an abelian variety, second exponent unnamed).**
Fontaine, *Formes différentielles et modules de Tate des variétés abéliennes sur les corps locaux*, Invent. Math.
65 (1982), 379-409, Théorème principal (with Tate 1967 §4, Cor. 2 of Thm 3, for good reduction, and Faltings,
JAMS 1 (1988)); locators UNVERIFIED. For an abelian variety `A` of dimension `g` over a finite extension `F` of
`ℚ_p` there is a `G_F`-equivariant `ℂ_p`-linear isomorphism
`ℂ_p ⊗_{ℚ_p} V_p(A) ≅ (ℂ_p(1) ⊗_F t_A) ⊕ (ℂ_p ⊗_F t*_{A'})`. Lean form: after choosing `F`-bases of `t_A`
(dimension `g = dim A`, the tangent space of a smooth group variety of dimension `g`) and of `t*_{A'}`
(dimension `b`, not named), `ℂ_p(1)^g ⊕ ℂ_p^b`; `G_F` acts on `ℂ_p ⊗ V` by `σ ⊗ ρ(σ)` and on `ℂ_p(1)` by
`c ↦ χ(σ) σ(c)`, through pkg-I4's `gfToGqp`. Same as the chain's `HodgeTateDecompAbVar` except that the
dimension of the second factor is existential, so no fact about the dual abelian variety is used. -/
def HodgeTateDecompAbVarPrinted : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∃ (b : ℕ) (e : ℂ_[p] ⊗[ℚ_[p]] A.V p ≃ₗ[ℂ_[p]] (Fin g → ℂ_[p]) × (Fin b → ℂ_[p])),
      ∀ (σ : Field.absoluteGaloisGroup F) (x : ℂ_[p] ⊗[ℚ_[p]] A.V p),
        e (TensorProduct.map (cpLin p (gfToGqp p F σ)) (A.galRep p σ) x) =
          ((fun k => cycPow p (gfToGqp p F σ) 1 • cpAct p (gfToGqp p F σ) ((e x).1 k)),
            (fun k => cpAct p (gfToGqp p F σ) ((e x).2 k)))

variable (p : ℕ) [Fact p.Prime]

/-- `(p : F) ≠ 0` for a `ℚ_p`-algebra `F` that is a field. -/
theorem natCast_p_ne_zero (F : Type) [Field F] [Algebra ℚ_[p] F] : (p : F) ≠ 0 := by
  have h : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [← map_natCast (algebraMap ℚ_[p] F)]
  exact (map_ne_zero_iff _ (algebraMap ℚ_[p] F).injective).mpr h

/-- The chain's `A` as a kernel `PkgI3.AbVar` (same fields). -/
def toKer {F : Type} [Field F] (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) : _root_.PkgI3.AbVar F :=
  @_root_.PkgI3.AbVar.mk F _ A.X A.grp A.proper A.smooth A.geomInt

/-- **`V_p(A)` is finite-dimensional of dimension `2 dim A`** over a field `F` with `(p : F) ≠ 0`, from T26
(`PkgI3.TateModuleFree`). -/
theorem finrank_V_of_tateModuleFree (hT : _root_.PkgI3.TateModuleFree) {F : Type} [Field F] (hp : (p : F) ≠ 0)
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞)) :
    FiniteDimensional ℚ_[p] (A.V p) ∧ finrank ℚ_[p] (A.V p) = 2 * g := by
  obtain ⟨hfree, hfin, hrk⟩ := hT F (toKer A) p hp
  have e1 : finrank ℚ_[p] (A.V p) = finrank ℤ_[p] ((toKer A).T p) :=
    ((ZInQ.Contrib.AbVarBC.vToI4 p (toKer A)).finrank_eq).trans Module.finrank_baseChange
  have hdim : (toKer A).dim = (g : WithBot ℕ∞) := hg
  rw [hdim] at hrk
  have h2 : finrank ℤ_[p] ((toKer A).T p) = 2 * g := by
    have h' : (((finrank ℤ_[p] ((toKer A).T p) : ℕ) : ℕ∞) : WithBot ℕ∞) =
        (((2 * g : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      rw [hrk]; push_cast; rfl
    exact Nat.cast_injective (WithBot.coe_injective h')
  refine ⟨?_, e1.trans h2⟩
  change FiniteDimensional ℚ_[p] (TensorProduct ℤ_[p] ℚ_[p] ((toKer A).T p))
  infer_instance

/-- T26 from the chain's textbook field `mumfordTorsionAlgClosed`. -/
theorem tateModuleFree_of_mumford (hM : AvSplit.MumfordTorsionAlgClosed) : _root_.PkgI3.TateModuleFree :=
  T5Torsion.TateFree.tateModuleFree_of_torsionStructure (AvSplit.Final.h25 hM)

/-- **The chain's field from the new leaf and `mumfordTorsionAlgClosed`.** -/
theorem hodgeTateDecompAbVar_of_printed (h : HodgeTateDecompAbVarPrinted)
    (hM : AvSplit.MumfordTorsionAlgClosed) : HodgeTateDecompAbVar := by
  intro p _ F _ _ _ A g hg
  obtain ⟨b, e, he⟩ := h p F A g hg
  have hb : b = g := by
    have h1 := e.finrank_eq
    rw [Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fin_fun,
      Module.finrank_fin_fun] at h1
    have h2 := (finrank_V_of_tateModuleFree p (tateModuleFree_of_mumford hM)
      (natCast_p_ne_zero p F) A g hg).2
    omega
  subst hb
  exact ⟨e, he⟩

end

end HodgeTateDict
