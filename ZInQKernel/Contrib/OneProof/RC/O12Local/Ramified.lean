import ZInQKernel.Contrib.OneProof.RC.O12Local.Galois
import ZInQKernel.Contrib.OneProof.RC.O12Local.Support
import ZInQKernel.Contrib.OneProof.RC.O12Local.Cosets

/-! What a ramified cuspidal block contributes to the characteristic-zero sum.
The actual local factor is common to all the copies supplied by degeneracies
away from (p). -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12Local

open Matrix AddressGenuine PrintsArith Symbols

variable {p : ℕ} [Fact p.Prime]
variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V]

/-- The finite operator acting in a local representation. -/
def localHecke (π : LocalAction p E V) : V →ₗ[E] V :=
  ∑ b : Fin p, π (representative p b)

/-- The (p) translates preserve the (K_1(p))-fixed space. -/
theorem localHecke_preserves {π : LocalAction p E V} {v : V}
    (hv : v ∈ levelSpace p π 1) : localHecke π v ∈ levelSpace p π 1 := by
  intro g hg
  obtain ⟨s, hs⟩ := level_one_permutes hg
  have ht (b : Fin p) : π g (π (representative p b) v) =
      π (representative p (s b)) v := by
    obtain ⟨k, hk, e⟩ := hs b
    change (π g * π (representative p b)) v = _
    rw [← map_mul, e, map_mul]
    change π (representative p (s b)) (π k v) = _
    rw [hv k hk]
  simp only [localHecke, LinearMap.sum_apply, map_sum, ht]
  exact Equiv.sum_comp s (fun b => π (representative p b) v)

/-- The operator on a conductor-one fixed line, evaluated using its normalized
induced function. No scalar property is assumed. -/
theorem localHecke_on_line {π : LocalAction p E V} {halfMod μ₁ μ₂ : LocalCharacter p E}
    (M : InducedModel p π halfMod μ₁ μ₂)
    (hhalf : (p : E) * (halfMod (uniformizer p) : E) ^ 2 = 1)
    (hdim : Module.finrank E (levelSpace p π 1) = 1)
    {v : V} (hv : v ∈ levelSpace p π 1) (h₁ : M.realize v 1 = 1)
    (hH : localHecke π v ∈ levelSpace p π 1) :
    localHecke π v =
      (((halfMod (uniformizer p))⁻¹ : Eˣ).val * (μ₁ (uniformizer p) : E)) • v := by
  let w : levelSpace p π 1 := ⟨v, hv⟩
  have hw : w ≠ 0 := by
    intro h
    have hz : v = 0 := congrArg Subtype.val h
    simp [hz] at h₁
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' w hw).mp hdim ⟨localHecke π v, hH⟩
  have hcv : c • v = localHecke π v := congrArg Subtype.val hc
  have hvalue : M.realize (localHecke π v) 1 = heckeSum p (M.realize v) 1 := by
    simp [localHecke, heckeSum, M.right_translate]
  have e := congrArg (fun x => M.realize x 1) hcv
  rw [hvalue, heckeSum_at_one_normalized p μ₁ μ₂ halfMod hhalf _ (M.covariance v)] at e
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, h₁, mul_one] at e
  rw [← hcv, e]

/-- Data of the local factor of a cuspidal constituent with primitive quadratic
nebentype (tex 9754–9756, 9773–9811). Casselman and Carayol are explicit inputs.
The unitary half-modulus is transported with the inducing characters, so both
computations use exactly the same square root. -/
structure RamifiedFactor (E : Type) [Field E] (P : O12.LocalPair p)
    (ρ : GalQ →* GL (Fin 2) E) where
  V : Type
  [addV : AddCommGroup V]
  [modV : Module E V]
  π : LocalAction p E V
  χ : LocalCharacter p E
  halfMod : LocalCharacter p E
  half_units : charTrivialAt p halfMod 0
  half_uniformizer : (p : E) * (halfMod (uniformizer p) : E) ^ 2 = 1
  central : centralAction p π χ
  level : ℕ
  level_le : level ≤ 1
  occurs : hasLevel p π level
  char_one : charConductor p χ 1
  conductor : ℕ
  exact_conductor : repConductor p π conductor
  casselman : CasselmanCases p π halfMod χ conductor
  oldspace : CasselmanOldspace p π conductor
  interchange : PrincipalInterchange p π halfMod
  reciprocity : ReciprocityAt P
  quadratic : ∀ w : weilAt P, (w : GalQ) ∈ P.Q.inertia GalQ →
    (χ (reciprocity.toUnits w) : E) = if bitChar p (w : GalQ) = 1 then 1 else -1
  carayol : ∀ μ₁ μ₂, charConductor p μ₁ 0 → charConductor p μ₂ 1 →
    Nonempty (InducedModel p π halfMod μ₁ μ₂) →
    Nonempty (CarayolPrincipal P ρ reciprocity μ₁ μ₂ halfMod)

attribute [instance] RamifiedFactor.addV RamifiedFactor.modV

/-- A generator of the actual local factor on which (H_p) and the first
Galois Frobenius line give the same scalar. Every copy of this line has
the same operator. -/
structure RamifiedLine {E : Type} [Field E] {P : O12.LocalPair p}
    {ρ : GalQ →* GL (Fin 2) E} (D : RamifiedFactor E P ρ) where
  gen : D.V
  in_line : gen ∈ levelSpace p D.π 1
  nonzero : gen ≠ 0
  basis : GL (Fin 2) E
  eigenvalue : E
  other : E
  inertia : (↑(basis * ρ P.τ * basis⁻¹) : Matrix (Fin 2) (Fin 2) E) = diagonal ![1, -1]
  frobenius : (↑(basis * ρ P.φ * basis⁻¹) : Matrix (Fin 2) (Fin 2) E) =
    diagonal ![eigenvalue, other]
  hecke : localHecke D.π gen = eigenvalue • gen

theorem RamifiedFactor.line {E : Type} [Field E] {P : O12.LocalPair p}
    {ρ : GalQ →* GL (Fin 2) E} (D : RamifiedFactor E P ρ) :
    Nonempty (RamifiedLine D) := by
  have hc := conductor_one p D.π D.χ D.central D.char_one D.exact_conductor D.occurs D.level_le
  have hπ : repConductor p D.π 1 := hc ▸ D.exact_conductor
  have hlev := newspace_one p D.π hπ D.occurs D.level_le (hc ▸ D.oldspace)
  have hdim : Module.finrank E (levelSpace p D.π 1) = 1 := by
    exact (congrArg (fun n => Module.finrank E (levelSpace p D.π n)) hlev.1).symm.trans hlev.2.2
  obtain ⟨μ₁, μ₂, h₁, h₂, hχ, ⟨M⟩⟩ :=
    ordered_principal p D.π D.halfMod D.χ D.char_one (hc ▸ D.casselman) D.interchange
  obtain ⟨C⟩ := D.carayol μ₁ μ₂ h₁ h₂ ⟨M⟩
  obtain ⟨v, hv, hval⟩ := M.normalized_generator D.half_units h₂ hπ.1
  obtain ⟨z, hz⟩ := C.on_frobenius h₁.1 D.half_units
  have ht := C.on_inertia h₁.1 D.half_units hχ D.quadratic P.inertia
  rw [P.flip] at ht
  have hflip : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
  refine ⟨⟨v, hv, ?_, C.b, _, z, ?_, hz,
    localHecke_on_line M D.half_uniformizer hdim hv hval (localHecke_preserves hv)⟩⟩
  · intro e
    simp [e] at hval
  · simpa only [ite_eq_right hflip] using ht

/-- Every multiplicity copy of the same generator carries the computed scalar. -/
theorem RamifiedLine.on_copy {E : Type} [Field E] {P : O12.LocalPair p}
    {ρ : GalQ →* GL (Fin 2) E} {D : RamifiedFactor E P ρ}
    (C : RamifiedLine D) (x : E) :
    localHecke D.π (x • C.gen) = (C.eigenvalue * x) • C.gen := by
  rw [map_smul, C.hecke, smul_smul, mul_comm x]

#print axioms localHecke_preserves
#print axioms localHecke_on_line
#print axioms RamifiedFactor.line
#print axioms RamifiedLine.on_copy

end ZInQ.Manuscript.RC.O12Local
