import ZInQKernel.Contrib.TYZGenus.Package

noncomputable section
namespace ZInQ.Contrib.TYZGenus.Package
open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields ZInQ.RouteK.Rank5b

variable (d : ℕ) [NeZero d]

/-- `H_{d,4}` restricted to `ℚ`-scalars. -/
abbrev H4Q : IntermediateField ℚ (SeparableClosure (QNeg d)) := (H4 d).restrictScalars ℚ

theorem H4bar_eq : H4bar d = (H4Q d).map (embed d) := by
  simp only [H4bar, NeZero.ne d, ↓reduceDIte]

/-- The ring automorphism of `H_{d,4}` (as `ℚ`-subfield) given by `g ∈ Gal(H_{d,4}/K_d)`. -/
def gQ (g : Gal(H4 d/QNeg d)) : H4Q d ≃+* H4Q d := g.toRingEquiv

/-- The induced automorphism of `H4bar d ⊂ ℚ̄`. -/
def gBar (g : Gal(H4 d/QNeg d)) : (H4Q d).map (embed d) ≃ₐ[ℚ] (H4Q d).map (embed d) :=
  AlgEquiv.ofRingEquiv (f := ((IntermediateField.equivMap (H4Q d) (embed d)).toRingEquiv.symm.trans
    ((gQ d g).trans (IntermediateField.equivMap (H4Q d) (embed d)).toRingEquiv)))
    (fun q => by simp)

/-- **Every `g ∈ Gal(H_{d,4}/K_d)` is induced by an automorphism of `ℚ̄`.** -/
theorem exists_actsAsArtin4 (c : Pic (O4 d)) : ∃ ρ : GalQ, ActsAsArtin4 ρ d c := by
  let χ := gBar d (artin4 d c)
  refine ⟨AlgEquiv.ofBijective (χ.toAlgHom.liftNormal Qbar) (AlgHom.normal_bijective _ _ _ _), ?_⟩
  intro x
  have hx : embed d (x : SeparableClosure (QNeg d)) =
      algebraMap ((H4Q d).map (embed d)) Qbar (IntermediateField.equivMap (H4Q d) (embed d) x) := rfl
  rw [AlgEquiv.ofBijective_apply, hx, AlgHom.liftNormal_commutes]
  have e : χ (IntermediateField.equivMap (H4Q d) (embed d) x) =
      IntermediateField.equivMap (H4Q d) (embed d) (artin4 d c x) := by
    simp only [χ, gBar, gQ, AlgEquiv.ofRingEquiv_apply]
    change IntermediateField.equivMap (H4Q d) (embed d) (artin4 d c
      ((IntermediateField.equivMap (H4Q d) (embed d)).symm
        (IntermediateField.equivMap (H4Q d) (embed d) x))) = _
    have h := AlgEquiv.symm_apply_apply (IntermediateField.equivMap (H4Q d) (embed d))
      (show ↥(H4Q d) from x)
    exact congrArg (fun y : ↥(H4Q d) => IntermediateField.equivMap (H4Q d) (embed d)
      (show ↥(H4Q d) from artin4 d c (show ↥(H4 d) from y))) h
  show algebraMap _ Qbar (χ (IntermediateField.equivMap (H4Q d) (embed d) x)) = _
  rw [e]
  rfl

omit [NeZero d] in
theorem Hprimebar_eq [NeZero d] : Hprimebar d = ((Hprime d).restrictScalars ℚ).map (embed d) := by
  simp only [Hprimebar, NeZero.ne d, ↓reduceDIte]

/-- **Galois descent to `H'_d`**: a point of `H_{d,4} ⊂ ℚ̄` fixed by every `ρ` acting as `σ_{1+2ϖ}`
lies in `H'_d`. -/
theorem mem_Hprimebar_of_fixed {x : Qbar} (hx : x ∈ H4bar d)
    (hfix : ∀ ρ : GalQ, ActsAsArtin4 ρ d (sigmaClass d) → ρ x = x) : x ∈ Hprimebar d := by
  rw [H4bar_eq] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨ρ, hρ⟩ := exists_actsAsArtin4 d (sigmaClass d)
  have h1 : ρ (embed d y) =
      embed d ((artin4 d (sigmaClass d) ⟨y, hy⟩ : H4 d) : SeparableClosure (QNeg d)) := hρ ⟨y, hy⟩
  have h0 : ρ (embed d y) = embed d y := hfix ρ hρ
  rw [h0] at h1
  have h2 : (artin4 d (sigmaClass d)) ⟨y, hy⟩ = ⟨y, hy⟩ :=
    Subtype.ext ((embed d).injective h1).symm
  rw [Hprimebar_eq]
  refine ⟨y, ?_, rfl⟩
  show y ∈ Hprime d
  rw [Hprime, show y = (⟨y, hy⟩ : H4 d).1 from rfl, IntermediateField.mem_lift,
    IntermediateField.mem_fixedField_iff]
  intro f hf
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
  have hst : artin4 d (sigmaClass d) ∈ MulAction.stabilizer (Gal(H4 d/QNeg d)) (⟨y, hy⟩ : H4 d) :=
    h2
  exact (MulAction.stabilizer _ _).zpow_mem hst k

omit [NeZero d]

/-- **Leaf GT (`i ∈ H_{n,4}`)**: for squarefree `n ≡ 5 (mod 8)`, `i` lies in the ring class field
`H_{n,4}`. Genus theory: `K_n(i) = K_n(√n)` is contained in the genus field of `K_n = ℚ(√−n)`
(`d_K = −4n`, genus field `K(√p* : p ∣ n, √−1)`; Cox, *Primes of the form x² + ny²*, Thm. 6.1 /
§6.C, UNVERIFIED numbers), hence in `H_n ⊆ H_{n,4}` (ring-class's target `HilbertLeH4`); also
`tyz-t1.md` §3.1 ("`ψ` the character of `K(i)/K = K(√n)/K`, which is unramified"). Refereed
(textbook). -/
def IInH4 : Prop := ∀ n : ℕ, n % 8 = 5 → Squarefree n → iQ ∈ H4bar n

/-- **`TYZZnOverHprime` is glue**: from the field of definition of the Heegner point
(`CMFieldOfDefinitionTYZ`, Shimura), `i ∈ H_{n,4}` (`IInH4`, genus theory) and Shimura reciprocity
in TYZ's form (`TYZSigmaFixesZn`, TYZ Cor. 3.9), by Galois descent from `H_{n,4}` to `H'_n`
(`mem_Hprimebar_of_fixed`, through Tau Ceti's Artin map and ring-class's embedding). -/
theorem tyzZnOverHprime_of (h1 : CMFieldOfDefinitionTYZ) (hi : IInH4) (hs : TYZSigmaFixesZn) :
    TYZZnOverHprime := by
  intro n hn hsq
  haveI : NeZero n := ⟨by omega⟩
  have hP := h1 n hn hsq
  have hz : tyzZn n ∈ ptsOver (H4bar n) :=
    (ptsOver (H4bar n)).sub_mem hP (iPt_mem (hi n hn hsq) hP)
  have hfixz := hs n inferInstance hn hsq
  rw [mem_ptsOver_iff] at hz ⊢
  revert hz hfixz
  rcases tyzZn n with _ | ⟨x, y, h⟩
  · intro _ _; trivial
  · intro hz hfixz
    have hc : ∀ ρ : GalQ, ActsAsArtin4 ρ n (sigmaClass n) → ρ x = x ∧ ρ y = y := by
      intro ρ hρ
      have e := hfixz ρ hρ
      obtain ⟨h', e'⟩ := galPt_some ρ h
      rw [e', WeierstrassCurve.Affine.Point.some.injEq] at e
      exact e
    exact ⟨mem_Hprimebar_of_fixed n hz.1 fun ρ hρ => (hc ρ hρ).1,
      mem_Hprimebar_of_fixed n hz.2 fun ρ hρ => (hc ρ hρ).2⟩

end ZInQ.Contrib.TYZGenus.Package

#print axioms ZInQ.Contrib.TYZGenus.Package.tyzZnOverHprime_of
