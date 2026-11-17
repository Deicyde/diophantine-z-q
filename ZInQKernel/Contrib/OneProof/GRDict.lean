import ZInQKernel.Contrib.OneProof.GR56Lattice
import ZInQKernel.Contrib.OneProof.ElkiesX6StarPrinted

/-!
# gr-dict: González–Rotger's theorems over CM points as González–Rotger define them

The research fields `gonzalezRotgerX6Ab` (`HDec.QMSplit.Moduli.GonzalezRotgerX6Ab`, `TailZ22`) and
`gonzalezRotgerProp56X6` (`GRCountX6.GonzalezRotgerProp56X6`, `Contrib/OneProof/GRCountX6.lean`) read "CM point by
`R`" as "a `ℚ̄`-point whose QM pair has `End_𝒪(A) ≅ R`". González–Rotger (J. Math. Soc. Japan 58 (2006), §5) define
`CM(R)` on `X₀(D,N)(ℂ) = Γ∖ℍ`: `P = [z]` with `z` fixed by `φ(k^×)` for an optimal embedding `φ : R ↪ 𝒪`. The
11-16 dictionary pass rated both fields GLUE for that reason. This file

* defines `IsGRCMPoint Ψ R x`, González–Rotger's predicate transported to a `ℚ̄`-point `x` of a coarse witness
  `(X, Ψ)`: the pair of `x`, base-changed to `ℂ` along `GR56.σQ`, is the torus `ℂ²/ι(𝒪)(z, 1)ᵀ` (an `ι`-compatible
  uniformization with kernel exactly `Λ_z`) for a `z ∈ ℍ` that is the CM point (`ShimuraCFT.IsCMPoint`) of an
  optimal embedding of `R`;
* proves the **dictionary** in both directions from the textbook fields `uniformizationLeafAll`, `gagaMorphism`,
  `mumfordTorsionAlgClosed` only (`isGRCMPoint_of_com`, `com_of_isGRCMPoint`; gr56-prove's lattice model);
* states González–Rotger Thm 5.12 (`GonzalezRotgerThm512X6`) and Prop. 5.6 (`GonzalezRotgerProp56X6CM`) over
  `IsGRCMPoint`, for every witness of the moduli description (no existence claim);
* proves the field `gonzalezRotgerX6Ab` from Thm 5.12, the witness of the existing research field
  `elkiesX6StarFunctionField` and the three textbook fields (`gonzalezRotgerX6Ab_of_printed`), and the field
  `gonzalezRotgerProp56X6` from Prop. 5.6 and the textbook fields (`gonzalezRotgerProp56X6_of_cm`).

No `sorry`; standard axioms only.
-/

set_option linter.style.longLine false

noncomputable section

namespace GRDict

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-! ## 1. CM points as González–Rotger define them -/

/-- **`x` is a CM point by `R` in González–Rotger's sense** (J. Math. Soc. Japan 58 (2006) §5: `P ∈ CM(R)` iff
`P = [z] ∈ Γ∖ℍ` with `z` fixed by `φ(k^×)` for an optimal embedding `φ : R ↪ 𝒪`), transported to a `ℚ̄`-point `x`
of a coarse witness `(X, Ψ)` through the moduli interpretation of `Γ∖ℍ` (`[z] ↦ ℂ²/ι(𝒪)(z, 1)ᵀ`, Shimura 1967):
the QM pair `P` of `x`, base-changed to `ℂ` along `GR56.σQ`, has an `ι`-compatible analytic uniformization with
kernel exactly `Λ_z = ι(𝒪)(z, 1)ᵀ` (the torus at `z`), and `z ∈ ℍ` is the CM point of an optimal embedding
`φ : k → B`, `φ⁻¹(𝒪) = R`: `ι(φ(a))·(z, 1)ᵀ = κ(a)·(z, 1)ᵀ` for some `κ : k → ℂ`, i.e. `φ(k^×)` fixes `z`. -/
def IsGRCMPoint {X : Over (Spec (CommRingCat.of ℚ))} (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    {k : Type} [Field k] [NumberField k] (R : Subring k) (x : fieldPt Qbar ⟶ X) : Prop :=
  ∃ P : QMPair Qbar, Ψ x = Quotient.mk _ P ∧
    ∃ (z : UpperHalfPlane) (Φu : (Fin 2 → ℂ) → ZInQ.LeafPush2.CPts (GR56.bcQ P).A (RingHom.id ℂ)),
      ZInQ.LeafPush2.IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice z.im_pos.ne') Φu ∧
      (∀ (a : LeafQM.O) (w : Fin 2 → ℂ),
        Φu ((HDec.HSyn.G0Split.FibreQM.qmMat a).mulVec w) = Φu w ≫ ((GR56.bcQ P).q.iota a).hom) ∧
      ∃ (φ : GRCountX6.OptEmb k R) (κ : k →+* ℂ), ShimuraCFT.IsCMPoint φ.1 κ z

/-! ## 2. The dictionary (glue, proved from the textbook fields) -/

/-- `ι(b)` on `ℂ²` is the matrix of `IsCMPoint`. -/
theorem act_eq_iota (b : B) (w : Fin 2 → ℂ) :
    HDec.QMSplit.CNO.act b w = Matrix.mulVec ((BPAnalytic.QM.iota b).map (algebraMap ℝ ℂ)) w := rfl

section Dict

variable (hU : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
  (hM : AvSplit.MumfordTorsionAlgClosed)

include hU hG hM in
/-- **Dictionary, direction used by Thm 5.12: a point whose pair has `End_𝒪 ≅ R` is a CM point by `R` in
González–Rotger's sense.** Its lattice model (gr56-prove's `datQ`) gives `z = τ ∈ ℍ` and the uniformization
`Φ ∘ Fl⁻¹` with kernel `Λ_τ`; the embedding `embP` (`a ↦ b` with `ι(b)(τ, 1)ᵀ = ψ(a)(τ, 1)ᵀ`) is optimal
(`emb_opt`). -/
theorem isGRCMPoint_of_com {k : Type} [Field k] [NumberField k] (hk : Module.finrank ℚ k = 2) {R : Subring k}
    (hR : R ≤ (integralClosure ℤ k).toSubring) (hc : Nat.Coprime (conductor R) 6)
    {X : Over (Spec (CommRingCat.of ℚ))} (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar) (hP : Ψ x = Quotient.mk _ P) (θ : com P.q ≃+* R) :
    IsGRCMPoint Ψ R x := by
  set D := GR56.datQ hU hG hM P with hDdef
  refine ⟨P, hP, UpperHalfPlane.mk D.τ D.hτ, fun w => D.Φ (D.Fl.symm w), ?_, ?_,
    GR56.embP hU hG hM hk hR hc P θ, GR56.ψk k, ?_⟩
  · have h := HDec.HSyn.G0Split.FibreQM.isUniformization_comp D.hΦ D.Fl
    have hL : BPAnalytic.QM.qmLattice (UpperHalfPlane.mk D.τ D.hτ).im_pos.ne' =
        D.Λ.map (D.Fl.toLinearMap.restrictScalars ℤ) := by
      ext w
      rw [Submodule.mem_map]
      have e1 : w ∈ BPAnalytic.QM.qmLattice (UpperHalfPlane.mk D.τ D.hτ).im_pos.ne' ↔ w ∈ GR56.L ![D.τ, 1] := by
        rw [GR56.L, ← HDec.FibreQMNorm.qmLattice_eq_orbit D.hτ.ne']
      rw [e1]
      constructor
      · intro hw
        refine ⟨D.Fl.symm w, (D.hΛ _).2 (by rwa [LinearEquiv.apply_symm_apply]), ?_⟩
        simp
      · rintro ⟨u, hu, rfl⟩
        exact (D.hΛ u).1 hu
    rw [hL]
    exact h
  · intro a w
    have h1 : D.Fl.symm ((HDec.HSyn.G0Split.FibreQM.qmMat a).mulVec w) =
        D.ρ ((GR56.bcQ P).q.iota a) (D.Fl.symm w) := by
      apply D.Fl.injective
      rw [LinearEquiv.apply_symm_apply, D.hFρ, LinearEquiv.apply_symm_apply]
      rfl
    change D.Φ (D.Fl.symm _) = D.Φ (D.Fl.symm w) ≫ _
    rw [h1, D.hρ]
  · intro a
    have := GR56.embP_spec hU hG hM hk hR hc P θ a
    rw [act_eq_iota] at this
    exact this

include hU hG in
/-- **Dictionary, converse: a CM point by `R` in González–Rotger's sense has `End_𝒪 ≅ R`.** The uniformization
with kernel `Λ_z` is lattice data with `τ = z` (`latData_of_torus`), and `com_equiv_of_eig` reads `End_𝒪` off
the optimal embedding fixing `z`; `End_𝒪` is unchanged by base change to `ℂ` (`com_bcQ`). -/
theorem com_of_isGRCMPoint {k : Type} [Field k] [NumberField k] (hk : Module.finrank ℚ k = 2) {R : Subring k}
    (hc : Nat.Coprime (conductor R) 6)
    {X : Over (Spec (CommRingCat.of ℚ))} (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (x : fieldPt Qbar ⟶ X) (h : IsGRCMPoint Ψ R x) :
    ∃ P : QMPair Qbar, Ψ x = Quotient.mk _ P ∧ Nonempty (com P.q ≃+* R) := by
  obtain ⟨P, hP, z, Φu, hΦ, hι, φ, κ, hcm⟩ := h
  have hC := AvSplit.Final.h69 hU hG
  obtain ⟨D, hD⟩ := GR56.latData_of_torus hC (GR56.bcQ P).surface z.im_pos Φu hΦ hι
  have heig : ∀ a, HDec.QMSplit.CNO.act (φ.1 a) D.v = κ a • D.v := by
    intro a
    rw [act_eq_iota]
    have hv : D.v = ![(z : ℂ), 1] := by rw [GR56.LatData.v, hD]
    rw [hv]
    exact hcm a
  obtain ⟨⟨e⟩, -⟩ := GR56.com_equiv_of_eig hC (GR56.bcQ P).surface D hk hc φ κ heig
  obtain ⟨e0⟩ := GR56.com_bcQ P
  exact ⟨P, hP, ⟨e0.trans e⟩⟩

include hU hG hM in
/-- **The two readings of "CM point by `R`" agree** (from the textbook fields). -/
theorem isGRCMPoint_iff {k : Type} [Field k] [NumberField k] (hk : Module.finrank ℚ k = 2) {R : Subring k}
    (hR : R ≤ (integralClosure ℤ k).toSubring) (hc : Nat.Coprime (conductor R) 6)
    {X : Over (Spec (CommRingCat.of ℚ))} (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (x : fieldPt Qbar ⟶ X) :
    IsGRCMPoint Ψ R x ↔ ∃ P : QMPair Qbar, Ψ x = Quotient.mk _ P ∧ Nonempty (com P.q ≃+* R) := by
  constructor
  · exact com_of_isGRCMPoint hU hG hk hc Ψ x
  · rintro ⟨P, hP, ⟨θ⟩⟩
    exact isGRCMPoint_of_com hU hG hM hk hR hc Ψ x P hP θ

end Dict

/-! ## 3. González–Rotger Thm 5.12 over its own CM points, and the field `gonzalezRotgerX6Ab` -/

/-- **LEAF (González–Rotger, *Non-elliptic Shimura curves of genus one*, J. Math. Soc. Japan 58 (2006),
Thm 5.12, p. 946 (read by the locator audit, docs/research/locators.md row "R5: fields of definition"), at
`(D, N) = (6, 1)`; printed form, degree-and-embedding consequence, on every witness of the moduli description).**

*Published statement* (as read by the audit): for `P ∈ CM(R) ⊂ X₀(D,N)`, `R` of conductor prime to `DN`,
`ℚ(P) = H_R` (the ring class field of `R`) if `D(R)N*(R) ≠ 1`, and otherwise `ℚ(P)` is a specified subfield of
`H_R` of index two. At `(6, 1)`: `D(R) ≠ 1` iff some `p ∣ 6` is inert in `k` (`inertCount6 k ≠ 0`), `N*(R) = 1`,
and `[H_R : ℚ] = 2h(R)` with `k ⊂ H_R`.

*Lean form*: for every witness `(Y, Φ, X, Ψ, fY)` of the moduli clause lists (`R1fpPropsAb`, `X6Props`) and every
`ℚ̄`-point `x` of `X` that is a CM point by `R` in González–Rotger's sense (`IsGRCMPoint`), the residue field
`ℚ(x)` has degree `2h(R)` and contains `k` if some `p ∣ 6` is inert in `k`, and degree `h(R)` otherwise.

*Why not stronger*: `x ↦ σQ ∘ x` is a point `P ∈ CM(R)` of `X(ℂ)` with `ℚ(P) ≅ ℚ(x)`, so the Lean form is the
printed statement's degree and embedding clauses at such `P`. On any witness, `ℚ(x)` is the fixed field of the
stabilizer of `Ψ x` in `Gal(ℚ̄/ℚ)` (`Ψ` is Galois-equivariant, `X6Props`), i.e. the field of moduli of the pair, so
the statement does not depend on the witness and asserts nothing about the model beyond the canonical one. -/
def GonzalezRotgerThm512X6 : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ → X6Props Y Φ X Ψ fY →
    ∀ (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
      Module.finrank ℚ k = 2 →
      ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring → Nat.Coprime (conductor R) 6 →
        ∀ x : fieldPt Qbar ⟶ X, IsGRCMPoint Ψ R x →
          Module.finrank ℚ (residueImage (X := X.left) x.left) =
            (if inertCount6 k = 0 then 1 else 2) * Nat.card (CommRing.Pic R) ∧
          (inertCount6 k ≠ 0 → Nonempty (k →ₐ[ℚ] residueImage (X := X.left) x.left))

/-- The clause `R5ptProps` on any witness, from Thm 5.12 over González–Rotger's CM points and the dictionary. -/
theorem r5ptProps_of_thm512 (h : GonzalezRotgerThm512X6) (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {X : Over (Spec (CommRingCat.of ℚ))}
    {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)} {fY : Y ⟶ X}
    (h1 : LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ) (h6 : X6Props Y Φ X Ψ fY) : R5ptProps X Ψ := by
  intro k _ _ _ hk R hR hc x P hP ⟨θ⟩
  exact h Y Φ X Ψ fY h1 h6 k hk R hR hc x (isGRCMPoint_of_com hU hG hM hk hR hc Ψ x P hP θ)

/-- **GLUE (composite) `X6ModuliWitness`: a witness of the moduli description of `Y₃` and `X₆ = X₀(6,1)` exists.**
The canonical models: Shimura, Ann. of Math. 85 (1967), Main Theorems I-II; Deligne, Sém. Bourbaki 389 (1971),
4.9-4.21 and the PEL form 5.7-5.8 (numbers UNVERIFIED), giving the fine moduli scheme `Y₃` of QM abelian surfaces
with level-3 structure (`R1fpPropsAb`, which also needs the polarization lemma of rv-qm-polar), and the coarse
quotient `X₆ = Y₃/(𝒪/3𝒪)^×` with its moduli bijection on `ℚ̄`-points (`X6Props`). No single printed statement has
this form, so it is a composite. It is not a new field: the existing research field `elkiesX6StarFunctionField`
asserts it (`x6ModuliWitness_of_elkies`), and so does the old field `gonzalezRotgerX6Ab`. -/
def X6ModuliWitness : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY

/-- The witness carried by the research field `elkiesX6StarFunctionField`. -/
theorem x6ModuliWitness_of_elkies (hE : HDec.QMSplit.Moduli.ElkiesCoord.ElkiesX6StarFunctionField) :
    X6ModuliWitness := by
  obtain ⟨Y, Φ, X, Ψ, fY, -, h1, h6, -⟩ := hE
  exact ⟨Y, Φ, X, Ψ, fY, h1, h6⟩

/-- The witness carried by the old field itself (so `X6ModuliWitness` is never stronger than `gonzalezRotgerX6Ab`). -/
theorem x6ModuliWitness_of_gonzalezRotgerX6Ab (h : HDec.QMSplit.Moduli.GonzalezRotgerX6Ab) : X6ModuliWitness := by
  obtain ⟨Y, Φ, X, Ψ, fY, h1, h6, -⟩ := h
  exact ⟨Y, Φ, X, Ψ, fY, h1, h6⟩

/-- **`gonzalezRotgerX6Ab` from the witness and Thm 5.12 over González–Rotger's CM points.** -/
theorem gonzalezRotgerX6Ab_of_witness (h : GonzalezRotgerThm512X6) (hW : X6ModuliWitness)
    (hU : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
    (hM : AvSplit.MumfordTorsionAlgClosed) : HDec.QMSplit.Moduli.GonzalezRotgerX6Ab := by
  obtain ⟨Y, Φ, X, Ψ, fY, h1, h6⟩ := hW
  exact ⟨Y, Φ, X, Ψ, fY, h1, h6, r5ptProps_of_thm512 h hU hG hM h1 h6⟩

/-- **The field `gonzalezRotgerX6Ab` from Thm 5.12 over González–Rotger's CM points** (new LEAF), the witness of
the existing research field `elkiesX6StarFunctionField` and the textbook fields `uniformizationLeafAll`,
`gagaMorphism`, `mumfordTorsionAlgClosed`. -/
theorem gonzalezRotgerX6Ab_of_printed (h : GonzalezRotgerThm512X6)
    (hE : HDec.QMSplit.Moduli.ElkiesCoord.ElkiesX6StarFunctionField)
    (hU : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
    (hM : AvSplit.MumfordTorsionAlgClosed) : HDec.QMSplit.Moduli.GonzalezRotgerX6Ab :=
  gonzalezRotgerX6Ab_of_witness h (x6ModuliWitness_of_elkies hE) hU hG hM

/-! ## 4. González–Rotger Prop. 5.6 over its own CM points, and the field `gonzalezRotgerProp56X6` -/

/-- **LEAF (González–Rotger, J. Math. Soc. Japan 58 (2006), Prop. 5.6, p. 943 (read by the locator audit), at
`(D, N) = (6, 1)`, on its own CM points, for every witness of the moduli description).**

*Published statement*: for an order `R` of conductor prime to `DN` in an imaginary quadratic field `k` that embeds
optimally in the Eichler order of level `N` of the quaternion algebra of discriminant `D`,
`#CM(R) = 2^{#{p ∣ D(R)N(R)}} h(R)`. At `(6, 1)`: `#CM(R) = 2^{inertCount6 k} · #Pic(R)`.

*Lean form*: for every witness `(Y, Φ, X, Ψ, fY)` and every such `R` with an optimal embedding into `LeafQM.O`,
the `ℚ̄`-points of `X` that are CM points by `R` in González–Rotger's sense (`IsGRCMPoint`) number
`2^{inertCount6 k} · #Pic(R)`.

*Reading*: González–Rotger count points of `X₀(D,N)(ℂ)`; the Lean form counts `ℚ̄`-points. They agree because every
`P ∈ CM(R)` is defined over the number field `ℚ(P) = H_R` (Thm 5.12 of the same paper) and `σQ(ℚ̄)` is the
algebraic closure of `ℚ` in `ℂ`; without that, the Lean form would only be `≤`. So it is a consequence of Prop. 5.6
together with Thm 5.12 (both printed in the paper), not Prop. 5.6 alone. -/
def GonzalezRotgerProp56X6CM : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ → X6Props Y Φ X Ψ fY →
    ∀ (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
      Module.finrank ℚ k = 2 →
      ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring → Nat.Coprime (conductor R) 6 →
        Nonempty (GRCountX6.OptEmb k R) →
          Nat.card {x : fieldPt Qbar ⟶ X // IsGRCMPoint Ψ R x} =
            2 ^ inertCount6 k * Nat.card (CommRing.Pic R)

/-- **The field `gonzalezRotgerProp56X6` from Prop. 5.6 over González–Rotger's CM points** (new LEAF) and the
textbook fields, through the dictionary (`isGRCMPoint_iff`); the occurrence hypothesis gives an optimal embedding
(`GR56.embP`). -/
theorem gonzalezRotgerProp56X6_of_cm (h : GonzalezRotgerProp56X6CM)
    (hU : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
    (hM : AvSplit.MumfordTorsionAlgClosed) : GRCountX6.GonzalezRotgerProp56X6 := by
  intro Y Φ X Ψ fY h1 h6 k _ _ _ hk R hR hc ho
  obtain ⟨P, ⟨θ⟩⟩ := ho
  have hopt : Nonempty (GRCountX6.OptEmb k R) := ⟨GR56.embP hU hG hM hk hR hc P θ⟩
  rw [← h Y Φ X Ψ fY h1 h6 k hk R hR hc hopt]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x =>
    (isGRCMPoint_iff hU hG hM hk hR hc Ψ x).symm)

end GRDict
