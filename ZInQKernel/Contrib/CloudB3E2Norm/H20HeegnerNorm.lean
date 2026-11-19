import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Heegner

/-!
# The Heegner norm relation `hnorm` from the print (Cai–Chen–Liu, Theorem 2.15)

Manuscript `diophantine_zq.tex`, tex 2914–2936 (the norm relations (4.1) of the Heegner points
`y_d = φ(x_d)`) and tex 4157–4170 (their use in the common-coordinate step: the trace of the relaxed
point is `(a_q − σ_q − σ_q⁻¹)` of the primitive point).

The norm identity of this directory (`TransferNorm.transfer_kummer_norm_of_transversal`,
`StageRing.hzR_stage_of_strictLifts`, `H20Assembly.h1_shapiro`) takes the norm relation in the form

  `hnorm : ∑_{τ ∈ H_P/U} ρ(t_τ) y_R = a • y_P − ρ(σ) y_P − ρ(σ⁻¹) y_P`

for points `y_R`, `y_P` of an ambient `ρ`-module `D` of points (`U` the image of `H_R` in `H_P`,
`t` a transversal). The tree's print is `CCLThm2_15Applied E Anchor` (`PrintsArith/Heegner.lean`):
some `HeegnerPointData D` satisfying `D.NormRelations` and the anchor; the split clause of
`NormRelations` is the same relation in `E(ℚ̄)`, with `D.relGal d q`, `D.frob d q`, `D.y`.

* **`HeegnerTransportAt`** (Prop; kind GLUE — the compatibility of the ring class fields
  `HeegnerPointData.H` in `ℚ̄` with their realization inside `K_S` (`RingClassKS.ringClassFieldS`),
  listed as open earlier): an additive equivariant comparison `j : E(ℚ̄) → D` carrying `D.y (d q)` to
  `y_R` and `D.y d` to `y_P`, a bijection between the transversal `H_P/U` and `D.relGal d q` compatible
  with `j` on `D.y (d q)`, and `σ`, `σ⁻¹` matching `D.frob d q`, `(D.frob d q)⁻¹` on `D.y d`.
* **`hnorm_of_normRelations`** (PROVED): `D.NormRelations`, admissibility, `q` split in `K` and
  `HeegnerTransportAt` give `hnorm` with `a = a_q = E.LFunction q`.
* **`hnorm_of_print`** (PROVED): from the print `CCLThm2_15Applied E Anchor`, if every anchored
  `D` admits the transport, there is a `D` (the print's) with `hnorm`. The anchor needed is the one
  pinning `D.y` to the genuine Heegner points (in the proof, Cai–Shu–Tian at conductor one, stated by
  the shared top layer, `CST.CSTThm11Split`); it is not used by this derivation, only carried.
* Non-vacuity: `nonVacuity_transport` (the zero comparison into the zero system).

Kinds: definitions and PROVED from the PRINT `CCLThm2_15Applied` and the GLUE `HeegnerTransportAt`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Manuscript.RC.PrintsArith
open scoped WeierstrassCurve

section Transport

variable {E : WeierstrassCurve ℚ} {G : Type*} [Group G] {A : Type*} [CommRing A] {Dm : Type*}
  [AddCommGroup Dm] [Module A Dm] (ρ : G →* Module.End A Dm)
  (HP : Subgroup G) (U : Subgroup HP) [Fintype (HP ⧸ U)] (t : HP ⧸ U → HP)

/-- **The transport of the Heegner point data to the ambient module of points** at `(d, q)`
(Prop; GLUE): see the module docstring. Kind: definition (Prop). -/
def HeegnerTransportAt (D : HeegnerPointData E) (d q : ℕ) (σ : G) (yR yP : Dm) : Prop :=
  ∃ (j : (E⁄Qbar).toAffine.Point →+ Dm) (e : HP ⧸ U ≃ D.relGal d q),
    j (D.y (d * q)) = yR ∧ j (D.y d) = yP ∧
    (∀ τ : HP ⧸ U, ρ (t τ : G) yR =
      j (WeierstrassCurve.Affine.Point.map (e τ).1.toAlgHom (D.y (d * q)))) ∧
    j (WeierstrassCurve.Affine.Point.map (D.frob d q).toAlgHom (D.y d)) = ρ σ yP ∧
    j (WeierstrassCurve.Affine.Point.map (D.frob d q)⁻¹.toAlgHom (D.y d)) = ρ σ⁻¹ yP

/-- **`hnorm` from the norm relations (4.1)** (PROVED; tex 2924–2929, 4157–4170): the split
clause of `D.NormRelations` at an admissible `(d, q)` with `q` split in `K`, transported by
`HeegnerTransportAt`, is the norm relation in the twisted-transfer form, with `a = a_q`. -/
theorem hnorm_of_normRelations (D : HeegnerPointData E) (hD : D.NormRelations) {d q : ℕ}
    (hadm : D.Admissible d q) (hsplit : jacobiSym D.DK q = 1) {σ : G} {yR yP : Dm}
    (htr : HeegnerTransportAt ρ HP U t D d q σ yR yP) :
    ∑ τ : HP ⧸ U, ρ (t τ : G) yR =
      (E.LFunction q : ℤ) • yP - ρ σ yP - ρ σ⁻¹ yP := by
  obtain ⟨j, e, hjR, hjP, hτ, hσ, hσi⟩ := htr
  have hrel := hD.2 d q hadm hsplit
  have hsum : ∑ τ : HP ⧸ U, ρ (t τ : G) yR =
      j (∑ τ ∈ D.relGal d q, WeierstrassCurve.Affine.Point.map τ.toAlgHom (D.y (d * q))) := by
    rw [map_sum, ← Finset.sum_coe_sort (D.relGal d q)]
    exact Fintype.sum_equiv e _ _ (fun τ => hτ τ)
  rw [hsum, hrel, map_sub, map_sub, map_zsmul, hjP, hσ, hσi]

/-- **`hnorm` from the print** (PROVED from the PRINT `CCLThm2_15Applied`): if every anchored
Heegner point datum admits the transport at `(d, q)` (with points `yR D`, `yP D`) and `(d, q)` is
admissible with `q` split, the print provides a datum whose transported points satisfy `hnorm`. -/
theorem hnorm_of_print {Anchor : HeegnerPointData E → Prop} (hprint : CCLThm2_15Applied E Anchor)
    {d q : ℕ} (σ : G) (yR yP : HeegnerPointData E → Dm)
    (hadm : ∀ D, Anchor D → D.Admissible d q) (hsplit : ∀ D : HeegnerPointData E, Anchor D →
      jacobiSym D.DK q = 1)
    (htr : ∀ D, Anchor D → HeegnerTransportAt ρ HP U t D d q σ (yR D) (yP D)) :
    ∃ D : HeegnerPointData E, Anchor D ∧
      ∑ τ : HP ⧸ U, ρ (t τ : G) (yR D) =
        (E.LFunction q : ℤ) • yP D - ρ σ (yP D) - ρ σ⁻¹ (yP D) := by
  obtain ⟨D, hD, hA⟩ := hprint
  exact ⟨D, hA, hnorm_of_normRelations ρ HP U t D hD (hadm D hA) (hsplit D hA) (htr D hA)⟩

end Transport

/-! ### Non-vacuity -/

/-- **Non-vacuity of `HeegnerTransportAt`**: for the zero system (`D.y = 0`), the zero comparison
into any module, with `relGal` the image of the transversal, transports to `y_R = y_P = 0`.
Kind: PROVED. -/
theorem nonVacuity_transport {E : WeierstrassCurve ℚ} {G : Type*} [Group G] {A : Type*}
    [CommRing A] {Dm : Type*} [AddCommGroup Dm] [Module A Dm] (ρ : G →* Module.End A Dm)
    (HP : Subgroup G) (U : Subgroup HP) [Fintype (HP ⧸ U)] (t : HP ⧸ U → HP) (DK : ℤ) (N d q : ℕ)
    (H : ℕ → IntermediateField ℚ Qbar) (frob : ℕ → ℕ → GalQ) (σ : G)
    (rg : Finset GalQ) (e : HP ⧸ U ≃ rg) :
    HeegnerTransportAt ρ HP U t (HeegnerPointData.mk (E := E) DK N H (fun _ => 0) (fun _ _ => rg)
      frob) d q σ 0 0 :=
  ⟨0, e, rfl, rfl, fun _ => by simp, by simp, by simp⟩

end ZInQ.Contrib.CloudB3E2.NormCochain
