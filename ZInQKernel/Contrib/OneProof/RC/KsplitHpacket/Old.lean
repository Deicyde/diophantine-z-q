import ZInQKernel.Contrib.OneProof.RC.KsplitHpacket.Shift
import ZInQKernel.Contrib.OneProof.RC.ThetaCoeff.Hecke

/-! Two p-old degeneracy copies at level exponent one. The good Fourier
recurrence is the same for cuspidal and Eisenstein sources. -/

noncomputable section

namespace ZInQ.Manuscript.RC.KsplitHpacket

open Matrix AddressGenuine PrintsArith O12Local
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}
variable {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
variable {chiType : GalQ →* Multiplicative L}
variable {X : GaloisConstituentModel T R ap B chiType}
variable {U : Finset ℕ} {p : ℕ} {P : O12.LocalPair p}

variable (D : O12.LocalBlocks X U P)

/-- On a constituent unramified at the place of the local pair, the good
polynomial at another arithmetic Frobenius lift equals the one at P.φ. -/
theorem old_frob_values {K : Type*} [Field K] (hp : p.Prime) {ρ : GalQ →* GL (Fin 2) K}
    (hu : CarayolUnramified P ρ) {g : GalQ} (hg : IsFrobAt g p) :
    (↑(ρ P.φ) : Matrix (Fin 2) (Fin 2) K).trace =
      (↑(ρ g) : Matrix (Fin 2) (Fin 2) K).trace ∧
    (↑(ρ P.φ) : Matrix (Fin 2) (Fin 2) K).det =
      (↑(ρ g) : Matrix (Fin 2) (Fin 2) K).det := by
  obtain ⟨Q, hQ, hpQ, hF⟩ := hg
  obtain ⟨τ, hτ⟩ := exists_smul_eq_of_isMaximal hQ P.maximal hp hpQ P.above
  have h' := hF.conj τ
  rw [← hτ] at h'
  have h := hu _ (P.frob.mul_inv_mem_inertia h')
  rw [map_mul, map_inv, mul_inv_eq_one, map_mul, map_mul, map_inv] at h
  rw [h]
  exact ⟨trace_units_conj (ρ τ) (ρ g), Matrix.det_units_conj (ρ τ) (ρ g)⟩

/-- Use the good cuspidal polynomial or Eisenstein character pair on both
copies of an old factor. Constancy at the chosen good Frobenius gives the
two scalar actions at the same lift as the ramified comparisons. -/
theorem old_scalars_of_frob (hp : p.Prime) {g : GalQ} (hg : IsFrobAt g p)
    {S : Set X.I} {v : X.I → X.K} (hv : SupportedOn S v) (a δ : X.K)
    (hu : ∀ i ∈ S, CarayolUnramified P (X.ρ i))
    (ht : ∀ i ∈ S, (↑(X.ρ i g) : Matrix (Fin 2) (Fin 2) X.K).trace = a)
    (hd : ∀ i ∈ S, (↑(X.ρ i g) : Matrix (Fin 2) (Fin 2) X.K).det = δ) :
    tV X.ρ P.φ v = a • v ∧ dV X.ρ P.φ v = δ • v := by
  exact ⟨scalarOp_eq_smul_of_support _ _ _ hv
      (fun i hi => (old_frob_values hp (hu i hi) hg).1.trans (ht i hi)),
    scalarOp_eq_smul_of_support _ _ _ hv
      (fun i hi => (old_frob_values hp (hu i hi) hg).2.trans (hd i hi))⟩

/-- Fourier data on the two old vectors determine the actual p-old matrix.
The two given shifts are only on the two generators; the coefficient
comparison for distinguishing their images is on the active space. -/
theorem old_pair_up_of_goodRec (A : O12.FourierData X) (hp : p ≠ 0)
    (ha : ∀ v, SupportedOn D.active v → SupportedOn D.active (D.Up v))
    (hinj : ∀ v w : X.I → X.K, SupportedOn D.active v → SupportedOn D.active w →
      (∀ n : O12.PosIndex, X.coefK v (A.index n) = X.coefK w (A.index n)) → v = w)
    {g vg : X.I → X.K} (hg : SupportedOn D.active g) (hvg : SupportedOn D.active vg)
    {a : ℕ → X.K} {aₚ χₚ : X.K} (hrec : ThetaCoeff.GoodRec a aₚ χₚ p)
    (hg_exp : ∀ n : O12.PosIndex, X.coefK g (A.index n) = a n)
    (hvg_exp : ∀ n : O12.PosIndex, X.coefK vg (A.index n) = Odd.divCoeff a p n)
    (hg_shift : ∀ n, X.coefK (D.Up g) (A.index n) = X.coefK g (A.index (mulIndex p hp n)))
    (hvg_shift : ∀ n, X.coefK (D.Up vg) (A.index n) = X.coefK vg (A.index (mulIndex p hp n))) :
    D.Up g = aₚ • g - ((p : X.K) * χₚ) • vg ∧ D.Up vg = g := by
  constructor
  · refine hinj _ _ (ha _ hg) (fun i hi => ?_) (fun n => ?_)
    · simp [hg i hi, hvg i hi]
    · rw [hg_shift, hg_exp, map_sub, Pi.sub_apply, map_smul, map_smul,
        Pi.smul_apply, Pi.smul_apply, hg_exp, hvg_exp]
      linear_combination -(hrec n)
  · refine hinj _ _ (ha _ hvg) hg (fun n => ?_)
    rw [hvg_shift, hvg_exp, hg_exp]
    exact Odd.divCoeff_mul_left a (Nat.pos_of_ne_zero hp) n

/-- An old multiplicity pair on the actual combined operator. The trace and
determinant eigenvalues come from the good polynomial on the lower-level
factor, and the two operator images from the old Fourier comparison. -/
structure OldPair where
  g : X.I → X.K
  vg : X.I → X.K
  a : X.K
  δ : X.K
  t_g : tV X.ρ P.φ g = a • g
  t_vg : tV X.ρ P.φ vg = a • vg
  d_g : dV X.ρ P.φ g = δ • g
  d_vg : dV X.ρ P.φ vg = δ • vg
  up_g : D.Up g = a • g - δ • vg
  up_vg : D.Up vg = g

theorem OldPair.map_up_g (Q : OldPair D) (J : (X.I → X.K) →ₗ[X.K] (X.I → X.K))
    (c : X.K) (hg : J Q.g = c • Q.g) (hvg : J Q.vg = c • Q.vg) :
    J (D.Up Q.g) = c • D.Up Q.g := by
  simp only [Q.up_g, map_sub, map_smul, hg, hvg, smul_sub, smul_smul, mul_comm c]

/-- The old comparison: the actual old space is spanned by the two
degeneracy vectors of such lower-level factors (retaining away-from-p
multiplicities). Both commutations and the cubic follow on that space. -/
theorem oldBlockCubic_of_pairs
    (ha : ∀ v, SupportedOn D.active v → SupportedOn D.active (D.Up v))
    (hspan : ∀ v : X.I → X.K, SupportedOn (OldCoordinates D) v →
      v ∈ Submodule.span X.K {w | ∃ Q : OldPair D, w = Q.g ∨ w = Q.vg}) :
    OldBlockCubic D := by
  let t := tV X.ρ P.φ
  let d := dV X.ρ P.φ
  let u := D.Up
  let Ct := u.comp t - t.comp u
  let Cd := u.comp d - d.comp u
  let Qp := u.comp u - t.comp u + d
  let N := (Ct.ker ⊓ Cd.ker) ⊓ Qp.ker
  have hN : Submodule.span X.K {w | ∃ Q : OldPair D, w = Q.g ∨ w = Q.vg} ≤ N := by
    apply Submodule.span_le.mpr
    rintro w ⟨Q, rfl | rfl⟩
    · change (Ct Q.g = 0 ∧ Cd Q.g = 0) ∧ Qp Q.g = 0
      refine ⟨⟨sub_eq_zero.mpr ?_, sub_eq_zero.mpr ?_⟩, ?_⟩
      · change u (t Q.g) = t (u Q.g)
        rw [Q.t_g, map_smul, Q.map_up_g D t _ Q.t_g Q.t_vg]
      · change u (d Q.g) = d (u Q.g)
        rw [Q.d_g, map_smul, Q.map_up_g D d _ Q.d_g Q.d_vg]
      · change u (u Q.g) - t (u Q.g) + d Q.g = 0
        have e : u (u Q.g) = Q.a • u Q.g - Q.δ • Q.g := by
          calc
            _ = u (Q.a • Q.g - Q.δ • Q.vg) := congrArg u Q.up_g
            _ = _ := by rw [map_sub, map_smul, map_smul, Q.up_vg]
        rw [e, Q.map_up_g D t _ Q.t_g Q.t_vg, Q.d_g]
        abel
    · change (Ct Q.vg = 0 ∧ Cd Q.vg = 0) ∧ Qp Q.vg = 0
      refine ⟨⟨sub_eq_zero.mpr ?_, sub_eq_zero.mpr ?_⟩, ?_⟩
      · change u (t Q.vg) = t (u Q.vg)
        rw [Q.t_vg, map_smul, Q.up_vg, Q.t_g]
      · change u (d Q.vg) = d (u Q.vg)
        rw [Q.d_vg, map_smul, Q.up_vg, Q.d_g]
      · change u (u Q.vg) - t (u Q.vg) + d Q.vg = 0
        rw [Q.up_vg, Q.up_g, Q.t_g, Q.d_vg]
        abel
  intro v hv
  have laws (w) (hw : SupportedOn (OldCoordinates D) w) :
      u (t w) = t (u w) ∧ u (d w) = d (u w) ∧ u (u w) - t (u w) + d w = 0 := by
    have hm := hN (hspan w hw)
    change (Ct w = 0 ∧ Cd w = 0) ∧ Qp w = 0 at hm
    exact ⟨sub_eq_zero.mp hm.1.1, sub_eq_zero.mp hm.1.2, hm.2⟩
  exact ⟨(laws v hv).1, (laws v hv).2.1, (laws (u v) (old_stable D ha hv)).2.2⟩

end ZInQ.Manuscript.RC.KsplitHpacket
