import ZInQKernel.Contrib.OneProof.RC.O12Local.Blocks

/-! The characteristic-zero operator identity at the singleton (tex 10326–10331).
The ramified comparison is the same one used in tex 9866–9873. -/

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

abbrev OldCoordinates : Set X.I := D.active \ D.ramified

/-- The lower-level block calculation missing from the inertia-difference
identity: the operator respects trace and determinant scalars on old
multiplicities, and is annihilated by X times the good polynomial. -/
def OldBlockCubic : Prop :=
  ∀ v : X.I → X.K, SupportedOn (OldCoordinates D) v →
    D.Up (tV X.ρ P.φ v) = tV X.ρ P.φ (D.Up v) ∧
    D.Up (dV X.ρ P.φ v) = dV X.ρ P.φ (D.Up v) ∧
    D.Up (D.Up (D.Up v)) - tV X.ρ P.φ (D.Up (D.Up v)) +
      dV X.ρ P.φ (D.Up v) = 0

theorem scalarOp_supported {I K : Type} [Field K] (S : Set I) (c : I → K)
    {v : I → K} (hv : SupportedOn S v) : SupportedOn S (scalarOp c v) := by
  intro i hi
  rw [scalarOp_apply, hv i hi, mul_zero]

/-- A coordinatewise scalar operator acts by the common scalar on a supported block. -/
theorem scalarOp_eq_smul_of_support {I K : Type} [Field K] (S : Set I) (c : I → K)
    (z : K) {v : I → K} (hv : SupportedOn S v) (hc : ∀ i ∈ S, c i = z) :
    scalarOp c v = z • v := by
  funext i
  by_cases hi : i ∈ S
  · rw [scalarOp_apply, hc i hi, Pi.smul_apply, smul_eq_mul]
  · simp [hv i hi]

theorem combine_active_stable (C E : Sector X P) (hd : Disjoint C.active E.active)
    (hF : SupportedOn (C.active ∪ E.active) (X.F U : X.I → X.K))
    (v : X.I → X.K) :
    SupportedOn (combine C E hd hF).active ((combine C E hd hF).Up v) := by
  intro i hi
  have hs (S : Set X.I) : SupportedOn S (mask S v) := by
    classical
    intro j hj
    rw [mask_apply, ite_eq_right hj]
  change C.Up (mask C.active v) i + E.Up (mask E.active v) i = 0
  rw [C.active_stable _ (hs _) i (fun h => hi (Or.inl h)),
    E.active_stable _ (hs _) i (fun h => hi (Or.inr h)), add_zero]

/-- The actual combined operator preserves the old space. This follows from
active stability and the diagonal action on ramified output coordinates. -/
theorem old_stable
    (ha : ∀ v, SupportedOn D.active v → SupportedOn D.active (D.Up v))
    {v : X.I → X.K} (hv : SupportedOn (OldCoordinates D) v) :
    SupportedOn (OldCoordinates D) (D.Up v) := by
  intro i hi
  by_cases hia : i ∈ D.active
  · have hir : i ∈ D.ramified := by
      by_contra h
      exact hi ⟨hia, h⟩
    obtain ⟨b, l, m, hτ, hφ, hUp⟩ := D.newLine i ⟨hia, hir⟩
    rw [hUp v (fun j hj => hv j (fun h => hj h.1)), hv i (fun h => h.2 hir), mul_zero]
  · exact ha v (fun j hj => hv j (fun h => hj h.1)) i hia

theorem trace_det_of_diagonal {K : Type*} [Field K] (g b : GL (Fin 2) K) {l m : K}
    (h : (↑(b * g * b⁻¹) : Matrix (Fin 2) (Fin 2) K) = diagonal ![l, m]) :
    (↑g : Matrix (Fin 2) (Fin 2) K).trace = l + m ∧
      (↑g : Matrix (Fin 2) (Fin 2) K).det = l * m := by
  constructor
  · calc
      _ = (↑(b * g * b⁻¹) : Matrix (Fin 2) (Fin 2) K).trace :=
        (trace_units_conj b g).symm
      _ = _ := by rw [h, trace_diagonal, Fin.sum_univ_two]; rfl
  · calc
      _ = (↑(b * g * b⁻¹) : Matrix (Fin 2) (Fin 2) K).det :=
        (det_units_conj b g).symm
      _ = _ := by rw [h, det_diagonal, Fin.prod_univ_two]; rfl

theorem ramified_law {v : X.I → X.K}
    (hv : SupportedOn (D.active ∩ D.ramified) v) :
    D.Up (D.Up (tV X.ρ P.φ v)) = D.Up (D.Up (D.Up v)) + dV X.ρ P.φ (D.Up v) ∧
      D.Up (dV X.ρ P.φ v) = dV X.ρ P.φ (D.Up v) := by
  have ht : SupportedOn (D.active ∩ D.ramified) (tV X.ρ P.φ v) :=
    scalarOp_supported _ _ hv
  have hd : SupportedOn (D.active ∩ D.ramified) (dV X.ρ P.φ v) :=
    scalarOp_supported _ _ hv
  have hdU : SupportedOn (D.active ∩ D.ramified) (dV X.ρ P.φ (D.Up v)) :=
    scalarOp_supported _ _ (D.preserves_ramified _ hv)
  have s {w : X.I → X.K} (hw : SupportedOn (D.active ∩ D.ramified) w) :
      SupportedOn D.active w := fun i hi => hw i (fun h => hi h.1)
  constructor
  · funext i
    by_cases hi : i ∈ D.active ∩ D.ramified
    · obtain ⟨b, l, m, _, hf, hup⟩ := D.newLine i hi
      obtain ⟨htr, hdet⟩ := trace_det_of_diagonal (X.ρ i P.φ) b hf
      rw [Pi.add_apply, hup _ (s (D.preserves_ramified _ ht)), hup _ (s ht),
        hup _ (s (D.preserves_ramified _ (D.preserves_ramified _ hv))),
        hup _ (s (D.preserves_ramified _ hv))]
      simp only [tV, dV, scalarOp_apply, hup _ (s hv), htr, hdet]
      ring
    · rw [D.preserves_ramified _ (D.preserves_ramified _ ht) i hi,
        Pi.add_apply, D.preserves_ramified _ (D.preserves_ramified _ (D.preserves_ramified _ hv)) i hi,
        hdU i hi, add_zero]
  · funext i
    by_cases hi : i ∈ D.active ∩ D.ramified
    · obtain ⟨b, l, m, _, hf, hup⟩ := D.newLine i hi
      rw [hup _ (s hd)]
      simp only [dV, scalarOp_apply, hup _ (s hv)]
      ring
    · rw [D.preserves_ramified _ hd i hi, hdU i hi]

/-- Both identities on the active sum, before any reduction. -/
theorem up_trace_identity
    (ha : ∀ v, SupportedOn D.active v → SupportedOn D.active (D.Up v))
    (hold : OldBlockCubic D) {v : X.I → X.K} (hv : SupportedOn D.active v) :
    D.Up (D.Up (tV X.ρ P.φ v)) = D.Up (D.Up (D.Up v)) + dV X.ρ P.φ (D.Up v) ∧
      D.Up (dV X.ρ P.φ v) = dV X.ρ P.φ (D.Up v) := by
  have hs : D.active = (D.active ∩ D.ramified) ∪ OldCoordinates D := by
    ext i
    classical
    simp only [OldCoordinates, Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]
    by_cases h : i ∈ D.ramified <;> simp [h]
  have hdis : Disjoint (D.active ∩ D.ramified) (OldCoordinates D) :=
    Set.disjoint_left.mpr (fun _ h h' => h'.2 h.2)
  let r := mask (D.active ∩ D.ramified) v
  let o := mask (OldCoordinates D) v
  have hvr : SupportedOn (D.active ∩ D.ramified) r := fun i hi =>
    mask_supported hv i (fun h => hi h.1)
  have hvo : SupportedOn (OldCoordinates D) o := fun i hi =>
    mask_supported hv i (fun h => hi h.1)
  have hsplit : v = r + o := split_supported hdis (hs ▸ hv)
  obtain ⟨hr, hdr⟩ := ramified_law D hvr
  obtain ⟨hto, hdo, hco⟩ := hold o hvo
  have htoo := (hold _ (old_stable D ha hvo)).1
  have ho : D.Up (D.Up (tV X.ρ P.φ o)) =
      D.Up (D.Up (D.Up o)) + dV X.ρ P.φ (D.Up o) := by
    rw [hto, htoo]
    have he : D.Up (D.Up (D.Up o)) + dV X.ρ P.φ (D.Up o) -
        tV X.ρ P.φ (D.Up (D.Up o)) = 0 := by
      convert hco using 1
      abel
    exact (sub_eq_zero.mp he).symm
  rw [hsplit]
  simp only [map_add, hr, ho, hdr, hdo]
  constructor
  · abel
  · trivial

end ZInQ.Manuscript.RC.KsplitHpacket
