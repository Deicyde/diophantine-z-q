import ZInQKernel.Contrib.OneProof.CasselsTatePairing
import ZInQKernel.Contrib.OneProof.CasselsTate.SelmerMultiplication

/-! Descent of a finite Cassels–Tate pairing from the Selmer group to the
torsion of the Tate–Shafarevich group at the same level. -/

noncomputable section

namespace ZInQ.Manuscript.CasselsTateGlobal

open SelmerTwoPower

/-- Reversing an alternating biadditive pairing negates its value. -/
theorem pairing_skew {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (b : A →+ A →+ B) (h : ∀ x, b x x = 0) (x y : A) : b x y = -b y x := by
  have hxy := h (x + y)
  simp only [map_add, AddMonoidHom.add_apply, h, zero_add, add_zero] at hxy
  exact eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm] using hxy)

private theorem exists_pairing_of_surjective
    {T S B C : Type*} [AddCommGroup T] [AddCommGroup S] [AddCommGroup B] [AddCommGroup C]
    (φ : S →+ B) (hφ : Function.Surjective φ) (ψ : T →+ S) (hψ : φ.ker ≤ ψ.range)
    (b : S →+ S →+ C) (halt : ∀ x, b x x = 0)
    (hrad : ∀ x, (∀ y, b x y = 0) ↔ x ∈ ψ.range) :
    ∃ d : B →+ B →+ C, (∀ x, d x x = 0) ∧ ∀ x,
      (∀ y, d x y = 0) ↔ x ∈ (φ.comp ψ).range := by
  let s := Function.surjInv hφ
  have hs : Function.RightInverse s φ := Function.rightInverse_surjInv hφ
  have hb : φ.ker ≤ b.ker := fun _ hx =>
    AddMonoidHom.mem_ker.mpr (AddMonoidHom.ext ((hrad _).mpr (hψ hx)))
  let c : B →+ S →+ C := φ.liftOfRightInverse s hs ⟨b, hb⟩
  have hc (x : S) : c (φ x) = b x := φ.liftOfRightInverse_comp_apply s hs _ x
  have hcKer : φ.ker ≤ c.flip.ker := by
    intro y hy
    apply AddMonoidHom.mem_ker.mpr
    ext x
    obtain ⟨x, rfl⟩ := hφ x
    change c (φ x) y = 0
    rw [hc, pairing_skew b halt, (hrad y).mpr (hψ hy) x, neg_zero]
  let d : B →+ B →+ C := (φ.liftOfRightInverse s hs ⟨c.flip, hcKer⟩).flip
  have hd (x y : S) : d (φ x) (φ y) = b x y := by
    change (φ.liftOfRightInverse s hs ⟨c.flip, hcKer⟩) (φ y) (φ x) = _
    rw [φ.liftOfRightInverse_comp_apply]
    exact DFunLike.congr_fun (hc x) y
  refine ⟨d, ?_, ?_⟩
  · intro x
    obtain ⟨x, rfl⟩ := hφ x
    rw [hd, halt]
  · intro x
    constructor
    · intro hx
      obtain ⟨x, rfl⟩ := hφ x
      obtain ⟨z, hz⟩ := (hrad x).mp (fun y => (hd x y).symm.trans (hx (φ y)))
      exact ⟨z, congrArg φ hz⟩
    · rintro ⟨z, rfl⟩ y
      obtain ⟨y, rfl⟩ := hφ y
      change d (φ (ψ z)) (φ y) = 0
      rw [hd]
      exact (hrad _).mpr ⟨z, rfl⟩ y

/-- At level `n`, the radical of the alternating Selmer pairing is the image
of the transition from level `n²`. -/
def FiniteSelmerPairingAt (E : WeierstrassCurve ℚ) (n : ℕ) : Prop :=
  let S := E.selmerGroup Fam.emb n
  ∃ b : S →+ S →+ QZ, (∀ x, b x x = 0) ∧ ∀ x,
    (∀ y, b x y = 0) ↔ x ∈ (E.selmerMultiplication Fam.emb n n).range

/-- The Selmer pairing descends to `Sha[n]`. Its radical consists exactly of
the classes divisible by `n` in `Sha`. -/
theorem fam_sha_torsion_pairing_of_finiteSelmerPairing (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (n : ℕ) (hn : IsUnit (n : ℚ)) (hPair : FiniteSelmerPairingAt E n) :
    let A := Fam.sha E
    let B := AddSubgroup.torsionBy A n
    ∃ b : B →+ B →+ QZ, (∀ x, b x x = 0) ∧ ∀ x,
      (∀ y, b x y = 0) ↔ ∃ z : A, n • z = (x : A) := by
  have hnn : IsUnit ((n * n : ℕ) : ℚ) := by rw [Nat.cast_mul]; exact hn.mul hn
  obtain ⟨b, halt, hrad⟩ := hPair
  obtain ⟨d, hd, hker⟩ := exists_pairing_of_surjective (E.selmerShaMap Fam.emb n)
    (E.selmerShaMap_surjective Fam.emb hn) (E.selmerMultiplication Fam.emb n n)
    (E.ker_selmerShaMap_le_range_multiplication Fam.emb n n hn hnn) b halt hrad
  exact ⟨d, hd, fun x => (hker x).trans (E.mem_range_selmerShaMap_multiplication_iff
    Fam.emb n n hnn x)⟩

/-- The quotient map `Selₙ → Sha[n]` transfers finiteness to the manuscript's
Tate–Shafarevich group. -/
theorem sha_torsion_finite_of_finiteSelmer (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (n : ℕ) (hn : 2 ≤ n) (hfin : Finite (E.selmerGroup Fam.emb n)) :
    Finite (AddSubgroup.torsionBy (sha E) n) := by
  rw [Fam.sha_eq]
  have hn' : IsUnit (n : ℚ) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))
  exact Finite.of_surjective (E.selmerShaMap Fam.emb n) (E.selmerShaMap_surjective Fam.emb hn')

/-- A finite-level Selmer pairing gives the pairing with its divisibility
radical on the manuscript's two-family definition of `Sha[n]`. -/
theorem sha_torsion_pairing_of_finiteSelmerPairing (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (n : ℕ) (hn : 2 ≤ n) (hPair : FiniteSelmerPairingAt E n) :
    let A := sha E
    let B := AddSubgroup.torsionBy A n
    ∃ b : B →+ B →+ QZ, (∀ x, b x x = 0) ∧ ∀ x,
      (∀ y, b x y = 0) ↔ ∃ z : A, n • z = (x : A) := by
  rw [Fam.sha_eq]
  have hn' : IsUnit (n : ℚ) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))
  exact fam_sha_torsion_pairing_of_finiteSelmerPairing E n hn' hPair

end ZInQ.Manuscript.CasselsTateGlobal
