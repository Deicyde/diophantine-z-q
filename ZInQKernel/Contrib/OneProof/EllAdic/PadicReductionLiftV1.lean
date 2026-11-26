import ZInQKernel.Contrib.OneProof.EllAdic.PadicReductionContinuityV1

set_option autoImplicit false

namespace RC53.EllAdic

/-- A compatible sequence of locally constant finite residue sections has a
unique continuous lift to the actual p-adic integers. The equality witnesses
use the same point of the domain and the actual residue ring homomorphisms. -/
theorem existsUnique_continuous_lift_padicReductions {p : ℕ} [Fact p.Prime]
    {U : Type*} [TopologicalSpace U] (r : (n : ℕ) → U → ZMod (p ^ n))
    (hloc : ∀ n, IsLocallyConstant (r n))
    (hcompat : ∀ (n : ℕ) (x : U), (ZMod.cast (r (n + 1) x) : ZMod (p ^ n)) = r n x) :
    ∃! f : U → ℤ_[p], Continuous f ∧ ∀ (n : ℕ) (x : U), PadicInt.toZModPow n (f x) = r n x := by
  let seq (x : U) (n : ℕ) : ℤ := (r n x).val
  have hstep (x : U) (n : ℕ) : (p : ℤ) ^ n ∣ seq x (n + 1) - seq x n := by
    rw [← Nat.cast_pow, ← ZMod.intCast_eq_intCast_iff_dvd_sub]
    calc
      ((seq x n : ℤ) : ZMod (p ^ n)) = r n x := by
        simp only [seq, Int.cast_natCast, ZMod.natCast_zmod_val]
      _ = ZMod.cast (r (n + 1) x) := (hcompat n x).symm
      _ = ZMod.cast ((r (n + 1) x).val : ZMod (p ^ (n + 1))) :=
        congrArg (fun a : ZMod (p ^ (n + 1)) => (ZMod.cast a : ZMod (p ^ n)))
          (ZMod.natCast_zmod_val (r (n + 1) x)).symm
      _ = ((seq x (n + 1) : ℤ) : ZMod (p ^ n)) := by
        simpa only [seq, Int.cast_natCast] using
          ZMod.cast_natCast (pow_dvd_pow p (Nat.le_succ n)) (r (n + 1) x).val
  let f (x : U) : ℤ_[p] := PadicInt.ofIntSeq _
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (seq x) p (hstep x))
  have hred (n : ℕ) (x : U) : PadicInt.toZModPow n (f x) = r n x := by
    simpa only [f, seq, Int.cast_natCast, ZMod.natCast_zmod_val] using
      PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (seq x) p (hstep x) n
  have hcont : Continuous f := (continuous_iff_locallyConstant_padicReductions f).2 fun n => by
    rw [show (fun x => PadicInt.toZModPow n (f x)) = r n from funext (hred n)]
    exact hloc n
  refine ⟨f, ⟨hcont, hred⟩, ?_⟩
  intro g hg
  funext x
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  exact (hg.2 n x).trans (hred n x).symm

end RC53.EllAdic
