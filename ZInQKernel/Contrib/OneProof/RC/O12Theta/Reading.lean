import ZInQKernel.Contrib.OneProof.RC.O12.Fourier
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! The coefficient-one functional. Extending the reading off the prime
subfield is linear algebra (given here); the manuscript's values are in
the prime subfield (tex 9688–9698). -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12Theta

open O12

variable {O : Type} [CommRing O] (m : Ideal O)

private theorem residue_char_two (hm : m.IsMaximal) (h2 : (2 : O) ∈ m) :
    CharP (O ⧸ m) 2 := by
  letI := hm
  have h := ringChar.dvd (R := O ⧸ m) (x := 2) (by
    simpa only [map_ofNat, Nat.cast_two] using (Ideal.Quotient.eq_zero_iff_mem.mpr h2 :
      Ideal.Quotient.mk m (2 : O) = 0))
  rcases (Nat.dvd_prime Nat.prime_two).mp h with h | h
  · exact False.elim (CharP.char_ne_one (O ⧸ m) (ringChar (O ⧸ m)) h)
  · exact ringChar.of_eq h

private theorem exists_decode (hm : m.IsMaximal) (h2 : (2 : O) ∈ m) :
    ∃ d : (O ⧸ m) →+ ZMod 2, d 1 = 1 := by
  letI := hm
  letI := residue_char_two m hm h2
  letI := ZMod.algebra (O ⧸ m) 2
  obtain ⟨d, hd⟩ := Module.Projective.exists_dual_eq_one (ZMod 2)
    (show (1 : O ⧸ m) ≠ 0 from one_ne_zero)
  exact ⟨d.toAddMonoidHom, hd⟩

/-- An additive prime-subfield retraction; its values on the rest of the
residue field are immaterial to the manuscript's readings. -/
def decode (hm : m.IsMaximal) (h2 : (2 : O) ∈ m) : (O ⧸ m) →+ ZMod 2 :=
  (exists_decode m hm h2).choose

theorem decode_one (hm : m.IsMaximal) (h2 : (2 : O) ∈ m) : decode m hm h2 1 = 1 :=
  (exists_decode m hm h2).choose_spec

/-- Evaluate the reduced expansion at its positive index one. -/
def readOne (hm : m.IsMaximal) (h2 : (2 : O) ∈ m) : (PosIndex → O ⧸ m) →+ ZMod 2 :=
  (decode m hm h2).comp (Pi.evalAddMonoidHom _ ⟨1, one_ne_zero⟩)


end ZInQ.Manuscript.RC.O12Theta
