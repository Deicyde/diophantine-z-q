"""d2a6-reroute: emit LTGoodRed.goodRedTorsion (TailF) as goodRedTorsionT with the hypothesis "3 is a unit"
replaced by "a prime p outside T is not a unit" (the manuscript's L529-530 good reduction outside S).
Usage (repository root): python3 scratch/d2a6-reroute/gen/gen_goodred.py > OUT"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from copylib import emit
F = "ZInQKernel/OneProof/H/TailF.lean"
OLD3 = """  have hp3' : p ≠ 3 := fun h => hp3 (by rw [h]; exact Finset.mem_singleton_self 3)
  have h3 : IsUnit (3 : O) := by
    have := hunit 3 ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3'))
    exact_mod_cast this
"""
NEW3 = """  have hpO : ¬ IsUnit ((p : ℕ) : O) := by
    intro hu
    obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.mp hu
    have hc' : (p : K) * (c : K) = 1 := by
      have := congrArg Subtype.val hc
      push_cast at this
      exact this
    have hpi : ((p : K))⁻¹ ∈ O := by
      rw [← eq_inv_of_mul_eq_one_right hc']
      exact c.2
    rw [ValuationSubring.mem_comap, map_inv₀, map_natCast] at hpi
    rw [ValuationSubring.mem_nonunits_iff_or] at hpw
    rcases hpw with h | h
    · exact hp.ne_zero (by exact_mod_cast h)
    · exact h hpi
"""
edits = [
    ("theorem goodRedTorsionT : HSyn.LinkedTate.GoodRedTorsion := by",
     "theorem goodRedTorsionT (T : Finset ℕ) : _root_.HDec.D2A6.GoodRedTorsionT T := by"),
    (OLD3, NEW3),
    ("(hA O h3)", "(hA O p hp hp3 hpO)"),
]
txt = emit(F, "goodRedTorsion", {"goodRedTorsion": "goodRedTorsionT"}, edits, ("theorem",))
txt = txt.replace("/-- **`GoodRedTorsion` proved**", "/-- **`GoodRedTorsionT T` proved** (d2a6-reroute: a copy of lt-goodred's `goodRedTorsion`, TailF, with the hypothesis on DVRs in which `3` is a unit replaced by DVRs in which a prime `p ∉ T` is not a unit)", 1)
print(txt)
