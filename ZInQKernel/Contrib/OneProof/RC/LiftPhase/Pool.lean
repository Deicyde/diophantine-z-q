import ZInQKernel.Contrib.OneProof.RC.LiftPhase.Local
import ZInQKernel.Contrib.OneProof.RC.PoolCharacter.Identification

/-! The same phase at the old and common levels (tex 8925–8936,
8982–8985 and 9706–9710). The residue comparison is on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.LiftPhase

open Adelic ThetaJoin BlocksPerU PoolCharacter
open scoped BigOperators

variable {O : Type} [CommRing O] {ell N m D : ℕ}
variable (C : LevelRoots O N) (hn : 2 * m * N * ell ≠ 0)

/-- The conductors of the actual local scalar factors divide the old level
once it contains four, the extraction and detecting primes, and each level prime. -/
theorem residueModuli_dvd (h4 : 4 ∣ D) (hm : m ∣ D) (he : ell ∣ D)
    (hN : ∀ q : Adelic.Prime, q.val ∣ N → q.val ∣ D) (q : Places m N ell hn) :
    rootModulus q.val ∣ D := by
  by_cases hq : q.val.val = 2
  · simpa [rootModulus, hq] using h4
  simp only [rootModulus, ite_eq_right hq, pow_one]
  have hd := (mem_exceptionalPlaces m N ell hn q.val).mp q.prop
  rcases q.val.prop.dvd_mul.mp hd with hd | hd
  · rcases q.val.prop.dvd_mul.mp hd with hd | hd
    · rcases q.val.prop.dvd_mul.mp hd with hd | hd
      · exact False.elim (hq ((Nat.prime_dvd_prime_iff_eq q.val.prop Nat.prime_two).mp hd))
      · exact hd.trans hm
    · exact hN q.val hd
  · exact hd.trans he

variable [NeZero D]

/-- The common unit group sees the full scaling product and the (O.5) twist. -/
def poolPhase (h4 : 4 ∣ D) (hc : ∀ q : Places m N ell hn, rootModulus q.val ∣ D) :
    (ZMod D)ˣ →* Oˣ :=
  phaseCharacter h4 m Finset.univ (fun q : Places m N ell hn => rootModulus q.val) hc
    (fun q => residueAlpha (ell := ell) (m := m) C q.val)

omit [NeZero D] in
private theorem representative_away
    (hc : ∀ q : Places m N ell hn, rootModulus q.val ∣ D) (u : (ZMod D)ˣ) :
    (schwartzPhase C m hn).Away (representative u) := by
  intro q hq
  exact q.prop.coprime_iff_not_dvd.mp
    ((ZMod.val_coe_unit_coprime u).of_dvd_right
      ((prime_dvd_rootModulus q).trans (hc ⟨q, hq⟩))).symm

/-- The pool constructor evaluates (O.5) using the stage's own integer
phase, before reduction or embedding. -/
theorem poolPhase_eval (h4 : 4 ∣ D) (hm : m ∣ D) (h3 : m % 4 = 3)
    (hc : ∀ q : Places m N ell hn, rootModulus q.val ∣ D) (u : (ZMod D)ˣ) :
    (poolPhase C hn h4 hc u : O) = (schwartzPhase C m hn).eta m (representative u) := by
  classical
  have h2 : Nat.Coprime 2 m := Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
  have h4m : Nat.Coprime 4 m := by simpa using h2.pow_left 2
  have ha := representative_away C hn hc u
  rw [poolPhase, phaseCharacter_value h4 (h4m.mul_dvd_of_dvd_of_dvd h4 hm),
    PhaseData.eta, ite_eq_left ha, PhaseData.phase, dite_eq_left ha, PhaseData.scalar, Units.coe_prod]
  congr 1
  change (∏ q : Places m N ell hn, _) = _
  apply Finset.prod_congr rfl
  intro q _
  apply residueAlpha_nat C q.val (ha q.val q.prop)
  rw [ZMod.unitsMap_val, ← ZMod.cast_natCast (hc q) (representative u), ZMod.natCast_zmod_val]

/-- The two-power order input of `diamondCharacters` on the common units. -/
theorem poolPhase_order (h4 : 4 ∣ D) (hm : m ∣ D) (h3 : m % 4 = 3)
    (hc : ∀ q : Places m N ell hn, rootModulus q.val ∣ D) (u : (ZMod D)ˣ) :
    ∃ e : ℕ, (poolPhase C hn h4 hc u : O) ^ (2 ^ e : ℕ) = 1 := by
  rw [poolPhase_eval C hn h4 hm h3 hc u]
  exact ⟨_, eta_order_of_away C hn (representative_away C hn hc u)⟩


end ZInQ.Manuscript.RC.LiftPhase
