import ZInQKernel.Contrib.OneProof.RC.BlocksPerU.Sieve
import ZInQKernel.Contrib.OneProof.RC.Odd.ThetaLocal
import ZInQKernel.Contrib.OneProof.RC.WeilIndex.Character

/-! The empty moving-sieve character on the fixed pool, and its comparison
with the local product in (O.5), tex 8891–8936, 8978–8986, 9491–9496,
9497–9555 and 9647–9662. The transport to the common unit group is (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.PoolCharacter

open BlocksPerU ThetaCoeff WeilIndex
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped BigOperators

variable {O K : Type} [CommRing O] [Field K] [Algebra O K]

/-- Before moving any primes, the pool character is the stage phase times
the quadratic sign `(-1/d)`, using the pool's chosen representative. -/
theorem embedded_bCharacter_empty {G : Type} [Group G] {ηsource : ℕ → O}
    (κ : K →+* ℂ) (C : DiamondCharacters O G ηsource) (u : G) :
    (((Units.map κ).comp (bCharacter (K := K) C ∅) u : ℂˣ) : ℂ) =
      κ (algebraMap O K (ηsource (C.representative u))) *
        (jacobiSym (-1) (C.representative u) : ℂ) := by
  have h4 : (4 * (-1) : ℤ) ∣ (C.level : ℤ) := by
    have h : (4 : ℤ) ∣ (C.level : ℤ) := by exact_mod_cast C.four_dvd
    simpa using h
  change κ (↑(bCharacter (K := K) C ∅ u) : K) = _
  rw [bCharacter_value]
  simp [DiamondCharacters.ψ, C.η_eval, C.symbol_eval (-1) u h4]

private def quadraticSymbols (N : ℕ) [NeZero N] (h4 : 4 ∣ N) :
    DiamondCharacters ℤ (ZMod N)ˣ (fun _ => 1) :=
  diamondCharacters h4 1 (fun _ => rfl) (fun _ => ⟨0, by simp⟩)

/-- The phase of (O.5) in the character ring: pull back the local scaling
characters and multiply by the genus character of `-m`. -/
def phaseCharacter {N : ℕ} [NeZero N] (h4 : 4 ∣ N) (m : ℕ)
    {ι : Type*} (s : Finset ι) (c : ι → ℕ) (hc : ∀ i, c i ∣ N)
    (α : ∀ i, (ZMod (c i))ˣ →* Oˣ) : (ZMod N)ˣ →* Oˣ :=
  (∏ i ∈ s, (α i).comp (ZMod.unitsMap (hc i))) *
    (Units.map (Int.castRingHom O)).comp ((quadraticSymbols N h4).symbol (-(m : ℤ)))

/-- The phase is built directly from the local values and the genus
symbol, before choosing any complex embedding or diamond scalars. -/
theorem phaseCharacter_value {N : ℕ} [NeZero N] (h4 : 4 ∣ N) {m : ℕ} (hm4 : 4 * m ∣ N)
    {ι : Type*} (s : Finset ι) (c : ι → ℕ) (hc : ∀ i, c i ∣ N)
    (α : ∀ i, (ZMod (c i))ˣ →* Oˣ) (u : (ZMod N)ˣ) :
    (phaseCharacter h4 m s c hc α u : O) =
      (∏ i ∈ s, (α i (ZMod.unitsMap (hc i) u) : O)) *
        (jacobiSym (-(m : ℤ)) (representative u) : O) := by
  have h : (4 * -(m : ℤ)) ∣ (N : ℤ) := by
    have h' : (4 * (m : ℤ)) ∣ (N : ℤ) := by exact_mod_cast hm4
    simpa using h'
  have he := (quadraticSymbols N h4).symbol_eval (-(m : ℤ)) u h
  change _ = jacobiSym (-(m : ℤ)) (representative u) at he
  simp [phaseCharacter, MonoidHom.finsetProd_apply, he]

variable {L : Type} [AddCommGroup L] {ε : L →+ ZMod 2} {T : TypeData L ε}
    {avoid : Finset ℕ} {M W N : ℕ} {S : AppF.ThetaStage (Odd.StageRing O M)}
    {P : Window T.Good S W} [NeZero N] [NeZero S.m]

/-- For the actual constructor used by `realize_of_stage`, the old-stage
character equality is equivalent to using the embedded (O.5) phase for the
same stage lift. The local factors include *all* scaling characters, including
the quadratic factors at the extraction primes and the detecting prime. -/
theorem oldCharacter_comp_eq_bCharacter_iff (κ : K →+* ℂ) (Dₗ : LevelSetup P avoid N)
    (E : Lift S) (η : (ZMod N)ˣ →* Oˣ)
    (η_eval : ∀ u, (η u : O) = E.η (representative u))
    (η_order : ∀ u, ∃ e : ℕ, (η u : O) ^ (2 ^ e : ℕ) = 1)
    (hm : S.m ∣ Dₗ.old) (h3 : S.m % 4 = 3)
    {ι : Type*} (s : Finset ι) (c : ι → ℕ) (hc : ∀ i, c i ∣ Dₗ.old)
    (α : ∀ i, (ZMod (c i))ˣ →* ℂˣ) :
    (oldCharacter Dₗ.four_dvd hm s c hc α).comp (ZMod.unitsMap Dₗ.old_dvd) =
      (Units.map κ).comp (bCharacter (K := K)
        (diamondCharacters Dₗ.common_four η η_eval η_order) ∅) ↔
    ∀ u : (ZMod N)ˣ, κ (algebraMap O K (E.η (representative u))) =
      (∏ i ∈ s, (α i (ZMod.unitsMap ((hc i).trans Dₗ.old_dvd) u) : ℂ)) *
        (jacobiSym (-(S.m : ℤ)) (representative u) : ℂ) := by
  rw [oldCharacter_comp_eq_iff Dₗ.four_dvd hm s c hc α h3 Dₗ.old_dvd]
  apply forall_congr'
  intro u
  rw [embedded_bCharacter_empty]
  simp only [diamondCharacters]
  have hj : (jacobiSym (S.m : ℤ) (representative u) : ℂ) =
      (jacobiSym (-(S.m : ℤ)) (representative u) : ℂ) *
        (jacobiSym (-1) (representative u) : ℂ) := by
    rw [mul_comm]
    exact_mod_cast Odd.psi_div_eta (S.m : ℤ) (representative u)
  have hs : (jacobiSym (-1) (representative u) : ℂ) ≠ 0 := by
    have hsq : jacobiSym (-1) (representative u) * jacobiSym (-1) (representative u) = 1 := by
      rw [← jacobiSym.mul_left]
      norm_num
    exact_mod_cast (show jacobiSym (-1) (representative u) ≠ 0 from by
      intro h
      simp [h] at hsq)
  change _ = (∏ i ∈ s, (α i (ZMod.unitsMap ((hc i).trans Dₗ.old_dvd) u) : ℂ)) *
    (jacobiSym (S.m : ℤ) (representative u) : ℂ) ↔ _
  rw [hj, ← mul_assoc]
  exact ⟨mul_right_cancel₀ hs, fun h => congrArg (· * _) h⟩

/-- For the phase defined by (O.5), the usual stage evaluation and order
arguments to the pool constructor suffice. The common embedding is used on
those same local factors. This supplies `hchar` in
`OldStageLaw.oldStageLaw_of_finiteAction`. -/
theorem oldCharacter_comp_eq_bCharacter_of_phase (κ : K →+* ℂ) (Dₗ : LevelSetup P avoid N)
    (E : Lift S) (hm : S.m ∣ Dₗ.old) (h3 : S.m % 4 = 3)
    {ι : Type*} (s : Finset ι) (c : ι → ℕ) (hc : ∀ i, c i ∣ Dₗ.old)
    (α : ∀ i, (ZMod (c i))ˣ →* Oˣ)
    (η_eval : ∀ u, (phaseCharacter Dₗ.common_four S.m s c
        (fun i => (hc i).trans Dₗ.old_dvd) α u : O) = E.η (representative u))
    (η_order : ∀ u, ∃ e : ℕ, (phaseCharacter Dₗ.common_four S.m s c
        (fun i => (hc i).trans Dₗ.old_dvd) α u : O) ^ (2 ^ e : ℕ) = 1) :
    (oldCharacter Dₗ.four_dvd hm s c hc
      (fun i => (Units.map (κ.comp (algebraMap O K))).comp (α i))).comp
        (ZMod.unitsMap Dₗ.old_dvd) =
      (Units.map κ).comp (bCharacter (K := K)
        (diamondCharacters Dₗ.common_four _ η_eval η_order) ∅) := by
  apply (oldCharacter_comp_eq_bCharacter_iff κ Dₗ E _ η_eval η_order hm h3 s c hc _).2
  intro u
  have h2 : Nat.Coprime 2 S.m := Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
  have h4 : Nat.Coprime 4 S.m := by simpa using h2.pow_left 2
  have hm4 := h4.mul_dvd_of_dvd_of_dvd Dₗ.common_four (hm.trans Dₗ.old_dvd)
  rw [← η_eval u]
  simpa using congrArg (κ.comp (algebraMap O K))
    (phaseCharacter_value Dₗ.common_four hm4 s c (fun i => (hc i).trans Dₗ.old_dvd) α u)


end ZInQ.Manuscript.RC.PoolCharacter
