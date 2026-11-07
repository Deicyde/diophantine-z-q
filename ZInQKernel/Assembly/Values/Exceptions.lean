import ZInQKernel.Assembly.Values.Chains
import ZInQKernel.Assembly.Values.Gadgets

/-!
# Semantics of the exceptional values

Blueprint: `assembly/value-templates/exceptions-semantics.md`.

`Rel_{value.exceptions}(N, t)` holds exactly when `N = ι(c)` and `t = c` for some contact value
`c ∈ 𝒞 = {0, -15, -20, -24, -30, -60}` (`Compiler.Precision.contacts`). Each branch `β_c` of the
template is the chain for `|c|` on the generator point `G` (or on `neg(G)` for `c < 0`), which
evaluates to `ι(c)` once the generator constants force `G = ι(1)`.
-/

namespace ZInQ.Assembly

open Syntax MvPolynomial Translation Compiler.Precision

/-- The states reached by the constructions of the branches: the generator constants are
recorded at `X₆, X₇, X₈` and the counter is past them. -/
def BranchState (s : BuildState) : Prop := s.globals = exceptionsGlobals ∧ 9 ≤ s.next

theorem gen_initial : Build.gen ⟨6, []⟩ = (genPoint 6, ⟨9, exceptionsGlobals⟩) := rfl

theorem gen_of_globals (s : BuildState) (h : s.globals = exceptionsGlobals) :
    Build.gen s = (genPoint 6, s) := by
  obtain ⟨n, g⟩ := s
  subst h
  rfl

/-- The construction of a branch after its generator request. -/
theorem exceptionBranch_eq (N : Code) (t : Poly) (c : ℤ) (s s' : BuildState)
    (hs : Build.gen s = (genPoint 6, s')) :
    exceptionBranch N t c s =
      (.and [.and (fixedMultipleBuild (genPoint 6) c s').1.2,
        peq N (fixedMultipleBuild (genPoint 6) c s').1.1, .eq t (C c)],
        (fixedMultipleBuild (genPoint 6) c s').2) := by
  simp only [exceptionBranch, Build.bind_apply, hs]
  rfl

/-- The value of the base of the chain of `c`: `ι(±1)`. -/
theorem evCode_chainBase {y : ℕ → ℚ} (hg : evCode y (genPoint 6) = iota 1) (c : ℤ) :
    evCode y (if c < 0 then (genPoint 6).neg else genPoint 6) =
      iota (if c < 0 then -1 else 1) := by
  split_ifs
  · exact evCode_neg_iota hg
  · exact hg

theorem natAbs_mul_sign (c : ℤ) : (c.natAbs : ℤ) * (if c < 0 then -1 else 1) = c := by
  rw [Int.natCast_natAbs]
  split_ifs with h
  · rw [abs_of_neg h]; ring
  · rw [abs_of_nonneg (not_lt.1 h), mul_one]

theorem varsIn_genPoint (i : Fin 5) : VarsIn (genPoint 6 i) (· < 9) := by
  fin_cases i
  · exact VarsIn.zero _
  · exact VarsIn.X (by decide)
  · exact VarsIn.neg (VarsIn.ofNat 145 _)
  · exact VarsIn.X (by decide)
  · exact VarsIn.X (by decide)

theorem varsIn_chainBase (c : ℤ) (i : Fin 5) :
    VarsIn ((if c < 0 then (genPoint 6).neg else genPoint 6) i) (· < 9) := by
  split_ifs
  · fin_cases i
    · exact varsIn_genPoint 0
    · exact varsIn_genPoint 1
    · exact varsIn_genPoint 2
    · exact (varsIn_genPoint 3).neg
    · exact (varsIn_genPoint 4).neg
  · exact varsIn_genPoint i

theorem varsIn_O (i : Fin 5) (n : ℕ) : VarsIn (Code.O i) (· < n) := by
  fin_cases i
  · exact VarsIn.one _
  all_goals exact VarsIn.zero _

/-- **One branch.** From a state whose generator request returns `G` with the constants recorded,
the branch `β_c` keeps the branch states; it implies `N = ι(c)` and `t = c` at every assignment
giving `G` the value `ι(1)`; and conversely it can be satisfied without changing the variables
below the counter. -/
theorem exceptionBranch_spec (c : ℤ) (s s' : BuildState) (hs : Build.gen s = (genPoint 6, s'))
    (hs' : BranchState s') :
    BranchState (exceptionBranch (varPoint 0) (X 5) c s).2 ∧
    (∀ y : ℕ → ℚ, evCode y (genPoint 6) = iota 1 →
      (exceptionBranch (varPoint 0) (X 5) c s).1.Lift y →
        evCode y (varPoint 0) = iota c ∧ y 5 = c) ∧
    (∀ y : ℕ → ℚ, evCode y (genPoint 6) = iota 1 → evCode y (varPoint 0) = iota c → y 5 = c →
      ∃ y' : ℕ → ℚ, (∀ i < s'.next, y' i = y i) ∧
        (exceptionBranch (varPoint 0) (X 5) c s).1.Lift y') := by
  rw [exceptionBranch_eq _ _ c s s' hs]
  simp only [fixedMultipleBuild]
  set base := if c < 0 then (genPoint 6).neg else genPoint 6 with hbase
  have hlift : ∀ y : ℕ → ℚ, (Formula.and [.and (chainBuild Code.O base (binDigits c.natAbs) s').1.2,
      peq (varPoint 0) (chainBuild Code.O base (binDigits c.natAbs) s').1.1,
      .eq (X 5) (C c)]).Lift y ↔
      (∀ φ ∈ (chainBuild Code.O base (binDigits c.natAbs) s').1.2, φ.Lift y) ∧
        evCode y (varPoint 0) = evCode y (chainBuild Code.O base (binDigits c.natAbs) s').1.1 ∧
        y 5 = c := by
    intro y
    simp only [Formula.lift_and, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, lift_peq, Formula.lift_eq, ev_X, ev_C]
  have hval : ∀ y : ℕ → ℚ, evCode y (genPoint 6) = iota 1 →
      (∀ φ ∈ (chainBuild Code.O base (binDigits c.natAbs) s').1.2, φ.Lift y) →
      evCode y (chainBuild Code.O base (binDigits c.natAbs) s').1.1 = iota c := by
    intro y hg h
    rw [chainBuild_binDigits_value _ _ _ y _ (evCode_chainBase hg c) h, natAbs_mul_sign]
  refine ⟨?_, fun y hg h => ?_, fun y hg hN ht => ?_⟩
  · obtain ⟨h1, h2⟩ := chainBuild_state (binDigits c.natAbs) Code.O base s'
    exact ⟨h1.trans hs'.1, hs'.2.trans h2⟩
  · obtain ⟨hc, hN, ht⟩ := (hlift y).1 h
    exact ⟨hN.trans (hval y hg hc), ht⟩
  · obtain ⟨y', hy', hc⟩ := chain_satisfiable (binDigits c.natAbs) Code.O base s' y 0 _
      (fun i => varsIn_O i _) (fun i => (varsIn_chainBase c i).mono fun j (hj : j < 9) =>
        show j < s'.next by have := hs'.2; omega)
      (evCode_O' y) (evCode_chainBase hg c)
    have h9 : ∀ i < 9, y' i = y i := fun i hi => hy' i (by have := hs'.2; omega)
    have hg' : evCode y' (genPoint 6) = iota 1 := by
      rw [← hg]
      exact evCode_congr fun i j hj => h9 j (varsIn_genPoint i j hj)
    refine ⟨y', hy', (hlift y').2 ⟨hc, ?_, ?_⟩⟩
    · rw [hval y' hg' hc, ← hN]
      exact evCode_congr fun i j hj => h9 j (varsIn_varPoint (by norm_num) i j hj)
    · rw [h9 5 (by norm_num), ht]

/-- The construction of `value.exceptions`, branch by branch. -/
theorem exceptionsBuild_eq :
    exceptionsBuild (varPoint 0) (X 5) ⟨6, []⟩ =
      let r0 := exceptionBranch (varPoint 0) (X 5) 0 ⟨6, []⟩
      let r1 := exceptionBranch (varPoint 0) (X 5) (-15) r0.2
      let r2 := exceptionBranch (varPoint 0) (X 5) (-20) r1.2
      let r3 := exceptionBranch (varPoint 0) (X 5) (-24) r2.2
      let r4 := exceptionBranch (varPoint 0) (X 5) (-30) r3.2
      let r5 := exceptionBranch (varPoint 0) (X 5) (-60) r4.2
      (.and [.call memberTemplate (varPoint 0) r5.2.next, .or [r0.1, r1.1, r2.1, r3.1, r4.1, r5.1]],
        { r5.2 with next := r5.2.next + memberTemplate.witnesses }) := rfl

/-- **Semantics of the exceptional values.** For all `N ∈ ℚ⁵` and `t ∈ ℚ`,
`Rel_{value.exceptions}(N, t) ⟺ ∃ c ∈ 𝒞, N = ι(c) ∧ t = c`. -/
theorem exceptions_rel_iff (N : Fin 5 → ℚ) (t : ℚ) :
    exceptionsTemplate.Rel (Fin.append N ![t]) ↔ ∃ c ∈ contacts, N = iota c ∧ t = c := by
  rw [exceptionsTemplate_rel_iff, exceptionsBuild_eq]
  -- the six branch specifications, along the chain of states
  have g0 := gen_initial
  have P0 : BranchState ⟨9, exceptionsGlobals⟩ := ⟨rfl, le_rfl⟩
  obtain ⟨S0, sound0, comp0⟩ := exceptionBranch_spec 0 _ _ g0 P0
  obtain ⟨S1, sound1, comp1⟩ := exceptionBranch_spec (-15) _ _ (gen_of_globals _ S0.1) S0
  obtain ⟨S2, sound2, comp2⟩ := exceptionBranch_spec (-20) _ _ (gen_of_globals _ S1.1) S1
  obtain ⟨S3, sound3, comp3⟩ := exceptionBranch_spec (-24) _ _ (gen_of_globals _ S2.1) S2
  obtain ⟨S4, sound4, comp4⟩ := exceptionBranch_spec (-30) _ _ (gen_of_globals _ S3.1) S3
  obtain ⟨-, sound5, comp5⟩ := exceptionBranch_spec (-60) _ _ (gen_of_globals _ S4.1) S4
  simp only [Formula.lift_and, Formula.lift_or, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, exists_eq_or_imp, exists_eq_left, lift_member_call]
  have hpar : ∀ y : ℕ → ℚ, (∀ i : Fin 6, y i = Fin.append N ![t] i) ↔
      evCode y (varPoint 0) = N ∧ y 5 = t := by
    intro y
    constructor
    · intro hy
      refine ⟨?_, (hy 5).trans rfl⟩
      rw [evCode_varPoint]; funext i; rw [hy ⟨0 + i, by omega⟩]; fin_cases i <;> rfl
    · rintro ⟨h0, h5⟩ i
      refine Fin.addCases (m := 5) (n := 1) (fun i => ?_) (fun i => ?_) i
      · rw [Fin.append_left, ← h0, evCode_varPoint]; simp
      · rw [Fin.append_right]; fin_cases i; simpa using h5
  simp only [hpar]
  constructor
  · rintro ⟨y, ⟨hN, ht⟩, ⟨g0', g1', g2'⟩, -, hb⟩
    have hg : evCode y (genPoint 6) = iota 1 := evCode_genPoint g0' g1' g2'
    rw [← hN, ← ht]
    rcases hb with h | h | h | h | h | h
    · obtain ⟨e1, e2⟩ := sound0 y hg h; exact ⟨0, by decide, e1, by rw [e2]⟩
    · obtain ⟨e1, e2⟩ := sound1 y hg h; exact ⟨-15, by decide, e1, by rw [e2]⟩
    · obtain ⟨e1, e2⟩ := sound2 y hg h; exact ⟨-20, by decide, e1, by rw [e2]⟩
    · obtain ⟨e1, e2⟩ := sound3 y hg h; exact ⟨-24, by decide, e1, by rw [e2]⟩
    · obtain ⟨e1, e2⟩ := sound4 y hg h; exact ⟨-30, by decide, e1, by rw [e2]⟩
    · obtain ⟨e1, e2⟩ := sound5 y hg h; exact ⟨-60, by decide, e1, by rw [e2]⟩
  · rintro ⟨c, hc, rfl, rfl⟩
    let y0 := writeVals (writePoints (fun _ => 0) [(0, iota c)])
      [(5, (c : ℚ)), (6, 1641 / 8), (7, -15465 / 4), (8, 87483 / 32)]
    have hN0 : evCode y0 (varPoint 0) = iota c :=
      evCode_writeVals_writePoints _ (by simp) (by simp) (by simp)
    have h5 : y0 5 = c := by simp [y0]
    have h6 : y0 6 = 1641 / 8 := by simp [y0]
    have h7 : y0 7 = -15465 / 4 := by simp [y0]
    have h8 : y0 8 = 87483 / 32 := by simp [y0]
    have hg : evCode y0 (genPoint 6) = iota 1 := evCode_genPoint h6 h7 h8
    -- every completed branch keeps the first nine variables
    have key : ∀ y' : ℕ → ℚ, (∀ i < 9, y' i = y0 i) →
        (evCode y' (varPoint 0) = iota c ∧ y' 5 = c) ∧
          (y' 6 = 1641 / 8 ∧ y' 7 = -15465 / 4 ∧ y' 8 = 87483 / 32) ∧
          memberTemplate.Rel (evCode y' (varPoint 0)) := by
      intro y' hy'
      have e0 : evCode y' (varPoint 0) = iota c := by
        rw [← hN0]; exact evCode_congr fun i j hj => hy' j (varsIn_varPoint (by norm_num) i j hj)
      refine ⟨⟨e0, by rw [hy' 5 (by norm_num), h5]⟩,
        ⟨by rw [hy' 6 (by norm_num), h6], by rw [hy' 7 (by norm_num), h7],
          by rw [hy' 8 (by norm_num), h8]⟩, ?_⟩
      rw [e0, rel_member_iff_iota]; exact ⟨c, rfl⟩
    simp only [contacts, Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨y', hy', h⟩ := comp0 y0 hg hN0 h5
      obtain ⟨k1, k2, k3⟩ := key y' fun i hi => hy' i (by simp only; omega)
      exact ⟨y', k1, k2, k3, Or.inl h⟩
    · obtain ⟨y', hy', h⟩ := comp1 y0 hg hN0 h5
      obtain ⟨k1, k2, k3⟩ := key y' fun i hi => hy' i (by have := S0.2; omega)
      exact ⟨y', k1, k2, k3, Or.inr (Or.inl h)⟩
    · obtain ⟨y', hy', h⟩ := comp2 y0 hg hN0 h5
      obtain ⟨k1, k2, k3⟩ := key y' fun i hi => hy' i (by have := S1.2; omega)
      exact ⟨y', k1, k2, k3, Or.inr (Or.inr (Or.inl h))⟩
    · obtain ⟨y', hy', h⟩ := comp3 y0 hg hN0 h5
      obtain ⟨k1, k2, k3⟩ := key y' fun i hi => hy' i (by have := S2.2; omega)
      exact ⟨y', k1, k2, k3, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
    · obtain ⟨y', hy', h⟩ := comp4 y0 hg hN0 h5
      obtain ⟨k1, k2, k3⟩ := key y' fun i hi => hy' i (by have := S3.2; omega)
      exact ⟨y', k1, k2, k3, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
    · obtain ⟨y', hy', h⟩ := comp5 y0 hg hN0 h5
      obtain ⟨k1, k2, k3⟩ := key y' fun i hi => hy' i (by have := S4.2; omega)
      exact ⟨y', k1, k2, k3, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))⟩

end ZInQ.Assembly
