import ZInQKernel.Contrib.TYZGenus.RingClassBridge

/-! rv-fast: checks on ring-class (ZInQKernel/Contrib/TYZGenus/RingClassBridge.lean). -/

open ZInQ.Contrib.TYZGenus ZInQ.Contrib.TYZGenus.RingClass ZInQ.Contrib.TYZGenus.Package
  ZInQ.Contrib.TYZDecomp.CurveA

-- (c) the proved statements are cm-points' Props, unfolded by `rfl`
example : HprimeNormal = ∀ d : ℕ, d % 8 = 5 → Squarefree d → Normal ℚ (Hprimebar d) := rfl
example : IInH4 = ∀ n : ℕ, n % 8 = 5 → Squarefree n → iQ ∈ H4bar n := rfl
example : RingClassBridge.hprimeNormal = (RingClassBridge.hprimeNormal : HprimeNormal) := rfl
example : CMFieldOfDefinitionTYZ =
    ∀ n : ℕ, n % 8 = 5 → Squarefree n → CM.tyzHeegnerPt n ∈ CM.ptsOver (H4bar n) := rfl
example : CM.CMFieldOfDefinition ringClassFieldD =
    ∀ (D : ℤ) (Q : CM.HeegnerForm 32 D), CM.heegnerPt Q ∈ CM.ptsOver (ringClassFieldD D) := rfl

-- (b) non-degeneracy of the fields: H'_d is a proper subfield of index 2 of H_{d,4} (d ≡ 5 mod 8),
-- so `sigmaClass` is not the junk value 1 and `Hprime` is not `H4`.
example : (Hprime 5).relfinrank (H4 5) = 2 := relfinrank_Hprime 5 rfl
example : Hprime 13 ≠ H4 13 := by
  intro h
  have := relfinrank_Hprime 13 rfl
  rw [h, IntermediateField.relfinrank_self] at this
  exact absurd this (by norm_num)
-- H4bar n is not ⊥ (it contains i)
example : H4bar 5 ≠ ⊥ := by
  intro h
  have hi := RingClassBridge.iInH4 5 rfl (by decide)
  rw [h, IntermediateField.mem_bot] at hi
  obtain ⟨q, hq⟩ := hi
  have h2 := iQ_sq
  rw [← hq] at h2
  have : (q : Qbar) ^ 2 = ((q ^ 2 : ℚ) : Qbar) := by push_cast; ring
  have h3 : ((q ^ 2 : ℚ) : Qbar) = ((-1 : ℚ) : Qbar) := by rw [← this, h2]; push_cast; ring
  have h4 : q ^ 2 = -1 := by exact_mod_cast h3
  nlinarith [sq_nonneg q]
-- the TYZ instance of the by-discriminant family
example : ringClassFieldD (-64 * 13) = H4bar 13 := ringClassFieldD_tyz (n := 13) rfl (by decide)

#print axioms RingClassBridge.hprimeNormal
#print axioms RingClassBridge.iInH4
#print axioms RingClassBridge.tyzThm35ReadingA_of_cmLeaves_ringClass
#print axioms RingClassBridge.cmFieldTYZ_of_ringClassD
#print axioms RingClassBridge.tyzThm35ReadingA_of_cmLeaves_ringClassD
#print axioms RingClass.ringClassFieldD_tyz
#print axioms RingClass.condD_spec
#print axioms RingClass.normal_ringClassFieldD
#print axioms RingClass.relfinrank_Hprime
