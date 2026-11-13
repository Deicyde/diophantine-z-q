/-! ## The three glue Props of G15, unconditionally -/

/-- **`SwanIndependent` (every `p`), `SwanIntegral` (L8) and `AdaptedExists` (every `p`) are
theorems**: `Swan.swan_main` with the leaf `HerbrandUpper` discharged by
`SwanBridge.herbrandUpper_of_quotient` from `PkgI6.herbrandQuotient` (t-different's proof of the
kernel leaf I6.8). -/
theorem Swan.swan_proved :
    (∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p)) ∧ LadicCond.SwanIntegral ∧
      (∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p)) :=
  Swan.swan_main (SwanBridge.herbrandUpper_of_quotient PkgI6.herbrandQuotient)

theorem Swan.swanIndependent_proved (p : ℕ) [Fact p.Prime] : LadicCond.SwanIndependent (p := p) :=
  Swan.swan_proved.1 p

theorem Swan.swanIntegral_proved : LadicCond.SwanIntegral := Swan.swan_proved.2.1

theorem Swan.adaptedExists_proved (p : ℕ) [Fact p.Prime] : LadicCond.AdaptedExists (p := p) :=
  Swan.swan_proved.2.2 p

#print axioms PkgI6.herbrandQuotient
#print axioms SwanBridge.herbrandUpper_of_quotient
#print axioms Swan.swan_main
#print axioms Swan.swan_proved
#print axioms Swan.swanIndependent_proved
#print axioms Swan.swanIntegral_proved
#print axioms Swan.adaptedExists_proved
