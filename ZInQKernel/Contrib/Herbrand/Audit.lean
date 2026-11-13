import ZInQKernel.Contrib.Herbrand.Tower

/-!
# Exact closed-statement audit for T22

This module deliberately names the two actual main propositions, not the draft
PR41 extraction, a weakened real-index range, or a conditional filtration law.
It changes no statement or provider registry. Its compilation and dependency
reports are formal verification evidence, not independent acceptance.
-/

namespace ZInQ.Contrib.Herbrand.Audit

/-- A closed theorem of precisely the requested conjunction. -/
theorem actualClosedConjunction :
    PkgI6.HerbrandQuotient ∧ PkgI6.HerbrandTransitivity :=
  ZInQ.Contrib.Herbrand.t22_holds

/-- The full quotient proposition is obtained without new explicit or instance hypotheses. -/
theorem actualHerbrandQuotient : PkgI6.HerbrandQuotient := actualClosedConjunction.1

/-- The full transitivity proposition is obtained without new explicit or instance hypotheses. -/
theorem actualHerbrandTransitivity : PkgI6.HerbrandTransitivity := actualClosedConjunction.2

end ZInQ.Contrib.Herbrand.Audit

#print ZInQ.Contrib.Herbrand.t22_holds
#print axioms ZInQ.Contrib.Herbrand.t22_holds
#print axioms ZInQ.Contrib.Herbrand.Audit.actualClosedConjunction
#print axioms ZInQ.Contrib.Herbrand.Audit.actualHerbrandQuotient
#print axioms ZInQ.Contrib.Herbrand.Audit.actualHerbrandTransitivity
