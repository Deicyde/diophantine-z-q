/-
CloudB3 Worker16 H102: the pure finite-abelian-group torsion structure API.
Uses the AxiomMath/Stacks c496df0d9 source proof ported in TorsionByCard.lean;
see that file and the accompanying LICENSE for source attribution.
No geometry, degree formula, or Mumford theorem is asserted here.
-/
import ZInQKernel.Contrib.CloudB3W16FiniteGroup.TorsionByCard

namespace ZInQ.Contrib.CloudB3W16FiniteGroup

/-- Pure group-theoretic classification from the cardinalities of the divisor torsion groups.
`Submodule.torsionBy ℤ M (d : ℤ)` consists of exactly the elements killed by `d • x`.
No finiteness instance on `M` is needed: the nonzero cardinality hypothesis supplies
finiteness of each relevant torsion group. The rank `r` is arbitrary, including zero. -/
theorem nonempty_torsionBy_addEquiv_pi_zmod {M : Type*} [AddCommGroup M] {n r : ℕ}
    (hn : 0 < n)
    (hcard : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ M (d : ℤ)) = d ^ r) :
    Nonempty (Submodule.torsionBy ℤ M (n : ℤ) ≃+ (Fin r → ZMod n)) :=
  AddSubgroup.nonempty_torsionBy_addEquiv_pi_zmod hn hcard

end ZInQ.Contrib.CloudB3W16FiniteGroup
