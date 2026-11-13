import ZInQKernel.Contrib.TYZGenus.X0
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.Newform

/-!
# x0-32: the weight-2 newform of level 32 in Tau Ceti's newform API

Report: `docs/research/x0-32.md`. Owner: task x0-32. Kept apart from `TYZGenus/X0.lean` so that
importing the modular curve does not pull in the vendored Tau Ceti newform theory.

Tau Ceti's `HeckeRing.GL2.Newform N k` (vendored, `Newforms/Newform.lean`) is a cusp form on
`Γ₁(N)` with a nebentypus `χ`, Hecke eigenvalues at indices prime to `N`, in the new subspace
(Petersson complement of the old space) and normalized (`a₁ = 1`). The leaf below says that
`f = η(4τ)²η(8τ)²` (`X0.fC`) is such a newform of level 32 and weight 2, with trivial nebentypus and
`T_p`-eigenvalue `a_p(A)` (Mathlib's `L(A, s)` coefficients) for every odd prime `p`.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.X0

open ZInQ.Contrib.TYZDecomp.CurveA HeckeRing.GL2

/-- **Leaf X0-NEWFORM-TC** (`f = η(4τ)²η(8τ)²` is the newform of level 32, in Tau Ceti's API):
there is a `Newform 32 2` whose underlying function is `fC`, with trivial nebentypus and with
eigenvalue `a_p(A)` at every odd prime `p`.

Sources (refereed; locators UNVERIFIED): `dim S₂(Γ₀(32)) = 1` (genus of `X₀(32)` is one; e.g.
Diamond–Shurman, *A first course in modular forms*, GTM 228, Fig. 3.4 / §3.9), so the normalized
cusp form `η(4τ)²η(8τ)²` of `S₂(Γ₀(32))` (Martin–Ono 1997) is a newform (there are no oldforms:
`S₂(Γ₀(N)) = 0` for `N ∣ 16`) and a Hecke eigenform with the eigenvalues of `32a`
(Koblitz GTM 97, Ch. IV). Implies-by-hand (not proved here): `CuspFormEta32` (modulo the
`Γ₁ ↔ Γ₀` bridge for trivial `χ`) and, with `NewformEta32`, the identification of the
eigenvalues. -/
def NewformTC32 : Prop :=
  ∃ g : Newform 32 2, (∀ τ : UpperHalfPlane, g.toCuspForm τ = fC τ) ∧ g.χ = 1 ∧
    ∀ (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2),
      g.eigenvalue ⟨p, hp.pos⟩
        ((Nat.coprime_primes hp Nat.prime_two).mpr hp2 |>.pow_right 5) =
        (curveA.LFunction p : ℂ)

end ZInQ.Contrib.TYZGenus.X0
