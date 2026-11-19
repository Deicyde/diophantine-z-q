import ZInQKernel.Contrib.CloudB3RC53.Prints

/-!
# Kolyvagin's Theorem 1 with its own premise: a weak Weil parametrization

`KolyvaginThm1Printed` (`Prints.lean`) takes as premise `IsModular E`: a `Γ₀(N)` cusp form whose
coefficients are those of `L(E, s)`. Kolyvagin's Theorem 1 (MPIM preprint MPI/90-69 (1990),
pp. 4–5) assumes instead a weak Weil parametrization `X₀(N) → E` with `N` the conductor (p. 3).
The manuscript (`lem:forward-rank`, tex L1092–1093) writes "Modularity follows from [BCDT,
Theorem A]. Apply [Kolyvagin, Theorem 1, pp. 4–5]": it passes from modularity directly to
Kolyvagin's hypothesis. This file states the print with its own premise and isolates that passage
as a named gap:

* `HasWeakWeilParametrization E`: the analytic data of a modular parametrization of `E` over `ℚ`
  at the conductor level. `X₀(N)` as a curve over `ℚ` is absent from Mathlib and Tau Ceti, so,
  as for the Cai–Shu–Tian print (`Prints/CST.lean`), the parametrization is stated through its
  complex-analytic model: a cusp form `f` on `Γ₀(N)` with the coefficients of `L(E, s)`, a period
  lattice `Lat` of `E`, and a nonzero RATIONAL `c` with `c · (periods of 2πi f dτ) ⊆ Lat`, so that
  `τ ↦ ℘_Lat-point of c ∫_{i∞}^τ 2πi f` (`CST.phiAn`) is a `Γ₀(N)`-invariant map
  `X₀(N)(ℂ) → E(ℂ)` sending `∞` to `O` with `φ^* ω_E = c ω_f`. `N` is `CST.newformLevel E`,
  which is the conductor by Carayol's theorem. That these analytic data are equivalent to a
  genuine nonconstant `ℚ`-morphism `X₀(N) → E` with the same `E`, differential, lattice and period
  map (uniformization and GAGA with `ℚ`-descent, the Eichler–Shimura construction) is NOT proved
  here. The print below is therefore faithful to the printed statement only modulo the
  translation algebraic `X₀(N) → E` ⇔ analytic data, which is an unproved GLUE (translation)
  step.
* `KolyvaginThm1WeilParam` (PRINT modulo that GLUE translation): Kolyvagin's Theorem 1 with the
  weak Weil parametrization premise.
* `ModularToWeakWeil`: a modular `E` has a weak Weil parametrization by `X₀(N)`. GLUE (textbook:
  BCDT condition (2) with trivial nebentypus, Shimura's construction (Milne, Modular functions and
  modular forms, Theorem 11.19 and Remark 11.18) and Faltings' isogeny theorem, with Carayol for
  the level). The manuscript carries it out for `E_ℓ` at tex 1779–1788 ("The modular realization
  gives a rational weight-two newform f of level N and an elliptic quotient q_f : J₀(N) ↠ A_f in
  the rational isogeny class of E … Choose a ℚ-isogeny α : A_f → E and put φ = α q_f and
  π(x) = φ([x] − [∞])") and leaves it implicit for the curves of `lem:forward-rank`
  (tex 1092–1093).
* `kolyvaginThm1Printed_of_weilParam` (PROVED): the old `IsModular`-premise form follows from the
  gap and the print, so the current consumers of `Prints.kolyvagin` keep working
  (`prints_of_weilParam`).

The old leaf is not relabelled: its premise is not Kolyvagin's.

Classification: `KolyvaginThm1WeilParam` PRINT modulo the GLUE translation above (not plain
PRINT); `ModularToWeakWeil` GLUE (the manuscript carries it out for `E_ℓ` at tex 1779–1788); the
bridges PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Manuscript.PoleS12 CST

/-- **`E` has a weak Weil parametrization `X₀(N) → E` over `ℚ`, `N` the conductor** (analytic
model; see the module docstring): a cusp form `f` of weight `2` on `Γ₀(N)`, `N = newformLevel E`,
with the coefficients of `L(E, s)`, a period lattice `Lat` of `E` (`IsLatticeOf`), and a nonzero
rational `c` scaling the periods of `2πi f dτ` into `Lat` (`IsParamScale`), so that
`φ^* ω_E = c ω_f` for the analytic map `CST.phiAn E f Lat c`. An analytic stand-in: faithful to the
printed statement only modulo the translation algebraic `X₀(N) → E` ⇔ analytic data, which is an
unproved GLUE (translation) step. -/
def HasWeakWeilParametrization (E : WeierstrassCurve ℚ) : Prop :=
  ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (Lat : PeriodPair) (c : ℚ),
    (∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ)) ∧
      IsLatticeOf E Lat ∧ IsParamScale (newformLevel E) f Lat (c : ℂ)

/-- **Kolyvagin, Theorem 1, with its own premise** (printed leaf; V. A. Kolyvagin, "On the
Mordell–Weil group and the Shafarevich–Tate group of modular elliptic curves", MPIM preprint
MPI/90-69 (1990), Theorem 1, pp. 4–5, under the weak Weil parametrization of p. 3; tex L1093
`\cite[Theorem 1, pp. 4–5]{kolyvagin}`): an elliptic curve `E/ℚ` with a weak Weil parametrization
`X₀(N) → E` (`N` the conductor) and `ord_{s=1} L(E, s) = r ≤ 1` has `rank E(ℚ) = r` and finite
`Ш(E/ℚ)`. The parametrization is in its analytic form (`HasWeakWeilParametrization`), so this leaf
is faithful to the printed statement only modulo the translation algebraic `X₀(N) → E` ⇔ analytic
data, which is an unproved GLUE (translation) step. -/
def KolyvaginThm1WeilParam : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → HasWeakWeilParametrization E →
    ∀ r : ℕ, r ≤ 1 → AnalyticRank E r →
      Module.rank ℤ E.toAffine.Point = r ∧ Finite (sha E)

/-- **From modularity to Kolyvagin's hypothesis**: a modular elliptic curve `E/ℚ` has a weak Weil
parametrization by `X₀(N)`, `N` the conductor. GLUE (textbook: BCDT condition (2) with trivial
nebentypus, Shimura's construction (Milne, Modular functions and modular forms, Theorem 11.19 and
Remark 11.18) and Faltings' isogeny theorem, with Carayol for the level). The manuscript carries it
out for `E_ℓ` at tex 1779–1788 ("The modular realization gives a rational weight-two newform f of
level N and an elliptic quotient q_f : J₀(N) ↠ A_f in the rational isogeny class of E … Choose a
ℚ-isogeny α : A_f → E and put φ = α q_f and π(x) = φ([x] − [∞])") and leaves it implicit for the
curves of `lem:forward-rank` (tex 1092–1093). -/
def ModularToWeakWeil : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → IsModular E → HasWeakWeilParametrization E

/-- **The old `IsModular`-premise form of Kolyvagin's Theorem 1** (PROVED) from the GLUE
`ModularToWeakWeil` and Kolyvagin's Theorem 1 with its own premise. -/
theorem kolyvaginThm1Printed_of_weilParam (hG : ModularToWeakWeil)
    (hK : KolyvaginThm1WeilParam) : KolyvaginThm1Printed :=
  fun E hE hM r hr hA => hK E hE (hG E hE hM) r hr hA

/-- **The printed leaves with Kolyvagin's own premise** (PROVED): `Prints` from BCDT Theorem A,
the GLUE `ModularToWeakWeil`, Kolyvagin's Theorem 1 with the weak Weil parametrization premise,
Dokchitser–Dokchitser Theorem 1.8 and Cai–Shu–Tian Theorem 1.1. -/
theorem prints_of_weilParam (hB : BCDTThmA) (hG : ModularToWeakWeil)
    (hK : KolyvaginThm1WeilParam) (hdd : DokchitserThm18) (hcst : CST.CSTThm11Split) : Prints :=
  ⟨hB, kolyvaginThm1Printed_of_weilParam hG hK, hdd, hcst⟩

end ZInQ.Contrib.CloudB3RC53
