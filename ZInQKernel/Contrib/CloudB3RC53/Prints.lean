import ZInQKernel.Contrib.CloudB3RC53.Basic
import ZInQKernel.Contrib.CloudB3RC53.Prints.CST
import ZInQKernel.Contrib.OneProof.PoleS12.Leaves

/-!
# RC53 blueprint: the printed results cited by the proof of Theorem 5.3

`RC53.Prints` bundles one `Prop` per cited result that this blueprint states over
genuine definitions. Each is stated in the printed form in which the manuscript cites it, with its
locator as the manuscript gives it. The statements of Kolyvagin Theorem 1 (MPI/90-69 p. 4; Proc.
ICM 1990 p. 430), Dokchitser–Dokchitser Theorem 1.8 (arXiv:0906.1815v1 p. 4) and BCDT Theorem A
with Introduction (1)–(6) (author manuscript pp. 1–3) were read; each one's docstring records the
standard identifications its Lean form adds (consequence form).

Project rule (issue #74, decision 3): Gross–Zagier enters only through the cited statements
Cai–Shu–Tian Theorem 1.1 (`CST.CSTThm11Split`) and Kolyvagin Theorem 1
(`KolyvaginThm1Printed`, GLUE: its source is an unrefereed preprint); there is no Gross–Zagier
or Tian–Yuan–Zhang argument here.

The remaining cited results (Kato, Nekovář, Waldspurger, Cornut–Jetchev, Hoffstein–Luo,
Bump–Friedberg–Hoffstein, Desjardins, Serre, Cai–Chen–Liu, Elkik, Milne ADT, Edixhoven, Lang,
Silverman, Voight, Jetchev–Kane, Weil, Carayol, Casselman, Ramsey, Stacks) are listed in
`DAG.md` with the definitions each one needs; they are added as fields here as soon as they are
stated over genuine definitions.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Manuscript.PoleS12

/-- **Kolyvagin, Theorem 1, as the manuscript cites it** (GLUE, not a leaf; tex L1093
`\cite[Theorem 1, pp. 4–5]{kolyvagin}`, "whose statement includes both `r = 0` and `r = 1`";
bibitem: V. A. Kolyvagin, "On the Mordell–Weil group and the Shafarevich–Tate group of modular
elliptic curves", MPIM preprint MPI/90-69 (1990)). A modular elliptic curve `E/ℚ` with
`ord_{s=1} L(E, s) = r ≤ 1` has `rank E(ℚ) = r` and finite `Ш(E/ℚ)` (`SelmerTwoPower.sha`).
Used in the proof of Theorem 5.3 through `lem:forward-rank` (tex L2386–2387, L2616–2617, L4020,
L4052, L5264–5266, L7625–7627, L7780–7781, L8267, L10140, L10279).

Form: consequence form. Theorem 1 of the print (p. 4) assumes a weak Weil parametrization
X₀(N) → E with N the conductor (p. 3); `IsModular` is weaker. This GLUE form follows from
`KolyvaginThm1WeilParam` and the GLUE `ModularToWeakWeil` (`kolyvaginThm1Printed_of_weilParam`,
`Prints/Kolyvagin.lean`); those files are not on the Theorem 5.3 headline's route.

Rating: GLUE. The cited source is an unrefereed preprint, which never counts as a leaf, and the
weaker `IsModular` premise makes this form stronger than the print. -/
def KolyvaginThm1Printed : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → IsModular E → ∀ r : ℕ, r ≤ 1 → AnalyticRank E r →
    Module.rank ℤ E.toAffine.Point = r ∧ Finite (sha E)

/-- **Dokchitser–Dokchitser, Theorem 1.8 (`2^∞`-Selmer parity), as the manuscript uses it**
(printed leaf; tex L1792–1796 `\cite[Theorem 1.8]{dd}`, J. reine angew. Math. 658 (2011); also
tex L8248–8250). For an elliptic curve `E/ℚ` with a rational point of order two (hence a rational
two-isogeny, tex L1792–1793), `corank_{ℤ₂} Sel_{2^∞}(E/ℚ) = r` gives root number `(-1)^r`.

Form: `RootNumber E w` is the sign of the functional equation of `L(E, s)` (see `Basic.lean`).
The print's `w(E)` is the global root number; that it is the sign of the functional equation is
modularity (BCDT Theorem A) with Hecke's theory (bridge (ii): the identification of the product
`∏_v w_v` of local root numbers with the sign of the functional equation), so this leaf is the
print composed with that standard identification: consequence form. That bridge (BCDT, Hecke and
the local–global factorization of `ε`) is GLUE, not part of the print. The print's own hypotheses
are matched: a `2^∞`-Selmer corank, and a rational point of order two, which gives the rational
two-isogeny the print assumes; no finiteness of `Ш` is assumed, and the root number keeps its real
place. Read: arXiv:0906.1815v1, p. 4 (J. reine angew. Math. 658 (2011)). Classification: PRINT
modulo the GLUE root-number bridge. -/
def DokchitserThm18 : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic →
    1 < Nat.card (nsmulAddMonoidHom 2 : E.toAffine.Point →+ E.toAffine.Point).ker →
    ∀ r : ℕ, Z2Corank (selmerTwoPower E) r → RootNumber E ((-1) ^ r)

/-- **The printed results cited by the proof of Theorem 5.3**, stated over genuine definitions.
Fields are added as further prints are stated (see `DAG.md`). -/
structure Prints : Prop where
  /-- Breuil–Conrad–Diamond–Taylor, Theorem A (tex L1779 `\cite[Theorem A and Introduction,
  conditions (1)–(6)]{bcdt}`): every elliptic curve over `ℚ` is modular. This is
  `PoleS12.BCDTThmA`. Its condition (6) is a parametrization by `X₁(N)`; the passage to
  Kolyvagin's `X₀(N)` premise is the GLUE `ModularToWeakWeil` (tex L1092–1093;
  `Prints/Kolyvagin.lean`), which the manuscript carries out for `E_ℓ` at tex 1779–1788. -/
  bcdt : BCDTThmA
  /-- Kolyvagin, Theorem 1 (`r ≤ 1`). -/
  kolyvagin : KolyvaginThm1Printed
  /-- Dokchitser–Dokchitser, Theorem 1.8. -/
  dd : DokchitserThm18
  /-- Cai–Shu–Tian, Theorem 1.1, split case (`CSTThm11Split`; arXiv:1408.1733v2, p. 2). -/
  cst : CST.CSTThm11Split

end ZInQ.Contrib.CloudB3RC53
