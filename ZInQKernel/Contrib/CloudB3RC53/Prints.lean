import ZInQKernel.Contrib.CloudB3RC53.Basic
import ZInQKernel.Contrib.CloudB3RC53.Prints.CST
import ZInQKernel.Contrib.OneProof.PoleS12.Leaves

/-!
# RC53 blueprint: the printed results cited by the proof of Theorem 5.3

`RC53.Prints` bundles one `Prop` per cited published result that this blueprint states over
genuine definitions. Each is stated in the printed form in which the manuscript cites it, with its
locator as the manuscript gives it. No print was read for this file (no network): **every locator
is UNVERIFIED (pending reading)**, so each leaf counts as GLUE until a statement check clears it.

Project rule (issue #74, decision 3): Gross–Zagier enters only through the printed leaves
Cai–Shu–Tian Theorem 1.1 (`CST.CSTThm11Split`) and Kolyvagin Theorem 1
(`KolyvaginThm1Printed`); there is no Gross–Zagier or Tian–Yuan–Zhang argument here.

The remaining cited results (Kato, Nekovář, Waldspurger, Cornut–Jetchev, Hoffstein–Luo,
Bump–Friedberg–Hoffstein, Desjardins, Serre, Cai–Chen–Liu, Elkik, Milne ADT, Edixhoven, Lang,
Silverman, Voight, Jetchev–Kane, Weil, Carayol, Casselman, Ramsey, Stacks) are listed in
`DAG.md` with the definitions each one needs; they are added as fields here as soon as they are
stated over genuine definitions.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Manuscript.PoleS12

/-- **Kolyvagin, Theorem 1, as the manuscript cites it** (printed leaf; tex L1093
`\cite[Theorem 1, pp. 4–5]{kolyvagin}`, "whose statement includes both `r = 0` and `r = 1`";
bibitem: V. A. Kolyvagin, "On the Mordell–Weil group and the Shafarevich–Tate group of modular
elliptic curves", MPIM preprint MPI/90-69 (1990)). A modular elliptic curve `E/ℚ` with
`ord_{s=1} L(E, s) = r ≤ 1` has `rank E(ℚ) = r` and finite `Ш(E/ℚ)` (`SelmerTwoPower.sha`).
Same statement as the fleet's `KolyvCST.KolyvaginThm1Printed` (branch `wip/kolyv-cst-printed`).
UNVERIFIED (pending reading). Used in the proof of Theorem 5.3 through `lem:forward-rank`
(tex L2376, L2617, L4020, L5250, L7626, L7780, L8272, L10111, L10279). -/
def KolyvaginThm1Printed : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → IsModular E → ∀ r : ℕ, r ≤ 1 → AnalyticRank E r →
    Module.rank ℤ E.toAffine.Point = r ∧ Finite (sha E)

/-- **Dokchitser–Dokchitser, Theorem 1.8 (`2^∞`-Selmer parity), as the manuscript uses it**
(printed leaf; tex L1795–1797 `\cite[Theorem 1.8]{dd}`, J. reine angew. Math. 658 (2011); also
tex L8249). For an elliptic curve `E/ℚ` with a rational point of order two (hence a rational
two-isogeny, tex L1794–1795), `corank_{ℤ₂} Sel_{2^∞}(E/ℚ) = r` gives root number `(-1)^r`.

Form: `RootNumber E w` is the sign of the functional equation of `L(E, s)` (see `Basic.lean`).
The print's `w(E)` is the global root number; that it is the sign of the functional equation is
modularity (BCDT Theorem A) with Hecke's theory, so this leaf is the print composed with that
standard identification: consequence form, GLUE pending reading. UNVERIFIED. -/
def DokchitserThm18 : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic →
    1 < Nat.card (nsmulAddMonoidHom 2 : E.toAffine.Point →+ E.toAffine.Point).ker →
    ∀ r : ℕ, Z2Corank (selmerTwoPower E) r → RootNumber E ((-1) ^ r)

/-- **The printed results cited by the proof of Theorem 5.3**, stated over genuine definitions.
Fields are added as further prints are stated (see `DAG.md`). -/
structure Prints : Prop where
  /-- Breuil–Conrad–Diamond–Taylor, Theorem A (tex L1779 `\cite[Theorem A and Introduction,
  conditions (1)–(6)]{bcdt}`): every elliptic curve over `ℚ` is modular. The fleet's
  `PoleS12.BCDTThmA`. UNVERIFIED. -/
  bcdt : BCDTThmA
  /-- Kolyvagin, Theorem 1 (`r ≤ 1`). UNVERIFIED. -/
  kolyvagin : KolyvaginThm1Printed
  /-- Dokchitser–Dokchitser, Theorem 1.8. UNVERIFIED. -/
  dd : DokchitserThm18
  /-- Cai–Shu–Tian, Theorem 1.1, split case (the fleet's `CSTThm11Split`). UNVERIFIED. -/
  cst : CST.CSTThm11Split

end ZInQ.Contrib.CloudB3RC53
