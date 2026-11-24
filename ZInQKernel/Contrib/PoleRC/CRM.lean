import ZInQKernel.Contrib.PoleRC.Defs

/-!
# `CR_M` from Theorem 5.3, Lemma 5.4 and Lemma 5.5 (`diophantine_zq.tex` lines 1076–1110)

`crm_of_restrictedConverse`: `CRM` from

* `Manuscript.RestrictedConverse P` (Theorem 5.3, `hyp:RC`), with `P` the abstract Selmer
  predicate `corank_{ℤ₂} Sel_{2^∞}(E/ℚ) = 1`;
* `Lemma54At P` (Lemma 5.4, `lem:corank`, at the curves `E_ℓ`): what Theorem 5.3 needs of `P`;
* `KolyvaginRankOne` (Lemma 5.5, `lem:forward-rank`, its rank assertion at `r = 1`): BCDT
  Theorem A and Kolyvagin Theorem 1, printed leaves;
* `MordellWeil` (textbook);
* `DescentGlueM` (GLUE: the complete 2-descent of `E_ℓ`, Silverman X.1.4, with the count
  `#E(ℚ)/2E(ℚ) ≥ 8`; the analogue of Route K's proved `loc_of_mem_sel2_of_infinite_order`).

`P` stays an abstract parameter (fork issue #83): everything the argument needs of it is the
hypothesis `Lemma54At P`.
-/

namespace ZInQ.Manuscript.PoleRC

open WeierstrassCurve

/-- `E_ℓ` is an elliptic curve for `ℓ ≠ 0` (`Δ = 2304 ℓ⁶`). -/
theorem curve_isElliptic {ℓ : ℚ} (hℓ : ℓ ≠ 0) : (curve ℓ).IsElliptic :=
  ⟨by rw [curve_Δ]; exact isUnit_iff_ne_zero.mpr (mul_ne_zero (by norm_num) (pow_ne_zero 6 hℓ))⟩

/-- **Lemma 5.4 (`lem:corank`) at the curves `E_ℓ`, against the abstract predicate `P`.** For
positive squarefree `ℓ ≡ 11 (mod 12)`, dimension three of the 2-Selmer group of `E_ℓ`
(`#SelM ℓ = 8`) gives `P (E_ℓ)`, where `P` stands for `corank_{ℤ₂} Sel_{2^∞}(E/ℚ) = 1`.

The manuscript proves Lemma 5.4 for every elliptic curve with full rational two-torsion from the
Kummer sequence and the Cassels–Tate pairing (Poonen–Stoll, Ann. of Math. 150 (1999)); `E_ℓ` has
full rational two-torsion (roots `0, ℓ, −3ℓ`), and `SelM ℓ` is the explicit form of
`Sel₂(E_ℓ/ℚ)` (Silverman X.1.4). Since `P` is abstract, this is an interface hypothesis: it is
Lemma 5.4 only once `P` is the genuine corank predicate and `SelM` is identified with `Sel₂`. -/
def Lemma54At (SelmerCorankOne : WeierstrassCurve ℚ → Prop) : Prop :=
  ∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ → ℓ % 12 = 11 → (SelM ℓ).ncard = 8 → SelmerCorankOne (curve ℓ)

/-- **Lemma 5.5 (`lem:forward-rank`), rank assertion for `r = 1` (printed leaves).** For an
elliptic curve `E/ℚ`, `ord_{s=1} L(E, s) = 1` (`AnalyticRankOne E`, over Mathlib's `L`-series)
implies `rank E(ℚ) = 1`.

Literature, as the manuscript cites it (line 1094): modularity by Breuil–Conrad–Diamond–Taylor,
Theorem A (J. Amer. Math. Soc. 14 (2001) 843–939; the manuscript cites the author manuscript),
and Kolyvagin, Theorem 1, pp. 4–5 of "On the Mordell–Weil group and the Shafarevich–Tate group
of modular elliptic curves", MPIM preprint MPI/90-69 (1990) (UNVERIFIED: not read here; the
manuscript says its Theorems 3–5 supply the auxiliary imaginary quadratic field and the nonzero
Heegner height). Kolyvagin's theorem also gives `Ш(E/ℚ)` finite; `Ш` has a Lean definition
(`SelmerTwoPower.sha`) and the finiteness is stated in `PoleS12.KolyvaginThm1`; the statement here is the
rank half, a consequence. The `rank` of the print is
the rank of the finitely generated group `E(ℚ)`, here `Module.rank ℤ E(ℚ)`. -/
def KolyvaginRankOne : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → AnalyticRankOne E →
    Module.rank ℤ E.toAffine.Point = 1

/-- **Mordell's theorem** (Mordell 1922; Silverman, *The Arithmetic of Elliptic Curves*,
Theorem VIII.6.7, UNVERIFIED numbering): `E(ℚ)` is finitely generated. Textbook leaf, implicit in
the manuscript's use of "rank" in Lemma 5.5. Route K proves it in Lean for the congruent number
curves (`ZInQ.RouteK.Rank.fg_points`). -/
def MordellWeil : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → AddGroup.FG E.toAffine.Point

/-- **The complete 2-descent of `E_ℓ` with the count (GLUE; proved in `DescentM.lean`).** For positive
squarefree `ℓ ≡ 11 (mod 12)`, if
`E_ℓ(ℚ)` is finitely generated and has a point of infinite order, and `#SelM ℓ = 8`, then every
class of `SelM ℓ` is the Kummer class of a rational point.

Proof (textbook): the Kummer map `P ↦ (x + 3ℓ, x − ℓ)` is a homomorphism
`E_ℓ(ℚ) → (ℚ*/ℚ*²)²` with kernel `2E_ℓ(ℚ)` (Silverman X.1.4), landing in `SelM ℓ`; since
`E_ℓ(ℚ)[2]` has order 4, a point of infinite order gives `#E_ℓ(ℚ)/2E_ℓ(ℚ) ≥ 8 = #SelM ℓ`, so the
Kummer map is onto. Route K proves the same statement in Lean for the congruent number curves
(`ZInQ.RouteK.Rank.loc_of_mem_sel2_of_infinite_order`); for `E_ℓ` it is proved in
`ZInQKernel/Contrib/PoleRC/DescentM.lean` (`descentGlueM`). -/
def DescentGlueM : Prop :=
  ∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ → ℓ % 12 = 11 → AddGroup.FG (curve (ℓ : ℚ)).toAffine.Point →
    (∃ P : (curve (ℓ : ℚ)).toAffine.Point, ¬ IsOfFinAddOrder P) → (SelM ℓ).ncard = 8 →
    ∀ ab ∈ SelM ℓ, LocM ℚ ℓ ab.1 ab.2

/-- Rank one gives a point of infinite order. -/
theorem exists_not_isOfFinAddOrder_of_rank {M : Type*} [AddCommGroup M]
    (h : Module.rank ℤ M = 1) : ∃ P : M, ¬ IsOfFinAddOrder P := by
  by_contra hcon
  have hcon' : ∀ P : M, IsOfFinAddOrder P := fun P => by_contra fun h => hcon ⟨P, h⟩
  have : Module.rank ℤ M = 0 := by
    rw [rank_eq_zero_iff]
    intro x
    obtain ⟨n, hn, hx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp (hcon' x)
    exact ⟨n, by exact_mod_cast hn.ne', by rw [natCast_zsmul]; exact hx⟩
  rw [this] at h
  exact zero_ne_one h

/-- **`CR_M` from Theorem 5.3, Lemma 5.4 and Lemma 5.5** (lines 1076–1110). -/
theorem crm_of_restrictedConverse (SelmerCorankOne : WeierstrassCurve ℚ → Prop)
    (hRC : RestrictedConverse SelmerCorankOne) (h54 : Lemma54At SelmerCorankOne)
    (hK : KolyvaginRankOne) (hMW : MordellWeil) (hD : DescentGlueM) : CRM := by
  intro ℓ hℓ hsf h12 h8 β hβ
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne'
  have hE := curve_isElliptic hℓ0
  have hP := h54 ℓ hℓ hsf h12 h8
  have hA := hRC ℓ hℓ hsf h12 hP
  have hr := hK _ hE hA
  exact hD ℓ hℓ hsf h12 (hMW _ hE) (exists_not_isOfFinAddOrder_of_rank hr) h8 (β, 1) hβ

end ZInQ.Manuscript.PoleRC
