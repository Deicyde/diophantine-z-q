
/-! ### leaf-adopt3 (2026-11-13): former bundle fields, now theorems or consequences of narrower fields

Wave 25 proved T13, T19, T22 (both parts) and T30 (from T16(a)), narrowed T17 and T18, made T10
concrete and added the leaves T36-T41. The former fields remain available as theorems. -/

/-- T13, Skolem–Noether (t-skolem-kw; proved, no leaf). -/
theorem t13_proved : SkolemNoether := TSkolemKW.hsyn_t13

/-- T19, Brauer–Nesbitt in characteristic 0, matrix form (t-skolem-kw; proved, no leaf). -/
theorem t19_proved : BrauerNesbitt := TSkolemKW.hsyn_t19

/-- T22(a), Herbrand's quotient formula (t-different; proved, no leaf). -/
theorem t22a_proved : PkgI6.HerbrandQuotient := PkgI6.herbrandQuotient

/-- T22(b), transitivity of Herbrand's function (t-different; proved, no leaf). -/
theorem t22b_proved : PkgI6.HerbrandTransitivity := PkgI6.herbrandTransitivity

/-- T20 in local form (I6.7, t-different; proved). The global form `t20` remains a leaf. -/
theorem t20_local_proved : PkgI6.HilbertDifferentFormula := PkgI6.hilbertDifferentFormula

/-- T21 in local form (I6.6, t-different; proved). The global form `t21` remains a leaf. -/
theorem t21_local_proved : PkgI6.DifferentBound := PkgI6.differentBound

/-- T18's density form from the narrowed field `t18 : ChebotarevExists` (t-skolem-kw). -/
theorem TextbookLeaves.frobeniusDense (t : TextbookLeaves) : FrobeniusDense :=
  TSkolemKW.hsyn_t18_of_chebotarev t.t18

/-- T30 from T16(a) (t30-adelic). -/
theorem TextbookLeaves.leafSqrtCrit (t : TextbookLeaves) : GlueDescent.B2Q.LeafSqrtCrit :=
  T30.leafSqrtCrit_of_t16a t.t16a

/-- leaf-push2's group-isomorphism form of T10 from the Galois-equivariant field (t10-etale). -/
theorem TextbookLeaves.t10_groupIso (t : TextbookLeaves) : ZInQ.LeafPush2.T10_groupIso :=
  T10Etale.T10_groupIso_of_tateDuality t.t10

/-- `X₁(N)` has a model over `ℚ` (leaf-modcurves' glue target, x1-belyi; from T36, T38-T40). -/
theorem TextbookLeaves.x1ModelExists (t : TextbookLeaves) : LeafModCurves.X1ModelExists :=
  (X1Belyi.x1ModelExists_and_belyiX1 t.x1).1

/-- `j/1728` is a Belyi function of degree `≤ N²` on `K_N` (E2's Belyi half, x1-belyi; from T36,
T37). -/
theorem TextbookLeaves.belyiX1 (t : TextbookLeaves) : LeafModCurves.BelyiX1 :=
  (X1Belyi.x1ModelExists_and_belyiX1 t.x1).2

/-- Non-vacuity of `IsJ1` (so of `r16`, `t34`; rv-leaves48 P2): a `J₁(N)` exists, from T33 and
T36, T38-T40 (x1-belyi). -/
theorem TextbookLeaves.exists_J1 (t : TextbookLeaves) (N : ℕ) (hN : 0 < N) :
    ∃ J : PkgI3.AbVar ℚ, LeafModCurves.IsJ1 N J :=
  X1Belyi.exists_J1_of_leaves t.x1 t.t33 N hN

/-- leaf-modcurves' bundle `ModCurveLeaves` from the two bundles (x1-belyi). -/
theorem modCurveLeaves_of_bundles (r : ResearchLeaves) (t : TextbookLeaves) :
    LeafModCurves.ModCurveLeaves :=
  X1Belyi.modCurveLeaves_of t.x1 t.t33 r.r16 t.t34
