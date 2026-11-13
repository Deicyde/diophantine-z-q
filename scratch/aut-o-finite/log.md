# aut-o-finite results log

Base 2dd83306 + merge origin/wip/mobius-glue. Target `LeafQM.AV.Pin.AutOInnerFinite`
(scratch/mobius-glue/MobiusGlue.lean lines 419-428).

## AutOFinite.lean (imports ZInQKernel.HDecomp.QM.Structures, ZInQKernel.HDecomp.Textbook.SkolemNoether)
- `lake build` of the two imports: success (1m33s). VERIFIED.
- §A target copied verbatim: `diff` of MobiusGlue.lean 419-428 vs AutOFinite.lean 31-40 empty. VERIFIED.
- §7, §8 copied from MobiusGlue.lean (lines 651-906, 923-1396; `mobiusGlue_of_normalizer` and
  everything depending on curves/T5 omitted).
- run1 (05:24, 11 s): 0 errors, linter warnings only; `#print axioms` of
  autOInnerFinite_of_normalizer, normalizerFinite, autOInnerFinite: [propext, Classical.choice,
  Quot.sound]. VERIFIED (compiled).
- Test9.lean (05:26, deleted after use): nrd (explicit re²−2imI²+3imJ²−6imK²), nrd_mul, nrd_algebraMap,
  nrd_ofInt (= nrdZ formula of mobius-glue), not_sq (via Rat.isSquare_iff), `¬IsSquare (6:ℤ)` by
  `decide +kernel` (plain `decide` gets stuck on Nat.sqrt), comm_scalar. 0 errors. VERIFIED.

## §9 (new, AutOFinite.lean): explicit computation
- `Exact.rep k = conjO (tt k)`, tt = ![1, ui, uj, ui*uj] (conjugation by 1, i, j, ij).
- `Exact.rep_cover`: ∀ α : O ≃+* O, ∃ k v, ∀ a, α a = v * rep k a * v⁻¹ (Skolem–Noether + the
  concrete normalizer statement `normalizer_rep` = body of NormO.normalizerFinite with T named).
- `Exact.rep_distinct`: rep k ~ rep l by a unit of O ⇒ k = l (w = t_l⁻¹ v⁻¹ t_k commutes with i, j
  ⇒ scalar r; nrd t_k = nrd(v)·r²·nrd t_l, nrd v = ±1, nrd(1,i,j,ij) = 1,−2,3,−6; (r·N l)² = ±N k N l
  is not a rational square, 24 cases by `decide +kernel`).
- `Exact.autO_mod_inner_exact` (exactly four classes) and `Exact.autOInnerFinite'` (AutOInnerFinite
  from rep_cover, second derivation).
- run2 (05:29): 0 errors (linter warnings only, inherited from §8 copy); 5 `#print axioms` all
  [propext, Classical.choice, Quot.sound] (run2.txt). VERIFIED (compiled).
