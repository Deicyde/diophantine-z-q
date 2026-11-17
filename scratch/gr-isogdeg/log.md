# gr-isogdeg log

Base: wip/gr-isogdeg at 73ac1620 (= wip/r3-residual), merged origin/main (ff558bedd).

## Plan
- New leaf `GaudronRemondThm14AnDeg`: GaudronRemondThm14An with `isogDeg φ` (#ker(K̄)) replaced by
  `finDeg φ := φ.left.finrank (genericPoint B.X.left)` (Mathlib's `Scheme.Hom.finrank`, the rank of
  φ_*O at the generic point = [K(A):K(B)], meaningful without flatness since the stalk is a field).
- Glue: `isogDeg φ ≤ finDeg φ` for every isogeny, any characteristic (#ker(K̄) = separable degree ≤ degree):
  translates ξ·P of a geometric generic point ξ : Spec Ω → A by kernel points P are distinct Ω-points over
  φ∘ξ; those inject into ring maps Γ(φ⁻¹U) → Ω over Γ(U) → Ω, counted by `card_algHom_le_finrank`.

## Results
- Ring.lean: `card_ringHom_le_rankAtStalk` (R domain, S finite, ψ₀ injective, p = ⊥): compiles (VERIFIED).
- T0.lean: `Scheme.Hom.finrank` unfolds by `rfl` from a non-module file (body visible) (VERIFIED, after fixing
  the test statement).
- Sch.lean: `card_points_le_finrank` (f finite, Y integral, y₀ : Spec Ω → Y onto the generic point: Ω-points of X over y₀ are finite, at most `f.finrank (genericPoint Y)`; ring lemma as hypothesis): compiles (VERIFIED).
- IsogDeg.lean (imports ZInQKernel.HDecomp.Faltings.Leaves + Mathlib): `finDeg φ := φ.left.finrank (genericPoint B.X.left)`
  and `isogDeg_le_finDeg : IsIsogeny φ → isogDeg φ ≤ finDeg φ` (any field K, any characteristic): compiles,
  axioms [propext, Classical.choice, Quot.sound] (VERIFIED).
  Pitfalls: `ι` is a reserved token under `open MonObj` (renamed `emb`); `mul_left_cancel` on Over-homs needs the
  type given explicitly (`@mul_left_cancel (ptObj K Ω ⟶ A.X) ...`); the local `Epi` instance was not found by
  `cancel_epi`, use `hepi.left_cancellation`.
- ZInQKernel/Contrib/OneProof/GaudronRemondIsogDeg.lean: lake build of Main+Discharges+module OK (16049 jobs; build1.txt);
  rebuilt with `gaudronRemondThm14Printed_of_anDeg_final` (MumfordTorsionAlgClosed filled by its proof; build2.txt).
- #discharges: `gaudronRemondThm14Printed_of_anDeg_final` discharges OpenResearchLeaves40.gaudronRemondThm14Printed,
  still assumes [ZInQ.GRIsogDeg.GaudronRemondThm14AnDeg], standard axioms (VERIFIED, discharges.txt).
- autofold.json dry run: 16/15 -> 16/15 (kinds.tsv already rated the replaced row LEAF); the generated module compiles,
  sixContactMin_of_open59 standard axioms (VERIFIED). First spec draft used {t}.mumfordTorsionAlgClosed, which is no
  longer a field of OpenTextbookLeaves17 on main (it is proved, TailZ64): fixed by the _final theorem.
- finDeg_eq_finrank_of_flat (flat + loc. fin. pres. ⇒ rank constant): compiles (remark, unused).
- Not proved: equality finDeg = isogDeg in char 0 (needs flatness of isogenies / étale kernel).
- EqRing.lean: finite_ringHom, card_ringHom_eq_rankAtStalk (char 0 equality), card_ringHom_le_of_isAlgClosed (descent to alg. closed subfield): compile (VERIFIED).
- EqSch.lean: points_equiv_ringHom (bijection points over Spec L→Spec R→Y with ring maps Γ(f⁻¹U)→L): compiles.
- EqAll.lean: finrank_le_card_points (generic fibre, char 0), card_points_le_of_isAlgClosed (descent Ω→K̄), finDeg_le_isogDeg [CharZero K], isogDeg_eq_finDeg [CharZero K]: compile, axioms standard (VERIFIED).
