# lt-local results log

## Step 0 (2026-11-13 09:35-09:50 PST): environment
- Merged origin/wip/lg-kerwild (745af133). origin/wip/g8-tate read, not merged (its `part_tools.lean`
  lemmas `padic_card_le`, `padicAlgCl_card` copied verbatim into part 1, renamed namespace).
- `lake build` of the 25 `ZInQKernel` modules imported by `scratch/lg-kerwild/KerWild.lean`: success (2m25s).
- `Base.lean` = `scratch/lg-kerwild/KerWild.lean` minus `#print axioms` lines (generated, not committed).
  `ctail.sh Base.lean Base`: exit 0, 69 s, olean in `olean/` (dev only).

## Step 1 (09:50-10:00): part_tools.lean (namespace `LTLocal`)
- New: `qbar_card_le` (`#ℚ̄ ≤ ℵ₀`), `exists_equiv_extending_aux` (two alg. closed fields of card `𝔠`
  with embeddings of `ℚ̄` are isomorphic compatibly: transcendence bases over `ℚ̄`,
  `MvPolynomial.renameEquiv`, `IsAlgClosure.equivOfEquiv_algebraMap`), **`exists_equiv_extending`**:
  `ιC : ℚ̄ →ₐ[ℚ] ℂ`, `j : ℚ̄ →ₐ[ℚ] ℚ̄_ℓ` ⟹ `∃ Φ : ℂ ≃+* ℚ̄_ℓ, ∀ x, Φ (ιC x) = j x`.
- Compile (VERIFIED): `ctail.sh T1.lean` (import Base + part_tools): exit 0, 6 s;
  `#print axioms LTLocal.exists_equiv_extending`: `[propext, Classical.choice, Quot.sound]`.
