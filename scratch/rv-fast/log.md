# rv-fast results log

Base: wip/rv-fast b7cdba8e + merges of origin/wip/{curve-infra 0eb4618a (already in base), lg-kerwild 745af133 (already in base), unram-roots b066d686, afr-absfrob 2ffcf322}.

## Reproducibility of assembled files (VERIFIED, 10:25)
Re-ran each task's assembly script with output to /tmp/rvf and `cmp` against the committed file:
- curve-infra/CurveInfraAll.lean (mk_all.sh): identical.
- unram-roots/UnramRoots.lean (build.sh): identical.
- afr-absfrob/AfrAbsFrob.lean (build.sh): identical.
- lg-kerwild/KerWild.lean (build.sh): DIFFERS. scratch/local-glue/LocalGlue.lean changed after lg-kerwild built
  (local-glue commits b582bf03, d2f6d6d1: added a verbatim g0-dim DimBlock, `localGlue_of_baseChange'`, and dropped
  `A₀.dim = 2` from `G7LocalPackBC`). The defs KerWild, DescentPts, LocalGlue, G7Clauses, UnramRoots are not in the
  diff (unchanged). The committed KerWild.lean is the file that was compiled; rebuilding it today would duplicate
  the G0Dim block (lg-kerwild also splices g0-dim's Dim.lean) -> integration conflict, not a soundness issue.

## ring-class: condD differential check (VERIFIED, computed, condD_check.py)
30 negative discriminants D ≡ 0,1 mod 4 (incl. conductors 2..8, d_K ∈ {-3,-4,-7,-8,-11,-15,-20,-24,-52,-84}, D=-64·13):
the Lean formula (m = sqfPart|D|, d_K = -m if m≡3 (4) else -4m, f = condD D) agrees with PARI quaddisc/sqrtint
in 30/30 cases. condD_spec (Lean) proves |D| = f²|d_K| in general; this checks it is the conductor, not just a factorization.
Every `HeegnerForm 32 D` has D = B²-4AC < 0, D ≡ 0,1 mod 4, so `CM.CMFieldOfDefinition ringClassFieldD` never evaluates
ringClassFieldD at a junk argument.

## lg-kerwild: G7Clauses vs TateBridgeK's witness (VERIFIED by reading; formal lemmas in KerWildCheck.lean)
- `exists_localGlue_of_tateModuleFree` concludes `∃ Tm c ε' a β' uu, G7Out … ∧ ∀ p ≠ ℓ, G7Clauses β' ε' L → LocalGlue …`.
  `G7Clauses` is about the existentially hidden `β', ε'`; `TateBridgeK`'s output says nothing about local constancy,
  `β'² = ι∘χ`, `ε' = 1` on `G_L×G_L` or `[L:ℚ] ≤ D`, so no consumer can discharge it.
- Read (KerWild.lean l.6669-6672, 6705, 8729, and `refine ⟨Tm, c', c', a', β', uu, …⟩` l.8800): the witness built by
  `tateBridgeK_of_piecesK` has `a' = fun _ => 1` and `ε' = c' = n/d` (the rational cocycle of the descent datum,
  conjugated by h).
- New lemma `rvf_g7Clauses_eps_sq`: `G7Clauses β ε L → ∀ g k, ε g k ^ 2 = 1` (β² = ι ∘ galChar χ is a homomorphism).
  `rvf_c_sq_of_a_one`: `G7Out … c ε a β u`, `a ≡ 1`, `G7Clauses β ε L` ⟹ `c² = 1`.
- DescentDatum (KerWild.lean l.5486-5526): `a_σ σ a_τ c(σ,τ) = ε(σ,τ) a_{στ}` with ε a sign cocycle and `a > 0`
  inflated from Gal(L/ℚ) (docstring: `a_σ = (deg μ_σ)^{-1/4}`). So `c = ±1` everywhere iff `a` is a homomorphism
  Gal(L/ℚ) → ℝ_{>0}, iff `a ≡ 1`. Hence for the witness, `G7Clauses β' ε' L` holds only when every conjugacy isogeny
  μ_σ has `a_σ = 1`; otherwise the implication `G7Clauses → LocalGlue` is vacuously true and carries no information.
