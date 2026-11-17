# charpoly-charp results log

Base: wip/degpoly-proof 0a9e6698 + merge origin/main c1e4ed1b8 (6ba2f2a67).
Build: .lake/build and lean/.lake/build reflink-copied from ~/dzq-wt/homfree-noemb (same ZInQKernel tree minus
deg-det Contrib files); `lake build ZInQKernel.OneProof.H.TailC` up to date (VERIFIED).

## Step 1: what `common_trace` needs (read, VERIFIED)

* `HDec.G14Trace.common_trace` (TailC L8718) uses `hM : PkgI3.CharPolyIndepOfEll` once:
  `trace_T_of_frobCompare hM Ab α` gives one integer `t` with `N·tr Tm_ℓ(τ) = t` at ℓ = 3 and ℓ = 5,
  where `(k, Ab, α, N)` come from `FrobTraceLink` (k only `CharP k p`; Ab, α existential).
* From the frob chain (FrobTrace.lean `AlgFrobRed` docstring): α' = F̄ ∘ Fr_Ā, Ā the special fibre over
  k = κ(w) (finite), F̄ the reduction of the descent endomorphism. α is not the reduction of a char-0
  endomorphism, so CharPolyIndepOfEllC cannot be applied.
* BUT common_trace also has h5, h3 (`GalG8Out`): e_ℓ : ℚ̄_ℓ ⊗ V_ℓ(A) ≃ W × W intertwining
  ρ_ℓ(τ) = (jβ)⁻¹ ja · Tm_ℓ(τ) with r_ℓ(τ) ⊕ r_ℓ(τ). Through FrobCompare, V_ℓ(α) ⊗ ℚ̄_ℓ is conjugate to
  M ⊕ M (M 2×2). Then minpoly(V_ℓ α) = minpoly(M) has degree ≤ 2. With Mumford §19 Thm 3
  (homFreeFinite: End free of finite rank, ℤ_ℓ ⊗ End → End(T_ℓ) injective) minpoly(V_ℓ α ⊗ ℚ̄_ℓ) equals
  the minimal polynomial m ∈ ℚ[X] of α in End⁰(Ā), so deg m ∈ {1, 2} and
  tr V_ℓ(α) = −(4 / deg m)·(nextCoeff m) ∈ ℚ, independent of ℓ. (SPECULATIVE until compiled.)
* So common_trace can be rerouted to HomFreeFinite + TateModuleFree (both already in the chain:
  t6 = t6_of_algClosed5 homFreeFiniteAlgClosed, tateModuleFree_of_t5' t5). Chain 2 (R16, A over ℚ)
  uses CharPolyIndepOfEllAlgClosedC (degpoly-proof, from mumfordTorsionAlgClosed and the PROVED
  uniformizationLeafAll_proof). Target −1, no new leaf looks reachable.

## Step 1 result (VERIFIED, compiled)

* scratch/charpoly-charp/LinAlg.lean (Mathlib only): `linIndep_map`, `linIndep_baseChange`, `aeval_intertwines`,
  `trace_eq_of_minpoly` (tr S = −(4/deg m)·nextCoeff m when S ~ M ⊕ M and the annihilator of S is (m), m ∈ ℚ[X]).
* scratch/charpoly-charp/Core.lean (+ HDecomp.C10.Link): `exists_minpoly_endE (hH : HomFreeFinite)
  (hT : TateModuleFree) A α : ∃ m : ℚ[X] monic, ∀ ℓ ≠ char k, ∀ E ⊇ ℚ_ℓ (char 0), ∀ G : E[X],
  aeval (endE α ℓ E) G = 0 ↔ m.map ∣ G` (minimal polynomial of 1⊗α in End⁰; ℤ_ℓ-injectivity of
  tateHomZl; clearing denominators ℤ_ℓ→ℚ_ℓ; left-inverse matrices ℚ→ℚ_ℓ→E).
* scratch/charpoly-charp/CommonTrace.lean (+ TailC): `HDec.G14Trace.common_trace_of_homFree` — exactly
  `common_trace` with `hM : CharPolyIndepOfEll` replaced by `hH : HomFreeFinite` `hT : TateModuleFree`.
  `#print axioms`: [propext, Classical.choice, Quot.sound].
* So (1) answered: the ℓ-independence of tr(α | T_ℓ Ā) is NOT an extra input at that k: G8's intertwining
  (already a hypothesis of common_trace) plus Mumford §19 Thm 3 force it.

## Contrib modules (VERIFIED, `lake build` succeeded, 11764 jobs)

* ZInQKernel/Contrib/OneProof/CommonTraceHomFree.lean (imports TailC): Core + `common_trace_of_homFree`,
  `g14TraceCompat_of_link_homFree`, `HDec.HSyn.G0AssembleMod.linkedTateData_of_local_homFree`.
* ZInQKernel/Contrib/OneProof/R16PrintedC.lean (imports R16Split, CharPolyLattice): `CharPolyIndepOfEllAtQ`,
  `trace_endV_ratC`, `rank_two_of_dimC`, `r16_of_coreYC` (verbatim copies, binder narrowed; one added
  `Module.Free.of_divisionRing` instance because CharPolyLattice's import makes that synthesis time out),
  `r16_of_printedC (hC) (HL : UniformizationLeafAll) (hM : MumfordTorsionAlgClosed)`.

## Fold (manual)

* scratch/charpoly-charp/fold_edit.py: 14 files under OneProof/H (`--check` passes on this tree).
* Fold tree: ~/cc-foldtree = reflink copy of this worktree (no .git) + fold_edit.py; `lake build
  ZInQKernel.OneProof.Main` started 11-16 ~17:45 (LPrefix edit ⇒ whole H chain rebuilds).
