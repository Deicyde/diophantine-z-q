# cpts-transport results log

Setup: g0-assemble3's compiled olean chain (LPrefix..TailF, worktree g0-assemble3 at 357f5d9e) copied to
~/cpts-olean (not committed); test files `import TailF`; compiled with `ct.sh`.

## Step 1 (10:15): `CPtsTransport` proved — VERIFIED (compiled)

- File `CPtsTransport.lean` (`import TailF`; = T1.lean). Output `CPtsTransport_out.txt`: 0 errors, no sorry, 6 s.
- `HSyn.G0Split.FibreQM.CPtsT.appLE_of_eq`, `cEvalAt_of_eq` (values along `p.left = x.left ≫ T`).
- `HSyn.G0Split.FibreQM.CPtsT.cPts_of_isPullback (A : PkgI3.AbVar K) (σ) (Q : PkgI3.AbVar ℂ) (T0)
  (S : IsPullback T0 Q.X.hom A.X.hom (Spec.map (ofHom σ)))` : the `∃ ψ …` body of CPtsTransport.
  Proof: `E : Q.X ≅ (A.baseChange ℂ).X` from `IsPullback.isoIsPullback`; `φ = E.hom * (toUnit ≫ (η ≫ E.hom)⁻¹)`,
  pointed, `IsMonHom` by `G0FibreSimple.rigidityHom` (proved in mul-rigidity); `ψ = (· ≫ φ)` then
  `UnramTate.bcPt` (explicit `Algebra.id ℂ` instance; the default instance search made a whnf timeout);
  `(ψ x).left = x.left ≫ φ.left ≫ pullback.fst`, so `U' = T⁻¹ᵁU`, `s' = T.app U s`.
- `HSyn.G0Split.FibreQM.cPtsTransport_proof : CPtsTransport`: paste `IsBaseChangeOf`'s square, the square of
  `e.inv` (iso), and the pullback square of `A.baseChange ℚ̄`; `Spec(ιe) ≫ 𝟙 ≫ Spec(emb) = Spec(ιe ∘ emb)`.
  Only the pullback clause of `IsBaseChangeOf` is used (not the `ι`, `η` clauses).
- `#print axioms` both: `[propext, Classical.choice, Quot.sound]`.
