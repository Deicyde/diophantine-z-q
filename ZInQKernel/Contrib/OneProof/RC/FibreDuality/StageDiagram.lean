import ZInQKernel.Contrib.OneProof.RC.FibreDuality.LimitGlobal

/-!
# Lane RC31, round 3, part 2: the stagewise matrix diagram of the paired limit

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-inner-limit` (tex 4391–4451): at one coefficient
stage `A_i`, after transporting the actual diagram (global complex, localization at the derivative
label, the trace pairings and the retained global duality with its reverse map and homotopies) to
the bounded finite free model, everything is a finite tuple of matrices over `A_i` satisfying
exact polynomial identities.

`StageMatrixDiagram A rank` is that tuple, at one stage, over any commutative ring `A`, for model
ranks `rank` (a parameter, so that stages with equal ranks can be compared by transport along the
equality). Its fields are exactly those of round two's `ComplexStages`, `RetainedLimitPairingStages`
and `RetainedGlobalDualityStages` at one stage, with the identities holding EXACTLY over `A`
(rather than modulo a stage ideal).

Kind: definition.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.FibreDuality

open Matrix
open ZInQ.Contrib.CloudB3RC53.PairedFunctional

/-- **The stagewise matrix diagram of the paired limit** (tex 4391–4451, one stage, exact
identities): the model differentials `dC` with `d_C² = 0`; the localization at the derivative label
`res` (in the coordinates `lIdx` of the split model), a chain map; the global trace pairing `glob`
and the local pairing `loc` with chain-level reciprocity; and the reverse map `rev` of the global
duality map with its source and target homotopies (`srcHom`, `tgtHom`) and the three
homotopy-inverse identities. Kind: definition (data with identities). -/
structure StageMatrixDiagram (A : Type) [CommRing A] (rank : ℤ → ℕ) where
  /-- The model differential matrices. -/
  dC : ∀ a b : ℤ, a + 1 = b → Matrix (Fin (rank b)) (Fin (rank a)) A
  /-- `d_C² = 0`. -/
  dC_sq : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c), dC b c hbc * dC a b hab = 0
  /-- The localization at the derivative label, in the coordinates of the split model. -/
  res : ∀ n : ℤ, Matrix (lIdx n) (Fin (rank n)) A
  /-- It is a chain map (the split model has zero differential). -/
  res_comm : ∀ n : ℤ, res (n + 1) * dC n (n + 1) rfl = 0
  /-- The global trace pairing `Gᵃ × Gᵇ → A`, `a + b = 3`. -/
  glob : ∀ a b : ℤ, a + b = 3 → Matrix (Fin (rank a)) (Fin (rank b)) A
  /-- The local pairing of the split model. -/
  loc : ∀ a b : ℤ, Matrix (lIdx a) (lIdx b) A
  /-- Chain-level reciprocity. -/
  recip : ∀ (a b : ℤ) (h : a + b = 2),
    (dC a (a + 1) rfl)ᵀ * glob (a + 1) b (by omega) +
        sgn a • (glob a (b + 1) (by omega) * dC b (b + 1) rfl) +
        (res a)ᵀ * loc a b * res b = 0
  /-- The reverse map of the global duality map, in the dual coordinates. -/
  rev : ∀ a : ℤ, Matrix (Fin (rank a)) (cIdxOf rank (3 - a)) A
  /-- The source homotopy. -/
  srcHom : ∀ a b : ℤ, b + 1 = a → Matrix (Fin (rank b)) (Fin (rank a)) A
  /-- The target homotopy. -/
  tgtHom : ∀ a b : ℤ, b + 1 = a → Matrix (cIdxOf rank (3 - b)) (cIdxOf rank (3 - a)) A
  /-- The reverse map is a chain map. -/
  chain : ∀ a : ℤ,
    rev (a + 1) * dualDiffMatOf dC res a (a + 1) rfl - dC a (a + 1) rfl * rev a = 0
  /-- The first homotopy-inverse identity. -/
  src : ∀ a : ℤ,
    rev a * forwardMatOf glob loc res a - srcHom (a + 1) a rfl * dC a (a + 1) rfl -
      dC (a - 1) a (by omega) * srcHom a (a - 1) (by omega) - 1 = 0
  /-- The second homotopy-inverse identity. -/
  tgt : ∀ a : ℤ,
    forwardMatOf glob loc res a * rev a -
      tgtHom (a + 1) a rfl * dualDiffMatOf dC res a (a + 1) rfl -
      dualDiffMatOf dC res (a - 1) a (by omega) * tgtHom a (a - 1) (by omega) - 1 = 0

end ZInQ.Manuscript.RC.FibreDuality
