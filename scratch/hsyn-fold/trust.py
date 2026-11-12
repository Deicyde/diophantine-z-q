p='docs/research/h-trust.md'; L=open(p).read()
old = """- *Suppliers.*
  - A4 gives `A[3] ⊂ A(K)`.
  - Potentially good reduction: Grothendieck's semistable reduction theorem (SGA 7 I, LNM 288,
    Exp. IX, Thm 3.6) plus the toric-part argument of h-b1 §4(ii) step 2. Alternatively Morita,
    Hokkaido Math. J. 10 (1981). Locators UNVERIFIED.
  - Finiteness of `ρ(I_v)` and Néron–Ogg–Shafarevich: Serre–Tate, *Good reduction of abelian
    varieties*, Ann. of Math. 88 (1968), Thms 1-2. Locator UNVERIFIED.
  - `1 + 3M₄(ℤ₃)` is torsion-free (elementary; N5 L468-470).
- *Status:* **[M]** (rv-h-b1 §5: Lemma PR(ii) holds as stated, including `v | 2`). Its inputs
  are [R]. Fallback as in A5."""
new = """- *Suppliers* (Raynaud route; rv-a6-route §5, adopted by hsyn-fold 2026-11-12): A4; Raynaud
  (SGA 7 IX 4.7 + 3.5); Serre–Tate Thm 1; Mumford §4 (structure of `A[n]`); `B ⊗ ℚ₃` division
  (computed). Locators UNVERIFIED. In Lean (`scratch/h-decomposition/Leaves.lean`, glue-a6-alg):
  `PkgI2.goodReduction_of_QM_rational3` from the leaves `RaynaudCriterion`,
  `NeronOggShafarevich`, `TorsionStructure` alone, with the algebra step `QuatUnipotentTrivial`
  proved; axioms `propext`, `Classical.choice`, `Quot.sound`. The instantiation on N5's `A`
  (which needs A4 and the moduli objects) is not in Lean.
- *Second route* (h-b1 §4(ii) steps 2-3, kept):
  - A4 gives `A[3] ⊂ A(K)`.
  - Potentially good reduction: Grothendieck's semistable reduction theorem (SGA 7 I, LNM 288,
    Exp. IX, Thm 3.6) plus the toric-part argument of h-b1 §4(ii) step 2. Alternatively Morita,
    Hokkaido Math. J. 10 (1981). Locators UNVERIFIED.
  - Finiteness of `ρ(I_v)` and Néron–Ogg–Shafarevich: Serre–Tate, *Good reduction of abelian
    varieties*, Ann. of Math. 88 (1968), Thms 1-2. Locator UNVERIFIED.
  - `1 + 3M₄(ℤ₃)` is torsion-free (elementary; N5 L468-470).
- *Status:* **[M]** (rv-h-b1 §5: Lemma PR(ii) holds as stated, including `v | 2`; the Raynaud
  route reviewed by rv-a6-route, sound after two wording repairs). Its inputs are [R]. Fallback
  as in A5."""
assert L.count(old)==1; L=L.replace(old,new)
L = L.rstrip('\n') + """

Task hsyn-fold (2026-11-12), step A6 only, applying `docs/research/rv-a6-route.md` §5. A6's
suppliers line is now the Raynaud route (A4; Raynaud SGA 7 IX 4.7 + 3.5; Serre–Tate Thm 1;
Mumford §4; `B ⊗ ℚ₃` division), with h-b1's argument (Grothendieck's semistable reduction and the
toric-part argument) kept as a second route. The Lean proof of the Raynaud route from its three
leaves (glue-a6-alg, `QuatUnipotentTrivial` proved) is cited. No status, count, constant or other
step changes.
"""
open(p,'w').write(L); print('ok')
