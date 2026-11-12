p='docs/research/h-decomposition.md'; L=open(p).read()
def r(a,b):
    global L
    assert L.count(a)==1,(a[:70],L.count(a)); L=L.replace(a,b)
r("""**What cannot be stated in Lean today, and why.** Items 1-3, 5, 8, 16, 18-22 need definitions that
no Lean library has: the Shimura curve as a moduli scheme of QM abelian surfaces with its canonical
model (1-3, 5), Néron models (8), the modular curve X₁(N) and its Jacobian over ℚ (16, 18), the
stable Faltings height (18-22). Item 17 needs conductors of ℓ-adic representations (medium).""",
"""**What cannot be stated in Lean today, and why.** Items 1-3, 5, 16, 18-22 need definitions that
no Lean library has: the Shimura curve as a moduli scheme of QM abelian surfaces with its canonical
model (1-3, 5), the modular curve X₁(N) and its Jacobian over ℚ (16, 18), the stable Faltings
height (18-22). Item 8 in its Néron-model form needs Néron models, but its Galois consequence,
the form the proof could use, is stated (and A6 no longer needs it). Item 17 needed conductors of
ℓ-adic representations; def-ladic-cond has now defined them and stated it (not yet in
`Leaves.lean`). Textbook items T10-T12 need étale cohomology and analytification.""")
r("Revised by hsyn-fix (2026-11-11) after six reviews and provers:",
  "Brought up to date by hsyn-fold (2026-11-12) with eleven later provers (dated paragraph at the end\nof §0; results log `scratch/hsyn-fold/log.md`). Revised by hsyn-fix (2026-11-11) after six reviews and provers:")
open(p,'w').write(L); print('ok')
