"""leaf-fold: edits of docs/research/h-decomposition.md (header, §0 paragraph, R10/R14 notes,
remaining-work list). Run once on the base note; doc_table.py adds the §2.2 Status column."""
p = 'docs/research/h-decomposition.md'
s = open(p).read()
def rep(old, new, count=1):
    global s
    assert s.count(old) == count, (old[:60], s.count(old))
    s = s.replace(old, new)

# header
rep("""end of §0). No file under
`ZInQKernel/`, `blueprint/` or another task's notes was edited.""",
"""end of §0). Brought up to date by **leaf-fold** (2026-11-13; report `docs/research/leaf-fold.md`,
log `scratch/leaf-fold/log.md`): the leaves closed in `ZInQKernel/Contrib/` are folded in, and
`HSyn.sixContactMin_of_open` takes only the **open** leaves (dated paragraph at the end of §0).
No file under `ZInQKernel/`, `blueprint/` or another task's notes was edited.""")

# §0 paragraph, before the locator audit paragraph
rep("""**Locator audit (loc-adopt, 2026-11-12).**""", open('scratch/leaf-fold/doc_par0.md').read() + """
**Locator audit (loc-adopt, 2026-11-12).**""")

# R10, R14 notes
rep("""good-reduction or odd-`p` hypothesis); the Tate weights `0, −1` are a consequence (duality and
Hodge dimensions).""", """good-reduction or odd-`p` hypothesis); the Tate weights `0, −1` are a consequence (duality and
Hodge dimensions). **leaf-fold (2026-11-13): statement corrected.** The Lean field omitted the
vanishing of the other Hodge–Tate multiplicities, which G9's output `HasHTWeights p ρ {0, −1}`
needs (g9-derham, finding F1). The open bundle uses `PkgI4.DeRhamComparisonHT`: R10 with the
clause "multiplicity `0` at every weight `w ∉ {0, −1}`" (g9-derham's `R10Weights`), part of the
same published statement (Hodge–Tate decomposition `ℂ_p ⊗ V_p(A) ≅ ℂ_p^g ⊕ ℂ_p(1)^g`, Tate 1967,
Faltings 1988; UNVERIFIED locators). `PkgI4.deRhamComparisonHT_iff` proves it equivalent to the old
field plus `R10Weights`.""")
rep("""construction, or the leaf must be restricted to cusp forms (a statement check, WP13; the Lean
statement is not changed here).""", """construction, or the leaf must be restricted to cusp forms (a statement check, WP13; the Lean
statement is not changed here). **leaf-fold (2026-11-13): statement corrected.** The open bundle
uses g0-mod-galois's `R14Det` (as `HSyn.OpenResearchLeaves.r14`): R14 with the published
determinant `det ρ_g = ε·χ_ℓ^{k−1}`, `ε` of finite image, which G12's determinant argument needs
(g0-mod-galois §3). It implies the old field (`HSyn.eigenformRepExists_of_r14Det`).""")

# remaining work
rep("""**Remaining work after leaf-adopt3 (2026-11-13).**""", open('scratch/leaf-fold/doc_remaining.md').read() + """
**Remaining work after leaf-adopt3 (2026-11-13; superseded by the list above).**""")
open(p, 'w').write(s)
print('ok')
