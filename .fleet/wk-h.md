# wk-h: reduction plan for H (SixContactMin)

Full note: `docs/research/wk-h.md`. Drafts: `scratch/wk-h/` (log `scratch/wk-h/log.md`).

**Finding.** N5's proof factors through the Faltings height of the fibre surface `A`. The
*modularity half* (h-trust A1-E1) gives an `L'`-isogeny `J₁(N) → A × Z` with `N ≤ QM²` and
`[L':ℚ] ≤ QM`. The *Arakelov half* (E2-F4) turns that into `h(u)`. All of Glazer's new
arguments (scalar descent B1-B3, C1; conductor bound D1-D4) are in the modularity half. The
36 steps split into 15 applications of well-known theorems, 8 new arguments, 3 repository
replacements and 10 bookkeeping steps. The well-known inputs form six interface packages: Shimura
curve, reduction theory, Faltings 1983, modularity (Pan, eigenform p-adic Hodge theory, newforms,
Carayol), Arakelov (Javanpeykar, Gaudron–Rémond, Faltings Lemma 5, Bost, Pazuki), and the
arithmetic of `ℚ`.

**Recommended reduction (tiers).**
- *Cheap win, done in scratch:* `SixContactMin ⇐ JHeightBound`, a bound on `h(J(u))` with
  `J(u) = −57600F²/G⁶`. `BackToU.lean` compiles with **no `sorry`**, and its axioms are
  `propext`, `Classical.choice` and `Quot.sound`. It proves F4 in the stronger form
  `12h(u) ≤ h(J(u)) + 450`, from two Nullstellensatz certificates.
- *Medium:* `JHeightBound ⇐ ArakelovSig.Literature ∧ ModularLevelBound`, a signature with one
  field per published Arakelov theorem. Drafted in `Arakelov.lean`, which compiles. Glazer's
  E3-E4 arithmetic is proved (`transfer_numerics`). The assembly is still `sorry`. Over abstract
  types the kernel cannot enforce the intended model: the packaged hypothesis is a `j`-height
  bound in disguise (SPECULATIVE, sketch in §4.3). So this tier gives attribution and checked
  bookkeeping, not less trust.
- *Bigger (years):* concrete abelian varieties with Tate modules, Galois representations of
  newforms, p-adic Hodge conditions, the Faltings height and Shimura curves.

Still assumed after the cheap and medium tiers: `ModularLevelBound` (Glazer's descent and
conductor bound with Pan, Carayol, Faltings, reduction theory and the geometry), and the
Arakelov theorems read through the signature.

**Most serious obstacle.** Mathlib v4.35 has no ℓ-adic Galois representations of abelian
varieties or modular forms: no Tate modules, eigenform representations, de Rham/Hodge–Tate
conditions or conductors. So neither Pan, Carayol nor Faltings' Hom theorem can be stated, and
neither can Glazer's own new argument. The Faltings height, needed for every Arakelov theorem, is
also absent. The deep inputs have no faithful elementary form like CR3's Proposition 0; the
theta step, for example, is vacuous when stated about rationals (§3.3).

**Single next step.** Ask the owner whether the `j`-form `JHeightBound` should replace
`SixContactMin` as the assumed statement. If yes, a task allowed to edit `ZInQKernel/` moves
`BackToU.lean` under `ZInQKernel/Hypotheses/`, importing `HeightMin` so that
`SixContactMinAt Mult.S_mul` is `SixContactMin`. It then rethreads the main theorems and runs a
full build and `print_axioms`.
