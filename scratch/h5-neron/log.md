# h5-neron results log

Start 2026-11-12 22:53 PST. Base 01267822. Build of ZInQKernel.HDecomp.Faltings.Leaves: OK.

## Plan (decided 23:00)
- Nonzero abelian varieties cannot be constructed in Mathlib v4.35 (Objects.lean `AbVar.zero`
  docstring): StableHeightFinite for elliptic curves is NOT provable now (needs AV7 + AN3).
- Provable now: (A) Néron mapping-property glue (lift, uniqueness, products);
  (B) the zero abelian variety: Néron model, metrized model, stable height = 0;
  (C) reduction of "stable height = Néron height over a semistable field" to stated Props.
