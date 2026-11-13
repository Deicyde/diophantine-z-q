# t-purity2 results log

Base 883c4ddf. Continues t-brauer-purity (T2 already proved there: T2Full.lean, T2Kernel.lean).

- `EtaleLocal.lean` (Mathlib only): COMPILES (lake env lean, 1m42), standard axioms.
  `TPurity2.isEtaleAt_of_isUnramifiedAt_of_flat_local`: `R → S` finitely presented, `q` over `p`,
  `S_q` flat over `R_p` (via `Localization.AtPrime.algebraOfLiesOver`), `IsUnramifiedAt R q`
  ⇒ `IsEtaleAt R q`. (Mathlib's `IsEtaleAt.of_isUnramifiedAt_of_flat` needs global flatness.)
