# Scripts for docs/research/rs-global.md

| Script | Needs | What it checks |
| --- | --- | --- |
| `budget.py` | Python 3 | witness count by role, from the template table and `witness_count_arith` |
| `audit_roles.py` | Python 3 | assignment of the 82 audit records to roles by manuscript line ranges |
| `parity_device.py` | Python 3 | the parity lemma C2 (cubic works, conic fails) and the valuation of `H = A(A − B²)` |
| `goodness_shift.py` | numpy | share of good primes when the fixed shift absorbs more small primes |
| `five_contact_j.py` | sympy | the four degree-6 passports; the map `J₅` with contacts `−1, 0, 1, 2, 3` |
| `five_contact_points.py` | Python 3 | rationals with `M_S = 1` for five and for six contacts (illustration) |

Each runs in under a minute; `five_contact_points.py` takes about 25 s.
