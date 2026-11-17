# mcheck-rc-deep log

- 2026-11-17 start (fresh; no earlier log). Read map report/fleet note/log of mcheck-rc-map.
- Block 1 (L2834-3410; map said 3393, proof ends 3410) read in full.
- Block 2 (L4747-5205) read, with setup L4650-4760 and the defs at L3704-3730, L3882-3892, (3.5) L2446, (4.6) L4045.
- First pass: no error found in either block. Writing checks (b1_*.py, b2_*.py).
- b1_checks.py 17/17 (two first-run FAILs were script bugs: Z- instead of Z_(2)-lattice for the span; wrong generator in H5). b1_transfer.py 6/6 (negative control fails as expected). b1_homotopy.py 5/5 (negative control fails).
