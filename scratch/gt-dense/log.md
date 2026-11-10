# gt-dense log
- 2026-11-09: started; merged origin/wip/gt-dense-plan. gt-import report absent. Starting step 1 (Window.lean).
- Step 1 done: Window.lean (frequently_window_of, Mathlib only; uses Chebyshev.pi_ge + trivial sqrt-tail, no upper Chebyshev needed), root External/GreenTaoDense.lean with frequently_window for PrimesRelUpperDensityPos. lake build ZInQKernel OK.
- Window.lean: added exists_prime_scale_near (Bertrand), card_window_le_card_quarter, exists_prime_modulus_of_frequently_window (c1/6 X/log X in (X/4,X], X=W*(q/8)). Build OK.
- Drafted (uncompiled, awaiting gt-import) scratch/gt-dense/draft/{SetWeight,PrimeModulusTransference,Assembly}.lean
