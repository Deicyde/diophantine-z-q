# h-b1-fix work log

## 1. Locator check (N5 = diophantine_zq.tex in repo)
- L557-558: "At a prime outside T, the field K is unramified and every conjugate has good reduction." CONFIRMED (T1).
- L563-566: Milne, polarizable complex tori / Hodge endomorphisms (not good reduction). CONFIRMED wrong locator.
- L752-753: r_ell unramified outside T ∪ {ell} since L unramified, A good reduction, beta unramified. CONFIRMED (T2a).
- L778-781: p ∉ T ∪ {3,5}, L_v/Q_p unramified and A has good reduction → Frobenius comparison. CONFIRMED (T2b).
- L814-816: p=3 adjoin A[3] (A[5] if p=3), Raynaud via Silverberg-Zarhin Thm 3.5. No model. CONFIRMED.
- L476-477: b11's sentence "represents exactly the full-three moduli problem, so its generic fiber is Y_3". CONFIRMED.
## 2. Edits: Summary item 1 (F1 remark, R5), Summary item 4 locators, §1.2 finiteness (excellence) + flatness (normal dim 2 → CM → miracle flatness).
## 3. Edits: M9 row → full R2 enumeration (6 types, W-images, (0,2) absent); NV step 2 → 'conductor prime to p' + orders disc -4,-3,-24 maximal with W-images.
## 4. Edit: NV step 3 → rv §3.3 argument (A' local finite over R, Frac=k_p ⇒ strictly henselian unibranch, residue degree 1 = [I_P:I_Q]; going-down via flatness; I_q ⊂ I_P).
## 5. Edits: W-layer remark (R7, Elkies constants -1,3) + labelling robustness after NV; §5 table L563-566→L557-558, rows L752-753, L778-781 added; downstream paragraph names them, L848-849 note, L814 confirmed.
## 6. Edits: new §4A (one Q-structure; inputs 1-4 STANDARD/UNVERIFIED with where-to-check; consequence); pointers from PR(ii) step 1, §6 items 2 and 5, §7 verdict; §7 line range fixed.
## 7. Script reruns (load 4.5)
- scratch/h-b1/b1_checks.py (cwd scratch/h-b1, ~/pyenv/bin/python): 0.85 s; output byte-identical (cmp) to b1_checks.output.txt.
- scratch/rv-h-b1/rv_checks.py (cwd scratch/rv-h-b1): 1.26 s; output byte-identical to rv_checks.output.txt.
- Copies saved in scratch/h-b1-fix/*.rerun.output.txt.
