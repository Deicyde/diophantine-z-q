# mcheck-rc-app: Appendices E-G of the manuscript mapped; conclusion on Theorem 5.3 (hyp:RC) updated

(Status: IN PROGRESS. The conclusion will be written after the map is complete.)

## Appendix map

Columns: tex lines | label | claim | kind | size (lines) | depends on | GZ/TYZ contact | used in.
"Own" means Elliot's own argument. Print locators are as the manuscript gives them; none was checked
against a print (no network).

### Appendix E (app:even-source), tex L6825-8205

| tex | label | claim | kind | size | depends on | GZ/TYZ | used in |
|---|---|---|---|---|---|---|---|
| 6825-6845 | (intro, setup) | E fixed; Lambda=Z_2[[t]] real cyclotomic, A=Lambda[1/2]; arithmetic Frobenius | own (conventions) | 21 | sec 7 setup | none | - |
| 6846-6889 | ex:app-kato-system (statement) | one retained-smoothed class Z_F (K1) for the whole family with fixed denominator 2^{c_E}; one F_E in Lambda, F_E(0)!=0, with height-one divisibility (K2); central reciprocity (K3): v2 exp*(F_E(Z_F)_x(0)) = v2 L_*(h) + sum_{q|F, q not dividing h} v2 #E^h(F_q) + 2e + v2 F_E(0) + eps_h, eps_h bounded | own construction on Kato's Euler system | 44 | Kato (below) | none | ex:sec7-even-scalar (L1825-1966), ex:app-even-scalar |
| 6890-6985 | (proof par. 1-3) | fixed symbol combination xi with both Betti projections nonzero; smoothing c=d_s=1+2^e 3N_odd F (K5), central scalar s_F with v2 = 2e (K6); integral j_* condition survives ramified corestriction (Leray + Mackey (K7)) | cites Kato (8.1.3) p.180, 8.9, 8.11, 13.6-13.7, (4.2.4), Thm 6.6; Stacks Tags 03Q9, 03QA; own Mackey argument | 96 | - | none | (K1) |
| 6986-7040 | (proof par. 4) | primitive twisting y_m = cor(z_{Dm} (x) e_chi) (K8) is an Euler system with factor (K9) E_q = P_q(q^{-1} sigma_q^{-1}); discriminant 4h covered by repeated-two norms | cites Kato Prop 8.12, 13.1 pp.224-225; own | 55 | par. 3 | none | (E.1), (K2) |
| 7041-7099 | (proof par. 5) | coefficient map Phi_n (K10) is integral and equivariant; one class Z_F; exact identity (E.1) (Z_F)_x = prod_{q|F/d} E_q(chi_x) y_{2^inf}; (E.2) dyadic character in module action | own; cites Nekovar Cor 4.1.3 p.96 (lim^1) | 59 | par. 4 | none | (K1), (K3) |
| 7100-7202 | (proof par. 6) | central trace (K12) = unnormalized chi-sum; Kato Thm 6.6 + 9.7 give (K13) per_f = s_F L_{prime(2Nd)}(f,chi,1) b_eps e_B; descent via basis sqrt(h) e_chi gives (K14) s_F b_eps L_*(h)/h times omitted 2N factors; no phi(D) or 2^{omega} factor; E_q(0) = #E^h(F_q)/q | cites Kato Thm 6.6 p.163, Thm 9.7 p.189; own normalization | 103 | par. 5 | none | (K3) |
| 7203-7245 | (proof par. 7) | hypotheses of Kato 13.4(2) verified: generic sign components nonzero (via Kato 13.5(2) finiteness of zero L-values), rank-one eigenspaces, w=-1, irreducibility, open image condition (v); gives (K15); H^1_p free of rank one | cites Kato Thm 13.4(1),(2), 13.5(2), (12.2.1)-(12.2.2); Serre open image | 43 | par. 6 | none | (K2) |
| 7246-7356 | (proof par. 8-9) | cone (K16) from j_* to full cochains: D_q = E_q at inactive good, 1 at active good; F_2 (local at 2) and F_bad with F_E(0)!=0; length chain proves (K2); uniformity | own; Kato (12.2.3) p.220; local duality | 111 | par. 7 | none | (K2) |
