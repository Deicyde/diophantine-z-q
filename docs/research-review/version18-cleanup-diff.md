# Complete Version 18 cleanup comparison

Base commit `f7b803e3252fa955ab6dcdc2ac3e756a03fde184`, manuscript SHA256 `e594eba7c9634f445185f507f05d7436ea6e6b1acc0c226051ab40e3767aee12`. Candidate manuscript SHA256 `23e7f5939c29afc85f4c0bf293164dd0e49095616613e06608e929426f8fb57f`. The line numbers below are one-based in those exact files. This is an author-produced comparison for review, not an independent verdict. It includes all changes relative to the base, not only the repair of PR119 head `f8a5dcf5e9816cf528d7868deb2e88fc2174565b`. Historical manuscript files are not modified.

Every hunk is printed below with both sides and three lines of context. Trailing horizontal whitespace is elided in this human-readable display; no non-whitespace text is omitted. The exact source bytes are identified by the hashes above. The classes are navigation aids; they do not establish proof preservation. The catalogue and status changes retain the limitations in [the status record](version18-cleanup-status.md). Earlier coverage and the open H170 obligation are explicitly retained there. The actual gate findings for this PR are separate from the historical PR107 IDs.

## The two source-bound symbol restorations

### F0406: `h_{*}` to `h_*` in this PR

Base line 2328; candidate line 2323. These two spellings render identically. P14 fixes the progression h=h_* mod L; P16 invokes exactly that progression in the compatible CRT conditions.

Correction to the first PR description: the damaged spelling `h_{\cdot }` occurred only in an intermediate local typography proposal and was caught before publication. It is not the base spelling and is not a mathematical correction introduced by this PR. The final edit preserves the star already present in the base. The original supplier comparison is retained below to make the identity inspectable.

Supplier: [research/quartic214/proofs/uniform-existence.md](https://github.com/elliotglazer/diophantine-z-q/blob/f7b803e3252fa955ab6dcdc2ac3e756a03fde184/research/quartic214/proofs/uniform-existence.md), SHA256 `d13cc2b846dc72a3f5b5cce8dcf11d3f11b33c45ebc3883263840afb8d82f3bc`. The following are exact project-source passages, not excerpts of an external copyrighted paper.

Source line 67:

```text
[P14: scalar finite preparation in correct order] For a particular x,N, put D_s=1+149^2 r4. Both gcd(A_N r4,D_s) and gcd(A_N r4+9792D_s,D_s) equal1; thus R_s(R_s+9792) has square reduced denominator D_s^2. Direct integer parity/congruences give v2(R_s) in {2,3} and v3(R_s)=v17(R_s)=0. Hence 1+9792/R_s is a square at2,3,17 (its difference from1 has depth>=3,>=1,>=1 respectively), so R_s(R_s+9792) is a square there. At its finite odd-valuation numerator support choose an initial H formal enough; then choose the positive scalar index a still deeper and arbitrarily large, with [a]P in the fixed real neighborhood of O. This makes the three terms of W_s integral at that support and deep enough at2,3,17 for the actual zero-preparation pole bounds. Compact-group recurrence in finite-index progressions gives the finite and real conditions together. After a is fixed, continuity preserves the scalar conditions for H in one progression h=h_* mod L, with64|h_*,64|L and the component-order divisibility included. This ordering permits support and depth to depend on x,N; the common N_C does not. The retained scalar/root chart guards hold on the chosen neighborhoods. No new condition a=1 mod any modulus is imposed.
```

Source line 71:

```text
[P16: prime theorem quantifiers and CRT] Apply the actual V15 simultaneous-prime theorem to this fixed list, prescribed divisibility q|w, fixed avoidance modulus M=rad_odd(3*17*L) with7 omitted, and arbitrarily large slope/prime lower bounds. Choose these data before the analytic asymptotic parameter (call it X_sel, distinct from input x). Its fixed-field proof first fixes the cutoff so positive cutoff mass exceeds the full obstruction tail, then fixes the ray field, then lets X_sel grow along sufficiently slow diagonal strip widths. No uniform estimate in x,N,T,D,L or number of contacts is needed. The selected Gaussian generators have residues9 mod16,1+3i mod7,i modM; adjacent norms d_minus,d_plus have v2=6,2 and cross-sign gcd4, and all odd factors avoid L. Define U=lcm(d_minus/4), V=lcm(d_plus/4). Full two-torsion makes d/4 kill the reduction of the double P; gcd(U,V)=1, gcd(U,L)=16 and gcd(V,L)=1. Thus h=0 mod U, h=1 mod V, h=h_* mod L are compatible. The real progression lemma gives arbitrarily large h in the original fixed compact neighborhoods. Set H=[h]P, U_i=[hn_i]P, V_i=[(h-1)n_i]P. This gives natural formal depth>=1 at the correct primary/opposite places and preserves the scalar data. The optional strengthened separation p_i not dividing d_j is available from the weighted strip argument; natural depth1 alone suffices for this 214 construction. Every merged repeated coefficient carries one prime/generator and all its incidences; CRT is imposed once and supplies all those incidences.
```

Candidate consumer, line 2323:

```tex
[P16: prime theorem quantifiers and CRT] Apply the actual \(V_{15}\) simultaneous-prime theorem to this fixed list, prescribed divisibility q|w, fixed avoidance modulus \(M=\operatorname{rad}_{\text{odd}}(3\cdot 17\cdot L)\) with 7 omitted, and arbitrarily large slope/prime lower bounds. Choose these data before the analytic asymptotic parameter \((\text{call} it X_{\text{sel}}, \text{distinct} \text{from} \text{input} x)\). Its fixed-field proof first fixes the cutoff so positive cutoff mass exceeds the full obstruction tail, then fixes the ray field, then lets \(X_{\text{sel}}\) grow along sufficiently slow diagonal strip widths. No uniform estimate in x,N,T,D,L or number of contacts is needed. The selected Gaussian generators have residues 9 mod 16,1+3i mod 7,i modM; adjacent norms \(d_{-},d_{+}\) have \(v_{2}=6,2\) and cross-sign gcd 4, and all odd factors avoid \(L\). Define \(U=\text{lcm}(d_{-}/4)\), \(V=\text{lcm}(d_{+}/4)\). Full two-torsion makes d/4 kill the reduction of the double \(P\); \(\text{gcd}(U,V)=1\), \(\text{gcd}(U,L)=16\) and \(\text{gcd}(V,L)=1\). Thus \(h=0\) mod \(U\), \(h=1\) mod \(V\), \(h=h_*\) mod \(L\) are compatible. The real progression lemma gives arbitrarily large \(h\) in the original fixed compact neighborhoods. Set \(H=[h]P\), \(U_{i}=[hn_{i}]P\), \(V_{i}=[(h-1)n_{i}]P\). This gives natural formal \(\operatorname{depth}\ge 1\) at the correct primary/opposite places and preserves the scalar data. The optional strengthened separation \(p_{i}\) not dividing \(d_{j}\) is available from the weighted strip argument; natural depth 1 alone suffices for this 214 construction. Every merged repeated coefficient carries one prime/generator and all its incidences; CRT is imposed once and supplies all those incidences.
```

### F0407: `j_{*}` to `j_*` in this PR

Base line 3390; candidate line 3377. These two spellings render identically. C05 preserves the integral j_* condition before mapping to the open scheme; C06 compares the full/j_* local cones.

Correction to the first PR description: the damaged spelling `j_{\cdot }` occurred only in an intermediate local typography proposal and was caught before publication. It is not the base spelling and is not a mathematical correction introduced by this PR. The final edit preserves the star already present in the base. The original supplier comparison is retained below to make the identity inspectable.

Supplier: [research/quartic214/proofs/source-carry.md](https://github.com/elliotglazer/diophantine-z-q/blob/f7b803e3252fa955ab6dcdc2ac3e756a03fde184/research/quartic214/proofs/source-carry.md), SHA256 `f7f4e550a4dcfbbd3b5ffcf783b11411f7888c821dbab7febb5132b7b2b891ed`. The following are exact project-source passages, not excerpts of an external copyrighted paper.

Source line 19:

```text
[C05: Kato required full index set] Read the actual current proof at13347–13946 and the actual earlier v11 `norms.md` and `interface.md` arguments. For a fixed constituent with primitive conductor D=2^a*d, the retained construction defines y_m=cor_{Q(zeta_Dm)/Q(zeta_m)}(z_Dm tensor e_chi) for every m with (m,c*d_s)=1. K5 makes N_K=2Nd and Nprime=c*d_s coprime. Restricting to all m divisible by N_K gives every index required by Kato1999§0.1, not merely the smaller2004§13.1 set. The class has the integral j_* condition by the inertia/Leray and Mackey calculation before mapping to the open scheme with N_K inverted. The same fixed lattice-clearing factor2^c_E applies at every level. It is a unit at the height-one localizations away from2 used downstream.
```

Source line 26:

```text
Arithmetic Frobenius acts on T*chi and inverse deck action is in the substitution; the representation is not dualized again. For every n>=1 the supports S_(D*N_K*2^n) and S_(D*2^n) equal prime(2Nd). Corestriction transitivity through the common upper field gives cor(y_(N_K*2^n))=y_(2^n), without an Euler factor or a field-degree multiplier. These equalities commute with transition maps; the cofinal dyadic inverse limit is exactly the Section0.7 divisor-parameter-one class xi_K, distinguished from the modular symbol xi. Thus the localized coordinate ideal J in K15 is the ideal of this actual retained class. Rank-one proportionality would not suffice and is not used. The full/j_* local cone comparison preserves H^1 and the same class/ideal; paying for the actual H^2 cone and fixed local factors yields K2. This source repair is incorporated already and is unchanged in214's supplier. A narrow current connection locator13775–13778 summarizes the coordinate-ideal conclusion; it is not the whole index/class argument. This carry binds the actual13799–13899 argument as well as its complete application record, so that short locator is not mistaken for the proof.
```

Candidate consumer, line 3377:

```tex
[C05: Kato required full index set] The current proof at 13347--13946 and the earlier \(v_{11}\) \nolinkurl{norms.md} and \nolinkurl{interface.md} arguments supply the construction below. For a fixed constituent with primitive conductor \(D=2^{a}\cdot d\), the retained construction defines \(y_{m}=\text{cor}_{Q(\zeta _{Dm})/Q(\zeta _{m})}(z_{Dm} \otimes e_{\chi })\) for every \(m\) with \((m,c\cdot d_{s})=1\). \(K_{5}\) makes \(N_{K}=2Nd\) and \(N'_K=c\cdot d_{s}\) coprime. Restricting to all \(m\) divisible by \(N_{K}\) gives every index required by Kato 1999\S{}0.1, not merely the smaller 2004\S{}13.1 set. The class has the integral \(j_*\) condition by the inertia/Leray and Mackey calculation before mapping to the open scheme with \(N_{K}\) inverted. The same fixed lattice-clearing \(\text{factor}2^{{c}_{E}}\) applies at every level. It is a unit at the height-one localizations away from 2 used downstream.
```

## All 166 hunks

| Hunk | Base lines | Candidate lines | Edit class |
|---|---|---|---|
| [H001](#h001) | 1-5 | 1-5 | status, source locator or provenance prose |
| [H002](#h002) | 76-83 | 76-82 | status, source locator or provenance prose |
| [H003](#h003) | 125-130 | 124-133 | status, source locator or provenance prose |
| [H004](#h004) | 184-200 | 187-198 | status, source locator or provenance prose |
| [H005](#h005) | 1996-2009 | 1994-2007 | status, source locator or provenance prose |
| [H006](#h006) | 2060-2086 | 2058-2081 | status, source locator or provenance prose |
| [H007](#h007) | 2095-2111 | 2090-2106 | status, source locator or provenance prose |
| [H008](#h008) | 2125-2167 | 2120-2162 | status, source locator or provenance prose |
| [H009](#h009) | 2173-2179 | 2168-2174 | whitespace only |
| [H010](#h010) | 2184-2251 | 2179-2246 | status, source locator or provenance prose |
| [H011](#h011) | 2254-2264 | 2249-2259 | status, source locator or provenance prose |
| [H012](#h012) | 2270-2292 | 2265-2287 | status, source locator or provenance prose |
| [H013](#h013) | 2294-2306 | 2289-2301 | prose, notation or text-conversion cleanup; inspect both sides |
| [H014](#h014) | 2310-2316 | 2305-2311 | whitespace only |
| [H015](#h015) | 2321-2333 | 2316-2328 | star-subscript spelling and surrounding prose; same mathematical symbol |
| [H016](#h016) | 2336-2380 | 2331-2375 | status, source locator or provenance prose |
| [H017](#h017) | 2390-2420 | 2385-2415 | status, source locator or provenance prose |
| [H018](#h018) | 2424-2474 | 2419-2469 | status, source locator or provenance prose |
| [H019](#h019) | 2476-2516 | 2471-2511 | status, source locator or provenance prose |
| [H020](#h020) | 2524-2556 | 2519-2551 | status, source locator or provenance prose |
| [H021](#h021) | 2580-2610 | 2575-2605 | status, source locator or provenance prose |
| [H022](#h022) | 2612-2638 | 2607-2633 | status, source locator or provenance prose |
| [H023](#h023) | 2640-2648 | 2635-2643 | status, source locator or provenance prose |
| [H024](#h024) | 2674-2680 | 2669-2675 | whitespace only |
| [H025](#h025) | 2682-2708 | 2677-2701 | status, source locator or provenance prose |
| [H026](#h026) | 2729-2735 | 2722-2728 | prose, notation or text-conversion cleanup; inspect both sides |
| [H027](#h027) | 2776-2784 | 2769-2777 | prose, notation or text-conversion cleanup; inspect both sides |
| [H028](#h028) | 2806-2812 | 2799-2805 | status, source locator or provenance prose |
| [H029](#h029) | 2824-2850 | 2817-2843 | status, source locator or provenance prose |
| [H030](#h030) | 2860-2866 | 2853-2859 | status, source locator or provenance prose |
| [H031](#h031) | 2868-2888 | 2861-2881 | prose, notation or text-conversion cleanup; inspect both sides |
| [H032](#h032) | 2890-2910 | 2883-2903 | status, source locator or provenance prose |
| [H033](#h033) | 2926-2978 | 2919-2967 | status, source locator or provenance prose |
| [H034](#h034) | 2980-2998 | 2969-2987 | status, source locator or provenance prose |
| [H035](#h035) | 3018-3036 | 3007-3025 | status, source locator or provenance prose |
| [H036](#h036) | 3046-3054 | 3035-3043 | status, source locator or provenance prose |
| [H037](#h037) | 3080-3117 | 3069-3104 | status, source locator or provenance prose |
| [H038](#h038) | 3119-3149 | 3106-3136 | status, source locator or provenance prose |
| [H039](#h039) | 3154-3176 | 3141-3163 | prose, notation or text-conversion cleanup; inspect both sides |
| [H040](#h040) | 3179-3185 | 3166-3172 | prose, notation or text-conversion cleanup; inspect both sides |
| [H041](#h041) | 3187-3193 | 3174-3180 | prose, notation or text-conversion cleanup; inspect both sides |
| [H042](#h042) | 3195-3201 | 3182-3188 | whitespace only |
| [H043](#h043) | 3203-3213 | 3190-3200 | whitespace only |
| [H044](#h044) | 3221-3227 | 3208-3214 | prose, notation or text-conversion cleanup; inspect both sides |
| [H045](#h045) | 3232-3246 | 3219-3233 | status, source locator or provenance prose |
| [H046](#h046) | 3248-3254 | 3235-3241 | prose, notation or text-conversion cleanup; inspect both sides |
| [H047](#h047) | 3260-3266 | 3247-3253 | status, source locator or provenance prose |
| [H048](#h048) | 3283-3289 | 3270-3276 | prose, notation or text-conversion cleanup; inspect both sides |
| [H049](#h049) | 3296-3325 | 3283-3312 | status, source locator or provenance prose |
| [H050](#h050) | 3335-3381 | 3322-3368 | status, source locator or provenance prose |
| [H051](#h051) | 3385-3404 | 3372-3391 | star-subscript spelling and surrounding prose; same mathematical symbol |
| [H052](#h052) | 3413-3429 | 3400-3416 | status, source locator or provenance prose |
| [H053](#h053) | 3437-3453 | 3424-3440 | whitespace only |
| [H054](#h054) | 3460-3466 | 3447-3453 | whitespace only |
| [H055](#h055) | 3473-3481 | 3460-3468 | whitespace only |
| [H056](#h056) | 3505-3512 | 3492-3499 | whitespace only |
| [H057](#h057) | 3521-3528 | 3508-3515 | whitespace only |
| [H058](#h058) | 3540-3555 | 3527-3542 | whitespace only |
| [H059](#h059) | 3568-3576 | 3555-3563 | whitespace only |
| [H060](#h060) | 3580-3586 | 3567-3573 | whitespace only |
| [H061](#h061) | 3629-3637 | 3616-3624 | whitespace only |
| [H062](#h062) | 3639-3645 | 3626-3632 | whitespace only |
| [H063](#h063) | 3675-3689 | 3662-3676 | whitespace only |
| [H064](#h064) | 3701-3707 | 3688-3694 | whitespace only |
| [H065](#h065) | 3710-3741 | 3697-3728 | status, source locator or provenance prose |
| [H066](#h066) | 4321-4342 | 4308-4329 | status, source locator or provenance prose |
| [H067](#h067) | 4378-4392 | 4365-4379 | status, source locator or provenance prose |
| [H068](#h068) | 4397-4425 | 4384-4412 | status, source locator or provenance prose |
| [H069](#h069) | 4442-4451 | 4429-4438 | journal edition, locator or associated scope wording |
| [H070](#h070) | 4453-4707 | 4440-4684 | status, source locator or provenance prose |
| [H071](#h071) | 4714-4731 | 4691-4708 | whitespace only |
| [H072](#h072) | 4740-4746 | 4717-4723 | whitespace only |
| [H073](#h073) | 4780-4821 | 4757-4798 | status, source locator or provenance prose |
| [H074](#h074) | 5079-5086 | 5056-5063 | status, source locator or provenance prose |
| [H075](#h075) | 5088-5094 | 5065-5071 | status, source locator or provenance prose |
| [H076](#h076) | 5096-5102 | 5073-5079 | status, source locator or provenance prose |
| [H077](#h077) | 5104-5110 | 5081-5087 | status, source locator or provenance prose |
| [H078](#h078) | 5112-5118 | 5089-5095 | status, source locator or provenance prose |
| [H079](#h079) | 5120-5126 | 5097-5103 | status, source locator or provenance prose |
| [H080](#h080) | 5128-5134 | 5105-5111 | status, source locator or provenance prose |
| [H081](#h081) | 5136-5142 | 5113-5119 | status, source locator or provenance prose |
| [H082](#h082) | 5144-5158 | 5121-5135 | status, source locator or provenance prose |
| [H083](#h083) | 5164-5213 | 5141-5190 | status, source locator or provenance prose |
| [H084](#h084) | 5216-5222 | 5193-5199 | status, source locator or provenance prose |
| [H085](#h085) | 5229-5235 | 5206-5212 | status, source locator or provenance prose |
| [H086](#h086) | 5238-5244 | 5215-5221 | status, source locator or provenance prose |
| [H087](#h087) | 5289-5299 | 5266-5276 | whitespace only |
| [H088](#h088) | 5341-5348 | 5318-5325 | status, source locator or provenance prose |
| [H089](#h089) | 13565-13571 | 13542-13548 | status, source locator or provenance prose |
| [H090](#h090) | 14669-14675 | 14646-14652 | status, source locator or provenance prose |
| [H091](#h091) | 15430-15436 | 15407-15413 | status, source locator or provenance prose |
| [H092](#h092) | 18135-18144 | 18112-18121 | status, source locator or provenance prose |
| [H093](#h093) | 18662-18668 | 18639-18645 | status, source locator or provenance prose |
| [H094](#h094) | 19195-19201 | 19172-19178 | prose, notation or text-conversion cleanup; inspect both sides |
| [H095](#h095) | 26655-26663 | 26632-26640 | status, source locator or provenance prose |
| [H096](#h096) | 27760-27770 | 27737-27747 | whitespace only |
| [H097](#h097) | 27773-27780 | 27750-27757 | whitespace only |
| [H098](#h098) | 27784-27798 | 27761-27775 | whitespace only |
| [H099](#h099) | 27895-27901 | 27872-27878 | whitespace only |
| [H100](#h100) | 27990-28000 | 27967-27977 | whitespace only |
| [H101](#h101) | 28018-28028 | 27995-28005 | whitespace only |
| [H102](#h102) | 28035-28041 | 28012-28018 | whitespace only |
| [H103](#h103) | 28046-28052 | 28023-28029 | whitespace only |
| [H104](#h104) | 28072-28104 | 28049-28081 | whitespace only |
| [H105](#h105) | 28154-28160 | 28131-28137 | whitespace only |
| [H106](#h106) | 28197-28227 | 28174-28204 | whitespace only |
| [H107](#h107) | 28321-28334 | 28298-28311 | whitespace only |
| [H108](#h108) | 28343-28351 | 28320-28328 | whitespace only |
| [H109](#h109) | 28398-28411 | 28375-28388 | status, source locator or provenance prose |
| [H110](#h110) | 28438-28447 | 28415-28424 | whitespace only |
| [H111](#h111) | 28529-28535 | 28506-28512 | status, source locator or provenance prose |
| [H112](#h112) | 28655-28661 | 28632-28638 | whitespace only |
| [H113](#h113) | 28694-28714 | 28671-28691 | whitespace only |
| [H114](#h114) | 28721-28733 | 28698-28710 | whitespace only |
| [H115](#h115) | 28750-28756 | 28727-28733 | whitespace only |
| [H116](#h116) | 28853-28859 | 28830-28836 | whitespace only |
| [H117](#h117) | 28869-28875 | 28846-28852 | whitespace only |
| [H118](#h118) | 28891-28898 | 28868-28875 | whitespace only |
| [H119](#h119) | 28902-28908 | 28879-28885 | whitespace only |
| [H120](#h120) | 28914-28920 | 28891-28897 | whitespace only |
| [H121](#h121) | 29099-29118 | 29076-29095 | whitespace only |
| [H122](#h122) | 29127-29133 | 29104-29110 | whitespace only |
| [H123](#h123) | 29140-29146 | 29117-29123 | whitespace only |
| [H124](#h124) | 29150-29166 | 29127-29143 | whitespace only |
| [H125](#h125) | 29245-29275 | 29222-29252 | whitespace only |
| [H126](#h126) | 29277-29283 | 29254-29260 | whitespace only |
| [H127](#h127) | 29402-29426 | 29379-29403 | whitespace only |
| [H128](#h128) | 29440-29446 | 29417-29423 | whitespace only |
| [H129](#h129) | 29470-29476 | 29447-29453 | whitespace only |
| [H130](#h130) | 29478-29484 | 29455-29461 | whitespace only |
| [H131](#h131) | 29560-29565 | 29537-29545 | prose, notation or text-conversion cleanup; inspect both sides |
| [H132](#h132) | 29598-29622 | 29578-29593 | journal edition, locator or associated scope wording |
| [H133](#h133) | 29626-29632 | 29597-29603 | journal edition, locator or associated scope wording |
| [H134](#h134) | 29641-29647 | 29612-29618 | journal edition, locator or associated scope wording |
| [H135](#h135) | 29668-29674 | 29639-29645 | journal edition, locator or associated scope wording |
| [H136](#h136) | 29678-29684 | 29649-29655 | journal edition, locator or associated scope wording |
| [H137](#h137) | 29835-29845 | 29806-29816 | journal edition, locator or associated scope wording |
| [H138](#h138) | 30008-30015 | 29979-29985 | prose, notation or text-conversion cleanup; inspect both sides |
| [H139](#h139) | 33002-33009 | 32972-32979 | whitespace only |
| [H140](#h140) | 33670-33676 | 33640-33646 | status, source locator or provenance prose |
| [H141](#h141) | 33679-33685 | 33649-33655 | status, source locator or provenance prose |
| [H142](#h142) | 33981-33987 | 33951-33957 | whitespace only |
| [H143](#h143) | 37542-37548 | 37512-37518 | whitespace only |
| [H144](#h144) | 37551-37573 | 37521-37543 | whitespace only |
| [H145](#h145) | 37575-37586 | 37545-37556 | whitespace only |
| [H146](#h146) | 37605-37617 | 37575-37587 | whitespace only |
| [H147](#h147) | 37636-37642 | 37606-37612 | whitespace only |
| [H148](#h148) | 37648-37656 | 37618-37626 | whitespace only |
| [H149](#h149) | 37750-37756 | 37720-37726 | whitespace only |
| [H150](#h150) | 37760-37766 | 37730-37736 | whitespace only |
| [H151](#h151) | 37768-37776 | 37738-37746 | whitespace only |
| [H152](#h152) | 37778-37796 | 37748-37766 | whitespace only |
| [H153](#h153) | 37802-37808 | 37772-37778 | whitespace only |
| [H154](#h154) | 37820-37830 | 37790-37800 | whitespace only |
| [H155](#h155) | 37837-37850 | 37807-37820 | whitespace only |
| [H156](#h156) | 37856-37870 | 37826-37840 | whitespace only |
| [H157](#h157) | 37963-37971 | 37933-37941 | whitespace only |
| [H158](#h158) | 37975-37981 | 37945-37951 | whitespace only |
| [H159](#h159) | 37984-37991 | 37954-37961 | whitespace only |
| [H160](#h160) | 39536-39555 | 39506-39525 | whitespace only |
| [H161](#h161) | 39689-39695 | 39659-39665 | status, source locator or provenance prose |
| [H162](#h162) | 39966-39972 | 39936-39942 | status, source locator or provenance prose |
| [H163](#h163) | 40146-40166 | 40116-40134 | status, source locator or provenance prose |
| [H164](#h164) | 40169-40175 | 40137-40143 | status, source locator or provenance prose |
| [H165](#h165) | 40282-40291 | 40250-40257 | prose, notation or text-conversion cleanup; inspect both sides |
| [H166](#h166) | 40305-40313 | 40271-40279 | status, source locator or provenance prose |

### H001

Class: status, source locator or provenance prose. Base 1-5; candidate 1-5.

```diff
@@ -1,5 +1,5 @@
 \PassOptionsToPackage{hypertexnames=false}{hyperref}
-% Height-source replacement: see work/remove-vkk-20261104/REPORT.md for scope and review status.
+% Historical height-source replacement; source identity and limitations are retained in the companion status record.
 \documentclass[11pt]{article}
 \usepackage[T1]{fontenc}
 \usepackage[utf8]{inputenc}
```

### H002

Class: status, source locator or provenance prose. Base 76-83; candidate 76-82.

```diff
@@ -76,8 +76,7 @@
 The inherited elliptic, scalar, prime-selection, pole and aggregate arguments remain.
 The exact coefficient calculation gives $2919$ coordinate monomials, $2920$
 parameter terms and height $149^{4N+2}+1$ for $N\ge53$; this is only a
-coefficient threshold.  This assembled manuscript is an author proposal for
-fresh review and does not itself confer Protocol~D or release acceptance.
+coefficient threshold.
 \end{abstract}
 \tableofcontents
 \clearpage
```

### H003

Class: status, source locator or provenance prose. Base 125-130; candidate 124-133.

```diff
@@ -125,6 +124,10 @@
 freeze; they do not assert that no later analytic correction is incorporated
 here.  Version~16 is the upstream foundation's edition, not a new numbered
 release of the proposed $214$ research manuscript.
+
+The separate \href{https://github.com/elliotglazer/diophantine-z-q/blob/main/docs/research-review/version18-cleanup-status.md}{Version~18 source and incorporation record}
+preserves outstanding incorporation obligations and review limitations
+for this edition.

 \paragraph{Navigation to current foundation passages.}
 The retained source has direct links to the
```

### H004

Class: status, source locator or provenance prose. Base 184-200; candidate 187-198.

```diff
@@ -184,17 +187,12 @@
 as provenance; the current character and conductor applications are M1 and
 M5 of Section~\ref{q214:modularity}.

-\paragraph{Attribution and review boundary.}
+\paragraph{Attribution.}
 This edition serializes the public $214$ proposal and its attributed internal
 model contributions under Elliot Glazer's direction.  The retained Version~16
 body records its historical authorship and acknowledgements, including
 Jos\'e Brox's starting construction and Gabriel Conant's contributions.
 The present assembly and typesetting were prepared by a Sol~6.1 author agent.
-Source statements concerning earlier inspection, pending status or historical
-acceptance remain dated evidence.  They are not new acceptance records for
-this exact TeX/PDF.  The independently authored public review overlay and
-protected controller decision govern any later adoption.  Internal model
-review is distinct from human peer review and formal verification.
 The bibliography and source catalogue identify external works without
 redistributing their full PDFs.  Exact source hashes, line coverage and
 typesetting transformations are recorded in \nolinkurl{SOURCE_SPANS.json}.
```

### H005

Class: status, source locator or provenance prose. Base 1996-2009; candidate 1994-2007.

```diff
@@ -1996,14 +1994,14 @@
 \section{The mathematical foundation and the 214 consumers}\label{q214:foundation-transition}
 \noindent\textit{Source: }\nolinkurl{research/quartic214-manuscript-review/FOUNDATION_TRANSITION.md}.\par

-\begin{quote}\footnotesize Author: model task \nolinkurl{/root/q214_tex_coverage}, 12 November 2026. This is a new source-to-consumer comparison for independent review. It supplies no independent acceptance. The upstream Version~16 foundation is \nolinkurl{manuscripts/quartic_v16.tex}, SHA-256 \nolinkurl{aeb2b6a42a03943d7f8c46682389c8da693d2903ba92ccc164bbbd236451de74}. The earlier \(V_{15}\) source, SHA-256 \nolinkurl{44ba3a8ec8521c29b81b26cfb9981cd6d5f3c76d54e7782438614842edb52c74}, remains immutable historical evidence.\end{quote}
+\begin{quote}\footnotesize The upstream Version~16 foundation is \nolinkurl{manuscripts/quartic_v16.tex}, SHA-256 \nolinkurl{aeb2b6a42a03943d7f8c46682389c8da693d2903ba92ccc164bbbd236451de74}. The earlier \(V_{15}\) source, SHA-256 \nolinkurl{44ba3a8ec8521c29b81b26cfb9981cd6d5f3c76d54e7782438614842edb52c74}, remains immutable historical evidence.\end{quote}

-\subsection{Current source rule}
+\subsection{Mathematical foundation}

 The operative foundation is the Version~16 text inherited in Part~II,
-with the Version~18 inverse-theorem replacement in Section~\ref{v15:gi-full}. The \(V_{15}\) byte-identity statements in uniform-existence \(P_{02}\) and source-carry \(C_{01}\) describe the earlier frozen packet. They are superseded as statements of the \textbf{current receiving source}. Their hashes, earlier arguments and review limits remain historical evidence; no old approval is transferred automatically. The current source supplies the retained rank, restricted-converse, Kato, GI, Gaussian-prime, scalar and pole interfaces, with the source applications compared below. The 214 polynomial, its raw224 branch, the new local factors, the uniform ineffective threshold and the product averaging route are unchanged by this substitution.
+with the Version~18 inverse-theorem replacement in Section~\ref{v15:gi-full}. The \(V_{15}\) byte-identity statements in uniform-existence \(P_{02}\) and source-carry \(C_{01}\) describe the earlier frozen packet. They are superseded as statements of the \textbf{current receiving source}. Their hashes and earlier arguments remain historical evidence. The current source supplies the retained rank, restricted-converse, Kato, GI, Gaussian-prime, scalar and pole interfaces, with the source applications compared below. The 214 polynomial, its raw 224 branch, the new local factors, the uniform ineffective threshold and the product averaging route are unchanged by this substitution.

-The historical Version~16 comparison used the actual complete normalized V15-to-current-V16 difference, the actual Fable audit passages concerning horizontal normalization and the four follow-ups, the current \(V_{16}\) passages themselves, and the actual 214 consumers. It follows both the editorial amendment and the later Tao--Ziegler precision amendment: the intermediate \nolinkurl{2f729...} and \nolinkurl{a9cb...} \(V_{16}\) hashes are not the final receiving source. Publication and pre-existing source-review scopes remain those recorded with the current foundation. This author does not claim a new reading of every external publication or a recursive reproof of the entire foundation.
+The historical comparison and its intermediate source hashes are recorded separately. Publication-version and source-application qualifications remain those recorded with the current foundation.

 \subsection{The finite-family inverse theorem}

```

### H006

Class: status, source locator or provenance prose. Base 2060-2086; candidate 2058-2081.

```diff
@@ -2060,27 +2058,24 @@

 \subsection{Height citations and the same-field product route}

-\(V_{16}\) lines30658--30683 now cite Gaudron--Remond, \emph{Theoreme des periodes et degres minimaux d'isogenies}, Commentarii Mathematici Helvetici89 (2014),343--403, Section2.3 and Corollary8.4, DOI10.4171/CMH/322. The earlier Duke paper remains a different source for its own Theorem1.4/Section9 uses. The CMH source supplies the original-normalization lower bound and the one-sided half-log-degree height change at the corrected surface consumer.
+\(V_{16}\) lines 30658--30683 now cite Gaudron--Remond, \emph{Theoreme des periodes et degres minimaux d'isogenies}, Commentarii Mathematici Helvetici 89 (2014),343--403, Section 2.3 and Corollary 8.4, DOI 10.4171/CMH/322. The earlier Duke paper remains a different source for its own Theorem 1.4/Section 9 uses. The CMH source supplies the original-normalization lower bound and the one-sided half-log-degree height change at the corrected surface consumer.

-The actual 214 primary-source-bridges already identifies that CMH article and its normalization conversion. The operative height-averaging proof applies the published GR2023 product construction over the actual L-prime, chooses \(r\) separate simple factors in the actual \(A_{a}-\text{isogeny}\) class, and uses a dimension-two isogeny from the selected \(C_{i}\) to \(A_{a}\) over that same field. All \(r\) occurrences, negative individual heights and a zero-dimensional complement remain covered. Neither this citation correction nor the \(V_{16}\) single-surface lemma substitutes an evaluation-splitting field for L-prime, replaces \(r\) by a set of distinct isogeny classes, or removes the published product supplier's indirect Remond dependencies. The exact received inequality is still H3.1, consumed with H2's multiplicity saving by \(H_{4}\). The historical quotient \(H_{3}\) remains superseded in the 214 application.
+The actual 214 primary-source-bridges already identifies that CMH article and its normalization conversion. The operative height-averaging proof applies the published GR2023 product construction over the actual \(L'\), chooses \(r\) separate simple factors in the actual \(A_{a}-\text{isogeny}\) class, and uses a dimension-two isogeny from the selected \(C_{i}\) to \(A_{a}\) over that same field. All \(r\) occurrences, negative individual heights and a zero-dimensional complement remain covered. Neither this citation correction nor the \(V_{16}\) single-surface lemma substitutes an evaluation-splitting field for \(L'\), replaces \(r\) by a set of distinct isogeny classes, or removes the published product supplier's indirect Remond dependencies. The exact received inequality is still H3.1, consumed with H2's multiplicity saving by \(H_{4}\). The historical quotient \(H_{3}\) remains superseded in the 214 application.

-\subsection{Related uses and remaining acceptance}
+\subsection{Related applications}

 For the historical Version~16 transition, the complete normalized source difference contained the GI insertion, fixed-lift division, Tao--Ziegler adaptation/precision wording, the two CMH citation changes, the added bibliography entry, publication metadata and the restored AI usage attribution. That historical comparison does not describe the Version~18 inverse-theorem replacement in Section~\ref{v15:gi-full}. The bounded related-use comparison covers source-carry C01/C08--C10/C12--C13, uniform-existence P02/P08--P10/P15--P20, the current product averaging and primary-source height bridges, and the explicit scope notices before the historical packet. Old \(V_{15}\) line numbers in the retained packet are provenance locators; the historical source map and that transition identify the corresponding receiving passages at that time. The historical source texts and fourteen original public contracts are not rewritten.

-The Fable Bogolyubov-numbering concern is expressly withdrawn in its follow-up after comparison with the published numbering; no manuscript repair is imported for that item. Its audit's other unexamined portions remain review-scope limitations, without inventing new objections or treating them as verification. The original audit and its \(V_{16}\) findings remain preserved in their versioned locations.
-
-This transition is a changed foundation application. A fresh non-author must assess its exact source passages, the corrected connections, the actual 214 consumers and the assembled TeX/PDF. Old component or \(V_{16}\) acceptance is evidence at its own bound scope, not automatic acceptance of this new receiving application. Until that decision and the matching release binding exist, assembled-proof and record-release acceptance remain pending.
 \clearpage
 % Source: research/quartic214/PROOF.md
 \section{Assembly of the selected 214 construction}\label{q214:assembly}
 \noindent\textit{Source: }\nolinkurl{research/quartic214/PROOF.md}.\par

-This is an author assembly for fresh public review. The construction and all source-to-consumer transitions below are proposed together. Historical source acceptance is separate from acceptance of this public adaptation. \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/SOURCE_PATH_MAP.json}{\nolinkurl{SOURCE_PATH_MAP.json}} records exact original source hashes, selected ranges, adaptations, and reused public paths. It deliberately contains no generated reviewer approval.
+\href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/SOURCE_PATH_MAP.json}{\nolinkurl{SOURCE_PATH_MAP.json}} records exact original source hashes, selected ranges, adaptations, and reused public paths.

 \subsection{Exact family and domains}

-Put \(A_{N}=149^{2N+1}\). Starting with the public \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/version15/quartics/quartic-222/provenance/shared-T-redundancy224-006/candidate224-ir.json}{raw224 predecessor}, \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/construction/build.py}{the builder} removes ten fourth-power cache coordinates and their ten defining rows, reuses six existing power slots for inverse weights, and changes twenty factor component rows. The result has 214 coordinates and 188 primitive integral quadratic rows \(r_{i}\). Define \(P_{N}=\sum _{i=1}^{188}\) \(r_{i}^{2}\) after substituting the fixed coefficient \(A_{N}\). Over \(Q\), \(P_{N}=0\) is equivalent to every \(r_{i}=0\).
+Put \(A_{N}=149^{2N+1}\). Starting with the public \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/version15/quartics/quartic-222/provenance/shared-T-redundancy224-006/candidate224-ir.json}{raw 224 predecessor}, \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/construction/build.py}{the builder} removes ten fourth-power cache coordinates and their ten defining rows, reuses six existing power slots for inverse weights, and changes twenty factor component rows. The result has 214 coordinates and 188 primitive integral quadratic rows \(r_{i}\). Define \(P_{N}=\sum _{i=1}^{188}\) \(r_{i}^{2}\) after substituting the fixed coefficient \(A_{N}\). Over \(Q\), \(P_{N}=0\) is equivalent to every \(r_{i}=0\).

 The exact \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/construction/check_exact.py}{Laurent proof checker} reconstructs the deleted coordinates, checks the six inverse-power definitions, and compares all twenty factor components to the changed physical factor system up to a nonzero rational normalization and \(q^{4}\). It compares all 162 untouched rows. The factors have exponents (5,2,4), with exponent 3 in the special input term. They are \textbf{new arithmetic factors}; an old factor-exponent conclusion is not reused to prove their soundness. The equations \(q\) \(s_{1}=1\), \(s_{2}=s_{1}^{2}\), \(s_{4}=s_{2}^{2}\) require \(q\ne 0\). Completeness constructs witnesses in that domain. No bijection with the discarded \(q=0\) witness stratum is claimed.

```

### H007

Class: status, source locator or provenance prose. Base 2095-2111; candidate 2090-2106.

```diff
@@ -2095,17 +2090,17 @@
 Application & Available result, constructed input, exact bridge and consumer\\
 \midrule
 \endhead
-Physical recovery and reciprocal clearing & \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/proofs/existence.md}{\nolinkurl{existence.md}}, ``Algebraic transport'', reconstructs the actual raw224 reference, root and scale objects using the predecessor's inverse maps. Forced-149 valuations recover \(w\) and the shared alternate ratio before division. Zero components and zero test numerators are retained. The full row identities are checked by the independent Laurent implementation.\\
+Physical recovery and reciprocal clearing & \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/proofs/existence.md}{\nolinkurl{existence.md}}, ``Algebraic transport'', reconstructs the actual raw 224 reference, root and scale objects using the predecessor's inverse maps. Forced-149 valuations recover \(w\) and the shared alternate ratio before division. Zero components and zero test numerators are retained. The full row identities are checked by the independent Laurent implementation.\\
 Changed local extraction & \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/proofs/uniform-existence.md}{\nolinkurl{uniform-existence.md}} P04--P07 applies the valuation-residue separation to the actual five changed factors at every consumed split or inert place, with arbitrary finite test valuations and zero tests. The trace/pole input is reconstructed literally. Positive reciprocal valuations precede logarithmic integrality. The outputs are the same integer residuals \(M_{j}^{3}\mid \Delta \) and \(M_{j}\mid J\), separately for each scale, with no extra scalar factor.\\
 Full-family geometric support & \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/proofs/geometry-carry.md}{\nolinkurl{geometry-carry.md}} G1--G4 and \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/proofs/provider-scope-carry.md}{\nolinkurl{provider-scope-carry.md}} P1--P4 identify the actual public \(D_{210}\) cover, its field and Hom objects, original metric and CM branch. Its \(S_{10}\) bridge covers all primitive rational pairs, including the infinity contact, deep even contacts and \(M=1\). The ten determinant values only prove the finite support calculation; the public geometric proof supplies the actual cover and tame charts.\\
 Original modular realization and conductor & \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/proofs/modularity.md}{\nolinkurl{modularity.md}} M1--M6 constructs the controlled cochain and the actual original representations, checks the published modularity hypotheses at 5, absorbs the finite twist into the final primitive weight-two form, compares the same form at 3, and covers every residue prime by the pair \{5,3\}. \(M_{5}\) preserves inertia and monodromy in the level comparison and gives \(N_{\text{level}}\le C_{N}\) \(R^{2}\), \(\operatorname{rad}(N_{\text{level}})\mid R\). Its field \(L'\) is distinct from coefficient and evaluation-splitting fields.\\
 Modular-Jacobian height & \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/proofs/height-evaluation.md}{\nolinkurl{height-evaluation.md}}, \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/proofs/height-different.md}{\nolinkurl{height-different.md}}, and \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/proofs/height-metric.md}{\nolinkurl{height-metric.md}} prove the integral trace-dual, complete discriminant and metric links. \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/proofs/height-assembly.md}{\nolinkurl{height-assembly.md}} A--D joins the same curve \(X_{1}(N_{\text{level}})/\operatorname{ker}\) \(\epsilon \), order, lattice, trace, metric and all fibre points to H0.3. The auxiliary evaluation field cancels in normalized height; it does not replace \(L'\).\\
-Multiplicity, averaging and \(H_{4}\) & \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/proofs/height-supplier.md}{\nolinkurl{height-supplier.md}} H1--H2 constructs the full coefficient-conjugate multiplicity over \(L'\). \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/proofs/primary-source-bridges.md}{\nolinkurl{primary-source-bridges.md}} pins the Faltings, Poincaré, Fricke and lower-height applications. \textbf{The current \(H_{3}\) application is \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/proofs/height-averaging.md}{\nolinkurl{height-averaging.md}}:} use the published product construction over \(L'\), select \(r\) separate simple factors in the actual \(A_{a}-\text{isogeny}\) class, and apply a dimension-two isogeny \(C_{i}\to A_{a}\). It supplies exactly H3.1 for \(H_{4}\). The historical quotient route retained in \nolinkurl{height-supplier.md} \(H_{3}\) is superseded in this application. \(H_{4}\) proves \(h(u)<C_{2}\) \(M_{S_{10}}(u)^{2103/1024}\) for every allowed rational \(u\), including CM and radical-one cases; its isolated rational certificate changes no row.\\
-Source theorem carry & \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/proofs/source-carry.md}{\nolinkurl{source-carry.md}} C01--C13 compares the exact public manuscript's rank, RC, Kato full-index/limiting-class, GI, Gaussian prime, scalar and pole statements with their actual 214 consumers. It does not import the final paired-root/trace-quotient reductions into this branch. Public review evidence is historical scope evidence, not a replacement for these statements and maps.\\
+Multiplicity, averaging and \(H_{4}\) & \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/proofs/height-supplier.md}{\nolinkurl{height-supplier.md}} H1--H2 constructs the full coefficient-conjugate multiplicity over \(L'\). \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/proofs/primary-source-bridges.md}{\nolinkurl{primary-source-bridges.md}} pins the Faltings, Poincar\'e, Fricke and lower-height applications. \textbf{The current \(H_{3}\) application is \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/proofs/height-averaging.md}{\nolinkurl{height-averaging.md}}:} use the published product construction over \(L'\), select \(r\) separate simple factors in the actual \(A_{a}-\text{isogeny}\) class, and apply a dimension-two isogeny \(C_{i}\to A_{a}\). It supplies exactly H3.1 for \(H_{4}\). The historical quotient route retained in \nolinkurl{height-supplier.md} \(H_{3}\) is superseded in this application. \(H_{4}\) proves \(h(u)<C_{2}\) \(M_{S_{10}}(u)^{2103/1024}\) for every allowed rational \(u\), including CM and radical-one cases; its isolated rational certificate changes no row.\\
+Source theorem carry & \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/proofs/source-carry.md}{\nolinkurl{source-carry.md}} C01--C13 compares the exact public manuscript's rank, RC, Kato full-index/limiting-class, GI, Gaussian prime, scalar and pole statements with their actual 214 consumers. It does not import the final paired-root/trace-quotient reductions into this branch.\\
 \bottomrule
 \end{longtable}

-The named source details are openly readable in the linked proofs and existing public manuscript. Selected older private proof fragments are in \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/sources/}{sources/}. Published works are identified by edition, URL, hash and theorem/page in \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/PRIMARY_SOURCES.json}{\nolinkurl{PRIMARY_SOURCES.json}}, rather than republished in full. The source metadata describes previous actual inspections; the present porter does not claim to have repeated all those primary-source readings.
+The named source details are openly readable in the linked proofs and existing public manuscript. Selected older private proof fragments are in \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/sources/}{sources/}. Published works are identified by edition, URL, hash and theorem/page in \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/PRIMARY_SOURCES.json}{\nolinkurl{PRIMARY_SOURCES.json}}, rather than republished in full.

 \subsection{Soundness with one fixed threshold}

```

### H008

Class: status, source locator or provenance prose. Base 2125-2167; candidate 2120-2162.

```diff
@@ -2125,43 +2120,43 @@

 The labels, fixed-data prime sets, moduli, slope and final witnesses may depend on (N,x). Their existence imposes no further lower bound on \(N\). Reconstructing the removed cache values and applying the exact row identities gives a zero of \(P_{N}\). With the fixed soundness threshold \(N_{S}\), take \(N_{0}=\operatorname{max}(N_{S},N_{C})\). This proves the asserted \(\exists N_{0}\forall N\ge N_{0}\forall x\) form relative to the exact retained source theorems and the applications proposed here. \(N_{0}\) remains ineffective.

-\subsection{Review boundary}
+\subsection{Effectivity and finite checks}

-The \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/contracts/INDEX.json}{public application contracts} retain the original authors' nine obligations with new whole-file and verified public passage bindings. Original private contract hashes are provenance; old private line pins and approvals do not become current public pins or approvals. Required internal sources resolve to public files, and external primary sources retain edition, URL and hash metadata.
+The \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/contracts/INDEX.json}{public application contracts} retain the original authors' nine obligations with new whole-file and verified public passage bindings. Original private contract hashes and line pins are historical provenance. Required internal sources resolve to public files, and external primary sources retain edition, URL and hash metadata.

-All current applications above require review of this exact public serialization and its dependencies. Prior scoped acceptance does not independently accept this assembly, establish a numerical \(N_{0}\), or certify a full example witness tuple. The isolated numeric and algebra checks establish only their declared finite conclusions. The public Astra/controller acceptance requirement remains in force.
+The defining threshold remains ineffective, and no full numerical witness tuple is supplied. The isolated numeric and algebra checks establish only their declared finite conclusions; they do not certify the retained arithmetic premises.
 \clearpage
 % Source: research/quartic214/proofs/existence.md
 \section{Reciprocal clearing on the 224-coordinate predecessor: 214 and 218}\label{q214:existence}
 \noindent\textit{Source: }\nolinkurl{research/quartic214/proofs/existence.md}.\par

-\begin{quote}\footnotesize Author: /root, integrating the attributed existence222 contribution. This is a new application on the literal public raw224 rows, not adoption of an earlier verdict. All source files and the author construction are bound by the author manifest for non-author review. This section is conditional on the retained elliptic, scalar, prime-selection, pole and aggregate-trace inputs of the frozen Version15 source. Its defining threshold remains ineffective. The 214 conclusion additionally uses the newly proved quadratic supplier in the sibling height packet; that theorem's inherited assumptions remain explicit.\end{quote}
+\begin{quote}\footnotesize This section is conditional on the retained elliptic, scalar, prime-selection, pole and aggregate-trace inputs of the frozen Version 15 source. Its defining threshold remains ineffective. The 214 conclusion additionally uses the newly proved quadratic supplier in the sibling height packet; that theorem's inherited assumptions remain explicit.\end{quote}

 \subsection{Statement and exact objects}

-Let \(A_{N}=149^{2N+1}\), \(N\ge 1\). The portable builder starts with \nolinkurl{research/version15/quartics/quartic-222/provenance/shared-T-redundancy224-006/candidate224-ir.json}, the public shared-T-redundancy224-006 stage (224 variables,198 primitive quadratic rows), before the paired-root and trace-quotient steps. It produces a 214-variable family with188 rows and a 218-variable control with192 rows. Every polynomial is the sum of the squares of its displayed primitive integral rows. The complete tables and symbolic row identities are executable evidence, not a substitute for the arithmetic argument below.
+Let \(A_{N}=149^{2N+1}\), \(N\ge 1\). The portable builder starts with \nolinkurl{research/version15/quartics/quartic-222/provenance/shared-T-redundancy224-006/candidate224-ir.json}, the public shared-T-redundancy224-006 stage (224 variables,198 primitive quadratic rows), before the paired-root and trace-quotient steps. It produces a 214-variable family with 188 rows and a 218-variable control with 192 rows. Every polynomial is the sum of the squares of its displayed primitive integral rows. The complete tables and symbolic row identities are executable evidence, not a substitute for the arithmetic argument below.

-For each family there is a fixed \(N_{0}\) such that all \(N\ge N_{0}\) define \(Z\) by rational projection of input coordinate1. This is the conditional conclusion established here. Its proof does not give an effective \(N_{0}\). The coefficient height \(\text{equals}149^{4N+2}+1\) for \(N\ge 53;53\) is solely a coefficient threshold. The parameter \(A_{N}\) is never a quantified variable.
+For each family there is a fixed \(N_{0}\) such that all \(N\ge N_{0}\) define \(Z\) by rational projection of input coordinate 1. This is the conditional conclusion established here. Its proof does not give an effective \(N_{0}\). The coefficient height equals \(149^{4N+2}+1\) for \(N\ge 53\); \(53\) is solely a coefficient threshold. The parameter \(A_{N}\) is never a quantified variable.

-Use exactly \(K=Q(\sqrt{2})\), \(d=3-\sqrt{2}\), \(D=d^{2}\), \(E:y^{2}=x^{3}-Dx\) and the generator \(P\) in the frozen source. The raw224 component bases, including the nonstandard \(W_{0}\) basis, are retained by literal rational component rows. The two actual weights are raw224 coordinates87 and102. The physical arguments are \(\lambda \) and \(T*\lambda \), with \(T=(1/4)\operatorname{Tr}(\sum _{i=1}^{4} x(Q_{i}))>0\). Reciprocal-scale and scalar-R rescalings are interpreted using their proved inverse maps, not by identifying a rescaled coordinate with an unscaled field value.
+Use exactly \(K=Q(\sqrt{2})\), \(d=3-\sqrt{2}\), \(D=d^{2}\), \(E:y^{2}=x^{3}-Dx\) and the generator \(P\) in the frozen source. The raw 224 component bases, including the nonstandard \(W_{0}\) basis, are retained by literal rational component rows. The two actual weights are raw 224 coordinates 87 and 102. The physical arguments are \(\lambda \) and \(T\cdot \lambda \), with \(T=(1/4)\operatorname{Tr}(\sum _{i=1}^{4} x(Q_{i}))>0\). Reciprocal-scale and scalar-R rescalings are interpreted using their proved inverse maps, not by identifying a rescaled coordinate with an unscaled field value.

-The exact ten-contact set is \(\Theta \) union(2-Theta), \(\Theta =\{0,-1/2,-1,1/2399,-32/407\}\); \(\Sigma \) consists of \(\text{primes}\le 76176\) and2029147. Write \(F_{2}\) for its monic polynomial, \(\delta =t-1\), \(R=F_{2}(t)/\delta ^{10}\) and \(q=\delta ^{10}/F_{2}(t)-1\) on \(\delta \ne 0\). The literal contact equation excludes every contact since \(F_{2}(1)\ne 0\). At \(\delta =0\) it forces \(q=-1\); the comparison radical is1 and no division by \(\delta \) is made. New inverse equations enforce \(q\ne 0\). They are allowed to remove some irrelevant old witnesses; no all-witness bijection with unrestricted raw224 is claimed.
+The exact ten-contact set is \(\Theta \cup(2-\Theta)\), \(\Theta =\{0,-1/2,-1,1/2399,-32/407\}\); \(\Sigma \) consists of \(\text{primes}\le 76176\) and 2029147. Write \(F_{2}\) for its monic polynomial, \(\delta =t-1\), \(R=F_{2}(t)/\delta ^{10}\) and \(q=\delta ^{10}/F_{2}(t)-1\) on \(\delta \ne 0\). The literal contact equation excludes every contact since \(F_{2}(1)\ne 0\). At \(\delta =0\) it forces \(q=-1\); the comparison radical is 1 and no division by \(\delta \) is made. New inverse equations enforce \(q\ne 0\). They are allowed to remove some irrelevant old witnesses; no all-witness bijection with unrestricted raw 224 is claimed.

 \subsection{Algebraic transport, domains and source-interface recovery}

-The removed coordinates are raw224 IDs23,24,29,30,33,34,37,38,133,134: the two rational components of each of five V-side fourth powers. Their defining equations solve them as explicit quadratic polynomials in retained reciprocal-abscissa-square coordinates. All other occurrences are in the twenty factor component rows; the symbolic checker verifies this occurrence statement and retains their actual component conventions.
+The removed coordinates are raw 224 IDs 23,24,29,30,33,34,37,38,133,134: the two rational components of each of five V-side fourth powers. Their defining equations solve them as explicit quadratic polynomials in retained reciprocal-abscissa-square coordinates. All other occurrences are in the twenty factor component rows; the symbolic checker verifies this occurrence statement and retains their actual component conventions.

-In each detector reuse three power slots as s1,s2,s4 and impose \(q*s_{1}=1\), \(s_{2}=s_{1}^{2}\), \(s_{4}=s_{2}^{2}\). The214 factors use exponents(5,2,4), with special exponent3 below. Multiplying their defining equations by \(q^{-4}\) makes the old highest powers quadratic expressions in already stored squares. The218 control retains exponents(7,2,4), special exponent1; it also stores \(q_{3}\) and \(s_{3}\), with \(s_{3}=s_{1}*s_{2}\) and \(q_{3}*s_{3}=1\). These equations imply \(q_{3}=q^{3}\) and \(s_{3}=q^{-3}\) without further guards.
+In each detector reuse three power slots as \(s_1,s_2,s_4\) and impose \(q\cdot s_{1}=1\), \(s_{2}=s_{1}^{2}\), \(s_{4}=s_{2}^{2}\). The 214 factors use exponents(5,2,4), with special exponent 3 below. Multiplying their defining equations by \(q^{-4}\) makes the old highest powers quadratic expressions in already stored squares. The 218 control retains exponents(7,2,4), special exponent 1; it also stores \(q_{3}\) and \(s_{3}\), with \(s_{3}=s_{1}\cdot s_{2}\) and \(q_{3}\cdot s_{3}=1\). These equations imply \(q_{3}=q^{3}\) and \(s_{3}=q^{-3}\) without further guards.

-The symbolic Laurent-polynomial checker independently substitutes every eliminated coordinate and every weight, then compares all twenty factor component identities with the appropriate positive or negative constant row multipliers and \(q^{4}\). It compares all162 untouched rows exactly up to their primitive sign convention and verifies all power relations. This is an identity of formal polynomial expressions, not agreement at sample points. For214 the target factor system has the changed exponents; it is not the old order-four system. For218 it is literally the old system on \(q_{0}*q_{1}\ne 0\).
+The symbolic Laurent-polynomial checker independently substitutes every eliminated coordinate and every weight, then compares all twenty factor component identities with the appropriate positive or negative constant row multipliers and \(q^{4}\). It compares all 162 untouched rows exactly up to their primitive sign convention and verifies all power relations. This is an identity of formal polynomial expressions, not agreement at sample points. For 214 the target factor system has the changed exponents; it is not the old order-four system. For 218 it is literally the old system on \(q_{0}\cdot q_{1}\ne 0\).

-Every new rational solution therefore reconstructs the physical scalar/reference/root system by the raw224 inverse maps. The reconstructed deleted fourth-power outputs satisfy their old definitions identically, including \(W_{0}\); \(Q_{5}\) had already been removed in raw224 and has no hidden \(W_{0}\) consumer. Source locations: the public predecessor proof listed in \nolinkurl{SOURCE_PATH_MAP.json,} Version15 \nolinkurl{v222:reference} and its displayed polynomial F/E identities; \nolinkurl{v222:ratio}; \nolinkurl{v15:reductions}. The reference recovery uses Q0,Q1,Q3 to obtain the \(H\) curve and \(f\ne 0\), before interpreting \(w\). The unchanged forced149 scalar argument then gives \(v_{149}(f)=m>0\), \(v_{149}(S)=-m/2\), \(v_{149}(g)=m/2\). The unique lowest \(S\) term in the coefficient of \(w\) in \(Q_{2}\) gives \(w=g^{4}/f^{2}\). The former \(W_{0}\) is simply reconstructed as \(w^{2}\). No factor exponent is used in this chain.
+Every new rational solution therefore reconstructs the physical scalar/reference/root system by the raw 224 inverse maps. The reconstructed deleted fourth-power outputs satisfy their old definitions identically, including \(W_{0}\); \(Q_{5}\) had already been removed in raw 224 and has no hidden \(W_{0}\) consumer. Source locations: the public predecessor proof listed in \nolinkurl{SOURCE_PATH_MAP.json,} Version 15 \nolinkurl{v222:reference} and its displayed polynomial F/E identities; \nolinkurl{v222:ratio}; \nolinkurl{v15:reductions}. The reference recovery uses \(Q_0,Q_1,Q_3\) to obtain the \(H\) curve and \(f\ne 0\), before interpreting \(w\). The unchanged forced 149 scalar argument then gives \(v_{149}(f)=m>0\), \(v_{149}(S)=-m/2\), \(v_{149}(g)=m/2\). The unique lowest \(S\) term in the coefficient of \(w\) in \(Q_{2}\) gives \(w=g^{4}/f^{2}\). The former \(W_{0}\) is simply reconstructed as \(w^{2}\). No factor exponent is used in this chain.

-The shared alternate ratio is recovered from \(D_{r}*T=N_{r}\) with both numerator and denominator having valuation -m/2 at149. Thus \(T\) is nonzero, all four alternate ratios regain their original meanings, and the \(k=0\) and zero-numerator branches are handled by the retained inverse maps. No division by a rational component or test numerator is added. The scalar four-contact normalizer and parity-scalar rows are untouched; the forced149 bound, real and finite scalar preparation, and nonzero integer root labels remain the same. These uses retain their earlier proofs at the exact source locations, rather than being inferred from finite row checks.
+The shared alternate ratio is recovered from \(D_{r}\cdot T=N_{r}\) with both numerator and denominator having valuation -m/2 at 149. Thus \(T\) is nonzero, all four alternate ratios regain their original meanings, and the \(k=0\) and zero-numerator branches are handled by the retained inverse maps. No division by a rational component or test numerator is added. The scalar four-contact normalizer and parity-scalar rows are untouched; the forced 149 bound, real and finite scalar preparation, and nonzero integer root labels remain the same. These uses retain their earlier proofs at the exact source locations, rather than being inferred from finite row checks.

-\subsection{New local factors and soundness for214}
+\subsection{New local factors and soundness for 214}

-At a consumed \(p\) outside \(\Sigma \) the fixed pairwise contact differences (equivalently the primitive-form determinants) and \(\delta \) are units; one contact factor has positive valuation. Thus \(\nu =v_{p}(R)>0\) is odd and \(v(q)=-\nu \). This statement concerns the physical argument \(t\) and does not assume its scale is a p-unit. At every place of \(K\) above \(p\), all reciprocal abscissa values have even finite valuation by the curve equation. The recovered H-P square has this same meaning; before reference recovery its parity is also supplied by \(f(H)*F_{0}=g^{2}\). Zeros have valuation+infinity.
+At a consumed \(p\) outside \(\Sigma \) the fixed pairwise contact differences (equivalently the primitive-form determinants) and \(\delta \) are units; one contact factor has positive valuation. Thus \(\nu =v_{p}(R)>0\) is odd and \(v(q)=-\nu \). This statement concerns the physical argument \(t\) and does not assume its scale is a p-unit. At every place of \(K\) above \(p\), all reciprocal abscissa values have even finite valuation by the curve equation. The recovered H-P square has this same meaning; before reference recovery its parity is also supplied by \(f(H)\cdot F_{0}=g^{2}\). Zeros have valuation+infinity.

 Write \(D_{H}=f(H)\), \(A_{i}=f(U_{i})\), \(B_{i}=\sigma \) \(f(V_{i})\), \(C_{i}=L_{i}-L_{i}'\), \(I=L_{1}-\beta \) and \(G=F(L_{2},L_{3},L_{4})\), with the exact Lucas polynomial in the source. The five factors are

```

### H009

Class: whitespace only. Base 2173-2179; candidate 2168-2174.

```diff
@@ -2173,7 +2168,7 @@
 T_{5}=1+q^{5} C_{4}^{2}+q^{2} A_{1}^{2}+q^{4} B_{2}^{4}
 \end{gather*}

-Except in \(T_{3}\) the three nonconstant valuations lie respectively in odd integers,2+4Z,4+8Z. In \(T_{3}\) their residues are -nu,nu,2 modulo4 and4 modulo8. These classes are pairwise distinct and exclude0. Omitting zero-test terms preserves that property. Therefore every factor has a unique minimum, is nonzero, and has \(\text{valuation}\le 0\); at valuation0 its residue is1. This holds at both split places and at the unique inert place, for arbitrary negative test valuations as well as positive ones.
+Except in \(T_{3}\) the three nonconstant valuations lie respectively in odd integers,2+4Z,4+8Z. In \(T_{3}\) their residues are -nu,nu,2 modulo 4 and 4 modulo 8. These classes are pairwise distinct and exclude 0. Omitting zero-test terms preserves that property. Therefore every factor has a unique minimum, is nonzero, and has \(\text{valuation}\le 0\); at valuation 0 its residue is 1. This holds at both split places and at the unique inert place, for arbitrary negative test valuations as well as positive ones.

 Let \(W=\prod \) \(T_{i}\) and \(\ell =\operatorname{max}_{v|p}v(W)\le 0\). The unchanged trace rows force \(w_{0}\ne 0\) and \(\tau =1/\operatorname{Tr}(W^{-1})\ne 0:\) \(w_{0}=0\) would force \(w_{1}=0\), contrary to \(W\ne 0\). The literal pole row gives \(b=\gamma ^{2}R/\operatorname{Tr}(W^{-1})^{2}\), \(\gamma =408/409\) a unit at \(p\). The trace inequality implies \(v_{p}(b)\le \nu +2\ell \). This valuation is odd. The retained pole obstruction forces an odd valuation of \(b\) to be positive, whence \(\ell >-\nu /2\). At a place attaining \(\ell \) every factor and every term has \(\text{valuation}>-\nu /2\). Thus

```

### H010

Class: status, source locator or provenance prose. Base 2184-2251; candidate 2179-2246.

```diff
@@ -2184,68 +2179,68 @@
 v(A_{1}),v(A_{3}),v(A_{4})>3\nu /4; v(Bi)>7\nu /8
 \end{gather*}

-Integer rounding gives the required high order3, input orders at least1, and positive even reciprocal valuations (at least2). The source's factor lemma for this exact exponent pattern is Brox228 \nolinkurl{lem:residues} and \nolinkurl{prop:extract}; the argument has been reapplied to the actual recovered raw224 objects above.
+Integer rounding gives the required high order 3, input orders at least 1, and positive even reciprocal valuations (at least 2). The source's factor lemma for this exact exponent pattern is Brox228 \nolinkurl{lem:residues} and \nolinkurl{prop:extract}; the argument has been reapplied to the actual recovered raw 224 objects above.

-Only after these positive reciprocal tests do all relevant nonidentity points lie in their respective formal groups. The source's constant-term logarithm estimate has relative precision4 at depth1. Write \(h=m/2\) for the reference index. The integral group identities yield logarithmic ratios \(u_{i}/h\) and \((u_{i}-n_{i})/(h-1)\), killing the possible two-torsion first. At least one of h,h-1 is a p-adic unit. That ratio is integral; the positive \(C_{i}\) test transfers integrality to the other plain ratio and then the full ratio. Relative errors may now be used as absolute errors modulo \(p^{4}\). For \(i>1\) the \(C_{i}\) test gives \(L_{i}=n_{i}\) modulo \(p^{3}\); for \(i=1\) the \(C_{1}\) and \(I\) tests give \(L_{1}=n=\beta \) modulo \(p\). Identity numerators, half-integral \(h\) and inert places are covered exactly as in Version15 \nolinkurl{Integrality before the formal congruences}; no invertibility of the tested numerator is needed. Consequently each comparison radical cubed divides the integer Lucas residual \(\Delta \), and each radical divides the reduced input residual \(J\). There is no added scalar factor \(c\) in these divisibilities.
+Only after these positive reciprocal tests do all relevant nonidentity points lie in their respective formal groups. The source's constant-term logarithm estimate has relative precision 4 at depth 1. Write \(h=m/2\) for the reference index. The integral group identities yield logarithmic ratios \(u_{i}/h\) and \((u_{i}-n_{i})/(h-1)\), killing the possible two-torsion first. At least one of h,h-1 is a p-adic unit. That ratio is integral; the positive \(C_{i}\) test transfers integrality to the other plain ratio and then the full ratio. Relative errors may now be used as absolute errors modulo \(p^{4}\). For \(i>1\) the \(C_{i}\) test gives \(L_{i}=n_{i}\) modulo \(p^{3}\); for \(i=1\) the \(C_{1}\) and \(I\) tests give \(L_{1}=n=\beta \) modulo \(p\). Identity numerators, half-integral \(h\) and inert places are covered exactly as in Version 15 \nolinkurl{Integrality before the formal congruences}; no invertibility of the tested numerator is needed. Consequently each comparison radical cubed divides the integer Lucas residual \(\Delta \), and each radical divides the reduced input residual \(J\). There is no added scalar factor \(c\) in these divisibilities.

 \subsection{Height supplier and global consumers}

-The sibling height theorem gives \(h(u)\le C_{2}\) \(M_{S_{10}}(u)^{\alpha }\) on the full five-contact family, \(\alpha =2103/1024<7/3\). To apply it to this unchanged public comparison set, let \(B_{\Sigma }\) be the product of the fixed primes in \(\Sigma \) outside \(S_{10}\). Then \(M_{S_{10}}(u)\le B_{\Sigma }\) \(M_{\Sigma }(u)\); all radicals are squarefree even when contact valuations are arbitrarily deep. Thus \(h(u)\le H\) \(M_{\Sigma }(u)^{7/3}\), with fixed \(H=C_{2}*B_{\Sigma }^{\alpha }\). No sharp numerical value of this \(H\) is needed or asserted.
+The sibling height theorem gives \(h(u)\le C_{2}\) \(M_{S_{10}}(u)^{\alpha }\) on the full five-contact family, \(\alpha =2103/1024<7/3\). To apply it to this unchanged public comparison set, let \(B_{\Sigma }\) be the product of the fixed primes in \(\Sigma \) outside \(S_{10}\). Then \(M_{S_{10}}(u)\le B_{\Sigma }\) \(M_{\Sigma }(u)\); all radicals are squarefree even when contact valuations are arbitrarily deep. Thus \(h(u)\le H\) \(M_{\Sigma }(u)^{7/3}\), with fixed \(H=C_{2}\cdot B_{\Sigma }^{\alpha }\). No sharp numerical value of this \(H\) is needed or asserted.

-Applying this bound to2+1/t and2+1/(2-t), whose inverse projective matrices have row norms3 and7, and multiplying the two inequalities after subtracting log7 gives
+Applying this bound to 2+1/t and 2+1/(2-t), whose inverse projective matrices have row norms 3 and 7, and multiplying the two inequalities after subtracting log 7 gives

 \begin{gather*}
 h(t)\le H_{2} M_{2}^{\circ }(t)^{7/6}, H_{2}=\log 7+H
 \end{gather*}

-The two block radicals outside \(\Sigma \) are coprime and multiply to the same physical comparison radical. The inequalities also hold when \(h(t)\le \log 7\) and on the harmless \(t=1\) stratum (radical1). All contact domains were already excluded by the literal rows. This source-to-consumer passage uses the new height theorem on both transformed arguments, with index-set coverage and fixed discarded primes explicitly accounted for.
+The two block radicals outside \(\Sigma \) are coprime and multiply to the same physical comparison radical. The inequalities also hold when \(h(t)\le \log 7\) and on the harmless \(t=1\) stratum (radical 1). All contact domains were already excluded by the literal rows. This source-to-consumer passage uses the new height theorem on both transformed arguments, with index-set coverage and fixed discarded primes explicitly accounted for.

-The retained aggregate trace theorem gives \(B^{2}\le M_{1}*h(T)+M_{2}\), \(B=\operatorname{max}(|n|,|a|,|t|,|b|)\), and \(M_{2}\) is ineffective. Since \(T=t_{1}/t_{0}\), \(h(T)\le h(t_{1})+h(t_{0})\). If each radical to power \(k\) divides a nonzero integer \(J_{0}\), then
+The retained aggregate trace theorem gives \(B^{2}\le M_{1}\cdot h(T)+M_{2}\), \(B=\operatorname{max}(|n|,|a|,|t|,|b|)\), and \(M_{2}\) is ineffective. Since \(T=t_{1}/t_{0}\), \(h(T)\le h(t_{1})+h(t_{0})\). If each radical to power \(k\) divides a nonzero integer \(J_{0}\), then

 \begin{gather*}
-B^{2}\le C |J_{0}|^{7/(6k)}+M_{2}, C=2*M_{1}*H_{2}
+B^{2}\le C |J_{0}|^{7/(6k)}+M_{2}, C=2\cdot M_{1}\cdot H_{2}
 \end{gather*}

-The unchanged scalar conclusions are \(c=|a|>0\), \(B\ge c\), \(c\ge 149^{{L}_{N}}\), \(L_{N}=\text{floor}(9(2N-1)/4)+1\), and
+The unchanged scalar conclusions are \(c=|a|>0\), \(B\ge c\), \(c\ge 149^{{L}_{N}}\), \(L_{N}=\left\lfloor 9(2N-1)/4\right\rfloor+1\), and

 \begin{gather*}
-h(\beta )\le C_{3}*149^{-L_{N}}*c*(1+\operatorname{log}(c)/3), C_{3}=2^{330770}
+h(\beta )\le C_{3}\cdot 149^{-L_{N}}\cdot c\cdot (1+\operatorname{log}(c)/3), C_{3}=2^{330770}
 \end{gather*}

-They are the actual four-contact/parity-scalar conclusions in Version15 \nolinkurl{v222:fourcontact} and the scalar-S step, not the old \(c=|a-1|\) assertion.
+They are the actual four-contact/parity-scalar conclusions in Version 15 \nolinkurl{v222:fourcontact} and the scalar-S step, not the old \(c=|a-1|\) assertion.

-If \(\Delta \ne 0\), \(|\Delta |\le 14B^{4}\). Take \(k=3\) to obtain \(B^{2}\le C*14^{7/18}*B^{14/9}+M_{2}\). The right exponent is strictly below2, so \(B\) is bounded by a fixed constant. Uniform \(c\ge 149^{{L}_{N}}\) contradicts this for all sufficiently large \(N\). Hence \(\Delta =0\). The retained integer Lucas argument then gives log \(B\ge (c-5)\operatorname{log}(c-2)\) for large \(c\) (the scalar-S variant is stronger).
+If \(\Delta \ne 0\), \(|\Delta |\le 14B^{4}\). Take \(k=3\) to obtain \(B^{2}\le C\cdot 14^{7/18}\cdot B^{14/9}+M_{2}\). The right exponent is strictly below 2, so \(B\) is bounded by a fixed constant. Uniform \(c\ge 149^{{L}_{N}}\) contradicts this for all sufficiently large \(N\). Hence \(\Delta =0\). The retained integer Lucas argument then gives log \(B\ge (c-5)\operatorname{log}(c-2)\) for large \(c\) (the scalar-S variant is stronger).

-If \(n-\beta \ne 0\), its reduced numerator \(J\) satisfies \(|J|\le 2B\) \(\operatorname{exp}(h(\beta ))\). Take \(k=1\); for \(B^{2}\ge 2M_{2}\) we have \(B^{5/6}\le 2C*2^{7/6}*\operatorname{exp}((7/6)h(\beta ))\). Thus
+If \(n-\beta \ne 0\), its reduced numerator \(J\) satisfies \(|J|\le 2B\) \(\operatorname{exp}(h(\beta ))\). Take \(k=1\); for \(B^{2}\ge 2M_{2}\) we have \(B^{5/6}\le 2C\cdot 2^{7/6}\cdot \operatorname{exp}((7/6)h(\beta ))\). Thus

 \begin{gather*}
 \operatorname{log} B\le (6/5)\operatorname{log}(2C)+(7/5)\log 2+(7/5)h(\beta )
 \end{gather*}

-As \(N\) grows, the coefficient \((7/5)C_{3}*149^{-{L}_{N}}\) becomes at most1. The right side is then bounded by a fixed constant+c+(c log c)/3, contradicting the Lucas lower bound for sufficiently large \(c\). Therefore \(n=\beta =51X^{2}+2504\) is integral; for \(X=u/v\) reduced, \(v^{2}|51\) and squarefreeness of51 imply \(v=1\). Every threshold depends only on fixed constants and \(L_{N}\) grows monotonically, so a single ineffective \(N_{0}\) works for every larger \(N\).
+As \(N\) grows, the coefficient \((7/5)C_{3}\cdot 149^{-{L}_{N}}\) becomes at most 1. The right side is then bounded by a fixed constant+c+(c log c)/3, contradicting the Lucas lower bound for sufficiently large \(c\). Therefore \(n=\beta =51X^{2}+2504\) is integral; for \(X=u/v\) reduced, \(v^{2}|51\) and squarefreeness of 51 imply \(v=1\). Every threshold depends only on fixed constants and \(L_{N}\) grows monotonically, so a single ineffective \(N_{0}\) works for every larger \(N\).

-\subsection{Fresh completeness and the218 control}
+\subsection{Fresh completeness and the 218 control}

-For an integer input use the unchanged scalar-S/four-contact/parity-scalar preparation, then the root labels, positive trace scale, fixed real neighborhoods and finite progression in the precise order of the frozen Version15 construction. Neither changed factors nor eliminated fourth-power caches occur in that preparation. The source chooses a common denominator dilation and the same ten contact forms per scale, merges repeated forms, and chooses the common reference index by the unchanged separated reduction-order congruences. No new prime pattern, scale or denominator is introduced here.
+For an integer input use the unchanged scalar-S/four-contact/parity-scalar preparation, then the root labels, positive trace scale, fixed real neighborhoods and finite progression in the precise order of the frozen Version 15 construction. Neither changed factors nor eliminated fourth-power caches occur in that preparation. The source chooses a common denominator dilation and the same ten contact forms per scale, merges repeated forms, and chooses the common reference index by the unchanged separated reduction-order congruences. No new prime pattern, scale or denominator is introduced here.

-At a selected contact prime \(v(q)=-1\), all \(C_{i},I,G\) have \(\text{valuation}\ge 4\) and every reciprocal abscissa has \(\text{valuation}\ge 2\). The changed terms \(q^{5}\) \(C_{i}^{2}\) have \(\text{valuation}\ge 3\), \(q^{5}\) \(I^{4}\ge 11\) and \(q^{3}\) \(A_{2}^{2}\ge 1\); every other nonconstant term was already positive. Hence \(W=1\) modulo the chosen place. At the opposite place the newly proved noncancellation lemma still applies; trace residues are1 or2. The comparison pole input therefore has the same odd depth1 at selected primes and even valuations away from them.
+At a selected contact prime \(v(q)=-1\), all \(C_{i},I,G\) have \(\text{valuation}\ge 4\) and every reciprocal abscissa has \(\text{valuation}\ge 2\). The changed terms \(q^{5}\) \(C_{i}^{2}\) have \(\text{valuation}\ge 3\), \(q^{5}\) \(I^{4}\ge 11\) and \(q^{3}\) \(A_{2}^{2}\ge 1\); every other nonconstant term was already positive. Hence \(W=1\) modulo the chosen place. At the opposite place the newly proved noncancellation lemma still applies; trace residues are 1 or 2. The comparison pole input therefore has the same odd depth 1 at selected primes and even valuations away from them.

-At prepared finite primes \(q\) tends arbitrarily deeply to0, so every positive exponent used in the new factors makes its term small. The source's squareclasses and depths4,2,2 for the pole input at2,3,17 are unchanged. At both real embeddings \(q>0\) is small, all test powers are even, \(W\) tends to1, and the pole input tends to \(\gamma ^{2}/4\) in(0,17). The same simultaneous pole-realization theorem supplies independent witnesses for each detector. These are new complete witnesses for the changed factors, not reuse of old pole coordinates. The selected contact primes ensure \(q_{0},q_{1}\ne 0\) \((\text{also} \text{real} q>0)\), so all reciprocal weights exist. Reconstruct each deleted fourth power and apply the inherited exact raw224 coordinate maps; the symbolic identities give the new quadratic rows. Completeness is uniform for all sufficiently large \(N\) as in the parent scalar preparation.
+At prepared finite primes \(q\) tends arbitrarily deeply to 0, so every positive exponent used in the new factors makes its term small. The source's squareclasses and depths 4,2,2 for the pole input at 2,3,17 are unchanged. At both real embeddings \(q>0\) is small, all test powers are even, \(W\) tends to 1, and the pole input tends to \(\gamma ^{2}/4\) in (0,17). The same simultaneous pole-realization theorem supplies independent witnesses for each detector. These are new complete witnesses for the changed factors, not reuse of old pole coordinates. The selected contact primes ensure \(q_{0},q_{1}\ne 0\) \((\text{also} \text{real} q>0)\), so all reciprocal weights exist. Reconstruct each deleted fourth power and apply the inherited exact raw 224 coordinate maps; the symbolic identities give the new quadratic rows. Completeness is uniform for all sufficiently large \(N\) as in the parent scalar preparation.

-For218 keep the parent's original factor exponents. The same exact clearing proof identifies its witnesses with the old ones on \(q_{0}*q_{1}\ne 0\). Soundness follows by reconstructing the unrestricted old system. Completeness uses the parent's selected witnesses with \(q>0\). Thus no claim that every old witness has \(q_{0}\ne 0\) is needed, and no new height theorem is needed for the218 control. This corrects the contribution's occasional unqualified phrase "solution-set transport": the all-solution bijection is restricted to the nonzero-weight domain; the rational projection agrees without that qualification by the two arguments just given.
+For 218 keep the parent's original factor exponents. The same exact clearing proof identifies its witnesses with the old ones on \(q_{0}\cdot q_{1}\ne 0\). Soundness follows by reconstructing the unrestricted old system. Completeness uses the parent's selected witnesses with \(q>0\). Thus no claim that every old witness has \(q_{0}\ne 0\) is needed, and no new height theorem is needed for the 218 control. This corrects the contribution's occasional unqualified phrase "solution-set transport": the all-solution bijection is restricted to the nonzero-weight domain; the rational projection agrees without that qualification by the two arguments just given.

 \subsection{Scope and evidence}

-The finite checker proves exact component identities, complete row occurrence coverage, inverse weights, unchanged rows, and full expansions, with deliberate corruptions rejected. These checks do not certify the retained arithmetic premises. The new214 argument has explicit local, completeness and height consumers above; their independent review and inventory coverage will be bound separately. No claim of public priority, a numerical defining parameter, or whole-proof completion is made. The construction deliberately branches at224; the final paired-root/trace-quotient reductions yielding222 are not counted again because they conflict with this clearing strategy.
+The finite checker proves exact component identities, complete row occurrence coverage, inverse weights, unchanged rows, and full expansions, with deliberate corruptions rejected. These checks do not certify the retained arithmetic premises. The local, completeness and height arguments use the explicit consumers above. No numerical defining parameter is supplied. The construction deliberately branches at 224; the final paired-root/trace-quotient reductions yielding 222 are not counted again because they conflict with this clearing strategy.
 \clearpage
 % Source: research/quartic214/proofs/uniform-existence.md
 \section{Existing 214: uniform existence and actual completeness interfaces}\label{q214:uniform-existence}
 \noindent\textit{Source: }\nolinkurl{research/quartic214/proofs/uniform-existence.md}.\par
-\begin{quote}\small \textbf{Current foundation overlay:} The Version~15 byte-identity and no-new-repair statements in this dated source describe its historical freeze.  This edition incorporates the Version~16 foundation with the Version~18 inverse-theorem replacement in Section~\ref{v15:gi-full}, and the explicit source-to-consumer transition in Section~\ref{q214:foundation-transition}.  The historical text is retained as evidence; it does not negate or independently accept that changed application.\end{quote}
+\begin{quote}\small \textbf{Foundation sources:} The Version~15 byte-identity and no-new-repair statements in this dated source describe its historical freeze.  This edition incorporates the Version~16 foundation with the Version~18 inverse-theorem replacement in Section~\ref{v15:gi-full}, and the explicit source-to-consumer transition in Section~\ref{q214:foundation-transition}.  The historical text describes the earlier source version.\end{quote}

-\begin{quote}\footnotesize Author: \nolinkurl{/root/d214_uniform_existence}, 2026-11-11. Author argument only; fresh non-author acceptance is required. No source, old packet, coefficient, witness table or public repository is changed. This is an additive clarification of the frozen existing 214 family, with its original hypotheses retained exactly. Source bindings and actual consumer passages are in \nolinkurl{SOURCE_USES.json} and \nolinkurl{CONTRACT.json.}\end{quote}
+\begin{quote}\footnotesize This argument concerns the existing 214 family, with its original hypotheses retained exactly. Source bindings and actual consumer passages are in \nolinkurl{SOURCE_USES.json} and \nolinkurl{CONTRACT.json}.\end{quote}

-[P01: exact theorem] Let the 214 family be exactly the family with 188 primitive integral quadratic residuals in \nolinkurl{research/quadratic-ten-contact-integration/existence/artifacts/candidate214-brox/}, at private HEAD \nolinkurl{bfeb8400982c9a169e4fdd39fb68ec053621e8ed.} Its parameter is the fixed coefficient \(A_{N}=149^{2N+1}\), not an existential coordinate. Subject to the named full-family height and retained elliptic/rank interfaces below, the conclusion is
+[P01: exact theorem] Let the 214 family be exactly the family with 188 primitive integral quadratic residuals in the finite specification in Section~\ref{q214:rows}, at source revision \nolinkurl{bfeb8400982c9a169e4fdd39fb68ec053621e8ed}. Its parameter is the fixed coefficient \(A_{N}=149^{2N+1}\), not an existential coordinate. Subject to the named full-family height and retained elliptic/rank interfaces below, the conclusion is

 \begin{gather*}
 \exists  N_{0} \in  Z_{\ge 1}, \text{ for }  \text{ every }  \text{ integer }  N\ge N_{0}, \text{ for }  \text{ every }  x \in  Q,\\
```

### H011

Class: status, source locator or provenance prose. Base 2254-2264; candidate 2249-2259.

```diff
@@ -2254,11 +2249,11 @@

 This is the same polynomial family. \(N_{0}\) is not computed. \(N\ge 53\) is a coefficient-height condition only; it need not be included in the arithmetic \(N_{0}\), and replacing \(N_{0}\) by \(\operatorname{max}(N_{0},53)\) is harmless. No \(N=53\) defining theorem or numerical defining member follows.

-[P02: scope of source carry] The entire latest PR26 manuscript at public checkout HEAD \nolinkurl{1a49013b5683f58d2f88bb018a07d13770354157} and the old 214 frozen \nolinkurl{existence/sources/quartic_v15.tex} have the identical \textbf{raw byte} SHA256 \nolinkurl{44ba3a8ec8521c29b81b26cfb9981cd6d5f3c76d54e7782438614842edb52c74} and 1924438 bytes. This is stronger than normalized-line identity. Thus no analytic, restricted-converse, aggregate, scalar or prime-selection manuscript repair is newly imported from PR26 here. The later audit records can justify exact unchanged applications at their stated scope only after source/consumer comparison; PR status is not an arithmetic premise. This author read the actual source passages identified in \(\text{SOURCE}_{\text{USES}}\), including the sum-pole/graph argument, the prime theorem/obstruction-tail/fixed-field and diagonal statements, the CRT argument, scalar-S/four-contact preparation and zero-preparation proof. This author did not reconstruct every internal RC/analytic sublemma or final published source anew. Those unchanged internal foundations and their eligible source review remain a separately bound dependency; this packet closes the 214 application joins, not their entire recursive review.
+[P02: scope of source carry] The entire latest PR26 manuscript at public checkout HEAD \nolinkurl{1a49013b5683f58d2f88bb018a07d13770354157} and the old 214 frozen \nolinkurl{existence/sources/quartic_v15.tex} have the identical \textbf{raw byte} SHA256 \nolinkurl{44ba3a8ec8521c29b81b26cfb9981cd6d5f3c76d54e7782438614842edb52c74} and 1924438 bytes. This is stronger than normalized-line identity. Thus no analytic, restricted-converse, aggregate, scalar or prime-selection manuscript repair is newly imported from PR26 here. The source statements are used at their stated domains and through the source-to-consumer maps. The application uses the source passages identified in \(\text{SOURCE}_{\text{USES}}\), including the sum-pole/graph argument, the prime theorem/obstruction-tail/fixed-field and diagonal statements, the CRT argument, scalar-S/four-contact preparation and zero-preparation proof. Their internal restricted-converse and analytic foundations remain separate prerequisites.

-[P03: exact retained inputs] Use \(K=Q(\sqrt{2})\), \(d=3-\sqrt{2}\), \(E:y^{2}=x^{3}-d^{2}\) \(x\), and the same \(P=2(1+\sqrt{2},2\sqrt{2})\). The four nonzero integer labels are (n,a,t,b), \(c=|a|\) and \(B=\operatorname{max}(|n|,|a|,|t|,|b|)\), so \(B\ge c\). The physical scale is \(T=(1/4)\operatorname{Tr}(\sum _{i} x([n_{i}]P))>0\). The physical arguments are \(t_{0}=\lambda \) and \(t_{1}=T\) \(\lambda \). The contact set is \(\Theta _{2}=\Theta \) union(2-Theta), \(\Theta =\{0,-1/2,-1,1/2399,-32/407\}\); \(\Sigma \) is the \(\text{primes}\le 76176\) together with 2029147. Each comparison radical \(M_{j}\) is the squarefree product of primes \(p\) outside \(\Sigma \) at a positive odd contact of \(t_{j}\). Do not substitute the sibling center-3/11 contact system or its input \(51(2X+1)^{2}+2504\). Here \(\beta =51x^{2}+2504\).
+[P03: exact retained inputs] Use \(K=Q(\sqrt{2})\), \(d=3-\sqrt{2}\), \(E:y^{2}=x^{3}-d^{2}\) \(x\), and the same \(P=2(1+\sqrt{2},2\sqrt{2})\). The four nonzero integer labels are (n,a,t,b), \(c=|a|\) and \(B=\operatorname{max}(|n|,|a|,|t|,|b|)\), so \(B\ge c\). The physical scale is \(T=(1/4)\operatorname{Tr}(\sum _{i} x([n_{i}]P))>0\). The physical arguments are \(t_{0}=\lambda \) and \(t_{1}=T\) \(\lambda \). The contact set is \(\Theta _{2}=\Theta \cup(2-\Theta)\), \(\Theta =\{0,-1/2,-1,1/2399,-32/407\}\); \(\Sigma \) is the \(\text{primes}\le 76176\) together with 2029147. Each comparison radical \(M_{j}\) is the squarefree product of primes \(p\) outside \(\Sigma \) at a positive odd contact of \(t_{j}\). Do not substitute the sibling center-3/11 contact system or its input \(51(2X+1)^{2}+2504\). Here \(\beta =51x^{2}+2504\).

-[P04: restored objects and branches] The old existence proof's exact Laurent clearing and raw224 inverse maps reconstruct the physical reference/scalar/root system before any ratio is consumed. Its recovered f,S,g and \(Q_{2}\) coefficient at149 imply \(w=g^{4}/f^{2}\); deleted fourth powers are their actual squares. The shared alternate ratio has numerator and denominator of valuation -v149(f)/2 and is nonzero. The unchanged scalar argument excludes reference torsion and \(H\) indices -1,0,1 before logarithms. No rational component or tested numerator is divided by. The new inverse rows enforce \(q_{j}\ne 0\), \(q_{j}=1/R_{j}-1\). They remove an irrelevant old \(q_{j}=0\) witness stratum, so this is not an all-old-witness bijection. The stratum \(\delta _{j}=t_{j}-1=0\) has \(q_{j}=-1\) and \(M_{j}=1\), and needs no division by \(\delta _{j}\). A contact \(t_{j}\) in \(\Theta _{2}\) is excluded by \(F_{2}(t_{j})(1+q_{j})=\delta _{j}^{10}\) and \(F_{2}(1)\ne 0\). A putative \(q_{j}=0\) has radical one, but is in any event excluded in 214. None of these statements confuses \(\delta _{j}\) with the integer Lucas residual \(\Delta \) below.
+[P04: restored objects and branches] The old existence proof's exact Laurent clearing and raw 224 inverse maps reconstruct the physical reference/scalar/root system before any ratio is consumed. Its recovered f,S,g and \(Q_{2}\) coefficient at 149 imply \(w=g^{4}/f^{2}\); deleted fourth powers are their actual squares. The shared alternate ratio has numerator and denominator of valuation -v149(f)/2 and is nonzero. The unchanged scalar argument excludes reference torsion and \(H\) indices -1,0,1 before logarithms. No rational component or tested numerator is divided by. The new inverse rows enforce \(q_{j}\ne 0\), \(q_{j}=1/R_{j}-1\). They remove an irrelevant old \(q_{j}=0\) witness stratum, so this is not an all-old-witness bijection. The stratum \(\delta _{j}=t_{j}-1=0\) has \(q_{j}=-1\) and \(M_{j}=1\), and needs no division by \(\delta _{j}\). A contact \(t_{j}\) in \(\Theta _{2}\) is excluded by \(F_{2}(t_{j})(1+q_{j})=\delta _{j}^{10}\) and \(F_{2}(1)\ne 0\). A putative \(q_{j}=0\) has radical one, but is in any event excluded in 214. None of these statements confuses \(\delta _{j}\) with the integer Lucas residual \(\Delta \) below.

 [P05: changed local factors] At a consumed \(p\) outside \(\Sigma \) and either place above \(p\), normalize \(v(p)=1\). Exactly one contact factor has positive odd valuation \(\nu \), \(\delta _{j}\) is a unit and \(v(q_{j})=-\nu \). The five actual 214 factors are

```

### H012

Class: status, source locator or provenance prose. Base 2270-2292; candidate 2265-2287.

```diff
@@ -2270,23 +2265,23 @@
 1+q^{5} C_{4}^{2}+q^{2} A_{1}^{2}+q^{4} B_{2}^{4}
 \end{gather*}

-Here \(D_{H}=f(H)\), \(A_{i}=f(U_{i})\), \(B_{i}=\sigma \) \(f(V_{i})\), \(C_{i}=L_{i}-L_{i}'\), \(I=L_{1}-\beta \) and \(G=L_{3}^{2}-L_{2}(L_{2}-2)L_{3}L_{4}+(L_{2}-2)^{2}L_{4}^{2}-1\), with \(f=1/x\) and \(f(O)=0\). Every nonzero reciprocal abscissa has even valuation, including \(f(H-P)\) restored before this step. In the generic factors the finite nonconstant valuations lie in odd integers, 2+4Z and 4+8Z. In the third factor the first three have residues \(-\nu \), \(\nu \), 2 modulo4 and the last is4 modulo8. They are pairwise distinct and distinct from zero. Zero tests omit leaves. Thus each factor is nonzero with \(\text{valuation}\le 0\), and has residue1 whenever its valuation is zero, at both split places and at the inert place. This argument treats arbitrary negative test valuations too.
+Here \(D_{H}=f(H)\), \(A_{i}=f(U_{i})\), \(B_{i}=\sigma \) \(f(V_{i})\), \(C_{i}=L_{i}-L_{i}'\), \(I=L_{1}-\beta \) and \(G=L_{3}^{2}-L_{2}(L_{2}-2)L_{3}L_{4}+(L_{2}-2)^{2}L_{4}^{2}-1\), with \(f=1/x\) and \(f(O)=0\). Every nonzero reciprocal abscissa has even valuation, including \(f(H-P)\) restored before this step. In the generic factors the finite nonconstant valuations lie in odd integers, 2+4Z and 4+8Z. In the third factor the first three have residues \(-\nu \), \(\nu \), 2 modulo 4 and the last is 4 modulo 8. They are pairwise distinct and distinct from zero. Zero tests omit leaves. Thus each factor is nonzero with \(\text{valuation}\le 0\), and has residue 1 whenever its valuation is zero, at both split places and at the inert place. This argument treats arbitrary negative test valuations too.

-[P06: trace/pole extraction] Write \(W\) for the product and \(\ell =\operatorname{max}_{v|p}v(W)\le 0\). The literal cleared trace equation \(w_{0}^{2}-2w_{0}*\tau -2w_{1}^{2}=0\), with \(W=w_{0}+\sqrt{2}*w_{1}\), forces \(w_{0}\ne 0\) since \(W\ne 0\), and \(\tau =1/\operatorname{Tr}(W^{-1})\ne 0\). The actual pole input is \(\mathfrak{b}=\gamma ^{2}\) \(R/\operatorname{Tr}(W^{-1})^{2}\), \(\gamma =408/409\), a p-unit. Trace gives \(v_{p}(\operatorname{Tr}(W^{-1}))\ge -\ell \), so \(v_{p}(\mathfrak{b})\le \nu +2\ell \). Its valuation is odd. The zero-preparation pole obstruction excludes negative odd valuations outside2,3,17 and hence forces it positive. Therefore \(\ell >-\nu /2\). At a place attaining \(\ell \) every factor valuation and every finite summand valuation exceeds \(-\nu /2\). Solving gives \(v(C_{2},C_{3},C_{4},G)>9\nu /4\), \(v(I)>9\nu /8\), \(v(C_{1})>3\nu /8\), \(v(D_{H})>3\nu /4\), \(v(A_{2})>5\nu /4\), \(v(A_{1},A_{3},A_{4})>3\nu /4\) and \(v(B_{i})>7\nu /8\). Integer rounding and even reciprocal valuations give cross/Lucas \(\text{orders}\ge 3\), input \(\text{order}\ge 1\), and every reciprocal \(\operatorname{depth}\ge 2\). No implication is extracted from a radical-one detector alone.
+[P06: trace/pole extraction] Write \(W\) for the product and \(\ell =\operatorname{max}_{v|p}v(W)\le 0\). The literal cleared trace equation \(w_{0}^{2}-2w_{0}\cdot \tau -2w_{1}^{2}=0\), with \(W=w_{0}+\sqrt{2}\cdot w_{1}\), forces \(w_{0}\ne 0\) since \(W\ne 0\), and \(\tau =1/\operatorname{Tr}(W^{-1})\ne 0\). The actual pole input is \(\mathfrak{b}=\gamma ^{2}\) \(R/\operatorname{Tr}(W^{-1})^{2}\), \(\gamma =408/409\), a p-unit. Trace gives \(v_{p}(\operatorname{Tr}(W^{-1}))\ge -\ell \), so \(v_{p}(\mathfrak{b})\le \nu +2\ell \). Its valuation is odd. The zero-preparation pole obstruction excludes negative odd valuations outside 2,3,17 and hence forces it positive. Therefore \(\ell >-\nu /2\). At a place attaining \(\ell \) every factor valuation and every finite summand valuation exceeds \(-\nu /2\). Solving gives \(v(C_{2},C_{3},C_{4},G)>9\nu /4\), \(v(I)>9\nu /8\), \(v(C_{1})>3\nu /8\), \(v(D_{H})>3\nu /4\), \(v(A_{2})>5\nu /4\), \(v(A_{1},A_{3},A_{4})>3\nu /4\) and \(v(B_{i})>7\nu /8\). Integer rounding and even reciprocal valuations give cross/Lucas \(\text{orders}\ge 3\), input \(\text{order}\ge 1\), and every reciprocal \(\operatorname{depth}\ge 2\). No implication is extracted from a radical-one detector alone.

-[P07: exact integer consumers] Positive reciprocal valuations put \(H,U_{i}\) in the primary formal group and \(H-P,V_{i}\) in its conjugate formal group, with the identity convention at zero numerator points. Write \(H=[m]R_{0}+T_{0}\), \(h=m/2\); all consumed \(p\) are odd. The integral identities \([m]U_{i}=[2u_{i}]H\) and \([m-2]V_{i}=[2(u_{i}-n_{i})](H-P)\) kill two-torsion. At least one of h,h-1 is a p-adic unit, so one full logarithmic ratio is integral. The positive \(C_{i}\) transfers integrality of the corresponding plain ratio to the other; formal logarithm units then give integrality of both full ratios. Only now is the relative error of order4 used as an absolute congruence. For \(i>1\), \(L_{i}=n_{i}\) mod \(p^{3}\); for \(i=1\), \(L_{1}=n=\beta \) mod \(p\). Consequently, for
+[P07: exact integer consumers] Positive reciprocal valuations put \(H,U_{i}\) in the primary formal group and \(H-P,V_{i}\) in its conjugate formal group, with the identity convention at zero numerator points. Write \(H=[m]R_{0}+T_{0}\), \(h=m/2\); all consumed \(p\) are odd. The integral identities \([m]U_{i}=[2u_{i}]H\) and \([m-2]V_{i}=[2(u_{i}-n_{i})](H-P)\) kill two-torsion. At least one of h,h-1 is a p-adic unit, so one full logarithmic ratio is integral. The positive \(C_{i}\) transfers integrality of the corresponding plain ratio to the other; formal logarithm units then give integrality of both full ratios. Only now is the relative error of order 4 used as an absolute congruence. For \(i>1\), \(L_{i}=n_{i}\) mod \(p^{3}\); for \(i=1\), \(L_{1}=n=\beta \) mod \(p\). Consequently, for

 \begin{gather*}
-\Delta =t^{2}-a(a-2)t*b+(a-2)^{2} b^{2}-1,
+\Delta =t^{2}-a(a-2)t\cdot b+(a-2)^{2} b^{2}-1,
 \end{gather*}

 one has \(M_{j}^{3}\) | \(\Delta \) for each \(j\), and \(M_{j}\) | \(J\) when \(J\) is the reduced numerator of n-beta. These are separate divisibilities, with no factor \(c\) and no requirement that \(M_{0}\) and \(M_{1}\) be coprime. Rational \(\beta \) is p-integral whenever an input congruence is consumed. If \(J\ne 0\), \(|J|\le 2B\) \(\operatorname{exp}(h(\beta ))\); if \(\Delta \ne 0\), \(|\Delta |\le 14B^{4}\). These are the exact objects used below.

 [P08: aggregate source application] The actual aggregate input is the \textbf{sum} theorem, not the odd-label product theorem. On \(E_{0}:Y^{2}=X^{3}-X\) let P1,P2 be the pointed-isomorphism images of \(P\) and its conjugate. The independent squareclasses d,d' in \(K(i)\) provide an automorphism fixing \(P_{1}\) and negating \(P_{2}\) while fixing Z[i]; applying it to a torsion relation proves their Z[i]-independence modulo torsion. For arbitrary nonzero labels, at any common pole of summands in one block, the pole coefficient is \(\lambda _{i}^{-2}\) \(\sum _{j}\) \((n_{i}/n_{j})^{2}\), a nonzero positive rational multiple of \(\lambda _{i}^{-2}\). Cross-block common poles would contradict that independence. Restriction to a nonzero elliptic subgroup direction therefore excludes every positive-dimensional abelian translate through the actual tuple in a sum fiber. This covers negative, repeated and noncoprime labels with no parity condition.

-[P09: family/normalization join] Apply final published Von Buhren2017 Theorem1.1, printed308, to \(A=E_{0}^{8}\), parameter \(P^{1}\), and the integral projective graph closure of \(F_{+}=(d/2)\sum \) \(X_{i}+(d'/2)\sum \) \(X_{i}'\). The fixed finite-rank group is generated by \(P_{1}\) in each first-block coordinate and \(P_{2}\) in each second-block coordinate. Its points lie in the theorem's \(C(\Gamma ,\epsilon )\) by taking error point0. Embed \(E_{0}\) by \(O(3O)\), and its product by Segre. Restriction of degree-n plane forms to a smooth plane cubic is surjective for all \(n\ge 1\) from \(0\to O(n-3)\to O(n)\to O_{E}(n)\to 0\) and \(H^{1}(P^{2},O(n-3))=0\). Tensoring and the Segre multiplication map provide the source's embedding condition(1.1) for the product. \(P^{1}\) uses \(O(1)\). The actual tuple avoids all coordinate poles since P1,P2 are nontorsion and labels nonzero. A translate in a projective graph fiber through this tuple would meet the function domain densely and make \(F_{+}\) constant there, contradicted by \(P_{08}\); graph boundary components do not change this. \(F_{+}(\text{tuple})=2T\). The fixed product canonical height is a positive multiple of the sum of all eight coordinate canonical heights, hence twice a multiple of the four original heights. Since \(h(2T)\le h(T)+\log 2\) and \(\widehat{h}([n_{i}]P)=n_{i}^{2}\) \(\widehat{h}(P)\), \(\widehat{h}(P)>0\), the theorem gives fixed \(M_{1}>0,M_{2}\ge 1\) with \(B^{2}\le M_{1}\) \(h(T)+M_{2}\) for every tuple. The constants are fixed before x,N or labels; the additive \(M_{2}\) is ineffective, exactly as in the published source. No full rank-one theorem is required for this aggregate step.
+[P09: family/normalization join] Apply final published Von Buhren 2017 Theorem 1.1, printed 308, to \(A=E_{0}^{8}\), parameter \(P^{1}\), and the integral projective graph closure of \(F_{+}=(d/2)\sum \) \(X_{i}+(d'/2)\sum \) \(X_{i}'\). The fixed finite-rank group is generated by \(P_{1}\) in each first-block coordinate and \(P_{2}\) in each second-block coordinate. Its points lie in the theorem's \(C(\Gamma ,\epsilon )\) by taking error point 0. Embed \(E_{0}\) by \(O(3O)\), and its product by Segre. Restriction of degree-n plane forms to a smooth plane cubic is surjective for all \(n\ge 1\) from \(0\to O(n-3)\to O(n)\to O_{E}(n)\to 0\) and \(H^{1}(P^{2},O(n-3))=0\). Tensoring and the Segre multiplication map provide the source's embedding condition (1.1) for the product. \(P^{1}\) uses \(O(1)\). The actual tuple avoids all coordinate poles since P1,P2 are nontorsion and labels nonzero. A translate in a projective graph fiber through this tuple would meet the function domain densely and make \(F_{+}\) constant there, contradicted by \(P_{08}\); graph boundary components do not change this. \(F_{+}(\text{tuple})=2T\). The fixed product canonical height is a positive multiple of the sum of all eight coordinate canonical heights, hence twice a multiple of the four original heights. Since \(h(2T)\le h(T)+\log 2\) and \(\widehat{h}([n_{i}]P)=n_{i}^{2}\) \(\widehat{h}(P)\), \(\widehat{h}(P)>0\), the theorem gives fixed \(M_{1}>0,M_{2}\ge 1\) with \(B^{2}\le M_{1}\) \(h(T)+M_{2}\) for every tuple. The constants are fixed before x,N or labels; the additive \(M_{2}\) is ineffective, exactly as in the published source. No full rank-one theorem is required for this aggregate step.

-[P10: height domain and maps] Retain the sibling full-family supplier \(h(u)\le C_{2}\) \(M_{S_{10}}(u)^{\alpha }\), \(\alpha =2103/1024<7/3\), on every rational argument avoiding its four finite contacts; the full geometric/modular/height chain supplying it remains a separately reviewed interface. Put \(B_{\Sigma }=\prod \) of primes in \(\Sigma \) outside \(S_{10}\). Squarefreeness gives \(M_{S_{10}}\le B_{\Sigma }\) \(M_{\Sigma }\), even at deep contacts, so \(h(u)\le H\) \(M_{\Sigma }(u)^{7/3}\), \(H=C_{2}\) \(B_{\Sigma }^{\alpha }\) fixed. Apply this to \(u=2+1/t_{j}\) and \(u=2+1/(2-t_{j})\). Their excluded finite contacts correspond exactly to the ten excluded \(t_{j}\) contacts, and \(t_{j}=0,2\) are already excluded; the inverse projective row norms are3 and7. If \(h(t_{j})>\log 7\), multiply the two inequalities for \(h(t_{j})-\log 7\). Outside \(\Sigma \) the two block radicals are disjoint and their product is exactly \(M_{j}\), giving \(h(t_{j})\le H_{2}\) \(M_{j}^{7/6}\), \(H_{2}=\log 7+H\). If \(h(t_{j})\le \log 7\) it follows directly, including \(t_{j}=1\) with \(M_{j}=1\). Thus the argument covers the full rational solution domain, not a bounded example. Because \(t_{0}\ne 0\) and \(t_{1}=Tt_{0}\), \(h(T)\le h(t_{0})+h(t_{1})\). If \(M_{j}^{k}\) divides the same nonzero integer \(J_{0}\) separately for both \(j\), then
+[P10: height domain and maps] Retain the sibling full-family supplier \(h(u)\le C_{2}\) \(M_{S_{10}}(u)^{\alpha }\), \(\alpha =2103/1024<7/3\), on every rational argument avoiding its four finite contacts; the full geometric/modular/height chain supplying it remains a separate prerequisite. Put \(B_{\Sigma }=\prod \) of primes in \(\Sigma \) outside \(S_{10}\). Squarefreeness gives \(M_{S_{10}}\le B_{\Sigma }\) \(M_{\Sigma }\), even at deep contacts, so \(h(u)\le H\) \(M_{\Sigma }(u)^{7/3}\), \(H=C_{2}\) \(B_{\Sigma }^{\alpha }\) fixed. Apply this to \(u=2+1/t_{j}\) and \(u=2+1/(2-t_{j})\). Their excluded finite contacts correspond exactly to the ten excluded \(t_{j}\) contacts, and \(t_{j}=0,2\) are already excluded; the inverse projective row norms are 3 and 7. If \(h(t_{j})>\log 7\), multiply the two inequalities for \(h(t_{j})-\log 7\). Outside \(\Sigma \) the two block radicals are disjoint and their product is exactly \(M_{j}\), giving \(h(t_{j})\le H_{2}\) \(M_{j}^{7/6}\), \(H_{2}=\log 7+H\). If \(h(t_{j})\le \log 7\) it follows directly, including \(t_{j}=1\) with \(M_{j}=1\). Thus the argument covers the full rational solution domain, not a bounded example. Because \(t_{0}\ne 0\) and \(t_{1}=Tt_{0}\), \(h(T)\le h(t_{0})+h(t_{1})\). If \(M_{j}^{k}\) divides the same nonzero integer \(J_{0}\) separately for both \(j\), then

 \begin{gather*}
 B^{2} \le  C |J_{0}|^{7/(6k)}+M_{2}, C=2 M_{1} H_{2}
```

### H013

Class: prose, notation or text-conversion cleanup; inspect both sides. Base 2294-2306; candidate 2289-2301.

```diff
@@ -2294,13 +2289,13 @@

 This is the source-to-physical-radical join; no product divisibility between scales is asserted.

-[P11: a single soundness threshold] The actual scalar-S/four-contact argument gives \(c>0\), \(c\ge 149^{{L}_{N}}\) and \(h(\beta )\le C_{3}*149^{-{L}_{N}}*c(1+\operatorname{log}(c)/3)\), \(C_{3}=2^{330770}\), \(L_{N}=\text{floor}(9(2N-1)/4)+1\). This uses \(c=|a|\), not |a-1|. For \(\Delta \ne 0\), P07/P10 imply \(B^{2}\le D\) \(B^{14/9}+M_{2}\) where \(D=C*14^{7/18}\). Hence \(B\le K_{D}=\operatorname{max}(\sqrt{2M_{2}},(2D)^{9/4}):\) when \(B^{2}>2M_{2}\), move \(M_{2}\) and divide by \(B^{14/9}\), obtaining \(B^{4/9}<2D\). Choose \(N_{D}\) so \(149^{{L}_{N}}>K_{D}\) for all \(N\ge N_{D}\). This is possible by monotonicity and excludes \(\Delta \ne 0\) uniformly in every \(x\) and every solution.
+[P11: a single soundness threshold] The actual scalar-S/four-contact argument gives \(c>0\), \(c\ge 149^{{L}_{N}}\) and \(h(\beta )\le C_{3}\cdot 149^{-{L}_{N}}\cdot c(1+\operatorname{log}(c)/3)\), \(C_{3}=2^{330770}\), \(L_{N}=\left\lfloor 9(2N-1)/4\right\rfloor+1\). This uses \(c=|a|\), not |a-1|. For \(\Delta \ne 0\), P07/P10 imply \(B^{2}\le D\) \(B^{14/9}+M_{2}\) where \(D=C\cdot 14^{7/18}\). Hence \(B\le K_{D}=\operatorname{max}(\sqrt{2M_{2}},(2D)^{9/4}):\) when \(B^{2}>2M_{2}\), move \(M_{2}\) and divide by \(B^{14/9}\), obtaining \(B^{4/9}<2D\). Choose \(N_{D}\) so \(149^{{L}_{N}}>K_{D}\) for all \(N\ge N_{D}\). This is possible by monotonicity and excludes \(\Delta \ne 0\) uniformly in every \(x\) and every solution.

-[P12: Lucas lower bound and input threshold] With \(\Delta =0\) and a,t,b nonzero, set \(A_{0}=|a|=c\) and \(w=\text{sign}(a)(a-2)b\). Then \(t^{2}-c*t*w+w^{2}=1\). The elementary norm-one unit reduction in \(Z[(c+\sqrt{c^2-4})/2]\) gives \(|w|=U_{j}\) and |t| in \(\{U_{j-1},U_{j+1}\}\), where \(U_{0}=0,U_{1}=1,U_{j+1}=cU_{j}-U_{j-1}\). Nonzero \(w\) excludes \(j=0\). Reduction modulo c-2 \((if a>0)\) or c+2 \((if a<0)\), together with |a-2| dividing \(w\), gives \(j\ge c-2\). Induction gives \(U_{j}\ge (c-1)^{j-1}\); hence for \(c\ge 8\) the weaker bound log \(B\ge (c-5)\operatorname{log}(c-2)\) holds. If \(J\ne 0\) and \(B^{2}\ge 2M_{2}\), \(P_{10}\) at \(k=1\) gives
+[P12: Lucas lower bound and input threshold] With \(\Delta =0\) and a,t,b nonzero, set \(A_{0}=|a|=c\) and \(w=\text{sign}(a)(a-2)b\). Then \(t^{2}-c\cdot t\cdot w+w^{2}=1\). The elementary norm-one unit reduction in \(Z[(c+\sqrt{c^2-4})/2]\) gives \(|w|=U_{j}\) and |t| in \(\{U_{j-1},U_{j+1}\}\), where \(U_{0}=0,U_{1}=1,U_{j+1}=cU_{j}-U_{j-1}\). Nonzero \(w\) excludes \(j=0\). Reduction modulo c-2 \((if a>0)\) or c+2 \((if a<0)\), together with |a-2| dividing \(w\), gives \(j\ge c-2\). Induction gives \(U_{j}\ge (c-1)^{j-1}\); hence for \(c\ge 8\) the weaker bound log \(B\ge (c-5)\operatorname{log}(c-2)\) holds. If \(J\ne 0\) and \(B^{2}\ge 2M_{2}\), \(P_{10}\) at \(k=1\) gives

 \begin{gather*}
 \operatorname{log} B \le  K + \epsilon _{N} c(1+\operatorname{log}(c)/3),\\
-K=(6/5)\operatorname{log}(2C)+(7/5)\log 2, \epsilon _{N}=(7/5)C_{3}*149^{-{L}_{N}}
+K=(6/5)\operatorname{log}(2C)+(7/5)\log 2, \epsilon _{N}=(7/5)C_{3}\cdot 149^{-{L}_{N}}
 \end{gather*}

 Choose \(N_{e}\) so \(\epsilon _{N}\le 1\) for every \(N\ge N_{e}\). Put \(K_{c}=\operatorname{max}(\operatorname{exp}(12),2\operatorname{max}(K,0)+1,8,\sqrt{2M_{2}}+1)\). For \(c\ge K_{c}\),
```

### H014

Class: whitespace only. Base 2310-2316; candidate 2305-2311.

```diff
@@ -2310,7 +2305,7 @@
 \ge  c[(\operatorname{log} c)/6-1-(\log 2)/2] > c/2 > K
 \end{gather*}

-Here \(c-5\ge c/2\) and \(c-2\ge c/2\) hold. Choose \(N_{c}\) so \(149^{{L}_{N}}\ge K_{c}\) for every \(N\ge N_{c}\). Then \(J\ne 0\) is impossible. Thus \(n=\beta \) is integral. Writing \(x=u/v\) reduced with \(v>0\), integrality forces \(v^{2}|51\); since51 is squarefree, \(v=1\). The same fixed \(N_{S}=\operatorname{max}(N_{D},N_{e},N_{c})\) works for every rational input and all solutions at every \(N\ge N_{S}\). This construction is existential, and \(K_{D},K_{c}\) depend on the ineffective \(M_{2}\).
+Here \(c-5\ge c/2\) and \(c-2\ge c/2\) hold. Choose \(N_{c}\) so \(149^{{L}_{N}}\ge K_{c}\) for every \(N\ge N_{c}\). Then \(J\ne 0\) is impossible. Thus \(n=\beta \) is integral. Writing \(x=u/v\) reduced with \(v>0\), integrality forces \(v^{2}|51\); since 51 is squarefree, \(v=1\). The same fixed \(N_{S}=\operatorname{max}(N_{D},N_{e},N_{c})\) works for every rational input and all solutions at every \(N\ge N_{S}\). This construction is existential, and \(K_{D},K_{c}\) depend on the ineffective \(M_{2}\).

 [P13: uniform scalar completeness threshold] For integer \(x\), the retained four-factor scalar \(r_{4}=\beta (\beta -1)(\beta -2401)(32\beta +343)\) is an \(\text{ integer } \ge 1\). With \(R_{s}=A_{N}\) \(r_{4}/(1+149^{2} r_{4})\), one has \(R_{s}\ge A_{N}/(1+149^{2})\), independently of \(x\). Choose the fixed compact real neighborhoods from the scalar-S proof before finite progression moduli; on them Z0,Z1,F are bounded by constants \(M_{Z},M_{F}\) independent of x,N. The actual parity-normalized scalar is

```

### H015

Class: star-subscript spelling and surrounding prose; same mathematical symbol. Base 2321-2333; candidate 2316-2328.

```diff
@@ -2321,13 +2316,13 @@

 For \(R_{s}\ge 1\), \(W_{s}\le K_{W}\) \(R_{s}^{-4}\), \(K_{W}=M_{Z}^{4}+M_{Z}^{2}+M_{F}^{2}\), so \(0<b_{s}\le 9793\) \(K_{W}^{2}\) \(R_{s}^{-6}\). Choose a fixed \(N_{C}\) so the right side \(\text{ is } <17\) for every \(N\ge N_{C}\). This is uniform in the integer input. \(F\ne 0\) and real positivity exclude \(b_{s}=0\). The neighborhoods and constants are those of the original scalar functions, before the later root-label-dependent comparison neighborhoods; the latter need no bound uniform in labels.

-[P14: scalar finite preparation in correct order] For a particular x,N, put \(D_{s}=1+149^{2}\) \(r_{4}\). Both \(\text{gcd}(A_{N} r_{4},D_{s})\) and \(\text{gcd}(A_{N} r_{4}+9792D_{s},D_{s})\) equal1; thus \(R_{s}(R_{s}+9792)\) has square reduced denominator \(D_{s}^{2}\). Direct integer parity/congruences give \(v_{2}(R_{s})\) in \{2,3\} and \(v_{3}(R_{s})=v_{17}(R_{s})=0\). Hence \(1+9792/R_{s}\) is a square at2,3,17 \((\text{its} \text{difference} \text{from}1 \text{has} \operatorname{depth}\ge 3,\ge 1,\ge 1 \text{ respectively } )\), so \(R_{s}(R_{s}+9792)\) is a square there. At its finite odd-valuation numerator support choose an initial \(H\) formal enough; then choose the positive scalar index a still deeper and arbitrarily large, with [a]P in the fixed real neighborhood of \(O\). This makes the three terms of \(W_{s}\) integral at that support and deep enough at2,3,17 for the actual zero-preparation pole bounds. Compact-group recurrence in finite-index progressions gives the finite and real conditions together. After a is fixed, continuity preserves the scalar conditions for \(H\) in one progression \(h=h_{*}\) mod \(L\), \(\text{ with } 64|h_{*},64|L\) and the component-order divisibility included. This ordering permits support and depth to depend on x,N; the common \(N_{C}\) does not. The retained scalar/root chart guards hold on the chosen neighborhoods. No new condition \(a=1\) mod any modulus is imposed.
+[P14: scalar finite preparation in correct order] For a particular x,N, put \(D_{s}=1+149^{2}\) \(r_{4}\). Both \(\text{gcd}(A_{N} r_{4},D_{s})\) and \(\text{gcd}(A_{N} r_{4}+9792D_{s},D_{s})\) equal 1; thus \(R_{s}(R_{s}+9792)\) has square reduced denominator \(D_{s}^{2}\). Direct integer parity/congruences give \(v_{2}(R_{s})\) in \{2,3\} and \(v_{3}(R_{s})=v_{17}(R_{s})=0\). Hence \(1+9792/R_{s}\) is a square at 2,3,17 \((\text{its} \text{difference} \text{from}1 \text{has} \operatorname{depth}\ge 3,\ge 1,\ge 1 \text{ respectively } )\), so \(R_{s}(R_{s}+9792)\) is a square there. At its finite odd-valuation numerator support choose an initial \(H\) formal enough; then choose the positive scalar index a still deeper and arbitrarily large, with [a]P in the fixed real neighborhood of \(O\). This makes the three terms of \(W_{s}\) integral at that support and deep enough at 2,3,17 for the actual zero-preparation pole bounds. Compact-group recurrence in finite-index progressions gives the finite and real conditions together. After a is fixed, continuity preserves the scalar conditions for \(H\) in one progression \(h=h_{*}\) mod \(L\), \(\text{ with } 64|h_{*},64|L\) and the component-order divisibility included. This ordering permits support and depth to depend on x,N; the common \(N_{C}\) does not. The retained scalar/root chart guards hold on the chosen neighborhoods. No new condition \(a=1\) mod any modulus is imposed.

-[P15: root labels, coefficients and incidences] Put \(n=\beta \). For the chosen positive \(a\ge 3\) choose \(j>0\) divisible by a-2; with the same Lucas recurrence put \(b=U_{j}/(a-2)\) and \(t=U_{j+1}\). Then n,a,t,b are positive nonzero integers and \(\Delta =0\). Fix their four root points and \(T>0\). Fix compact real neighborhoods for \(H\) and all comparison rational functions avoiding their denominators and chart guards. These neighborhoods may depend on the fixed labels. Enlarge the finite preparation set to contain \(\Sigma \), scale numerator/denominator primes, scalar-support primes and fixed guards. Choose \(D>0\) so all numbers \(D^{2}\) \(\theta /a_{*}\) are integers for \(a_{*}\) in \{1,T\}, \(\theta \) in \(\Theta _{2}\), and so \(v_{p}(a_{*}\lambda )<0\) with the needed depth at every prepared \(p\) when \(\lambda =u/(D^{2} w^{2})\). Use coefficients \(c_{a_{*},\theta }=-D^{2}\) \(\theta /a_{*}\); merge equal coefficients \textbf{across} detectors, retaining each incidence. Within a detector distinct \(\theta \) give distinct coefficients; at least ten distinct coefficients remain. The zero contact supplies coefficient0 and the prime \(u\). This is exactly the old center-two pattern.
+[P15: root labels, coefficients and incidences] Put \(n=\beta \). For the chosen positive \(a\ge 3\) choose \(j>0\) divisible by a-2; with the same Lucas recurrence put \(b=U_{j}/(a-2)\) and \(t=U_{j+1}\). Then n,a,t,b are positive nonzero integers and \(\Delta =0\). Fix their four root points and \(T>0\). Fix compact real neighborhoods for \(H\) and all comparison rational functions avoiding their denominators and chart guards. These neighborhoods may depend on the fixed labels. Enlarge the finite preparation set to contain \(\Sigma \), scale numerator/denominator primes, scalar-support primes and fixed guards. Choose \(D>0\) so all numbers \(D^{2}\) \(\theta /a_{*}\) are integers for \(a_{*}\) in \{1,T\}, \(\theta \) in \(\Theta _{2}\), and so \(v_{p}(a_{*}\lambda )<0\) with the needed depth at every prepared \(p\) when \(\lambda =u/(D^{2} w^{2})\). Use coefficients \(c_{a_{*},\theta }=-D^{2}\) \(\theta /a_{*}\); merge equal coefficients \textbf{across} detectors, retaining each incidence. Within a detector distinct \(\theta \) give distinct coefficients; at least ten distinct coefficients remain. The zero contact supplies coefficient 0 and the prime \(u\). This is exactly the old center-two pattern.

-[P16: prime theorem quantifiers and CRT] Apply the actual \(V_{15}\) simultaneous-prime theorem to this fixed list, prescribed divisibility q|w, fixed avoidance modulus \(M=\operatorname{rad}_{\text{odd}}(3*17*L)\) with7 omitted, and arbitrarily large slope/prime lower bounds. Choose these data before the analytic asymptotic parameter \((\text{call} it X_{\text{sel}}, \text{distinct} \text{from} \text{input} x)\). Its fixed-field proof first fixes the cutoff so positive cutoff mass exceeds the full obstruction tail, then fixes the ray field, then lets \(X_{\text{sel}}\) grow along sufficiently slow diagonal strip widths. No uniform estimate in x,N,T,D,L or number of contacts is needed. The selected Gaussian generators have residues9 mod16,1+3i mod7,i modM; adjacent norms \(d_{\text{minus}},d_{\text{plus}}\) have \(v_{2}=6,2\) and cross-sign gcd4, and all odd factors avoid \(L\). Define \(U=\text{lcm}(d_{\text{minus}}/4)\), \(V=\text{lcm}(d_{\text{plus}}/4)\). Full two-torsion makes d/4 kill the reduction of the double \(P\); \(\text{gcd}(U,V)=1\), \(\text{gcd}(U,L)=16\) and \(\text{gcd}(V,L)=1\). Thus \(h=0\) mod \(U\), \(h=1\) mod \(V\), \(h=h_{*}\) mod \(L\) are compatible. The real progression lemma gives arbitrarily large \(h\) in the original fixed compact neighborhoods. Set \(H=[h]P\), \(U_{i}=[hn_{i}]P\), \(V_{i}=[(h-1)n_{i}]P\). This gives natural formal \(\operatorname{depth}\ge 1\) at the correct primary/opposite places and preserves the scalar data. The optional strengthened separation \(p_{i}\) not dividing \(d_{j}\) is available from the weighted strip argument; natural depth1 alone suffices for this 214 construction. Every merged repeated coefficient carries one prime/generator and all its incidences; CRT is imposed once and supplies all those incidences.
+[P16: prime theorem quantifiers and CRT] Apply the actual \(V_{15}\) simultaneous-prime theorem to this fixed list, prescribed divisibility q|w, fixed avoidance modulus \(M=\operatorname{rad}_{\text{odd}}(3\cdot 17\cdot L)\) with 7 omitted, and arbitrarily large slope/prime lower bounds. Choose these data before the analytic asymptotic parameter \((\text{call} it X_{\text{sel}}, \text{distinct} \text{from} \text{input} x)\). Its fixed-field proof first fixes the cutoff so positive cutoff mass exceeds the full obstruction tail, then fixes the ray field, then lets \(X_{\text{sel}}\) grow along sufficiently slow diagonal strip widths. No uniform estimate in x,N,T,D,L or number of contacts is needed. The selected Gaussian generators have residues 9 mod 16,1+3i mod 7,i modM; adjacent norms \(d_{-},d_{+}\) have \(v_{2}=6,2\) and cross-sign gcd 4, and all odd factors avoid \(L\). Define \(U=\text{lcm}(d_{-}/4)\), \(V=\text{lcm}(d_{+}/4)\). Full two-torsion makes d/4 kill the reduction of the double \(P\); \(\text{gcd}(U,V)=1\), \(\text{gcd}(U,L)=16\) and \(\text{gcd}(V,L)=1\). Thus \(h=0\) mod \(U\), \(h=1\) mod \(V\), \(h=h_*\) mod \(L\) are compatible. The real progression lemma gives arbitrarily large \(h\) in the original fixed compact neighborhoods. Set \(H=[h]P\), \(U_{i}=[hn_{i}]P\), \(V_{i}=[(h-1)n_{i}]P\). This gives natural formal \(\operatorname{depth}\ge 1\) at the correct primary/opposite places and preserves the scalar data. The optional strengthened separation \(p_{i}\) not dividing \(d_{j}\) is available from the weighted strip argument; natural depth 1 alone suffices for this 214 construction. Every merged repeated coefficient carries one prime/generator and all its incidences; CRT is imposed once and supplies all those incidences.

-[P17: changed factors at the actual fresh witnesses] At any selected contact \(p\), the slope and prime cutoff make \(p\) avoid D,w and both scale supports; selected primes are distinct and larger than \(w^{2}\). Thus exactly its indicated contact numerator has depth1 in each incident detector, \(\delta \) is a unit, \(v(q)=-1\), every reciprocal test has \(\operatorname{depth}\ge 2\), and every \(C_{i},I,G\) has \(\operatorname{depth}\ge 4\) by the full ratios \(n_{i}\) and relative formal error4. The changed factor terms have minimal depths \(q^{5}\) \(C_{i}^{2}:3\); \(q^{5}\) \(I^{4}:11\); \(q^{3}\) \(A_{2}^{2}:1\); \(q^{2}\) \(D_{H}^{2}\) or \(q^{2}\) \(A_{i}^{2}:2\); \(q^{2}\) \(C_{1}^{4}:14\); \(q^{4}\) \(B_{i}^{4}:4\). Therefore \(W=1\) mod the selected place. At the opposite place the \(P_{05}\) residue argument applies without a formalness assumption: \(W^{-1}\) reduces to0 or1, so \(\operatorname{Tr}(W^{-1})\) reduces to1 or2, a unit since \(p\) is odd. The new actual pole input \(\mathfrak{b}\) has valuation1 there. This is a fresh order-three-factor proof, not an appeal to the old order-four conclusion.
+[P17: changed factors at the actual fresh witnesses] At any selected contact \(p\), the slope and prime cutoff make \(p\) avoid D,w and both scale supports; selected primes are distinct and larger than \(w^{2}\). Thus exactly its indicated contact numerator has depth 1 in each incident detector, \(\delta \) is a unit, \(v(q)=-1\), every reciprocal test has \(\operatorname{depth}\ge 2\), and every \(C_{i},I,G\) has \(\operatorname{depth}\ge 4\) by the full ratios \(n_{i}\) and relative formal error 4. The changed factor terms have minimal depths \(q^{5}\) \(C_{i}^{2}:3\); \(q^{5}\) \(I^{4}:11\); \(q^{3}\) \(A_{2}^{2}:1\); \(q^{2}\) \(D_{H}^{2}\) or \(q^{2}\) \(A_{i}^{2}:2\); \(q^{2}\) \(C_{1}^{4}:14\); \(q^{4}\) \(B_{i}^{4}:4\). Therefore \(W=1\) mod the selected place. At the opposite place the \(P_{05}\) residue argument applies without a formalness assumption: \(W^{-1}\) reduces to 0 or 1, so \(\operatorname{Tr}(W^{-1})\) reduces to 1 or 2, a unit since \(p\) is odd. The new actual pole input \(\mathfrak{b}\) has valuation 1 there. This is a fresh order-three-factor proof, not an appeal to the old order-four conclusion.

 [P18: all other primes and completions] For each physical scale \(a_{*}\), the exact identity is

```

### H016

Class: status, source locator or provenance prose. Base 2336-2380; candidate 2331-2375.

```diff
@@ -2336,45 +2331,45 @@
 [(D^{2} w^{2})^{10} \delta ^{10}]
 \end{gather*}

-Every non-prime factor here is a rational square, including \(a_{*}^{10}\) for a nonsquare scale; each contact coefficient occurs once within a detector. Hence outside its selected prime numerators, \(v_{p}(R)\) is even. This includes primes dividing \(\delta \). Multiplication by \(\gamma ^{2}\) and division by the squared trace preserve that parity. At prepared \(p\), \(D\) and the fixed divisibility q|w make \(R=\prod _{\theta }(1+(1-\theta )/\delta )\) as close to1 as needed and the weight \(q=R^{-1}-1\) arbitrarily small. All positive exponents in the changed factors therefore make test terms small there uniformly on the fixed p-adic neighborhoods, and \(\operatorname{Tr}(W^{-1})\) is close to2. Choose closeness so \(R\) is a square at2,3,17. As \(v_{2}(\gamma )=3\) and \(v_{3}(\gamma )=v_{17}(\gamma )=1\), the actual pole input is a local square with depths4,2,2. At both real embeddings, as \(\lambda \) grows on the fixed neighborhoods, \(R=\prod _{r=1}^{5}(1-\alpha _{r}/\delta ^{2})\), \(\alpha _{r}>0\), so \(q>0\) tends to0; all factors are positive and \(W\) tends to1. Thus \(\mathfrak{b}\) tends to \(\gamma ^{2}/4\) in(0,17). The prime theorem permits an arbitrarily high fixed slope after these neighborhoods are chosen. This proves positivity and a nonzero trace globally, and \(q_{0},q_{1}>0\) so all new inverse weights exist.
+Every non-prime factor here is a rational square, including \(a_{*}^{10}\) for a nonsquare scale; each contact coefficient occurs once within a detector. Hence outside its selected prime numerators, \(v_{p}(R)\) is even. This includes primes dividing \(\delta \). Multiplication by \(\gamma ^{2}\) and division by the squared trace preserve that parity. At prepared \(p\), \(D\) and the fixed divisibility q|w make \(R=\prod _{\theta }(1+(1-\theta )/\delta )\) as close to 1 as needed and the weight \(q=R^{-1}-1\) arbitrarily small. All positive exponents in the changed factors therefore make test terms small there uniformly on the fixed p-adic neighborhoods, and \(\operatorname{Tr}(W^{-1})\) is close to 2. Choose closeness so \(R\) is a square at 2,3,17. As \(v_{2}(\gamma )=3\) and \(v_{3}(\gamma )=v_{17}(\gamma )=1\), the actual pole input is a local square with depths 4,2,2. At both real embeddings, as \(\lambda \) grows on the fixed neighborhoods, \(R=\prod _{r=1}^{5}(1-\alpha _{r}/\delta ^{2})\), \(\alpha _{r}>0\), so \(q>0\) tends to 0; all factors are positive and \(W\) tends to 1. Thus \(\mathfrak{b}\) tends to \(\gamma ^{2}/4\) in (0,17). The prime theorem permits an arbitrarily high fixed slope after these neighborhoods are chosen. This proves positivity and a nonzero trace globally, and \(q_{0},q_{1}>0\) so all new inverse weights exist.

-[P19: actual pole theorem and its curve domain] The input just constructed has square reduced \(\text{denominator},0<\mathfrak{b}<17\), local squares at2,3,17 and depths4,2,2, meeting the exact preparation-zero predicate Psi0 (source requires3,1,2). In its proof set \(B_{\text{pole}}=17\mathfrak{b}\) and \(V_{\text{pole}}=B_{\text{pole}}^{2}(1-\mathfrak{b}/17)\). The positive squarefree representatives mu,theta have disjoint support avoiding2,3, \(\mu =17\) \(\text{mod}24,\theta =1\) mod24, mutual local squareness, and \(\theta \) may equal1. The simultaneous-descent lemma constructs positive squarefree \(n_{\text{pole}},n_{\text{pole}}\) \(\theta \), both11 mod12 and with full2-primary Selmer corank1; this uses full Selmer corank, including divisible Sha, before any finiteness claim. The retained RC is for \(E_{l}:y^{2}=x(x-l)(x+3l)\), \(l>0\) \(\text{ squarefree } ,l=11\) mod12. These curves have \(j=35152/9\), are non-CM, and are distinct from the CM index curve E/K. RC is applied separately to these exact two parameters; no constants uniform in them are required. The published forward analytic-rank-one input then gives rank1 and finite Sha, and Kummer gives points with the required nonzero abscissa class. The zero-preparation proof explicitly rescales those two points to produce e,p,q,s for this actual new input. Distinct detector certificates have independent structural coordinates and can be chosen separately after both inputs are fixed. Zero auxiliary witnesses remain allowed, and the finite conic/support charts include those branches. The later CRT or prime choices are not revisited.
+[P19: actual pole theorem and its curve domain] The input just constructed has square reduced \(\text{denominator},0<\mathfrak{b}<17\), local squares at 2,3,17 and depths 4,2,2, meeting the exact preparation-zero predicate Psi0 (source requires 3,1,2). In its proof set \(B_{\text{pole}}=17\mathfrak{b}\) and \(V_{\text{pole}}=B_{\text{pole}}^{2}(1-\mathfrak{b}/17)\). The positive squarefree representatives mu,theta have disjoint support avoiding 2,3, \(\mu =17\) \(\text{mod}24,\theta =1\) mod 24, mutual local squareness, and \(\theta \) may equal 1. The simultaneous-descent lemma constructs positive squarefree \(n_{\text{pole}},n_{\text{pole}}\) \(\theta \), both 11 mod 12 and with full 2-primary Selmer corank 1; this uses full Selmer corank, including divisible Sha, before any finiteness claim. The retained RC is for \(E_{l}:y^{2}=x(x-l)(x+3l)\), \(l>0\) \(\text{ squarefree } ,l=11\) mod 12. These curves have \(j=35152/9\), are non-CM, and are distinct from the CM index curve E/K. RC is applied separately to these exact two parameters; no constants uniform in them are required. The published forward analytic-rank-one input then gives rank 1 and finite Sha, and Kummer gives points with the required nonzero abscissa class. The zero-preparation proof explicitly rescales those two points to produce e,p,q,s for this actual new input. Distinct detector certificates have independent structural coordinates and can be chosen separately after both inputs are fixed. Zero auxiliary witnesses remain allowed, and the finite conic/support charts include those branches. The later CRT or prime choices are not revisited.

-[P20: final quantifiers and limitations] For every \(N\ge N_{C}\) and every integer \(x\), P14-P19 construct rational witnesses (existentially) in the original physical system, with the changed factors and nonzero inverse weights. Reconstruct deleted fourth powers and apply the exact raw224 coordinate maps and Laurent row identities; this gives a rational zero of the fixed 214 residuals. That argument allows the labels, selected primes, finite moduli, slope, final \(h\) and pole certificates to depend on the given (N,x); it imposes no further lower bound on \(N\). Taking \(N_{0}=\operatorname{max}(N_{S},N_{C})\) combines this with P11-P12 for all larger \(N\) and every rational input, proving \(P_{01}\) relative to the explicitly retained interfaces. This author did \textbf{not} produce a full numerical 214 witness tuple, even for a sample input; no sample could establish universal completeness. This packet gives no numerical defining threshold, no Busy Beaver coefficient replacement, no independent acceptance of itself. Full Protocol \(D\) closure additionally requires the fresh eligible review and exact assembly of unchanged RC/analytic and height foundations, not a green structural check.
+[P20: final quantifiers and limitations] For every \(N\ge N_{C}\) and every integer \(x\), P14-P19 construct rational witnesses (existentially) in the original physical system, with the changed factors and nonzero inverse weights. Reconstruct deleted fourth powers and apply the exact raw 224 coordinate maps and Laurent row identities; this gives a rational zero of the fixed 214 residuals. That argument allows the labels, selected primes, finite moduli, slope, final \(h\) and pole certificates to depend on the given (N,x); it imposes no further lower bound on \(N\). Taking \(N_{0}=\operatorname{max}(N_{S},N_{C})\) combines this with P11-P12 for all larger \(N\) and every rational input, proving \(P_{01}\) relative to the explicitly retained interfaces. No full numerical 214 witness tuple is supplied, even for a sample input; no sample could establish universal completeness. No numerical defining threshold or Busy Beaver coefficient replacement is provided. The unchanged restricted-converse, analytic and height foundations remain separate prerequisites.
 \clearpage
 % Source: research/quartic214/proofs/geometry-carry.md
 \section{\(H_{01}:\) the actual \(D_{210}\) geometry and the small \(S_{10}\) application}\label{q214:geometry-carry}
 \noindent\textit{Source: }\nolinkurl{research/quartic214/proofs/geometry-carry.md}.\par

-Author supplement to \(\text{AUTHOR}_{{\text{FREEZE}}_{001}}\), \nolinkurl{/root/d214_modularity_closure}, 11 November 2026. Author proposal, pending nonauthor acceptance. This checks the actual earlier arguments and the changed application; it supplies no independent approval.
+

 \subsection{\(G_{0}\). Locator correction and exact scope}

-The suggested public SF08--10 locators concern modular curves, torsion differents and the modular-Jacobian estimate. They belong to \(H_{04}\), not \(H_{01}\). Public V15-HEIGHT-MODULAR accordingly supplies no \(D_{210}\) fine cover merely by accepting its modular curve. V15-FOUNDATION's third clause retains the original \textbf{six-contact} theorem; it is not by itself the five-contact \(D_{210}\) argument either. These are locator corrections, not new arithmetic objections.
+The suggested public SF08--10 locators concern modular curves, torsion differents and the modular-Jacobian estimate. They belong to \(H_{04}\), not \(H_{01}\). Public V15-HEIGHT-MODULAR accordingly supplies no \(D_{210}\) fine cover from its modular-curve assertion. V15-FOUNDATION's third clause retains the original \textbf{six-contact} theorem; it is not by itself the five-contact \(D_{210}\) argument either.

-There is a further distinction: H6-ORIGINAL-POLARIZED-QM-DATUM, H6-FINE-THREE-INTEGRAL-COVER and the \(B_{11}\) six-phase construction concern the discriminant-six surface, its auxiliary full-five model, and degree at most324. Reading their actual proofs exposed this difference. They must not be substituted for the discriminant210 \(H_{01}\) surface of degree576. A preliminary author message listing those \(H_{6}\) cards as if they were \(H_{01}\) providers was too broad. The actual providers are \nolinkurl{research/version14/proofs/h5-full-three-v1/PROOF.md}, its \nolinkurl{GEOMETRIC-ISOGENY.md} and parent \(D_{210}\) construction, together with the actual maximal-stack Yuan applications. Every assertion below concerns that \(D_{210}\) object.
+There is a further distinction: H6-ORIGINAL-POLARIZED-QM-DATUM, H6-FINE-THREE-INTEGRAL-COVER and the \(B_{11}\) six-phase construction concern the discriminant-six surface, its auxiliary full-five model, and degree at most 324. They must not be substituted for the discriminant 210 \(H_{01}\) surface of degree 576. The actual providers are \nolinkurl{research/version14/proofs/h5-full-three-v1/PROOF.md}, its \nolinkurl{GEOMETRIC-ISOGENY.md} and parent \(D_{210}\) construction, together with the actual maximal-stack Yuan applications. Every assertion below concerns that \(D_{210}\) object.

-The old private \(\text{FOUNDATION}_{\text{MAP}}\) F-H01-GEOMETRY already points to frozen \(V_{14}\) lines7605--8040 and8517--8655 and the cutoff proof. Its REPORT explicitly retains \(H_{01}\) source-closure limits; it does not identify the D6/B11 construction as proof of the \(D_{210}\) field. Thus the newly corrected locator suggestion is not an error in that old map. The old files remain untouched.
+The historical foundation map identifies the discriminant-210 construction and cutoff proof, with their source qualifications. It does not use the discriminant-six construction to supply that field.

 \subsection{\(G_{1}\). Exact text and retained public scopes}

-\nolinkurl{GEOMETRY_TEXT_COMPARISON.json} binds three actual sources: private frozen \(V_{14}\), the private frozen \(V_{15}\) copy consumed elsewhere in the 214 packet, and current public \(V_{15}\) at accepted PR26 head1a49013b. The full \(D_{210}\) integral-geometry, fine-cover, field, Hom, and metric passage is \(V_{14}\) lines7605--8020, \(V_{15}\) lines7737--8152. Private and public \(V_{15}\) have \textbf{byte-identical} passages, raw SHA256 \nolinkurl{d8cea4a2552c8e5af575145b5db0e802bd6d96ff80da2e5d561a7e7da7c302d5}. The \(V_{14}\) passage differs only by LF/CRLF; its LF hash is \nolinkurl{c300ad111a16296fd05fa7c560a354222307124173de6790fa1c7390e1c7cac8}. No mathematical whitespace normalization was used.
+\nolinkurl{GEOMETRY_TEXT_COMPARISON.json} binds three actual sources: private frozen \(V_{14}\), the private frozen \(V_{15}\) copy consumed elsewhere in the 214 packet, and current public \(V_{15}\) at PR26 head1a49013b. The full \(D_{210}\) integral-geometry, fine-cover, field, Hom, and metric passage is \(V_{14}\) lines7605--8020, \(V_{15}\) lines7737--8152. Private and public \(V_{15}\) have \textbf{byte-identical} passages, raw SHA256 \nolinkurl{d8cea4a2552c8e5af575145b5db0e802bd6d96ff80da2e5d561a7e7da7c302d5}. The \(V_{14}\) passage differs only by LF/CRLF; its LF hash is \nolinkurl{c300ad111a16296fd05fa7c560a354222307124173de6790fa1c7390e1c7cac8}. No mathematical whitespace normalization was used.

 The complete CM854R proof is \(V_{14}\) lines8519--8654 and \(V_{15}\) lines8618--8753. Private/public \(V_{15}\) are byte-identical, raw SHA256 \nolinkurl{42732844c948b234ba3820d2915b205aa0f909b1bdd0bd3d4fe8959fb0575412}; the LF content is the same as private \(V_{14}\). The CM supplier excerpt used by public inherited transport has SHA256 \nolinkurl{9abb3c65609362383a43ccbb463b2fc7dd4a6487c38be4c413f20bb1ed1fb02b}, equal to the private \(V_{14}\) raw excerpt when its terminal newline is included. This connects the actual proof, not merely its final inequality.

-\nolinkurl{PUBLIC_GEOMETRY_SCOPES.json} extracts the precise final006 coverage decisions for ACTIVE-H19-D210-FIBER-FIELD, ACTIVE-H19-D210-GEOMETRIC-ISOGENIES, ACTIVE-H19-CM-ELLIPTIC-DISCRIMINANT, ACTIVE-H19-CM-HEIGHT, ACTIVE-H19-CM-GR2023 and CURRENT-YUAN-MODEL/INTEGRAL/METRIC. These decisions reuse exact retained derivations and explicitly preserve their prerequisites. They are evidence of public acceptance at the recorded scope, not a newly authored approval of the private \(S_{10}\) application.
+The retained source statements cover the \(D_{210}\) fiber field and geometric isogenies, the CM elliptic discriminant, CM height and GR2023 comparison, and Yuan's model, integral and metric applications. Their stated prerequisites remain required for the \(S_{10}\) application.

-The actual full \(D_{210}\) source proof was read in full. It constructs \(\text{Isom}_{O}(O/3O,A[3])\), proving the division-lattice assertion at ramified3. It distinguishes stack marking degree72, coarse degree36 and normalizer order576; proves trivial inertia on arbitrary bases; obtains projectivity by the component/genus/relative-ampleness sequence; and identifies the entire canonical Q-model, all multipliers and both half-planes. It checks Milne's full Hodge-orbit condition directly instead of using the corrected general8.17 implication. Its integral statement is only over Z[1/210]. The metric proof uses Yuan's maximal stack at bad primes, not a smooth fine model there or the disputed coarse Lemma2.1/Theorem2.2.
+The \(D_{210}\) source proof constructs \(\text{Isom}_{O}(O/3O,A[3])\), proving the division-lattice assertion at ramified 3. It distinguishes stack marking degree 72, coarse degree 36 and normalizer order 576; proves trivial inertia on arbitrary bases; obtains projectivity by the component/genus/relative-ampleness sequence; and identifies the entire canonical Q-model, all multipliers and both half-planes. It checks Milne's full Hodge-orbit condition directly instead of using the corrected general 8.17 implication. Its integral statement is only over Z[1/210]. The metric proof uses Yuan's maximal stack at bad primes, not a smooth fine model there or the disputed coarse Lemma 2.1/Theorem 2.2.

-\nolinkurl{GEOMETRY_PROVIDER_COMPARISON.json} honestly records that these separately packaged supplier files were not found under the queried \nolinkurl{current/...} names in the old private handoff zip. No byte equality of an absent archive member is claimed. The \textbf{integrated proof text} equality above is established independently, and the actual publicly retained supplier is pinned and read. Its prior \(D_{210}\) index explicitly preserved five source-prerequisite bundles; public final006 acceptance preserves its exact source scope. This supplement does not infer resolution of any unexamined transitive prerequisite solely from that index or a PASS label.
+The source comparison establishes equality of the integrated proof text, without asserting byte equality for separately packaged files absent from the historical archive. The publicly retained \(D_{210}\) supplier has five source-prerequisite bundles. Those transitive prerequisites remain required; the index alone does not establish them.

 \subsection{\(G_{2}\). Same cover, field, Hom and surface for every allowed a}

-Let \(a=u/v\) be in lowest terms, \(v>0\), and a not in \{0,1,2401,-343/32\}. The omitted fifth contact is infinity. Choose the actual whole \(D_{210}\) full-three cover \(Y\) of the parent proof and its normalizer quotient line with precisely these five branch sections. The unbranched fiber at a is a torsor for the same constant group \(\Gamma \) of order576. Its commuting Galois action lies in the regular centralizer of \(\Gamma \), also of order576. The normal splitting field \(L\) therefore has degree \textbf{dividing}576. This argument depends on the same whole canonical cover and all-component rational action, not on the size of \(S\) or on a being integral.
+Let \(a=u/v\) be in lowest terms, \(v>0\), and a not in \{0,1,2401,-343/32\}. The omitted fifth contact is infinity. Choose the actual whole \(D_{210}\) full-three cover \(Y\) of the parent proof and its normalizer quotient line with precisely these five branch sections. The unbranched fiber at a is a torsor for the same constant group \(\Gamma \) of order 576. Its commuting Galois action lies in the regular centralizer of \(\Gamma \), also of order 576. The normal splitting field \(L\) therefore has degree \textbf{dividing}576. This argument depends on the same whole canonical cover and all-component rational action, not on the size of \(S\) or on a being integral.

-All fiber3-torsion markings are defined over that \(L\). For any pair of the fiber surfaces, a homomorphism vanishing on3-torsion factors through[3]. Thus Hom/3Hom injects into \(\operatorname{Hom}(A[3],B[3])\). The finite Galois image on the integral Hom lattice is trivial modulo3, and the principal congruence subgroup mod3 is torsion-free; therefore the image is trivial. Every geometric Hom between actual conjugate surfaces is L-defined. The normalizer changes a commensurable integral lattice while retaining the rational Hodge object. Clearing denominators gives a geometric isogeny between the actual conjugate surfaces. The full Hodge-centralizer calculation gives \(\operatorname{End}^{0}(A)=B\) in the non-CM branch and the CM alternative otherwise. This is exactly the input of M0--M2, with no replacement surface or extra Hom field.
+All fiber3-torsion markings are defined over that \(L\). For any pair of the fiber surfaces, a homomorphism vanishing on3-torsion factors through[3]. Thus Hom/3Hom injects into \(\operatorname{Hom}(A[3],B[3])\). The finite Galois image on the integral Hom lattice is trivial modulo 3, and the principal congruence subgroup mod 3 is torsion-free; therefore the image is trivial. Every geometric Hom between actual conjugate surfaces is L-defined. The normalizer changes a commensurable integral lattice while retaining the rational Hodge object. Clearing denominators gives a geometric isogeny between the actual conjugate surfaces. The full Hodge-centralizer calculation gives \(\operatorname{End}^{0}(A)=B\) in the non-CM branch and the CM alternative otherwise. This is exactly the input of M0--M2, with no replacement surface or extra Hom field.

-None of these statements uses \(B_{*}=\prod _{p\le 76176}p\), the old exponent19, the large-primorial inequality or the scalar character chosen later. Their complete proofs are the same in private frozen \(V_{15}\) and current public \(V_{15}\).
+None of these statements uses \(B_{*}=\prod _{p\le 76176}p\), the old exponent 19, the large-primorial inequality or the scalar character chosen later. Their complete proofs are the same in private frozen \(V_{15}\) and current public \(V_{15}\).

 \subsection{\(G_{3}\). Fresh support extension to \(S_{10}\), with all contact cases}

```

### H017

Class: status, source locator or provenance prose. Base 2390-2420; candidate 2385-2415.

```diff
@@ -2390,31 +2385,31 @@
 -1,-1,-1,-32,-1,-2401,343,-2400,375,77175
 \end{gather*}

-The nonunit factorizations are \(32=2^{5}\), \(2401=7^{4}\), \(343=7^{3}\), \(2400=2^{5}*3*5^{2}\), \(375=3*5^{3}\), \(77175=3^{2}*5^{2}*7^{3}\). Hence the \textbf{exact union} of their prime supports is \{2,3,5,7\}, contained in \(S_{10}\) and inverted in Z[1/210]. \nolinkurl{SMALL_SUPPORT_CERTIFICATE.json} gives every pair, coefficient vector and factorization. This finite calculation establishes distinct reductions and unit leading coefficients, not the arithmetic theorem by itself.
+The nonunit factorizations are \(32=2^{5}\), \(2401=7^{4}\), \(343=7^{3}\), \(2400=2^{5}\cdot 3\cdot 5^{2}\), \(375=3\cdot 5^{3}\), \(77175=3^{2}\cdot 5^{2}\cdot 7^{3}\). Hence the \textbf{exact union} of their prime supports is \{2,3,5,7\}, contained in \(S_{10}\) and inverted in Z[1/210]. \nolinkurl{SMALL_SUPPORT_CERTIFICATE.json} gives every pair, coefficient vector and factorization. This finite calculation establishes distinct reductions and unit leading coefficients, not the arithmetic theorem by itself.

 Define \(M\) to contain once every \(p\) outside \(S_{10}\) having positive odd valuation on any one of those five forms, and \(R=B_{S}\) \(M\), with \(B_{S}=\prod _{p \in  S_{10}}p\). For each \(p\) outside \(S_{10}\), primitiveness covers every case:

 \begin{itemize}
-\item If p|v, then \(p\) does not divide \(u\), and the other four forms are units because32 is a p-unit. The specialization is the infinity section. Its contact depth is \(v_{p}(v)\), since \(u\) is a unit.
-\item If \(p\) does not divide \(v\), a is p-integral. The determinant calculation shows that at most one finite-contact form can have positive valuation. Its valuation is exactly the contact depth of a with that branch section: all \(v\) and32 denominators are p-units.
+\item If p|v, then \(p\) does not divide \(u\), and the other four forms are units because 32 is a p-unit. The specialization is the infinity section. Its contact depth is \(v_{p}(v)\), since \(u\) is a unit.
+\item If \(p\) does not divide \(v\), a is p-integral. The determinant calculation shows that at most one finite-contact form can have positive valuation. Its valuation is exactly the contact depth of a with that branch section: all \(v\) and 32 denominators are p-units.
 \item If no form has positive valuation, the point lies in the unbranched locus.
 \end{itemize}

-Thus if \(p\) does not divide \(R\), every contact depth that occurs is even, including infinity. The retained actual tame model has local equation \(w=z^{2}\) up to a unit at a branch section and is etale elsewhere. Over a finite unramified extension the unit has a square root (p is odd), and an even valuation has square uniformizer factor. Each such local fiber is therefore unramified. The entire normal fiber splitting field is consequently unramified: finite unramified local extensions and their normal closure remain unramified. This proves \(\operatorname{rad}(D_{L})|R\) for this \textbf{new} \(R\), with no cutoff76176 hypothesis.
+Thus if \(p\) does not divide \(R\), every contact depth that occurs is even, including infinity. The retained actual tame model has local equation \(w=z^{2}\) up to a unit at a branch section and is etale elsewhere. Over a finite unramified extension the unit has a square root (p is odd), and an even valuation has square uniformizer factor. Each such local fiber is therefore unramified. The entire normal fiber splitting field is consequently unramified: finite unramified local extensions and their normal closure remain unramified. This proves \(\operatorname{rad}(D_{L})|R\) for this \textbf{new} \(R\), with no cutoff 76176 hypothesis.

-The same projective fine cover over Z[1/210] and its universal abelian scheme give good reduction of each A/L at all places not over210, irrespective of whether L/Q itself ramifies there. Properness extends the L-point over the valuation ring; pullback of the universal abelian scheme supplies the reduction. In particular the support assertion needed by \(H_{0}\) is valid for this smaller \(S_{10}\). This does not infer the cover or its tame charts from the determinant table: both are the actual retained \(D_{210}\) constructions read above.
+The same projective fine cover over Z[1/210] and its universal abelian scheme give good reduction of each A/L at all places not over 210, irrespective of whether L/Q itself ramifies there. Properness extends the L-point over the valuation ring; pullback of the universal abelian scheme supplies the reduction. In particular the support assertion needed by \(H_{0}\) is valid for this smaller \(S_{10}\). This does not infer the cover or its tame charts from the determinant table: both are the actual retained \(D_{210}\) constructions read above.

-The changed application is precisely this support sharpening from the old \(R_{*}=B_{*}\) \(M_{5}(a)\) to \(R=B_{S}\) \(M_{S}(a)\). One cannot obtain it by substituting a smaller \(R\) into an inequality proved only with the old radical. The explicit local case argument supplies the needed extension. It applies to \textbf{all} rational a in the stated domain, including denominators, negative a, \(M=1\), \(p\) in \(S_{10}\) but larger than7, and arbitrarily deep contacts. Primes in \(S_{10}\) impose no asserted local unramified condition and are already in \(R\).
+The changed application is precisely this support sharpening from the old \(R_{*}=B_{*}\) \(M_{5}(a)\) to \(R=B_{S}\) \(M_{S}(a)\). One cannot obtain it by substituting a smaller \(R\) into an inequality proved only with the old radical. The explicit local case argument supplies the needed extension. It applies to \textbf{all} rational a in the stated domain, including denominators, negative a, \(M=1\), \(p\) in \(S_{10}\) but larger than 7, and arbitrarily deep contacts. Primes in \(S_{10}\) impose no asserted local unramified condition and are already in \(R\).

 \subsection{\(G_{4}\). Metric and CM consumers of that exact field}

-The metric comparison is independent of \(S\). On the same maximal \(D_{210}\) stack use \(t=32a\), branch values(0,32,76832,-343), sections \(q_{0}=(dt)^{2}/P(t),q_{1}=tq_{0}\), and \(J=2^{10}*3^{2}*5^{3}*7^{4}\). The actual proof extends \(J^{2}q_{i}\) vertically on the stack using semistability and controls their Petersson norms \(by4C_{\text{met}}\). Yuan's final isometry and the original stable normalization give
+The metric comparison is independent of \(S\). On the same maximal \(D_{210}\) stack use \(t=32a\), branch values (0,32,76832,-343), sections \(q_{0}=(dt)^{2}/P(t),q_{1}=tq_{0}\), and \(J=2^{10}\cdot 3^{2}\cdot 5^{3}\cdot 7^{4}\). The actual proof extends \(J^{2}q_{i}\) vertically on the stack using semistability and controls their Petersson norms by \(4C_{\text{met}}\). Yuan's final isometry and the original stable normalization give

 \begin{gather*}
 h_{\omega ^{2}}(y)=2h_{F}(A_{y})+2\operatorname{log}(\pi )+\log 210
 \end{gather*}

-The positive log210 sign is retained. The same explicit integer estimate bounds the additive term \(by120<128\), so
+The positive log 210 sign is retained. The same explicit integer estimate bounds the additive term by \(120<128\), so

 \begin{gather*}
 h(a)\le 2 \operatorname{max}(0,h_{F}(A_{a}))+128
```

### H018

Class: status, source locator or provenance prose. Base 2424-2474; candidate 2419-2469.

```diff
@@ -2424,51 +2419,51 @@

 In the CM branch, retain that same A/L, all geometric endomorphisms over \(L\) and \([L:Q]\le 576\). \(G_{3}\) supplies \(\operatorname{rad}(D_{L})\le R\). The literal CM854R lemma assumes only these facts and \(R\ge 1\); it has no primorial or branch-coordinate hypothesis. Its dimension argument shows \(A\sim E^{2}\). L-defined idempotents give E/L and all its endomorphisms over \(L\). The derivative action embeds \(F=\operatorname{End}^{0}(E)\) into \(L\). Its same-field subgroup \(K=\sum (f \alpha _{i})(E[f])\) yields a quotient E'/L of maximal order, with \(A\sim (E')^{2}\) over \(L\). No coefficient-value field, \(L'\), or auxiliary good-reduction field replaces \(L\).

-The discriminant tower gives \(|\Delta _{F}|\le 4\operatorname{rad}(D_{L})\le 4R\), including the dyadic multiplier4. The individual-embedding CM height formula bounds \(h_{F}(E')<3R\), hence \(h_{F}((E')^{2})<6R\). The same general dimension-two Gaudron--Rémond2023 Theorem1.9(1), over \(L\) and with no base extension, bounds an isogeny \((E')^{2}\to A\). The original stable half-log-degree inequality gives
+The discriminant tower gives \(|\Delta _{F}|\le 4\operatorname{rad}(D_{L})\le 4R\), including the dyadic multiplier 4. The individual-embedding CM height formula bounds \(h_{F}(E')<3R\), hence \(h_{F}((E')^{2})<6R\). The same general dimension-two Gaudron--R\'emond 2023 Theorem 1.9(1), over \(L\) and with no base extension, bounds an isogeny \((E')^{2}\to A\). The original stable half-log-degree inequality gives

 \begin{gather*}
 h_{F}(A)<6R+8(96+7+2+\operatorname{log} R)\le 854R
 \end{gather*}

-All objects and constants in that proof are identical to the actual public source. It uses the individual-embedding discriminant formula, not a class average requiring a \(Q(j)\) Weierstrass model; the temporary field evaluating stable height contributes no degree to the isogeny estimate. The final006 H19-CM records explicitly state this universally quantified \(R\ge 1\) interface. This is why the changed small-support application fits it once \(G_{3}\) is proved.
+All objects and constants in that proof are identical to the actual public source. It uses the individual-embedding discriminant formula, not a class average requiring a \(Q(j)\) Weierstrass model; the temporary field evaluating stable height contributes no degree to the isogeny estimate. The source interface is universally quantified over \(R\ge 1\). This is why the changed small-support application fits it once \(G_{3}\) is proved.

-\subsection{\(G_{5}\). Dispositions and acceptance boundary}
+\subsection{\(G_{5}\). Scope of the geometric comparison}

-Historical classification: prior substantive justification found and read for the actual \(D_{210}\) cover, same-L Hom, metric and CM854R arguments. The \(S_{10}\) cutoff/local-support bridge already appears in private cutoff \S{}1; this supplement verifies its full contact cases, determinant equality and exact primary-object joins. It is not claimed as a newly discovered missing arithmetic argument. Private heightH0 states these inputs but leaves their source qualifications inherited; incorporation of this additive comparison is pending.
+The \(S_{10}\) cutoff/local-support bridge appears in private cutoff \S{}1. The comparison above includes its full contact cases, determinant equality and exact primary objects.

-Current author conclusion: H01's change of support introduces no additional mathematical hypothesis once the retained \(D_{210}\) source statements are supplied at their public accepted scopes. The source-to-private application and its consumer are now explicit. This is an author conclusion, awaiting the assigned nonauthor reviewer. Public final006's scoped approvals and byte identity do not alone certify every transitive primary-source prerequisite or the entire private 214 proof. Any such unresolved prerequisite must remain open in the root closure assessment; neither the mistaken SF08--10/D6 locators nor the ten-determinant check closes it.
+H01's change of support introduces no additional mathematical hypothesis provided the retained \(D_{210}\) source statements hold at the scopes specified here. Their transitive source prerequisites remain required: neither the ten-determinant calculation nor the source index establishes those prerequisites or the full 214 argument.
 \clearpage
 % Source: research/quartic214/proofs/provider-scope-carry.md
 \section{Exact retained \(D_{210}\) provider and conductor scope}\label{q214:provider-scope-carry}
 \noindent\textit{Source: }\nolinkurl{research/quartic214/proofs/provider-scope-carry.md}.\par

-Author supplement, \nolinkurl{/root/d214_modularity_closure}, 11 November 2026. Pending nonauthor review. Read together with \nolinkurl{GEOMETRY_CARRY.md} and \nolinkurl{PROOF_FINAL.md.} This supplies the detailed current-scope comparison requested after the first author freeze; it does not rewrite the older limited reviews.
+Read together with \nolinkurl{GEOMETRY_CARRY.md} and \nolinkurl{PROOF_FINAL.md}. This supplies the detailed comparison of the source scopes.

 \subsection{\(P_{1}\). Full \(D_{210}\) provider: sixteen actual applications}

-The exact public final006 decisions are in \nolinkurl{PUBLIC_FULL_COVER_DECISIONS.json.} \nolinkurl{FULL_COVER_SOURCE_PROFILES.json} extracts the actual incoming assertions, hypotheses, source editions/hashes, constructed objects and connecting maps from \nolinkurl{protocol/current-coverage/INHERITED-TRANSPORT-PROPOSALS.json}. These are the sixteen \nolinkurl{ACTIVE-H19-FULL-COVER-*} applications, \textbf{not} a generic \(H_{19}\) verdict, D6/B11 proof or modular SF08--10 application. The actual entire \nolinkurl{h5-full-three-v1/PROOF.md} (SHA256054ec4a6...) and its \nolinkurl{GEOMETRIC-ISOGENY.md} (f889eab0...) were read. The composition below explains how the antecedents in each source profile are supplied by the previous construction.
+The sixteen full-cover applications are specified in \nolinkurl{research/quartic214/sources/public-provider-scopes.json}, with their incoming assertions, hypotheses, source editions and hashes, constructed objects and connecting maps. Their scope is distinct from a generic \(H_{19}\) assertion, the discriminant-six construction or the modular SF08--10 application. The source text is \nolinkurl{research/version14/proofs/h5-full-three-v1/PROOF.md} (SHA256 054ec4a6...) and its \nolinkurl{GEOMETRIC-ISOGENY.md} (f889eab0...). The composition below supplies the antecedents of each source application from the preceding construction.

 \begin{longtable}{@{}p{0.23\linewidth}p{0.73\linewidth}@{}}
 \toprule
 Exact suffix of ACTIVE-H19-FULL-COVER-* & Supplier and actual construction-to-input match\\
 \midrule
 \endhead
-MAXIMAL-STACK & Yuan final Chinese2024 \S{}2.1, pp230--231, aee74126...; use only \(N=1\) and the specified \(D_{210}\) division algebra/order/involution. It supplies the proper smooth DM maximal stack over Z[1/210] with universal surface. The separate Isom construction defines full3; no literal level-map statement is used at ramified3.\\
-THREE-TORSION & Milne1986 Theorem8.2/Remark8.4, pp115--116, 86259344...; 3 is invertible on this base, A has dimension2, so A[3] is finite etale of rank81 and \(T_{3}\) has rank4. The projection T3/3 \(\to \) A[3] respects the O-action and multiplication-by3 transition maps.\\
-DIVISION-LATTICE & Voight2021 \S{}13.3.4/13.3.11, pp206--207, exact final extract8f808986...; \(B_{3}\) is division, not split. Rank4 makes \(V_{3}\) rank1 over \(B_{3}\). A least \(w=\operatorname{ord}3(\operatorname{nrd})/2\) lattice element proves \(T_{3}=O_{3}\) \(x\). Thus A[3] is the regular O/3 module. Its unit \(\text{count}81-9=72\) is the stack-cover degree.\\
-TATE-FAITHFULNESS & Milne1986 Lemma12.2, \(p_{122}\); inject the finite geometric stabilizer into GL4(Z3). Preservation of the full marking places it in1+3M4. The written binomial argument for prime-order elements proves torsion-freeness. It is not deduced merely from the Tate rank.\\
-TRIVIAL-INERTIA & Stacks03YR, dated source82246ff7...; inertia of this proper DM cover is finite unramified. Its identity section is open and closed; its complement has empty geometric fibers. Hence inertia is trivial on every base and this same stack is an algebraic space with its universal scheme. This is stronger than geometric-point rigidity alone.\\
-CURVE-FIBERS & Stacks0ADD, f067c166...; the smooth geometric fibers of that algebraic space have dimension1 and regular local rings, hence are schemes. The total space has not yet been assumed schematic.\\
-GENUS-INPUT & Gonzalez--Rotger2006 pp937--941, e595d1a4..., for the selected \(D_{210}\) coarse curve. Every characteristic-zero marking-cover component maps finitely and nonconstantly to it. Its genus5 and Riemann--Hurwitz give \(\text{genus}\ge 5\) on each component. This is not inferred from degree72.\\
+MAXIMAL-STACK & Yuan final Chinese 2024 \S{}2.1, pp.~230--231, aee74126...; use only \(N=1\) and the specified \(D_{210}\) division algebra/order/involution. It supplies the proper smooth DM maximal stack over Z[1/210] with universal surface. The separate Isom construction defines full 3; no literal level-map statement is used at ramified 3.\\
+THREE-TORSION & Milne 1986 Theorem 8.2/Remark 8.4, pp.~115--116, 86259344...; 3 is invertible on this base, A has dimension 2, so A[3] is finite etale of rank 81 and \(T_{3}\) has rank 4. The projection T3/3 \(\to \) A[3] respects the O-action and multiplication-by 3 transition maps.\\
+DIVISION-LATTICE & Voight 2021 \S{}13.3.4/13.3.11, pp.~206--207, exact final extract 8f808986...; \(B_{3}\) is division, not split. Rank 4 makes \(V_{3}\) rank 1 over \(B_{3}\). A least \(w=\operatorname{ord}3(\operatorname{nrd})/2\) lattice element proves \(T_{3}=O_{3}\) \(x\). Thus A[3] is the regular O/3 module. Its unit \(\text{count}81-9=72\) is the stack-cover degree.\\
+TATE-FAITHFULNESS & Milne 1986 Lemma 12.2, p.~122; inject the finite geometric stabilizer into GL4(Z3). Preservation of the full marking places it in 1+3M4. The written binomial argument for prime-order elements proves torsion-freeness. It is not deduced merely from the Tate rank.\\
+TRIVIAL-INERTIA & Stacks 03YR, dated source82246ff7...; inertia of this proper DM cover is finite unramified. Its identity section is open and closed; its complement has empty geometric fibers. Hence inertia is trivial on every base and this same stack is an algebraic space with its universal scheme. This is stronger than geometric-point rigidity alone.\\
+CURVE-FIBERS & Stacks 0ADD, f067c166...; the smooth geometric fibers of that algebraic space have dimension 1 and regular local rings, hence are schemes. The total space has not yet been assumed schematic.\\
+GENUS-INPUT & Gonzalez--Rotger2006 pp.~937--941, e595d1a4..., for the selected \(D_{210}\) coarse curve. Every characteristic-zero marking-cover component maps finitely and nonconstantly to it. Its genus 5 and Riemann--Hurwitz give \(\text{genus}\ge 5\) on each component. This is not inferred from degree 72.\\
 COMPONENT-BASE & Stacks0A18, e7df43c1...; the already proper smooth space is flat with geometrically reduced fibers. Its Stein component base is finite etale, with geometrically connected fibers. Every component of this finite-etale base meets the generic fiber.\\
 GENUS-CONSTANCY & Stacks0E83, 3cac1b5d...; apply over that component base, using the schematic smooth proper connected curve fibers just proved. It carries \(\text{genus}\ge 2\) to every fiber component.\\
 RELATIVE-AMPLENESS & Stacks0D3A,99f65961...; the relative canonical line has positive \(\text{degree}2g-2\) on each proper smooth fiber component and is ample there. Properness and a Noetherian base give relative ampleness locally near each base point.\\
 SCHEME-FROM-AMPLE & Stacks0D32,a525102d...; that relative ample line makes the already constructed algebraic space a scheme. Trivial inertia or properness alone did not supply this.\\
 PROJECTIVITY & Stacks0B45,d3057d39..., \(\text{implication}(6)\to (1)\); the base SpecZ[1/210] is affine and has an ample line, and \(Y\) is now a proper scheme with a relative ample line. Thus \(Y\) is projective.\\
-PEL-CLASSIFICATION & Original MilneClay2005,6336f0a2..., Theorem7.4's full Hodge-orbit condition,8.6--8.7/8.16. Rank-one left \(B\) and the specified involution give one-dimensional compatible alternating forms and the right-centralizer \(\operatorname{GL}2\) type-C1. On the two-dimensional multiplicity factor, (v,Jv) is a basis and conjugates the full Hodge map into the same orbit. Both half-planes and all marking multipliers remain. The erroneous general8.17 implication is not used.\\
-PRINCIPAL-POLARIZATION & Buzzard1997 p592,ed34a072..., before its level restrictions; recover the O-stable full Tate lattice, then its unique positive perfect polarization for the fixed involution. This changes no marking or unit multiplier. No auxiliary five-level \(D_{6}\) construction is imported.\\
-ALGEBRAIC-FAMILY & Milne2005 Theorem14.8, \(p_{352}\); every arithmetic component has its integral lattice and polarization. A rational stabilizer preserving that lattice has positive multiplier a unit at every finite prime, hence1. Thus the variation is integrally polarized and the theorem supplies its abelian scheme/O maps algebraically. The marking's graph is a component union of a finite etale Isom cover, hence algebraic. The fine moduli map is bijective on geometric points; nonsingular characteristic-zero curve theory makes it an isomorphism.\\
-CANONICAL-MODEL & Milne2005 pp354--355 type-A/C criterion and13.6--13.7,p349; the comparison transports the algebraic order, polarization, torsion quotients and marking under every automorphism of C/Q. Reflex field isQ. This is the required rational model, and uniqueness/Hecke-map compatibility identifies the same normalizer action. There is no fictitious Galois action on rational Betti homology or restriction to one component.\\
+PEL-CLASSIFICATION & Original Milne, Clay 2005,6336f0a2..., Theorem 7.4's full Hodge-orbit condition,8.6--8.7/8.16. Rank-one left \(B\) and the specified involution give one-dimensional compatible alternating forms and the right-centralizer \(\operatorname{GL}_{2}\) type-C1. On the two-dimensional multiplicity factor, (v,Jv) is a basis and conjugates the full Hodge map into the same orbit. Both half-planes and all marking multipliers remain. The erroneous general 8.17 implication is not used.\\
+PRINCIPAL-POLARIZATION & Buzzard 1997 p592,ed34a072..., before its level restrictions; recover the O-stable full Tate lattice, then its unique positive perfect polarization for the fixed involution. This changes no marking or unit multiplier. No auxiliary five-level \(D_{6}\) construction is imported.\\
+ALGEBRAIC-FAMILY & Milne 2005 Theorem 14.8, p.~352; every arithmetic component has its integral lattice and polarization. A rational stabilizer preserving that lattice has positive multiplier a unit at every finite prime, hence 1. Thus the variation is integrally polarized and the theorem supplies its abelian scheme/O maps algebraically. The marking's graph is a component union of a finite etale Isom cover, hence algebraic. The fine moduli map is bijective on geometric points; nonsingular characteristic-zero curve theory makes it an isomorphism.\\
+CANONICAL-MODEL & Milne 2005 pp.~354--355 type-A/C criterion and 13.6--13.7,p349; the comparison transports the algebraic order, polarization, torsion quotients and marking under every automorphism of C/Q. Reflex field isQ. This is the required rational model, and uniqueness/Hecke-map compatibility identifies the same normalizer action. There is no fictitious Galois action on rational Betti homology or restriction to one component.\\
 \bottomrule
 \end{longtable}

```

### H019

Class: status, source locator or provenance prose. Base 2476-2516; candidate 2471-2511.

```diff
@@ -2476,41 +2471,41 @@

 The integral-to-rational lattice comparison also has actual maps: a full adelic lattice commensurable with the given one is realized after multiplying by an integer by quotienting by the corresponding finite torsion subgroup. O-stability descends the action. An isogeny preserving every integral Tate lattice has no nontrivial kernel/cokernel and is an isomorphism. The unique positive perfect representative restores the same polarization. This supplies the exact object classification consumed by ALGEBRAIC-FAMILY; it is not an equality of point counts alone.

-\subsection{\(P_{2}\). The five old pending bundles, and what is retained}
+\subsection{\(P_{2}\). The five geometric input groups}

-The older H5-FULL-COVER-SOURCE-INDEX-REVIEW accepted a role index and explicitly left five bundles pending. That historical limited judgment is preserved. The later sixteen final006 source profiles above and the actual integrated proof support the following \textbf{new author comparison}, whose acceptance is still pending:
+The five geometric input groups are used as follows:

 \begin{itemize}
 \item 1. The fixed \(D_{210}\) datum and genus input are exactly MAXIMAL-STACK, PRINCIPAL-POLARIZATION and GENUS-INPUT, together with the selected order/involution in the actual \(D_{210}\) text. They are not supplied by the \(D_{6}\) original polarized datum.
 \item 2. The finite-etale/Isom/stack-stability bundle is the explicit trivialization/equalities/descent construction above, with universal-scheme pullback and TRIVIAL-INERTIA. It applies to every geometric fiber over Z[1/210], not just characteristic zero.
 \item 3. Riemann--Hurwitz and positive canonical degree are used in GENUS-INPUT and RELATIVE-AMPLENESS exactly at their proper smooth characteristic-zero/positive-genus curve scope; COMPONENT-BASE precedes GENUS-CONSTANCY. The current proof does not assume the total space was already a scheme.
-\item 4. Finite torsion quotients, integral Tate detection and algebraic finite-etale markings are the actual constructions in \(P_{1}\) and \S{}6 of the full provider. The characteristic-zero nonsingular comparison is a morphism of curves with degree1, hence an isomorphism; no arbitrary complex isomorphism is descended.
-\item 5. The central-idele and normalizer calculation is on that same entire canonical model: a rational scalar and its sign make any central idele trivial moduloU(3). The exact quotient \(\text{has}72/2=36\) marking classes and16 normalizer parities, hence576. Properness/good reduction is the valuative extension of points on that same projective \(Y\). Bad-prime metric statements use the separate Yuan maximal stack and its Hodge isometry, not a coarse-pullback lemma. These are respectively G2/G3/G4 in \(\text{GEOMETRY}_{\text{CARRY}}\).
+\item 4. Finite torsion quotients, integral Tate detection and algebraic finite-etale markings are the actual constructions in \(P_{1}\) and \S{}6 of the full provider. The characteristic-zero nonsingular comparison is a morphism of curves with degree 1, hence an isomorphism; no arbitrary complex isomorphism is descended.
+\item 5. The central-idele and normalizer calculation is on that same entire canonical model: a rational scalar and its sign make any central idele trivial moduloU(3). The exact quotient \(\text{has}72/2=36\) marking classes and 16 normalizer parities, hence 576. Properness/good reduction is the valuative extension of points on that same projective \(Y\). Bad-prime metric statements use the separate Yuan maximal stack and its Hodge isometry, not a coarse-pullback lemma. These are respectively G2/G3/G4 in \(\text{GEOMETRY}_{\text{CARRY}}\).
 \end{itemize}

-Published canonical-model/PEL and CM reciprocity theorems retain their published statements as theorem inputs. The protocol does not require reproving their whole ancestry. The present author has not independently re-inspected every original final PDF/Stacks HTML byte in the sixteen old profiles; exact public accepted applications are carried at their existing source scope, while the actual entire internal \(D_{210}\) construction and its changed private application have been read and compared. This is the disclosed \S{}33 carry boundary for nonauthor review. If that exact carry is not accepted, those precise source applications remain open; a broad \(H_{19}\) or Yuan label cannot replace it.
+Published canonical-model/PEL and CM reciprocity theorems retain their published statements as theorem inputs. Not every original final PDF or Stacks page underlying the sixteen source profiles has been independently re-inspected here. Their exact statements, hypotheses and source scopes remain required for the \(D_{210}\) construction and its current application; a broad \(H_{19}\) or Yuan label cannot replace the individual applications.

 \subsection{\(P_{3}\). Contact-line identity and tame branch composition}

-The relevant actual predecessor passage, privateV14 lines7532--7604/currentV15 lines7664--7736, derives the \(D_{210}\) contact line from Gonzalez--Rotger's four published quartic quotients. It is distinct from both \(D_{6}\) and the modular j/1728 map. The quotient models have coefficient rows for \(m=30,42,70,105\) exactly as displayed there. Genus5, \(W=(C_{2})^{4}\) and Riemann--Hurwitz give the four known eight-point fixed sets, total fixed count40, genus-zero full quotient, and one further branch orbit. The four labels are independent and their product is210; therefore the five rational branch sections have labels30,42,70,105,210. Normalizing labels210,105,70 to infinity,0,1 fixes the coordinate.
+The relevant actual predecessor passage, private V14 lines7532--7604/current V15 lines7664--7736, derives the \(D_{210}\) contact line from Gonzalez--Rotger's four published quartic quotients. It is distinct from both \(D_{6}\) and the modular j/1728 map. The quotient models have coefficient rows for \(m=30,42,70,105\) exactly as displayed there. Genus 5, \(W=(C_{2})^{4}\) and Riemann--Hurwitz give the four known eight-point fixed sets, total fixed count 40, genus-zero full quotient, and one further branch orbit. The four labels are independent and their product is 210; therefore the five rational branch sections have labels 30,42,70,105,210. Normalizing labels 210,105,70 to infinity,0,1 fixes the coordinate.

-\nolinkurl{CONTACT_LINE_CERTIFICATE.json} independently recomputes the four quartic I,J invariants and verifies their exact Legendre j-invariants for parameters1/2401,32/375,1/225,5/1029. It exhausts the36 pairs from the six cross-ratios of each first-two parameter. The last-two \(j\) equations leave uniquely \((\lambda ,\mu )=(2401,-343/32)\). This verifies the finite algebra consumed by the geometry proof; the published identification of the four quotient curves remains its identified published input.
+\nolinkurl{CONTACT_LINE_CERTIFICATE.json} independently recomputes the four quartic I,J invariants and verifies their exact Legendre j-invariants for parameters 1/2401,32/375,1/225,5/1029. It exhausts the 36 pairs from the six cross-ratios of each first-two parameter. The last-two \(j\) equations leave uniquely \((\lambda ,\mu )=(2401,-343/32)\). This verifies the finite algebra consumed by the geometry proof; the published identification of the four quotient curves remains its identified published input.

-Over Z[1/210], the level-change group36 and \(W\) of order16 have invertible orders. The generic level action is free. For a tame finite-order automorphism of a smooth curve, the fixed scheme is smooth along a fixed point (average a local tangent parameter to its eigencharacter); an isolated special fixed point lifts uniquely. Thus it cannot create a new special branch orbit or collision; intersecting distinct fixed loci would give a noncyclic stabilizer, impossible in a one-dimensional tame tangent action. The stable-curve Isom extension gives the same \(W\) action on the proper smooth model. The quotient remains genus zero with the same ordered three sections, hence that same normalized rational coordinate, and local anti-invariant parameter gives \(w=z^{2}\) up to a unit. This is the actual tame-model join used in \(G_{3}\), independent of the old primorial. It is not inferred from the determinant certificate.
+Over Z[1/210], the level-change group 36 and \(W\) of order 16 have invertible orders. The generic level action is free. For a tame finite-order automorphism of a smooth curve, the fixed scheme is smooth along a fixed point (average a local tangent parameter to its eigencharacter); an isolated special fixed point lifts uniquely. Thus it cannot create a new special branch orbit or collision; intersecting distinct fixed loci would give a noncyclic stabilizer, impossible in a one-dimensional tame tangent action. The stable-curve Isom extension gives the same \(W\) action on the proper smooth model. The quotient remains genus zero with the same ordered three sections, hence that same normalized rational coordinate, and local anti-invariant parameter gives \(w=z^{2}\) up to a unit. This is the actual tame-model join used in \(G_{3}\), independent of the old primorial. It is not inferred from the determinant certificate.

-\subsection{\(P_{4}\). Full11 semistability, torus rank and exact retained ramification source}
+\subsection{\(P_{4}\). Full 11 semistability, torus rank and exact retained ramification source}

-\nolinkurl{CONDUCTOR_INHERITED_PROFILES.json} records the actual public full11 and torus statements. The final Silverberg--Zarhin1995 AIF45,403--420 PDF was reacquired from Numdam; its hash is \textbf{\nolinkurl{fc62ba1c9d1315a0c441a3dd7de46a254f379289e630c407a3336c0230d91052}}, exactly the public source pin. Its actual Theorem3.4 and Theorem3.5, printed406, were read. The former gives a finite Galois semistable extension at every discrete valuation. The latter applies when n-torsion is rational over an unramified extension and \(n\ge 3\) is prime to residue characteristic. In our application \(n=11\), the ground field is \(E=L(A[11])\), and that unramified extension is the identity extension of \(E\). Thus every place over2,3,5,7 is covered; residue11 is excluded. No earlier \(n=3\) or5 occurrence is used as a substitute.
+\nolinkurl{CONDUCTOR_INHERITED_PROFILES.json} records the actual public full 11 and torus statements. The final Silverberg--Zarhin 1995 AIF 45,403--420 PDF is identified by the Numdam hash \textbf{\nolinkurl{fc62ba1c9d1315a0c441a3dd7de46a254f379289e630c407a3336c0230d91052}}, exactly the public source pin. Theorem 3.4 and Theorem 3.5 are on printed 406. The former gives a finite Galois semistable extension at every discrete valuation. The latter applies when n-torsion is rational over an unramified extension and \(n\ge 3\) is prime to residue characteristic. In our application \(n=11\), the ground field is \(E=L(A[11])\), and that unramified extension is the identity extension of \(E\). Thus every place over 2,3,5,7 is covered; residue 11 is excluded. No earlier \(n=3\) or 5 occurrence is used as a substitute.

-The same \(D_{210}\) B-action is defined over \(E\). Every actual endomorphism extends to the Neron model and preserves the semistable torus. If its geometric torus rank \(t>0\), restriction gives a unital homomorphism \(B\to M_{t}(Q),1\le t\le 2\). Its kernel is an ideal in simpleB and is not allB because1 maps to1. For \(t=1\) dimensions contradict injectivity; for \(t=2\) injectivity makes an isomorphism onto splitM2(Q), contradicting divisionB. Therefore \(t=0\) and semistable reduction is good. This proof is independent of chi,b and the size of \(R\).
+The same \(D_{210}\) B-action is defined over \(E\). Every actual endomorphism extends to the Neron model and preserves the semistable torus. If its geometric torus rank \(t>0\), restriction gives a unital homomorphism \(B\to M_{t}(Q),1\le t\le 2\). Its kernel is an ideal in simpleB and is not allB because 1 maps to 1. For \(t=1\) dimensions contradict injectivity; for \(t=2\) injectivity makes an isomorphism onto split M2(Q), contradicting divisionB. Therefore \(t=0\) and semistable reduction is good. This proof is independent of chi,b and the size of \(R\).

-E/Q is normal by the actual prime-to11 normalizer isogenies over \(L:\) at11 the algebra is split and a normalizer is Q11*GL2(Z11); a rational rescaling makes it integral invertible there, and denominators elsewhere are cleared by an integer prime to11. The original isogeny and every conjugate therefore identify the11-torsion kernels over \(L\). Every conjugate of \(E\) is \(E\). Lagrange strengthens the public inequality to divisibility
+E/Q is normal by the actual prime-to-11 normalizer isogenies over \(L:\) at 11 the algebra is split and a normalizer is \(\mathbb Q_{11}^{\times}\operatorname{GL}_{2}(\mathbb Z_{11})\); a rational rescaling makes it integral invertible there, and denominators elsewhere are cleared by an integer prime to 11. The original isogeny and every conjugate therefore identify the 11-torsion kernels over \(L\). Every conjugate of \(E\) is \(E\). Lagrange strengthens the public inequality to divisibility

 \begin{gather*}
-[E:Q] | 576 |\operatorname{GL}4(F_{11})|
+[E:Q]\mid 576 |\operatorname{GL}_{4}(F_{11})|
 \end{gather*}

-The public accepted source scope needed only the displayed larger \(\text{bound}<2^{66}\). The private sharper valuations(15,4,4,1) follow from this divisibility, not by substituting a new unproved finite-field estimate. Chi's new minimal-order choice does not change \(E\), A, \(B\) or these isogenies.
+The public source argument needed only the displayed larger \(\text{bound}<2^{66}\). The private sharper valuations (15,4,4,1) follow from this divisibility, not by substituting a new unproved finite-field estimate. Chi's new minimal-order choice does not change \(E\), A, \(B\) or these isogenies.

 The ramification calculation uses two chapters of Cassels--Fr\"ohlich,
 \emph{Algebraic Number Theory} (1967). Hilbert's different formula is
```

### H020

Class: status, source locator or provenance prose. Base 2524-2556; candidate 2519-2551.

```diff
@@ -2524,33 +2519,33 @@
 gives the tame codimension plus the upper Swan integral. These
 statements have no lower bound on the extension degree or fixed list
 of ramification indices. The historical source profile
-ACTIVE-H19-RAMIFICATION-NUMBERING and its final006 decision retain the
+ACTIVE-H19-RAMIFICATION-NUMBERING retain the
 extract hash \nolinkurl{e0367b25a022eb27ec220e3c15b474a94fb96d70a6bb89b77f4a02c2231950fe};
 the original retrieval URL of that extract remains unknown. The
 printed pages just cited have now also been inspected in a scan of
 the 1967 volume.

-The new input to that unchanged theorem is the same kind of local finite Galois extension \(F'/Q_{p}\) with better wild-part valuations. \(Q(\chi )\) is the kernel field; it is tame at oddp and its dyadic inertia has \(\text{order}\le 2\). On \(F=E\) \(Q(\chi )\), \(b\) is a quadratic conjugation-invariant character and its kernel gives F'/F of \(\text{degree}\le 2\). At oddp this addition is tame, at2 it adds at most one factor2. Thus the actual constructed extensions satisfy all source hypotheses with \(v_{p}(e)\le (17,4,4,1)\). A/E is already good at2,3,5,7, and on \(G_{F'}\) all scalar/isogeny corrections are1, so the actual \(r_{\ell }\) is trivial on its local inertia for \(\ell \ne p\). The upper-numbering quotient map is therefore the one used to bound \textbf{this} representation's Swan conductor. The derivative/Hilbert/Herbrand calculation is explicitly derived in \(M_{5}\), retaining the tame term and allowing arbitrarily large tame index. The resulting conductor exponents(70,18,18,6) are a fresh numerical consequence; the \(\text{public}274<300\) conclusion itself is not carried as proof of them.
+The new input to that unchanged theorem is the same kind of local finite Galois extension \(F'/Q_{p}\) with better wild-part valuations. \(Q(\chi )\) is the kernel field; it is tame at oddp and its dyadic inertia has \(\text{order}\le 2\). On \(F=E\) \(Q(\chi )\), \(b\) is a quadratic conjugation-invariant character and its kernel gives F'/F of \(\text{degree}\le 2\). At oddp this addition is tame, at 2 it adds at most one factor 2. Thus the actual constructed extensions satisfy all source hypotheses with \(v_{p}(e)\le (17,4,4,1)\). A/E is already good at 2,3,5,7, and on \(G_{F'}\) all scalar/isogeny corrections are 1, so the actual \(r_{\ell }\) is trivial on its local inertia for \(\ell \ne p\). The upper-numbering quotient map is therefore the one used to bound \textbf{this} representation's Swan conductor. The derivative/Hilbert/Herbrand calculation is explicitly derived in \(M_{5}\), retaining the tame term and allowing arbitrarily large tame index. The resulting conductor exponents(70,18,18,6) are a fresh numerical consequence; the \(\text{public}274<300\) conclusion itself is not carried as proof of them.

-\nolinkurl{PUBLIC_CONDUCTOR_SCOPES.json} and \nolinkurl{PUBLIC_FULL_COVER_DECISIONS.json} point to the nonauthor public decisions for these exact inputs. They do not authorize an unreviewed changed application. This supplement, M1/M5's new lift and sharper arithmetic, and the exact same-form r3/r5 consumer remain subject to the assigned current independent review.
+\nolinkurl{PUBLIC_CONDUCTOR_SCOPES.json} and \nolinkurl{PUBLIC_FULL_COVER_DECISIONS.json} record the source scopes for these exact inputs.
 \clearpage
 % Source: research/quartic214/proofs/modularity.md
-\section{Original normalized modularity for the private 214 construction}\label{q214:modularity}
+\section{Original normalized modularity for the 214 construction}\label{q214:modularity}
 \noindent\textit{Source: }\nolinkurl{research/quartic214/proofs/modularity.md}.\par

-\begin{quote}\footnotesize Final author revision after the first freeze. Author: \nolinkurl{/root/d214_modularity_closure}, internal Sol author lane, 11 November 2026. \textbf{Author proposal; no independent acceptance.} The frozen private repository is \nolinkurl{bfeb8400982c9a169e4fdd39fb68ec053621e8ed}. Sources and consumers are byte-bound in \nolinkurl{SOURCE_USES.json.} \nolinkurl{INITIAL_AUTHOR_ANALYSIS.json} records the actual order of exposure, including the scope summary read before reconstruction. This is an additive proof: no historical argument, verdict, count or polynomial is changed.\end{quote}
+\begin{quote}\footnotesize The frozen private repository is \nolinkurl{bfeb8400982c9a169e4fdd39fb68ec053621e8ed}. Sources and consumers are byte-bound in \nolinkurl{SOURCE_USES.json}. \end{quote}

 \subsection{\(M_{0}\). Exact input and conclusion}

-For every rational \(a=u/v\) in the domain of private \nolinkurl{height/PROOF.md} \(H_{0}\), retain its original full-three-marked normalizer surface \(A=A_{a}\), normal field \(L\), and B-linear conjugate isogenies \(\mu _{\sigma }\). In the non-CM case the geometric endomorphism algebra is the division quaternion algebra \(B\) of discriminant 210. All conjugate Hom groups are L-defined, \(\mu _{1}=1\), and the choices are inflated from Gal(L/Q). These are geometric input assertions, not consequences of the modularity theorem. Put \(T=\operatorname{supp}(R)\), \(R=B_{S}\) \(M_{S}(a)\), and \(U=\operatorname{max}(\{2\} \cup  \{2^{v_{2}(p-1)}: \text{odd} p|R\})\).
+For every rational \(a=u/v\) in the domain of \nolinkurl{height/PROOF.md} \(H_{0}\), retain its original full-three-marked normalizer surface \(A=A_{a}\), normal field \(L\), and B-linear conjugate isogenies \(\mu _{\sigma }\). In the non-CM case the geometric endomorphism algebra is the division quaternion algebra \(B\) of discriminant 210. All conjugate Hom groups are L-defined, \(\mu _{1}=1\), and the choices are inflated from Gal(L/Q). These are geometric input assertions, not consequences of the modularity theorem. Put \(T=\operatorname{supp}(R)\), \(R=B_{S}\) \(M_{S}(a)\), and \(U=\operatorname{max}(\{2\} \cup  \{2^{v_{2}(p-1)}: \text{odd} p|R\})\).

-The claims established below, conditional only on those exact geometric inputs and the source applications individually identified here, are: the new minimal-character lift gives genuine original representations \(r_{\ell }\); the same final normalized primitive weight-two \(f\) realizes \(r_{5}\) and \(r_{3}\); its actual level satisfies \(N\le 2^{68}\) \(3^{16}\) \(5^{16}\) \(7^{4}\) \(R^{2}\) and \(\operatorname{rad}(N)|R\); and the multiplicity and character estimates of H1--H2 hold over the actual \(L'\). The exact \(H_{01}\) geometric/metric/CM and retained conductor-source transport is supplied by \nolinkurl{GEOMETRY_CARRY.md} and \nolinkurl{PROVIDER_SCOPE_CARRY.md.} These additive comparisons require the same current nonauthor review; H3's Rémond inequality and the full214 assembly are separate.
+The claims established below, conditional only on those exact geometric inputs and the source applications individually identified here, are: the new minimal-character lift gives genuine original representations \(r_{\ell }\); the same final normalized primitive weight-two \(f\) realizes \(r_{5}\) and \(r_{3}\); its actual level satisfies \(N\le 2^{68}\) \(3^{16}\) \(5^{16}\) \(7^{4}\) \(R^{2}\) and \(\operatorname{rad}(N)|R\); and the multiplicity and character estimates of H1--H2 hold over the actual \(L'\). The exact \(H_{01}\) geometric/metric/CM and retained conductor-source transport is supplied by \nolinkurl{GEOMETRY_CARRY.md} and \nolinkurl{PROVIDER_SCOPE_CARRY.md}. H3's R\'emond inequality and the full 214 assembly are separate.

 Use covariant rational Tate modules, arithmetic Frobenius, and \(HT(Q_{\ell }(1))=-1\). Added algebraic coefficients have trivial Galois action. The names \(\chi \), \(b\), \(\epsilon _{\text{sign}}\), \(\epsilon _{f}\), \(\delta \) and the cyclotomic character \(\kappa \) are distinct.

 \subsection{\(M_{1}\). The changed two-primary lift}

-Let \(c(\sigma ,\tau )=\mu _{\sigma }\) \(\sigma (\mu _{\tau })\) \(\mu _{\sigma  \tau }^{-1}\) in Q*. Rational quasi-isogeny degree is defined by \(D(\mu )=\operatorname{deg}([n]\mu )/n^{4}\); multiplicativity, conjugation invariance and \(\operatorname{deg}([n])=n^{4}\) make this independent of \(n\). Thus \(D(c \mu )=c^{4}\) \(D(\mu )\). For \(a_{\sigma }=D(\mu _{\sigma })^{-1/4}\) with positive real fourth root,
+Let \(c(\sigma ,\tau )=\mu _{\sigma }\) \(\sigma (\mu _{\tau })\) \(\mu _{\sigma  \tau }^{-1}\) in \(\mathbb Q^{\times}\). Rational quasi-isogeny degree is defined by \(D(\mu )=\operatorname{deg}([n]\mu )/n^{4}\); multiplicativity, conjugation invariance and \(\operatorname{deg}([n])=n^{4}\) make this independent of \(n\). Thus \(D(c \mu )=c^{4}\) \(D(\mu )\). For \(a_{\sigma }=D(\mu _{\sigma })^{-1/4}\) with positive real fourth root,

 \begin{gather*}
 a_{\sigma } a_{\tau }/a_{\sigma  \tau }=1/|c(\sigma ,\tau )|
```

### H021

Class: status, source locator or provenance prose. Base 2580-2610; candidate 2575-2605.

```diff
@@ -2580,31 +2575,31 @@

 Faltings' final Theorem 1(a,b), published \emph{Rational Points}, second edition (1986), printed 204, applies over \(L'\) to A and to products. A number field is finitely generated in characteristic zero. Its Tate representation is semisimple and its commutant is \(\operatorname{End}_{L'}(A)\) tensor \(Q_{\ell }\). All geometric endomorphisms are L-defined, so after extending to a splitting coefficient field this is \(M_{2}(E)\). The multiplicity commutant is \(E\), also after scalar extension; intertwiner equations are finite-dimensional linear equations and commute with extension. Semisimplicity persists under scalar extension in characteristic zero because the semisimple image algebra is separable. Thus \(r_{\ell }|G_{L'}\) and \(r_{\ell }\) are absolutely irreducible. Finite-index restriction and averaging also show semisimplicity upstairs. Continuity follows from continuity of the Tate action on this open subgroup and the finite coset decomposition. Away from \(T\) union \{ell\}, good reduction and the unramified field/cochain give unramified \(r_{\ell }\).

-For \(\ell =5\), take a completion of \(L'\) above 5. It is a finite extension of \(Q_{5}\), hence complete discretely valued with perfect residue field. A is smooth proper over that field, so its analytification satisfies Scholze's final Corollary 1.8, pp.5--6. Theorems 9.1 and 9.3, pp.74--75, identify coherent/de Rham and etale algebraic/analytic realizations; the finite etale comparisons respect every \(Z/5^{n}\) transition and therefore their inverse limit. The final 2016 corrigendum, all four pages read, restricts the pro-etale covers and corrects the completed period-sheaf definition; it explicitly retains the comparison results. It does not impose good reduction at 5. Milne1986 Theorem15.1(a), p.129, identifies etale \(H^{1}\) with the Tate dual without another Tate twist. The surface's Hodge numbers 2,2 give Tate weights \{0,0,-1,-1\}; the two identical summands each have weights \{0,-1\}. Fontaine1994 Theorem3.8, p.142, supplies exact tensor/dual/subobject closure. Kato2004 \S{}9.2, p.187, explicitly supplies descent through finite local extensions and filtered base change. Hence this original \(r_{5}\) is de Rham over \(Q_{5}\) with those weights.
+For \(\ell =5\), take a completion of \(L'\) above 5. It is a finite extension of \(Q_{5}\), hence complete discretely valued with perfect residue field. A is smooth proper over that field, so its analytification satisfies Scholze's final Corollary 1.8, pp.5--6. Theorems 9.1 and 9.3, pp.74--75, identify coherent/de Rham and etale algebraic/analytic realizations; the finite etale comparisons respect every \(Z/5^{n}\) transition and therefore their inverse limit. The final 2016 corrigendum, restricts the pro-etale covers and corrects the completed period-sheaf definition; it explicitly retains the comparison results. It does not impose good reduction at 5. Milne 1986 Theorem 15.1(a), p.129, identifies etale \(H^{1}\) with the Tate dual without another Tate twist. The surface's Hodge numbers 2,2 give Tate weights \{0,0,-1,-1\}; the two identical summands each have weights \{0,-1\}. Fontaine 1994 Theorem 3.8, p.142, supplies exact tensor/dual/subobject closure. Kato 2004 \S{}9.2, p.187, explicitly supplies descent through finite local extensions and filtered base change. Hence this original \(r_{5}\) is de Rham over \(Q_{5}\) with those weights.

-For oddness, on complex Betti homology conjugation interchanges the two Hodge summands, whereas \(\mu _{c}\) is holomorphic and preserves their types. Thus \(t_{c}\) \(\mu _{c}\) \(c\) has trace zero. Milne2005's complex uniformization and Theorem6.8/Corollary6.9, p.319, identify the lattice with \(H_{1}\). Multiplication by \(5^{n}\) identifies \((5^{-n} \text{Lambda})/\text{Lambda}\) with \(\text{Lambda}/5^{n}\) Lambda. Exponentiation commutes with holomorphic homomorphisms and conjugation to the conjugate variety. Clearing isogeny denominators and taking the inverse limit transports this operator to \(\rho _{5}(c)\). Thus \(\operatorname{tr}(r_{5}(c))=0\). Since \(r_{5}(c)^{2}=1\), it has eigenvalues 1,-1 and is odd.
+For oddness, on complex Betti homology conjugation interchanges the two Hodge summands, whereas \(\mu _{c}\) is holomorphic and preserves their types. Thus \(t_{c}\) \(\mu _{c}\) \(c\) has trace zero. Milne 2005's complex uniformization and Theorem 6.8/Corollary 6.9, p.319, identify the lattice with \(H_{1}\). Multiplication by \(5^{n}\) identifies \((5^{-n}\Lambda)/\Lambda\) with \(\Lambda/5^{n}\Lambda\). Exponentiation commutes with holomorphic homomorphisms and conjugation to the conjugate variety. Clearing isogeny denominators and taking the inverse limit transports this operator to \(\rho _{5}(c)\). Thus \(\operatorname{tr}(r_{5}(c))=0\). Since \(r_{5}(c)^{2}=1\), it has eigenvalues 1,-1 and is odd.

-Calegari's final EMS ICM2022 volume2 chapter, published 2023, definitions pp.611--612 and statement p.624, is the immediate published theorem: continuous irreducible geometric two-dimensional representations at \(p\ge 5\) with distinct weights and oddness are modular up to character twist. Every condition has now been checked at \(p=5\). No residual irreducibility assumption, local ordinary assumption, or missing \(p=3\) modularity theorem is being inserted. The historical Pan \(v_{2}\) Theorem1.0.4, p.5, was also read; its exceptional residual condition occurs only at 3. Final Pan JAMS body retrieval returned 403. We do not claim to have compared that body, or to have recursively re-audited its proof. The immediate final published Calegari statement is independently available and directly applicable under the protocol's published-theorem boundary.
+Calegari's final EMS ICM 2022 volume 2 chapter, published 2023, definitions pp.611--612 and statement p.624, is the immediate published theorem: continuous irreducible geometric two-dimensional representations at \(p\ge 5\) with distinct weights and oddness are modular up to character twist. Every condition has now been checked at \(p=5\). No residual irreducibility assumption, local ordinary assumption, or missing \(p=3\) modularity theorem is being inserted. Pan version 2, Theorem 1.0.4, p.5, has an exceptional residual condition only at 3. Its final JAMS body has not been compared with that author version. The immediate input is the final published Calegari statement under the hypotheses checked above.

 \subsection{\(M_{3}\). Weight, finite twist and final primitive form}

 The theorem gives \(r_{5}=U_{g}\) tensor \(\delta \) after finite coefficient enlargement, with a classical nonzero cuspidal eigenform \(g\) of positive integral weight \(k\). Select a normalized primitive constituent before determining \(k:\) Deligne--Serre1974 \S{}1.9, p.510, decomposes \(g\) into primitive oldforms; \S{}1.6, p.509, shows good-prime \(T_{q}\) commutes with each degeneracy map since its index is prime to \(q\). Uniqueness of the decomposition forces every nonzero constituent to have g's good-prime eigenvalues. \S{}1.7 normalizes \(a_{1}=1\). Its realization \(U_{f}\) therefore equals \(U_{g}\) by \S{}3.2, p.513, applied after semisimplification.

-If \(k=1\), Deligne--Serre Theorem4.1, pp.513--514, gives a finite-image irreducible representation; \S{}3.1 uses the discrete complex topology, and \S{}\S{}8.2,8.5--8.6 realize it over a number field. It has a finite-image 5-adic realization with these same polynomials. After a finite local extension kills that image, \(r_{5}\) becomes two copies of \(\delta \). Kato \S{}9.2 preserves de Rhamness and weights under that extension; subobject closure gives two equal weights, contradicting \{0,-1\}. Thus \(k\ge 2\).
+If \(k=1\), Deligne--Serre Theorem 4.1, pp.513--514, gives a finite-image irreducible representation; \S{}3.1 uses the discrete complex topology, and \S{}\S{}8.2,8.5--8.6 realize it over a number field. It has a finite-image 5-adic realization with these same polynomials. After a finite local extension kills that image, \(r_{5}\) becomes two copies of \(\delta \). Kato \S{}9.2 preserves de Rhamness and weights under that extension; subobject closure gives two equal weights, contradicting \{0,-1\}. Thus \(k\ge 2\).

-Use Kato's exact coefficient realization \(V=V_{E_{f},\lambda }(f)\), \S{}\S{}6.3 and9.4, pp.161--162,188. Its two-dimensional de Rham filtration has jumps 0,k-1; its middle step has dimension one. Small original levels are handled by \S{}\S{}5.4/8.3 through fine-level invariants; \(p\) may divide \(N\). Equations14.10.2--3, p.240, put the polynomial \(1-a_{q}\) \(X+\epsilon _{f}(q)q^{k-1}X^{2}\) on inverse arithmetic Frobenius in \(V\). Thus \(U_{f}=V^{\text{dual}}\), det \(U_{f}=\epsilon _{f}\) \(\kappa ^{k-1}\), and \(HT(U_{f})=\{0,1-k\}\). Equality follows first on semisimplifications; since \(U_{f}\) is an irreducible twist of \(r_{5}\), the matched two-dimensional object has composition length one and is actually isomorphic. There is no further Tate twist.
+Use Kato's exact coefficient realization \(V=V_{E_{f},\lambda }(f)\), \S{}\S{}6.3 and 9.4, pp.161--162,188. Its two-dimensional de Rham filtration has jumps 0,k-1; its middle step has dimension one. Small original levels are handled by \S{}\S{}5.4/8.3 through fine-level invariants; \(p\) may divide \(N\). Equations 14.10.2--3, p.240, put the polynomial \(1-a_{q}\) \(X+\epsilon _{f}(q)q^{k-1}X^{2}\) on inverse arithmetic Frobenius in \(V\). Thus \(U_{f}=V^{\text{dual}}\), det \(U_{f}=\epsilon _{f}\) \(\kappa ^{k-1}\), and \(HT(U_{f})=\{0,1-k\}\). Equality follows first on semisimplifications; since \(U_{f}\) is an irreducible twist of \(r_{5}\), the matched two-dimensional object has composition length one and is actually isomorphic. There is no further Tate twist.

 The delta-line in \(\operatorname{Hom}(U_{f},r_{5})\) is a de Rham subobject. If its weight is \(h\), \(\{h,h+1-k\}=\{0,-1\}\); \(k\ge 2\) gives \(h=0,k=2\). Put \(\alpha =\operatorname{det}(r_{5})/\kappa \). On \(G_{L'}\), the polarization determinant gives \(\alpha ^{2}=1\), hence \(\alpha \) has finite global image. Taking determinants gives \(\delta ^{2}=\alpha /\epsilon _{f}\), which is finite. Each nonzero scalar has at most two square roots; \(\delta \) is finite. Weight zero alone was not used to infer this.

-To obtain a Dirichlet twist one may use the inherited Washington Theorem14.1; its final page was not reacquired here. The following replacement uses the final published Milne ADT already inspected: I.1.3 and1.6(c), pp.18--19, give global reciprocity for the idele class group, compatible with the local maps. Composing the finite character \(\delta \) with reciprocity gives a finite continuous idele-class character. The connected positive real component acts trivially. Every rational idele class has a representative whose finite components lie in \(\prod  Z_{p}^{*}\), unique after choosing positive real component; this follows by multiplying by the rational product of its finite uniformizer powers. A finite continuous character of that compact product factors through \((Z/rZ)^{*}\) for some \(r\). Take \(r\) to be the least such modulus; the Dirichlet character \(\eta \) defined below is then primitive of conductor \(r\). This choice changes neither \(\delta \) nor the controlled field \(L'\). Write \(\lambda \) for this idele-class character. In the decomposition \(C_{Q}=R_{>0}\) times \(\prod  Z_{p}^{*}\), the idele which is a uniformizer \(q\) at \(q\) and1 elsewhere is represented, after multiplication by \(q^{-1}\), by positive real component1/q and finite units \(q^{-1}\) at every \(p\ne q\) and1 at \(q\). Therefore, with arithmetic reciprocity, define \(\eta \) on \((Z/rZ)^{*}\) to be the inverse of \(\lambda \) restricted to the finite units; then \(\eta (q)=\delta (\text{Frob}_{q})\) for \(q\) prime to \(r\). If the published reciprocity convention is inverse arithmetic, invert that reciprocity map first. This retains the necessary inverse on the finite-unit character rather than silently reversing the twist. This derivation uses neither Washington's unreacquired page nor an unpublished theorem.
+To obtain a Dirichlet twist one may use the inherited Washington Theorem 14.1; its final page was not reacquired here. The following replacement uses the final published Milne ADT: I.1.3 and 1.6(c), pp.18--19, give global reciprocity for the idele class group, compatible with the local maps. Composing the finite character \(\delta \) with reciprocity gives a finite continuous idele-class character. The connected positive real component acts trivially. Every rational idele class has a representative whose finite components lie in \(\prod  Z_{p}^{*}\), unique after choosing positive real component; this follows by multiplying by the rational product of its finite uniformizer powers. A finite continuous character of that compact product factors through \((Z/rZ)^{*}\) for some \(r\). Take \(r\) to be the least such modulus; the Dirichlet character \(\eta \) defined below is then primitive of conductor \(r\). This choice changes neither \(\delta \) nor the controlled field \(L'\). Write \(\lambda \) for this idele-class character. In the decomposition \(C_{Q}=R_{>0}\) times \(\prod  Z_{p}^{*}\), the idele which is a uniformizer \(q\) at \(q\) and 1 elsewhere is represented, after multiplication by \(q^{-1}\), by positive real component 1/q and finite units \(q^{-1}\) at every \(p\ne q\) and 1 at \(q\). Therefore, with arithmetic reciprocity, define \(\eta \) on \((Z/rZ)^{*}\) to be the inverse of \(\lambda \) restricted to the finite units; then \(\eta (q)=\delta (\text{Frob}_{q})\) for \(q\) prime to \(r\). If the published reciprocity convention is inverse arithmetic, invert that reciprocity map first. This retains the necessary inverse on the finite-unit character rather than silently reversing the twist. This derivation uses neither Washington's unreacquired page nor an unpublished theorem.

-Shimura1973 \S{}4 equation4.1, p.531, sends \(f\) to a nonzero Gauss sum times \(h=\sum \) \(\eta (n)a_{n}(f)q^{n}\) at level \(Mr^{2}\). For \(\gamma =(A B;C D)\) in \(\Gamma _{0}(Mr^{2})\), the translation indices reindex by a \(\to \) \(aD^{2}\) mod \(r\); their weights transform by \(\eta (D)^{2}\), so \(h\) has nebentypus \(\epsilon _{f}\) \(\eta ^{2}\). The coefficient formula gives \(T_{q}\) \(h=\eta (q)a_{q}(f)h\) for \(q\) not dividing Mr, and \(h_{1}=1\). Select a primitive constituent using the same Deligne--Serre \S{}\S{}1.6--1.9 decomposition just proved. Its good-prime traces identify its Tate realization with \(U_{f}\) tensor \(\delta \), hence with the original \(r_{5}\). Call this \textbf{final} primitive form \(f\) and its actual level \(N\).
+Shimura 1973 \S{}4 equation 4.1, p.531, sends \(f\) to a nonzero Gauss sum times \(h=\sum \) \(\eta (n)a_{n}(f)q^{n}\) at level \(Mr^{2}\). For \(\gamma =(A B;C D)\) in \(\Gamma _{0}(Mr^{2})\), the translation indices reindex by a \(\to \) \(aD^{2}\) mod \(r\); their weights transform by \(\eta (D)^{2}\), so \(h\) has nebentypus \(\epsilon _{f}\) \(\eta ^{2}\). The coefficient formula gives \(T_{q}\) \(h=\eta (q)a_{q}(f)h\) for \(q\) not dividing Mr, and \(h_{1}=1\). Select a primitive constituent using the same Deligne--Serre \S{}\S{}1.6--1.9 decomposition just proved. Its good-prime traces identify its Tate realization with \(U_{f}\) tensor \(\delta \), hence with the original \(r_{5}\). Call this \textbf{final} primitive form \(f\) and its actual level \(N\).

-Precision repair: Li1975 Theorem5, p.298, proves uniqueness of normalized primitive forms from almost-all prime eigenvalues. It does not itself assert existence of a primitive constituent. The current \(V_{15}\) p294/Theorem5 citation should not bear that existence claim alone. The explicit Deligne--Serre extraction above repairs the application without changing its arithmetic conclusion. Li's actual Fricke statement is used separately below.
+Li 1975 Theorem 5, p.298, proves uniqueness of normalized primitive forms from almost-all prime eigenvalues. It does not itself assert existence of a primitive constituent. Existence is supplied by the explicit Deligne--Serre extraction above. Li's actual Fricke statement is used separately below.

 \subsection{\(M_{4}\). Original companion \(r_{3}\) and full prime coverage}

-Fix a common coefficient number field containing the original \(a_{\sigma },b-\text{values}\), the \(B\) splitting field and final f's coefficients. Extend the original embeddings at 5 and3; do not alter either \(r_{\ell }\). For the comparison alone, spread the finitely many varieties and quasi-isogenies over a finite Galois auxiliary field \(K\) and clear denominators by an integer \(n\). Remove finitely many rational primes so all reductions and spread maps are smooth proper abelian schemes and \(n\) \(\mu _{\sigma }\) are homomorphisms; remove primes ramified in \(K\) as well. This comparison set is not \(T\) and its size enters no estimate.
+Fix a common coefficient number field containing the original \(a_{\sigma },b-\text{values}\), the \(B\) splitting field and final f's coefficients. Extend the original embeddings at 5 and 3; do not alter either \(r_{\ell }\). For the comparison alone, spread the finitely many varieties and quasi-isogenies over a finite Galois auxiliary field \(K\) and clear denominators by an integer \(n\). Remove finitely many rational primes so all reductions and spread maps are smooth proper abelian schemes and \(n\) \(\mu _{\sigma }\) are homomorphisms; remove primes ramified in \(K\) as well. This comparison set is not \(T\) and its size enters no estimate.

 At a remaining \(p\), choose v|p and an arithmetic Frobenius \(\sigma _{p}\). Reduction of \(\sigma _{p}\) A is the p-twist of \(A_{v}\). The source/target of \(\mu _{\sigma }\) is \(\sigma \) A \(\to \) A. Therefore

```

### H022

Class: status, source locator or provenance prose. Base 2612-2638; candidate 2607-2633.

```diff
@@ -2612,27 +2607,27 @@
 e_{p} = \operatorname{reduction} (n \mu _{{\sigma }_{p}}) \circ  \text{ with }  \text{ relative }  Fr_{p,A_{v}}
 \end{gather*}

-is an actual endomorphism of \(A_{v}\). It is relative p-Frobenius, not the residue-cardinality Frobenius. Milne1986 Proposition12.9 and its definition, p.125, give a common rational degree polynomial on every \(V_{\ell }\) for \(\ell \ne p\). Put \(q_{p}=\operatorname{Tr}(e_{p})/n\) in \(Q\); retain division by \(n\). Finite etale \(\ell ^{j}\) torsion specializes compatibly with multiplication-by-ell transitions and \(n\) \(\mu _{\sigma }\), so
+is an actual endomorphism of \(A_{v}\). It is relative p-Frobenius, not the residue-cardinality Frobenius. Milne 1986 Proposition 12.9 and its definition, p.125, give a common rational degree polynomial on every \(V_{\ell }\) for \(\ell \ne p\). Put \(q_{p}=\operatorname{Tr}(e_{p})/n\) in \(Q\); retain division by \(n\). Finite etale \(\ell ^{j}\) torsion specializes compatibly with multiplication-by-ell transitions and \(n\) \(\mu _{\sigma }\), so

 \begin{gather*}
-\operatorname{tr} r_{\ell }(\sigma _{p}) = \iota _{\ell }((a_{{\sigma }_{p}}/b(\sigma _{p}))*q_{p}/2)
+\operatorname{tr} r_{\ell }(\sigma _{p}) = \iota _{\ell }((a_{{\sigma }_{p}}/b(\sigma _{p}))\cdot q_{p}/2)
 \end{gather*}

-The factor 1/2 is from the two identical summands, not an omitted scalar. The algebraic number \(\tau _{p}\) in parentheses lies in the common coefficient field. The isomorphism at5 gives \(\iota _{5}(\tau _{p})=\iota _{5}(a_{p}(f))\), hence equality in that field. Applying \(\iota _{3}\) gives equality of traces with \(U_{f,3}\) outside finitely many primes. Serre's published 1968 text/1989 reprint, ChapterI \S{}2.2 Corollary2 and \S{}2.3 theorem and lemma, pp.I-8,I-10--11, gives density and semisimple trace uniqueness. \(r_{3}\) is absolutely irreducible by \(M_{2}\); thus \(U_{f,3}^{ss}=r_{3}\) has a single simple constituent, forcing the full \(U_{f,3}\) to be irreducible and isomorphic to \(r_{3}\). This is an isomorphism on \(G_{Q}\), including its restriction at 5. It is not only an equality of local semisimplified traces.
+The factor 1/2 is from the two identical summands, not an omitted scalar. The algebraic number \(\tau _{p}\) in parentheses lies in the common coefficient field. The isomorphism at 5 gives \(\iota _{5}(\tau _{p})=\iota _{5}(a_{p}(f))\), hence equality in that field. Applying \(\iota _{3}\) gives equality of traces with \(U_{f,3}\) outside finitely many primes. Serre's published 1968 text/1989 reprint, ChapterI \S{}2.2 Corollary 2 and \S{}2.3 theorem and lemma, pp.I-8,I-10--11, gives density and semisimple trace uniqueness. \(r_{3}\) is absolutely irreducible by \(M_{2}\); thus \(U_{f,3}^{ss}=r_{3}\) has a single simple constituent, forcing the full \(U_{f,3}\) to be irreducible and isomorphic to \(r_{3}\). This is an isomorphism on \(G_{Q}\), including its restriction at 5. It is not only an equality of local semisimplified traces.

-The same argument works for every coefficient prime, but only the pair 5 and3 is needed: at residue \(p\ne 5\) use \(r_{5}\), and at \(p=5\) use \(r_{3}\). This explicitly covers the full residue-prime index set without a \(p=\ell \) compatibility assertion.
+The same argument works for every coefficient prime, but only the pair 5 and 3 is needed: at residue \(p\ne 5\) use \(r_{5}\), and at \(p=5\) use \(r_{3}\). This explicitly covers the full residue-prime index set without a \(p=\ell \) compatibility assertion.

 \subsection{\(M_{5}\). Final level and changed-lift conductor bound}

-Use Carayol1987 final Astérisque147--148, \S{}\S{}2.1/2.4/4.1, printed36,37,42. Its normalized new cuspidal form permits arbitrary Dirichlet nebentypus and \(\text{weight}\ge 2\). The full Theorem4 removes the unramified-principal-series condition of Theorem3; the following deduction affirms the conductor question of \S{}2.4. The separately stated weak theorem's extraordinary-cuspidal exclusion is not a restriction on Theorem4. \(Q\) has odd degree1. Thus all dyadic cases and all \(N\) are included. The cohomological dual and unramified norm normalization change no Artin conductor. M4's actual global isomorphism identifies the full local object, preserving inertia invariants and Swan terms; no inertia semisimplification drops monodromy. Consequently
+Use Carayol 1987 final Ast\'erisque 147--148, \S{}\S{}2.1/2.4/4.1, printed 36,37,42. Its normalized new cuspidal form permits arbitrary Dirichlet nebentypus and \(\text{weight}\ge 2\). The full Theorem 4 removes the unramified-principal-series condition of Theorem 3; the following deduction affirms the conductor question of \S{}2.4. The separately stated weak theorem's extraordinary-cuspidal exclusion is not a restriction on Theorem 4. \(Q\) has odd degree 1. Thus all dyadic cases and all \(N\) are included. The cohomological dual and unramified norm normalization change no Artin conductor. M4's actual global isomorphism identifies the full local object, preserving inertia invariants and Swan terms; no inertia semisimplification drops monodromy. Consequently

 \begin{gather*}
 v_{p}(N)=a_{p}(r_{\ell }), \text{ for }  \ell \ne p,
 \end{gather*}

-with the pair \((\ell =5 \text{ for }  p\ne 5; \ell =3 \text{ for }  p=5)\). This replaces the old private parent9 Casselman/Carayol-TheoremA chain at this exact conclusion. It does not purport to accept that separately formulated automorphic chain.
+with the pair \((\ell =5 \text{ for }  p\ne 5; \ell =3 \text{ for }  p=5)\). This replaces the old private parent9 Casselman/Carayol-TheoremA chain at this exact conclusion. It does not supply that separately formulated automorphic chain.

-For completeness the changed lift preserves every numerical hypothesis of parent9 \S{}\S{}1--3. \(E=L(A[11])\) is normal and [E:Q] divides \(576|\operatorname{GL}_{4}(F_{11})|\) by the retained prime-to11 normalizer isogenies. The order is 23842542097059840000 with valuations at (2,3,5,7) equal to (15,4,4,1). The full11-torsion semistability criterion is used only in those four residue characteristics, and the division-B torus argument makes reduction good. Put \(F=E\) \(Q(\chi )\), where \(Q(\chi )\) denotes its \textbf{kernel field}, and let F'/F kill the quadratic character \(b|G_{F}\). Both fields are normal. At odd \(p\) the added character and quadratic extension are tame; at2 the \(\chi \) inertia has \(\text{order}\le 2\) and the second extension \(\text{degree}\le 2\). Hence \(v_{p}(e(F'/Q))\le (17,4,4,1)\). This is a wild-part bound, with no upper bound on the tame part.
+For completeness the changed lift preserves every numerical hypothesis of parent9 \S{}\S{}1--3. \(E=L(A[11])\) is normal and [E:Q] divides \(576|\operatorname{GL}_{4}(F_{11})|\) by the retained prime-to-11 normalizer isogenies. The order is 23842542097059840000 with valuations at (2,3,5,7) equal to (15,4,4,1). The full 11-torsion semistability criterion is used only in those four residue characteristics, and the division-B torus argument makes reduction good. Put \(F=E\) \(Q(\chi )\), where \(Q(\chi )\) denotes its \textbf{kernel field}, and let F'/F kill the quadratic character \(b|G_{F}\). Both fields are normal. At odd \(p\) the added character and quadratic extension are tame; at 2 the \(\chi \) inertia has \(\text{order}\le 2\) and the second extension \(\text{degree}\le 2\). Hence \(v_{p}(e(F'/Q))\le (17,4,4,1)\). This is a wild-part bound, with no upper bound on the tame part.

 Here is the original derivative argument, independently restated. For the totally ramified part \(K/K_{0}\) of a finite Galois \(Q_{p}-\text{extension}\), an Eisenstein uniformizer polynomial of degree \(e\) has derivative terms of distinct valuations modulo \(e\). Its different exponent satisfies \(d_{K}\le e\) \(v_{p}(e)+e-1\). Hilbert's derivative product gives \(d_{K}=\sum _{i\ge 0}(|G_{i}|-1)\). The Herbrand change of variable therefore yields

```

### H023

Class: status, source locator or provenance prose. Base 2640-2648; candidate 2635-2643.

```diff
@@ -2640,9 +2635,9 @@
 d_{K}/e = 1-1/e + \int _{0,\infty }(1-1/|G^{u}|)du
 \end{gather*}

-Before the last positive upper break \(b_{\text{last}}\) the integrand is at least1/2, so \(b_{\text{last}}\le 2\) \(v_{p}(e)\). Quotient compatibility of upper numbering then bounds the Swan conductor of the actual two-dimensional \(r_{\ell }\) by 2 \(b_{\text{last}}\), with tame \(\text{codimension}\le 2\). Thus exponents are \(\le (70,18,18,6)\). At \(p>7\), L/Q is tame since its degree divides576, A/L has good reduction, and \(b\) is trivial on wild inertia by \(M_{1}\). Thus \(a_{p}\le 2\) there and \(a_{p}=0\) outside \(T\). No11-torsion semistability argument is used at residue11. \nolinkurl{PROVIDER_SCOPE_CARRY.md} \(P_{4}\) supplies the exact current-source carry: the final Silverberg--Zarhin1995 Theorems3.4/3.5 have been directly read at the same public PDF hash; the exact previously accepted Serre1967 chapterVI ramification application is retained at its general finite-local-Galois-extension scope. It is not the1979 Local Fields book. The changed wild valuations and maps to the actual \(r_{\ell }\) are proved anew here.
+Before the last positive upper break \(b_{\text{last}}\) the integrand is at least 1/2, so \(b_{\text{last}}\le 2\) \(v_{p}(e)\). Quotient compatibility of upper numbering then bounds the Swan conductor of the actual two-dimensional \(r_{\ell }\) by 2 \(b_{\text{last}}\), with tame \(\text{codimension}\le 2\). Thus exponents are \(\le (70,18,18,6)\). At \(p>7\), L/Q is tame since its degree divides 576, A/L has good reduction, and \(b\) is trivial on wild inertia by \(M_{1}\). Thus \(a_{p}\le 2\) there and \(a_{p}=0\) outside \(T\). No11-torsion semistability argument is used at residue 11. \nolinkurl{PROVIDER_SCOPE_CARRY.md} \(P_{4}\) supplies the exact current-source carry: the final Silverberg--Zarhin1995 Theorems 3.4/3.5 are identified by the same public PDF hash; the exact Serre 1967 chapter VI ramification application is retained at its general finite-local-Galois-extension scope. It is not the 1979 Local Fields book. The changed wild valuations and maps to the actual \(r_{\ell }\) are proved anew here.

-Absorb baseline exponent2 at 2,3,5,7 into squarefree \(R^{2}\) to obtain
+Absorb baseline exponent 2 at 2,3,5,7 into squarefree \(R^{2}\) to obtain

 \begin{gather*}
 N \le  C_{N} R^{2}, \operatorname{rad}(N)|R, C_{N}=2^{68} 3^{16} 5^{16} 7^{4}
```

### H024

Class: whitespace only. Base 2674-2680; candidate 2669-2675.

```diff
@@ -2674,7 +2669,7 @@
 \operatorname{det} \rho _{\ell } = b^{-4} \kappa ^{2} = \chi ^{-2} \kappa ^{2}
 \end{gather*}

-The final modular identity gives det \(\rho _{5}=\epsilon _{f}^{2}\) \(\kappa ^{2}\). Thus \((\epsilon _{f} \chi )^{2}=1\). Because \(U\) is an even power of2 and m|U, \(s=\operatorname{ord}(\epsilon _{f})\) divides \(U\). The weight-two -I condition gives \(\epsilon _{f}(-1)=1\). Also U|phi(R) and
+The final modular identity gives det \(\rho _{5}=\epsilon _{f}^{2}\) \(\kappa ^{2}\). Thus \((\epsilon _{f} \chi )^{2}=1\). Because \(U\) is an even power of 2 and m|U, \(s=\operatorname{ord}(\epsilon _{f})\) divides \(U\). The weight-two -I condition gives \(\epsilon _{f}(-1)=1\). Also U|phi(R) and

 \begin{gather*}
 s \prod _{p|R}(1+1/p) \le  R \prod _{p|R}(1-p^{-2}) < R
```

### H025

Class: status, source locator or provenance prose. Base 2682-2708; candidate 2677-2701.

```diff
@@ -2682,27 +2677,25 @@

 The statement U|phi(R) includes \(R\) with no new prime outside \(S\). No uniform bound on \(U\) or \([E_{f}:Q]\) is asserted.

-Let \(E_{f}=Q(a_{n}(f))\), \(e=[E_{f}:Q]\). Li's actual final \(p_{296}\) formula \(f|H_{N}=\gamma \) f|K, \(\gamma \ne 0\), shows that the span of \textbf{all} coefficient conjugates is Fricke-stable: for each embedding \(\tau \), conjugating that embedding produces another of the same field. Apply it at Li's \((M,1)=(N,1)\), with arbitrary \(\epsilon _{f}\), to the final form after absorption. Shimura1973 Theorem1, pp.526--527, then gives \(A_{f}/Q\), dimension \(e\), a quotient of \(J_{1}(N)\), differential span all \(f^{\tau }\) and the Euler factor identity. Its Tate module over \(\text{Qbar}_{5}\) is the sum of all \(U_{f,5}^{\tau }\); the cohomological statement is dualized consistently.
+Let \(E_{f}=Q(a_{n}(f))\), \(e=[E_{f}:Q]\). Li's actual final p.~296 formula \(f|H_{N}=\gamma \) f|K, \(\gamma \ne 0\), shows that the span of \textbf{all} coefficient conjugates is Fricke-stable: for each embedding \(\tau \), conjugating that embedding produces another of the same field. Apply it at Li's \((M,1)=(N,1)\), with arbitrary \(\epsilon _{f}\), to the final form after absorption. Shimura 1973 Theorem 1, pp.526--527, then gives \(A_{f}/Q\), dimension \(e\), a quotient of \(J_{1}(N)\), differential span all \(f^{\tau }\) and the Euler factor identity. Its Tate module over \(\overline{\mathbb Q}_{5}\) is the sum of all \(U_{f,5}^{\tau }\); the cohomological statement is dualized consistently.

-At a good place \(v\) of the actual \(L'\), with residue degree \(f_{v}\) over \(p\), tr \(r_{f}(\text{Frob}_{v})\) is an \(E_{f}\) element: it is the trace of the \(f_{v}-th\) power of a matrix with polynomial \(X^{2}-a_{p}\) X+p \(\epsilon _{f}(p)\). Its equality at the fixed embedding5 to half the rational Tate trace of A identifies it with a rational number in \(E_{f}\). Every embedding \(\tau \) fixes that number. Faltings semisimplicity and Serre's general-number-field density/trace criterion therefore identify every \(r_{f}^{\tau }|G_{L'}\) with the same absolutely irreducible \(W\). All \(e\) embeddings enter; no subset or bounded coefficient field is substituted.
+At a good place \(v\) of the actual \(L'\), with residue degree \(f_{v}\) over \(p\), tr \(r_{f}(\text{Frob}_{v})\) is an \(E_{f}\) element: it is the trace of the \(f_{v}-th\) power of a matrix with polynomial \(X^{2}-a_{p}\) X+p \(\epsilon _{f}(p)\). Its equality at the fixed embedding 5 to half the rational Tate trace of A identifies it with a rational number in \(E_{f}\). Every embedding \(\tau \) fixes that number. Faltings semisimplicity and Serre's general-number-field density/trace criterion therefore identify every \(r_{f}^{\tau }|G_{L'}\) with the same absolutely irreducible \(W\). All \(e\) embeddings enter; no subset or bounded coefficient field is substituted.

-Consequently \(((A_{f})_{L'})^{2}\) and \(A^{e}\) have isomorphic rational Tate modules. The rational isomorphism descends from coefficient extension because an invertible element exists in the finite-dimensional intertwiner space over \(Q_{5}:\) invertibility is a nonempty Zariski-open condition and \(Q_{5}\) is infinite. Faltings' End theorem applied to their product gives the Hom comparison. Rational combinations of actual Hom maps are dense in its \(Q_{5}\) extension, so an invertible Tate map may be chosen over \(Q\) and then denominators cleared; it is an L'-isogeny. Poincare reducibility, Milne1986 Proposition12.1 and following paragraph, p.122, applies over that same ground field. A is absolutely simple, so every simple factor of \((A_{f})_{L'}\) is L'-isogenous to A. Dimensions force \(e=2r\) and \((A_{f})_{L'}\sim A^{r}\) over \(L'\). This does not use invariance of Faltings height under isogeny.
+Consequently \(((A_{f})_{L'})^{2}\) and \(A^{e}\) have isomorphic rational Tate modules. The rational isomorphism descends from coefficient extension because an invertible element exists in the finite-dimensional intertwiner space over \(Q_{5}:\) invertibility is a nonempty Zariski-open condition and \(Q_{5}\) is infinite. Faltings' End theorem applied to their product gives the Hom comparison. Rational combinations of actual Hom maps are dense in its \(Q_{5}\) extension, so an invertible Tate map may be chosen over \(Q\) and then denominators cleared; it is an L'-isogeny. Poincare reducibility, Milne 1986 Proposition 12.1 and following paragraph, p.122, applies over that same ground field. A is absolutely simple, so every simple factor of \((A_{f})_{L'}\) is L'-isogenous to A. Dimensions force \(e=2r\) and \((A_{f})_{L'}\sim A^{r}\) over \(L'\). This does not use invariance of Faltings height under isogeny.

-The good-prime Hecke relation \(\epsilon _{f}(p)=(a_{p}^{2}-a_{p^{2}})/p\) and density in the finite cyclotomic quotient put the full image of \(\epsilon _{f}\) in \(E_{f}\). Hence \(Q(\zeta _{s})\) embeds into \(E_{f}\), \(r\ge \phi (s)/2\), and \(s/r\le 4:\) for \(s\ge 4\) a power of2 use \(\phi (s)=s/2\); for \(s=1,2\) use \(r\ge 1\).
+The good-prime Hecke relation \(\epsilon _{f}(p)=(a_{p}^{2}-a_{p^{2}})/p\) and density in the finite cyclotomic quotient put the full image of \(\epsilon _{f}\) in \(E_{f}\). Hence \(Q(\zeta _{s})\) embeds into \(E_{f}\), \(r\ge \phi (s)/2\), and \(s/r\le 4:\) for \(s\ge 4\) a power of 2 use \(\phi (s)=s/2\); for \(s=1,2\) use \(r\ge 1\).

 Put \(H=\operatorname{ker}\) \(\epsilon _{f}\). Every coefficient conjugate has the same kernel \(H\), so the entire \(A_{f}\) differential span is H-invariant. Pullback under \(X_{1}(N)\to X_{H}\) identifies differentials with invariants; on Jacobians the pullback image is the invariant subvariety up to isogeny, since the norm composed with pullback is multiplication by deg and is invertible in Hom tensor \(Q\). The \(A_{f}\) quotient restricts surjectively to that image, as its cotangent map is injective on the same H-fixed differentials. Poincare reducibility over \(Q\) therefore supplies a Q-subvariety isogenous to \(A_{f}\). Base-changing to \(L'\) gives the actual \(B_{0}\) subset \(J_{L'}\) isogenous over \(L'\) to \(A^{r}\), so \(g\ge 2r\ge 2\). It supplies exactly the surfaces of \(H_{3}\). The modular evaluation-fiber field plays no role.

-\subsection{\(M_{7}\). Historical and current dispositions}
+\subsection{\(M_{7}\). Source scope}

-Actual earlier arguments read include private frozen \(V_{14}\) lemma481--660, b-family8097--8347 (including original r5/r3 and CL1/CL2); cutoff \S{}1; parent9 \S{}\S{}1--3; heightH0--H4; the published-source Faltings/Poincare/Li bridge; public \(V_{15}\) lemma505--705, baseline1334--1505 and b-family; direct-p5 PROOF, FAMILY-CONNECTION, FIVE-TO-THREE and CLASSICAL-LOCAL; the later direct Carayol proof and source statement. These establish \textbf{prior justification found} for the general normalized modularity, same-form companion and numerical conductor derivations. The new minimal-character choice is an explicitly changed application requiring this fresh proof and fresh review. The old qualification rollup's final-Pan access limitation is preserved as history; it is not a reason to deny applicability of Calegari's actually read final published theorem. The Li existence locator needs the explicit repair \(M_{3}\). General source statements carry independently of \(\chi \); no approval carries to a revised constructed representation by itself.
-
-Current incorporation is \textbf{pending} for this additive bridge. Current acceptance is \textbf{pending} a nonauthor reviewer on the final hashes. No final-Pan-body comparison or complete214 theorem is inferred. The actual \(D_{210}\) \(H_{01}\) provider/source composition and the exact retained Serre1967/full11 conductor applications are now supplied in \nolinkurl{GEOMETRY_CARRY.md} and \nolinkurl{PROVIDER_SCOPE_CARRY.md;} their current acceptance is pending the nonauthor reviewer. \nolinkurl{SOURCE_USES_FINAL.json} and \nolinkurl{FINDINGS.md} name the remaining scope limits precisely.
+The normalized modularity, same-form companion and numerical conductor arguments use the source applications specified above. General source statements are independent of \(\chi \). The minimal-character choice is a changed application and requires the proof given here; a general source statement alone does not supply its application to the revised representation. The final Pan JAMS body has not been compared. The immediate modularity input is Calegari's final published theorem. Primitive-constituent existence uses the Deligne--Serre extraction in \(M_{3}\). The \(D_{210}\) \(H_{01}\) construction and the retained Serre 1967/full 11 conductor applications are specified in \nolinkurl{GEOMETRY_CARRY.md} and \nolinkurl{PROVIDER_SCOPE_CARRY.md}. The remaining source scopes are recorded in \nolinkurl{SOURCE_USES_FINAL.json} and \nolinkurl{FINDINGS.md}.
 \clearpage
 % Source: research/quartic214/proofs/height-evaluation.md
 \section{Integral evaluation and the trace-dual lattice}\label{q214:height-evaluation}
 \noindent\textit{Source: }\nolinkurl{research/quartic214/proofs/height-evaluation.md}.\par

-\begin{quote}\footnotesize Author: internal model agent \nolinkurl{/root/d214_integral_evaluation}, 2026-11-10. This is a proposed source/application bridge, not independent acceptance. Frozen private repository: \nolinkurl{a81afd7996a20e6b7bb5e48670418541c036d7aa}. The exact target is Brox \(v_{17}\), \nolinkurl{research/quadratic-ten-contact-integration/height/sources/brox-v17.tex}, lines 87--99, 117--209 and its consumer at 218--225. Whole-file and passage bindings are in \nolinkurl{SOURCE_USES.json} and \nolinkurl{CONTRACT.json}.\end{quote}
+\begin{quote}\footnotesize Frozen private repository: \nolinkurl{a81afd7996a20e6b7bb5e48670418541c036d7aa}. The exact target is Brox \(v_{17}\), lines 87--99, 117--209 and its consumer at 218--225. The retained public excerpt is \nolinkurl{research/quartic214/sources/evaluation-sections1-4.tex}. Whole-file and passage bindings are in \nolinkurl{SOURCE_USES.json} and \nolinkurl{CONTRACT.json}.\end{quote}

 The conclusion proposed here is exactly the integral map

```

### H026

Class: prose, notation or text-conversion cleanup; inspect both sides. Base 2729-2735; candidate 2722-2728.

```diff
@@ -2729,7 +2722,7 @@

 All three hypotheses of miracle flatness 00R4 are now checked, including its dimension equality. Hence \(B_{q}\) is \(A_{p}-\text{flat}\) at every \(q\). Flatness is local, so \(B\) is finite flat, consequently finite projective, of rank \(d\). The same holds on the second target chart. \(Y\) is an integral normal proper flat arithmetic surface, finite over \(P^{1}_{R}\). No smoothness of its special fibres and no Gorenstein property of \(Y\) is asserted.

-Consequently \(C=B\otimes _{A}\) \(R=B/(t-2)B\) is finite projective of rank \(d\) over \(R\). Its generic fibre is the \textbf{specified} \(K^{d}\) via evaluation at \(P_{i}\). Its map into \(K^{d}\) is injective because \(C\) is R-torsion-free. Each coordinate of an element of \(C\) is integral over \(R\) and belongs to \(K\), hence lies in \(R\). Thus \(C\subset O:=R^{d}\) with full rank. No claim that \(C\) is reduced modulo a finite prime, étale over \(R\), or normal is needed.
+Consequently \(C=B\otimes _{A}\) \(R=B/(t-2)B\) is finite projective of rank \(d\) over \(R\). Its generic fibre is the \textbf{specified} \(K^{d}\) via evaluation at \(P_{i}\). Its map into \(K^{d}\) is injective because \(C\) is R-torsion-free. Each coordinate of an element of \(C\) is integral over \(R\) and belongs to \(K\), hence lies in \(R\). Thus \(C\subset O:=R^{d}\) with full rank. No claim that \(C\) is reduced modulo a finite prime, \'etale over \(R\), or normal is needed.

 \subsection{2. A common regular model with the required direction}

```

### H027

Class: prose, notation or text-conversion cleanup; inspect both sides. Base 2776-2784; candidate 2769-2777.

```diff
@@ -2776,9 +2769,9 @@

 There are two separate comparisons; both are necessary.

-First, on an open of the generic t-line avoiding branch points, the finite map is étale. The usual smooth identification of the canonical module with \(\Omega ^{1}\) is the one obtained from the conormal/adjunction construction of Stacks 0E9Z. Its construction uses the determinant of the conormal exact sequence, and therefore commutes with flat base change. Duality transitivity is 0ATX, the tensor comparison is 0B6U, and the flat base-change isomorphism is 0E9U. All schemes here are separated and finite type over the Noetherian base \(R\) (the category defined in 0F42); on the generic chart one can equally work over \(K\).
+First, on an open of the generic t-line avoiding branch points, the finite map is \'etale. The usual smooth identification of the canonical module with \(\Omega ^{1}\) is the one obtained from the conormal/adjunction construction of Stacks 0E9Z. Its construction uses the determinant of the conormal exact sequence, and therefore commutes with flat base change. Duality transitivity is 0ATX, the tensor comparison is 0B6U, and the flat base-change isomorphism is 0E9U. All schemes here are separated and finite type over the Noetherian base \(R\) (the category defined in 0F42); on the generic chart one can equally work over \(K\).

-To compute the identification, use an étale neighbourhood splitting the finite étale cover (04HN). On that neighbourhood \(B\) becomes \(A^{d}\). Both the exterior/conormal construction and finite Hom duality are compatible with this flat base change. For a product of identity morphisms, the i-th differential \(f_{i}\) dt defines the coordinate functional \(b_{i}\mapsto f_{i}\) \(b_{i}\), and finite pushforward sums these functionals. Thus the map is
+To compute the identification, use an \'etale neighbourhood splitting the finite \'etale cover (04HN). On that neighbourhood \(B\) becomes \(A^{d}\). Both the exterior/conormal construction and finite Hom duality are compatible with this flat base change. For a product of identity morphisms, the i-th differential \(f_{i}\) dt defines the coordinate functional \(b_{i}\mapsto f_{i}\) \(b_{i}\), and finite pushforward sums these functionals. Thus the map is

 \[
 (f_i\,dt)_i\longmapsto [\,(b_i)_i\mapsto\sum_i f_i b_i\,]\,dt.
```

### H028

Class: status, source locator or provenance prose. Base 2806-2812; candidate 2799-2805.

```diff
@@ -2806,7 +2799,7 @@

 \subsection{5. Trace-dual projection and arithmetic degree}

-This part is an elementary local calculation, reconstructed here rather than imported from a review verdict. For every nonzero prime \(p\) of \(R\), choose an \(R_{p}-\text{basis}\) of \(C_{p}\), with matrix \(U\) in the coordinate basis of \(O_{p}\). \(U\) has nonzero determinant; trace on \(K^{d}\) is the dot product. The dual basis matrix is \((U^{T})^{-1}\), and the trace Gram matrix is \(U^{T}\) \(U\). Therefore
+This part is an elementary local calculation. For every nonzero prime \(p\) of \(R\), choose an \(R_{p}-\text{basis}\) of \(C_{p}\), with matrix \(U\) in the coordinate basis of \(O_{p}\). \(U\) has nonzero determinant; trace on \(K^{d}\) is the dot product. The dual basis matrix is \((U^{T})^{-1}\), and the trace Gram matrix is \(U^{T}\) \(U\). Therefore

 \[
 \ell_{R_p}(C_p^\vee/O_p)=\ell_{R_p}(O_p/C_p)
```

### H029

Class: status, source locator or provenance prose. Base 2824-2850; candidate 2817-2843.

```diff
@@ -2824,27 +2817,27 @@

 This also checks the sign for an overlattice. The proof treats nonprincipal global modules by local bases, all finite primes including residue characteristic 2, and every \(I\) with \(|I|=g\le d\). The existence of an \(I\) for which evaluation has rank \(g\) belongs to the separate analytic/rank component; this component supplies the lattice conclusion for every such \(I\) once chosen.

-\subsection{6. Exact consumer and bounded status}
+\subsection{6. Exact consumer and scope}

 The output is the same integral map and same trace discriminant used at v17:218--225. Composing with a chosen coordinate projection gives \(E\to F_{I}\); its generic determinant is nonzero only after the rank argument. Combining with the separate metric/determinant proof gives the unchanged Theorem 1.1 estimate. The modular-height consequence feeds \nolinkurl{height/PROOF.md} H0.3 and \(H_{4}\) and the retained existence/global bound, including the downstream 256 route. No replacement order, normalization, extension field, curve or metric has entered this component.

-History: the earlier foundation report had already read a complete project proof of this route and specifically requested source/application closure. The retained quadratic integration review explicitly checked \(v_{17}\) at component scope and kept inherited foundational qualifications. Accordingly this is prior justification found plus an expanded source bridge, proposed for incorporation; it is not evidence that no earlier reviewer had supplied these details. No historical verdict is rewritten. A non-author must review this frozen bridge and its sources before the application can be called independently accepted. This component does not close the full arithmetic theorem or all of Protocol \(D\).
+
 \clearpage
 % Source: research/quartic214/proofs/height-different.md
 \section{Different and modular-model bridge for the retained height bound}\label{q214:height-different}
 \noindent\textit{Source: }\nolinkurl{research/quartic214/proofs/height-different.md}.\par

-\begin{quote}\footnotesize Author: internal model \nolinkurl{/root/d214_different_bounds}, 2026-11-10. This is an author proposal for fresh non-author review. It neither writes nor supplies an independent acceptance. Frozen target: private repository commit \nolinkurl{a81afd7996a20e6b7bb5e48670418541c036d7aa}, \nolinkurl{research/quadratic-ten-contact-integration/height/sources/brox-v17.tex}, SHA-256 \nolinkurl{2ba5dd497276073d92db95f0119bede82d182997c66375e5be294157de6d9f7c}.\end{quote}
+\begin{quote}\footnotesize Frozen target: Brox \(v_{17}\) at private repository commit \nolinkurl{a81afd7996a20e6b7bb5e48670418541c036d7aa}, whole-file SHA-256 \nolinkurl{2ba5dd497276073d92db95f0119bede82d182997c66375e5be294157de6d9f7c}. The retained public excerpt is \nolinkurl{research/quartic214/sources/evaluation-sections1-4.tex}.\end{quote}

 The proposed conclusion is that Brox v17:274--328, 354--451 and 461--488 have the required different bounds, including at every imperfect-residue vertical generic DVR. The resulting bound is unchanged:

 \(\operatorname{log} \operatorname{Norm} \operatorname{disc}(C)/[K:Q] \le  d_{H} (\log 12 + \log N + 2\operatorname{log} d_{H})\).

-Together with the separate integral and analytic evaluation interfaces, which require their own non-author review, this is exactly the input to \nolinkurl{height/PROOF.md} H0.3. No full-torsion splitting-field degree, extra factor two, or changed height constant is introduced. The source citation to Lemma49.12.6 is valid and now bound to its exact current tag0BWJ. The mathematical argument below supplies the expanded explicit source comparisons; incorporation and current independent acceptance remain pending.
+Together with the separate integral and analytic evaluation interfaces, this is exactly the input to \nolinkurl{height/PROOF.md} H0.3. No full-torsion splitting-field degree, extra factor two, or changed height constant is introduced. The source citation to Lemma 49.12.6 is valid and now bound to its exact current tag 0BWJ. The mathematical argument below supplies the expanded explicit source comparisons.

 \subsection{1. Fixed objects and the trace-discriminant identity}

-Put \(R=O_{K}[t]\), where \(K\) is any finite extension used for semistability and splitting the \(t=2\) fibre. Let \(B\) be the normalization of \(R\) in \(K(X)\); let \(d=[K(X):K(t)]\). The integral-evaluation lane supplies finite projectivity of this same \(B\) of rank \(d\). Put \textbf{\(C=B/(t-2)B\)}, retaining this order rather than replacing it with its normalization \(O\). Its generic algebra is \(K^{d}\) after the chosen splitting extension. The determinant of \(B\to \operatorname{Hom}_{R}(B,R)\), \(b\mapsto (b'\mapsto \operatorname{Tr}(bb'))\), is a nonzero section of an invertible line. Base change \(t\mapsto 2\) gives exactly the trace determinant of \(C\), since trace of multiplication on a finite projective module commutes with base change. Thus the section's arithmetic intersection with \(t=2\) is log Norm disc(C). This is an equality of determinant ideals and does not assert that \(C\) is maximal.
+Put \(R=O_{K}[t]\), where \(K\) is any finite extension used for semistability and splitting the \(t=2\) fibre. Let \(B\) be the normalization of \(R\) in \(K(X)\); let \(d=[K(X):K(t)]\). The integral-evaluation argument supplies finite projectivity of this same \(B\) of rank \(d\). Put \textbf{\(C=B/(t-2)B\)}, retaining this order rather than replacing it with its normalization \(O\). Its generic algebra is \(K^{d}\) after the chosen splitting extension. The determinant of \(B\to \operatorname{Hom}_{R}(B,R)\), \(b\mapsto (b'\mapsto \operatorname{Tr}(bb'))\), is a nonzero section of an invertible line. Base change \(t\mapsto 2\) gives exactly the trace determinant of \(C\), since trace of multiplication on a finite projective module commutes with base change. Thus the section's arithmetic intersection with \(t=2\) is log Norm disc(C). This is an equality of determinant ideals and does not assert that \(C\) is maximal.

 At every height-one point \(q\) of Spec \(R\), \(V=R_{q}\) is a DVR and \(T=B\otimes _{R}\) \(V\) is its finite normal integral closure in the generic separable algebra. \(T\) can be semilocal; do not silently identify a single localization \(T_{m}\) with a finite V-algebra. Complete \(V\). Then \(T\otimes _{V}\) Vhat is the product of the complete DVRs \(U_{j}\) over every \(m_{j}\) above \(q\), with generic fields \(F_{j}\). Let \(e_{j}\) be the ramification index, \(f_{j}\) the full residue degree (including its inseparable degree), and \(r_{j}\) the Dedekind different exponent. Each \(U_{j}\) is finite free over Vhat. Filtering \(U_{j}/\pi _{V}\) \(U_{j}\) by powers of its uniformizer gives

```

### H030

Class: status, source locator or provenance prose. Base 2860-2866; candidate 2853-2859.

```diff
@@ -2860,7 +2853,7 @@

 \subsection{2. Lenstra's estimate really covers the vertical DVR}

-The actual published source is Javanpeykar, ANT8(2014), \S{}4.1, printed pp112--113, Propositions4.1.1 and4.1.3 and Remark4.1.2. The retained PDF is the final publisher article, DOI10.2140/ant.2014.8.89; see \nolinkurl{SOURCE_USES.json}. The setup is a characteristic-zero DVR and its finite separable field extension. No perfect-residue assumption occurs. The remark explicitly distinguishes the separable-residue result in Serre and the imperfect-residue application. Proposition4.1.3 obtains a bound for each maximal ideal by completing it; it does not require the original integral closure to be a local ring.
+The actual published source is Javanpeykar, ANT 8(2014), \S{}4.1, printed pp.~112--113, Propositions 4.1.1 and 4.1.3 and Remark 4.1.2. The retained PDF is the final publisher article, DOI 10.2140/ant.2014.8.89; see \nolinkurl{SOURCE_USES.json}. The setup is a characteristic-zero DVR and its finite separable field extension. No perfect-residue assumption occurs. The remark explicitly distinguishes the separable-residue result in Serre and the imperfect-residue application. Proposition 4.1.3 obtains a bound for each maximal ideal by completing it; it does not require the original integral closure to be a local ring.

 Here is a direct reconstruction useful for checking conventions. For a finite extension of complete DVRs \(V\subset U\) with fraction-field degree \(n\), choose uniformizer \(\pi \) of \(V\). The element \(y=1/(n\pi )\) has field trace \(1/\pi \) and is therefore outside \(U^{\vee }\). As \(U^{\vee }\) is a fractional ideal of the DVR \(U\), it is strictly smaller than yU. Taking inverse fractional ideals gives \(D_{U/V}\) strictly larger than \(n\pi U\). With \(v_{U}(\pi )=e\) this yields

```

### H031

Class: prose, notation or text-conversion cleanup; inspect both sides. Base 2868-2888; candidate 2861-2881.

```diff
@@ -2868,21 +2861,21 @@

 This uses only characteristic zero, finite freeness, nondegeneracy of generic trace and total ordering of fractional ideals in a DVR. In particular it applies when the residue extension is inseparable. For a component of an algebra of total degree \(d\), its completed degree \(n\) is at most \(d\). In residue characteristic \(p\),

-\(v_{V}(n) = v_{V}(p) v_{p}(n) \le  v_{V}(p) \text{floor}(\operatorname{log} d/\operatorname{log} p)\).
+\(v_{V}(n) = v_{V}(p) v_{p}(n) \le  v_{V}(p) \left\lfloor\operatorname{log} d/\operatorname{log} p\right\rfloor\).

-Now take the actual vertical point \(q=(\text{pfrak})\) of Spec \(O_{K}[t]\). Then \(V=O_{K}[t]_{\text{pfrak}}\), residue field \(k(\text{pfrak})(t)\), which generally is \textbf{imperfect}, fraction field \(K(t)\), and \(v_{V}(p)=e_{\text{pfrak}}\). \(V\) is excellent \((a \text{localization} of a \text{finite}-\text{type} \text{algebra} \text{ over }  O_{K})\), so the normalizations are finite. For \textbf{every} component \(j\) the displayed estimate gives
+Now take the actual vertical point \(q=(\mathfrak p)\) of Spec \(O_{K}[t]\). Then \(V=O_{K}[t]_{\mathfrak p}\), residue field \(k(\mathfrak p)(t)\), which generally is \textbf{imperfect}, fraction field \(K(t)\), and \(v_{V}(p)=e_{\mathfrak p}\). \(V\) is excellent \((a \text{localization} of a \text{finite}-\text{type} \text{algebra} \text{ over }  O_{K})\), so the normalizations are finite. For \textbf{every} component \(j\) the displayed estimate gives

-\(r_{j} \le  e_{j}-1 + e_{j} e_{\text{pfrak}} \text{floor}(\operatorname{log} d/\operatorname{log} p)\).
+\(r_{j} \le  e_{j}-1 + e_{j} e_{\mathfrak p} \left\lfloor\operatorname{log} d/\operatorname{log} p\right\rfloor\).

 Multiplying by all \(f_{j}\) and using \(\sum _{j} e_{j} f_{j}=d\) bounds the whole discriminant coefficient by

-\(d(1+e_{\text{pfrak}} \text{floor}(\operatorname{log} d/\operatorname{log} p))\).
+\(d(1+e_{\mathfrak p} \left\lfloor\operatorname{log} d/\operatorname{log} p\right\rfloor)\).

 There is no restriction \(p\le d\) needed: if \(p>d\) the floor is zero and the same estimate holds. At a horizontal branch point the residue characteristic is zero. In completed curve coordinates, after the unramified coefficient-field extension one has \(t-a=u^{e}\) \(v(u)\), \(v(0)\ne 0\). The derivative has order \(e-1\) because \(e\) is a unit. The local complete-intersection/Jacobian formula for the different therefore gives \(r=e-1\). Thus its discriminant coefficient is at most \(d\). This applies to the horizontal branch divisor at \(t=0\); \(t=1\) and infinity contribute no intersection with the section \(t=2\).

-If normalization is finite étale over \(O_{K_{0}}[S^{-1},t,t^{-1},(t-1)^{-1}]\), then after any finite K/K0 it stays finite étale there. The base is normal and a finite étale algebra over a normal ring is normal; its generic algebra is the base-changed cover. It is therefore the normalization of that algebra on the open. This identifies the actual \(B\) there, and rules out additional vertical discriminant components outside \(S\) after the auxiliary extension. It does not assert that normalization commutes with arbitrary base change everywhere.
+If normalization is finite \'etale over \(O_{K_{0}}[S^{-1},t,t^{-1},(t-1)^{-1}]\), then after any finite K/K0 it stays finite \'etale there. The base is normal and a finite \'etale algebra over a normal ring is normal; its generic algebra is the base-changed cover. It is therefore the normalization of that algebra on the open. This identifies the actual \(B\) there, and rules out additional vertical discriminant components outside \(S\) after the auxiliary extension. It does not assert that normalization commutes with arbitrary base change everywhere.

-The horizontal intersection with \(t=0\) has normalized value log2. At pfrak above \(p\) the vertical intersection is \(f_{\text{pfrak}}\) logp. Summing the last bound, using \(\sum _{\text{pfrak}|p}e_{\text{pfrak}}\) \(f_{\text{pfrak}}=[K:Q]\) and \(\sum f_{\text{pfrak}}\le [K:Q]\), gives
+The horizontal intersection with \(t=0\) has normalized value log 2. At \(\mathfrak p\) above \(p\) the vertical intersection is \(f_{\mathfrak p}\) log p. Summing the last bound, using \(\sum _{\mathfrak p|p}e_{\mathfrak p}\) \(f_{\mathfrak p}=[K:Q]\) and \(\sum f_{\mathfrak p}\le [K:Q]\), gives

 \(\operatorname{log} \operatorname{Norm} \operatorname{disc}(C)/[K:Q] \le  d(\log 2 + \operatorname{log} R_{S} + |S|\operatorname{log} d)\).

```

### H032

Class: status, source locator or provenance prose. Base 2890-2910; candidate 2883-2903.

```diff
@@ -2890,21 +2883,21 @@

 \subsection{3. Torsion different as an identity of fractional ideals}

-Let \(V\) be the excellent characteristic-zero DVR occurring above, E/V an elliptic scheme, \(n\ge 1\), and \(E[n]=\operatorname{Spec}\) A. Its generic algebra \(L\) is finite étale; it need not be a field. The fact that \([n]\) is finite locally free of rank \(n^{2}\) can be checked using the field theorem Stacks0BFG, Lemma39.9.8, on every fibre: properness and finite fibres give finiteness. Stacks49.12.6/0BWJ applies with \(S=\operatorname{Spec}\) \(V\), \(X=Y=E\) smooth of relative dimension1, and \(f=[n]\) locally quasi-finite. It gives flatness, and its proof gives the LCI property. Thus the rank is \(n^{2}\) by its fibre ranks. The same application works over the regular base \(U\) used in \S{}4. Where \(n\) is invertible, the differential below is invertible, so \([n]\) is étale.
+Let \(V\) be the excellent characteristic-zero DVR occurring above, E/V an elliptic scheme, \(n\ge 1\), and \(E[n]=\operatorname{Spec}\) A. Its generic algebra \(L\) is finite \'etale; it need not be a field. The fact that \([n]\) is finite locally free of rank \(n^{2}\) can be checked using the field theorem Stacks 0BFG, Lemma 39.9.8, on every fibre: properness and finite fibres give finiteness. Stacks 49.12.6/0BWJ applies with \(S=\operatorname{Spec}\) \(V\), \(X=Y=E\) smooth of relative dimension 1, and \(f=[n]\) locally quasi-finite. It gives flatness, and its proof gives the LCI property. Thus the rank is \(n^{2}\) by its fibre ranks. The same application works over the regular base \(U\) used in \S{}4. Where \(n\) is invertible, the differential below is invertible, so \([n]\) is \'etale.

 The graph of \([n]\) is the base change of the diagonal of the smooth relative curve E/V, hence a regular immersion into \(E\times _{V}\) \(E\). Projection is smooth. This gives an explicit local-complete-intersection factorization of \([n]\). Invariant differentials trivialize \(\Omega _{E/V}\) as a line pulled back from \(V\). The group law differentiates as addition at the identity; induction gives \([n]^{*}\omega =n\omega \) for positive \(n\). Therefore the relative differentials of \([n]\) have presentation \(O_{E}\) \(--n-\to \) \(O_{E}\) and \(\text{Fitt}_{0}\) \(\Omega _{[n]}=(n)\). This is \(n\), \textbf{not the degree \(n^{2}\)}.

-Base change by the zero section \(E[n]\to \operatorname{Spec}\) \(V\) preserves finite flatness, the local-complete-intersection property, the displayed presentation and its Fitting ideal. For this finite flat LCI \(V\to A\), Stacks0BWE (Lemma49.10.1) checks the exact syntomic hypotheses, Stacks0BWF (49.10.4) gives invertibility of \(\omega _{A/V}\), and Stacks0BWG (49.12.3, on the archived section0BWB) identifies the scheme different with \(\text{Fitt}_{0}\) \(\Omega _{A/V}=(n)\). Stacks Definition49.9.1/0BW4 defines that scheme different as \(\text{Ann}(\omega _{A/V} / A\tau )\).
+Base change by the zero section \(E[n]\to \operatorname{Spec}\) \(V\) preserves finite flatness, the local-complete-intersection property, the displayed presentation and its Fitting ideal. For this finite flat LCI \(V\to A\), Stacks 0BWE (Lemma 49.10.1) checks the exact syntomic hypotheses, Stacks 0BWF (49.10.4) gives invertibility of \(\omega _{A/V}\), and Stacks 0BWG (49.12.3, on the archived section 0BWB) identifies the scheme different with \(\text{Fitt}_{0}\) \(\Omega _{A/V}=(n)\). Stacks Definition 49.9.1/0BW4 defines that scheme different as \(\text{Ann}(\omega _{A/V} / A\tau )\).

 The generic trace identification is fixed, rather than an unspecified module isomorphism: Stacks0BW2 (49.8.2) maps \(x\in A^{\vee }\) to \(b\mapsto \operatorname{Tr}_{L/\text{Frac}(V)}(xb)\). Stacks0BW3 (49.8.3) maps \textbf{1 to \(\tau \)}. Under this map, the annihilator in the preceding paragraph is

 \(\{a\in A: a A^{\vee }\subset A\}\).

-Since \(A^{\vee }\) is an invertible fractional A-ideal (from0BWF) and contains1, this is exactly its inverse fractional ideal. Thus \((A^{\vee })^{-1}=nA\), and inverting again gives the literal equality inside \(L\)
+Since \(A^{\vee }\) is an invertible fractional A-ideal (from 0BWF) and contains 1, this is exactly its inverse fractional ideal. Thus \((A^{\vee })^{-1}=nA\), and inverting again gives the literal equality inside \(L\)

 \(A^{\vee }=n^{-1} A\).

-This argument checks the scalar fixed by trace; an abstract isomorphism \(\omega \cong A\) by itself would not do so. It also explains how the Kähler different equals the Dedekind different here. In Stacks49.12.4/0BWH the local generator is mapped so that the Jacobian determinant maps to \(\tau \), consistently with the same equality. Brox's citation49.12.6 is the valid current tag0BWJ. It applies directly to \([n]\) as checked above and gives the same differential-determinant formula. The archived section0BWB includes Lemmas49.12.1--4, Example49.12.5 and Lemma49.12.6; a shortened web-text extraction had omitted the latter part. This author initially misclassified the citation as absent; fresh review caught that error before freeze. \nolinkurl{FINDINGS.md} preserves the correction.
+This argument checks the scalar fixed by trace; an abstract isomorphism \(\omega \cong A\) by itself would not do so. It also explains how the K\"ahler different equals the Dedekind different here. In Stacks 49.12.4/0BWH the local generator is mapped so that the Jacobian determinant maps to \(\tau \), consistently with the same equality. Brox's citation 49.12.6 is the valid current tag 0BWJ. It applies directly to \([n]\) as checked above and gives the same differential-determinant formula. The archived section 0BWB includes Lemmas 49.12.1--4, Example 49.12.5 and Lemma 49.12.6; a shortened web-text extraction had omitted the latter part.

 Normalize A in \(L\), obtaining finite Atilde (excellence of V). Both A and Atilde are finite torsion-free V-modules with generic algebra \(L\). Trace duality reverses the actual inclusion \(A\subset \text{Atilde}:\)

```

### H033

Class: status, source locator or provenance prose. Base 2926-2978; candidate 2919-2967.

```diff
@@ -2926,53 +2919,49 @@

 \(E_{t}: y^{2}=x^{3}-3t/(t-1)x-2t/(t-1)\).

-Direct substitution into \(\Delta =-16(4a^{3}+27b^{2})\), \(c_{4}=-48a\) and \(j=c_{4}^{3}/\Delta \) gives \(\Delta =1728t^{2}/(t-1)^{3}\) and \(j=1728t\). All denominators and \(\Delta \) are units on \(U\). It is an elliptic scheme there. As \(N\) is invertible, \(E_{t}[N]\) is finite étale. Its primitive locus is open and closed: remove \(E_{t}[m]\) for the finitely many proper divisors m|N; these are unions of components étale locally on \(U\). Thus the exact-order-N locus is finite étale as well, including \(N=1\) with the usual order-one point.
+Direct substitution into \(\Delta =-16(4a^{3}+27b^{2})\), \(c_{4}=-48a\) and \(j=c_{4}^{3}/\Delta \) gives \(\Delta =1728t^{2}/(t-1)^{3}\) and \(j=1728t\). All denominators and \(\Delta \) are units on \(U\). It is an elliptic scheme there. As \(N\) is invertible, \(E_{t}[N]\) is finite \'etale. Its primitive locus is open and closed: remove \(E_{t}[m]\) for the finitely many proper divisors m|N; these are unions of components \'etale locally on \(U\). Thus the exact-order-N locus is finite \'etale as well, including \(N=1\) with the usual order-one point.

-The constant \(H\) action is scalar multiplication. On primitive points \(aP=P\) implies \((a-1)P=0\), hence \(a=1\) modN. Étale locally the algebra is a product of copies of the base ring and \(H\) permutes these copies; the quotient is the product indexed by the H-orbits. This constructs a finite étale quotient even at residue characteristics dividing |H|. No averaging by |H| and no assumption |H| invertible is used. Freeness makes every orbit have |H| points.
+The constant \(H\) action is scalar multiplication. On primitive points \(aP=P\) implies \((a-1)P=0\), hence \(a=1\) modN. \'Etale locally the algebra is a product of copies of the base ring and \(H\) permutes these copies; the quotient is the product indexed by the H-orbits. This constructs a finite \'etale quotient even at residue characteristics dividing |H|. No averaging by |H| and no assumption |H| invertible is used. Freeness makes every orbit have |H| points.

-Identify its generic fibre over \(Q(t)\) by the moduli definition of \(X_{1}(N)\). Over an algebraic closure, \(j\ne 0,1728\), an elliptic curve has automorphism group \(\{\pm 1\}\). Given another curve with that \(j\) and a primitive point, choose an isomorphism to \(E_{t}\); two choices differ \(by\pm 1\) and hence give the same H-orbit. This bijection is Galois compatible: changing the chosen isomorphism after a Galois action again differs only \(by\pm 1\). Thus it is an isomorphism of the finite étale \(Q(t)-\text{algebras}\), not just a count of their geometric points. Quadratic twisting is exactly this \(\pm 1\) ambiguity, already killed in \(H\). The generic cover is the actual \(X_{H}=X_{1}(N)/H\) with \(t=j/1728\). A normal finite étale cover over normal \(U\) is its normalization there.
+Identify its generic fibre over \(Q(t)\) by the moduli definition of \(X_{1}(N)\). Over an algebraic closure, \(j\ne 0,1728\), an elliptic curve has automorphism group \(\{\pm 1\}\). Given another curve with that \(j\) and a primitive point, choose an isomorphism to \(E_{t}\); two choices differ by \(\pm 1\) and hence give the same H-orbit. This bijection is Galois compatible: changing the chosen isomorphism after a Galois action again differs only by \(\pm 1\). Thus it is an isomorphism of the finite \'etale \(Q(t)-\text{algebras}\), not just a count of their geometric points. Quadratic twisting is exactly this \(\pm 1\) ambiguity, already killed in \(H\). The generic cover is the actual \(X_{H}=X_{1}(N)/H\) with \(t=j/1728\). A normal finite \'etale cover over normal \(U\) is its normalization there.

-Geometric primitive vectors are a single SL2(Z/NZ) orbit: a primitive pair (a,b) can be completed to a determinant-one matrix by Bézout modN. This is compatible with the standard analytic model of the connected modular curve; the construction introduces no full-level cyclotomic component. Counting primitive vectors gives \(N^{2}\prod _{p|N}(1-p^{-2})\); dividing by \(|H|=\phi (N)/t_{H}\) yields
+Geometric primitive vectors are a single SL2(Z/NZ) orbit: a primitive pair (a,b) can be completed to a determinant-one matrix by B\'ezout modN. This is compatible with the standard analytic model of the connected modular curve; the construction introduces no full-level cyclotomic component. Counting primitive vectors gives \(N^{2}\prod _{p|N}(1-p^{-2})\); dividing by \(|H|=\phi (N)/t_{H}\) yields

 \(d_{H}=N t_{H} \prod _{p|N}(1+p^{-1})\).

-For \(N=1\) the products and \(\phi (1)\) are one, and \(d_{H}=1\); the positive-genus hypothesis later simply excludes irrelevant small-genus cases. Published von Känel2021 \S{}4, \(p_{8}\), (4.1) independently records the degree/index convention: the factor two occurs exactly \(\text{when}-I\) is absent, and the only possible branch values are the elliptic points and cusp. \(\text{Here}-I\) is present \(\text{because}-1\in H\), so no additional two divides the formula. The finite étale model already proves absence of branch away \(\text{from}0,1,\infty \) in characteristic zero.
+For \(N=1\) the products and \(\phi (1)\) are one, and \(d_{H}=1\); the positive-genus hypothesis later simply excludes irrelevant small-genus cases. Published von K\"anel 2021 \S{}4, p.~8, (4.1) independently records the degree/index convention: the factor two occurs exactly when \(-I\) is absent, and the only possible branch values are the elliptic points and cusp. Here \(-I\) is present because \(-1\in H\), so no additional two divides the formula. The finite \'etale model already proves absence of branch away from \(0,1,\infty\) in characteristic zero.

 A geometric H-orbit has Galois stabilizer containing the stabilizer of any chosen primitive point \(P\) in it. Consequently its field of definition is an intermediate field of \(Q(t)(P)/Q(t)\). This remains true after replacing \(Q\) by the auxiliary \(K\) and completing at a vertical generic point: each component field and each chosen place is covered by \S{}3. The quotient need not itself be a subalgebra factor of the integral nonnormal A; the generic field inclusion and its normalizations are the objects to which the intermediate-field conclusion applies.

 \subsection{5. Same constant at every prime}

-For every prime \(\text{pfrak}|p>3\) of \(K\), take \(V=O_{K}[t]_{\text{pfrak}}\). Both \(t\) and \(t-1\) are units there, and1728 is a unit, so \(E_{t}/V\) is an elliptic scheme even if p|N. Do \textbf{not} use the finite étale model \(U\) at such \(p\), since \(U\) inverted \(N\); instead use the finite flat torsion theorem of \S{}3. The quotient component field identified in \S{}4 is an intermediate field of a single N-torsion-point field. Its different exponent is at most \(v_{j}(N)=e_{j}\) \(v_{V}(N)\). By \S{}1 the full vertical discriminant coefficient is therefore
+For every prime \(\mathfrak p|p>3\) of \(K\), take \(V=O_{K}[t]_{\mathfrak p}\). Both \(t\) and \(t-1\) are units there, and 1728 is a unit, so \(E_{t}/V\) is an elliptic scheme even if p|N. Do \textbf{not} use the finite \'etale model \(U\) at such \(p\), since \(U\) inverted \(N\); instead use the finite flat torsion theorem of \S{}3. The quotient component field identified in \S{}4 is an intermediate field of a single N-torsion-point field. Its different exponent is at most \(v_{j}(N)=e_{j}\) \(v_{V}(N)\). By \S{}1 the full vertical discriminant coefficient is therefore

-\(\sum _{j} f_{j} r_{j} \le  (\sum _{j} f_{j} e_{j}) v_{V}(N) = d_{H} v_{\text{pfrak}}(N)\).
+\(\sum _{j} f_{j} r_{j} \le  (\sum _{j} f_{j} e_{j}) v_{V}(N) = d_{H} v_{\mathfrak p}(N)\).

-After intersection with the section, summation over pfrak and division by [K:Q], this contributes at most \(d_{H}\) \(\sum _{p>3}v_{p}(N)\log p\le d_{H}\) logN. Every component is included; the algebra's rank is \(d_{H}\), not \(N^{2}\) and not the degree of a full torsion field.
+After intersection with the section, summation over \(\mathfrak p\) and division by [K:Q], this contributes at most \(d_{H}\) \(\sum _{p>3}v_{p}(N)\log p\le d_{H}\) logN. Every component is included; the algebra's rank is \(d_{H}\), not \(N^{2}\) and not the degree of a full torsion field.

-At \(p=2\) and3 use \S{}2 rather than the elliptic model, which is not asserted smooth there. Their combined normalized bound is at most \(d_{H}(\log 6+2\operatorname{log} d_{H})\). This includes primes not dividing \(N\) and levels with \(d_{H}<p\). The horizontal \(t=0\) contribution is at most \(d_{H}\) log2. Altogether
+At \(p=2\) and 3 use \S{}2 rather than the elliptic model, which is not asserted smooth there. Their combined normalized bound is at most \(d_{H}(\log 6+2\operatorname{log} d_{H})\). This includes primes not dividing \(N\) and levels with \(d_{H}<p\). The horizontal \(t=0\) contribution is at most \(d_{H}\) log 2. Altogether

 \(\operatorname{log} \operatorname{Norm} \operatorname{disc}(C)/[K:Q] \le  d_{H}(\log 12+\log N+2\operatorname{log} d_{H})\).

-This is Broxv17:461--488 with every local supplier matched to the actual objects. The independent evaluation conclusion, if accepted for this same \(C\), gives
+This is Brox v17:461--488 with every local supplier matched to the actual objects. The evaluation conclusion, applied to this same \(C\), gives

 \(\hF(J_{H}) \le  d_{H}/2 (\log 12+\log N+2\operatorname{log} d_{H}) + g_{H} \operatorname{log}(2/\sqrt{\pi})\).

-The stable-height metric and the evaluation lattice are separate interfaces assigned to the other two author lanes; this document does not self-approve their conclusions. The prime summations show why the auxiliary \(K\) cancels, so no [K:Q] enters H0.3 or the later surface-isogeny field degree.
+The stable-height metric and the evaluation lattice are separate required inputs. The prime summations show why the auxiliary \(K\) cancels, so no [K:Q] enters H0.3 or the later surface-isogeny field degree.

-\subsection{6. History, incorporation and limits}

-Actual earlier proof text read: frozen Broxv17 \S{}\S{}3--4 at274--488; \nolinkurl{height/PROOF.md} H0.3 and \(H_{4}\); \nolinkurl{research/v14-brox-order8/PROOF.md}45--56; its actual \nolinkurl{review/SOURCE_ASSESSMENT.md} sections ``The lattice and discriminant argument'' and ``The modular cover and surface''; its \nolinkurl{review/REPORT.md}19--33; \nolinkurl{research/v14-small-prime-conductor/review/REPORT.md} section ``Fresh height estimate''; and retained Protocol-D foundationREPORT/H04. The earlier source assessment already states the imperfect-residue Lenstra application, exact torsion derivative \(n\), reversed trace dual and intermediate-field conclusion. Its final review expressly retains published-source/whole-assembly limits. Therefore \textbf{prior justification found and read} is the historical disposition for these arguments. This packet is a source-pinned expansion and precise current-tag binding, not a claim to have first repaired a newly discovered arithmetic error.
-
-Current incorporation: Broxv17 contains the substantive arguments but not this expanded bridge and current-tag expansion; the private height H0.3 retains their inherited status. This packet proposes the bridge for additive incorporation. Current acceptance: pending a reviewer other than this author after the packet is frozen, including the precise joins to the other two evaluation lanes. No global modularity, height-transfer, 214 existence or256 theorem is accepted by this bounded work. The source inventory records what was inspected; it does not claim exhaustive search of every historical archive, nor a new inspection of the complete Serre book. The relevant trace, different, tower and tame-horizontal assertions are instead derived explicitly above.
 \clearpage
 % Source: research/quartic214/proofs/height-metric.md
 \section{Metric and archimedean evaluation bridge}\label{q214:height-metric}
 \noindent\textit{Source: }\nolinkurl{research/quartic214/proofs/height-metric.md}.\par

-\begin{quote}\footnotesize Author: internal model task \nolinkurl{/root/d214_metric_evaluation} (requested Sol61 lane), 2026-11-10. This is an author proposal awaiting a separately authored review. It supplies only Brox \(v_{17}\) lines62--78 and210--251, conditional on the exact integral map and trace-lattice bound specified below. It supplies neither acceptance of those algebraic inputs nor whole-214/256 closure. The immutable manuscript is private commit \nolinkurl{a81afd7996a20e6b7bb5e48670418541c036d7aa}; exact whole-file and passage bindings are in \nolinkurl{SOURCE_USES.json.}\end{quote}
+\begin{quote}\footnotesize It supplies only Brox \(v_{17}\) lines 62--78 and 210--251, conditional on the exact integral map and trace-lattice bound specified below. Those algebraic inputs and the remaining arguments for the full 214 and 256 constructions are separate prerequisites. The immutable manuscript is private commit \nolinkurl{a81afd7996a20e6b7bb5e48670418541c036d7aa}; exact whole-file and passage bindings are in \nolinkurl{SOURCE_USES.json}.\end{quote}

 \subsection{1. Published normalization and actual Jacobian}

-Read the final published Javanpeykar2014, \S{}\S{}2.1/2.3, printed pp93--94/97--98, and final von Känel2021 \S{}2.1, printed \(p_{5}\). The former specifies the inner product \((i/2)\int _{X} \omega \wedge \overline{\eta }\), its determinant metric, and \(\text{hFal}(X)=\text{Ardeg}(\operatorname{det} p_{*}\omega )/[K:Q]\), equal to stable Faltings height of the Jacobian. The latter defines original relative height using the Néron top-differential line and all embeddings, then defines stable height by semistable extension and proves its extension invariance. Its paragraph after(2.2) explicitly distinguishes the alternative shifted height by \((g/2)\operatorname{log} \pi \). That shifted height is not used here. Sources were acquired from their publishers on2026-11-10; hashes and exact source locations are retained in \nolinkurl{SOURCE_USES.json.}
+The final published Javanpeykar 2014, \S{}\S{}2.1/2.3, printed pp.~93--94/97--98, and final von K\"anel 2021 \S{}2.1, printed p.~5 give the following normalizations. The former specifies the inner product \((i/2)\int _{X} \omega \wedge \overline{\eta }\), its determinant metric, and \(\text{hFal}(X)=\text{Ardeg}(\operatorname{det} p_{*}\omega )/[K:Q]\), equal to stable Faltings height of the Jacobian. The latter defines original relative height using the N\'eron top-differential line and all embeddings, then defines stable height by semistable extension and proves its extension invariance. Its paragraph after (2.2) explicitly distinguishes the alternative shifted height by \((g/2)\operatorname{log} \pi \). That shifted height is not used here. Hashes and exact source locations are retained in \nolinkurl{SOURCE_USES.json}.

 Apply Javanpeykar's identification to the \emph{same} smooth projective geometrically connected curve \nolinkurl{X/K}, genus \(g\ge 1\), and its minimal regular semistable model \(p:{\mathcal X}\to \operatorname{Spec} O_{K}\). Thus \(E=H^{0}({\mathcal X},\omega _{{\mathcal X}/O_{K}})\) with the displayed \(L^{2}\) metric has

```

### H034

Class: status, source locator or provenance prose. Base 2980-2998; candidate 2969-2987.

```diff
@@ -2980,19 +2969,19 @@

 This is the Jacobian itself, not an isogenous abelian variety, a modular factor, the singular normalization model, or an Arakelov metric on individual cotangent fibres. The relevant metric is on global differentials. Javanpeykar's published statement supplies the integral model identification; it is a theorem input, not a claim that a generic vector-space identification alone identifies lattices.

-For an explicit check of the archimedean determinant scalar, choose symplectic integral cycles and normalized holomorphic forms \(\omega _{1},\ldots ,\omega _{g}\); write their period matrix \((1,\tau )\). Riemann's bilinear identity gives their Gram matrix \(Im \tau \). The analytic Jacobian is \(C^{g}/(Z^{g}+\tau Z^{g})\) and Abel--Jacobi pulls \(dz_{i}\) to \(\omega _{i}\). The positive volume of its fundamental parallelepiped is \(\operatorname{det} Im \tau \), so the squared norm of \(dz_{1}\wedge \ldots \wedge dz_{g}\) in the positive top-form convention is exactly \(\operatorname{det} Im \tau \), also the squared determinant norm of the \(\omega _{i}\). The top-form integral uses the usual positive ordering of real pairs; changing between block and interleaved complex wedges accounts for the orientation sign, not a positive metric scalar. No \nolinkurl{g!}, \(\pi ^{g}\), polarization degree, or isogeny degree occurs. A Kähler form raised to its gth power would require a factorial, but that is not this norm.
+For an explicit check of the archimedean determinant scalar, choose symplectic integral cycles and normalized holomorphic forms \(\omega _{1},\ldots ,\omega _{g}\); write their period matrix \((1,\tau )\). Riemann's bilinear identity gives their Gram matrix \(Im \tau \). The analytic Jacobian is \(C^{g}/(Z^{g}+\tau Z^{g})\) and Abel--Jacobi pulls \(dz_{i}\) to \(\omega _{i}\). The positive volume of its fundamental parallelepiped is \(\operatorname{det} Im \tau \), so the squared norm of \(dz_{1}\wedge \ldots \wedge dz_{g}\) in the positive top-form convention is exactly \(\operatorname{det} Im \tau \), also the squared determinant norm of the \(\omega _{i}\). The top-form integral uses the usual positive ordering of real pairs; changing between block and interleaved complex wedges accounts for the orientation sign, not a positive metric scalar. No \nolinkurl{g!}, \(\pi ^{g}\), polarization degree, or isogeny degree occurs. A K\"ahler form raised to its gth power would require a factorial, but that is not this norm.

 For any further number-field extension \nolinkurl{K'/K}, stable height is unchanged. Equivalently the normalized degree for the semistable model over \(K'\) again equals this same stable height. We need no assertion that the singular base change of a minimal regular model is already regular. In this argument choose one extension that simultaneously makes the curve semistable and splits the finite unramified fibre, then construct its model and \(E\) there. The degree in the height formula and the number of complex embeddings are both \nolinkurl{[K:Q]}. The auxiliary field is unrelated to the controlled field \(L'\) in the surface-isogeny argument.

 \subsection{2. One global coordinate choice and its analytic bound}

-Let \(\pi :X\to P^{1}_{t}\) be the same degree-d Belyi cover and let its split fibre over2 be \(P_{1},\ldots ,P_{d}\). Characteristic zero implies separability. Riemann--Hurwitz gives \(2g-2=-2d+\sum (e_{P}-1)\le -2d+3(d-1)=d-3\); over each of the three possible branch values the contribution is \(d\) minus the nonzero number of geometric points in that fibre. Hence \(d>2g-2\). A nonzero regular differential has zero divisor of degree \(2g-2\), including \(g=1\) where it has no zeros. Since every \(P_{j}\) is unramified, \(\omega /dt(P_{j})=0\) is precisely vanishing there. Thus
+Let \(\pi :X\to P^{1}_{t}\) be the same degree-d Belyi cover and let its split fibre over 2 be \(P_{1},\ldots ,P_{d}\). Characteristic zero implies separability. Riemann--Hurwitz gives \(2g-2=-2d+\sum (e_{P}-1)\le -2d+3(d-1)=d-3\); over each of the three possible branch values the contribution is \(d\) minus the nonzero number of geometric points in that fibre. Hence \(d>2g-2\). A nonzero regular differential has zero divisor of degree \(2g-2\), including \(g=1\) where it has no zeros. Since every \(P_{j}\) is unramified, \(\omega /dt(P_{j})=0\) is precisely vanishing there. Thus

 \(ev:E\otimes K\to K^{d}\), \(\omega \mapsto (\omega /dt(P_{j}))_{j}\)

 has rank \(g\). Some \(g\times g\) minor is nonzero over \(K\). Fix its coordinate set \(I\subset \{1,\ldots ,d\}\) \textbf{once over \(K\)}. Each embedding sends that nonzero minor to a nonzero complex number, so the same \(I\) works at every embedding. An embedding permutes the labels of the geometric fibre but does not lose distinctness or unramifiedness. No separately chosen analytic minor is used to define the integral map.

-The algebraic lane must supply the actual integral \(ev:E\to C^{\vee }\) for \(C=B/(t-2)B\), where \(B\) is the normalization algebra over \(O_{K}[t]\). Set \(F=pr_{I}(C^{\vee })\) with the standard Euclidean metric, and use the exact lattice bound \(\text{Ardeg}(F)\le (1/2)\operatorname{log} N \operatorname{disc}(C)\). Projection gives the generically invertible integral map \(\phi :E\to F\) used here. This packet does not replace \(F\) by the maximal order or its trace dual.
+The required algebraic input is the actual integral \(ev:E\to C^{\vee }\) for \(C=B/(t-2)B\), where \(B\) is the normalization algebra over \(O_{K}[t]\). Set \(F=pr_{I}(C^{\vee })\) with the standard Euclidean metric, and use the exact lattice bound \(\text{Ardeg}(F)\le (1/2)\operatorname{log} N \operatorname{disc}(C)\). Projection gives the generically invertible integral map \(\phi :E\to F\) used here. This argument does not replace \(F\) by the maximal order or its trace dual.

 At every complex embedding the open disc \(D=\{|t-2|<1/2\}\) avoids \(0,1,\infty \). The inverse image consists of \(d\) disjoint sheets isomorphic to \(D\). On the sheet through \(P_{j}\), write \(\omega =f_{j}(t)dt\). The power-series identity, or the mean-value inequality, gives

```

### H035

Class: status, source locator or provenance prose. Base 3018-3036; candidate 3007-3025.

```diff
@@ -3018,19 +3007,19 @@

 The small positive constant is \(\operatorname{log}(2/\sqrt{\pi })=(1/2)\operatorname{log}(4/\pi )\); there is no extra \nolinkurl{g log g}, square-norm factor two, or half-weight for a conjugate embedding pair.

-For the modular consumer, substitute \emph{the same} \(X=X_{H}=X_{1}(N)/H\), \(H\supset \{-1\}\), \(t=j/1728\), \(J_{H}=\operatorname{Jac} X_{H}\), \(d=d_{H}\), and \(g=g_{H}\) from Brox354--401. The modular-model and different lanes must establish that cover and the normalized discriminant bound \(d_{H}(\log 12+\operatorname{log} N+2\operatorname{log} d_{H})\). The result is exactly Brox453--488/H0.3, with no convention change when used in \nolinkurl{height/PROOF.md} H2--H4. In the actual non-CM realization \(H=\operatorname{ker} \epsilon \) with \(\epsilon \) even; the actual Jacobian contains an abelian surface over \(L'\), so \(g_{H}\ge 2\). That identity is not supplied by this metric lane.
+For the modular consumer, substitute \emph{the same} \(X=X_{H}=X_{1}(N)/H\), \(H\supset \{-1\}\), \(t=j/1728\), \(J_{H}=\operatorname{Jac} X_{H}\), \(d=d_{H}\), and \(g=g_{H}\) from Brox354--401. The modular-model and different arguments must establish that cover and the normalized discriminant bound \(d_{H}(\log 12+\operatorname{log} N+2\operatorname{log} d_{H})\). The result is exactly Brox453--488/H0.3, with no convention change when used in \nolinkurl{height/PROOF.md} H2--H4. In the actual non-CM realization \(H=\operatorname{ker} \epsilon \) with \(\epsilon \) even; the actual Jacobian contains an abelian surface over \(L'\), so \(g_{H}\ge 2\). That identity is not supplied by this metric argument.

-There is no large-level, torsion-free-congruence-subgroup, \(\text{genus}\ge 2\), or absence-of-elliptic-points assumption in the evaluation proof. Every positive-genus modular curve for every positive \(N\) is covered, including genus1. Possible elliptic/cusp ramification is confined to the three omitted branch values; it cannot affect the disc over2. \(N=1\) and \(N=2\) give genus-zero curves (the covers have degrees1 and3); the modular section's explicit positive-genus hypothesis excludes them. Any other genus-zero level is excluded by that same hypothesis, and cannot be the actual surface-factor consumer since a zero Jacobian has no surface factor. No classification of small \(N\) is needed to cover all allowed positive-genus cases. If one extends the displayed modular inequality to genus0, its left side is \(\hF(0)=0\) and its right side is nonnegative, but that extension is not used in this contract.
+There is no large-level, torsion-free-congruence-subgroup, \(\text{genus}\ge 2\), or absence-of-elliptic-points assumption in the evaluation proof. Every positive-genus modular curve for every positive \(N\) is covered, including genus 1. Possible elliptic/cusp ramification is confined to the three omitted branch values; it cannot affect the disc over 2. \(N=1\) and \(N=2\) give genus-zero curves (the covers have degrees 1 and 3); the modular section's explicit positive-genus hypothesis excludes them. Any other genus-zero level is excluded by that same hypothesis, and cannot be the actual surface-factor consumer since a zero Jacobian has no surface factor. No classification of small \(N\) is needed to cover all allowed positive-genus cases. If one extends the displayed modular inequality to genus 0, its left side is \(\hF(0)=0\) and its right side is nonnegative, but that extension is not used in this contract.

 \subsection{4. Scope and incorporation}

-This is a source/application explanation of an already written argument; no numerical repair or manuscript edit is proposed. Historical justification was found in the actual earlier source assessment and report, including their withdrawn normalization concern, and in the current frozen \(v_{17}\) proof. We do not call this a newly repaired gap. The explanation can be incorporated by an exact pointer from an additive height-closure packet. Its author status, the still-separate algebraic/different inputs, and the need for fresh non-author acceptance must remain explicit. The 214 existence and the proposed256 work both consume the same full-family height supplier; the proof here is not restricted to a distinguished parameter \(\beta \).
+The algebraic evaluation and different bounds remain separate inputs. The 214 existence and proposed 256 arguments use the same full-family height supplier; the proof here is not restricted to a distinguished parameter \(\beta \).
 \clearpage
 % Source: research/quartic214/proofs/height-assembly.md
 \section{Assembly at the actual modular-Jacobian consumer}\label{q214:height-assembly}
 \noindent\textit{Source: }\nolinkurl{research/quartic214/proofs/height-assembly.md}.\par

-\begin{quote}\footnotesize Author/integrator: \nolinkurl{/root}, 2026-11-10. This is an author proposal for a fresh non-author review. It supplements the two immutable packets at private commit \nolinkurl{a81afd7996a20e6b7bb5e48670418541c036d7aa}. The source/application target is Brox \(v_{17}\), SHA-256 \nolinkurl{2ba5dd497276073d92db95f0119bede82d182997c66375e5be294157de6d9f7c}, lines 47--488, and H0.3/H4 in \nolinkurl{research/quadratic-ten-contact-integration/height/PROOF.md}. No polynomial, parameter choice or constant is changed.\end{quote}
+\begin{quote}\footnotesize It supplements the two immutable packets at private commit \nolinkurl{a81afd7996a20e6b7bb5e48670418541c036d7aa}. The source/application target is Brox \(v_{17}\), SHA-256 \nolinkurl{2ba5dd497276073d92db95f0119bede82d182997c66375e5be294157de6d9f7c}, lines 47--488, and H0.3/H4 in the height supplier reproduced in Section~\ref{q214:height-supplier}. No polynomial, parameter choice or constant is changed.\end{quote}

 \subsection{A. The scoped theorem}

```

### H036

Class: status, source locator or provenance prose. Base 3046-3054; candidate 3035-3043.

```diff
@@ -3046,9 +3035,9 @@

 \subsection{\(B\). Same curve, order, lattice and maps}

-The modular-model construction in \nolinkurl{different/PROOF.md} \S{}4 identifies the generic primitive N-torsion points modulo \(H\) with the actual modular quotient, compatibly with Galois action. It provides the finite étale model away from 6N and the degree \(d\). The \(\pm 1\) ambiguity of a chosen elliptic-curve isomorphism is already killed in \(H\). At a prime dividing \(N\) we use the finite flat torsion argument, not the model with \(N\) inverted. Every component and every place is included in the discriminant sum. The positive-genus hypothesis removes the genus-zero cases without imposing an unrecorded large-level condition.
+The modular-model construction in Section~\ref{q214:height-different} \S{}4 identifies the generic primitive N-torsion points modulo \(H\) with the actual modular quotient, compatibly with Galois action. It provides the finite \'etale model away from 6N and the degree \(d\). The \(\pm 1\) ambiguity of a chosen elliptic-curve isomorphism is already killed in \(H\). At a prime dividing \(N\) we use the finite flat torsion argument, not the model with \(N\) inverted. Every component and every place is included in the discriminant sum. The positive-genus hypothesis removes the genus-zero cases without imposing an unrecorded large-level condition.

-Choose one finite number field \(K\) defining the cover, making the curve semistable, and splitting its unramified fibre over \(t=2\). Existence of such an extension follows from semistable reduction and adjoining finitely many point coordinates. Its degree is not bounded. Let \(B\) be the normalization of \(O_{K}[t]\) in \(K(X_{H})\), and put \(C=B/(t-2)B\). The integral-evaluation proof uses this same \(B\) and this possibly nonmaximal order \(C\). Let \(E=H^{0}({\mathcal X},\omega _{{\mathcal X}/O_{K}})\) for the minimal regular semistable model \({\mathcal X}\) of \(X_{H}\). Then \nolinkurl{evaluation/PROOF.md} supplies the literal integral map
+Choose one finite number field \(K\) defining the cover, making the curve semistable, and splitting its unramified fibre over \(t=2\). Existence of such an extension follows from semistable reduction and adjoining finitely many point coordinates. Its degree is not bounded. Let \(B\) be the normalization of \(O_{K}[t]\) in \(K(X_{H})\), and put \(C=B/(t-2)B\). The integral-evaluation proof uses this same \(B\) and this possibly nonmaximal order \(C\). Let \(E=H^{0}({\mathcal X},\omega _{{\mathcal X}/O_{K}})\) for the minimal regular semistable model \({\mathcal X}\) of \(X_{H}\). Then Section~\ref{q214:height-evaluation} supplies the literal integral map

 \(ev:E \to  C^{\vee }\), \(\omega  \to  (\omega /dt(P_{j}))_{j=1,...,d}\).

```

### H037

Class: status, source locator or provenance prose. Base 3080-3117; candidate 3069-3104.

```diff
@@ -3080,38 +3069,36 @@

 The 214 construction remains an existence family with an ineffective threshold \(N_{0}\); the separate condition \(N\ge 53\) only bounds coefficients. Neither this height supplier nor a passing finite checker makes \(N_{0}\) effective. No effective construction is asserted in this public package.

-\subsection{\(E\). History and remaining closure}
+\subsection{\(E\). Remaining dependencies}

-The earlier source assessment and review already explained integral evaluation, trace duality, different bounds and the metric constant. This round compares those actual arguments to final primary sources and expands the joins. It does not claim a newly discovered arithmetic error or priority for the underlying proof. The old packets and verdicts stay immutable; the new reviewer decision applies only to the exact new supplement and its stated interfaces.
-
-Acceptance of A does not accept \(H_{0}\) geometry/CM bounds, normalized modularity and companion trace assembly, the entire analytic/restricted-converse chain, or every remaining final-publication/source qualification in the prior foundation map. In particular the final 2022 Rémond body comparison remains a separate item. The current status overlay must carry those obligations forward rather than infer whole-proof closure from the success of this supplier.
+Argument A does not supply \(H_{0}\) geometry/CM bounds, normalized modularity and companion trace assembly, the entire analytic/restricted-converse chain, or every remaining final-publication/source qualification in the prior foundation map. In particular the final 2022 R\'emond body comparison remains a separate item. Those source applications remain separate prerequisites.
 \clearpage
 % Source: research/quartic214/proofs/height-supplier.md
 \section{Quadratic \(S_{10}\) contact supplier and its reflected effective consumers}\label{q214:height-supplier}
 \noindent\textit{Source: }\nolinkurl{research/quartic214/proofs/height-supplier.md}.\par
 \begin{quote}\small \textbf{Current application:} H0--H2 and H4 are consumed with the product averaging proof in Section~\ref{q214:height-averaging}.  The historical H3 quotient-filtration route is retained only as superseded evidence and is not used in this edition's 214 argument.\end{quote}

-\begin{quote}\footnotesize Author: internal model task \nolinkurl{/root/sol61_height_foundation}, 2026-11-10. Author proposal, not independent acceptance. This selected H0--H4 text supplies the full-family height input for the 214 construction. Its scope is a complete connecting argument \textbf{relative to the inherited geometric, normalized modular-realization, modular-Jacobian height, root-height, scalar/anchor, rank and Lucas interfaces specified below}. It does not silently claim full published-source closure of those inherited proofs. Publication-version limitations are explicit in \nolinkurl{SOURCES.json} and \nolinkurl{FINDINGS.md.}\end{quote}
+\begin{quote}\footnotesize This selected H0--H4 text supplies the full-family height input for the 214 construction. Its scope is a complete connecting argument \textbf{relative to the inherited geometric, normalized modular-realization, modular-Jacobian height, root-height, scalar/anchor, rank and Lucas interfaces specified below}. The source qualifications of those inherited proofs remain required. Publication-version limitations are explicit in \nolinkurl{SOURCES.json} and \nolinkurl{FINDINGS.md}.\end{quote}

-All heights \(h\) are absolute logarithmic Weil heights. All \(\hF\) are original stable Faltings heights. Tate modules use arithmetic Frobenius and \(\operatorname{det}(r_{f})=\epsilon *\chi _{\text{cyc}}\). Added algebraic scalar coefficients have trivial Galois action. Symbols for number fields, scalar characters and integer labels are kept distinct below.
+All heights \(h\) are absolute logarithmic Weil heights. All \(\hF\) are original stable Faltings heights. Tate modules use arithmetic Frobenius and \(\operatorname{det}(r_{f})=\epsilon \cdot \chi _{\text{cyc}}\). Added algebraic scalar coefficients have trivial Galois action. Symbols for number fields, scalar characters and integer labels are kept distinct below.

 \subsection{\(H_{0}\). Exact inherited interfaces and domain}

-Let \(S=\{2,3,5,7,11,13,17,37,41,2399\}\), \(B_{S}=1857890364330\), and \(E(R)=\prod _{p|R}(1+1/p)\). For every finite rational \(a=u/v\) in lowest terms, \(v>0\), with \nolinkurl{a notin {0,1,2401,-343/32}}, define \(M=M_{S}(a)\) to count once each \(p\) outside \(S\) having positive odd valuation on one of
+Let \(S=\{2,3,5,7,11,13,17,37,41,2399\}\), \(B_{S}=1857890364330\), and \(E(R)=\prod _{p|R}(1+1/p)\). For every finite rational \(a=u/v\) in lowest terms, \(v>0\), with \(a\notin\{0,1,2401,-343/32\}\), define \(M=M_{S}(a)\) to count once each \(p\) outside \(S\) having positive odd valuation on one of

 \nolinkurl{v,u,u-v,u-2401v,32u+343v}.

-Put \(R=B_{S} M\) and \(\ell =\operatorname{log}\) \(R\). \(R\) is squarefree; \(M=1\) is allowed. The exact small-prime support argument is inherited from private\#8 cutoff proof \S{}1 and private\#9 conductor proof \S{}\S{}1--3. It uses the same full three-marked normalizer fiber as the parent manuscript, not a substituted surface: its branch sections are the five indicated contacts; outside210, even contact is unramified after an unramified extension, including infinity. The normal fiber field \(L\) has degree dividing576, is unramified outside supp(R), defines all geometric homomorphisms between the conjugate surfaces, and \(A_{a}\) has good reduction over \(L\) away from210. The same surface satisfies
+Put \(R=B_{S} M\) and \(\ell =\operatorname{log}\) \(R\). \(R\) is squarefree; \(M=1\) is allowed. The exact small-prime support argument is inherited from private\#8 cutoff proof \S{}1 and private\#9 conductor proof \S{}\S{}1--3. It uses the same full three-marked normalizer fiber as the parent manuscript, not a substituted surface: its branch sections are the five indicated contacts; outside 210, even contact is unramified after an unramified extension, including infinity. The normal fiber field \(L\) has degree dividing 576, is unramified outside supp(R), defines all geometric homomorphisms between the conjugate surfaces, and \(A_{a}\) has good reduction over \(L\) away from 210. The same surface satisfies

 \(h(a) \le  2 \operatorname{max}(0,\hF(A_{a}))+128\).                         (H0.1)

-The CM branch gives \(\hF(A_{a})<854R\), over the same support and metric. These uniform source statements apply to every a above, not only the later constructed \(\beta \) or detector values. The non-CM surface has geometric endomorphism algebra the quaternion division algebra \(B\) of discriminant210, hence is absolutely simple. Its B-linear conjugate isogenies \(\mu _{\sigma }\) are L-defined, chosen with \(\mu _{1}=1\) and inflated from Gal(L/Q). The normalized sign cocycle and modularity-descent lemma are the actual parent \nolinkurl{quartic_v14.tex} passages481ff,8110ff; the latter lemma accepts any locally constant scalar splitting satisfying its cocycle equation. It identifies the \textbf{original} \(r_{5}\), with its finite twist absorbed into the final primitive weight-two form \(f\). The companion trace argument identifies the original \(r_{3}\) with that same \(f\); neither the absorbed finite twist nor its kernel field replaces the controlled lift or \(L'\).
+The CM branch gives \(\hF(A_{a})<854R\), over the same support and metric. These uniform source statements apply to every a above, not only the later constructed \(\beta \) or detector values. The non-CM surface has geometric endomorphism algebra the quaternion division algebra \(B\) of discriminant 210, hence is absolutely simple. Its B-linear conjugate isogenies \(\mu _{\sigma }\) are L-defined, chosen with \(\mu _{1}=1\) and inflated from Gal(L/Q). The normalized sign cocycle and modularity-descent lemma are the actual parent \nolinkurl{quartic_v14.tex} passages 481ff, 8110ff; the latter lemma accepts any locally constant scalar splitting satisfying its cocycle equation. It identifies the \textbf{original} \(r_{5}\), with its finite twist absorbed into the final primitive weight-two form \(f\). The companion trace argument identifies the original \(r_{3}\) with that same \(f\); neither the absorbed finite twist nor its kernel field replaces the controlled lift or \(L'\).

-The private\#9 conductor argument applies to every controlled lift that is tame at odd primes and has scalar Dirichlet conductor dividing4 at2. It proves for this final \(f\)
+The private\#9 conductor argument applies to every controlled lift that is tame at odd primes and has scalar Dirichlet conductor dividing 4 at 2. It proves for this final \(f\)

 \(N \le  C_{N} R^{2}\), \(\operatorname{rad}(N)|R\), \(C_{N}=2^{68} 3^{16} 5^{16} 7^{4}\). (H0.2)

-Here is why the freedom used below preserves that argument: the torsion field \(E_{\text{tor}}=L(A[11])\) is normal, \([E_{\text{tor}}:Q]\) divides \(576 |\operatorname{GL}_{4}(F_{11})|\), and the valuations of that integer at2,3,5,7 are15,4,4,1. Adjoining the kernel field of the scalar Dirichlet character and then the quadratic kernel of its lift adds at most two dyadic factors and only tame factors at odd primes. Thus \(v_{p}(e)\le 17,4,4,1\). The derivative/different calculation in private\#9 \S{}2 bounds the last positive upper break \(by2v_{p}(e)\), the Swan conductor of a two-dimensional representation \(by4v_{p}(e)\), and its tame codimension by2. Exponents70,18,18,6 follow. At \(p>7\), L/Q is tame, A/L has good reduction and the scalar lift is trivial on wild inertia; \(\text{exponent}\le 2\) follows. The original \(r_{5}\) is used at every \(p\ne 5\) and original \(r_{3}\) at5, so the level bound omits no prime. No bound on the tame part of \(e\) or the coefficient degree is substituted. This repeats the changed-lift connecting argument while retaining the parent published local-compatibility/modularity qualifications.
+Here is why the freedom used below preserves that argument: the torsion field \(E_{\text{tor}}=L(A[11])\) is normal, \([E_{\text{tor}}:Q]\) divides \(576 |\operatorname{GL}_{4}(F_{11})|\), and the valuations of that integer at 2,3,5,7 are 15,4,4,1. Adjoining the kernel field of the scalar Dirichlet character and then the quadratic kernel of its lift adds at most two dyadic factors and only tame factors at odd primes. Thus \(v_{p}(e)\le 17,4,4,1\). The derivative/different calculation in private\#9 \S{}2 bounds the last positive upper break by \(2v_{p}(e)\), the Swan conductor of a two-dimensional representation by \(4v_{p}(e)\), and its tame codimension by 2. Exponents 70,18,18,6 follow. At \(p>7\), L/Q is tame, A/L has good reduction and the scalar lift is trivial on wild inertia; \(\text{exponent}\le 2\) follows. The original \(r_{5}\) is used at every \(p\ne 5\) and original \(r_{3}\) at 5, so the level bound omits no prime. No bound on the tame part of \(e\) or the coefficient degree is substituted. This repeats the changed-lift connecting argument while retaining the parent published local-compatibility/modularity qualifications.

 The retained modular-Jacobian project proof supplies, for \(H=\operatorname{ker} \epsilon \), \(J=\operatorname{Jac}(X_{1}(N)/H)\), genus \(g>0\) and actual j-map degree \(d\),

```

### H038

Class: status, source locator or provenance prose. Base 3119-3149; candidate 3106-3136.

```diff
@@ -3119,31 +3106,31 @@

 \(\hF(J) \le  d/2(\log 12+\operatorname{log} N+2\operatorname{log} d)+g \operatorname{log}(2/\sqrt{\pi})\). (H0.3)

-This is the differential-evaluation proof at Brox \(v_{17}\) Corollary4.3 (label cor:modularheight), not its large-primorial numerical theorem. It is retained as the precise versioned project height input already consumed by private\#9. It is valid after arbitrary finite extension; the auxiliary field splitting its evaluation fiber contributes no degree to the isogeny estimate. The local expanded proofs \nolinkurl{height-evaluation.md,} \nolinkurl{height-different.md,} \nolinkurl{height-metric.md} and \nolinkurl{height-assembly.md} supply this interface.
+This is the differential-evaluation proof at Brox \(v_{17}\) Corollary 4.3 (label cor:modularheight), not its large-primorial numerical theorem. It is retained as the precise versioned project height input already consumed by private\#9. It is valid after arbitrary finite extension; the auxiliary field splitting its evaluation fiber contributes no degree to the isogeny estimate. The local expanded proofs \nolinkurl{height-evaluation.md,} \nolinkurl{height-different.md,} \nolinkurl{height-metric.md} and \nolinkurl{height-assembly.md} supply this interface.

 \subsection{\(H_{1}\). Minimal two-primary characters and the actual normalized field}

-Let \(U(R)=\operatorname{max}(\{2\} \cup  \{2^{v_{2}(p-1)}: p \text{odd}, p|R\})\). At each odd prime where the sign cocycle has nontrivial local boundary, choose a generator \(g\) of the cyclic group modulo \(p\) and take the character sending \(g\) to a primitive \(2^{v_{2}(p-1)}\) root of unity. Since \nolinkurl{(p-1)/2} has exactly one fewer factor2, the character takes -1 to-1. Where the boundary is trivial choose the trivial local character. At2 choose the nontrivial character modulo4 only if its boundary is required. The product \(\chi \) has order \(m\) dividing \(U(R)\), is tame at every odd prime and has conductor dividing4 at2.
+Let \(U(R)=\operatorname{max}(\{2\} \cup  \{2^{v_{2}(p-1)}: p \text{odd}, p|R\})\). At each odd prime where the sign cocycle has nontrivial local boundary, choose a generator \(g\) of the cyclic group modulo \(p\) and take the character sending \(g\) to a primitive \(2^{v_{2}(p-1)}\) root of unity. Since \nolinkurl{(p-1)/2} has exactly one fewer factor 2, the character takes -1 to-1. Where the boundary is trivial choose the trivial local character. At 2 choose the nontrivial character modulo 4 only if its boundary is required. The product \(\chi \) has order \(m\) dividing \(U(R)\), is tame at every odd prime and has conductor dividing 4 at 2.

 This is a choice inside the parent's instruction to choose an odd local character; it changes the representation and final \(f\) and therefore needs the fresh comparison here. The parent's local reciprocity criterion for the constant-coefficient squaring sequence says that the boundary is nontrivial exactly when the local character takes -1 to-1. Hence the new \(\chi \) has the same prescribed local boundaries as the original sign cocycle at every finite prime. The global Brauer injection/reciprocity argument used in the parent supplies the same sign-class equality, including the determined real invariant. A continuous pointwise square root, corrected by a sign cochain, gives

 \(b^{2}=\chi \), \(\delta  b=\epsilon _{\text{sign}}\), \(b:G_{Q} \to  \mu _{2m}\).

-Twist \(b\) by the parent's quadratic character to remove the finitely many unwanted inertia characters outside supp(R). This preserves \(b^{2}\) and \(\delta \) \(b\), stays in \(\mu _{2m}\), is tame at every odd added place, and adds possible support only at2, already in \(S\). On \(G_{L}\) the sign cocycle is trivial, so \(b\) is a character, invariant under conjugation by \(G_{Q}\). Its kernel field \(L'\) contains \(L\), is normal over \(Q\), and
+Twist \(b\) by the parent's quadratic character to remove the finitely many unwanted inertia characters outside supp(R). This preserves \(b^{2}\) and \(\delta \) \(b\), stays in \(\mu _{2m}\), is tame at every odd added place, and adds possible support only at 2, already in \(S\). On \(G_{L}\) the sign cocycle is trivial, so \(b\) is a character, invariant under conjugation by \(G_{Q}\). Its kernel field \(L'\) contains \(L\), is normal over \(Q\), and

 \(d'=[L':Q] \le  2m[L:Q] \le 1152 U(R) \le 2304 \phi (R)\).    (H1.1)

-The last deliberately conservative bound will be used numerically. Since the isogenies are inflated from Gal(L/Q) and \(\mu _{1}=1\), both \(\mu _{\sigma }\) and \(a_{\sigma }=(\operatorname{deg} \mu _{\sigma })^{-1/4}\) equal1 on \(G_{L}\). Consequently
+The last deliberately conservative bound will be used numerically. Since the isogenies are inflated from Gal(L/Q) and \(\mu _{1}=1\), both \(\mu _{\sigma }\) and \(a_{\sigma }=(\operatorname{deg} \mu _{\sigma })^{-1/4}\) equal 1 on \(G_{L}\). Consequently

 \(\rho _{l}(\sigma )=b(\sigma )^{-1} a_{\sigma } \mu _{\sigma } \circ \sigma \)

-restricts on \(G_{L'}\) to the \textbf{actual Tate representation of this \(A_{a}\)}, not an unspecified scalar twist. The normalized cocycle identity makes \(\rho _{l}\) a representation; the B-action gives \(\rho _{l}=r_{l} \oplus  r_{l}\). All geometric endomorphisms remain defined over \(L'\). Faltings semisimplicity and the commutant \(B \text{tensor} \text{Qbar}_{l}=M_{2}(\text{Qbar}_{l})\) imply that \(r_{l}|G_{L'}\) is absolutely irreducible. The parent modularity lemma applies with \(t_{\sigma }=a_{\sigma }/b(\sigma )\); changing \(\chi \) has preserved every hypothesis, including finite local constancy. It supplies a final primitive weight-two \(f\) with \(r_{5}=r_{f,5}\). The companion trace comparison supplies the same identity at3. For the multiplicity argument below one prime, say5, suffices; no assertion at a missing coefficient prime is needed.
+restricts on \(G_{L'}\) to the \textbf{actual Tate representation of this \(A_{a}\)}, not an unspecified scalar twist. The normalized cocycle identity makes \(\rho _{l}\) a representation; the B-action gives \(\rho _{l}=r_{l} \oplus  r_{l}\). All geometric endomorphisms remain defined over \(L'\). Faltings semisimplicity and the commutant \(B \otimes \overline{\mathbb Q}_{l}=M_{2}(\overline{\mathbb Q}_{l})\) imply that \(r_{l}|G_{L'}\) is absolutely irreducible. The parent modularity lemma applies with \(t_{\sigma }=a_{\sigma }/b(\sigma )\); changing \(\chi \) has preserved every hypothesis, including finite local constancy. It supplies a final primitive weight-two \(f\) with \(r_{5}=r_{f,5}\). The companion trace comparison supplies the same identity at 3. For the multiplicity argument below one prime, say 5, suffices; no assertion at a missing coefficient prime is needed.

 The polarization-transport calculation in \(M_6\) of Section~\ref{q214:modularity} applies to these same \(B\)-linear conjugate isogenies. It gives \(\mu_\sigma^\vee\lambda\mu_\sigma=q_\sigma\,{}^\sigma\lambda\) with \(q_\sigma>0\), \(D(\mu_\sigma)=q_\sigma^2\), and \(a_\sigma^2q_\sigma=1\). Thus the normalized action has Tate-pairing multiplier \(b^{-2}\chi_{\text{cyc}}\) on all of \(G_{\mathbb Q}\), and its exact determinant is \(\operatorname{det}\rho_l=b^{-4}\chi_{\text{cyc}}^2=\chi^{-2}\chi_{\text{cyc}}^2\). On the other hand the modular decomposition gives \(\operatorname{det} \rho _{l}=\epsilon ^{2} \chi _{\text{cyc}}^{2}\). Thus

 \((\epsilon  \chi )^{2}=1\) and \(s=\operatorname{ord}(\epsilon ) \mid  U(R)\). (H1.2)

-Indeed \(U(R)\) is a power of two and is even; both \(\chi \) and \(\epsilon *\chi \) have orders dividing it. Weight two gives \(\epsilon (-1)=1\), so -1 belongs to \(H\). Finally \(U(R)|\phi (R)\) and
+Indeed \(U(R)\) is a power of two and is even; both \(\chi \) and \(\epsilon \cdot \chi \) have orders dividing it. Weight two gives \(\epsilon (-1)=1\), so -1 belongs to \(H\). Finally \(U(R)|\phi (R)\) and

 \begin{gather*}
 s E(R) \le  U(R)E(R) \le  \phi (R)E(R)\\
```

### H039

Class: prose, notation or text-conversion cleanup; inspect both sides. Base 3154-3176; candidate 3141-3163.

```diff
@@ -3154,23 +3141,23 @@

 \subsection{\(H_{2}\). Multiplicity over \(L'\), not only geometric multiplicity}

-Let \(E_{f}=Q(a_{n}(f): n\ge 1)\), \(e=[E_{f}:Q]\). The modular abelian variety \(A_{f}\) is defined over \(Q\), has dimension \(e\), and over \(\text{Qbar}_{5}\) its Tate module is the sum of the two-dimensional coefficient conjugates \(r_{f}^{\tau }\). This is the standard modular-factor input: published Shimura Theorem1 gives the quotient, dimension and differentials; its Euler-factor assertion requires the coefficient-conjugate span to be Fricke-stable. For the final primitive weight-two newform this condition is supplied by the Li Fricke formula in the actual parent modularity argument. Thus the formula applies to this \(f\) with arbitrary nebentypus, not only to a \(\Gamma _{0}\) form. The Tate/cohomology dual convention is the same as that parent's modular identification. This is an explicit hypothesis match, not an appeal to a similarly named modular variety.
+Let \(E_{f}=Q(a_{n}(f): n\ge 1)\), \(e=[E_{f}:Q]\). The modular abelian variety \(A_{f}\) is defined over \(Q\), has dimension \(e\), and over \(\overline{\mathbb Q}_{5}\) its Tate module is the sum of the two-dimensional coefficient conjugates \(r_{f}^{\tau }\). This is the standard modular-factor input: published Shimura Theorem 1 gives the quotient, dimension and differentials; its Euler-factor assertion requires the coefficient-conjugate span to be Fricke-stable. For the final primitive weight-two newform this condition is supplied by the Li Fricke formula in the actual parent modularity argument. Thus the formula applies to this \(f\) with arbitrary nebentypus, not only to a \(\Gamma _{0}\) form. The Tate/cohomology dual convention is the same as that parent's modular identification. This is an explicit hypothesis match, not an appeal to a similarly named modular variety.

-At every good place \(v\) of \(L'\) away from5 and the finitely many bad rational primes, \(\operatorname{tr}(r_{f}(\text{Frob}_{v}))=\operatorname{tr}(V_{5}(A_{a})(\text{Frob}_{v}))/2\) is rational. The trace on the left belongs to \(E_{f}\) before any coefficient embedding: if \(v\) has residue degree \(f_{v}\) over rational \(p\), it is the trace of the \(f_{v}-th\) power of a rational-prime Frobenius, a polynomial in \(a_{p}\) and \(p\) \(\epsilon (p)\). The equality in the chosen embedding at5 to a rational number therefore identifies that \(E_{f}\) element with the same rational number. Every coefficient embedding fixes it. Chebotarev and semisimple character uniqueness identify every \(r_{f}^{\tau }|G_{L'}\) with the same absolutely irreducible restricted representation \(W\). Its semisimplicity also follows directly from that of the abelian variety Tate modules; a finite-index restriction here introduces no unproved extension-class replacement.
+At every good place \(v\) of \(L'\) away from 5 and the finitely many bad rational primes, \(\operatorname{tr}(r_{f}(\text{Frob}_{v}))=\operatorname{tr}(V_{5}(A_{a})(\text{Frob}_{v}))/2\) is rational. The trace on the left belongs to \(E_{f}\) before any coefficient embedding: if \(v\) has residue degree \(f_{v}\) over rational \(p\), it is the trace of the \(f_{v}-th\) power of a rational-prime Frobenius, a polynomial in \(a_{p}\) and \(p\) \(\epsilon (p)\). The equality in the chosen embedding at 5 to a rational number therefore identifies that \(E_{f}\) element with the same rational number. Every coefficient embedding fixes it. Chebotarev and semisimple character uniqueness identify every \(r_{f}^{\tau }|G_{L'}\) with the same absolutely irreducible restricted representation \(W\). Its semisimplicity also follows directly from that of the abelian variety Tate modules; a finite-index restriction here introduces no unproved extension-class replacement.

 Consequently the Tate modules of \((A_{f})_{L'}^{2}\) and \(A_{a}^{e}\) have identical semisimple characters, already over \(Q_{5}\). Faltings' isogeny theorem gives an L'-isogeny. In the semisimple L'-isogeny category, absolute simplicity of \(A_{a}\) forces every simple factor of \((A_{f})_{L'}\) to be isogenous to \(A_{a}\) over \(L'\). Comparing dimensions proves \(e\) is even and

 \((A_{f})_{L'} \text{ is }  L'-\text{isogenous} \text{ to }  A_{a}^{r}\), \(r=e/2\).         (H2.1)

-The Hecke relation \(a_{p}^{2}-a_{p^{2}}=p \epsilon (p)\) puts \(\epsilon (p)\) in \(E_{f}\) for every \(p\) prime to \(N\). Chebotarev for the finite cyclotomic quotient supplies primes in every invertible residue class modulo \(N\), hence the complete image of \(\epsilon \) lies in \(E_{f}\). Therefore \(Q(\zeta _{s}) \subset  E_{f}\), so \(r\ge \phi (s)/2\). If \(s\ge 4\) is a power of two, \(\phi (s)=s/2\); if \(s=1\) or2, use \(r\ge 1\). In all cases
+The Hecke relation \(a_{p}^{2}-a_{p^{2}}=p \epsilon (p)\) puts \(\epsilon (p)\) in \(E_{f}\) for every \(p\) prime to \(N\). Chebotarev for the finite cyclotomic quotient supplies primes in every invertible residue class modulo \(N\), hence the complete image of \(\epsilon \) lies in \(E_{f}\). Therefore \(Q(\zeta _{s}) \subset  E_{f}\), so \(r\ge \phi (s)/2\). If \(s\ge 4\) is a power of two, \(\phi (s)=s/2\); if \(s=1\) or 2, use \(r\ge 1\). In all cases

 \(s/r \le 4\).                                         (H2.2)

-Every coefficient conjugate of \(f\) has the same diamond-character kernel \(H\), so all its differentials are fixed by \(H\). For the quotient map \(X_{1}(N)\to X_{H}\), pullback identifies the Jacobian of \(X_{H}\) up to isogeny with the H-invariant subvariety. The \(A_{f}\) quotient restricted to that invariant subvariety is surjective, as seen on those differentials; characteristic zero makes this a genuine surjective homomorphism, not merely an equality of dimensions. Poincare reducibility over \(Q\) supplies a subvariety of \(J\) isogenous over \(Q\) to \(A_{f}\). Base change and(H2.1) supply an \textbf{L'-defined} \(B_{0}\) inside \(J_{L'}\) isogenous over \(L'\) to \(A_{a}^{r}\). In particular \(g\ge 2r\ge 2\). The field splitting a modular evaluation fiber and the coefficient value field are not substituted for \(L'\).
+Every coefficient conjugate of \(f\) has the same diamond-character kernel \(H\), so all its differentials are fixed by \(H\). For the quotient map \(X_{1}(N)\to X_{H}\), pullback identifies the Jacobian of \(X_{H}\) up to isogeny with the H-invariant subvariety. The \(A_{f}\) quotient restricted to that invariant subvariety is surjective, as seen on those differentials; characteristic zero makes this a genuine surjective homomorphism, not merely an equality of dimensions. Poincare reducibility over \(Q\) supplies a subvariety of \(J\) isogenous over \(Q\) to \(A_{f}\). Base change and (H2.1) supply an \textbf{L'-defined} \(B_{0}\) inside \(J_{L'}\) isogenous over \(L'\) to \(A_{a}^{r}\). In particular \(g\ge 2r\ge 2\). The field splitting a modular evaluation fiber and the coefficient value field are not substituted for \(L'\).

 \subsection{\(H_{3}\). Historical averaging route (superseded in this public application by height-averaging.md)}

-Take an L'-isogeny \(A_{a}^{r} \to  B_{0}\), and let \(D_{0}=0 \subset  D_{1} \subset  ... \subset  D_{r}=B_{0}\) be the images of its first \(i\) factors. Each \(C_{i}=D_{i}/D_{i-1}\) is an L'-defined surface L'-isogenous to \(A_{a}\). Rémond's stable subvariety/quotient inequality and Bost's lower bound \(\hF(C)\ge -3 \operatorname{dim}(C)/2\) give
+Take an L'-isogeny \(A_{a}^{r} \to  B_{0}\), and let \(D_{0}=0 \subset  D_{1} \subset  ... \subset  D_{r}=B_{0}\) be the images of its first \(i\) factors. Each \(C_{i}=D_{i}/D_{i-1}\) is an L'-defined surface L'-isogenous to \(A_{a}\). R\'emond's stable subvariety/quotient inequality and Bost's lower bound \(\hF(C)\ge -3 \operatorname{dim}(C)/2\) give

 \begin{gather*}
 \sum _{i} \hF(C_{i}) \le  \hF(B_{0})\\
```

### H040

Class: prose, notation or text-conversion cleanup; inspect both sides. Base 3179-3185; candidate 3166-3172.

```diff
@@ -3179,7 +3166,7 @@

 where \(H_{J}=\operatorname{max}(1,\hF(J)+3g/2)\). Thus one actual \(C_{i}\) has \(\hF(C_{i})\le H_{J}/r\). No invariance of \(\hF\) under isogeny is assumed.

-Apply Gaudron--Rémond Theorem1.9(1) with reference variety \(C_{i}\) of dimension2, base field \(K=L'\), and extension equal to \(K\). The published bound gives an L'-isogeny \(C_{i}\to A_{a}\) of degree at most
+Apply Gaudron--R\'emond Theorem 1.9(1) with reference variety \(C_{i}\) of dimension 2, base field \(K=L'\), and extension equal to \(K\). The published bound gives an L'-isogeny \(C_{i}\to A_{a}\) of degree at most

 \([14^{32} d' \operatorname{max}(1,\operatorname{log} d',\hF(C_{i}))]^{16}\).

```

### H041

Class: prose, notation or text-conversion cleanup; inspect both sides. Base 3187-3193; candidate 3174-3180.

```diff
@@ -3187,7 +3174,7 @@

 \(\hF(A_{a}) \le  X+8[32\log 14+\operatorname{log} d'+\operatorname{log} \operatorname{max}(1,\operatorname{log} d',X)]\). (H3.1)

-The small surface \(C_{i}\), its quotient maps and the final isogeny are all over \(L'\). The growing multiplicity \(r\) is never used as an isogeny dimension. The published GR theorem's original stable normalization and both isogeny directions were checked directly in its final publisher PDF, pp7--8. Rémond's authorJune2021 source explicitly states the stable version after Corollary1.3; its final2022 journal body remains unavailable through the subscription redirect. This is a source-version coverage limitation, not a claim that the known inequality is false or unpublished.
+The small surface \(C_{i}\), its quotient maps and the final isogeny are all over \(L'\). The growing multiplicity \(r\) is never used as an isogeny dimension. The published GR theorem's original stable normalization and both isogeny directions were checked directly in its final publisher PDF, pp.~7--8. R\'emond's author June 2021 source explicitly states the stable version after Corollary 1.3; its final 2022 journal body remains unavailable through the subscription redirect. This is a source-version coverage limitation, not a claim that the known inequality is false or unpublished.

 \subsection{\(H_{4}\). \(S_{10}\) quadratic constant, all \(M\ge 1\)}

```

### H042

Class: whitespace only. Base 3195-3201; candidate 3182-3188.

```diff
@@ -3195,7 +3182,7 @@

 \(K_{0}=(\log 12+3\operatorname{log} C_{N})/2+\log 2+3/2\).

-The rational interval certificate proves \(4+K_{0}/\operatorname{log} B_{S} < k\). It follows that \(H_{J}\le k d \ell \), including its max with1, because \(k\) \(d\) \(\ell >1\). Equations(H2.2),(H0.3) then give
+The rational interval certificate proves \(4+K_{0}/\operatorname{log} B_{S} < k\). It follows that \(H_{J}\le k d \ell \), including its max with 1, because \(k\) \(d\) \(\ell >1\). Equations(H2.2),(H0.3) then give

 \(H_{J}/r \le 4k T \ell  = X\).

```

### H043

Class: whitespace only. Base 3203-3213; candidate 3190-3200.

```diff
@@ -3203,11 +3190,11 @@

 \(\hF(A_{a}) < X+768+80\ell  < X+108\ell \).

-Combining with(H0.1), \(216+128/\log B_{S} < \delta  C_{N} B_{S}^{2}\), gives
+Combining with (H0.1), \(216+128/\log B_{S} < \delta  C_{N} B_{S}^{2}\), gives

 \(h(a) < c_{0} C_{N} R^{2} E(R) \log R\).                       (H4.1)

-The CM bound also satisfies(H4.1): \(1708B_{S}+128<c_{0} C_{N} B_{S}^{2} \log B_{S}\), and the right side grows at least quadratically with \(R\) whereas1708R+128 is linear. Thus(H4.1) is uniform across both branches.
+The CM bound also satisfies(H4.1): \(1708B_{S}+128<c_{0} C_{N} B_{S}^{2} \log B_{S}\), and the right side grows at least quadratically with \(R\) whereas 1708R+128 is linear. Thus(H4.1) is uniform across both branches.

 Define the exact positive real constant

```

### H044

Class: prose, notation or text-conversion cleanup; inspect both sides. Base 3221-3227; candidate 3208-3214.

```diff
@@ -3221,7 +3208,7 @@

 \(C_{2} < 2^{7557/32}\).

-Every \(p\) outside \(S\) is at least19. With \(\theta _{0}=\operatorname{log}(20/19)/\log 19\), the positive ratio \(\operatorname{log}(1+1/p)/\log p\) is at most \(\theta _{0}:\) its numerator decreases and denominator increases for \(p\ge 19\). Thus \(E(M)\le M^{\theta _{0}}\). Also \(1+\log M/\log B_{S} \le  M^{1/\log B_{S}}\) \(by1+x\le \operatorname{exp}(x)\). The certificate proves \(\theta _{0}+1/\log B_{S}<55/1024\). Consequently, including \(M=1\),
+Every \(p\) outside \(S\) is at least 19. With \(\theta _{0}=\operatorname{log}(20/19)/\log 19\), the positive ratio \(\operatorname{log}(1+1/p)/\log p\) is at most \(\theta _{0}:\) its numerator decreases and denominator increases for \(p\ge 19\). Thus \(E(M)\le M^{\theta _{0}}\). Also \(1+\log M/\log B_{S} \le  M^{1/\log B_{S}}\) by \(1+x\le \operatorname{exp}(x)\). The certificate proves \(\theta _{0}+1/\log B_{S}<55/1024\). Consequently, including \(M=1\),

 \(h(a) < C_{2} M^{\alpha }\), \(\alpha =2103/1024\).              (H4.3)

```

### H045

Class: status, source locator or provenance prose. Base 3232-3246; candidate 3219-3233.

```diff
@@ -3232,15 +3219,15 @@
 \section{Published product route for the multiplicity saving}\label{q214:height-averaging}
 \noindent\textit{Source: }\nolinkurl{research/quartic214/proofs/height-averaging.md}.\par

-\begin{quote}\footnotesize Author: \nolinkurl{/root}, 2026-11-11. This is a new application proof for independent review, not an acceptance record. It changes the supplier and auxiliary surfaces in \(H_{3}\) of the frozen private quadratic-height proof. It preserves the inequality H3.1, H4's constants and all polynomial rows.\end{quote}
+\begin{quote}\footnotesize It changes the supplier and auxiliary surfaces in \(H_{3}\) of the frozen private quadratic-height proof. It preserves the inequality H3.1, H4's constants and all polynomial rows.\end{quote}

-\subsection{Sources and historical disposition}
+\subsection{Sources}

-The original \(H_{3}\) applies the stable subvariety/quotient inequality in Rémond, \emph{Propriétés de la hauteur de Faltings}, Annali SNS Pisa 23 (2022), 1589--1596. Its June 2021 author version was read, including Corollary 1.2 and the stable-height statement after Corollary 1.3. On 2026-11-11 the final publisher body again redirected to subscriptions. That final-body comparison remains unavailable; no claim about its absence or incorrectness follows.
+The original \(H_{3}\) applies the stable subvariety/quotient inequality in R\'emond, \emph{Propri\'et\'es de la hauteur de Faltings}, Annali SNS Pisa 23 (2022), 1589--1596. Its June 2021 author version was read, including Corollary 1.2 and the stable-height statement after Corollary 1.3. On 2026-11-11 the final publisher body again redirected to subscriptions. That final-body comparison remains unavailable; no claim about its absence or incorrectness follows.

-There is an existing alternative argument in the current public Version 15, \nolinkurl{v15:height:lem:surface}, especially lines 30617--30636. \(I\) read that argument and its recorded source-route disposition. It consumes the construction in the published proof of Gaudron--Rémond, \emph{Nouveaux théorèmes d'isogénie}, Mémoires SMF 176 (2023), Lemma 16.2(1), printed pp. 97--98. \(I\) independently downloaded the final publisher PDF, SHA256 \nolinkurl{b1e2e32bec626cf6d27fb7d6d8702b5c707e0c3dc002d979088e62d8cda514a4}, and read the text and image of printed \(p\). 98. The source constructs, over its given number field, an isogenous abelian variety of no larger original stable Faltings height which is a product of simple abelian varieties over that field. Its factors are explicitly allowed to repeat.
+There is an existing alternative argument in the current public Version 15, \nolinkurl{v15:height:lem:surface}, especially lines 30617--30636. It consumes the construction in the published proof of Gaudron--R\'emond, \emph{Nouveaux th\'eor\`emes d'isog\'enie}, M\'emoires SMF 176 (2023), Lemma 16.2(1), printed pp. 97--98. The final publisher PDF has SHA256 \nolinkurl{b1e2e32bec626cf6d27fb7d6d8702b5c707e0c3dc002d979088e62d8cda514a4}. The source constructs, over its given number field, an isogenous abelian variety of no larger original stable Faltings height which is a product of simple abelian varieties over that field. Its factors are explicitly allowed to repeat.

-This published proof uses Rémond 2022, Corollary 1.3, and Rémond 2017, Theorem 1.6 \cite{v15-height-Remond,remond2017-maximal}. They remain indirect dependencies. The present route does not assert that the inaccessible final 2022 text was read, and does not re-prove the published product supplier. It uses that construction at its exact stated scope. Public Version 15's accepted single-surface application is historical support for the route, not approval of the new multiplicity application below.
+This published proof uses R\'emond 2022, Corollary 1.3, and R\'emond 2017, Theorem 1.6 \cite{v15-height-Remond,remond2017-maximal}. They remain indirect dependencies. The present route does not assert that the inaccessible final 2022 text was read, and does not re-prove the published product supplier. It uses that construction at its exact stated scope. The Version 15 single-surface application does not by itself supply the multiplicity application below.

 \subsection{Fixed-field product and multiplicity}

```

### H046

Class: prose, notation or text-conversion cleanup; inspect both sides. Base 3248-3254; candidate 3235-3241.

```diff
@@ -3248,7 +3235,7 @@

 Apply the construction in the proof of GR2023 Lemma 16.2(1) to \(J\) over \(L'\). It gives \(J_{0}=\prod \) \(D_{j}\), where every \(D_{j}\) is simple over \(L'\), \(J_{0}\) is L'-isogenous to \(J\), and \(\hF(J_{0})\le \hF(J)\). This is an isomorphism to a product, not merely an isogeny between the displayed factors and \(J_{0}\). No invariance of height under arbitrary isogeny is asserted.

-Poincaré complete reducibility over \(L'\) and uniqueness of simple isogeny factors imply that the isogeny class of A occurs in this product with multiplicity at least \(r\). To see the multiplicity explicitly, \(B_{0}\sim A^{r}\) is a subobject of \(J\) in the semisimple category up to L'-isogeny. Passing to the isomorphic object \(J_{0}\) in that category preserves the multiplicity of every simple constituent. Since A is absolutely simple, it is simple over \(L'\); each constituent in its class has dimension two. Choose \(r\) distinct occurrences, name them \(C_{1},...,C_{r}\), and denote the product of all remaining factors by \(E\). Then
+Poincar\'e complete reducibility over \(L'\) and uniqueness of simple isogeny factors imply that the isogeny class of A occurs in this product with multiplicity at least \(r\). To see the multiplicity explicitly, \(B_{0}\sim A^{r}\) is a subobject of \(J\) in the semisimple category up to L'-isogeny. Passing to the isomorphic object \(J_{0}\) in that category preserves the multiplicity of every simple constituent. Since A is absolutely simple, it is simple over \(L'\); each constituent in its class has dimension two. Choose \(r\) distinct occurrences, name them \(C_{1},...,C_{r}\), and denote the product of all remaining factors by \(E\). Then

 \begin{gather*}
 J_{0} = C_{1} \times  ... \times  C_{r} \times  E,\\
```

### H047

Class: status, source locator or provenance prose. Base 3260-3266; candidate 3247-3253.

```diff
@@ -3260,7 +3247,7 @@

 \subsection{Height average and transfer}

-Use the original stable Faltings normalization throughout. Height is additive on products. The original-normalization lower bound is \(\hF(E)\ge -3\) \(\operatorname{dim}(E)/2\), from the actual GR2014 \S{}2.3 and Corollary 8.4 calculation recorded in \nolinkurl{quartic214-protocol-d/PRIMARY_SOURCE_BRIDGES.md}. It holds without a polarization hypothesis; if \(\operatorname{dim}(E)=0\) its height is zero. Consequently
+Use the original stable Faltings normalization throughout. Height is additive on products. The original-normalization lower bound is \(\hF(E)\ge -3\) \(\operatorname{dim}(E)/2\), from the actual GR2014 \S{}2.3 and Corollary 8.4 calculation recorded in Section~\ref{q214:primary-source-bridges}. It holds without a polarization hypothesis; if \(\operatorname{dim}(E)=0\) its height is zero. Consequently

 \begin{gather*}
 \sum _{i} \hF(C_{i}) = \hF(J_{0})-\hF(E)\\
```

### H048

Class: prose, notation or text-conversion cleanup; inspect both sides. Base 3283-3289; candidate 3270-3276.

```diff
@@ -3283,7 +3270,7 @@
 \hF(A) \le  X+8[32 \log 14+\operatorname{log} d'+\operatorname{log} \operatorname{max}(1,\operatorname{log} d',X)]
 \end{gather*}

-This is exactly H3.1. The later calculation in \(H_{4}\) uses only this displayed inequality, the \(H_{2}\) bound \(s/r\le 4\) and its separately supplied modular-Jacobian estimate. Neither \(H_{4}\) nor its rational certificate uses the old quotient presentation. The full-family domain, both CM/non-CM branches and the two transformed arguments used in 214 are unchanged. This proof does not itself accept those receiving applications or their other premises.
+This is exactly H3.1. The later calculation in \(H_{4}\) uses only this displayed inequality, the \(H_{2}\) bound \(s/r\le 4\) and its separately supplied modular-Jacobian estimate. Neither \(H_{4}\) nor its rational certificate uses the old quotient presentation. The full-family domain, both CM/non-CM branches and the two transformed arguments used in 214 are unchanged. The receiving applications require their other stated premises.

 \subsection{Nine application obligations}

```

### H049

Class: status, source locator or provenance prose. Base 3296-3325; candidate 3283-3312.

```diff
@@ -3296,30 +3283,30 @@
 \item 6. \textbf{Conventions.} All heights are original stable \(\hF\); all logarithms are natural; \(d'\) is the degree of \(L'\), not the evaluation splitting field. No Tate/cohomology change is made.
 \item 7. \textbf{Local conditions.} These published height/isogeny statements impose no new conductor, good-prime or integral-model constraint on the selected surfaces. Existing H0--H2 local hypotheses remain upstream; enlarging \(L'\) is not used.
 \item 8. \textbf{Exceptions.} \(r\ge 1\) and \(g\ge 2r\); \(E\) of dimension zero is included. Absolute simplicity is required in the non-CM \(H_{2}\) branch. The original separate CM estimate does not use this lemma. Negative individual heights are allowed, and the maximum with 1 is retained.
-\item 9. \textbf{Downstream dependencies.} Only the supplier for the \(H_{3}\) average and the auxiliary \(C_{i}\) change. H3.1 and all constants are identical, so downstream numerical arguments and rows need no modification, subject to review of this substitution. The indirect Rémond dependencies and final-body access limitation remain recorded.
+\item 9. \textbf{Downstream dependencies.} Only the supplier for the \(H_{3}\) average and the auxiliary \(C_{i}\) change. H3.1 and all constants are identical, so downstream numerical arguments and rows need no modification. The indirect R\'emond dependencies and final-body access limitation remain recorded.
 \end{itemize}

-Acceptance, if obtained, must bind this proof, these nine obligations, the actual \(H_{2}\) construction, H3/H4 consumer and published source version. The author makes no whole-214 Protocol \(D\) completion claim.
+
 \clearpage
 % Source: research/quartic214/proofs/primary-source-bridges.md
 \section{Published-source bridges for the inherited multiplicity argument}\label{q214:primary-source-bridges}
 \noindent\textit{Source: }\nolinkurl{research/quartic214/proofs/primary-source-bridges.md}.\par

-\begin{quote}\footnotesize Author: \nolinkurl{/root}, 2026-11-10. This is a source/application supplement to the unchanged \nolinkurl{../quadratic-ten-contact-integration/height/PROOF.md}, H1--H3. It is author work awaiting the separately recorded review. It closes only the identified source-access and application records; it does not prove the inherited geometric or modular-realization premises.\end{quote}
+\begin{quote}\footnotesize This is a source/application supplement to the unchanged height supplier reproduced in Section~\ref{q214:height-supplier}, H1--H3. It supplies only the identified source applications; it does not prove the inherited geometric or modular-realization premises.\end{quote}

 \subsection{Faltings: the actual field and Tate objects}

-\(I\) retrieved and read the published second edition of \emph{Rational Points} (1986), including the printed title/copyright pages and Faltings, ``Complements to Mordell'', Theorem 1(a)--(b), printed p.204 (PDF page 212). \(I\) inspected the page image as well as its extracted text. The exact downloaded PDF has SHA-256 \nolinkurl{3122011c0f12cc991fc0ff1601bb77cc1cd3e5ab2a0db023c0bf224ea576b6aa}; access URL: \url{https://yhzhumath.github.io/Mordell2024/RP.pdf}. This is a scan of the published edition, not an identification inferred from a search result. The publisher's edition identifier is \url{https://doi.org/10.1007/978-3-663-06812-9}.
+The published second edition of \emph{Rational Points} (1986) contains Faltings, \emph{Complements to Mordell}, Theorem 1(a)--(b), printed p.204 (PDF page 212). The exact downloaded PDF has SHA-256 \nolinkurl{3122011c0f12cc991fc0ff1601bb77cc1cd3e5ab2a0db023c0bf224ea576b6aa}; access URL: \url{https://yhzhumath.github.io/Mordell2024/RP.pdf}. This is a scan of the published edition. The publisher's edition identifier is \url{https://doi.org/10.1007/978-3-663-06812-9}.

 The theorem concerns an abelian variety over a finitely generated field of characteristic zero and any prime \(\ell \). It gives semisimplicity of the rational Tate representation and the endomorphism comparison (indeed the printed statement gives the integral comparison). Apply it with the \textbf{same} number field \(L'\) constructed in \(H_{1}\) and \(\ell =5\). A number field is finitely generated over \(Q\); after inverting its discriminant, its ring of integers supplies the smooth finitely generated Z-algebra in the source's setup. This applies to \(A_{a}\), \((A_{f})\) over \(L'\), and their finite products. No field obtained by splitting an evaluation fiber is substituted for \(L'\).

-\(H_{1}\) has shown that \(\rho _{5}\) restricted to \(G_{L'}\) is the actual covariant Tate action of \(A_{a}:\) the isogeny and scalar normalizations are 1 there. Under the retained assertion that all geometric endomorphisms are defined over \(L'\), the rational endomorphism algebra is \(B\). After extending scalars to \(\text{Qbar}_{5}\) it becomes \(M_{2}(\text{Qbar}_{5})\). The semisimple representation \(V_{5}(A_{a})\) therefore has one absolutely irreducible constituent \(W\) with multiplicity two: the endomorphism algebra of a semisimple representation is a product of matrix algebras, and here that product is the single \(M_{2}\). This is exactly the \(W\) consumed in \(H_{2}\), rather than a finite scalar twist. Semisimplicity remains valid after the coefficient extension because the finite-dimensional semisimple algebra generated by the image is separable in characteristic zero.
+\(H_{1}\) has shown that \(\rho _{5}\) restricted to \(G_{L'}\) is the actual covariant Tate action of \(A_{a}:\) the isogeny and scalar normalizations are 1 there. Under the retained assertion that all geometric endomorphisms are defined over \(L'\), the rational endomorphism algebra is \(B\). After extending scalars to \(\overline{\mathbb Q}_{5}\) it becomes \(M_{2}(\overline{\mathbb Q}_{5})\). The semisimple representation \(V_{5}(A_{a})\) therefore has one absolutely irreducible constituent \(W\) with multiplicity two: the endomorphism algebra of a semisimple representation is a product of matrix algebras, and here that product is the single \(M_{2}\). This is exactly the \(W\) consumed in \(H_{2}\), rather than a finite scalar twist. Semisimplicity remains valid after the coefficient extension because the finite-dimensional semisimple algebra generated by the image is separable in characteristic zero.

 For completeness, the isogeny conclusion in \(H_{2}\) follows from the stated endomorphism theorem, without needing a differently normalized ``isogeny theorem''. Apply \((b)\) to \(X\) times \(Y\) and use the two factor idempotents. The off-diagonal block gives \(\operatorname{Hom}_{L'}(X,Y)\) tensor \(Q_{5}\) \(=\) \(\operatorname{Hom}_{{G}_{L'}}(V_{5}(X),V_{5}(Y))\). Take \(X=((A_{f})_{L'})^{2}\) and \(Y=A_{a}^{e}\). H2's trace and semisimple-character comparison identifies their rational Tate representations; that comparison remains a separately stated input. The invertible maps form a nonempty open subset of this Hom space. Rational combinations of a basis of \(\operatorname{Hom}_{L'}(X,Y)\) tensor \(Q\) are dense in its \(Q_{5}\) extension, so one such combination is invertible on Tate modules. Clear its denominators. Its image has full dimension, and its kernel has dimension zero, hence it is an L'-isogeny. This argument neither assumes integral Tate lattices agree nor introduces an extra field extension.

 \subsection{Poincare reducibility over the stated ground field}

-\(I\) read the author-hosted scan of Milne, ``Abelian varieties'', \emph{Arithmetic Geometry} (1986), Proposition 12.1 and the following decomposition paragraph, printed p.122 (PDF page 20). Its PDF SHA-256 is \nolinkurl{86259344a576e4ef75a9d81e9bf43143f872a72b14cf8fcc2703f3aea6349136}; source: \url{https://www.jmilne.org/math/articles/1986b.pdf}. This scan is image-only; the page image was inspected directly. The theorem constructs a complement using an ample sheaf and the reduced connected kernel of the associated dual morphism. Those data are over the original field, so the complement is over that field, not just over its algebraic closure.
+The author-hosted scan of Milne, ``Abelian varieties'', \emph{Arithmetic Geometry} (1986), contains Proposition 12.1 and the following decomposition paragraph on printed p.122 (PDF page 20). Its PDF SHA-256 is \nolinkurl{86259344a576e4ef75a9d81e9bf43143f872a72b14cf8fcc2703f3aea6349136}; source: \url{https://www.jmilne.org/math/articles/1986b.pdf}. This scan is image-only. The theorem constructs a complement using an ample sheaf and the reduced connected kernel of the associated dual morphism. Those data are over the original field, so the complement is over that field, not just over its algebraic closure.

 For the surjection \(J\) over \(Q\) to \(A_{f}\) already supplied in \(H_{2}\), let \(K\) be the connected kernel. Apply Proposition 12.1 to \(K\) inside \(J\) over \(Q\). Its complement \(B'\) maps onto \(A_{f}\) with finite kernel; thus \(B'\) is a Q-defined subvariety Q-isogenous to \(A_{f}\). Base change to \(L'\) gives the \(B_{0}\) used in H2--H3. Separately, apply the same proposition over \(L'\) to decompose varieties into simple isogeny factors. Since \(A_{a}\) is absolutely simple under \(H_{0}\) and \(((A_{f})_{L'})^{2}\) is L'-isogenous to \(A_{a}^{e}\), every simple factor of \((A_{f})_{L'}\) is L'-isogenous to \(A_{a}\). Dimensions give \(e=2r\) and \((A_{f})_{L'}\) is L'-isogenous to \(A_{a}^{r}\). The division-algebra and absolute-simplicity premise remains H0's actual surface statement; Poincare reducibility does not supply that premise.

```

### H050

Class: status, source locator or provenance prose. Base 3335-3381; candidate 3322-3368.

```diff
@@ -3335,47 +3322,47 @@
 Domain and index coverage & Every rational a admitted by \(H_{0}\) is covered, separately in the non-CM branch. All \(e\) coefficient conjugates enter the unchanged trace comparison. The CM branch does not use the multiplicity argument.\\
 Transition and comparison maps & Restriction is to \(G_{L'}\); factor idempotents recover Hom from End of a product. Rational approximation and denominator clearing yield an isogeny over \(L'\). The kernel complement is first constructed over \(Q\), then base changed.\\
 Identity of the consumed object & The resulting \(W\), \(A_{a}^{r}\) and \(B_{0}\) are exactly those named in \(H_{2}\) and the filtration of \(H_{3}\). The dual cohomology convention is not substituted for the covariant Tate convention.\\
-Coefficient and normalization conventions & The initial comparison is rational \(Q_{5}\), with \(\text{Qbar}_{5}\) used only to identify simple constituents. Integral lattice equality is not claimed. No Faltings-height invariance under isogeny is inferred.\\
+Coefficient and normalization conventions & The initial comparison is rational \(Q_{5}\), with \(\overline{\mathbb Q}_{5}\) used only to identify simple constituents. Integral lattice equality is not claimed. No Faltings-height invariance under isogeny is inferred.\\
 Local conditions & The source theorems need no good-reduction or semistability hypothesis at every place. The good-place trace comparison is the separate \(H_{2}\) argument. \(\ell =5\) is a prime different from characteristic zero.\\
 Exceptional cases & Products have matching positive dimension. H0's non-CM absolute simplicity is required; the CM branch remains separate. The complement may have a finite kernel, which is sufficient.\\
-Downstream consumption & These identifications justify the L'-defined surfaces \(C_{i}\) in \(H_{3}\), conditional on its other inputs. The Rémond averaging inequality, modular-Jacobian height bound and normalized modularity are not proved by this supplement.\\
+Downstream consumption & These identifications justify the L'-defined surfaces \(C_{i}\) in \(H_{3}\), conditional on its other inputs. The R\'emond averaging inequality, modular-Jacobian height bound and normalized modularity are not proved by this supplement.\\
 \bottomrule
 \end{longtable}

 \subsection{Li's Fricke condition for the modular quotient}

-\(I\) read Li, ``Newforms and functional equations'', \emph{Mathematische Annalen} 212 (1975), pp.294--296, in Göttingen's digitized published volume \url{https://gdz.sub.uni-goettingen.de/id/PPN235181684_0212}. The library's IIIF manifest labels canvas 00000304 as printed p.296. \nolinkurl{PRIMARY_SOURCE_ACCESS.json} records the exact public page-image URLs and hashes. Page294 defines normalized primitive newforms; page296 defines the Fricke operator \(H_{M}\) and coefficient-conjugation operator \(K\) and, immediately before Lemma6, gives \(F|H_{M}=\gamma \) F|K for such a form. The character is arbitrary; no trivial-nebentypus assumption occurs there.
+Li, ``Newforms and functional equations'', \emph{Mathematische Annalen} 212 (1975), pp.294--296, is available in G\"ottingen's digitized published volume \url{https://gdz.sub.uni-goettingen.de/id/PPN235181684_0212}. The library's IIIF manifest labels canvas 00000304 as printed p.296. \nolinkurl{PRIMARY_SOURCE_ACCESS.json} records the exact public page-image URLs and hashes. Page 294 defines normalized primitive newforms; page 296 defines the Fricke operator \(H_{M}\) and coefficient-conjugation operator \(K\) and, immediately before Lemma 6, gives \(F|H_{M}=\gamma \) F|K for such a form. The character is arbitrary; no trivial-nebentypus assumption occurs there.

-Use Li's \(M=N\) from \(H_{2}\) and Li's second level parameter 1. The final form \(f\) in \(H_{1}\) is the primitive weight-two form, after the permitted finite twist has been absorbed; it is that same final form to which the formula applies. For each coefficient embedding \(\tau \), \(f^{\tau }\) is a normalized primitive form at the same level with character \(\epsilon ^{\tau }\), as in the inherited modular-factor construction. Its Fricke image is a nonzero scalar times its coefficient conjugate. Conjugating the embedding gives another embedding of the coefficient field into \(C\), so the latter form is in the span of all coefficient conjugates. Fricke is invertible, hence this span is Fricke-stable. Any nonzero scalar difference between normalized slash conventions preserves that span; no numerical value of \(\gamma \) is consumed. This supplies the specific Fricke-span hypothesis of the already checked published Shimura Theorem1 used in \(H_{2}\). It does not prove the existence/modularity of \(f\), nor replace the independent normalized modularity application in H0--H1.
+Use Li's \(M=N\) from \(H_{2}\) and Li's second level parameter 1. The final form \(f\) in \(H_{1}\) is the primitive weight-two form, after the permitted finite twist has been absorbed; it is that same final form to which the formula applies. For each coefficient embedding \(\tau \), \(f^{\tau }\) is a normalized primitive form at the same level with character \(\epsilon ^{\tau }\), as in the inherited modular-factor construction. Its Fricke image is a nonzero scalar times its coefficient conjugate. Conjugating the embedding gives another embedding of the coefficient field into \(C\), so the latter form is in the span of all coefficient conjugates. Fricke is invertible, hence this span is Fricke-stable. Any nonzero scalar difference between normalized slash conventions preserves that span; no numerical value of \(\gamma \) is consumed. This supplies the specific Fricke-span hypothesis of the published Shimura Theorem 1 used in \(H_{2}\). It does not prove the existence/modularity of \(f\), nor replace the independent normalized modularity application in H0--H1.

-The nine obligations for this identification are: (1) a normalized primitive weight-two form with finite character, supplied by \(H_{1}\); (2) the same \(f\) and all its coefficient conjugates, not an untwisted predecessor; (3) every coefficient embedding \(\tau \), including conjugate embeddings; (4) the operator \(H_{N}\) and coefficient conjugation \(K\), with no discarded scalar affecting span; (5) the exact stable span consumed by Shimura; (6) Li's \((M,1)=(N,1)\) and complex coefficient conventions, with only span used; (7) no added good-prime condition or character-conductor restriction; (8) nonzero forms and invertible Fricke, hence nonzero \(\gamma \), including nontrivial nebentypus; and (9) the resulting modular quotient/Tate constituent in \(H_{2}\), with the retained Galois-conjugacy and modularity premises explicit. This is a source/application bridge awaiting the new independent review, not a new assertion that those premises were all audited here.
+The nine obligations for this identification are: (1) a normalized primitive weight-two form with finite character, supplied by \(H_{1}\); (2) the same \(f\) and all its coefficient conjugates, not an untwisted predecessor; (3) every coefficient embedding \(\tau \), including conjugate embeddings; (4) the operator \(H_{N}\) and coefficient conjugation \(K\), with no discarded scalar affecting span; (5) the exact stable span consumed by Shimura; (6) Li's \((M,1)=(N,1)\) and complex coefficient conventions, with only span used; (7) no added good-prime condition or character-conductor restriction; (8) nonzero forms and invertible Fricke, hence nonzero \(\gamma \), including nontrivial nebentypus; and (9) the resulting modular quotient/Tate constituent in \(H_{2}\), with the retained Galois-conjugacy and modularity premises explicit. The stated modularity and Galois-conjugacy premises remain required.

 \subsection{Original-normalization lower bound used in \(H_{3}\)}

-\(I\) also checked the publisher PDF of Gaudron--Rémond, ``Théorème des périodes et degrés minimaux d'isogénies'', \emph{Commentarii Mathematici Helvetici} 89 (2014), 343--403, DOI \url{https://doi.org/10.4171/CMH/322}, from \url{https://ems.press/content/serial-article-files/43351?nt=1}. The precise downloaded hash is in \nolinkurl{PRIMARY_SOURCE_ACCESS.json}. Definition2.1 and \S{}2.3, printed pp.351--352, define a stable height \(h\) and identify \(\hF=h-(\operatorname{dim} A/2)\operatorname{log}\) \(\pi \). Corollary8.4, printed p.400, proves \(h(A)\ge -(\operatorname{dim} A/2)\operatorname{log}(2\pi )\) without a polarization hypothesis. \(I\) checked both page images. Combining the two gives \(\hF(A)\ge -\operatorname{dim}\) A \(\operatorname{log}(\pi  \sqrt{2})\ge -3\operatorname{dim}\) A/2; the final numerical relaxation is also stated on p.352.
+The publisher PDF of Gaudron--R\'emond, ``Th\'eor\`eme des p\'eriodes et degr\'es minimaux d'isog\'enies'', \emph{Commentarii Mathematici Helvetici} 89 (2014), 343--403, DOI \url{https://doi.org/10.4171/CMH/322}, is available from \url{https://ems.press/content/serial-article-files/43351?nt=1}. The precise downloaded hash is in \nolinkurl{PRIMARY_SOURCE_ACCESS.json}. Definition 2.1 and \S{}2.3, printed pp.351--352, define a stable height \(h\) and identify \(\hF=h-(\operatorname{dim} A/2)\operatorname{log}\) \(\pi \). Corollary 8.4, printed p.400, proves \(h(A)\ge -(\operatorname{dim} A/2)\operatorname{log}(2\pi )\) without a polarization hypothesis. Combining the two gives \(\hF(A)\ge -\operatorname{dim}\) A \(\operatorname{log}(\pi  \sqrt{2})\ge -3\operatorname{dim}\) A/2; the final numerical relaxation is also stated on p.352.

-This applies over the same number field \(L'\) to every quotient \(C_{i}\) and \(J/B_{0}\) in \(H_{3}\). These are abelian varieties defined over \(L'\), with no principal polarization or new ramification condition required. All \(i=1,...,r\) are covered, including growing \(r\); for a zero-dimensional quotient the bound is 0. No isogeny-invariance assertion is used. Thus the lower bound consumed when isolating \(\hF(B_{0})\) has the required original stable normalization. This closes that particular Bost-normalization source/application record at author level, pending review; it does not supply Rémond's superadditivity inequality.
+This applies over the same number field \(L'\) to every quotient \(C_{i}\) and \(J/B_{0}\) in \(H_{3}\). These are abelian varieties defined over \(L'\), with no principal polarization or new ramification condition required. All \(i=1,...,r\) are covered, including growing \(r\); for a zero-dimensional quotient the bound is 0. No isogeny-invariance assertion is used. Thus the lower bound consumed when isolating \(\hF(B_{0})\) has the required original stable normalization. This lower bound does not supply R\'emond's superadditivity inequality.

 The nine obligations are supplied by: (1) an abelian variety over a number field, (2) the actual \(C_{i}\) and \(J/B_{0}\), (3) every \(i\) and both positive- and zero-dimensional quotients, (4) the displayed stable-height normalization conversion, (5) the identical \(\hF\) in \(H_{3}\), (6) the dimension-dependent correction exactly retained, (7) no extra local hypothesis, (8) no principal-polarization or positive-dimension exception, and (9) the bound sum \(\hF(C_{i})\le \hF(B_{0})\le \hF(J)+3(g-2r)/2\) when combined with the separately retained superadditivity input. The corollary proves its all-polarizations assertion, rather than leaving an omitted polarization choice to the application.

-\subsection{Rémond publication-version check remains open}
+\subsection{R\'emond publication-version check remains open}

-On 2026-11-10 \(I\) rechecked the publisher record for \emph{Propriétés de la hauteur de Faltings}, Annali SNS Pisa 23 (2022), 1589--1596, DOI \url{https://doi.org/10.2422/2036-2145.202010_062}. The article-body link again redirected to subscriptions. The author page still links the June 2021 text \url{https://www-fourier.univ-grenoble-alpes.fr/~remond/2476.pdf}, already frozen in the old packet. Its Corollary 1.2 is the subvariety/quotient inequality, its post-Corollary 1.3 paragraph explicitly includes stable heights, and Proposition 2.1 gives the one-sided height variation used in \(H_{3}\). \(I\) compared those actual passages, not merely the abstract. The final 2022 body has \textbf{not} been compared; this record does not promote the author text to a checked final edition.
+The publisher record identifies \emph{Propri\'et\'es de la hauteur de Faltings}, Annali SNS Pisa 23 (2022), 1589--1596, DOI \url{https://doi.org/10.2422/2036-2145.202010_062}. The article-body link again redirected to subscriptions. The author page still links the June 2021 text \url{https://www-fourier.univ-grenoble-alpes.fr/~remond/2476.pdf}, already frozen in the old packet. Its Corollary 1.2 is the subvariety/quotient inequality, its post-Corollary 1.3 paragraph explicitly includes stable heights, and Proposition 2.1 gives the one-sided height variation used in \(H_{3}\). The final 2022 body has \textbf{not} been compared; this record does not promote the author text to a checked final edition.

-The new Faltings, Milne and Li source checks narrow the previous access qualification. They neither resolve the Rémond version comparison nor close the \(H_{0}\) geometry, modularity, modular-height or analytic prime-pattern chain. Historical files and verdicts remain unchanged. The new sources are recorded by URL, edition, hash and exact locator; the full third-party books are not added to this repository.
+The R\'emond version comparison and the \(H_{0}\) geometry, modularity, modular-height and analytic prime-pattern inputs remain separate requirements. The sources are recorded by URL, edition, hash and exact locator; the full third-party books are not reproduced here.
 \clearpage
 % Source: research/quartic214/proofs/source-carry.md
-\section{Exact retained analytic and restricted-converse carry to existing214}\label{q214:source-carry}
+\section{Exact retained analytic and restricted-converse carry to existing 214}\label{q214:source-carry}
 \noindent\textit{Source: }\nolinkurl{research/quartic214/proofs/source-carry.md}.\par
-\begin{quote}\small \textbf{Current foundation overlay:} The Version~15 byte-identity and no-new-repair statements in this dated source describe its historical freeze.  This edition incorporates the Version~16 foundation with the Version~18 inverse-theorem replacement in Section~\ref{v15:gi-full}, and the explicit source-to-consumer transition in Section~\ref{q214:foundation-transition}.  The historical text is retained as evidence; it does not negate or independently accept that changed application.\end{quote}
+\begin{quote}\small \textbf{Foundation sources:} The Version~15 byte-identity and no-new-repair statements in this dated source describe its historical freeze.  This edition incorporates the Version~16 foundation with the Version~18 inverse-theorem replacement in Section~\ref{v15:gi-full}, and the explicit source-to-consumer transition in Section~\ref{q214:foundation-transition}.  The historical text describes the earlier source version.\end{quote}

-Author \nolinkurl{/root/d214_uniform_existence}, 2026-11-11. This is an author comparison, not independent acceptance. The prior existence supplement remains frozen at manifest SHA256\nolinkurl{61509c3d17d642ad0b76fc1c6ffd435e68481e8e112143449faf5a188d368e05}. Public evidence is the root-frozen104-file subset at \nolinkurl{../../public-carry/}, manifest SHA256\nolinkurl{4137a55c240edb06d39f6332dc1145d8591f98045ff2ec62d817c97c0f8ab487}. Full read-only public checkout is HEAD\nolinkurl{1a49013b5683f58d2f88bb018a07d13770354157}. No acceptance is authored here.
+The prior existence supplement remains frozen at manifest SHA256\nolinkurl{61509c3d17d642ad0b76fc1c6ffd435e68481e8e112143449faf5a188d368e05}. Public evidence is the specified 104-file subset, manifest SHA256\nolinkurl{4137a55c240edb06d39f6332dc1145d8591f98045ff2ec62d817c97c0f8ab487}. The public source checkout is revision\nolinkurl{1a49013b5683f58d2f88bb018a07d13770354157}.

-[C01: carry rule and exact source] Both the latest public manuscript and the entire frozen214 \nolinkurl{existence/sources/quartic_v15.tex} are the same1924438 raw bytes, SHA256\nolinkurl{44ba3a8ec8521c29b81b26cfb9981cd6d5f3c76d54e7782438614842edb52c74}. Therefore the internal RC, Kato, GI and Gaussian proof objects below are unchanged source applications. Protocol D's permitted reuse of exact accepted derivations does not require pretending that this author re-proved every published theorem or every old proof. It does require the object/domain/map/consumer comparison made here. The source-first public final006 application and connection decisions, source-profile decisions and findings retain their original scopes and limitations. Their green result is not a premise of an arithmetic implication. Eligible review must decide whether these exact bindings carry; this author does not certify that decision.
+[C01: carry rule and exact source] Both the latest public manuscript and the entire frozen 214 \nolinkurl{existence/sources/quartic_v15.tex} are the same 1924438 raw bytes, SHA256\nolinkurl{44ba3a8ec8521c29b81b26cfb9981cd6d5f3c76d54e7782438614842edb52c74}. Therefore the internal RC, Kato, GI and Gaussian proof objects below are unchanged source applications. The source statements are used through the object, domain, map and consumer comparisons below, with all their stated hypotheses and source qualifications.

-[C02: restricted statements selected from broad targets] The relevant public targets are V15-FOUNDATION, V15-PROJECT-CLOSURE, V15-GAUSSIAN, KATO-1999-INDEX-AND-CLASS, the inverse theorem in Section~\ref{v15:gi:ASSEMBLY}, and their stated dependencies. The original huge polynomial's compiler, six-contact input and canonical code domain are not themselves needed to deduce a new214 solution; only the theorem components actually used here are selected. In particular the later short zero-preparation pole is not identified with the old eleven-witness degree75 predicate. The raw224 construction branches before the public223/222 paired-root/trace-quotient reductions. No approval of the latter is required to infer their unused equations. The retained scalar/root/reference/raw224 inverse maps are checked at their own current application targets and in the frozen214 algebra packet.
+[C02: restricted statements selected from broad targets] The relevant public targets are V15-FOUNDATION, V15-PROJECT-CLOSURE, V15-GAUSSIAN, KATO-1999-INDEX-AND-CLASS, the inverse theorem in Section~\ref{v15:gi:ASSEMBLY}, and their stated dependencies. The original huge polynomial's compiler, six-contact input and canonical code domain are not themselves needed to deduce a new 214 solution; only the theorem components actually used here are selected. In particular the later short zero-preparation pole is not identified with the old eleven-witness degree 75 predicate. The raw 224 construction branches before the public 223/222 paired-root/trace-quotient reductions. The retained scalar/root/reference/raw 224 inverse maps are checked at their own current application targets and in the frozen 214 algebra packet.

-[C03: exact rank and normalization] Read the actual generator proof at V15:347--443: two-isogeny descent, local squareclasses, torsion reductions, duplication-height comparison and finite small-height saturation certificate give \(2E_{\text{old}}(K)=ZP0\) for \(d_{\text{old}}=75-53\sqrt{2}\). The normalized model is obtained with \(\epsilon =1+\sqrt{2}\), \(\lambda =\epsilon ^{2}=3+2\sqrt{2}\) and \((x_{\text{new}},y_{\text{new}})=(\epsilon ^{4}*x_{\text{old}},\epsilon ^{6}*y_{\text{old}})\). Explicitly \((75-53\sqrt{2})(17+12\sqrt{2})=3-\sqrt{2}\) and \((1641-1160\sqrt{2})(17+12\sqrt{2})=57-28\sqrt{2}\); the ordinate transformation gives -660+417sqrt2 over32. Thus the normalized curve and generator are exactly \(E:y^{2}=x^{3}-(3-\sqrt{2})^{2}*x\) and \(P=2(1+\sqrt{2},2\sqrt{2})\), not an unrelated rank-one curve. The pointed isomorphism sends doubles to doubles and torsion to torsion; the finite nonidentity root charts therefore produce actual nonzero integer labels (n,a,t,b). Current profileSF27 explicitly records this corrected transport and separately supplies the normalized \(n^{2}-6\) height bound. The aggregate step of the214 supplement needs only nontorsionness, but the scalar and formal-index steps need this actual subgroup identification.
+[C03: exact rank and normalization] The generator proof at V15:347--443 shows that two-isogeny descent, local squareclasses, torsion reductions, duplication-height comparison and finite small-height saturation certificate give \(2E_{\text{old}}(K)=ZP0\) for \(d_{\text{old}}=75-53\sqrt{2}\). The normalized model is obtained with \(\epsilon =1+\sqrt{2}\), \(\lambda =\epsilon ^{2}=3+2\sqrt{2}\) and \((x_{\text{new}},y_{\text{new}})=(\epsilon ^{4}\cdot x_{\text{old}},\epsilon ^{6}\cdot y_{\text{old}})\). Explicitly \((75-53\sqrt{2})(17+12\sqrt{2})=3-\sqrt{2}\) and \((1641-1160\sqrt{2})(17+12\sqrt{2})=57-28\sqrt{2}\); the ordinate transformation gives \((-660+417\sqrt{2})/32\). Thus the normalized curve and generator are exactly \(E:y^{2}=x^{3}-(3-\sqrt{2})^{2}\cdot x\) and \(P=2(1+\sqrt{2},2\sqrt{2})\), not an unrelated rank-one curve. The pointed isomorphism sends doubles to doubles and torsion to torsion; the finite nonidentity root charts therefore produce actual nonzero integer labels (n,a,t,b). Current profile SF27 explicitly records this corrected transport and separately supplies the normalized \(n^{2}-6\) height bound. The aggregate step of the 214 supplement needs only nontorsionness, but the scalar and formal-index steps need this actual subgroup identification.

 [C04: exact RC input/output at the pole consumer] The retained restricted converse is

```

### H051

Class: star-subscript spelling and surrounding prose; same mathematical symbol. Base 3385-3404; candidate 3372-3391.

```diff
@@ -3385,20 +3372,20 @@
 E_{l}:y^{2}=x(x-l)(x+3l)
 \end{gather*}

-The current proof computes \(j=35152/9\) and non-CM before applying its representation arguments. The CM index curve in \(C_{03}\) is a different curve. The simultaneous descent in V15:8870--8970 constructs exactly two such parameters \(n_{\text{pole}}\) and \(n_{\text{pole}}*\theta \), including \(\theta =1\), and establishes full Selmer corank1 before invoking RC; it does not equate Selmer corank and Mordell--Weil rank before proving finite Sha. The preparation-zero proof at11656--11739 then rescales the resulting actual points to rational e,p,q,s for the actual given \(b\). The new214 supplementP19 verifies every hypothesis for its fresh \(b\), so the same two applications remain within domain. The RC proof fixes each \(E_{l}\) and its conductor before constructing coefficient families; no bound uniform as \(l\) varies is claimed or needed. Each input-dependent \(b\) may give different \(l\), and the universal theorem applies separately to each. None of its proof constants becomes a lower bound on the family parameter \(N\).
+The current proof computes \(j=35152/9\) and non-CM before applying its representation arguments. The CM index curve in \(C_{03}\) is a different curve. The simultaneous descent in V15:8870--8970 constructs exactly two such parameters \(n_{\text{pole}}\) and \(n_{\text{pole}}\cdot \theta \), including \(\theta =1\), and establishes full Selmer corank 1 before invoking RC; it does not equate Selmer corank and Mordell--Weil rank before proving finite Sha. The preparation-zero proof at 11656--11739 then rescales the resulting actual points to rational e,p,q,s for the actual given \(b\). The new 214 supplement P19 verifies every hypothesis for its fresh \(b\), so the same two applications remain within domain. The RC proof fixes each \(E_{l}\) and its conductor before constructing coefficient families; no bound uniform as \(l\) varies is claimed or needed. Each input-dependent \(b\) may give different \(l\), and the universal theorem applies separately to each. None of its proof constants becomes a lower bound on the family parameter \(N\).

-[C05: Kato required full index set] Read the actual current proof at13347--13946 and the actual earlier \(v_{11}\) \nolinkurl{norms.md} and \nolinkurl{interface.md} arguments. For a fixed constituent with primitive conductor \(D=2^{a}*d\), the retained construction defines \(y_{m}=\text{cor}_{Q(\zeta _{Dm})/Q(\zeta _{m})}(z_{Dm} \text{tensor} e_{\chi })\) for every \(m\) with \((m,c*d_{s})=1\). \(K_{5}\) makes \(N_{K}=2Nd\) and \(\text{Nprime}=c*d_{s}\) coprime. Restricting to all \(m\) divisible by \(N_{K}\) gives every index required by Kato1999\S{}0.1, not merely the smaller2004\S{}13.1 set. The class has the integral \(j_{*}\) condition by the inertia/Leray and Mackey calculation before mapping to the open scheme with \(N_{K}\) inverted. The same fixed lattice-clearing \(\text{factor}2^{{c}_{E}}\) applies at every level. It is a unit at the height-one localizations away from2 used downstream.
+[C05: Kato required full index set] The current proof at 13347--13946 and the earlier \(v_{11}\) \nolinkurl{norms.md} and \nolinkurl{interface.md} arguments supply the construction below. For a fixed constituent with primitive conductor \(D=2^{a}\cdot d\), the retained construction defines \(y_{m}=\text{cor}_{Q(\zeta _{Dm})/Q(\zeta _{m})}(z_{Dm} \otimes e_{\chi })\) for every \(m\) with \((m,c\cdot d_{s})=1\). \(K_{5}\) makes \(N_{K}=2Nd\) and \(N'_K=c\cdot d_{s}\) coprime. Restricting to all \(m\) divisible by \(N_{K}\) gives every index required by Kato 1999\S{}0.1, not merely the smaller 2004\S{}13.1 set. The class has the integral \(j_*\) condition by the inertia/Leray and Mackey calculation before mapping to the open scheme with \(N_{K}\) inverted. The same fixed lattice-clearing \(\text{factor}2^{{c}_{E}}\) applies at every level. It is a unit at the height-one localizations away from 2 used downstream.

-[C06: Kato transitions and actual limiting class] For every prime \(q\) not dividing Nprime, if q|m then \(S_{\text{Dmq}}=S_{Dm}\) and Proposition8.12 contributes the empty product, factor1. If \(q\) does not divide \(m\), \(N_{K}|m\) forces \(q\) outside2Nd; it is good and unramified for \(\chi \). Twisted equivariance gives the exact factor
+[C06: Kato transitions and actual limiting class] For every prime \(q\) not dividing \(N'_K\), if q|m then \(S_{Dmq}=S_{Dm}\) and Proposition 8.12 contributes the empty product, factor 1. If \(q\) does not divide \(m\), \(N_{K}|m\) forces \(q\) outside 2Nd; it is good and unramified for \(\chi \). Twisted equivariance gives the exact factor

 \begin{gather*}
-1-a_{q}*\chi (q)*q^{-1}*\sigma _{q}^{-1}+q^{-1}*\sigma _{q}^{-2}\\
-=P_{q}(q^{-1}*\sigma _{q}^{-1}), P_{q}(X)=1-a_{q}*\chi (q)*X+q*X^{2}
+1-a_{q}\cdot \chi (q)\cdot q^{-1}\cdot \sigma _{q}^{-1}+q^{-1}\cdot \sigma _{q}^{-2}\\
+=P_{q}(q^{-1}\cdot \sigma _{q}^{-1}), P_{q}(X)=1-a_{q}\cdot \chi (q)\cdot X+q\cdot X^{2}
 \end{gather*}

-Arithmetic Frobenius acts on \(T*\chi \) and inverse deck action is in the substitution; the representation is not dualized again. For every \(n\ge 1\) the supports \(S_{D*N_{K}*2^{n}}\) and \(S_{D*2^{n}}\) equal prime(2Nd). Corestriction transitivity through the common upper field gives \(\text{cor}(y_{N_{K}*2^{n}})=y_{2^{n}}\), without an Euler factor or a field-degree multiplier. These equalities commute with transition maps; the cofinal dyadic inverse limit is exactly the Section0.7 divisor-parameter-one class \(xi_{K}\), distinguished from the modular symbol xi. Thus the localized coordinate ideal \(J\) in \(K_{15}\) is the ideal of this actual retained class. Rank-one proportionality would not suffice and is not used. The \(\text{full}/j_{*}\) local cone comparison preserves \(H^{1}\) and the same class/ideal; paying for the actual \(H^{2}\) cone and fixed local factors yields \(K_{2}\). This source repair is incorporated already and is unchanged in214's supplier. A narrow current connection locator13775--13778 summarizes the coordinate-ideal conclusion; it is not the whole index/class argument. This carry binds the actual13799--13899 argument as well as its complete application record, so that short locator is not mistaken for the proof.
+Arithmetic Frobenius acts on \(T\otimes\chi \) and inverse deck action is in the substitution; the representation is not dualized again. For every \(n\ge 1\) the supports \(S_{DN_{K}2^{n}}\) and \(S_{D2^{n}}\) equal \(\operatorname{prime}(2Nd)\). Corestriction transitivity through the common upper field gives \(\text{cor}(y_{N_{K}2^{n}})=y_{2^{n}}\), without an Euler factor or a field-degree multiplier. These equalities commute with transition maps; the cofinal dyadic inverse limit is exactly the Section 0.7 divisor-parameter-one class \(\xi_{K}\), distinguished from the modular symbol \(\xi\). Thus the localized coordinate ideal \(J\) in \(K_{15}\) is the ideal of this actual retained class. Rank-one proportionality would not suffice and is not used. The \(\text{full}/j_{*}\) local cone comparison preserves \(H^{1}\) and the same class/ideal; paying for the actual \(H^{2}\) cone and fixed local factors yields \(K_{2}\). This index and class argument is the one used by the 214 supplier. A narrow current connection locator 13775--13778 summarizes the coordinate-ideal conclusion; it is not the whole index/class argument. This carry binds the actual 13799--13899 argument as well as its complete application record, so that short locator is not mistaken for the proof.

-[C07: RC assembly object preserved] The even bound uses one fixed-form, retained-smoothed class over one group ring, not separate varying-newform lattices. Smoothing has \(v_{2}(s_{F})=2e\), independent of the odd common conductor support; it is not divided out. The binary families have one fixed real sign and local squareclasses at2N. The common scalar/determinant construction acts on actual finite free cochain/local-condition/duality diagrams for fixed support, retaining maps and homotopies. The current terminal argument at6650--6721 compares the actual nonzero-address constant coefficients with the base derivative; it does not apply the unknown base estimate to itself. Its finite-degree/missing-address bound is chosen before the graph precision. The odd coefficient and conductor-one oriented-CM source replacements retain their current type, place and normalization restrictions via V15-PROJECT-CLOSURE. New214 only consumes the resulting universal RC implication in \(C_{04}\); it constructs no new coefficient family and alters none of these internal maps. Exact unchanged dependency carry therefore applies to the theorem already proved for every such fixed curve; this does not assert a new proof of all RC internals by this author.
+[C07: RC assembly object preserved] The even bound uses one fixed-form, retained-smoothed class over one group ring, not separate varying-newform lattices. Smoothing has \(v_{2}(s_{F})=2e\), independent of the odd common conductor support; it is not divided out. The binary families have one fixed real sign and local squareclasses at 2N. The common scalar/determinant construction acts on actual finite free cochain/local-condition/duality diagrams for fixed support, retaining maps and homotopies. The current terminal argument at 6650--6721 compares the actual nonzero-address constant coefficients with the base derivative; it does not apply the unknown base estimate to itself. Its finite-degree/missing-address bound is chosen before the graph precision. The odd coefficient and conductor-one oriented-CM source replacements retain their current type, place and normalization restrictions via V15-PROJECT-CLOSURE. New 214 only consumes the resulting universal RC implication in \(C_{04}\); it constructs no new coefficient family and alters none of these internal maps. Exact unchanged dependency carry therefore applies to the theorem already proved for every such fixed curve; all internal restricted-converse hypotheses remain required.

 [C08: the required GI output] Section~\ref{v15:gi:ASSEMBLY}
 gives, for fixed $k\geq3$ and $0<\delta\leq1$, one finite family of
```

### H052

Class: status, source locator or provenance prose. Base 3413-3429; candidate 3400-3416.

```diff
@@ -3413,17 +3400,17 @@
 step. These are the assertions used by $C_{09}$ and the arithmetic proof;
 no degree-rank induction or full-limit nilcharacter law is required.

-[C09: GI to Gaussian relative input] The Gaussian inverse step is in Section~\ref{subsec:gaussian-gowers-bridge}. For a required norm order \(s\ge 2\) it sets \(r=\operatorname{max}(s,4)\), \(k=r-1\ge 3\), fixes pseudorandom complexity and majorant scaling \(\alpha \), then a positive norm threshold. The prime-dominated function is not asserted one-bounded. The relative inverse theorem consumes GI(k) as its absolute input. Truncation and the precise indicator ratios give normalized \(U^{r}[L]\) norm at least \(\alpha *\delta /(4C_{\text{star}})\); no monotonicity with constant1 for normalized interval norms is assumed. The returned finite family is independent of L,z,b and the ray-class union. Stagewise \(z_{j}\) and physical thresholds fix each modulus before its asymptotic nilsequence and majorant estimates, uniformly over the finite residues at that stage. Thus the small-norm contradiction uses a pseudorandom sequence along a slow cutoff, not a fixed-z or growing-field limit. This is exactly the input used by the unchanged Gaussian prime theorem; the214 coefficient list only changes fixed arithmetic data after which that theorem quantifies.
+[C09: GI to Gaussian relative input] The Gaussian inverse step is in Section~\ref{subsec:gaussian-gowers-bridge}. For a required norm order \(s\ge 2\) it sets \(r=\operatorname{max}(s,4)\), \(k=r-1\ge 3\), fixes pseudorandom complexity and majorant scaling \(\alpha \), then a positive norm threshold. The prime-dominated function is not asserted one-bounded. The relative inverse theorem consumes GI(k) as its absolute input. Truncation and the precise indicator ratios give normalized \(U^{r}[L]\) norm at least \(\alpha \cdot \delta /(4C_*)\); no monotonicity with constant 1 for normalized interval norms is assumed. The returned finite family is independent of L,z,b and the ray-class union. Stagewise \(z_{j}\) and physical thresholds fix each modulus before its asymptotic nilsequence and majorant estimates, uniformly over the finite residues at that stage. Thus the small-norm contradiction uses a pseudorandom sequence along a slow cutoff, not a fixed-z or growing-field limit. This is exactly the input used by the unchanged Gaussian prime theorem; the 214 coefficient list only changes fixed arithmetic data after which that theorem quantifies.

-[C10: Gaussian finite-field and tail scope] The actual proof at17545--20359 uses fixed \(E=Q(i)\) ray fields, arithmetic Frobenius, Mitsui fixed-field Hecke estimates, ordinary prime majorants and the inverse theorem in Section~\ref{v15:gi-full}; no unrestricted Galois-prime theorem or Frei--Tinkova preprint is silently assumed. For fixed coefficients the full obstruction tail is bounded separately from finite-cutoff local exclusions. First choose the cutoff \(L_{\text{cut}}\) so \(C/(L_{\text{cut}} \log L_{\text{cut}})<c/[32(\log L_{\text{cut}})^{4k}]\), then fix the field/ray class data and use the slow-width diagonal asymptotic. This retains positive mass after removing every forbidden odd common divisor, including the same-position obstruction. The rational214 coefficient list after clearing scale denominators and merging repeats is within that exact fixed-data theorem. The finite set and sizes may depend on (N,x), which is allowed; no estimate uniform in them is used to define \(N_{0}\). The separate actual reduction lemma12239--12268 applies because \(\pi =9\) mod16 and1+3i mod7 imply \(p=1\) mod8 and \((7/p)=-1\). The reductions of \(d=3-\sqrt{2}\) have opposite squareclasses; the two CM traces are opposite and the actual group orders are the unordered norms \(N(\pi -1),N(\pi +1)\). Full two-torsion and \(P\) being a double justify d/4 in CRT. This is the precise curve and generator already identified in \(C_{03}\).
+[C10: Gaussian finite-field and tail scope] The actual proof at 17545--20359 uses fixed \(E=Q(i)\) ray fields, arithmetic Frobenius, Mitsui fixed-field Hecke estimates, ordinary prime majorants and the inverse theorem in Section~\ref{v15:gi-full}; no unrestricted Galois-prime theorem or Frei--Tinkova preprint is silently assumed. For fixed coefficients the full obstruction tail is bounded separately from finite-cutoff local exclusions. First choose the cutoff \(L_{\text{cut}}\) so \(C/(L_{\text{cut}} \log L_{\text{cut}})<c/[32(\log L_{\text{cut}})^{4k}]\), then fix the field/ray class data and use the slow-width diagonal asymptotic. This retains positive mass after removing every forbidden odd common divisor, including the same-position obstruction. The rational 214 coefficient list after clearing scale denominators and merging repeats is within that exact fixed-data theorem. The finite set and sizes may depend on (N,x), which is allowed; no estimate uniform in them is used to define \(N_{0}\). The separate actual reduction lemma12239--12268 applies because \(\pi =9\) mod 16 and 1+3i mod 7 imply \(p=1\) mod 8 and \((7/p)=-1\). The reductions of \(d=3-\sqrt{2}\) have opposite squareclasses; the two CM traces are opposite and the actual group orders are the unordered norms \(N(\pi -1),N(\pi +1)\). Full two-torsion and \(P\) being a double justify d/4 in CRT. This is the precise curve and generator already identified in \(C_{03}\).

-[C11: source-profile arithmetic replacements selected exactly] The two final source-profile files have raw hashes\nolinkurl{3668753afd46bff7e3a1bc3bed63d2f102009d5bd3d379fa67411c55b2aaa2d2} and\nolinkurl{881213958ad12b1af53e3c6758361ea8e1c371833453bcac7d63ee48909ad971}, exactly the subject hashes in the public source-profile decision. Their actual mathematical statements were read, as well as selected current connection records; the review verdict is not substituted for those statements. SF22--26 give fixed-data counting, strip, rational coefficients, CRT and real recurrence. SF27 identifies the normalized index model. SF33's finite/real order of choices and SF40's specific scalar rates \(R^{-4},R^{-6}\) match the new supplementP13--P18. SF35 changes the baseline |a-1| criterion to |a| with its own soundness/completeness; SF39 gives the parity criterion's exponent9/4; the four-contact232 application retains that exponent and supplies \(L_{N}=\text{floor}(9(2N-1)/4)+1\). SF45 gives the exact zero-preparation domain and conic charts, including \(e=1\) and \(e=-1/3\). These are unchanged source applications in the literal raw224 system.
+[C11: source-profile arithmetic replacements selected exactly] The two final source-profile files have raw hashes\nolinkurl{3668753afd46bff7e3a1bc3bed63d2f102009d5bd3d379fa67411c55b2aaa2d2} and\nolinkurl{881213958ad12b1af53e3c6758361ea8e1c371833453bcac7d63ee48909ad971}. Their mathematical statements supply the following inputs. SF22--26 give fixed-data counting, strip, rational coefficients, CRT and real recurrence. SF27 identifies the normalized index model. SF33's finite/real order of choices and SF40's specific scalar rates \(R^{-4},R^{-6}\) match the new supplementP13--P18. SF35 changes the baseline |a-1| criterion to |a| with its own soundness/completeness; SF39 gives the parity criterion's exponent 9/4; the four-contact 232 application retains that exponent and supplies \(L_{N}=\left\lfloor 9(2N-1)/4\right\rfloor+1\). SF45 gives the exact zero-preparation domain and conic charts, including \(e=1\) and \(e=-1/3\). These are unchanged source applications in the literal raw 224 system.

-[C12: changes that are freshly checked, not carried by their conclusions] SF28's old reflected exponent7/4 is replaced in214 by the new full-family height transfer giving7/6; its arithmetic conclusion does not authorize the stronger bound. SF30/SF32 describe old order-four extraction and a shifted scalar at the baseline, so they cannot directly supply214's order-three factor proof or \(c=|a|\). The frozen supplementP05--P12 supplies that changed route and exact integer consumers anew. SF33's old comparison factors cannot supply new pole certificates without reevaluating actual \(b\); the frozen supplementP17--P19 performs that reevaluation and checks the fresh Psi0 hypotheses. These are the substantive new214 joins requiring fresh eligible acceptance. The source rank, RC theorem, prime-pattern theorem, scalar parity/four-contact theorem and exact raw maps themselves are unchanged; their previously checked statement/domain/map scopes can be carried only with the bindings recorded here.
+[C12: arguments requiring separate source comparisons] SF28's old reflected exponent 7/4 is replaced in 214 by the new full-family height transfer giving 7/6; its arithmetic conclusion does not authorize the stronger bound. SF30/SF32 describe old order-four extraction and a shifted scalar at the baseline, so they cannot directly supply 214's order-three factor proof or \(c=|a|\). The frozen supplementP05--P12 supplies that changed route and exact integer consumers anew. SF33's old comparison factors cannot supply new pole certificates without reevaluating actual \(b\); the frozen supplementP17--P19 performs that reevaluation and checks the fresh Psi0 hypotheses. These are separate source applications required by the 214 argument. The source rank, RC theorem, prime-pattern theorem, scalar parity/four-contact theorem and exact raw maps themselves are unchanged; their stated domains and maps remain required with the bindings recorded here.

-[C13: exact disposition] Within the inspected source-to214 analytic/RC/rank/prime/scalar/pole joins, no unmatched mathematical required input remains after the frozen supplement is included. This is a bounded author conclusion: it does not newly validate every source theorem, the separate full-family height chain, contributor identities or final release. It gives concrete current application matching sufficient for an eligible reviewer to decide reuse at the established source scopes. The public final006 coverage decision expressly permits retained accepted source proofs while declining a fresh line-by-line reproof of all history; this author retains that distinction. Any source profile, theorem body, construction, consumer or inherited dependency change invalidates this carry. Historical classification is prior justification found and read, with current incorporation already present in the identical supplier; the fresh214 boundary supplement remains pending new independent acceptance. The defining threshold remains ineffective and no full numerical214 witness tuple has been produced.
+[C13: scope and limitations] The comparisons above identify the analytic, restricted-converse, rank, prime-selection, scalar and pole inputs used by the 214 argument. Their source hypotheses and the separate full-family height argument remain required. A change to a source statement, construction, consumer or inherited dependency requires a new source-to-consumer comparison. The defining threshold remains ineffective and no full numerical 214 witness tuple has been produced.
 \clearpage\section{Retained selected source proofs}\label{q214:selected}
-These mathematical fragments are reproduced in full at the selected public ranges.  Their original coarse character/conductor route is retained as historical source evidence; M1 and M5 in Section~\ref{q214:modularity} supply the current character and conductor comparison.  The evaluation fragments are read together with the exact lattice, different and metric bridges above.  Historical source qualifications remain visible; no new acceptance is inferred from their inclusion.
+These mathematical fragments are reproduced in full at the selected public ranges.  Their original coarse character/conductor route is retained as historical source evidence; M1 and M5 in Section~\ref{q214:modularity} supply the current character and conductor comparison.  The evaluation fragments are read together with the exact lattice, different and metric bridges above.  Historical source qualifications remain visible.
 \clearpage
 % Source: research/quartic214/sources/support-section1.md
 \subsection{1. The new radical and the actual modular objects}
```

### H053

Class: whitespace only. Base 3437-3453; candidate 3424-3440.

```diff
@@ -3437,17 +3424,17 @@
 \end{gather*}

 has positive odd valuation. Put \(R=B_{S}\) \(M_{S}(a)\). All prime products count
-a prime once. \(R\) is squarefree, divisible by210, and \(R\ge B_{S}>e\).
+a prime once. \(R\) is squarefree, divisible by 210, and \(R\ge B_{S}>e\).

 The supplied geometric construction in M:7605--8040 is the same full
 three-level normalizer fiber, not a different abelian surface. Its normal
-fiber field \(L\) has degree dividing576; all geometric homomorphisms
-between its conjugate fibers are defined over \(L\). Outside210 the quotient
+fiber field \(L\) has degree dividing 576; all geometric homomorphisms
+between its conjugate fibers are defined over \(L\). Outside 210 the quotient
 has tame coordinates \(w=z^{2}\) at its five branch sections and is etale
 elsewhere. Even contact is unramified after an unramified extension,
 including contact with infinity. Thus its field discriminant and bad
 reduction support lie in supp(R) for this \(S:\) the proof of M's \((R)\) uses
-only the branch contacts and primes dividing210, not the cutoff76176.
+only the branch contacts and primes dividing 210, not the cutoff 76176.
 The metric computation \((G)\), on this same surface, remains

 \begin{gather*}
```

### H054

Class: whitespace only. Base 3460-3466; candidate 3447-3453.

```diff
@@ -3460,7 +3447,7 @@
 In the non-CM case follow M's LR1--LR5 and \nolinkurl{quartic-height19}, with this
 same support \(T=\operatorname{supp}(R)\). The scalar sign cocycle is inflated from Gal(L/Q).
 At an odd ramified prime the chosen odd tame Dirichlet character has
-order dividing p-1; at2 its conductor divides4. The combined character
+order dividing p-1; at 2 its conductor divides 4. The combined character
 has order \(m\le 2\) \(\prod _{p|R,p \text{odd}}(p-1)=2\) \(\phi (R)\). Its square-root lift
 \(b\) and quadratic support-killing twist produce the same normal field \(L'\)
 with degree \(\le 2m[L:Q]\le 2304\) \(\phi (R)\). The twist introduces no prime
```

### H055

Class: whitespace only. Base 3473-3481; candidate 3460-3468.

```diff
@@ -3473,9 +3460,9 @@
 N\le 210^{300} R^{2}, \operatorname{rad}(N)|R. (2)
 \end{gather*}

-At \(p>7\) the field degree divides576, so the field inertia is tame;
+At \(p>7\) the field degree divides 576, so the field inertia is tame;
 the scalar lift is tame at odd primes and the representation conductor
-exponent is at most2. The unchanged crude exponents at2,3,5,7 are below300.
+exponent is at most 2. The unchanged crude exponents at 2,3,5,7 are below 300.
 No reduction of those exponents or new 2-primary character choice is
 used. The same \(A_{a}\) over \(L'\) is an isogeny factor of
 \(J=\operatorname{Jac}(X_{1}(N)/\operatorname{ker} \epsilon )\) over \(L'\). This is the actual factor, not a
```

### H056

Class: whitespace only. Base 3505-3512; candidate 3492-3499.

```diff
@@ -3505,8 +3492,8 @@

 Set \(R=B_{S}\) \(M_{S}(a)\), \(T=\operatorname{supp}(R)\), and \(\ell =\operatorname{log}\) \(R\). The parent proof \S{}1
 constructs the same surface \(A_{a}\) over a normal fiber field \(L\), with
-[L:Q] dividing576, \(L\) unramified outside \(T\), and \(A_{a}\) having good
-reduction over \(L\) away from210. All geometric homomorphisms between
+[L:Q] dividing 576, \(L\) unramified outside \(T\), and \(A_{a}\) having good
+reduction over \(L\) away from 210. All geometric homomorphisms between
 conjugate fibers are L-defined. These statements apply to every rational
 parameter in the stated domain; they are not restricted to integer
 inputs. Keep the parent's original stable Faltings height convention and
```

### H057

Class: whitespace only. Base 3521-3528; candidate 3508-3515.

```diff
@@ -3521,8 +3508,8 @@
 a positive torus rank \(t\le 2\) would give a unital injection \(B_{\text{quat}}\) into
 \(M_{t}(Q)\), which is impossible. It then proves that \(E=L(A_{a}[11])\) is normal
 over \(Q\). For every conjugate, the B-linear normalizer isogeny can be
-scaled to have degree prime to11, since the maximal-order normalizer
-at11 is \(Q_{11}^{*}\) \(\operatorname{GL}_{2}(Z_{11})\). The isogeny is L-defined and identifies the
+scaled to have degree prime to 11, since the maximal-order normalizer
+at 11 is \(Q_{11}^{*}\) \(\operatorname{GL}_{2}(Z_{11})\). The isogeny is L-defined and identifies the
 11-torsion kernels of the original surface and its conjugate. Thus every
 conjugate of \(E\) is \(E\). This normality is used, not inferred from a size
 estimate. Its faithful action gives Gal(E/L) contained in \(\operatorname{GL}_{4}(F_{11})\), so
```

### H058

Class: whitespace only. Base 3540-3555; candidate 3527-3542.

```diff
@@ -3540,16 +3527,16 @@
 576 |\operatorname{GL}_{4}(F_{11})| =23842542097059840000
 \end{gather*}

-Its valuations at2,3,5,7 are respectively15,4,4,1. Full11-torsion makes
-\(A_{a}\) semistable over \(E\) at every residue characteristic different from11;
-the preceding torus argument makes this good reduction. Only2,3,5,7
+Its valuations at 2,3,5,7 are respectively 15,4,4,1. Full 11-torsion makes
+\(A_{a}\) semistable over \(E\) at every residue characteristic different from 11;
+the preceding torus argument makes this good reduction. Only 2,3,5,7
 use this torsion criterion here.

 Retain the precise scalar construction M:8097--8179. The finite choice
 \(\mu _{\sigma }\) is inflated from Gal(L/Q), with \(\mu _{1}=1\). Its normalized version
 \(a_{\sigma }\) \(\mu _{\sigma }\), where \(a_{\sigma }=(\operatorname{deg} \mu _{\sigma })^{-1/4}\), has sign cocycle
 \(\epsilon _{\text{sign}}\) inflated from Gal(L/Q). The controlled Dirichlet character
-\(\chi \) is tame at every odd prime, has conductor dividing4 at2, and has
+\(\chi \) is tame at every odd prime, has conductor dividing 4 at 2, and has
 order \(m\le 2\) \(\phi (R)\). After the support-killing quadratic twist, the
 cochain \(b\) still satisfies \(b^{2}=\chi \) and \(\delta \) \(b=\epsilon _{\text{sign}}\). Its restriction
 to \(G_{L}\) is a conjugation-invariant character. Thus its kernel field \(L'\)
```

### H059

Class: whitespace only. Base 3568-3576; candidate 3555-3563.

```diff
@@ -3568,9 +3555,9 @@

 At an odd \(p\), \(Q(\chi )/Q\) is locally tame and the quadratic extension
 F'/F is tame. Base change of a tame local extension remains tame, so
-these additions do not increase \(v_{p}\) of the ramification index. At2,
-the inertia image of \(\chi \) has order at most2, and the second extension
-also has ramification degree at most2. Unramified degrees of these
+these additions do not increase \(v_{p}\) of the ramification index. At 2,
+the inertia image of \(\chi \) has order at most 2, and the second extension
+also has ramification degree at most 2. Unramified degrees of these
 fields do not affect this assertion. For a completion of \(F'\) at a place
 over \(p\) let \(e\) be its absolute ramification index. Equation(2), divisibility
 of a local inertia order into the global Galois group, and these two
```

### H060

Class: whitespace only. Base 3580-3586; candidate 3567-3573.

```diff
@@ -3580,7 +3567,7 @@
 v_{2}(e)\le 17, v_{3}(e)\le 4, v_{5}(e)\le 4, v_{7}(e)\le 1. (4)
 \end{gather*}

-The tame part of \(e\) is not bounded by(4), and will not need to be.
+The tame part of \(e\) is not bounded by (4), and will not need to be.

 \subsection{2. From the different to the last upper break}

```

### H061

Class: whitespace only. Base 3629-3637; candidate 3616-3624.

```diff
@@ -3629,9 +3616,9 @@
 at M:8363--8378; the calculation does not substitute the manuscript's
 coarse numerical bound.

-Let \(b_{\text{last}}\) be the last positive upper break, or0 when there is no
+Let \(b_{\text{last}}\) be the last positive upper break, or 0 when there is no
 wild ramification. Until \(b_{\text{last}}\) the upper group is nontrivial, so the
-integrand in(6) is at least1/2, except at irrelevant endpoints. Equations
+integrand in (6) is at least 1/2, except at irrelevant endpoints. Equations
 (5)--(6) imply

 \begin{gather*}
```

### H062

Class: whitespace only. Base 3639-3645; candidate 3626-3632.

```diff
@@ -3639,7 +3626,7 @@
 \end{gather*}

 No abelian or Hasse--Arf assumption is used. Large tame inertia cancels
-in the integral change of variables and causes no extra term in(7).
+in the integral change of variables and causes no extra term in (7).

 \subsection{3. The representation whose conductor is the final level}

```

### H063

Class: whitespace only. Base 3675-3689; candidate 3662-3676.

```diff
@@ -3675,15 +3662,15 @@
 \text{ for }  p=(2,3,5,7), \text{ respectively } . (8)
 \end{gather*}

-For \(p>7\), [L:Q] dividing576 implies that L/Q is tame at \(p\).
+For \(p>7\), [L:Q] dividing 576 implies that L/Q is tame at \(p\).
 \(A_{a}/L\) already has good reduction there, including \(p=11\). Wild inertia
 lies in \(G_{L}\), so \(\mu =a=1\) on it. On this pro-p group \(b\) is a character,
-its square \(\chi \) is tame, and its remaining image has order at most2;
+its square \(\chi \) is tame, and its remaining image has order at most 2;
 hence \(b\) is trivial. This proves \(a_{p}(r_{{\ell }_{c}})\le 2\) for \(p>7\), and zero
-outside \(T\). The prime11 argument does not apply the full11-torsion
-criterion in residue characteristic11.
+outside \(T\). The prime 11 argument does not apply the full 11-torsion
+criterion in residue characteristic 11.

-The object in(8) is the representation of the final primitive newform
+The object in (8) is the representation of the final primitive newform
 \(f\), after its finite twist is absorbed. M:8191--8273 identifies \(r_{5}\)
 exactly, then compares rational traces of the same quasi-isogenies
 (including division by the denominator-clearing integer and the factor
```

### H064

Class: whitespace only. Base 3701-3707; candidate 3688-3694.

```diff
@@ -3701,7 +3688,7 @@
 every \(p\ne 5\) and \(r_{3}\) at \(p=5\); this covers every prime. These established
 identifications are retained source inputs, not new modularity proofs.

-All four primes in(8) divide \(R\). Absorbing their baseline exponent2
+All four primes in (8) divide \(R\). Absorbing their baseline exponent 2
 into \(R^{2}\) gives

 \begin{gather*}
```

### H065

Class: status, source locator or provenance prose. Base 3710-3741; candidate 3697-3728.

```diff
@@ -3710,32 +3697,32 @@
 D_{0}=4608 C_{N}. (9)
 \end{gather*}

-This bound is the only conductor change in this packet.
+This bound is the only conductor change in this argument.

 \clearpage
 % Source: research/quartic214/sources/aggregate-bridge.md
 \section{Actual aggregate input for the 214 argument}\label{q214:source-aggregate-bridge}
 \noindent\textit{Source: }\nolinkurl{research/quartic214/sources/aggregate-bridge.md}.\par

-\begin{quote}\footnotesize Author: model task \nolinkurl{/root/d214_foundation_trace}, 2026-11-10. This is a proposed source/application bridge, not independent acceptance. All file and passage bindings are in \nolinkurl{FOUNDATION_MAP.json} (F-AGGREGATE). The target is the unchanged 214 proof at frozen private commit\nolinkurl{569a990bd3dfe141e2a1328f289fe62a82d13563}.\end{quote}
+\begin{quote}\footnotesize All file and passage bindings are in \nolinkurl{FOUNDATION_MAP.json} (F-AGGREGATE). The target is the unchanged 214 proof at frozen private commit\nolinkurl{569a990bd3dfe141e2a1328f289fe62a82d13563}.\end{quote}

-The conclusion needed at \nolinkurl{existence/PROOF.md:62} is a fixed inequality \(B^{2}\le M_{1}\) \(h(T)+M_{2}\) for all four nonzero integer labels, where \(T\) is the actual quarter-trace of the sum of their abscissae. No computable \(M_{2}\) is needed. The supplier is the internal proof in the frozen Version15 source, lines31238--31643, consumed explicitly at32449--32468. \(I\) read the sum-pole, cross-block independence, graph-family and canonical-height arguments, rather than inferring this conclusion from the product version.
+The conclusion needed at \nolinkurl{existence/PROOF.md:62} is a fixed inequality \(B^{2}\le M_{1}\) \(h(T)+M_{2}\) for all four nonzero integer labels, where \(T\) is the actual quarter-trace of the sum of their abscissae. No computable \(M_{2}\) is needed. The supplier is the internal proof in the frozen Version 15 source, lines 31238--31643, consumed explicitly at 32449--32468. This application uses the sum-pole, cross-block independence, graph-family and canonical-height arguments; the product version alone does not supply this conclusion.

-The final published source was retrieved on2026-11-10: \(J\). Von Buhren, \emph{Borne de hauteur semi-effective pour le problème de Mordell--Lang dans une variété abélienne}, JTNB29(2017),307--320, DOI10.5802/jtnb.981, publisher-distributed PDF at \url{https://www.numdam.org/item/10.5802/jtnb.981.pdf}. Theorem1.1 and preceding definitions, printed308, require a projective integral parameter scheme, an integral closed family in an abelian variety times that scheme, suitable ample embeddings, a finite-rank subgroup, and avoidance of fiberwise positive-dimensional abelian translates. They bound the canonical height by a fixed geometric multiple of parameter height plus a subgroup-dependent constant. Points of the subgroup belong to its allowed thickening by taking the error point zero. The final body explicitly does not determine the additive constant. No theorem about an individual finite fiber is substituted for this family theorem.
+The final published source is \(J\). Von Buhren, \emph{Borne de hauteur semi-effective pour le probl\`eme de Mordell--Lang dans une vari\'et\'e ab\'elienne}, JTNB 29(2017),307--320, DOI 10.5802/jtnb.981, publisher-distributed PDF at \url{https://www.numdam.org/item/10.5802/jtnb.981.pdf}. Theorem 1.1 and preceding definitions, printed 308, require a projective integral parameter scheme, an integral closed family in an abelian variety times that scheme, suitable ample embeddings, a finite-rank subgroup, and avoidance of fiberwise positive-dimensional abelian translates. They bound the canonical height by a fixed geometric multiple of parameter height plus a subgroup-dependent constant. Points of the subgroup belong to its allowed thickening by taking the error point zero. The final body explicitly does not determine the additive constant. No theorem about an individual finite fiber is substituted for this family theorem.

 \begin{itemize}
-\item 1. \textbf{Source hypotheses.} Take \(A=E_{0}^{8}\), \(E_{0}:Y^{2}=X^{3}-X\), parameter space \(P^{1}\), and the reduced graph closure \(V\) of the rational function \(F_{+}=(d/2)\sum X_{i}+(d'/2)\sum X'_{i}\), where \(d=3-\sqrt{2}\) and \(d'=3+\sqrt{2}\). The graph over its nonempty domain is integral; its closure is integral and closed in the projective product. All geometry is fixed before the labels. The source's embedding condition(1.1) can be met concretely: embed \(E_{0}\) by \(O(3O)\) as a smooth plane cubic, and the product by its Segre embedding. For every \(n\ge 1\) the plane-cubic exact sequence and \(H^{1}(P^{2},O(n-3))=0\) give surjective restriction of degree-n forms; tensor products give the same surjectivity on the product. Thus this fixed symmetric ample embedding has the required surjectivity in every degree. \(P^{1}\) uses \(O(1)\). This spells out an implicit embedding choice in the retained project proof; it does not alter its rational function or inequality.
+\item 1. \textbf{Source hypotheses.} Take \(A=E_{0}^{8}\), \(E_{0}:Y^{2}=X^{3}-X\), parameter space \(P^{1}\), and the reduced graph closure \(V\) of the rational function \(F_{+}=(d/2)\sum X_{i}+(d'/2)\sum X'_{i}\), where \(d=3-\sqrt{2}\) and \(d'=3+\sqrt{2}\). The graph over its nonempty domain is integral; its closure is integral and closed in the projective product. All geometry is fixed before the labels. The source's embedding condition (1.1) can be met concretely: embed \(E_{0}\) by \(O(3O)\) as a smooth plane cubic, and the product by its Segre embedding. For every \(n\ge 1\) the plane-cubic exact sequence and \(H^{1}(P^{2},O(n-3))=0\) give surjective restriction of degree-n forms; tensor products give the same surjectivity on the product. Thus this fixed symmetric ample embedding has the required surjectivity in every degree. \(P^{1}\) uses \(O(1)\). This spells out an implicit embedding choice in the retained project proof; it does not alter its rational function or inequality.
 \item 2. \textbf{Constructed objects.} The eight coordinates are \(([n_{i}]P_{1})\) and \(([n_{i}]P_{2})\), \(i=1,\ldots ,4\), where P1,P2 are the two pointed-isomorphism images of the same \(P\) and its conjugate. The finite-rank subgroup is generated by \(P_{1}\) in each of the first four positions and \(P_{2}\) in each of the last four. It is fixed and finitely generated, and contains every required tuple. The extra equality of the paired integer labels is an allowed restriction of that domain.
 \item 3. \textbf{Domain and index coverage.} Every \(n_{i}\) is a nonzero integer; negative, repeated and noncoprime labels are included. A nonzero multiple of either nontorsion base point is not \(O\), so the tuple lies in the domain of \(F_{+}\). The sum proof has no oddness hypothesis. The older product proof's odd-label domain is not used.
-\item 4. \textbf{Maps.} Use \(x=dX\), \(y=d\sqrt{d}Y\) and their conjugates; these are pointed isomorphisms. The squareclasses of d,d' are independent in \(K(i):\) neither is a square because its norm is7, and \(dd'=7\) is not a square in \(K\). A positive square from \(K(i)\) would already be a square in the real field \(K\). The automorphism fixing \(\sqrt{d}\) and negating \(\sqrt{d'}\) fixes \(\operatorname{End}(E_{0})=Z[i]\), fixes \(P_{1}\) and negates \(P_{2}\). Applying it to a torsion relation proves independence over Z[i] modulo torsion. These are the actual two base points; no unrelated generic pair is substituted.
-\item 5. \textbf{Consumed object.} \(F_{+}(q)=(1/2)\operatorname{Tr}(\sum x([n_{i}]P))=2T\). Canonical heights are preserved by the pointed isomorphisms and absolute conjugation. The eight-coordinate canonical-height sum is twice the four-coordinate sum. The fixed \(O(3O)\) product height is a fixed positive multiple of this sum. Since \(h(2T)\le h(T)+\log 2\), the factor2 is absorbed only into the fixed additive constant. The resulting \(T\) is the quarter-trace in the literal raw224 recovery and existence proof.
-\item 6. \textbf{Conventions.} \(h\) is absolute logarithmic Weil height, and the elliptic canonical height is the normalization with \(2\widehat{h}(Q)=\text{lim}\) \(4^{-m}\) \(h(x([2^{m}]Q))\). Put \(hP=\widehat{h}(P)>0\). The family theorem gives \(\sum \widehat{h}([n_{i}]P)\le M\) \(h(2T)+M_{0}\) for fixed M,M0. Then \(hP\cdot B^{2}\le \sum \widehat{h}([n_{i}]P)\); division by hP and the preceding log2 loss give exactly the required inequality. This also avoids using a sharper rank-height estimate merely to obtain existence of M1,M2. Replace \(M_{1}\) by a larger positive value and \(M_{2}\) by \(\operatorname{max}(1,M_{2})\) if necessary.
+\item 4. \textbf{Maps.} Use \(x=dX\), \(y=d\sqrt{d}Y\) and their conjugates; these are pointed isomorphisms. The squareclasses of d,d' are independent in \(K(i):\) neither is a square because its norm is 7, and \(dd'=7\) is not a square in \(K\). A positive square from \(K(i)\) would already be a square in the real field \(K\). The automorphism fixing \(\sqrt{d}\) and negating \(\sqrt{d'}\) fixes \(\operatorname{End}(E_{0})=Z[i]\), fixes \(P_{1}\) and negates \(P_{2}\). Applying it to a torsion relation proves independence over Z[i] modulo torsion. These are the actual two base points; no unrelated generic pair is substituted.
+\item 5. \textbf{Consumed object.} \(F_{+}(q)=(1/2)\operatorname{Tr}(\sum x([n_{i}]P))=2T\). Canonical heights are preserved by the pointed isomorphisms and absolute conjugation. The eight-coordinate canonical-height sum is twice the four-coordinate sum. The fixed \(O(3O)\) product height is a fixed positive multiple of this sum. Since \(h(2T)\le h(T)+\log 2\), the factor 2 is absorbed only into the fixed additive constant. The resulting \(T\) is the quarter-trace in the literal raw 224 recovery and existence proof.
+\item 6. \textbf{Conventions.} \(h\) is absolute logarithmic Weil height, and the elliptic canonical height is the normalization with \(2\widehat{h}(Q)=\text{lim}\) \(4^{-m}\) \(h(x([2^{m}]Q))\). Put \(hP=\widehat{h}(P)>0\). The family theorem gives \(\sum \widehat{h}([n_{i}]P)\le M\) \(h(2T)+M_{0}\) for fixed M,M0. Then \(hP\cdot B^{2}\le \sum \widehat{h}([n_{i}]P)\); division by hP and the preceding log 2 loss give exactly the required inequality. This also avoids using a sharper rank-height estimate merely to obtain existence of M1,M2. Replace \(M_{1}\) by a larger positive value and \(M_{2}\) by \(\operatorname{max}(1,M_{2})\) if necessary.
 \item 7. \textbf{Local conditions.} The source application is over algebraic number fields with absolute heights; no local integrality, splitting or coprimality condition is added. In the internal nonconstant-fiber proof, any nonzero abelian subgroup direction contains an elliptic direction \(E_{0}\to B\), obtained from a nonzero coordinate projection by duality and a polarization up to isogeny. Within one block, the common-pole leading coefficient is a nonzero tangent scalar times a sum of positive rational weights times \((n_{i}/n_{j})^{2}\). It cannot vanish. A pole cannot occur in both independent blocks. Thus \(F_{+}\) is nonconstant on every proposed positive-dimensional translate through \(q\).
-\item 8. \textbf{Exceptional cases.} Nonzero labels exclude all coordinate poles. Their signs and coincidences do not affect the positive-square coefficient. If a translate through \(q\) lay in a projective graph-closure fiber, its nonempty open intersection with the rational-function domain would force \(F_{+}\) to be constant there, contrary to the pole argument. Boundary components introduce no exception through \(q\). P's infinite order is independently established in the same source by its nonzero formal parameter at2, lines31544--31568; full rank-one generation is unnecessary for this height step.
-\item 9. \textbf{Downstream consumption.} The same recovered labels and \(T\) occur in \nolinkurl{existence/PROOF.md:9,62–78.} The nonzero physical arguments \(t_{0}=\lambda \) and \(t_{1}=T\lambda \) give \(h(T)\le h(t_{0})+h(t_{1})\). Separate divisibilities of each radical suffice; no product divisibility is claimed. This yields the displayed exponent7/(6k), \(\text{hence}14/9<2\) for the Lucas residual at \(k=3\). The additive constant remains fixed and ineffective, so it is absorbed only after choosing a sufficiently large uniform \(N_{0}\). No numerical defining threshold follows.
+\item 8. \textbf{Exceptional cases.} Nonzero labels exclude all coordinate poles. Their signs and coincidences do not affect the positive-square coefficient. If a translate through \(q\) lay in a projective graph-closure fiber, its nonempty open intersection with the rational-function domain would force \(F_{+}\) to be constant there, contrary to the pole argument. Boundary components introduce no exception through \(q\). P's infinite order is independently established in the same source by its nonzero formal parameter at 2, lines31544--31568; full rank-one generation is unnecessary for this height step.
+\item 9. \textbf{Downstream consumption.} The same recovered labels and \(T\) occur in \nolinkurl{existence/PROOF.md:9,62--78}. The nonzero physical arguments \(t_{0}=\lambda \) and \(t_{1}=T\lambda \) give \(h(T)\le h(t_{0})+h(t_{1})\). Separate divisibilities of each radical suffice; no product divisibility is claimed. This yields the displayed exponent 7/(6k), hence \(14/9<2\) for the Lucas residual at \(k=3\). The additive constant remains fixed and ineffective, so it is absorbed only after choosing a sufficiently large uniform \(N_{0}\). No numerical defining threshold follows.
 \end{itemize}

-Historical disposition: prior justification found, including the independent effective-aggregate assessment in \nolinkurl{research/v14-small-prime-height/exploration/effective-aggregate/ASSESSMENT.md.} That assessment already distinguishes a valid qualitative bound from the unprovided effective additive constant; it is not an objection to the current ineffective theorem. Manuscript disposition: the sum/graph/quarter-trace argument is incorporated in the frozen Version15 supplier and referenced by the 214 proof. The explicit embedding choice and the \(\text{canonical}-\text{height}-\text{ to } -B^{2}\) derivation above are supplemental author explanations pending non-author comparison. Current review: the old component review retains the aggregate interface conditionally; this new final-source bridge has no independent acceptance yet. It does not close rank/descent, modularity, prime patterns or pole realization.
+The aggregate bound is qualitative: no effective additive constant has been supplied, and none is needed for the ineffective theorem. The sum, graph and quarter-trace argument supplies the stated aggregate input. Rank and descent, modularity, prime patterns and pole realization remain separate prerequisites.
 \section{Retained differential-evaluation proof}\label{q214:eval-source}
 \subsection{Conventions and the evaluation estimate}

```

### H066

Class: status, source locator or provenance prose. Base 4321-4342; candidate 4308-4329.

```diff
@@ -4321,22 +4308,22 @@
 \section{Two redundant reference equations}\label{q214:raw224-source}
 \noindent\textit{Source: }\nolinkurl{research/version15/quartics/quartic-222/provenance/shared-T-redundancy224-006/PROOF.md}.\par

-This author-frozen successor removes Q5's two rational components from accepted raw224, retaining224 variables and198 residuals. Coordinates and parameter/input are unchanged. The parent manifest is \nolinkurl{a907e6dab18305d6b0f9443578c123d854eda6643d6e6c8b83db5c8dcaef0487} and its independent acceptance is7f79535dd88fcec653370ce495eaef4d4080e8791bdb40bc7cf205ac3710639f. The normative \(Q\) numbering and coefficients are the parent's \nolinkurl{FIELD-RELATIONS.json} first entry. No new identity is inferred from finite samples.
+This construction removes Q5's two rational components from raw 224, retaining 224 variables and 198 residuals. Coordinates and parameter/input are unchanged. The parent manifest is \nolinkurl{a907e6dab18305d6b0f9443578c123d854eda6643d6e6c8b83db5c8dcaef0487}. The normative \(Q\) numbering and coefficients are the parent's \nolinkurl{FIELD-RELATIONS.json} first entry. No new identity is inferred from finite samples.

-Write \(Q_{2}=M*w+L\). Its coefficient is
-\(M=B+(23335979380411305/9142573010269636-r*256685364214285/4571286505134818)f+(44649296511110307/111996519375803041-r*2886885451827729/447986077503212164)S+3317607896141091533/7167777240051394624+r*677690583653850567/1791944310012848656\).
+Write \(Q_{2}=M\cdot w+L\). Its coefficient is
+\(M=B+(23335979380411305/9142573010269636-r\cdot 256685364214285/4571286505134818)f+(44649296511110307/111996519375803041-r\cdot 2886885451827729/447986077503212164)S+3317607896141091533/7167777240051394624+r\cdot 677690583653850567/1791944310012848656\).

-The coefficients are149-integral and the coefficient of \(S\) is a149-unit; \nolinkurl{COEFFICIENT-DOMAIN.json} gives exact norm fractions and residues. \(B=f^{2}\) is retained.
+The coefficients are 149-integral and the coefficient of \(S\) is a149-unit; \nolinkurl{COEFFICIENT-DOMAIN.json} gives exact norm fractions and residues. \(B=f^{2}\) is retained.

-For any new solution, define \(g\) by the same polynomial as in the parent224 proof. The parent \nolinkurl{CONVERSE-RESULT.json} \(F\) and \(E\) certificates use only Q0,Q1,Q3, so these old reference equations already hold without \(Q_{2}\) orQ5. The same direct \(f=0\) contradiction also uses onlyQ0,Q1,Q3. Thus \(f\) is nonzero and the old \(H\) curve is recovered before interpreting \(w\). The unchanged scalar normalizer/core/pole equations give the inherited forced149 bound on Norm(f), independently of referencew and its outputW. Therefore \(\operatorname{ord}(f)=m>0\), \(\operatorname{ord}(S)=-m/2<0\), and \(\operatorname{ord}(g)=m/2\). Also \(A=a+cf\) is a unit, and \(D=\beta *S+\alpha \) is nonzero. No deleted relation has entered this argument.
+For any new solution, define \(g\) by the same polynomial as in the parent224 proof. The parent \nolinkurl{CONVERSE-RESULT.json} \(F\) and \(E\) certificates use only \(Q_0,Q_1,Q_3\), so these old reference equations already hold without \(Q_{2}\) or \(Q_5\). The same direct \(f=0\) contradiction also uses only \(Q_0,Q_1,Q_3\). Thus \(f\) is nonzero and the old \(H\) curve is recovered before interpreting \(w\). The unchanged scalar normalizer/core/pole equations give the inherited forced 149 bound on Norm(f), independently of reference w and its output W. Therefore \(\operatorname{ord}(f)=m>0\), \(\operatorname{ord}(S)=-m/2<0\), and \(\operatorname{ord}(g)=m/2\). Also \(A=a+cf\) is a unit, and \(D=\beta \cdot S+\alpha \) is nonzero. No deleted relation has entered this argument.

-The \(S\) term is the unique lowest-valuation term in \(M:\) \(B\) has order2m, the \(f\) term has orderm, and the constant has \(\text{order}\ge 0\). Hence \(M\ne 0\). Now form the expected value \(w*=g^{4}/f^{2}\). The parent's exact forward identity for \(Q_{2}\) gives \(Q_{2}(f,S,B,w*,T)=0\); it uses only the \(H\) curve, the reconstructed F/E, and \(D*T=N\), with f,A,D nonzero, not \(Q_{5}\). Since \(Q_{2}\) is linear in \(w\) with nonzero coefficientM, the retained \(Q_{2}=0\) forces \(w=w*\). Retained \(Q_{4}\) then forces \(W=w^{2}\). The parent's exact forward \(Q_{5}\) identity therefore gives \(Q_{5}=0\). All parent equations are recovered.
+The \(S\) term is the unique lowest-valuation term in \(M:\) \(B\) has order 2m, the \(f\) term has order m, and the constant has \(\text{order}\ge 0\). Hence \(M\ne 0\). Now form the expected value \(w_*=g^{4}/f^{2}\). The parent's exact forward identity for \(Q_{2}\) gives \(Q_{2}(f,S,B,w_*,T)=0\); it uses only the \(H\) curve, the reconstructed F/E, and \(D\cdot T=N\), with f,A,D nonzero, not \(Q_{5}\). Since \(Q_{2}\) is linear in \(w\) with nonzero coefficient M, the retained \(Q_{2}=0\) forces \(w=w_*\). Retained \(Q_{4}\) then forces \(W=w^{2}\). The parent's exact forward \(Q_{5}\) identity therefore gives \(Q_{5}=0\). All parent equations are recovered.

 Old to new simply drops two satisfied equations. New to old is the identity on every coordinate and reconstructs those equations by the preceding argument. Thus there is no lost zero branch. The admissible \(A_{N}\) family and ineffective defining threshold are essential inherited qualifications; this is not asserted for arbitrary symbolicA.

-Exact full expansion gives224 variables,198 residuals,degree4,content1,3014 coordinate monomials and3015 parameter terms. All coordinates occur. The coefficient height remains \(A_{N}^{2}+1\) for \(N\ge 53\), which is only a coefficient threshold. No manuscript adoption or independent acceptance is claimed by this author packet.
+Exact full expansion gives 224 variables,198 residuals,degree 4,content 1,3014 coordinate monomials and 3015 parameter terms. All coordinates occur. The coefficient height remains \(A_{N}^{2}+1\) for \(N\ge 53\), which is only a coefficient threshold.
 \clearpage\section{Finite certificates and exact computational sources}\label{q214:certificates}
-The following files identify finite inputs, methods and conclusions used in Part~I.  Their byte hashes bind the exact public objects.  The links provide the full recoverable certificates or implementations.  Their finite conclusions are distinct from the arithmetic theorem and from review acceptance.
+The following files identify finite inputs, methods and conclusions used in Part~I.  Their byte hashes bind the exact public objects.  The links provide the full recoverable certificates or implementations.  Their finite conclusions are distinct from the arithmetic theorem.
 \medskip\noindent\textbf{\nolinkurl{sources/contact-line-certificate.json}}\par\noindent
 The four quotient-quartic invariant checks and all $36$ cross-ratio candidate pairs used to recover the branch parameters $(2401,-343/32)$. The separate small-support certificate lists the five primitive forms and their ten pair determinants; the geometric proof supplies the cover and its tame charts.
 \par\noindent SHA-256: \nolinkurl{64896dfbb8661e04c044a68aa8679ee5dc20c0da36cc9a57640a885b7ca46614}.\par
```

### H067

Class: status, source locator or provenance prose. Base 4378-4392; candidate 4365-4379.

```diff
@@ -4378,15 +4365,15 @@
 \par\noindent SHA-256: \nolinkurl{9f461531df52ac73e02cf7a4ce270422715642c0d3112952cad4968d9a7e24ea}.\par
 \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/construction/artifacts/candidate214-brox/candidate214-polynomial.json}{Read the exact public source}.\par
 \medskip\noindent\textbf{\nolinkurl{construction/artifacts/candidate214-brox/STATISTICS.json}}\par\noindent
-The declared finite totals 214,188,2919,2920, degree four, content one and coefficient-only threshold53.
+The declared finite totals 214,188,2919,2920, degree four, content one and coefficient-only threshold 53.
 \par\noindent SHA-256: \nolinkurl{585635dab6320049320bffd5c1652c89db760d9f4e2ef19a10119011f70b5a68}.\par
 \href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/construction/artifacts/candidate214-brox/STATISTICS.json}{Read the exact public source}.\par
-\clearpage\section{Primary-source editions and inspection catalogue}\label{q214:catalogue}
+\clearpage\section{Primary-source editions and qualifications}\label{q214:catalogue}
 \begingroup\raggedright
-This catalogue retains the complete primary-source metadata accompanying the author packet.  An inspection statement describes its original named author and date.  It is not an assertion that the typesetter repeated that inspection, nor an independent acceptance of the present manuscript.  External books and PDFs are identified by their editions, locators, URLs and byte hashes; their complete contents are not republished here.
+This catalogue identifies primary sources by edition, locator, URL and byte hash. Their complete contents are not reproduced here. Source-access and edition-comparison limitations remain stated with the entries.
 \paragraph{height}
-\noindent\textbf{format}: height-sources-v1\par
-\noindent\textbf{author}: /root/sol61\_height\_foundation\par
+
+
 \noindent\textbf{parentPrivateCommit}: \nolinkurl{4acd40881c4abb6da7017c803a8f8d4b851d54cf}\par
 \noindent\textbf{broxCommit}: \nolinkurl{0697019486451cdfdb71b3272d5f26c6270d2a6b}\par
 \noindent\textbf{proofSha256}: \nolinkurl{25960e40419c7abea1f90ab4b35108169a5ca6ad04dccf3a3643e8d0e9bb7d7f}\par
```

### H068

Class: status, source locator or provenance prose. Base 4397-4425; candidate 4384-4412.

```diff
@@ -4397,29 +4384,29 @@
 \noindent\textbf{accessDate}: 2026-11-10\par
 \noindent\textbf{sha256}: \nolinkurl{b1e2e32bec626cf6d27fb7d6d8702b5c707e0c3dc002d979088e62d8cda514a4}\par
 \noindent\textbf{status}: final published PDF checked\par
-\noindent\textbf{locator}: Theorem1.9(1),pp7--8; original stable normalization\par
-\noindent\textbf{omitted\_local\_path}: GR2023-published.pdf\par
+\noindent\textbf{locator}: Theorem 1.9(1),pp.~7--8; original stable normalization\par
+
 \medskip\noindent\textbf{files entry 2.}\par
 \noindent\textbf{url}: \url{https://www-fourier.univ-grenoble-alpes.fr/~remond/2476.pdf}\par
 \noindent\textbf{accessDate}: 2026-11-10\par
 \noindent\textbf{sha256}: \nolinkurl{e23a019a7432e299014ead57a1ba51c3945b8351a64c96f339536786c8f79c5d}\par
-\noindent\textbf{status}: authorJune2021PD\allowbreak{}F checked; final2022body unavailable via subscription redirect\par
-\noindent\textbf{locator}: Corollary1.2,stable remark,Proposition2.1\par
-\noindent\textbf{omitted\_local\_path}: Remond2021-author.pdf\par
+\noindent\textbf{qualification}: June 2021 author PDF used; final 2022 body unavailable through the subscription redirect and not compared.\par
+\noindent\textbf{locator}: Corollary 1.2,stable remark,Proposition 2.1\par
+
 \medskip\noindent\textbf{files entry 3.}\par
 \noindent\textbf{url}: \url{https://www.jstage.jst.go.jp/article/jmath1948/25/3/25_3_523/_pdf/-char/ja}\par
 \noindent\textbf{accessDate}: 2026-11-10\par
 \noindent\textbf{sha256}: \nolinkurl{6a34cc46d06c0f5d4e7d380ddcbc45ec3143b19359bfebba5b1c8f00976f3308}\par
 \noindent\textbf{status}: final published PDF checked\par
-\noindent\textbf{locator}: Theorem1,pp526--527 including Fricke condition\par
-\noindent\textbf{omitted\_local\_path}: Shimura1973-published.pdf\par
+\noindent\textbf{locator}: Theorem 1,pp.~526--527 including Fricke condition\par
+
 \medskip\noindent\textbf{files entry 4.}\par
 \noindent\textbf{url}: \url{https://math.berkeley.edu/~ribet/Articles/korea.pdf}\par
 \noindent\textbf{accessDate}: 2026-11-10\par
 \noindent\textbf{sha256}: \nolinkurl{4c491a5294d1f4ec1b62855560aaea95cb64802d8fdd80fdd51ae2d2432f66ed}\par
 \noindent\textbf{status}: archived author PDF checked; final publication identity not asserted\par
 \noindent\textbf{locator}: \S{}3\par
-\noindent\textbf{omitted\_local\_path}: Ribet-author.pdf\par
+
 \paragraph{applications}
 \paragraph{O1-supplier}
 \noindent $\bullet$ U01\par
```

### H069

Class: journal edition, locator or associated scope wording. Base 4442-4451; candidate 4429-4438.

```diff
@@ -4442,10 +4429,10 @@
 \noindent $\bullet$ U14\par
 \noindent $\bullet$ U15\par
 \paragraph{closureLimits}
-\noindent $\bullet$ Final Rémond2022body not compared\par
+\noindent $\bullet$ Final R\'emond 2022 body not compared\par
 \noindent $\bullet$ Faltings/Chebotarev/Poincare/Li and underlying geometry/modularity/Arakelov inputs retain parent source-version qualifications\par
-\noindent $\bullet$ No independent inventory-coverage decision supplied\par
-\noindent\textbf{copyright}: Local third-party PDFs are source evidence. Do not infer redistribution permission; release may retain URL/hash/locator without PDF copies.\par
+
+\noindent\textbf{copyright}: Third-party PDFs are identified by URL, hash and locator and are not reproduced here.\par
 \paragraph{bridges}
 \paragraph{sources}
 \medskip\noindent\textbf{sources entry 1.}\par
```

### H070

Class: status, source locator or provenance prose. Base 4453-4707; candidate 4440-4684.

```diff
@@ -4453,255 +4440,245 @@
 \noindent\textbf{url}: \url{https://yhzhumath.github.io/Mordell2024/RP.pdf}\par
 \noindent\textbf{sha256}: \nolinkurl{3122011c0f12cc991fc0ff1601bb77cc1cd3e5ab2a0db023c0bf224ea576b6aa}\par
 \noindent\textbf{bytes}: 11049110\par
-\noindent\textbf{locator}: Second edition1986, Theorem1a-b, printed204/PDF212; title pages checked\par
+\noindent\textbf{locator}: Second edition 1986, Theorem 1a-b, printed 204/PDF 212\par
 \noindent\textbf{accessDate}: 2026-11-10\par
-\noindent\textbf{inspectedBy}: /root\par
-\noindent\textbf{status}: published page image directly read; current application authored separately, awaiting independent review\par
-\noindent\textbf{repositoryCopy}: false\par
+
+
+
 \medskip\noindent\textbf{sources entry 2.}\par
 \noindent\textbf{id}: Milne-Abelian-Varieties-1986.pdf\par
 \noindent\textbf{url}: \url{https://www.jmilne.org/math/articles/1986b.pdf}\par
 \noindent\textbf{sha256}: \nolinkurl{86259344a576e4ef75a9d81e9bf43143f872a72b14cf8fcc2703f3aea6349136}\par
 \noindent\textbf{bytes}: 3833583\par
-\noindent\textbf{locator}: Published1986, Proposition12.1, printed122/PDF20\par
+\noindent\textbf{locator}: Published 1986, Proposition 12.1, printed 122/PDF 20\par
 \noindent\textbf{accessDate}: 2026-11-10\par
-\noindent\textbf{inspectedBy}: /root\par
-\noindent\textbf{status}: published page image directly read; current application authored separately, awaiting independent review\par
-\noindent\textbf{repositoryCopy}: false\par
+
+
+
 \medskip\noindent\textbf{sources entry 3.}\par
 \noindent\textbf{id}: Li-p294.jpg\par
 \noindent\textbf{url}: \url{https://images.p.sub.uni-goettingen.de/iiif/image/gdz:PPN235181684_0212:00000302/full/1800,/0/default.jpg}\par
 \noindent\textbf{sha256}: \nolinkurl{9b31b9fc6f0b176bff3b0ef85f8f07285c0d40cb282cc80d20401e24a6b60d49}\par
 \noindent\textbf{bytes}: 991846\par
-\noindent\textbf{locator}: Mathematische Annalen212(1975), printed294\par
+\noindent\textbf{locator}: Mathematische Annalen 212(1975), printed 294\par
 \noindent\textbf{accessDate}: 2026-11-10\par
-\noindent\textbf{inspectedBy}: /root\par
-\noindent\textbf{status}: published page image directly read; current application authored separately, awaiting independent review\par
-\noindent\textbf{repositoryCopy}: false\par
+
+
+
 \medskip\noindent\textbf{sources entry 4.}\par
 \noindent\textbf{id}: Li-p295.jpg\par
 \noindent\textbf{url}: \url{https://images.p.sub.uni-goettingen.de/iiif/image/gdz:PPN235181684_0212:00000303/full/1800,/0/default.jpg}\par
 \noindent\textbf{sha256}: \nolinkurl{3c4882694168d10693977176097644198fc312259ce7715872b063264cf78633}\par
 \noindent\textbf{bytes}: 629475\par
-\noindent\textbf{locator}: Mathematische Annalen212(1975), printed295\par
+\noindent\textbf{locator}: Mathematische Annalen 212(1975), printed 295\par
 \noindent\textbf{accessDate}: 2026-11-10\par
-\noindent\textbf{inspectedBy}: /root\par
-\noindent\textbf{status}: published page image directly read; current application authored separately, awaiting independent review\par
-\noindent\textbf{repositoryCopy}: false\par
+
+
+
 \medskip\noindent\textbf{sources entry 5.}\par
 \noindent\textbf{id}: Li-p296.jpg\par
 \noindent\textbf{url}: \url{https://images.p.sub.uni-goettingen.de/iiif/image/gdz:PPN235181684_0212:00000304/full/1800,/0/default.jpg}\par
 \noindent\textbf{sha256}: \nolinkurl{11f38136cd27108d507c7662d1ddb46d8c572874b314b69aa1ad8be16395aad3}\par
 \noindent\textbf{bytes}: 758672\par
-\noindent\textbf{locator}: Mathematische Annalen212(1975), printed296\par
+\noindent\textbf{locator}: Mathematische Annalen 212(1975), printed 296\par
 \noindent\textbf{accessDate}: 2026-11-10\par
-\noindent\textbf{inspectedBy}: /root\par
-\noindent\textbf{status}: published page image directly read; current application authored separately, awaiting independent review\par
-\noindent\textbf{repositoryCopy}: false\par
+
+
+
 \medskip\noindent\textbf{sources entry 6.}\par
 \noindent\textbf{id}: GR2014-published.pdf\par
 \noindent\textbf{url}: \url{https://ems.press/content/serial-article-files/43351?nt=1}\par
 \noindent\textbf{sha256}: \nolinkurl{5afec329530089fd62d686f5e75331c91fc97fbf775ad6c4b275fc514459f31e}\par
 \noindent\textbf{bytes}: 576654\par
-\noindent\textbf{locator}: Definition2.1 and\S{}2.3 pp351--352; Corollary8.4 p400; PDFpages9--10,58\par
+\noindent\textbf{locator}: Definition 2.1 and \S{}2.3 pp.~351--352; Corollary 8.4 p.~400; PDF pages~9--10,58\par
 \noindent\textbf{accessDate}: 2026-11-10\par
-\noindent\textbf{inspectedBy}: /root\par
-\noindent\textbf{status}: Published definition,corollary proof and pageimages read; source/application bridge awaiting independent review\par
-\noindent\textbf{repositoryCopy}: false\par
-\noindent\textbf{qualification}: URLs and exact byte hashes identify external published evidence. Full third-party books and images are local review copies, not redistributed in the packet. Source/application discussion is PRIMARY\_SOURCE\_BRIDGES.md.\par
-\noindent\textbf{remondFinal}: Publisher article link redirects to subscription; final2022body not compared. Existing authorJune2021 version remains frozen.\par
+
+
+
+\noindent\textbf{qualification}: URLs and exact byte hashes identify external published evidence. Full third-party books and images are not reproduced here. Source/application discussion is PRIMARY\_SOURCE\_BRIDGES.md.\par
+\noindent\textbf{remondFinal}: Publisher article link redirects to subscription; final 2022 body not compared. Existing author June 2021 version remains frozen.\par
 \paragraph{modularity}
-\noindent\textbf{role}: AUTHOR only\par
+
 \noindent\textbf{date}: 2026-11-11\par
 \paragraph{primary sources}
 \medskip\noindent\textbf{primary\_sources entry 1.}\par
 \noindent\textbf{id}: Calegari2023\par
 \noindent\textbf{sha256}: \nolinkurl{d8e9a3ec3f2a4bedd674d95cf5f1e03fe26a67745c6f1cadf39b3fbf9e004cb5}\par
 \noindent\textbf{bytes}: 834759\par
-\noindent\textbf{locator}: definitions611--612; statement624\par
+\noindent\textbf{locator}: definitions 611--612; statement 624\par
 \noindent\textbf{url}: \url{https://ems.press/content/book-chapter-files/33140?nt=1}\par
-\noindent\textbf{publication}: EMS ICM2022 vol2 (2023),610--651\par
-\noindent\textbf{actual\_inspection}: actual statement text read; image-only Milne and Faltings pages additionally visually inspected\par
+\noindent\textbf{publication}: EMS ICM 2022 vol. 2 (2023),610--651\par
+
 \noindent\textbf{consumer\_proof\_sections}: M2\par
-\noindent\textbf{authoritative\_version}: published source; Milne author-hosted published chapter/edition\par
 \medskip\noindent\textbf{primary\_sources entry 2.}\par
 \noindent\textbf{id}: Carayol1987\par
 \noindent\textbf{sha256}: \nolinkurl{cc2605dd390eae903712a650e925b322472bb8831a11d6282b40030c0753944b}\par
 \noindent\textbf{bytes}: 1162324\par
-\noindent\textbf{locator}: \S{}\S{}1.4,2.1,2.4,3.4.2,4.1/fullTheorem4; printed36,37,41,42\par
+\noindent\textbf{locator}: \S{}\S{}1.4,2.1,2.4,3.4.2,4.1/full Theorem 4; printed 36,37,41,42\par
 \noindent\textbf{url}: \url{https://www.numdam.org/item/AST_1987__147-148__33_0.pdf}\par
-\noindent\textbf{publication}: Astérisque147--148(1987),33--47\par
-\noindent\textbf{actual\_inspection}: actual statement text read; image-only Milne and Faltings pages additionally visually inspected\par
+\noindent\textbf{publication}: Ast\'erisque 147--148(1987),33--47\par
+
 \noindent\textbf{consumer\_proof\_sections}: M5\par
-\noindent\textbf{authoritative\_version}: published source; Milne author-hosted published chapter/edition\par
 \medskip\noindent\textbf{primary\_sources entry 3.}\par
 \noindent\textbf{id}: Scholze2013\par
 \noindent\textbf{sha256}: \nolinkurl{f47a05bbcdd1ac69deb87ce4b6af5bbbc245cbbf0e99df74e8bf73b6d89227d7}\par
 \noindent\textbf{bytes}: 688182\par
-\noindent\textbf{locator}: Cor1.8pp5--6; Thms9.1,9.3pp74--75\par
+\noindent\textbf{locator}: Cor. 1.8, pp.~5--6; Thms. 9.1, 9.3, pp.~74--75\par
 \noindent\textbf{url}: \url{https://www.cambridge.org/core/services/aop-cambridge-core/content/view/9C5E8381BE3CD320ECADDDEAD2616B55/S2050508613000012a.pdf}\par
-\noindent\textbf{publication}: Forum Math.Pi1(2013),e1\par
-\noindent\textbf{actual\_inspection}: actual statement text read; image-only Milne and Faltings pages additionally visually inspected\par
+\noindent\textbf{publication}: Forum Math. Pi 1(2013),e1\par
+
 \noindent\textbf{consumer\_proof\_sections}: M2\par
-\noindent\textbf{authoritative\_version}: published source; Milne author-hosted published chapter/edition\par
 \medskip\noindent\textbf{primary\_sources entry 4.}\par
 \noindent\textbf{id}: Scholze2016\par
 \noindent\textbf{sha256}: \nolinkurl{3caea8d89df1e7d047d4edc89a679cd1deb2a19ec350effb450305a9c8eef3d1}\par
 \noindent\textbf{bytes}: 166017\par
-\noindent\textbf{locator}: whole4-page correction, especiallyp2\par
+\noindent\textbf{locator}: whole 4-page correction, especially p.~2\par
 \noindent\textbf{url}: \url{https://www.cambridge.org/core/services/aop-cambridge-core/content/view/423022854D448D337C999BCD505D8F75/S2050508616000044a.pdf}\par
-\noindent\textbf{publication}: Forum Math.Pi4(2016),e6\par
-\noindent\textbf{actual\_inspection}: actual statement text read; image-only Milne and Faltings pages additionally visually inspected\par
+\noindent\textbf{publication}: Forum Math. Pi 4(2016),e6\par
+
 \noindent\textbf{consumer\_proof\_sections}: M2\par
-\noindent\textbf{authoritative\_version}: published source; Milne author-hosted published chapter/edition\par
 \medskip\noindent\textbf{primary\_sources entry 5.}\par
 \noindent\textbf{id}: Fontaine1994\par
 \noindent\textbf{sha256}: \nolinkurl{ace926ffda578dacfe8a333c38d450235506ebe18f558ee9bfcb96dc6f70a8ec}\par
 \noindent\textbf{bytes}: 6497435\par
-\noindent\textbf{locator}: \S{}\S{}3.4--3.8; Theorem3.8p142\par
+\noindent\textbf{locator}: \S{}\S{}3.4--3.8; Theorem 3.8, p.~142\par
 \noindent\textbf{url}: \url{https://www.numdam.org/item/AST_1994__223__113_0.pdf}\par
-\noindent\textbf{publication}: Astérisque223(1994),113--184\par
-\noindent\textbf{actual\_inspection}: actual statement text read; image-only Milne and Faltings pages additionally visually inspected\par
+\noindent\textbf{publication}: Ast\'erisque 223(1994),113--184\par
+
 \noindent\textbf{consumer\_proof\_sections}: M2--M3\par
-\noindent\textbf{authoritative\_version}: published source; Milne author-hosted published chapter/edition\par
 \medskip\noindent\textbf{primary\_sources entry 6.}\par
 \noindent\textbf{id}: Kato2004\par
 \noindent\textbf{sha256}: \nolinkurl{3c6e14b11fa60262db8aff782ce3cf4d83e9100c0be83621a7e4ce502cec605d}\par
 \noindent\textbf{bytes}: 18010813\par
-\noindent\textbf{locator}: \S{}\S{}5.4,6.3,8.3,9.2,9.4,14.10.2--3; pp155,161--162,181,187--188,240\par
+\noindent\textbf{locator}: \S{}\S{}5.4,6.3,8.3,9.2,9.4,14.10.2--3; pp.~155,161--162,181,187--188,240\par
 \noindent\textbf{url}: \url{https://www.numdam.org/item/AST_2004__295__117_0.pdf}\par
-\noindent\textbf{publication}: Astérisque295(2004),117--290\par
-\noindent\textbf{actual\_inspection}: actual statement text read; image-only Milne and Faltings pages additionally visually inspected\par
+\noindent\textbf{publication}: Ast\'erisque 295(2004),117--290\par
+
 \noindent\textbf{consumer\_proof\_sections}: M2--M3\par
-\noindent\textbf{authoritative\_version}: published source; Milne author-hosted published chapter/edition\par
 \medskip\noindent\textbf{primary\_sources entry 7.}\par
 \noindent\textbf{id}: DeligneSerre1974\allowbreak{}\par
 \noindent\textbf{sha256}: \nolinkurl{65b390f6d33e827e30c6c66bbc15421eca51db3180bdf5996dcee19047be97fc}\par
 \noindent\textbf{bytes}: 2402609\par
-\noindent\textbf{locator}: \S{}\S{}1.6--1.9,3.1--3.2,Theorem4.1,8.2,8.5--8.6; pp509--510,513--514,525--526\par
+\noindent\textbf{locator}: \S{}\S{}1.6--1.9,3.1--3.2,Theorem 4.1,8.2,8.5--8.6; pp.~509--510,513--514,525--526\par
 \noindent\textbf{url}: null\par
-\noindent\textbf{publication}: Ann.Sci.ENS(4)7(1974),507--530\par
-\noindent\textbf{actual\_inspection}: actual statement text read; image-only Milne and Faltings pages additionally visually inspected\par
+\noindent\textbf{publication}: Ann. Sci. ENS (4) 7(1974),507--530\par
+
 \noindent\textbf{consumer\_proof\_sections}: M3--M4\par
-\noindent\textbf{authoritative\_version}: published source; Milne author-hosted published chapter/edition\par
 \medskip\noindent\textbf{primary\_sources entry 8.}\par
-\noindent\textbf{id}: Milne1986\par
+\noindent\textbf{id}: Milne 1986\par
 \noindent\textbf{sha256}: \nolinkurl{86259344a576e4ef75a9d81e9bf43143f872a72b14cf8fcc2703f3aea6349136}\par
 \noindent\textbf{bytes}: 3833583\par
-\noindent\textbf{locator}: Prop12.1p122; Prop12.9p125; Thm15.1(a)p129; scanpages20,23,27 visually read\par
+\noindent\textbf{locator}: Prop. 12.1, p.~122; Prop. 12.9, p.~125; Thm. 15.1(a), p.~129; scan pages 20, 23, 27 visually read\par
 \noindent\textbf{url}: null\par
-\noindent\textbf{publication}: ArithmeticGeomet\allowbreak{}ry,Springer(1986),103--150\par
-\noindent\textbf{actual\_inspection}: actual statement text read; image-only Milne and Faltings pages additionally visually inspected\par
+\noindent\textbf{publication}: Arithmetic Geometry, Springer (1986),103--150\par
+
 \noindent\textbf{consumer\_proof\_sections}: M2,M4,M6\par
 \noindent\textbf{authoritative\_version}: published source; Milne author-hosted published chapter/edition\par
 \medskip\noindent\textbf{primary\_sources entry 9.}\par
 \noindent\textbf{id}: Faltings1986\par
 \noindent\textbf{sha256}: \nolinkurl{3122011c0f12cc991fc0ff1601bb77cc1cd3e5ab2a0db023c0bf224ea576b6aa}\par
 \noindent\textbf{bytes}: 11049110\par
-\noindent\textbf{locator}: Complements to Mordell,Theorem1(a,b)p204; scanp212 visually read\par
+\noindent\textbf{locator}: Complements to Mordell, Theorem 1(a,b), p.~204; scan p.~212 visually read\par
 \noindent\textbf{url}: null\par
-\noindent\textbf{publication}: RationalPoints,secondedition,Vieweg(1986)\par
-\noindent\textbf{actual\_inspection}: actual statement text read; image-only Milne and Faltings pages additionally visually inspected\par
+\noindent\textbf{publication}: Rational Points, second edition, Vieweg (1986)\par
+
 \noindent\textbf{consumer\_proof\_sections}: M2,M6\par
-\noindent\textbf{authoritative\_version}: published source; Milne author-hosted published chapter/edition\par
 \medskip\noindent\textbf{primary\_sources entry 10.}\par
 \noindent\textbf{id}: MilneADT2006\par
 \noindent\textbf{sha256}: \nolinkurl{2c6195ec76a974f3f336c77cb71cc3845b018aad2d43136716b3477a3bc5fb31}\par
 \noindent\textbf{bytes}: 2136045\par
-\noindent\textbf{locator}: I.1.3,1.5,1.6(b,c)pp18--19; II.2.1proofp164\par
+\noindent\textbf{locator}: I.1.3,1.5,1.6(b,c), pp.~18--19; II.2.1, proof, p.~164\par
 \noindent\textbf{url}: \url{https://www.jmilne.org/math/Books/ADTnot.pdf}\par
-\noindent\textbf{publication}: ArithmeticDualit\allowbreak{}yTheorems,2ndedition,BookSurge2006\par
-\noindent\textbf{actual\_inspection}: actual statement text read; image-only Milne and Faltings pages additionally visually inspected\par
+\noindent\textbf{publication}: Arithmetic Duality Theorems, 2nd edition, BookSurge 2006\par
+
 \noindent\textbf{consumer\_proof\_sections}: M1,M3\par
 \noindent\textbf{authoritative\_version}: published source; Milne author-hosted published chapter/edition\par
 \medskip\noindent\textbf{primary\_sources entry 11.}\par
 \noindent\textbf{id}: MilneShimura2005\allowbreak{}\par
 \noindent\textbf{sha256}: \nolinkurl{6336f0a23084dc0bf815a901c61a0f925dbc8dc1c395af8864c1d90bea69c4a1}\par
 \noindent\textbf{bytes}: 1035957\par
-\noindent\textbf{locator}: complex uniformization and Theorem6.8,Cor6.9p319\par
+\noindent\textbf{locator}: complex uniformization and Theorem 6.8, Cor. 6.9, p.~319\par
 \noindent\textbf{url}: \url{https://www.jmilne.org/math/xnotes/svi2005.pdf}\par
-\noindent\textbf{publication}: ClayMath.Proc4(2005),265--378\par
-\noindent\textbf{actual\_inspection}: actual statement text read; image-only Milne and Faltings pages additionally visually inspected\par
+\noindent\textbf{publication}: Clay Math. Proc. 4(2005),265--378\par
+
 \noindent\textbf{consumer\_proof\_sections}: M2\par
 \noindent\textbf{authoritative\_version}: published source; Milne author-hosted published chapter/edition\par
 \medskip\noindent\textbf{primary\_sources entry 12.}\par
 \noindent\textbf{id}: Shimura1973\par
 \noindent\textbf{sha256}: \nolinkurl{6a34cc46d06c0f5d4e7d380ddcbc45ec3143b19359bfebba5b1c8f00976f3308}\par
 \noindent\textbf{bytes}: 1646652\par
-\noindent\textbf{locator}: Theorem1pp526--527; \S{}4equation4.1p531\par
+\noindent\textbf{locator}: Theorem~1, pp.~526--527; \S{}4, equation~4.1, p.~531\par
 \noindent\textbf{url}: \url{https://www.jstage.jst.go.jp/article/jmath/25/3/25_3_523/_pdf}\par
-\noindent\textbf{publication}: J.Math.Soc.Japan25(1973),523--544\par
-\noindent\textbf{actual\_inspection}: actual statement text read; image-only Milne and Faltings pages additionally visually inspected\par
+\noindent\textbf{publication}: J. Math. Soc. Japan 25(1973),523--544\par
+
 \noindent\textbf{consumer\_proof\_sections}: M3,M6\par
-\noindent\textbf{authoritative\_version}: published source; Milne author-hosted published chapter/edition\par
-\noindent\textbf{access}: Copied exact already-frozen published PDF from private height packet after current JStage500; source text directly read\par
+\noindent\textbf{access}: Retained published PDF; the current JStage retrieval returned 500.\par
 \medskip\noindent\textbf{primary\_sources entry 13.}\par
 \noindent\textbf{id}: Serre1968-reprint1989\par
 \noindent\textbf{sha256}: \nolinkurl{971dbfdd4414d99ea21d7d0af63dbb790d7b1188e9aec37f422181a2b543dec4}\par
 \noindent\textbf{bytes}: 5563667\par
-\noindent\textbf{locator}: ChapterI\S{}2.2Corollary2pI-8;\S{}2.3theorem/lemmapI-10--11\par
+\noindent\textbf{locator}: Chapter I, \S{}2.2, Corollary 2, p.~I-8; \S{}2.3, theorem/lemma, pp.~I-10--11\par
 \noindent\textbf{url}: \url{https://www.math.mcgill.ca/darmon/courses/18-19/gs/serre-mcgill.pdf}\par
-\noindent\textbf{publication}: Abelianl-AdicRepresentati\allowbreak{}onsandEllipticCu\allowbreak{}rves,1968,Addison-Wesley1989reprin\allowbreak{}t\par
-\noindent\textbf{actual\_inspection}: actual statement text read; image-only Milne and Faltings pages additionally visually inspected\par
+\noindent\textbf{publication}: Abelian \(l\)-Adic Representations and Elliptic Curves, 1968, Addison-Wesley 1989 reprint\par
+
 \noindent\textbf{consumer\_proof\_sections}: M4,M6\par
-\noindent\textbf{authoritative\_version}: published source; Milne author-hosted published chapter/edition\par
 \medskip\noindent\textbf{primary\_sources entry 14.}\par
 \noindent\textbf{id}: Li1975-p294\par
 \noindent\textbf{sha256}: \nolinkurl{9b31b9fc6f0b176bff3b0ef85f8f07285c0d40cb282cc80d20401e24a6b60d49}\par
 \noindent\textbf{bytes}: 991846\par
-\noindent\textbf{locator}: Math.Ann.212(1975),printed294\par
+\noindent\textbf{locator}: Math.Ann.212(1975),printed 294\par
 \noindent\textbf{url}: \url{https://images.p.sub.uni-goettingen.de/iiif/image/gdz:PPN235181684_0212:00000302/full/1800,/0/default.jpg}\par
-\noindent\textbf{actual\_inspection}: p296,p298 visually read; p294,p295 acquired, prior bridge read; no false claim of visual reading p294/p295\par
-\noindent\textbf{consumer\_proof\_sections}: M3precision finding; M6Fricke\par
+\noindent\textbf{qualification}: Printed pp.296 and 298 were visually checked; pp.294 and 295 were acquired but were not visually checked.\par
+\noindent\textbf{consumer\_proof\_sections}: M3 precision finding; M6 Fricke\par
 \medskip\noindent\textbf{primary\_sources entry 15.}\par
 \noindent\textbf{id}: Li1975-p295\par
 \noindent\textbf{sha256}: \nolinkurl{3c4882694168d10693977176097644198fc312259ce7715872b063264cf78633}\par
 \noindent\textbf{bytes}: 629475\par
-\noindent\textbf{locator}: Math.Ann.212(1975),printed295\par
+\noindent\textbf{locator}: Math.Ann.212(1975),printed 295\par
 \noindent\textbf{url}: \url{https://images.p.sub.uni-goettingen.de/iiif/image/gdz:PPN235181684_0212:00000303/full/1800,/0/default.jpg}\par
-\noindent\textbf{actual\_inspection}: p296,p298 visually read; p294,p295 acquired, prior bridge read; no false claim of visual reading p294/p295\par
-\noindent\textbf{consumer\_proof\_sections}: M3precision finding; M6Fricke\par
+\noindent\textbf{qualification}: Printed pp.296 and 298 were visually checked; pp.294 and 295 were acquired but were not visually checked.\par
+\noindent\textbf{consumer\_proof\_sections}: M3 precision finding; M6 Fricke\par
 \medskip\noindent\textbf{primary\_sources entry 16.}\par
 \noindent\textbf{id}: Li1975-p296\par
 \noindent\textbf{sha256}: \nolinkurl{11f38136cd27108d507c7662d1ddb46d8c572874b314b69aa1ad8be16395aad3}\par
 \noindent\textbf{bytes}: 758672\par
-\noindent\textbf{locator}: Math.Ann.212(1975),printed296\par
+\noindent\textbf{locator}: Math.Ann.212(1975),printed 296\par
 \noindent\textbf{url}: \url{https://images.p.sub.uni-goettingen.de/iiif/image/gdz:PPN235181684_0212:00000304/full/1800,/0/default.jpg}\par
-\noindent\textbf{actual\_inspection}: p296,p298 visually read; p294,p295 acquired, prior bridge read; no false claim of visual reading p294/p295\par
-\noindent\textbf{consumer\_proof\_sections}: M3precision finding; M6Fricke\par
+\noindent\textbf{qualification}: Printed pp.296 and 298 were visually checked; pp.294 and 295 were acquired but were not visually checked.\par
+\noindent\textbf{consumer\_proof\_sections}: M3 precision finding; M6 Fricke\par
 \medskip\noindent\textbf{primary\_sources entry 17.}\par
 \noindent\textbf{id}: Li1975-p298\par
 \noindent\textbf{sha256}: \nolinkurl{609bb6f3a234820789a6a07ed8219ac002e723e9fa46103e27a60d3b1dcdc386}\par
 \noindent\textbf{bytes}: 868473\par
-\noindent\textbf{locator}: Math.Ann.212(1975),printed298\par
+\noindent\textbf{locator}: Math.Ann.212(1975),printed 298\par
 \noindent\textbf{url}: \url{https://images.p.sub.uni-goettingen.de/iiif/image/gdz:PPN235181684_0212:00000306/full/1800,/0/default.jpg}\par
-\noindent\textbf{actual\_inspection}: p296,p298 visually read; p294,p295 acquired, prior bridge read; no false claim of visual reading p294/p295\par
-\noindent\textbf{consumer\_proof\_sections}: M3precision finding; M6Fricke\par
+\noindent\textbf{qualification}: Printed pp.296 and 298 were visually checked; pp.294 and 295 were acquired but were not visually checked.\par
+\noindent\textbf{consumer\_proof\_sections}: M3 precision finding; M6 Fricke\par
 \medskip\noindent\textbf{primary\_sources entry 18.}\par
 \noindent\textbf{id}: PanAuthorV2\par
 \noindent\textbf{sha256}: \nolinkurl{590171129d28a65749cf92b1f6099dbacaa90cc6698828f0a4dfd3da943f4824}\par
 \noindent\textbf{bytes}: 1552018\par
-\noindent\textbf{locator}: Theorem1.0.4p5; Conjecture1.0.1p2\par
+\noindent\textbf{locator}: Theorem 1.0.4, p.~5; Conjecture 1.0.1, p.~2\par
 \noindent\textbf{url}: \url{https://arxiv.org/pdf/1901.07166v2}\par
 \noindent\textbf{authoritative\_version}: historical author version, NOT final published body\par
-\noindent\textbf{actual\_inspection}: actual theorem/definitions read\par
-\noindent\textbf{use}: proof ancestry/history only; immediate live modularity input is Calegari2023\par
+
+\noindent\textbf{use}: proof ancestry/history only; immediate live modularity input is Calegari 2023\par
 \medskip\noindent\textbf{primary\_sources entry 19.}\par
 \noindent\textbf{id}: SilverbergZarhin\allowbreak{}1995\par
 \noindent\textbf{sha256}: \nolinkurl{fc62ba1c9d1315a0c441a3dd7de46a254f379289e630c407a3336c0230d91052}\par
 \noindent\textbf{bytes}: 1826653\par
-\noindent\textbf{locator}: Theorems3.4/3.5,printed405--406\par
+\noindent\textbf{locator}: Theorems 3.4/3.5,printed 405--406\par
 \noindent\textbf{url}: \url{https://www.numdam.org/article/AIF_1995__45_2_403_0.pdf}\par
-\noindent\textbf{publication}: AnnalesInstitutF\allowbreak{}ourier45(1995),403--420\par
-\noindent\textbf{actual\_inspection}: actualfinalTheor\allowbreak{}ems3.4/3.5andSection3text\allowbreak{}read;hashmatchesretai\allowbreak{}nedpublicsource\par
-\noindent\textbf{consumer}: PROVIDER\_SCOPE\_CARRYP4;PROOF\_FINALM5\par
+\noindent\textbf{publication}: Annales Institut Fourier 45(1995),403--420\par
+
+\noindent\textbf{consumer}: PROVIDER\_SCOPE\_CARRY P4; PROOF\_FINAL M5\par
 \medskip\noindent\textbf{primary\_sources entry 20.}\par
 \noindent\textbf{id}: Serre1967-retained-ramification\par
-\noindent\textbf{publication}: Cassels--FrohlichAlgebrai\allowbreak{}cNumberTheory(1967),ChapterVI,Localclassfieldt\allowbreak{}heory,128--161\par
-\noindent\textbf{locator}: \S{}\S{}4.1--4.3pp155--159\par
+\noindent\textbf{publication}: Cassels--Frohlich, Algebraic Number Theory (1967), Chapter VI, Local class field theory,128--161\par
+\noindent\textbf{locator}: \S{}\S{}4.1--4.3, pp.~155--159\par
 \noindent\textbf{retained\_extract\_sha256}: \nolinkurl{e0367b25a022eb27ec220e3c15b474a94fb96d70a6bb89b77f4a02c2231950fe}\par
-\noindent\textbf{retrieval\_url}: unknown in retainedsource record; no newlyinventedURL\allowbreak{}\par
-\noindent\textbf{actual\_inspection}: retainedexactsou\allowbreak{}rceapplicationan\allowbreak{}dgeneraltheoremp\allowbreak{}rofilecheckedaga\allowbreak{}instcurrentobjec\allowbreak{}ts;notafreshprimary\allowbreak{}extractread\par
+\noindent\textbf{retrieval\_url}: unknown in retained source record; no newly invented URL\par
+\noindent\textbf{qualification}: The retained source application was compared with the current objects; the primary extract was not freshly read.\par
 \noindent\textbf{fresh\_inspection\_supplement}: The 1967 printed volume has now
 been inspected at Chapter I, \S9, pp.~34, 36--39, and Chapter VI,
 \S2.4, p.~141, \S4.1, pp.~155--157, and \S4.3, pp.~158--159.
```

### H071

Class: whitespace only. Base 4714-4731; candidate 4691-4708.

```diff
@@ -4714,18 +4691,18 @@
 \paragraph{carry evidence}
 \noindent $\bullet$ CONDUCTOR\_RAMIFICATION\_PROFILES.json\par
 \noindent $\bullet$ PUBLIC\_FULL\_COVER\_DECISIONS.json\par
-\noindent $\bullet$ PROVIDER\_SCOPE\_CARRY.mdP4\par
+\noindent $\bullet$ PROVIDER\_SCOPE\_CARRY.md P4\par
 \paragraph{internal sources}
 \medskip\noindent\textbf{internal\_sources entry 1.}\par
 \noindent\textbf{id}: private-height\par
 \noindent\textbf{sha256}: \nolinkurl{25960e40419c7abea1f90ab4b35108169a5ca6ad04dccf3a3643e8d0e9bb7d7f}\par
 \noindent\textbf{bytes}: 23844\par
-\noindent\textbf{locator}: H0--H4; constructionH0/H1; applicationsH0.2/H1/H2; consumersH2--H4\par
+\noindent\textbf{locator}: H0--H4; construction H0/H1; applications H0.2/H1/H2; consumers H2--H4\par
 \medskip\noindent\textbf{internal\_sources entry 2.}\par
 \noindent\textbf{id}: private-v14-source\par
 \noindent\textbf{sha256}: \nolinkurl{b6f35c38c9e7370e8ee1b73948f9caa805ed194ca8551a9a61ab9f543ef06d5c}\par
 \noindent\textbf{bytes}: 1164623\par
-\noindent\textbf{locator}: 481--660;8097--8347 actual originalr5/r3/CL1/CL2\par
+\noindent\textbf{locator}: 481--660;8097--8347 actual original r5/r3/CL1/CL2\par
 \medskip\noindent\textbf{internal\_sources entry 3.}\par
 \noindent\textbf{id}: parent9\par
 \noindent\textbf{sha256}: \nolinkurl{73ca3d625ba42160cd2a58b4479a9053ee487d95f99161bf62b28d71c0fe54da}\par
```

### H072

Class: whitespace only. Base 4740-4746; candidate 4717-4723.

```diff
@@ -4740,7 +4717,7 @@
 \noindent\textbf{id}: public-v15\par
 \noindent\textbf{sha256}: \nolinkurl{44ba3a8ec8521c29b81b26cfb9981cd6d5f3c76d54e7782438614842edb52c74}\par
 \noindent\textbf{bytes}: 1924438\par
-\noindent\textbf{locator}: lemma505--705; baseline1334--1505; b-family8252--8495\par
+\noindent\textbf{locator}: lemma 505--705; baseline 1334--1505; b-family 8252--8495\par
 \medskip\noindent\textbf{internal\_sources entry 6.}\par
 \noindent\textbf{id}: source-bridge\par
 \noindent\textbf{sha256}: \nolinkurl{2c95d02a13ffa972eb6cb8d956b9063e970e33fd960e282c6d53ae8bb655c43c}\par
```

### H073

Class: status, source locator or provenance prose. Base 4780-4821; candidate 4757-4798.

```diff
@@ -4780,42 +4757,42 @@
 \noindent\textbf{id}: D210-fullprovider\par
 \noindent\textbf{sha256}: \nolinkurl{054ec4a656b82e1d1d17c7e9d3575afe722c42594f933256e7ea225f6a3f5e3b}\par
 \noindent\textbf{bytes}: 19349\par
-\noindent\textbf{locator}: wholeproof \S{}\S{}1--9,16sourceapplicat\allowbreak{}ions\par
+\noindent\textbf{locator}: whole proof, \S{}\S{}1--9, 16 source applications\par
 \medskip\noindent\textbf{internal\_sources entry 14.}\par
 \noindent\textbf{id}: D210-geometricisogeny\allowbreak{}\par
 \noindent\textbf{sha256}: \nolinkurl{f889eab0b9f7880a647ebb34f10ac44a73aaf748f2041cb03dea756079d6ab9e}\par
 \noindent\textbf{bytes}: 5819\par
-\noindent\textbf{locator}: wholeactualargum\allowbreak{}ent\par
+\noindent\textbf{locator}: whole actual argument\par
 \medskip\noindent\textbf{internal\_sources entry 15.}\par
 \noindent\textbf{id}: Yuan-finalbridge\par
 \noindent\textbf{sha256}: \nolinkurl{cad3c3e1a78dc2f300a6150181184067ae5636a7339292c7fe74ef8298e89f69}\par
 \noindent\textbf{bytes}: 4154\par
-\noindent\textbf{locator}: wholeactualmaxim\allowbreak{}alstackandisomet\allowbreak{}rycomparison\par
+\noindent\textbf{locator}: whole actual maximal-stack and isometry comparison\par
 \medskip\noindent\textbf{internal\_sources entry 16.}\par
 \noindent\textbf{id}: H19-sourceprofiles\par
 \noindent\textbf{sha256}: \nolinkurl{e9d209cbbecf3c0048cb7d5fb17ff4b428de23c8263659b84b2be8097816e9ec}\par
 \noindent\textbf{bytes}: 4940417\par
-\noindent\textbf{locator}: 16FULL-COVER+4conductor+H19RAMIFICATION+CM/D210profiles\par
+\noindent\textbf{locator}: 16 FULL-COVER + 4 conductor + H19 RAMIFICATION + CM/D210 profiles\par
 \medskip\noindent\textbf{internal\_sources entry 17.}\par
 \noindent\textbf{id}: public-final006coverage\allowbreak{}\par
 \noindent\textbf{sha256}: \nolinkurl{9b7dc976e14eb57b940e6f478e921726f3158403b890589f3269ee6eec3f743c}\par
 \noindent\textbf{bytes}: 1428503\par
-\noindent\textbf{locator}: exactextractedsc\allowbreak{}opes\par
+\noindent\textbf{locator}: exact extracted scopes\par
 \paragraph{access findings}
 \medskip\noindent\textbf{access\_findings entry 1.}\par
-\noindent\textbf{source}: PanfinalJAMS2022\allowbreak{}\par
+\noindent\textbf{source}: Pan final JAMS 2022\par
 \paragraph{attempts}
 \noindent $\bullet$ \url{https://www.ams.org/jams/2022-35-04/S0894-0347-2021-00991-1/S0894-0347-2021-00991-1.pdf}\par
 \noindent $\bullet$ \url{https://www.ams.org/journals/jams/2022-35-04/S0894-0347-2021-00991-1/S0894-0347-2021-00991-1.pdf}\par
 \noindent\textbf{result}: 403; final body not read; Calegari final statement read and used directly\par
 \medskip\noindent\textbf{access\_findings entry 2.}\par
-\noindent\textbf{source}: Washington1997Th\allowbreak{}eorem14.1\par
-\noindent\textbf{result}: not reacquired; proofM3instead derives finiteDirichletc\allowbreak{}haracter from published MilneADTglobalre\allowbreak{}ciprocity and Qidele decomposition\par
+\noindent\textbf{source}: Washington 1997 Theorem 14.1\par
+\noindent\textbf{result}: not reacquired; proof M3 instead derives a finite Dirichlet character from published Milne ADT global reciprocity and the rational idele decomposition\par
 \paragraph{uninspected live antecedents}
-\noindent $\bullet$ The sixteen exactpublicfullD\allowbreak{}210sourceapplica\allowbreak{}tions are carried at their accepted scope, not freshly reaudited from every finalPDF/HTML; the wholeinternalpro\allowbreak{}of and currentprivateco\allowbreak{}nnection are directlyread. Independentcurre\allowbreak{}ntreviewmustacce\allowbreak{}ptthisexactcarry\allowbreak{}.\par
-\noindent $\bullet$ No primaryfinalPanJ\allowbreak{}AMSbodycompariso\allowbreak{}n; immediatefinalpu\allowbreak{}blishedCalegarit\allowbreak{}heoremisdirectly\allowbreak{}checked.\par
-\noindent $\bullet$ SeparateheightH3\allowbreak{}Remond/final214assembly\allowbreak{}remainrootlanes.\par
-\noindent\textbf{supersedes\_scope\_statements\_only}: SOURCE\_USES.json remains frozen initialauthorhis\allowbreak{}tory; this finalinventory adds exactH01andcondu\allowbreak{}ctorcarry, without changing initialfiles.\par
+\noindent $\bullet$ The sixteen full D210 source applications retain their stated hypotheses and source scopes. Not every final PDF or HTML source has been freshly re-examined.\par
+\noindent $\bullet$ No primary final Pan JAMS body comparison; the immediate final published Calegari theorem is directly checked.\par
+\noindent $\bullet$ The height H3 R\'emond application and the full 214 argument remain separate requirements.\par
+\noindent\textbf{source scope}: SOURCE\_USES.json records the initial source use; this inventory also identifies the H01 and conductor applications.\par
 \paragraph{final bindings}
 \medskip\noindent\textbf{final\_bindings entry 1.}\par
 \noindent\textbf{sha256}: \nolinkurl{814676050b389793d196346f45e2797f39e2c5be0f3fee8457bb709b2607606e}\par
```

### H074

Class: status, source locator or provenance prose. Base 5079-5086; candidate 5056-5063.

```diff
@@ -5079,8 +5056,8 @@
 \noindent\textbf{url}: \url{https://msp.org/ant/2014/8-1/ant-v8-n1-p04-s.pdf}\par
 \noindent\textbf{access\_date}: 2026-11-10\par
 \noindent\textbf{publication\_status}: final publisher PDF\par
-\noindent\textbf{version}: ANT8(2014),89--140, DOI10.2140/ant.2014.8.89\par
-\noindent\textbf{publication\_scope}: Full third-party PDF retained only as local reviewer source; publication bundle may retain URL/hash and scoped excerpts instead.\par
+\noindent\textbf{version}: ANT 8(2014),89--140, DOI 10.2140/ant.2014.8.89\par
+\noindent\textbf{publication\_scope}: The full third-party PDF is not reproduced here; its URL, hash and source locators are retained.\par
 \medskip\noindent\textbf{height\_different entry 2.}\par
 \noindent\textbf{id}: stacks-0BFG.html\par
 \noindent\textbf{sha256}: \nolinkurl{f2b650fba17a059317eb935e33d33572a84edb970a5a7fc954a2be3d8a6eb212}\par
```

### H075

Class: status, source locator or provenance prose. Base 5088-5094; candidate 5065-5071.

```diff
@@ -5088,7 +5065,7 @@
 \noindent\textbf{access\_date}: 2026-11-10\par
 \noindent\textbf{publication\_status}: Stacks live tag page archived as exact HTML snapshot; no Git commit asserted\par
 \noindent\textbf{version}: content served at access date, byte-hash version\par
-\noindent\textbf{publication\_scope}: Full third-party PDF retained only as local reviewer source; publication bundle may retain URL/hash and scoped excerpts instead.\par
+\noindent\textbf{publication\_scope}: The full third-party PDF is not reproduced here; its URL, hash and source locators are retained.\par
 \medskip\noindent\textbf{height\_different entry 3.}\par
 \noindent\textbf{id}: stacks-0BVZ.html\par
 \noindent\textbf{sha256}: \nolinkurl{40a236f53d34753c7301bd6c881018f086b149e6b482cf15d1fed7339b11c829}\par
```

### H076

Class: status, source locator or provenance prose. Base 5096-5102; candidate 5073-5079.

```diff
@@ -5096,7 +5073,7 @@
 \noindent\textbf{access\_date}: 2026-11-10\par
 \noindent\textbf{publication\_status}: Stacks live tag page archived as exact HTML snapshot; no Git commit asserted\par
 \noindent\textbf{version}: content served at access date, byte-hash version\par
-\noindent\textbf{publication\_scope}: Full third-party PDF retained only as local reviewer source; publication bundle may retain URL/hash and scoped excerpts instead.\par
+\noindent\textbf{publication\_scope}: The full third-party PDF is not reproduced here; its URL, hash and source locators are retained.\par
 \medskip\noindent\textbf{height\_different entry 4.}\par
 \noindent\textbf{id}: stacks-0BW0.html\par
 \noindent\textbf{sha256}: \nolinkurl{0615dff37470db0bc6ed411b7e9b340bc8636ebe2ba73f92155eb41b02af85da}\par
```

### H077

Class: status, source locator or provenance prose. Base 5104-5110; candidate 5081-5087.

```diff
@@ -5104,7 +5081,7 @@
 \noindent\textbf{access\_date}: 2026-11-10\par
 \noindent\textbf{publication\_status}: Stacks live tag page archived as exact HTML snapshot; no Git commit asserted\par
 \noindent\textbf{version}: content served at access date, byte-hash version\par
-\noindent\textbf{publication\_scope}: Full third-party PDF retained only as local reviewer source; publication bundle may retain URL/hash and scoped excerpts instead.\par
+\noindent\textbf{publication\_scope}: The full third-party PDF is not reproduced here; its URL, hash and source locators are retained.\par
 \medskip\noindent\textbf{height\_different entry 5.}\par
 \noindent\textbf{id}: stacks-0BW4.html\par
 \noindent\textbf{sha256}: \nolinkurl{e00ca39df1423bf9650831740a12ba11073e26b97145501aed047e71e3b5eb29}\par
```

### H078

Class: status, source locator or provenance prose. Base 5112-5118; candidate 5089-5095.

```diff
@@ -5112,7 +5089,7 @@
 \noindent\textbf{access\_date}: 2026-11-10\par
 \noindent\textbf{publication\_status}: Stacks live tag page archived as exact HTML snapshot; no Git commit asserted\par
 \noindent\textbf{version}: content served at access date, byte-hash version\par
-\noindent\textbf{publication\_scope}: Full third-party PDF retained only as local reviewer source; publication bundle may retain URL/hash and scoped excerpts instead.\par
+\noindent\textbf{publication\_scope}: The full third-party PDF is not reproduced here; its URL, hash and source locators are retained.\par
 \medskip\noindent\textbf{height\_different entry 6.}\par
 \noindent\textbf{id}: stacks-0BW6.html\par
 \noindent\textbf{sha256}: \nolinkurl{1fd9f612c858f0111c257515bf42f527408d4fedf4e4351a01a5ab3abdfabe9f}\par
```

### H079

Class: status, source locator or provenance prose. Base 5120-5126; candidate 5097-5103.

```diff
@@ -5120,7 +5097,7 @@
 \noindent\textbf{access\_date}: 2026-11-10\par
 \noindent\textbf{publication\_status}: Stacks live tag page archived as exact HTML snapshot; no Git commit asserted\par
 \noindent\textbf{version}: content served at access date, byte-hash version\par
-\noindent\textbf{publication\_scope}: Full third-party PDF retained only as local reviewer source; publication bundle may retain URL/hash and scoped excerpts instead.\par
+\noindent\textbf{publication\_scope}: The full third-party PDF is not reproduced here; its URL, hash and source locators are retained.\par
 \medskip\noindent\textbf{height\_different entry 7.}\par
 \noindent\textbf{id}: stacks-0BWB.html\par
 \noindent\textbf{sha256}: \nolinkurl{3f08ca631d04dcd310e4831f2129c98fc5aad0e16a374bfcd2dffeb7a65338b0}\par
```

### H080

Class: status, source locator or provenance prose. Base 5128-5134; candidate 5105-5111.

```diff
@@ -5128,7 +5105,7 @@
 \noindent\textbf{access\_date}: 2026-11-10\par
 \noindent\textbf{publication\_status}: Stacks live tag page archived as exact HTML snapshot; no Git commit asserted\par
 \noindent\textbf{version}: content served at access date, byte-hash version\par
-\noindent\textbf{publication\_scope}: Full third-party PDF retained only as local reviewer source; publication bundle may retain URL/hash and scoped excerpts instead.\par
+\noindent\textbf{publication\_scope}: The full third-party PDF is not reproduced here; its URL, hash and source locators are retained.\par
 \medskip\noindent\textbf{height\_different entry 8.}\par
 \noindent\textbf{id}: stacks-0BWE.html\par
 \noindent\textbf{sha256}: \nolinkurl{a6ea73cec0946ca70e7c1bdfc99594f2a8e15ee232abab158d9a92a39cc9fbac}\par
```

### H081

Class: status, source locator or provenance prose. Base 5136-5142; candidate 5113-5119.

```diff
@@ -5136,7 +5113,7 @@
 \noindent\textbf{access\_date}: 2026-11-10\par
 \noindent\textbf{publication\_status}: Stacks live tag page archived as exact HTML snapshot; no Git commit asserted\par
 \noindent\textbf{version}: content served at access date, byte-hash version\par
-\noindent\textbf{publication\_scope}: Full third-party PDF retained only as local reviewer source; publication bundle may retain URL/hash and scoped excerpts instead.\par
+\noindent\textbf{publication\_scope}: The full third-party PDF is not reproduced here; its URL, hash and source locators are retained.\par
 \medskip\noindent\textbf{height\_different entry 9.}\par
 \noindent\textbf{id}: stacks-0BWF.html\par
 \noindent\textbf{sha256}: \nolinkurl{a1a842d28f6abc94ef2eadd9948f894988d02d1ea125b014f1ca441d702360b5}\par
```

### H082

Class: status, source locator or provenance prose. Base 5144-5158; candidate 5121-5135.

```diff
@@ -5144,15 +5121,15 @@
 \noindent\textbf{access\_date}: 2026-11-10\par
 \noindent\textbf{publication\_status}: Stacks live tag page archived as exact HTML snapshot; no Git commit asserted\par
 \noindent\textbf{version}: content served at access date, byte-hash version\par
-\noindent\textbf{publication\_scope}: Full third-party PDF retained only as local reviewer source; publication bundle may retain URL/hash and scoped excerpts instead.\par
+\noindent\textbf{publication\_scope}: The full third-party PDF is not reproduced here; its URL, hash and source locators are retained.\par
 \medskip\noindent\textbf{height\_different entry 10.}\par
 \noindent\textbf{id}: von-kaenel-published.pdf\par
 \noindent\textbf{sha256}: \nolinkurl{5749ce3a371c571655b44174e2a0d65c2e53dc179f518f0e52d585ff73da46f9}\par
 \noindent\textbf{url}: \url{https://www.cambridge.org/core/services/aop-cambridge-core/content/view/5DA2DC5985591DFBC9A26C20BA22F49B/S2050509421000293a.pdf/the-effective-shafarevich-conjecture-for-abelian-varieties-of-dollartext-gl2dollar-type.pdf}\par
 \noindent\textbf{access\_date}: 2026-11-10\par
 \noindent\textbf{publication\_status}: final publisher PDF\par
-\noindent\textbf{version}: FoM Sigma9(2021)e39, DOI10.1017/fms.2021.29\par
-\noindent\textbf{publication\_scope}: Full third-party PDF retained only as local reviewer source; publication bundle may retain URL/hash and scoped excerpts instead.\par
+\noindent\textbf{version}: FoM Sigma 9(2021)e39, DOI 10.1017/fms.2021.29\par
+\noindent\textbf{publication\_scope}: The full third-party PDF is not reproduced here; its URL, hash and source locators are retained.\par
 \paragraph{height metric}
 \medskip\noindent\textbf{height\_metric entry 1.}\par
 \noindent\textbf{id}: J2014\par
```

### H083

Class: status, source locator or provenance prose. Base 5164-5213; candidate 5141-5190.

```diff
@@ -5164,50 +5141,50 @@
 \noindent\textbf{accessed}: 2026-11-10\par
 \noindent\textbf{version}: Final publisher PDF\par
 \paragraph{evidence}
-\noindent\textbf{path}: sources/javanpeykar2014.pdf\par
+
 \noindent\textbf{sha256}: \nolinkurl{ec890fb41c58dee038ee2e06b530954f3aab85035238cd54a4c0ef081fcb8ea0}\par
 \noindent\textbf{bytes}: 1222544\par
 \paragraph{text}
-\noindent\textbf{path}: sources/javanpeykar2014.txt\par
+
 \noindent\textbf{sha256}: \nolinkurl{ae952c57b066d1cd0daaffb88a5407a84bc970a694bb8f1e1e27e2aa33935845}\par
 \noindent\textbf{bytes}: 163512\par
 \paragraph{locators}
-\noindent $\bullet$ \S{}2.1 printed pp93--94: H0 inner product and determinant metric\par
-\noindent $\bullet$ \S{}2.3 printed pp97--98: minimal regular semistable model, normalized arithmetic degree and stable Jacobian identification\par
+\noindent $\bullet$ \S{}2.1 printed pp.~93--94: H0 inner product and determinant metric\par
+\noindent $\bullet$ \S{}2.3 printed pp.~97--98: minimal regular semistable model, normalized arithmetic degree and stable Jacobian identification\par
 \noindent\textbf{scope}: Direct final published statement and its definitions; Szpiro lemma cited there is not separately re-audited. The published identification is the permitted theorem input.\par
 \medskip\noindent\textbf{height\_metric entry 2.}\par
 \noindent\textbf{id}: VK2021\par
 \noindent\textbf{title}: The effective Shafarevich conjecture for abelian varieties of GL2-type\par
-\noindent\textbf{author}: Rafael von Känel\par
+\noindent\textbf{author}: Rafael von K\"anel\par
 \noindent\textbf{publication}: Forum of Mathematics, Sigma 9 (2021), e39, 1--29\par
 \noindent\textbf{doi}: 10.1017/fms.2021.29\par
 \noindent\textbf{url}: \url{https://www.cambridge.org/core/services/aop-cambridge-core/content/view/5DA2DC5985591DFBC9A26C20BA22F49B/S2050509421000293a.pdf/the-effective-shafarevich-conjecture-for-abelian-varieties-of-dollartext-gl2dollar-type.pdf}\par
 \noindent\textbf{accessed}: 2026-11-10\par
 \noindent\textbf{version}: Final publisher PDF\par
 \paragraph{evidence}
-\noindent\textbf{path}: sources/vonkanel2021.pdf\par
+
 \noindent\textbf{sha256}: \nolinkurl{5749ce3a371c571655b44174e2a0d65c2e53dc179f518f0e52d585ff73da46f9}\par
 \noindent\textbf{bytes}: 667353\par
 \paragraph{text}
-\noindent\textbf{path}: sources/vonkanel2021.txt\par
+
 \noindent\textbf{sha256}: \nolinkurl{6ddb8af13dc25fd1c5a2a8f8c822e8ab77ed65fde6a4456ab9609b6c50a671a2}\par
 \noindent\textbf{bytes}: 161161\par
 \paragraph{locators}
-\noindent $\bullet$ \S{}2.1 printed p5: Néron differential-line norm, all-embedding degree, stable extension invariance\par
-\noindent $\bullet$ \S{}2.1 printed p5 after(2.2): hF=hB-(g/2)log\ensuremath{\pi }\par
-\noindent\textbf{scope}: Final definition/base-change paragraphs read, not a complete source audit of its cited semistable-reduction and Néron-model theorems.\par
+\noindent $\bullet$ \S{}2.1 printed p.~5: N\'eron differential-line norm, all-embedding degree, stable extension invariance\par
+\noindent $\bullet$ \S{}2.1 printed p.~5 after (2.2): hF=hB-(g/2)log\ensuremath{\pi }\par
+\noindent\textbf{scope}: Final definition/base-change paragraphs read, not a complete source audit of its cited semistable-reduction and N\'eron-model theorems.\par
 \paragraph{uniform existence}
 \medskip\noindent\textbf{uniform\_existence entry 1.}\par
-\noindent\textbf{author}: Jérôme Von Buhren\par
-\noindent\textbf{title}: Borne de hauteur semi-effective pour le problème de Mordell--Lang dans une variété abélienne\par
-\noindent\textbf{edition}: JTNB29(2017),307--320, final published\par
+\noindent\textbf{author}: J\'er\^ome Von Buhren\par
+\noindent\textbf{title}: Borne de hauteur semi-effective pour le probl\`eme de Mordell--Lang dans une vari\'et\'e ab\'elienne\par
+\noindent\textbf{edition}: JTNB 29(2017),307--320, final published\par
 \noindent\textbf{url}: \url{https://www.numdam.org/item/10.5802/jtnb.981.pdf}\par
 \noindent\textbf{doi}: 10.5802/jtnb.981\par
-\noindent\textbf{locator}: printed308 Theorem1.1, definition of C(Gamma,epsilon) and embedding(1.1)\par
-\noindent\textbf{distribution}: local read-only source; no third-party PDF copied into this packet\par
+\noindent\textbf{locator}: printed 308 Theorem 1.1, definition of \(C(\Gamma,\epsilon)\) and embedding (1.1)\par
+\noindent\textbf{distribution}: source identified by URL and locator; the full third-party PDF is not reproduced here\par
 \endgroup
 \clearpage\section{Public-source resolution and reproducibility}\label{q214:resolution}
-The historical path names in the retained author proofs are provenance locators.  The complete mathematical foundation they identify is present in Part~II, and the selected later proofs are present in Part~I.  The public reading aliases below resolve the retained historical locators; none requires private-repository access.  Exact file and passage bindings for the source packet remain in \nolinkurl{research/quartic214/SOURCE_PATH_MAP.json} and the application contracts.  They are not rewritten into current acceptance for this new manuscript.
+The historical path names in the retained author proofs are provenance locators.  The complete mathematical foundation they identify is present in Part~II, and the selected later proofs are present in Part~I.  The public reading aliases below resolve the retained historical locators; none requires private-repository access.  Exact file and passage bindings for the source packet remain in \nolinkurl{research/quartic214/SOURCE_PATH_MAP.json} and the application contracts.
 \begin{description}[style=nextline]
 \item[\nolinkurl{height/PROOF.md}] \nolinkurl{research/quartic214/proofs/height-supplier.md}
 \item[\nolinkurl{existence/PROOF.md}] \nolinkurl{research/quartic214/proofs/existence.md}
```

### H084

Class: status, source locator or provenance prose. Base 5216-5222; candidate 5193-5199.

```diff
@@ -5216,7 +5193,7 @@
 \item[\nolinkurl{brox-v17.tex}] \nolinkurl{research/quartic214/sources/evaluation-sections1-4.tex}
 \item[\nolinkurl{parent9-PROOF.md}] \nolinkurl{research/quartic214/sources/conductor-sections1-3.md}
 \item[\nolinkurl{cutoff-PROOF.md}] \nolinkurl{research/quartic214/sources/support-section1.md}
-\item[\nolinkurl{quartic214-protocol-d/PRIMARY_SOURCE_BRIDGES.md}] \nolinkurl{research/quartic214/proofs/primary-source-bridges.md}
+\item[Primary-source bridges] \nolinkurl{research/quartic214/proofs/primary-source-bridges.md}
 \item[\nolinkurl{quartic214-height-closure/ASSEMBLY.md}] \nolinkurl{research/quartic214/proofs/height-assembly.md}
 \item[\nolinkurl{HEIGHT_AVERAGING.md}] \nolinkurl{research/quartic214/proofs/height-averaging.md}
 \item[\nolinkurl{GEOMETRY_CARRY.md}] \nolinkurl{research/quartic214/proofs/geometry-carry.md}
```

### H085

Class: status, source locator or provenance prose. Base 5229-5235; candidate 5206-5212.

```diff
@@ -5229,7 +5206,7 @@
 \item[\nolinkurl{CONDUCTOR_INHERITED_PROFILES.json}] \nolinkurl{research/quartic214/sources/public-provider-scopes.json}
 \item[\nolinkurl{CONDUCTOR_RAMIFICATION_PROFILES.json}] \nolinkurl{research/quartic214/sources/public-provider-scopes.json}
 \end{description}
-\paragraph{Historical assembly procedure.} The command \nolinkurl{python3 -B research/quartic214-manuscript/assemble.py} was run from the repository root.  It read bounded source files and emitted the assembled TeX source and \nolinkurl{SOURCE_SPANS.json}, and performs no polynomial expansion or TeX build.  Its \nolinkurl{--check} mode verifies byte-for-byte deterministic output.  The separate PDF build and release metadata record the exact generated-source hash, toolchain and PDF hash.  The Version~18 draft is subsequently amended and its source and built PDF are identified separately. Source mapping and successful compilation concern serialization, not arithmetic acceptance.
+
 \clearpage\part{The mathematical foundation inherited from Version 16}
 \begin{quote}\small\textbf{Scope of retained foundation.} The following mathematical foundation is inherited from the upstream
 Version~16 source (SHA-256 \nolinkurl{aeb2b6a42a03943d7f8c46682389c8da693d2903ba92ccc164bbbd236451de74}),
```

### H086

Class: status, source locator or provenance prose. Base 5238-5244; candidate 5215-5221.

```diff
@@ -5238,7 +5215,7 @@
 The inverse-theorem conclusion is retained; its old local proof is replaced.
 The other inherited arguments are read with the source/application corrections
 identified in Section~\ref{q214:foundation-transition}.
-Assertions about $222$, $314$ and earlier variable counts refer to those constructions.  They do not replace the $214$ row specification in Part~I.  Historical review and incorporation statements belong to that upstream edition; they do not accept the newly assembled 214 manuscript.  Section, theorem, equation and cross-reference numbering in this part is restored to its original convention.\end{quote}
+Assertions about $222$, $314$ and earlier variable counts refer to those constructions.  They do not replace the $214$ row specification in Part~I.  Section, theorem, equation and cross-reference numbering in this part is restored to its original convention.\end{quote}
 \setcounter{section}{0}\setcounter{subsection}{0}\setcounter{equation}{0}\setcounter{theorem}{0}
 \renewcommand{\thesection}{\arabic{section}}\renewcommand{\theHsection}{foundation.\arabic{section}}
 \renewcommand{\theHequation}{foundation.\arabic{equation}}
```

### H087

Class: whitespace only. Base 5289-5299; candidate 5266-5276.

```diff
@@ -5289,11 +5266,11 @@
 \end{theorem}

 \begin{theorem}[The 222-variable family]\label{thm:v15-main}
-For $N\in\N$ let $A_N=149^{2N+1}$. Let $Q_{1,N},\ldots,Q_{196,N}$ and the positive integer weights $w_i$ be the expressions in Section~\ref{v222:equations}, in222 coordinates. Put $P_N=\sum_{i=1}^{196}w_iQ_{i,N}^2$. There is an integer $N_0$ such that, for every $N\ge N_0$ and $x\in\Q$,
+For $N\in\N$ let $A_N=149^{2N+1}$. Let $Q_{1,N},\ldots,Q_{196,N}$ and the positive integer weights $w_i$ be the expressions in Section~\ref{v222:equations}, in 222 coordinates. Put $P_N=\sum_{i=1}^{196}w_iQ_{i,N}^2$. There is an integer $N_0$ such that, for every $N\ge N_0$ and $x\in\Q$,
 \[
 x\in\Z\quad\Longleftrightarrow\quad\exists(z_2,\ldots,z_{222})\in\Q^{221}:P_N(x,z_2,\ldots,z_{222})=0.
 \]
-Every $P_N$ has degree four and content one. For $N\ge53$ it has2277 coordinate monomials and largest absolute coefficient $A_N^2+1=149^{4N+2}+1$. The defining threshold $N_0$ is ineffective; the coefficient calculation does not certify a particular defining member.
+Every $P_N$ has degree four and content one. For $N\ge53$ it has 2277 coordinate monomials and largest absolute coefficient $A_N^2+1=149^{4N+2}+1$. The defining threshold $N_0$ is ineffective; the coefficient calculation does not certify a particular defining member.
 \end{theorem}
 The additional222-variable reduction is proved in Sections~\ref{v222:construction}--\ref{v222:height}. The predecessor proof is given in the internal contact-height, aggregate-height, scalar, prime-selection and transformation sections culminating in Sections~\ref{v15x:reductions}--\ref{v15x:height}. The arithmetic foundation developed throughout this manuscript is reused there with its exact domains. The 248-variable starting construction is due to Jos\'e Brox; its new height argument, aggregate argument, and local construction are included here, rather than used as external black boxes. The 314-variable quartic is the other featured quartic. The large polynomial construction below supplies the original quantitative definition. Earlier quartic systems are retained as proof intermediates for the two featured quartics.

```

### H088

Class: status, source locator or provenance prose. Base 5341-5348; candidate 5318-5325.

```diff
@@ -5341,8 +5318,8 @@

 Version 10 clarified determinant specialization, the published
 prime-two Euler-system input, the local valuation deduction, and the
-identification of the saved templates, following the review in repository
-Issue~2. It also corrects and expands the historical attribution.
+identification of the saved templates.
+It also corrects and expands the historical attribution.
 The polynomial specifications and numerical bounds are unchanged.
 We thank \texttt{manvirjaswal} for the detailed review
 \footnote{\url{https://github.com/elliotglazer/diophantine-z-q/issues/2}}.
```

### H089

Class: status, source locator or provenance prose. Base 13565-13571; candidate 13542-13548.

```diff
@@ -13565,7 +13542,7 @@
 with $r\Lambda_n\subset\Lambda$ and equality at $11$.
 The Hodge-lattice equivalence turns $r\,\mathrm{id}_V$ into a
 $B$-linear isogeny from the translated
-surface to the original one, of degree prime to $11$. The accepted
+surface to the original one, of degree prime to $11$. The retained
 integral-lattice identification retains the actual $\mathcal O$-labels;
 changes of the full-three marking are $\mathcal O$-linear isomorphisms.
 The two-surface Hom argument places these maps over the same $L$.
```

### H090

Class: status, source locator or provenance prose. Base 14669-14675; candidate 14646-14652.

```diff
@@ -14669,7 +14646,7 @@
 In this calculation $H=H_*$ is the constant in Theorem~\ref{hyp:o8-height}.

 The anchor gives $|n|\ge3^{2^{23}-1}$. Conditional only on the separately
-audited original height bound $\log_2H<4783227$, it follows that
+stated original height bound $\log_2H<4783227$, it follows that
 $|n|>(20H)^2$. Indeed $\log_2 3>3/2$ and $\log_2 20<5$, and
 \[
  3(2^{23}-1)=25165821
```

### H091

Class: status, source locator or provenance prose. Base 15430-15436; candidate 15407-15413.

```diff
@@ -15430,7 +15407,7 @@
 restriction of $q$ is surjective. Poincare reducibility makes $A_f$
 a $\mathbb Q$-isogeny factor of $J_H$.

-The accepted realization of $r_\ell$ in $A_f$ puts it in $V_\ell(J_H)$.
+The realization of $r_\ell$ in $A_f$ puts it in $V_\ell(J_H)$.
 Over $L'$, Faltings' Hom theorem and extension of scalars give a nonzero
 homomorphism $A\to J_H$. Absolute simplicity and Poincare reducibility
 give an $L'$-isogeny $A\times Z\to J_H$. In particular
```

### H092

Class: status, source locator or provenance prose. Base 18135-18144; candidate 18112-18121.

```diff
@@ -18135,10 +18112,10 @@
 $\log_2(64\mathsf S^2)<6+(8/5)2^{28}<429496736$ because $3^5<2^8$.
 \end{proof}

-The frozen package includes the builder, raw systems, all $904$ gate
+The package includes the builder, raw systems, all $904$ gate
 definitions, the exact elimination and normalization certificate,
 compact coordinate map, final residuals, complete coefficient table,
-source-equivalence proofs and independent reviews. Its manifest has
+source-equivalence proofs. Its manifest has
 SHA-256
 \begin{center}\small
 \nolinkurl{36fca72cb0eb126193ffa43d890ff09d5e29cbf1274561d2632ed1e227163787}.
```

### H093

Class: status, source locator or provenance prose. Base 18662-18668; candidate 18639-18645.

```diff
@@ -18662,7 +18639,7 @@
 The released specification, natural precision polynomial and construction
 files are identified in \nolinkurl{construction/SOURCE_MANIFEST.json}.
 For the selected supporting proof arguments, see
-\href{https://github.com/elliotglazer/diophantine-z-q/blob/005b17abfbefd8bee7b34f3bbe8f5aabf872eb1f/research/version14/SUPPORTING-NOTES.md}{the supporting-note index}. A source identity is not a proof verdict.
+\href{https://github.com/elliotglazer/diophantine-z-q/blob/005b17abfbefd8bee7b34f3bbe8f5aabf872eb1f/research/version14/SUPPORTING-NOTES.md}{the supporting-note index}. These source identities do not by themselves establish the mathematical conclusions.

 % End 06-literal-construction.tex

```

### H094

Class: prose, notation or text-conversion cleanup; inspect both sides. Base 19195-19201; candidate 19172-19178.

```diff
@@ -19195,7 +19172,7 @@

 We also account for the difference between the two published
 cohomology conventions. Write $C_j$ for the $j_*$ Iwasawa complex of
-\cite[Sections 8.2 and 12.2]{kato}, and $C_S$ for \emph{étale}
+\cite[Sections 8.2 and 12.2]{kato}, and $C_S$ for \emph{\'etale}
 cochains on the open arithmetic scheme obtained by inverting $2$
 and every odd prime in the actual ramification support $S$,
 including the fixed twist, as in \cite[Sections 0.1 and 0.5]{kato1999}.
```

### H095

Class: status, source locator or provenance prose. Base 26655-26663; candidate 26632-26640.

```diff
@@ -26655,9 +26632,9 @@
 \]
 These witnesses have unique rational values and $c_{16}=S_0$. Substitution for $S_0$ leaves every residual quadratic. Direct expansion gives the 3,247-bit maximum coefficient bound.

-The accompanying archive contains the complete polynomial tables, residual systems, coordinate maps, elimination certificates, pinned source generators, arithmetic notes and independent checkers. Each final package has a standard-library-only \texttt{verify\_all.py}. It replays all eliminations, verifies the unique constant lift, independently expands the sums of squares, and compares every coefficient. Both full packages have passed fresh independent runs. A separate source replay rebuilds the two compiled precursors and checks the match to their frozen residual systems.
+The accompanying archive contains the complete polynomial tables, residual systems, coordinate maps, elimination certificates, pinned source generators, arithmetic notes and independent checkers. Each final package has a standard-library-only \texttt{verify\_all.py}. It replays all eliminations, verifies the unique constant lift, independently expands the sums of squares, and compares every coefficient. A separate source replay rebuilds the two compiled precursors and checks the match to their frozen residual systems.

-These finite checks certify the counts, degrees and stated algebraic transformations. The arithmetic assertions in Sections~\ref{v9:sec:height}--\ref{v9:sec:depth} received separate adversarial AI review; they have not received independent human peer review or a complete formal proof check. The inherited arithmetic inputs are the results of this manuscript identified in Section~\ref{subsec:v9-inputs}; no theorem from the contribution archive is assumed as an additional arithmetic input.
+These finite checks certify the counts, degrees and stated algebraic transformations. The inherited arithmetic inputs are the results of this manuscript identified in Section~\ref{subsec:v9-inputs}; no theorem from the contribution archive is assumed as an additional arithmetic input.



```

### H096

Class: whitespace only. Base 27760-27770; candidate 27737-27747.

```diff
@@ -27760,11 +27737,11 @@

 At an unramified place above $p>76176$, a nonidentity formal point of
 depth $r=v(z)\ge1$ has $v(Df^2)=4r$. All coefficient denominators
-above are supported at primes at most37. Consequently
+above are supported at primes at most 37. Consequently
 $v(\mathcal R-G_9)\ge40r$. The earlier full-tail estimate gives
 $v(\log_E(Q)-z\mathcal R(Df^2))\ge41r$.
 The point $O$ has exact zero error. We retain the $G_2$ numerator at
-$V_1$, of relative precision12, and use $\mathcal R$ at $V_0,V_2,V_3,V_4$.
+$V_1$, of relative precision 12, and use $\mathcal R$ at $V_0,V_2,V_3,V_4$.

 Set $\ell_0=z(V_0)\mathcal R(Df(V_0)^2)$ and define
 \[
```

### H097

Class: whitespace only. Base 27773-27780; candidate 27750-27757.

```diff
@@ -27773,8 +27750,8 @@
  L'_i=\overline{z(V_i)\mathcal R(Df(V_i)^2)/\ell_0}\quad(i>1).
 \]
 The nonzero denominator is proved below, before these quotients are used.
-The tests have orders1 on $f(U_i)$ and $\overline{f(V_i)}$, order40
-on $f(H)$, order10 on $L_1-L'_1,L_1-\beta$, and order40 on the other
+The tests have orders 1 on $f(U_i)$ and $\overline{f(V_i)}$, order 40
+on $f(H)$, order 10 on $L_1-L'_1,L_1-\beta$, and order 40 on the other
 three cross-tests and
 \[
  F(L_2,L_3,L_4),\qquad F(A,T,B)=T^2-A(A-2)TB+(A-2)^2B^2-1.
```

### H098

Class: whitespace only. Base 27784-27798; candidate 27761-27775.

```diff
@@ -27784,15 +27761,15 @@
 For completeness, spell out the zero-safe local argument. Let $A(Q)$ be
 the analytic unit defined by $\log_E(Q)=z(Q)A(Q)$, with $A(O)=1$.
 Define $T_2=G_2/A$ and $T_{40}=\mathcal R/A$ by their power series.
-These units equal1 at $O$. Their errors at nonidentity formal points
+These units equal 1 at $O$. Their errors at nonidentity formal points
 have the stated orders. The primary ratio is exactly
 $(u_i/h)A(H)/A(U_i)$, also when $u_i=0$. The alternate ratio is
 $(u_i-n_i)/(h-1)$ times the corresponding conjugated unit ratio.
 At least one of $h,h-1$ is a $p$-unit. Therefore one full ratio is
 integral, and the positive-order cross-test transfers integrality to
-both approximate and full ratios. Only now infer depth at least20 for
+both approximate and full ratios. Only now infer depth at least 20 for
 a nonzero $U_i$; if $U_i=O$, its error is zero. The primary error has
-order80. Multiplication by $h,h-1$ and subtraction give
+order 80. Multiplication by $h,h-1$ and subtraction give
 \[
  L_1\equiv n\pmod{p^{10}},\qquad L_i\equiv n_i\pmod{p^{40}} (i>1).
 \]
```

### H099

Class: whitespace only. Base 27895-27901; candidate 27872-27878.

```diff
@@ -27895,7 +27872,7 @@
 \]
 is a unit at every consumed place over $p>76176$. The one-place detector
 lemma would force its order-forty test at any contact prime, a contradiction.
-Thus all three contact radicals equal1. Equation~\eqref{eq:v13-height}
+Thus all three contact radicals equal 1. Equation~\eqref{eq:v13-height}
 with $N=1$ gives $B^2-6<7\mathcal H$, contrary to
 $B\ge|a|>(40\mathcal H)^{10}$ from the unchanged anchor.
 This argument precedes every interpretation of an LP quotient.
```

### H100

Class: whitespace only. Base 27990-28000; candidate 27967-27977.

```diff
@@ -27990,11 +27967,11 @@
 Each of these abscissae and its inverse is integral outside
 $\{2,3,7,17,41\}$. The same is true for the nonzero torsion
 abscissae, and negating P changes none of these abscissae. Thus
-f(H) is a unit at every consumed place. The retained order40 f(H)
+f(H) is a unit at every consumed place. The retained order 40 f(H)
 test would then rule out every contact prime. All three radicals
-would equal1, contradicting the root-height bound and scalar anchor
+would equal 1, contradicting the root-height bound and scalar anchor
 exactly as in the preceding V0 exclusion. This proof needs no
-ratio involving H. Consequently m is neither0 nor2, H and H-P are
+ratio involving H. Consequently m is neither 0 nor 2, H and H-P are
 nontorsion, S is nonzero, and H is neither P nor -P.

 In the rescaled difference equations put
```

### H101

Class: whitespace only. Base 28018-28028; candidate 27995-28005.

```diff
@@ -28018,11 +27995,11 @@

 The old positivity interval for the rational logarithm is no longer
 enough. A stronger certificate is available: N(w) above has no root
-modulo71, and Q(w) has no root modulo7. At the respective prime all
+modulo 71, and Q(w) has no root modulo 7. At the respective prime all
 coefficients are integral and the leading coefficient is a unit.
 These assertions are finite substitutions through all residues. Both
-primes split in K, with square roots of2 equal to12,59 modulo71
-and3,4 modulo7. A K-root would give a local root, necessarily integral,
+primes split in K, with square roots of 2 equal to 12,59 modulo 71
+and 3,4 modulo 7. A K-root would give a local root, necessarily integral,
 and then a forbidden residue root. Hence N and Q never vanish in K.
 The actual equation $T'\ell_0+a_*N\mathcal R(Df(V_0)^2)=0$
 therefore implies $\ell_0\ne0$ and gives the correct denominator
```

### H102

Class: whitespace only. Base 28035-28041; candidate 28012-28018.

```diff
@@ -28035,7 +28012,7 @@
 \]
 They kill T. Applying the formal logarithm only to formal points
 gives ratios $u_i/h$ and $(u_i-n_i)/(h-1)$. At every consumed odd
-prime h and h-1 are integral and differ by1. The earlier transfer
+prime h and h-1 are integral and differ by 1. The earlier transfer
 and subtraction proof therefore applies, including zero numerators.
 At opposite split places use the same conjugation as before; at an
 inert place it preserves the valuation.
```

### H103

Class: whitespace only. Base 28046-28052; candidate 28023-28029.

```diff
@@ -28046,7 +28023,7 @@
 \]
 If the scalar coefficient test has depth $d_s$, formal logarithm
 isometry gives $v_p(s/(m/2))\ge d_s$. Since m/2 is p-integral,
-$v_p(s)\ge d_s$. This includes the selected depth24. The proof
+$v_p(s)\ge d_s$. This includes the selected depth 24. The proof
 that 2R is formal when R is near O or (0,0) is unchanged. Thus
 both the comparison and scalar height arguments survive the larger
 domain. Completeness uses the original H in $2E(K)$ and forgets its
```

### H104

Class: whitespace only. Base 28072-28104; candidate 28049-28081.

```diff
@@ -28072,33 +28049,33 @@
 At a consumed prime $p>76176$, $51$ is a unit. A negative valuation
 of $\beta$ is $2v_p(\tau)$, hence even. The five contact factors then
 have the same valuation, so an odd valuation of $r$ must be positive.
-This argument makes no assertion at the exceptional primes3 and17.
+This argument makes no assertion at the exceptional primes 3 and 17.

 For integral $X$ the following simultaneous local calculation holds.
 Since $\tau$ is odd, $\beta\equiv3\pmod8$; the two even contact
-factors each have valuation one and equal odd parts modulo8. The
-other factors have residues3,7,5. Therefore $v_2(r)=2$ and
-$r/4\equiv1\pmod8$. At3, $\beta\equiv2$ and the first four factors
-have product1 modulo3. Furthermore
+factors each have valuation one and equal odd parts modulo 8. The
+other factors have residues 3,7,5. Therefore $v_2(r)=2$ and
+$r/4\equiv1\pmod8$. At 3, $\beta\equiv2$ and the first four factors
+have product 1 modulo 3. Furthermore
 \[
  (2\beta-1)/3=34\tau^2+1669\equiv1+\tau^2\pmod3,
 \]
-which is nonzero. Thus $v_3(r)=1$. At17, the contact residues are
-5,4,1,10,9 with product15, a nonzero square. Thus $v_{17}(r)=0$.
+which is nonzero. Thus $v_3(r)=1$. At 17, the contact residues are
+5,4,1,10,9 with product 15, a nonzero square. Thus $v_{17}(r)=0$.

 An intermediate one-choice construction used $c=33033$ when
-$3\mid\tau$ and $c=33$ otherwise. Both are square units at2 and17,
-and their unit parts at3 are respectively1 and2, correcting the two
+$3\mid\tau$ and $c=33$ otherwise. Both are square units at 2 and 17,
+and their unit parts at 3 are respectively 1 and 2, correcting the two
 possible classes of $r$. The selected construction removes even
 this choice and sets
 \[
                  c=r+4896,\qquad4896=2^5\cdot3^2\cdot17.
 \]
-At2 the quotient $c/r=1+4896/r$ belongs to $1+8\mathbb Z_2$;
-at3 and17 it belongs to $1+p\mathbb Z_p$. Hence $cr$ is a square
+At 2 the quotient $c/r=1+4896/r$ belongs to $1+8\mathbb Z_2$;
+at 3 and 17 it belongs to $1+p\mathbb Z_p$. Hence $cr$ is a square
 in all three local fields. Also $c,r$ are positive integers.
 At a consumed scalar contact prime, positivity of the odd valuation
-$v_p(r)$ was proved before using $c$; since4896 is a unit there,
+$v_p(r)$ was proved before using $c$; since 4896 is a unit there,
 $c$ is a unit there too. We do not assert that $c$ is a unit at
 \emph{every} large prime. Its additional finite prime support is
 included in the preparation before the continuity modulus is chosen.
```

### H105

Class: whitespace only. Base 28154-28160; candidate 28131-28137.

```diff
@@ -28154,7 +28131,7 @@
  v_p(B_s)>63\eta/4,\quad v_p(q)>61\eta/4,\quad
  v_p(z_0)>191\eta/8,\quad v_p(z_1)>187\eta/8.
 \]
-Thus both rational coefficient valuations are at least24.
+Thus both rational coefficient valuations are at least 24.
 Positive valuation of the norm supplies a place with $v(f(H))>0$;
 there $H$ is formal and $v(z(R)/z(H))\ge24$.
 Small $z(R)$ alone does not imply that $R$ is formal. If $e=v(x(R))$,
```

### H106

Class: whitespace only. Base 28197-28227; candidate 28174-28204.

```diff
@@ -28197,31 +28174,31 @@

 \subsection{The two final height contradictions}
 The local order-forty tests force the contact radicals to divide
-$F=t^2-a(a-2)tb+(a-2)^2b^2-1$ to order40.
+$F=t^2-a(a-2)tb+(a-2)^2b^2-1$ to order 40.
 If $F\ne0$, then $|F|<5B^4$ and~\eqref{eq:v13-height} contradicts
 the retained lower bound $B\ge|a|>(40\mathcal H)^{10}$.
 Thus $F=0$. The nonzero odd root label $b$ and the retained Lucas lemma
 give $\log B>|a|-3$.
 If $n\ne\beta$, its nonzero reduced numerator $N$ satisfies
 $|N|\le2e^{\operatorname h(\beta)}B$ and is divisible by the three
-contact radicals to order10. Since $B^2-6>(5/8)B^2$ for $B>4$,
+contact radicals to order 10. Since $B^2-6>(5/8)B^2$ for $B>4$,
 \[
  B^{1/10}<48\mathcal H e^{(19/10)\operatorname h(\beta)},\qquad
  \log B<10\log(48\mathcal H)+19\operatorname h(\beta)
           <29|a|/40<|a|-3.
 \]
 This contradiction proves $n=\beta$. The unchanged root chart makes $n$ odd, so the parity-sensitive input argument above gives $X\in\mathbb Z$.
-The first contradiction uses order40; lowering only the scalar depth
+The first contradiction uses order 40; lowering only the scalar depth
 does not weaken that test.

 \subsection{Polynomial circuit reductions}
 For retained field values $Y_i$, each order block evaluates
-$\prod_i(1+qY_i)$. In order1 group the nine factors as
+$\prod_i(1+qY_i)$. In order 1 group the nine factors as
 \[
  [V_0,U_1,U_2],\quad[V_1,U_3,U_4],\quad[V_2,V_3,V_4],
 \]
 where labels denote the squared test values with their existing
-conjugations. Order10 uses its pair; order40 retains its pair and
+conjugations. Order 10 uses its pair; order 40 retains its pair and
 triple. For a triple $a,b,c$ the polynomial is
 \[
  1+q(a+b+c)+q^2(ab+ac+bc)+q^3abc.
```

### H107

Class: whitespace only. Base 28321-28334; candidate 28298-28311.

```diff
@@ -28321,14 +28298,14 @@
 Choose a multiple $M$ of $64m_0$ whose multiples give all desired formal
 depths at primes in $S=\operatorname{supp}(cr)\cup\{2,3,17\}$.
 In particular require coefficient depth $8\eta$ for $f(H)$ when
-$\eta=v_p(r)>0$, and positive coefficient depth at17. Density permits
+$\eta=v_p(r)>0$, and positive coefficient depth at 17. Density permits
 $H_0=[h_0]P$, $h_0>0$, $M\mid h_0$, as close to the two real identities
 as needed to make $q(H_0)^2/r^{31}$ arbitrarily small.
 Its real $z$ values are nonzero.

 With $H_0$ fixed, choose a multiple $N_0$ of $6m_0$ imposing the anchor
 and all required scalar finite depths. At $p\mid r$ require coefficient
-depth $24\eta$ for $z(R)/z(H_0)$; impose positive depths also at17 and
+depth $24\eta$ for $z(R)/z(H_0)$; impose positive depths also at 17 and
 at primes dividing $c$ but not $r$. The formal subgroups have finite
 index, so arbitrary further depths can be imposed this way. Density of
 the positive progression $s\equiv0\pmod{N_0}$ permits $s$ arbitrarily
```

### H108

Class: whitespace only. Base 28343-28351; candidate 28320-28328.

```diff
@@ -28343,9 +28320,9 @@
 support $v_p(\mathfrak b)=2v_p(W)$, so the reduced denominator of
 $\mathfrak b$ is a square. Its squareclasses at $2,3,17$ are those of
 $cr$. Since $v_2(cr)=4$, $v_3(cr)=2$, the first two required bounds
-hold. At17 both $r,c$ are units; the separately imposed depths give
+hold. At 17 both $r,c$ are units; the separately imposed depths give
 $v_{17}(q),v_{17}(B)\ge2$, hence $v_{17}(W)\ge4$ and
-$v_{17}(\mathfrak b)\ge8$. Inclusion of17 does not depend on it
+$v_{17}(\mathfrak b)\ge8$. Inclusion of 17 does not depend on it
 belonging to the support of $cr$.

 Keep $R$ fixed. A nonempty real neighborhood $U\subset G^0$ of $H_0$
```

### H109

Class: status, source locator or provenance prose. Base 28398-28411; candidate 28375-28388.

```diff
@@ -28398,14 +28375,14 @@
 and discard the preparation-square slot $n$, setting it equal to $x^2$.
 Every one of the five remaining pole residuals is then $x^2$ times
 its new residual. For example the first conic and the h equation have
-respectively their $ex$ and $x^2$ terms replaced by $e$ and1, and
+respectively their $ex$ and $x^2$ terms replaced by $e$ and 1, and
 \[
  17ex+Ken-17hv=0
        \quad\longmapsto\quad 17e+Kxe-17hv=0.
 \]
 The square rows remain $p_2=p^2$, $q_2=q^2$, and the factored
 second-conic coefficient list is unchanged. In the physical indexing
-of the reviewed component, the weight-one slots are
+of the specified component, the weight-one slots are
 $51,52,53,54,532$, the weight-two slots are $527,534$, and $531$ is n.
 These are implementation indices, not mathematical constants.

```

### H110

Class: whitespace only. Base 28438-28447; candidate 28415-28424.

```diff
@@ -28438,10 +28415,10 @@
 \]
 Its hypotheses contain no anchor equation. Indeed
 $z(2P)/3\equiv2+\rho\pmod3$; multiplication by units and then by
-powers of3 in the integral formal group preserve the stated leading
+powers of 3 in the integral formal group preserve the stated leading
 term. The curve equation makes the leading residue of
 $f/3^{2+2v_3(s)}$ a nonzero rational multiple of $\rho$.
-Independence of1 and $\rho$ in the residue field proves the displayed
+Independence of 1 and $\rho$ in the residue field proves the displayed
 coefficient valuation, also for negative s. Consequently
 $F=f_1([s]P)=2g_0g_1\ne0$, in particular $g_1\ne0$.
 This is the noncircular justification for restoring the old inverse.
```

### H111

Class: status, source locator or provenance prose. Base 28529-28535; candidate 28506-28512.

```diff
@@ -28529,7 +28506,7 @@
 residual lists, coordinate maps and exact maximum coefficients specify
 the two polynomials independently of their factored construction.

-% Isolated Version 14 author draft; assembled independent review is required.
+% Historical Version 14 author draft.
 % This file does not modify the original polynomial or Version 13.
 \section{A quartic presentation with 299 variables}\label{sec:v14}

```

### H112

Class: whitespace only. Base 28655-28661; candidate 28632-28638.

```diff
@@ -28655,7 +28632,7 @@
  v=\frac{-36+16\rho}{49}.
 \]
 These are units at every place above $p>76176$:
-$c_*+b_*=12-8\rho$ has norm16 and
+$c_*+b_*=12-8\rho$ has norm 16 and
 $c_*-b_*=(9+4\rho)/4$ has norm$49/16$.
 Section~\ref{subsec:v14-groups} excludes these branches by their
 unchanged $V_0$ unit leaf and the pre-H height/anchor contradiction.
```

### H113

Class: whitespace only. Base 28694-28714; candidate 28671-28691.

```diff
@@ -28694,21 +28671,21 @@
  \begin{cases}0&n\text{ odd},\\-2-2v_3(n)&n\text{ even},\end{cases}
  \qquad v_2(X_n)=-1\quad(n\text{ odd}).
 \end{equation}
-At3 the reduction of $P$ is $(\rho,0)$ over $\mathbb F_9$,
+At 3 the reduction of $P$ is $(\rho,0)$ over $\mathbb F_9$,
 which proves the odd case. For $n=2\cdot3^ku$, $u$ a3-unit,
 the formal expansion gives
 $z([n]P)/3^{k+1}\equiv u(2+\rho)\pmod3$.
 Since $x(z)=z^{-2}+O(z^2)$ and
 $(2+\rho)^{-2}=3/2-\rho\equiv2\rho\pmod3$, the scaled
-abscissa has nonzero imaginary coefficient modulo3. This proves
+abscissa has nonzero imaginary coefficient modulo 3. This proves
 the even case and $X_n\ne0$.
-At2, $z(P)=(232+86\rho)/357$ has component valuations3 and1.
+At 2, $z(P)=(232+86\rho)/357$ has component valuations 3 and 1.
 The integral odd multiplication series preserves these values:
 its error has field valuation at least$9/2$ when $v(2)=1$.
 For $z=A+B\rho$ with those valuations the imaginary coefficient
 of $z^{-2}$ is $-2AB/(A^2-2B^2)^2$, of valuation$-1$.
 The Laurent correction has larger valuation. This uses integral
-formal coefficients, not good reduction at2.
+formal coefficients, not good reduction at 2.

 The retained scalar-coefficient lemma gives $v_3(F_n)=0$ for odd
 $n$, $2+2v_3(n)$ for even nonzero $n$, and dyadic integrality.
```

### H114

Class: whitespace only. Base 28721-28733; candidate 28698-28710.

```diff
@@ -28721,13 +28698,13 @@
  u^2+6v_a^2-2w_a^2-4Cw_a-3T^2=0.
 \end{equation}
 The inherited quaternion criterion, including parameter zero,
-supplies rational witnesses exactly when $T/C$ is integral at2
-and3. Its3-integrality forces all three summands in $F_s/C+q$
+supplies rational witnesses exactly when $T/C$ is integral at 2
+and 3. Its3-integrality forces all three summands in $F_s/C+q$
 to be3-integral. Their possible finite valuations lie in the
 disjoint classes $2\mathbb Z$, $1+4\mathbb Z$, $3+4\mathbb Z$;
-the binary sum uses anisotropy modulo3 and~\eqref{eq:v14-X}.
-A negative minimum cannot cancel. Thus $X_A,X_T,X_Z$ are3-units,
-so the three root labels are odd. Also $F_s/C$ is3-integral
+the binary sum uses anisotropy modulo 3 and~\eqref{eq:v14-X}.
+A negative minimum cannot cancel. Thus $X_A,X_T,X_Z$ are 3-units,
+so the three root labels are odd. Also $F_s/C$ is 3-integral
 and is dyadically integral by the scalar lemma. The old unshifted
 anchor can therefore be restored with new private witnesses
 before H or height. An odd $s$ would make $F_s$ a3-unit,
```

### H115

Class: whitespace only. Base 28750-28756; candidate 28727-28733.

```diff
@@ -28750,7 +28727,7 @@
 points, $F_s$, all detector values and the private unscaled anchor
 witnesses. The scalar rows change at most by an overall sign.

-Conversely the old odd roots make $q$ integral at2 and3 by
+Conversely the old odd roots make $q$ integral at 2 and 3 by
 \eqref{eq:v14-X}, so the same quaternion criterion supplies the
 shifted anchor. No prime or H choice changes. The exact private
 unscaling used here multiplies the old anchor witnesses and its
```

### H116

Class: whitespace only. Base 28853-28859; candidate 28830-28836.

```diff
@@ -28853,7 +28830,7 @@
 $h^2=f(1-Df^2)$, a nonzero $f$ has even valuation: the leading
 valuation is $v(f)$ when positive and $3v(f)$ when negative.
 Zero leaves are omitted. Thus the relevant powers have
-periods4,8,16 before formality or logarithms. In the generic
+periods 4,8,16 before formality or logarithms. In the generic
 squared-H branch its algebraic reconstruction gives the same
 curve fact; its exceptional branches have the fixed signed
 values already classified. Other high and middle tests are
```

### H117

Class: whitespace only. Base 28869-28875; candidate 28846-28852.

```diff
@@ -28869,7 +28846,7 @@
  \end{array}
 \]
 All gamma exponents are divisible by the relevant periods.
-Within each row the classes modulo16 are disjoint and exclude
+Within each row the classes modulo 16 are disjoint and exclude
 zero for every odd $\alpha$. Every group therefore has a unique
 minimum valuation, is nonzero, and has valuation at most zero.
 This covers arbitrary $c_\gamma$ and every zero-leaf pattern.
```

### H118

Class: whitespace only. Base 28891-28898; candidate 28868-28875.

```diff
@@ -28891,8 +28868,8 @@
  4v(H_i)>160c_\gamma-(r+1/2)\alpha,\qquad
  4v(M_i)>40c_\gamma-(r+1/2)\alpha\quad(r=1\text{ or }2).
 \]
-For $\alpha=1$ the worst bounds are157.5 and37.5; for
-$\alpha=3$ they are312.5 and72.5; for $\alpha\geq5$ they
+For $\alpha=1$ the worst bounds are 157.5 and 37.5; for
+$\alpha=3$ they are 312.5 and 72.5; for $\alpha\geq5$ they
 exceed$72.5\alpha$ and$16.25\alpha$. Thus $v(H_i)\geq40$
 and $v(M_i)\geq10$. The primary bounds are
 \[
```

### H119

Class: whitespace only. Base 28902-28908; candidate 28879-28885.

```diff
@@ -28902,7 +28879,7 @@
  4v(f(U_4))&>80c_\gamma+3.5\alpha.
  \end{split}
 \]
-Using even valuations, these give respectively40,20,22 for the
+Using even valuations, these give respectively 40,20,22 for the
 reciprocal depths. The other low terms force positive valuation
 of every required nonzero primary or alternate reciprocal value.

```

### H120

Class: whitespace only. Base 28914-28920; candidate 28891-28897.

```diff
@@ -28914,7 +28891,7 @@
 from Section~\ref{sec:v13} then restore the full H/V0 domain
 before logarithms. Here their required hypothesis is only
 positive valuation of $f(H)$, rather than the former stronger
-order40 test. A nonidentity torsion value of H, or a value
+order 40 test. A nonidentity torsion value of H, or a value
 in either of the fixed translates $\pm P+E[2](K)$, has the
 same fixed unit obstruction used there at every consumed
 large prime. The new term $EU$, where $U=f(H)^2$ after
```

### H121

Class: whitespace only. Base 29099-29118; candidate 29076-29095.

```diff
@@ -29099,20 +29076,20 @@
 the common place. Their retained Lucas test has positive
 valuation and its value at $(0,0,0)$ is $-1$. At least one of
 these three $L_i$ is therefore a unit. The primary bounds proved
-above give formal depth at least10 for its point $U_i$.
-The exact identity $z(U_i)=L_i z(H)$ then gives depth at least10
+above give formal depth at least 10 for its point $U_i$.
+The exact identity $z(U_i)=L_i z(H)$ then gives depth at least 10
 for $H$. All integral primary $L_i$ give the same depth for
 every nonidentity primary point.

-This bootstrap precedes the order40 estimate. At depth10 the
-relative primary logarithm error has valuation at least40.
-The alternate estimates have order40 for the degree-nine
-approximants and order12 for the middle approximants. Their
+This bootstrap precedes the order 40 estimate. At depth 10 the
+relative primary logarithm error has valuation at least 40.
+The alternate estimates have order 40 for the degree-nine
+approximants and order 12 for the middle approximants. Their
 denominators are units at the consumed place. Since the full
 ratios are integral, these relative errors are also absolute
 errors. Multiplying the two ratios by $h_0$ and $h_0-1$ and
 subtracting gives the retained congruences to the integer root
-labels $n_i$, with their required orders10 or40.
+labels $n_i$, with their required orders 10 or 40.
 No assertion that the global auxiliary labels $u_i$ are integers
 is used.

```

### H122

Class: whitespace only. Base 29127-29133; candidate 29104-29110.

```diff
@@ -29127,7 +29104,7 @@
 Q(w):\;&1,-1526/1073,513/1073 .
 \end{split}
 \]
-The unchanged certificates modulo71 for $N$ and modulo7 for $Q$
+The unchanged certificates modulo 71 for $N$ and modulo 7 for $Q$
 apply to every element of $K$. Both primes split in $K$; the
 respective coefficients are integral, with unit leading
 coefficient, and their reductions have no root. A root with
```

### H123

Class: whitespace only. Base 29140-29146; candidate 29117-29123.

```diff
@@ -29140,7 +29117,7 @@
 now be applied with their original inputs. The roots are the
 same odd integer multiples, the congruences have the required
 precision, the scalar point has the orientation
-in~\eqref{eq:v14-S-orientation}, and the scalar depth24 transfer
+in~\eqref{eq:v14-S-orientation}, and the scalar depth 24 transfer
 is unchanged. They conclude that the distinguished input is
 an integer. This proves soundness of the changed arithmetic
 certificates.
```

### H124

Class: whitespace only. Base 29150-29166; candidate 29127-29143.

```diff
@@ -29150,17 +29127,17 @@
 We check that a single choice of witnesses meets all the new
 tests. Start with the original simultaneous construction for
 an integer input, with the same positive progression and the
-same contact-prime restrictions. Use its depth19 preparation.
-The resulting primary formal depths are at least20, the high
-tests have valuation at least40, and the middle tests have
-valuation at least12. The fixed H/V0 exclusions remain part of
+same contact-prime restrictions. Use its depth 19 preparation.
+The resulting primary formal depths are at least 20, the high
+tests have valuation at least 40, and the middle tests have
+valuation at least 12. The fixed H/V0 exclusions remain part of
 this construction.

 At each contact prime $\alpha=v(R)=1$. Prescribe $v(\gamma)=1$.
-In the three groups the high-term valuations are at least1
-or2 and the middle-term valuations at least9 or10. The primary
-terms have lower bounds159,3,83,76 in root order; the guard has
-lower bound8. The alternate low terms are unchanged and have
+In the three groups the high-term valuations are at least 1
+or 2 and the middle-term valuations at least 9 or 10. The primary
+terms have lower bounds 159,3,83,76 in root order; the guard has
+lower bound 8. The alternate low terms are unchanged and have
 positive valuation. Every group is therefore one plus an
 element of the maximal ideal at the successful place.
 At the other place above a split contact prime, the inverse
```

### H125

Class: whitespace only. Base 29245-29275; candidate 29222-29252.

```diff
@@ -29245,31 +29222,31 @@
 \[
  q=3(2X_A)^2+3(2X_T)^2+27(2X_Z)^2\equiv1\pmod8.
 \]
-The shifted anchor therefore has $t=T/C$ odd at2 and integral
-at3. The retained quaternion criterion supplies one rational
+The shifted anchor therefore has $t=T/C$ odd at 2 and integral
+at 3. The retained quaternion criterion supplies one rational
 point $P$ on~\eqref{eq:v14-anchor-quadric}.
 Fix it before choosing the contact primes.

 The required local sets on this quadric are nonempty. Choose
 $\nu_2,\nu_{17}\geq1$ and
 $\nu_3>v_3(C)=2^{25}$, enlarged to meet all earlier preparation
-bounds. At2 take
+bounds. At 2 take
 \[
  u=2^{\nu_2},\qquad v=T/2,\qquad
  z=(C/2)\sqrt{4-3t^2+2(u/C)^2}.
 \]
-The radicand is one modulo8. At3 take
+The radicand is one modulo 8. At 3 take
 \[
  u=3^{\nu_3},\quad v=0,\quad
  z=C\sqrt{1-3t^2/2+(u/C)^2/2};
 \]
-the radicand is one modulo3. At17 take
+the radicand is one modulo 3. At 17 take
 \[
  u=17^{\nu_{17}},\quad v=T/\sqrt2,\quad
  z=C\sqrt{1+u^2/(2C^2)}.
 \]
 Here2 is a square in $\mathbb Q_{17}$ and the last radicand
-is one modulo17. Each construction solves the quadric exactly.
+is one modulo 17. Each construction solves the quadric exactly.

 At a contact prime $p>76176$ exclude the finitely many
 denominator primes of $T$, and prescribe $u=p^{-1}$.
```

### H126

Class: whitespace only. Base 29277-29283; candidate 29254-29260.

```diff
@@ -29277,7 +29254,7 @@
 $6V^2-2Z^2=p^2N-1$.
 Modulo $p$ the right side is $-1$. The binary form
 $Z^2-3V^2$ represents every nonzero residue: it is a split
-product if3 is a square and a surjective finite-field norm
+product if 3 is a square and a surjective finite-field norm
 otherwise. The resulting solution is nonsingular, so Hensel
 lifting gives the desired local point. At the real place take
 $1/(2\lambda)<u<1/\lambda$, choose $v$ sufficiently large,
```

### H127

Class: whitespace only. Base 29402-29426; candidate 29379-29403.

```diff
@@ -29402,25 +29379,25 @@
 318,\ 315,\ 314,\ 313,\ 307,\ 301,\ 299 .
 \]
 The early exact eliminations, affine H chart and squared-H
-replacement are justified above. The count326 replaces
+replacement are justified above. The count 326 replaces
 separate pole blocks by the three groups; the final group
 argument proves their required arithmetic properties
-directly. The count315 precedes common scaling.
+directly. The count 315 precedes common scaling.
 Common scaling removes twelve local coordinates, adds nine
-shared coordinates and two scaled test coordinates, giving314.
+shared coordinates and two scaled test coordinates, giving 314.
 The coupled quaternion anchor replaces those nine by eight,
-giving313. Reciprocal A, T and Z root charts give307,
-alternate-ordinate elimination gives301, and the oriented
-scalar auxiliary chart gives299.
+giving 313. Reciprocal A, T and Z root charts give 307,
+alternate-ordinate elimination gives 301, and the oriented
+scalar auxiliary chart gives 299.
 Intermediate alternatives with different depth requirements
 are not needed for this selected proof.

-The literal final system has279 quadratic component
-equations in299 active rational variables, including the
+The literal final system has 279 quadratic component
+equations in 299 active rational variables, including the
 input. Its polynomial is their unweighted sum of squares.
 Over $\mathbb Q$ it vanishes exactly when every component
 equation vanishes. Exact expansion, collection by exponent
-vector and removal of zero coefficients give6,630 monomials,
+vector and removal of zero coefficients give 6,630 monomials,
 total degree four, content one, and maximum absolute
 coefficient $186624C^2=186624\cdot3^{2^{26}}$.
 Every coordinate is active. The coefficient artifacts specify
```

### H128

Class: whitespace only. Base 29440-29446; candidate 29417-29423.

```diff
@@ -29440,7 +29417,7 @@
 $c_0=3^{a_0}$ and $c_j=3^{a_j}c_{j-1}^2$ for $1\leq j\leq13$.
 If $c_j=3^{e_j}$ then
 $e_0=2049$ and $e_j=2e_{j-1}+a_j$.
-After the eleven2048 steps $e_{11}=2^{23}$, and the two
+After the eleven 2048 steps $e_{11}=2^{23}$, and the two
 last squares give $e_{13}=2^{25}$. Thus $c_{13}=C$.
 Each coordinate is uniquely determined; no square-root sign
 is introduced.
```

### H129

Class: whitespace only. Base 29470-29476; candidate 29447-29453.

```diff
@@ -29470,7 +29447,7 @@
 6,672 nonzero monomials and content one.
 Let $K_0$ denote the constant coefficient of the symbolic
 sum of squares, an explicitly tabulated positive integer
-of1,514 bits. The exact largest absolute coefficient of
+of 1,514 bits. The exact largest absolute coefficient of
 the ordinary expansion is
 \[
  3^{4098}+K_0,\qquad
```

### H130

Class: whitespace only. Base 29478-29484; candidate 29455-29461.

```diff
@@ -29478,7 +29455,7 @@
 \]
 This proves the asserted ordinary coefficient bound.
 The source-coordinate table retains the original coordinate
-identifiers and has222,890 bytes. A compact table renames
+identifiers and has 222,890 bytes. A compact table renames
 the active variables consecutively by an explicit bijection
 fixing the input; its byte count is a separate artifact
 property. That renaming changes neither the equations nor
```

### H131

Class: prose, notation or text-conversion cleanup; inspect both sides. Base 29560-29565; candidate 29537-29545.

```diff
@@ -29560,6 +29537,9 @@
 linearization proved below. The three algebraic polynomial-map results
 from Green--Tao--Ziegler used here, Corollary B.4, Proposition B.6 and
 Lemma B.9, are not among the statements affected by the authors' erratum.
+The inverse-theorem derivation uses polynomial maps on $\mathbb Z$.
+The clauses below concerning limit polynomial maps and limit functions
+are not invoked by this derivation.

 \subsection{Exact target and conventions}

```

### H132

Class: journal edition, locator or associated scope wording. Base 29598-29622; candidate 29578-29593.

```diff
@@ -29598,25 +29578,16 @@
 orbit without a same-step linearization or an $N$-dependent family does
 not satisfy this target.

-% Standalone proposal for insertion after the unchanged GI target.
-% This fragment changes no manuscript.  The integrator supplies the bibliography
-% keys cs2022, candela2017compact, candela2017algebraic, and v15-gi-14-GTZ.
-% It invokes the retained local theorem v15:gi:14:thm:linear.

 \subsection{Finite-family witnesses from compact nilspaces}
 \label{v18:cs:witnesses}

 We use the inverse-theorem inputs of Candela--Szegedy
-\cite{cs2022} in the 39-page author version
-\texttt{arXiv:1902.01098v3}, dated 13 March 2022.  The arXiv record
-identifies this as the final version to appear, with referee comments
-incorporated.  All page numbers for that source below refer to this
-author version.  The 42-page Crelle version of record has not been
-obtained for comparison; no identity of its pagination or individual
-statements with the author version is asserted here.
+\cite{cs2022}, published in Crelle \textbf{789} (2022), 1--42.
+All page references to that source below refer to the journal edition.
 We use the stated Theorems 5.2 and 6.1 and Proposition 6.3, rather
 than infer connectedness of all filtration groups from the phrase
-``connected filtered nilmanifolds'' in Theorem 1.7 alone.
+``connected filtered nilmanifolds'' in Theorem 1.7 on page~5 alone.

 A compact finite-rank nilspace has compact abelian Lie structure
 groups; it is \emph{toral} if those structure groups are tori.
```

### H133

Class: journal edition, locator or associated scope wording. Base 29626-29632; candidate 29597-29603.

```diff
@@ -29626,7 +29597,7 @@
 Choose one representative of each class.  On these representatives
 fix the metrics used for the Lipschitz bound in Definition 1.3,
 and a factor-consistent metrization of cube-probability spaces
-as in \cite[\S6, equation (5), pp.~26--27]{cs2022}.
+as in \cite[\S6, equation (6.1), p.~29]{cs2022}.
 The latter metrics induce the weak topology; recursively they
 include the distance between the pushforwards to the preceding
 canonical factor.  Whenever another copy of a representative is
```

### H134

Class: journal edition, locator or associated scope wording. Base 29641-29647; candidate 29612-29618.

```diff
@@ -29641,7 +29612,7 @@
 positive integer $n\leq1/b$, the pushforward of the uniform cube
 measure on $\mathrm C^n(X)$ under $\phi$ has distance at most $b$
 from the uniform cube measure on $\mathrm C^n(Y)$, in the chosen
-metric; see \cite[Definition 5.1, p.~23]{cs2022}.
+metric; see \cite[Definition 5.1, p.~25]{cs2022}.
 If $0<b\leq b'$, then $b$-balance implies $b'$-balance.

 \begin{lemma}[Toral witnesses with uniform finite geometry]
```

### H135

Class: journal edition, locator or associated scope wording. Base 29668-29674; candidate 29639-29645.

```diff
@@ -29668,7 +29639,7 @@

 \begin{proof}
 For every positive integer $j$, apply
-\cite[Theorem 6.1, p.~27]{cs2022} at complexity bound $j$.
+\cite[Theorem 6.1, p.~29]{cs2022} at complexity bound $j$.
 Choose its balance constant $\beta_j>0$ and a number $P_j\geq2$
 at least as large as its prime threshold.  Its conclusion applies
 to a $\beta_j$-balanced morphism from $\mathbb Z/p\mathbb Z$ to a
```

### H136

Class: journal edition, locator or associated scope wording. Base 29678-29684; candidate 29649-29655.

```diff
@@ -29678,7 +29649,7 @@
 \[
  b(t)=\min\{1,\beta_{\lceil t\rceil}\}\quad(t>0).
 \]
-Theorem 5.2 of \cite[p.~26]{cs2022} allows this arbitrary positive
+Theorem 5.2 of \cite[p.~28]{cs2022} allows this arbitrary positive
 function.  Apply it with $k,b,\eta$ and denote its uniform
 complexity bound by $M$.  Put
 \[
```

### H137

Class: journal edition, locator or associated scope wording. Base 29835-29845; candidate 29806-29816.

```diff
@@ -29835,11 +29806,11 @@
 $H_Y=\widehat G$, $\Lambda_Y=\widehat\Gamma$ and fix the resulting
 isomorphism $\psi_Y$.

-Apply \cite[Proposition 6.3, p.~27]{cs2022} to the morphism
+Apply \cite[Proposition 6.3, p.~30]{cs2022} to the morphism
 $\psi_Y^{-1}\circ\phi$ into this coset nilspace and to the
 homomorphism $\mathbb Z\to\mathbb Z/p\mathbb Z$.
 It gives a polynomial lift on all of $\mathbb Z$.
-The Taylor expansion in \cite[Lemma A.5, p.~34]{cs2022} writes it as
+The Taylor expansion in \cite[Lemma A.5, p.~36]{cs2022} writes it as
 \[
  g(n)=a_0a_1^{\binom n1}\cdots a_k^{\binom nk},
  \qquad a_j\in H_{Y,j}.
```

### H138

Class: prose, notation or text-conversion cleanup; inspect both sides. Base 30008-30015; candidate 29979-29985.

```diff
@@ -30008,8 +29979,7 @@
 $\widetilde\Lambda_Y$ is one of the base points allowed by the
 unchanged GI target.  This proves that target relative to the
 specified source statements and the retained local
-same-step linearization theorem, with the source-version
-qualification stated above.  It does not assert the additional
+same-step linearization theorem.  It does not assert the additional
 internal nilcharacter identities used in the superseded local
 inverse-proof route.

```

### H139

Class: whitespace only. Base 33002-33009; candidate 32972-32979.

```diff
@@ -33002,8 +32972,8 @@
 clearing. The normalized scalar pole has exactly the ordinary pole
 input $b_s$ in~\eqref{v15:base248:eq:scalarnorm}. To verify its scaling literally,
 let $M$ be the coefficient of the stored $W_s$-square coordinate in
-source row491, let $K$ be the coefficient of $e\bar b$ in row499,
-and let $L$ be the coefficient of $\bar b p^2$ in row494. The exact
+source row 491, let $K$ be the coefficient of $e\bar b$ in row 499,
+and let $L$ be the coefficient of $\bar b p^2$ in row 494. The exact
 coefficient identities are
 \[
                   K=82479248M,\qquad 3L=17K.
```

### H140

Class: status, source locator or provenance prose. Base 33670-33676; candidate 33640-33646.

```diff
@@ -33670,7 +33640,7 @@
 The normalizer equation is $(1+22201r)R=A_Nr$, so $R>0$. The forward map divides by the indicated powers of $R$; the inverse multiplies by them and restores $R^4$. Every division is therefore legitimate on both solution sets. Together with the row identities this proves a fixed-input, fixed-parameter rational witness bijection. The count is 238 coordinates and 212 residuals.

 \subsection{Sparse presentation of the 238-variable predecessor}
-The preceding section describes the raw 238-coordinate presentation. The predecessor presentation is the independently accepted composition in \texttt{composition238-007}. Apply its affine coordinate stages to the raw system: the Lucas $P/E$ basis, four constant shifts, five non-Lucas shears, and the four root sum/difference bases. In each root block the old slots become
+The preceding section describes the raw 238-coordinate presentation. The predecessor presentation is the composition in \texttt{composition238-007}. Apply its affine coordinate stages to the raw system: the Lucas $P/E$ basis, four constant shifts, five non-Lucas shears, and the four root sum/difference bases. In each root block the old slots become
 \[
  A=(X_1+Y_1)/2,\quad B=(X_1-Y_1)/2,\quad
  C=(J_1+H_1)/2,\quad E=(J_1-H_1)/2.
```

### H141

Class: status, source locator or provenance prose. Base 33679-33685; candidate 33649-33655.

```diff
@@ -33679,7 +33649,7 @@

 For each coordinate stage, that file states old coordinates as affine polynomials in new ones; unspecified coordinates are fixed. A raw solution is sent to the final system by applying the inverse coordinate stages in forward stage order. Recover the raw solution by applying the forward stages in reverse order. \path{INVERSE-MAPS.json} records these inverses. Row additions are undone by subtraction, sum/difference by half-sum/half-difference, and primitive normalization by its recorded nonzero rational multiplier. Thus simultaneous vanishing is equivalent in both directions with the input and $A_N$ fixed. All 238 variables occur.

-The exact final definitions are the 212 equations in Section~\ref{v15:equations}; the coordinate and row transformations are specified below. The companion files are reproducibility aids only. All 212 explicit quadratic equations are listed in the appendix, in the IR order. Its table specifies every large integer coefficient. Squaring and collecting these final equations yields 2342 coordinate monomials (2343 parameter-separated terms). The sparse composition changes the polynomial's coefficients, but not its rational zero-set projection onto the input. Its independent review is identified by the prefix \texttt{07f3b18c}; the complete receipt is included in the delivery evidence.
+The exact final definitions are the 212 equations in Section~\ref{v15:equations}; the coordinate and row transformations are specified below. The companion files are reproducibility aids only. All 212 explicit quadratic equations are listed in the appendix, in the IR order. Its table specifies every large integer coefficient. Squaring and collecting these final equations yields 2342 coordinate monomials (2343 parameter-separated terms). The sparse composition changes the polynomial's coefficients, but not its rational zero-set projection onto the input.


 \subsection{Field components and scalar gate meanings}\label{v15:component-typing}
```

### H142

Class: whitespace only. Base 33981-33987; candidate 33951-33957.

```diff
@@ -33981,7 +33951,7 @@
 238&\path{rootProduct.4.u.0}\\
 239&\path{rootProduct.4.u.1}\\
 \end{longtable}
-\paragraph{Row multipliers for global rescaling.} The omitted raw row is87. For every other raw row $i$, the substituted residual is $R^{k_i}$ times new row $j$. Zero powers are omitted from this table; row order is unchanged apart from deletion87.
+\paragraph{Row multipliers for global rescaling.} The omitted raw row is 87. For every other raw row $i$, the substituted residual is $R^{k_i}$ times new row $j$. Zero powers are omitted from this table; row order is unchanged apart from deletion 87.
 \begin{longtable}{rrr}
 $i$ & $j$ & $k_i$\\\hline
 15&15&-1\\
```

### H143

Class: whitespace only. Base 37542-37548; candidate 37512-37518.

```diff
@@ -37542,7 +37512,7 @@
 \]
 The finite contacts of the retained $M_5(\beta)$ are precisely
 $0,1,2401,-343/32$; its fifth contact is infinity. Thus the extra
-predecessor factor $2\beta-1$ is unnecessary. In the corrected raw233
+predecessor factor $2\beta-1$ is unnecessary. In the corrected raw 233
 indexing of Section~\ref{v15x:dictionary}, retain
 $t=x_{63}=x^2$ and $u=x_{121}=(51t+2501)^2/4$, delete $x_{122}$ and
 its defining equation, and replace the contact-product equation by
```

### H144

Class: whitespace only. Base 37551-37573; candidate 37521-37543.

```diff
@@ -37551,23 +37521,23 @@
        +767410608u-512u^2=0.                 \tag{C232}
 \]
 This is exactly $x_{123}=r_4$. Compact indices after the deleted slot.
-The other205 equations retain their meanings, giving232 coordinates
-and206 quadratic equations.
+The other 205 equations retain their meanings, giving 232 coordinates
+and 206 quadratic equations.

 For every rational $x$, all four factors of $r_4$ are positive and
 $r_4\ge1$. Consequently $R>0$ and
-$A/(1+149^2)\le R<A/149^2$. At149 the four residues
+$A/(1+149^2)\le R<A/149^2$. At 149 the four residues
 $(\theta-2504)/51$, for the four finite contacts $\theta$, are
 $59,97,109,108$, each a nonsquare. If $v_{149}(x)\ge0$, $r_4$ is a
 unit; otherwise $v_{149}(r_4)=8v_{149}(x)$ and
 $v_{149}(1+149^2r_4)=2+8v_{149}(x)$. Thus for $N\ge1$, $v_{149}(R)$ is respectively
 $2N+1$ or $2N-1$, positive and odd. The unchanged scalar argument of
-Section~\ref{v15x:parity} therefore still gives the forced149 depth
+Section~\ref{v15x:parity} therefore still gives the forced 149 depth
 and the reference exceptional-value exclusions.

 For $p>76176$ contributing to $M_5(\beta)$, exactly one finite
 contact factor has positive odd valuation. The constant differences
-and32 are units at such a prime, so $v_p(R)=v_p(r_4)>0$ is odd.
+and 32 are units at such a prime, so $v_p(R)=v_p(r_4)>0$ is odd.
 If $\beta$ is nonintegral then $v_p(\beta)=2v_p(x)$ is even and the
 infinite contact supplies no odd factor. The same local extraction
 therefore gives, for the nonzero scalar index $a$,
```

### H145

Class: whitespace only. Base 37575-37586; candidate 37545-37556.

```diff
@@ -37575,12 +37545,12 @@
 149^{\lfloor9(2N-1)/4\rfloor+1}M_5(\beta)^3\mid |a|.
 \]
 This is the divisibility input in the two retained height/Lucas
-contradictions. Those arguments, and the squarefree51 denominator
+contradictions. Those arguments, and the squarefree 51 denominator
 argument recovering $x\in\Z$, apply unchanged.

 For completeness, fix an integer $x$. A direct parity calculation gives
-$v_2(r_4)\in\{2,3\}$. Modulo3, $r_4=1$ and $1+149^2r_4=2$;
-modulo17, $r_4=13$ and $1+149^2r_4=5$. Hence
+$v_2(r_4)\in\{2,3\}$. Modulo 3, $r_4=1$ and $1+149^2r_4=2$;
+modulo 17, $r_4=13$ and $1+149^2r_4=5$. Hence
 $v_3(R)=v_{17}(R)=0$ and $v_2(R)\in\{2,3\}$.
 Since $9792=2^6 3^2 17$, the element $1+9792/R$ is a square in each
 of $\Q_2,\Q_3,\Q_{17}$. In particular the changed value $v_3(R)=0$
```

### H146

Class: whitespace only. Base 37605-37617; candidate 37575-37587.

```diff
@@ -37605,13 +37575,13 @@

 \subsection{One common alternate ratio}\label{v222:ratio}
 The useful direct-ratio idea is due to Jos\'e Brox's
-\emph{Fixed-difference charts}, version18, public revision
+\emph{Fixed-difference charts}, version 18, public revision
 \texttt{34454098637ba9100b19071da55a38199589f5e0}, equations for formal-parameter
 ratios. Here we retain the preceding reference chart and prove the
-needed domain from the scalar149 argument; no new arithmetic theorem
+needed domain from the scalar 149 argument; no new arithmetic theorem
 from that revision is assumed.

-In raw232 coordinates write $f=x_{17}+\rho x_{18}$,
+In raw 232 coordinates write $f=x_{17}+\rho x_{18}$,
 $S=x_{19}+\rho x_{20}$ and $g=x_{134}+\rho x_{135}$. Put
 \[
  \alpha=156+\tfrac{69}{2}\rho,\quad \beta_0=118+60\rho,
```

### H147

Class: whitespace only. Base 37636-37642; candidate 37606-37612.

```diff
@@ -37636,7 +37606,7 @@
 \[
 D_rT=N_r,\qquad E_iT=K_iL_i'\quad(0\le i\le3).
 \]
-At the inert prime149 the unchanged reference and scalar equations,
+At the inert prime 149 the unchanged reference and scalar equations,
 without any alternate-ratio equation, give
 $v(f)=m>0$, $v(S)=-m/2$ and $v(g)=m/2$.
 The norms $\Norm(\alpha)=43911/2$ and $\Norm(\beta_0)=6724$ are units.
```

### H148

Class: whitespace only. Base 37648-37656; candidate 37618-37626.

```diff
@@ -37648,9 +37618,9 @@
 D_r(E_iT-K_iL_i')=D_rT(E_i+K_iz_i)
  -K_i(N_rz_i+D_rL_i')-K_iz_i(D_rT-N_r)
 \]
-checks the forward implication directly. Delete raw232 slots21--28,
+checks the forward implication directly. Delete raw 232 slots 21--28,
 compact the survivors and append the two components of $T$.
-This gives226 coordinates and200 equations.
+This gives 226 coordinates and 200 equations.

 \subsection{Polynomial reference elimination}\label{v222:reference}
 Write $a=57-28\rho$, $b=8-14\rho$, $c=88-48\rho$, $e=39-36\rho$.
```

### H149

Class: whitespace only. Base 37750-37756; candidate 37720-37726.

```diff
@@ -37750,7 +37720,7 @@
 Furthermore
 \[(bS-e)\mathcal F-(a+cf)\mathcal E=8a(fS^2+D_cf^2-1).\]
 Thus the finite $H$ curve and $f\ne0$ hold before interpreting $w$.
-The unchanged scalar149 argument gives $v(f)=m>0$, $v(S)=-m/2$,
+The unchanged scalar 149 argument gives $v(f)=m>0$, $v(S)=-m/2$,
 and $v(g)=m/2$, independently of $w$. In $Q_2=Mw+L$ the coefficient is
 \begin{align*}
 M={}&B+\left({23335979380411305\over9142573010269636}
```

### H150

Class: whitespace only. Base 37760-37766; candidate 37730-37736.

```diff
@@ -37760,7 +37730,7 @@
 &+{3317607896141091533\over7167777240051394624}
  +{677690583653850567\over1791944310012848656}\rho .
 \end{align*}
-All coefficients are149-integral, and the norm of the $S$ coefficient
+All coefficients are 149-integral, and the norm of the $S$ coefficient
 is $414947904808977/2612163717219896$, a149-unit. Thus its $S$ term is
 uniquely lowest and $M\ne0$. Substitute $g=-f(bS+e)/(a+cf)$,
 $w_*=g^4/f^2$ and $T=N_r/D_r$ into the listed quadrics and reduce by
```

### H151

Class: whitespace only. Base 37768-37776; candidate 37738-37746.

```diff
@@ -37768,9 +37738,9 @@
 remainder is zero. Both factors are nonzero by the preceding valuation
 argument. In particular $Q_2=0$ forces $w=w_*$; $Q_4=0$ gives $W=w^2$,
 and $Q_5$ follows. Retain only $Q_0,Q_1,Q_2,Q_3,Q_4$.
-Delete raw226 slots126,127 and compact. This gives224 coordinates and198
+Delete raw 226 slots 126,127 and compact. This gives 224 coordinates and 198
 quadrics with inverse (G), including all zero numerator and component
-branches. In raw224 the actual output bases are
+branches. In raw 224 the actual output bases are
 \[
  B=x_{74}+2\rho x_{75},\quad w=x_{21}+2\rho x_{22},\quad
  W={37249x_{23}-34848x_{24}\over2401}
```

### H152

Class: whitespace only. Base 37778-37796; candidate 37748-37766.

```diff
@@ -37778,19 +37748,19 @@
 \]

 \subsection{Paired factors and three root normalizations}\label{v222:roots}
-Until the next subsection indices refer to raw224. Set
+Until the next subsection indices refer to raw 224. Set
 $q_0=x_{87}$, $q=x_{102}$, $Q_0=x_{89}=q_0^2$,
 $Q_1=x_{104}=q^2$, $h_0=x_{88}=q_0^7$, $h_1=x_{103}=q^7$,
 $j_0=x_{90}=q_0^4$, $j_1=x_{105}=q^4$, $R=x_{126}$, $R^2=x_{125}$.
 The retained contact equations imply $q\ne0$ without using a root or
 trace equation. After division by the nonzero $R^2$ they give
-$(1+q)P_5(r)=r^5$, $r=(t-1)^2$. Modulo5,
-$P_5(r)=(r-1)^2(r-4)^3$. If $q=0$ and $t$ is5-integral, the square
+$(1+q)P_5(r)=r^5$, $r=(t-1)^2$. Modulo 5,
+$P_5(r)=(r-1)^2(r-4)^3$. If $q=0$ and $t$ is 5-integral, the square
 residues $r=0,1,4$ contradict this equation. If $v_5(t)<0$,
-$P_5(r)-r^5$ has degree4 and unit leading coefficient, so its leading
+$P_5(r)-r^5$ has degree 4 and unit leading coefficient, so its leading
 term cannot cancel. This argument preserves $q=-1$.

-Delete slots62,63,66,67,68,69. For each tuple
+Delete slots 62,63,66,67,68,69. For each tuple
 \[
 (F_0,F_1,U_0,U_1)=(62,63,179,180),(66,67,207,208),(68,69,221,222)
 \]
```

### H153

Class: whitespace only. Base 37802-37808; candidate 37772-37778.

```diff
@@ -37802,7 +37772,7 @@
 The other changes, with unlisted coordinates fixed, are
 \[
 \begin{array}{c|c}
-\text{raw224 slots}&\text{new value}\\\hline
+\text{raw 224 slots}&\text{new value}\\\hline
 167\!:\!178,\ 195\!:\!202,\ 209\!:\!216 &(q/R)\,\text{old value}\\
 179,180,203\!:\!208,217\!:\!222&q\,\text{old value}\\
 47\!:\!54,56\!:\!59&\text{old value}/R
```

### H154

Class: whitespace only. Base 37820-37830; candidate 37790-37800.

```diff
@@ -37820,11 +37790,11 @@
 H=Q_1h_0-Q_0h_1,\quad J=Q_1j_0-Q_0j_1,\quad K_*=Q_1q_0-Q_0q.
 \]
 For matching factor expressions $F_j=1+h_jA+Q_jB+j_jC+q_jS_*$,
-where $S_*$ occurs only in factor2,
+where $S_*$ occurs only in factor 2,
 \[
 Q_1F_0-Q_0F_1=Q_1-Q_0+HA+JC+K_*S_*.
 \]
-Apply this to factors1,2,4, retaining the detector1 equation and replacing
+Apply this to factors 1,2,4, retaining the detector1 equation and replacing
 the detector0 equation by the combination. The deleted $q^2F_U$ terms
 in detector1 become the quadratic expressions in $U$ above. The special
 $qF_U$ output of root2 is retained. Since $Q_1\ne0$, this row operation
```

### H155

Class: whitespace only. Base 37837-37850; candidate 37807-37820.

```diff
@@ -37837,14 +37807,14 @@
 \]
 using the unchanged second root, and let $Z$ be the sum of the three
 new trace squares for pairs $(171,173),(199,201),(213,215)$ and their
-imaginary pairs with coefficient2. The new trace is $Q_1G-R^2Z=0$,
+imaginary pairs with coefficient 2. The new trace is $Q_1G-R^2Z=0$,
 which is $q^2$ times the old trace after substitution. Delete the six
 output slots, compact in increasing order, and append $H,J,K_*,G,Z$.
-There are223 coordinates and197 quadrics. No component, label or root
+There are 223 coordinates and 197 quadrics. No component, label or root
 numerator has been divided by.

 \subsection{The final common quotient}\label{v222:quotient}
-In raw223 the only consumers of $G=x_{222},Z=x_{223}$ are
+In raw 223 the only consumers of $G=x_{222},Z=x_{223}$ are
 \[
 Q_1G-R^2Z=0,\quad G=P-T_2,\quad Z=T_1+T_3+T_4,
 \]
```

### H156

Class: whitespace only. Base 37856-37870; candidate 37826-37840.

```diff
@@ -37856,15 +37826,15 @@
 They are quadratic. The inverse is polynomial, $G=R^2U_*$,
 $Z=Q_1U_*$, and the old trace becomes identically zero.
 The forward quotient exists by the unchanged contact proof of $q\ne0$.
-No trace value or rational component is inverted. Keep slots1 through221
-and number $U_*$ as222. This proves222 variables and196 quadrics with
+No trace value or rational component is inverted. Keep slots 1 through 221
+and number $U_*$ as 222. This proves 222 variables and 196 quadrics with
 all zero branches preserved. The input, arithmetic hypotheses and
 ineffective sufficient threshold remain unchanged.

 \subsection{Exact final affine and row presentation}\label{v222:maps}
-The following ordered affine substitutions use raw223 indices and give
-old coordinates in terms of new ones. They do not touch slots222,223,98
-or119, so commute with the final common quotient. Unlisted coordinates
+The following ordered affine substitutions use raw 223 indices and give
+old coordinates in terms of new ones. They do not touch slots 222,223,98
+or 119, so commute with the final common quotient. Unlisted coordinates
 are fixed. Each has a rational linear inverse.

 \paragraph{Affine stage 1.}
```

### H157

Class: whitespace only. Base 37963-37971; candidate 37933-37941.

```diff
@@ -37963,9 +37933,9 @@

 Finally clear denominators and divide each row by the positive gcd of
 its integer coefficients. These are nonzero constant row scalings.
-Then replace row124 by $3Q_{124}+11Q_{125}$, leaving row125 fixed;
-the inverse subtracts $11Q_{125}$ and divides by3. The common quotient
-removes former row186, and all subsequent row indices decrease by one.
+Then replace row 124 by $3Q_{124}+11Q_{125}$, leaving row 125 fixed;
+the inverse subtracts $11Q_{125}$ and divides by 3. The common quotient
+removes former row 186, and all subsequent row indices decrease by one.
 The explicit list below fixes every sign and normalization. All these
 row operations are invertible on simultaneous zero sets.

```

### H158

Class: whitespace only. Base 37975-37981; candidate 37945-37951.

```diff
@@ -37975,7 +37945,7 @@
 \[
  P_N(z)=\sum_{i=1}^{196}w_iQ_{i,N}(z)^2.
 \]
-Every weight is a positive integer. Unlisted weights are2; the exceptions are
+Every weight is a positive integer. Unlisted weights are 2; the exceptions are
 \[
 \begin{array}{c|l}w_i&i\\\hline
 4&40,53,119,121,153,155,169,171\\
```

### H159

Class: whitespace only. Base 37984-37991; candidate 37954-37961.

```diff
@@ -37984,8 +37954,8 @@
 6&133,183\\
 \end{array}
 \]
-The weights sum to428. Thus this is also a sum of428 repeated squares,
-not196 unit-weight squares. The positive weights preserve the common zero set.
+The weights sum to 428. Thus this is also a sum of 428 repeated squares,
+not 196 unit-weight squares. The positive weights preserve the common zero set.

 The following exact integer constants abbreviate long coefficients.
 {\scriptsize
```

### H160

Class: whitespace only. Base 39536-39555; candidate 39506-39525.

```diff
@@ -39536,20 +39506,20 @@
 operations preserve that zero set, and positive weights preserve it
 again. This proves Theorem~\ref{thm:v15-main} for the displayed polynomial.

-Expanding the196 weighted squares gives2277 coordinate monomials,
-or2278 terms if the coefficient parameter is separated. The polynomial
-has degree four and content one, and all222 coordinates occur. The only
+Expanding the 196 weighted squares gives 2277 coordinate monomials,
+or 2278 terms if the coefficient parameter is separated. The polynomial
+has degree four and content one, and all 222 coordinates occur. The only
 quadratic dependence on $A_N$ occurs in the coefficient of $z_{108}^2$,
 which is $A_N^2+1$. Linear parameter coefficients have absolute value at
-most44402; every parameter-free coefficient has magnitude less than
+most 44402; every parameter-free coefficient has magnitude less than
 $149^{214}$. Consequently for $N\ge53$ the exact largest absolute
 coefficient is $A_N^2+1=149^{4N+2}+1$. These are finite coefficient facts,
 not an effective bound for the defining threshold. No particular
 numerical $N$ is certified to define the integers solely by this calculation.

-The full ordinary decimal314-variable example and the original huge
+The full ordinary decimal 314-variable example and the original huge
 polynomial in the earlier sections are retained independently of this
-family. The222 construction does not replace their distinct finite
+family. The 222 construction does not replace their distinct finite
 coefficient specifications or strengthen any inherited arithmetic premise.

 \begin{thebibliography}{99}
```

### H161

Class: status, source locator or provenance prose. Base 39689-39695; candidate 39659-39665.

```diff
@@ -39689,7 +39659,7 @@
 \bibitem{a001-moduli-project} Project proof,
 \emph{The fixed principal datum and its discriminant-six coarse quotient},
 \href{https://github.com/elliotglazer/diophantine-z-q/blob/main/research/version14/proofs/a001-moduli-current-v1/PROOF.md}{Fixed-datum and coarse-moduli proof}.
-The adjacent Baba--Granath product-map finding is preserved separately.
+
 \bibitem{ly-d6-normalization-project} Project proof,
 \emph{Discriminant-six normalization from Lin--Yang Example 30},
 \href{https://github.com/elliotglazer/diophantine-z-q/blob/main/research/version14/proofs/ly-d6-normalization-v1/PROOF.md}{Normalization proof},
```

### H162

Class: status, source locator or provenance prose. Base 39966-39972; candidate 39936-39942.

```diff
@@ -39966,7 +39936,7 @@
 \url{https://arxiv.org/abs/0908.3905}.
 \bibitem{cj-conductor-one-project}
 Versioned project proof, \emph{A direct conductor-one reduction argument},
-version 1. Exact proof, explicit retained inputs and bounded review at
+version 1. Proof and explicit retained inputs at
 \href{https://github.com/elliotglazer/diophantine-z-q/blob/main/research/version14/proofs/cj-conductor-one-v1/README.md}
 {\texttt{research/version14/proofs/cj-conductor-one-v1/}}.
 \bibitem{cornutjetchev} C. Cornut and D. Jetchev,
```

### H163

Class: status, source locator or provenance prose. Base 40146-40166; candidate 40116-40134.

```diff
@@ -40146,21 +40116,19 @@
 \url{https://doi.org/10.1090/conm/270/04376}.
 \bibitem{pan-p5-sw99-project}
 Versioned project proof, \emph{Prime-five auxiliary cohomology and element
-selection}, version 1. Authored proof, supporting sources and bounded
-review records at
+selection}, version 1. Proof and supporting sources at
 \href{https://github.com/elliotglazer/diophantine-z-q/blob/main/research/version14/proofs/pan-p5-sw99-v1/README.md}
 {\texttt{research/version14/proofs/pan-p5-sw99-v1/}}.

 \bibitem{pan-local-rings-project}
 Versioned project proof, \emph{Local matrix connections for Pan at prime five},
-version 1. Exact source qualifications, integral proof and bounded
-independent review at
+version 1. Exact source qualifications and integral proof at
 \href{https://github.com/elliotglazer/diophantine-z-q/blob/main/research/version14/proofs/pan-local-rings-v1/README.md}
 {\texttt{research/version14/proofs/pan-local-rings-v1/}}.

 \bibitem{pan-utility-project}
 Versioned project proof, \emph{Four utility applications in Pan},
-version 1. Proof, exact source qualifications and bounded review at
+version 1. Proof and exact source qualifications at
 \href{https://github.com/elliotglazer/diophantine-z-q/blob/main/research/version14/proofs/pan-utility-p5-v1/README.md}
 {\texttt{research/version14/proofs/pan-utility-p5-v1/}}.

```

### H164

Class: status, source locator or provenance prose. Base 40169-40175; candidate 40137-40143.

```diff
@@ -40169,7 +40137,7 @@
 version 1, \href{https://github.com/elliotglazer/diophantine-z-q/blob/main/research/version14/proofs/cj-cm-inputs-v1/README.md}{proof and source contracts}.
 \bibitem{cj-good-reduction-project}
 Project proof supplement, \emph{Good-reduction specialization}, version 1,
-\href{https://github.com/elliotglazer/diophantine-z-q/blob/main/research/version14/proofs/cj-good-reduction-v1/README.md}{proof and independent scoped review}.
+\href{https://github.com/elliotglazer/diophantine-z-q/blob/main/research/version14/proofs/cj-good-reduction-v1/README.md}{proof with its stated hypotheses}.

 \bibitem{milne1986-abelian} J. S. Milne, \emph{Abelian varieties},
 in \emph{Arithmetic Geometry}, Springer, 1986, 103--150,
```

### H165

Class: prose, notation or text-conversion cleanup; inspect both sides. Base 40282-40291; candidate 40250-40257.

```diff
@@ -40282,10 +40250,8 @@
 abelian groups and nilmanifolds},
 Journal f\"ur die reine und angewandte Mathematik \textbf{789} (2022), 1--42.
 \url{https://doi.org/10.1515/crelle-2022-0016}.
-The text and page locators used here are those of the final author version,
-arXiv:1902.01098v3, 13 March 2022, 39 pages,
+An author version is available as arXiv:1902.01098v3, 13 March 2022,
 \url{https://arxiv.org/abs/1902.01098v3}.
-The 42-page journal edition has not been compared.

 \bibitem{candela2017compact}
 P. Candela, \emph{Notes on compact nilspaces},
```

### H166

Class: status, source locator or provenance prose. Base 40305-40313; candidate 40271-40279.

```diff
@@ -40305,9 +40271,9 @@
 \section*{Version 15 provenance}
 The historical 233-variable system uses the three-residue 237-variable scalar criterion, the two-reference-identity reduction to 235 variables, and the corrected reference-square elimination to 233 variables. The full sparse presentation has 207 quadratic residuals and 2514 monomials. Its exact source IR has SHA256
 \begin{center}\small\ttfamily 10fe99b5ee41b8ed7b602fd9e8bd759f8640cd18b37326ce12ca62832320d702\end{center}
-These reductions and finite transformations were developed and internally reviewed by separate Astra agents. The present manuscript integrates those arguments; its companion audit records source versions, equation generation, and subsequent review separately. Internal model review is not independent human peer review or formal verification. The earlier complete development follows with its provenance preserved.
+These reductions and finite transformations were developed by separate Astra agents. The present manuscript integrates those arguments; the companion audit records source versions and equation generation.
 \section*{The 238-variable predecessor: provenance}
-The 238-variable development begins with Jos\'e Brox's 9 November 2026 version-17 sources, pinned to repository commit \texttt{d25e0aa6046662d9a878755aca8ed742821d3e61}. Its height, aggregate and local-construction arguments have been incorporated into this manuscript with internal references. Astra agents authored and independently reviewed the scalar-S replacement, root-product charts, reciprocal scale, global scalar rescaling, sparse transformations, exact expansions and source matching, under Elliot Glazer's direction. These are internal model reviews, not independent human peer review or formal verification. The companion dependency map preserves exact source hashes and transformation provenance. Earlier provenance follows unchanged.
+The 238-variable development begins with Jos\'e Brox's 9 November 2026 version-17 sources, pinned to repository commit \texttt{d25e0aa6046662d9a878755aca8ed742821d3e61}. Its height, aggregate and local-construction arguments have been incorporated into this manuscript with internal references. Astra agents authored the scalar-S replacement, root-product charts, reciprocal scale, global scalar rescaling, sparse transformations, exact expansions and source matching, under Elliot Glazer's direction. The companion dependency map preserves exact source hashes and transformation provenance.
 The Version 9 odd-product and asymmetric-depth improvements were developed
 by Gabriel Conant with ChatGPT and incorporated with additional source,
 convention, and finite-certificate checks.
```

