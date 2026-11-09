# slot-k running notes

## Step 0 (read descent-alt in full)
- Certificate for C_d: d ≡ ±β mod squares (torsion), or dim Sel2(C_d)=3 and β ∈ π1(Sel2(C_d)).
- Prop 0 linear system (odd d>0): A u + Dλ v = a0 λ + a1 μ; Dμ u + (A+Dλ) v = b0 λ + b1 μ; a0=b0; 2-adic rows by d mod 8.
- Input facts: θ>0, θ≡1 mod 8, gcd(θ,2730)=1, (β/ℓ)=1 for ℓ|θ, (θ/p)=1 for odd p|β.
- Need |d| ≡ 5,6,7 mod 8 for odd Selmer parity. m chosen so β odd, |β| ≡5,7 mod 8.
- Both curves: d1 = β n', d2 = β n' θ; same class mod 8 as θ≡1(8).
- Prop B: needs ≥ k aux primes. Prop C: symmetric sets fail.
- Greedy stalls; random 2-3 aux primes solved all.
- pc-audit.md not present in repo (searched).

## Step 1 (read rv-route-k 4.2-4.4, manuscript 1019-1070, symsel.py)
- symsel.equations(cfg) gives rows over [a0,a1,b0,b1,u,v]; cfg=(d mod 8, lam, mu, L). has_first(cfg,umask).
- Manuscript template: kerK = <1, 1_supp β>, d-1 slots type (0,0) + one q0 of type (1,1); rank-one correction.
- Next: design the construction for C_d in Prop 0 language. Plan: one sub-question per step.

## Step 2 (merge origin/main; read descent-alt in full again, pc-audit §2, §4)
- origin/main merged: pc-audit.md now present.
- pc-audit §2.2: deep input needed only as (R≥1) for Selmer-minimal C_d (dim Sel2=3) with class β; RK9: rank≥1 + dim 3 ⇒ σ_d from a point.
- pc-audit §4.2 K-TYZ-β variant: extra rule |n|≡5 (8), β odd, |β|≡3 (4) — optional strengthening; target Kriz form first.

## Step 3 (first structural analysis; by hand, to be verified)
- Mazur–Rubin twisting shortcut unusable: comparison needs q square at all bad p, then reciprocity kills loc_q (all [p/q]=0).
- Parity: q≡1 (8) keeps |d| mod 8, so s changes by even amounts.
- A = K (manuscript's K: (Ku)_i = Σ_{j≠i}[p_j/p_i](u_j+u_i)), K1=0.
- Aux q≡1 (8): equations at q are (Ku)_q=0,(Kv)_q=0; Q-block K_QQ = diag(X1_I+Y1)+Y, K_QQ 1_Q = X1_I.
- σ (u=1_P,u_Q=0) needs X1_P=0 ⇒ K_QQ singular; aux block acts as Laplacian change of input symbols + one virtual prime with symbol vector w=[n'/·].
- Edge gadget (q1~p, q2~p', q1~q2, all ≡1 (8)) toggles L_pp' exactly, but lifts u_P=1_P to u_{q1}=u_{q2}=1 (breaks σ unless both p,p'∈P... lifts to |β|q1q2).

## Step 4 (θ-transfer lemma)
- Construction: aux hub h≡1 (8) = partner of an aux z (symbol 1 only at z, 0 at T); for each ℓ∈T a partner r_ℓ≡1 (8) with [r_ℓ/ℓ]=[r_ℓ/h]=1, all other symbols 0; all other aux q have [q/ℓ]=0 ∀ℓ∈T.
- Claim (derived by hand): Sel(C_{d1 θ}) ≅ Sel(C_{d1}) (d1=|β|·n'), via u_T=u_h 1_T, v_T=v_h 1_T, u_{r_ℓ}, v_{r_ℓ} slack. Uses only θ≡1 (8), (θ/p)=1 (p|β), (β/ℓ)=1.
- σ (u=1_P) lifts with first coordinate β iff v_z(σ)+a0(σ)=0 (u_{r_ℓ}=λ_ℓ(v_h+a0)).
- t1_transfer.py: 200 random actual-prime trials, dim Sel equal in all; β∈π1 transfers in 31/37 (6 failures = the v_z+a0 condition).
- PARI available via `~/bin/uv run --with cypari2 python`.

## Step 5 (collapse lemma, template, full construction — derived, to validate)
- P-collapse: partners r_p (p∈P∖{p0}) ≡1 (8), [r_p/p]=[r_p/p0]=1, else 0 ⇒ Sel ≅ virtual system with P replaced by one prime p* ≡ |β| (8), symbols = Jacobi sums. Lift of σ*: u_{r_p} = [n''/p]+1+λ_p(v*+a0) (must be 0).
- t2_template.py: one aux suffices iff (p*,q0) ≡ (7,3) or (3,7) mod 8, any symbol x=[q0/p*]: dim 3, p*∈π1. By hand: σ*: v_p*=a0+x, v_q0=a0+x+1 (ε=v*+a0=x, η=v_q0+a0=x+1).
- T-hub may be q0 itself. T lift: u_{r_ℓ}=λ_ℓ(s+η), s=[β<0].
- Construction: m with β odd, |β|≡7 (8); x=s+1; q0≡3 (8), [q0/p]=1+λ_p x (p≠p0), [q0/p0]=x+Σ_{p≠p0}(1+λ_p x), [q0/ℓ]=0; r_p; r_ℓ ([r_ℓ/ℓ]=[r_ℓ/q0]=1). n=β q0 ∏r. #aux = ω(β)+ω(θ).
- m with |β|≡7 (8), β odd always exists: |m_odd| mod 8 covers 1,3,5,7.

## Step 6 (implementation, first validation)
- slotk.py: construction with actual primes (CRT on P∪T, Euler-criterion search for symbols between aux primes; naive full CRT made sizes double per slot).
- run_dl.py random30 (seed 2026, first multiplier with |β|≡7 (8)): 30/30 both curves certified ('selmer3') by the exact descent sel2cong.py; #aux = ω(β)+ω(θ) ∈ [?], aux primes ≤ 46 digits. Output out_random30.txt.
- Draft §1, §2.1–2.3 of docs/research/slot-k.md written.

## Step 7 (families)
- Greedy-stall inputs: e8 replayed (seed 7, MAXK 9 recovered by find_seed_e8.py; replay diverges after #0 because of tie-breaking, but uses the same greedy) → stall inputs #8,#18,#19,#20,#23,#28 (out_e8_replay.txt; #8 not solved by e8's random fallback either). Construction: 6/6 inputs OK for every multiplier with β odd, |β|≡7 (8) (out_stall.txt).
- Speed: Jacobi via PARI kronecker; search cost 2^j for mutual aux symbols (j ≤ ω(β)+ω(θ)).
- Observation: n=βq0∏r has |n|≡7·3≡5 (8) and |β|≡3 (4): this is the K-TYZ-β row-5b rule of pc-audit §4.2.

## Step 8 (symbolic test of the theorem; proof written in note §2.4–2.6)
- t3_symbolic.py: random abstract data with only (θ1)–(θ4), Prop 0 system (symsel): 300 (ω≤6), 1000 (ω≤12), 2000 (ω≤3) trials: 0 failures (both curves dim 3, β∈π1 with sign).
- Negative control WRONGX=1 (x=s instead of s+1): curve 1 still certified, curve 2 dim 3 but β∉π1 in 183/300 (exactly when T has primes ≡3 mod 4) — the sign choice is necessary.
- slotk.py speed: gcd with primorial sieve.

## Step 9 (note §4 drafted; place-2 check)
- Place-2 rows: structure (depends on c(𝒞) and λ·u, μ·u, λ·v, μ·v) and c=5 rows verified by hand: image of C_5(Q_2) spanned by (5,2),(7,3),(1,5) [x=1/4]; conditions a_v=0, a_ε=b_ε, b_v=a_ω ⇔ a1=0, λ·u=λ·v, b1=μ·u.
- Mathlib names checked: Nat.forall_exists_prime_gt_and_zmodEq, Nat.chineseRemainderOfList, jacobiSym.quadratic_reciprocity_one_mod_four, legendreSym.mul, FiniteField.exists_nonsquare.
- B1 (8 multipliers) all OK; B2 running.

## Step 10 (families B123, e11; ellrank)
- B1, B2, B3 (no certifying multiplier with n=β, descent-alt §4.3): all 8 multipliers each with β odd, |β|≡7 (8): 24/24 OK (out_B123.txt), up to 17 aux primes (B1, m=±65), ≤ 89 digits.
- e11 core-6 instances #0 (=B3), #1: 16/16 OK (out_e11.txt).
- t4_ellrank.py (small realizations, PARI ellrank effort 6): rank bounds [1,1] on all 20 curves; explicit points found on 6 curves (3 instances), all with abscissa class β (mod torsion cosets). ellheegner too slow.
