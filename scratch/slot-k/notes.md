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
