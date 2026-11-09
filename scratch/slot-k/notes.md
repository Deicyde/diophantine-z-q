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
