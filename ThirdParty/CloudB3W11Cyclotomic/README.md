# `ZInQKernel/Contrib/CloudB3W11Cyclotomic/` — the arithmetic edge of H-120

Task cloud-b3/w11, author D, 2026-11-16. Branch `cloud-b3/w11-tate-foundations`,
base `cc4d360378d888e1e403804f803168701128522a`, Lean 4.35.0, Mathlib `56a00585`.

Target: `ZInQ.Contrib.HodgeSplit.TateTwistInvariants`
(`ZInQKernel/OneProof/H/TailS.lean` l. 69-72; frontier H-120; Tate 1967 §3.3 Thm 2).

Nothing here imports `ZInQKernel.OneProof`. Everything is stated over the repository's genuine
objects `ZInQ.Contrib.G9.PkgI4.cyc` / `cycPow` / `cpAct`
(`ZInQKernel/Contrib/G9/I4Layer.lean` l. 829-849). Attribution for the ported material is in
`UPSTREAM_NOTICE`.

## Modules

| module | imports | contents |
| --- | --- | --- |
| `TowerDefinition` | `Contrib.G9.I4Layer` | `PadicAlgCl.cyclotomicTower` and its fixing subgroups |
| `TowerDegree` | `TowerDefinition`, `Contrib.TauCeti.…Cyclotomic.Irreducible` | degrees, the degree-`p` step |
| `InfiniteImage` | `TowerDegree` | the infinite cyclotomic image, algebraic twisted invariants |

Build (one Lean process, two threads, peak RSS about 7.0 GB, about 20 s in total):

```
lake env lean --threads=2 -R . -o .lake/build/lib/lean/ZInQKernel/Contrib/CloudB3W11Cyclotomic/<M>.olean \
  ZInQKernel/Contrib/CloudB3W11Cyclotomic/<M>.lean
```

for `<M>` = `TowerDefinition`, `TowerDegree`, `InfiniteImage`, in that order. Zero errors, zero
warnings; every declaration depends on `[propext, Classical.choice, Quot.sound]` only.

## API

### The tower (`PadicAlgCl` namespace, upstream names kept)

```
cyclotomicTower p n                        : IntermediateField ℚ_[p] (PadicAlgCl p)   -- ℚ_p(μ_{p^n})
mem_cyclotomicTower_of_pow_eq_one          : ζ ^ p ^ n = 1 → ζ ∈ cyclotomicTower p n
cyclotomicTower_mono                       : Monotone (cyclotomicTower p)
exists_isPrimitiveRoot_pow p n             : ∃ ζ, IsPrimitiveRoot ζ (p ^ n)
cyclotomicTower_eq_adjoin p n hζ           : cyclotomicTower p n = adjoin ℚ_[p] {ζ}
mem_fixingSubgroup_cyclotomicTower_iff     : σ ∈ (cyclotomicTower p n).fixingSubgroup ↔ σ ζ = ζ
mem_fixingSubgroup_cyclotomicTower_iff_dvd : (σ ζ = ζ ^ b, n ≤ N) → (σ ∈ … ↔ p ^ n ∣ b - 1)
pow_apply_eq_pow_pow                       : σ ζ = ζ ^ a → (σ ^ j) ζ = ζ ^ a ^ j
map_mem_cyclotomicTower                    : y ∈ cyclotomicTower p n → σ y ∈ cyclotomicTower p n
finiteDimensional_cyclotomicTower          : FiniteDimensional ℚ_[p] (cyclotomicTower p n)  [instance]
finrank_cyclotomicTower p n (0 < n)        : finrank ℚ_[p] (cyclotomicTower p n) = (p-1) * p^(n-1)
finrank_cyclotomicTower_eq_totient p n     : finrank ℚ_[p] (cyclotomicTower p n) = (p ^ n).totient
finrank_cyclotomicTower_succ p n (0 < n)   : finrank (… (n+1)) = p * finrank (… n)
finrank_cyclotomicTower_shift_succ p m     : finrank (… (m+3)) = p * finrank (… (m+2))
pow_p_sub_one_of_dvd                       : v_p(a-1) = k ≥ 2 → v_p(a^p - 1) = k + 1
pow_mem_and_not_mem_fixingSubgroup         : the degree-p step on fixing subgroups
finrank_cyclotomicTower_and_pow_mem_fixingSubgroup : the two above, packaged
cyclotomicTower_shift_hypotheses           : hmono ∧ hfin ∧ hstab ∧ hdeg ∧ hcyc for Km m = ℚ_p(μ_{p^{m+2}})
```

`cyclotomicTower_shift_hypotheses` is every tower hypothesis of Tate's normalised-trace
construction; the one remaining hypothesis there, the estimate on `‖∑_{i<p} σ^i y‖`, is not
proved here.

Note for `CloudB3W11TateTrace`: its `rootField p n` is *definitionally* `cyclotomicTower p n`
(both are `IntermediateField.adjoin ℚ_[p] {ζ | ζ ^ p ^ n = 1}`), so
`rootField p n = PadicAlgCl.cyclotomicTower p n` holds by `rfl`. Its K-relative
`CloudB3W11TateTrace.cyclotomicTower p K` is a different object and does not collide.

### The infinite image and the algebraic case (`ZInQ.Contrib.CloudB3W11Cyclotomic`)

```
cycHom p                                   : GQp p →* ℤ_[p]ˣ            -- χ, as a homomorphism
cycHom_apply                               : cycHom p σ = cyc p σ        -- rfl
cyc_zpow_eq_one_iff_cycPow_eq_one          : cyc p σ ^ i = 1 ↔ cycPow p σ i = 1
exists_mem_fixingSubgroup_cyc_zpow_ne_one  : i ≠ 0 → ∃ σ ∈ K.fixingSubgroup, cyc p σ ^ i ≠ 1
exists_mem_fixingSubgroup_cycPow_ne_one    : i ≠ 0 → ∃ σ ∈ K.fixingSubgroup, cycPow p σ i ≠ 1
infinite_image_cyc                         : (cycHom p '' K.fixingSubgroup).Infinite
eq_zero_of_exists_pow_cyc_zpow_eq_one      : (∃ n > 0, ∀ σ ∈ K.fixingSubgroup, (cyc p σ ^ k)^n = 1) → k = 0
coe_eq_zero_of_forall_mem_fixingSubgroup_cycPow_smul_cpAct_eq
tateTwistInvariants_algebraic              : H-120 for x in the image of ℚ̄_p → ℂ_p
```

(`K : IntermediateField ℚ_[p] (PadicAlgCl p)` with `[FiniteDimensional ℚ_[p] K]` throughout.)

## Status against H-120

Proved: the target for every `x ∈ ℂ_p` that is algebraic, i.e. in the image of `ℚ̄_p`.

Not proved: the target itself. The gap is exactly

```
∀ p K i, i ≠ 0 → ∀ x : ℂ_[p],
  (∀ σ ∈ K.fixingSubgroup, cycPow p σ i • cpAct p σ x = x) → ∃ y : PadicAlgCl p, x = (y : ℂ_[p])
```

— the twisted invariants are carried by `ℚ̄_p`. **Density of `ℚ̄_p` in `ℂ_p` does not supply
it**: the twisted invariants form a closed `ℚ_p`-subspace, and a closed subspace meeting a
dense subset only in `0` need not be `0`. That input is Tate's normalised trace on the
cyclotomic tower, owned by C; its tower hypotheses are the lemmas above.

A local verification scratch file, not part of the contribution, proves that
`tateTwistInvariants_algebraic` plus that one statement gives the target verbatim
and carries a `rfl` statement lock against the real constant. `#check`/`#print`
live only in that local scratch file.
