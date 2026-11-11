# el-k3: points on the Kummer surfaces X_{β,θ} from their geometry

Branch `wip/el-k3` (from `origin/wip/cr3-maps`). Scripts and the step log: `scratch/el-k3/`.
No Lean was run, and nothing under `ZInQKernel/` or `blueprint/` was edited.

Marks:
- **VERIFIED**: exact computation (script named) or a derivation checked against the sources.
- **STANDARD**: a published theorem, with a reference.
- **SPECULATIVE**: an idea or heuristic that is not proved.

## 0. Verdict

- **The angle does not eliminate CR₃. Chance: very low.**
- **Setting.** For a multiplier `m`, `Φ(B)` holds iff `X_{β,θ}(ℚ) ≠ ∅` (cr3-map-needs L5,
  cr3-map-literature R1/R3), where
  `X_{β,θ} : w² = θ f(s) f(t)`, `f(s) = β²s⁴ − 1`.
  `X_{β,θ}` is a twisted Kummer surface of the product of two twists of `y² = x³ + 4x`, which has CM by `ℤ[i]`.
- **The strongest obstruction (VERIFIED, §2):**
  - For every admissible `θ ≠ 1`, the classes defined over ℚ, `NS(X̄)^G`, form a lattice of
    rank 8. The lattice does not depend on `θ`.
  - All its intersection numbers are even, and all self-intersections are `≡ 0 (mod 4)`.
- **Consequences:**
  - no smooth rational curve over ℚ;
  - no genus-one fibration over ℚ with a section;
  - the generic fibre of every genus-one fibration over ℚ has even index, so every fibre is a
    2-covering and its points are a Sha[2] (Hasse-principle) question, which is exactly CR₃;
  - `H¹(G, NS) = 0` (no algebraic Brauer–Manin obstruction);
  - no deck-invariant rational curve over ℚ (§3). Such curves would be conics `w² = θh(z)`,
    soluble from local data by Hasse–Minkowski, and they are the only θ-uniform source of points.
- **Heights.** On realistic inputs the points have log-height `≳ 10⁷` (BSD heuristic, §4), so
  points can only come from existence theorems.

## 1. Objects (VERIFIED)

- **Roots.** `r₁..r₄ = 1/√β, −1/√β, i/√β, −i/√β`. The Galois group of `ℚ(i, √β)` is `V4` when
  `β ≠ ±1, ±2`, which always holds since `|β| ≡ 7 (mod 8)`.
- **The double cover.** `Y = Bl₁₆(ℙ¹×ℙ¹)` at the points `(r_a, r_b)`. `X → Y` is the double
  cover branched on the eight disjoint lines `L_a (s = r_a)` and `M_b (t = r_b)`.
  - Nodes: `N_ab = π⁻¹E_ab`.
  - Tropes: `T_a`, `T′_b`.
  - Deck involution: `w ↦ −w`.
- **Graph curves.** The CM and 2-torsion symmetries give the eight Möbius maps
  `φ ∈ D4 = {λs, λ/(βs) : λ⁴ = 1}`, which preserve the roots.
  - On the graphs, `f(φ(s)) = k_φ f(s)` with `k = 1` or `k = −β²`.
  - So `π⁻¹{t = φ(s)}` splits into two curves `G_φ^±`:
    - `w = ±√θ f(s)` for `φ = λs`, defined over `ℚ(λ, √θ)`;
    - `w = ±iβ√θ f(s)/(βs)²` for `φ = λ/(βs)`, defined over `ℚ(λ, √−θ)`.
- **Equivalence with Φ.** `θ f(s)f(t) ∈ ℚ*²` iff `Loc(N, β) ∧ Loc(Nθ, β)` with `N = βf(s)`. The
  value `s = ∞` is the torsion first curve. Signs are absorbed by `f(1/(βs)) ≡ −f(s)`.

## 2. Route 1: an elliptic fibration over ℚ with a section, or an odd multisection

- **Replacement statement.** None is needed. This route would prove the following, for each DL multiplier:
  ```
  ∀ β θ, AdmissiblePair β θ → ∃ s t w : ℚ, w ^ 2 = θ * (β^2*s^4 - 1) * (β^2*t^4 - 1)
  ```
  This is W2 of cr3-map-needs, which implies PC.
- **Soundness.** Unchanged: `polePoly` and Lemma 5.1 are untouched.
- **Completeness.** It would come from a section `P¹ → X` defined over ℚ, or from a ℚ-divisor of
  odd degree on the generic fibre.
- **Computation** (`ns_lattice.py`, `ns_invariants.py`; VERIFIED, exact):
  - The 40 curves `N_ab, T_a, T′_b, G_φ^±` have a Gram matrix of rank 20 and span a lattice of
    discriminant −16. That equals `−disc T(Km(E×E))` with `T = ⟨4⟩⊕⟨4⟩` (STANDARD:
    `T(Km A) = T(A)(2)`, Shioda–Inose 1977). So the 40 curves generate `NS(X̄)`.
  - The intersection numbers `G·G` come from solving `φ(s) = ψ(s)` and matching the signs of `w`.
    There is no tangency at blown-up points because `D4` is finite.
  - Galois acts through `(ℤ/2)³ = ⟨σ_β, σ_i, σ_θ⟩`, isometrically.
- **Outcome.** `NS(X̄)^G` has:

  | θ class | rank | disc | values |
  | --- | --- | --- | --- |
  | `θ ∉ ⟨−1, β⟩ℚ*²` (every admissible `θ ≠ 1`) | 8 | −1024 | `D² ≡ 0 (4)`, `D·D′` even |
  | `θ = β` | 8 | −1024 | the same |
  | `θ = ±1` | 9 | 1024 | odd values; the `G_φ^±` are defined over ℚ |

- **Consequences** (`Pic X ⊆ NS(X̄)^G`):
  - there is no ℚ-class of square −2, so no smooth rational curve and no section over ℚ;
  - `D·F` is even for every ℚ-divisor `D` and every ℚ-fibre class `F`. The closure of a degree-1
    divisor on a generic fibre would be a ℚ-divisor with `D·F = 1`. So every genus-one fibration
    over ℚ has generic fibre of even index, and its fibres are 2-coverings;
  - every curve over ℚ has odd arithmetic genus;
  - the lattice does not depend on θ. Any construction read off the Picard lattice is uniform in θ,
    so it cannot select the θ for which points exist.
- **Brauer group** (`ns_h1.py`; VERIFIED). `H¹(Gal(K/ℚ), NS(X̄)) = 0` for admissible `θ ≠ 1`, and
  `ℤ/2` for `θ = ±1, β`. So `Br₁/Br₀ = 0`.
  - Since X is everywhere locally soluble (descent-alt §4.2(i)), only a transcendental
    Brauer–Manin obstruction could prevent points.
  - Points do exist for DL-admissible pairs: by TYZ+GZ (CR₃), the DL slot curves supply them.
    That is a theorem, but not an elimination.
- **Verdict.** Impossible as stated (VERIFIED obstruction).

## 3. Route 2: rational curves over ℚ plus Hasse–Minkowski

- **Replacement statement.** For each β, a curve `Γ_β ⊂ Y` defined over ℚ with `π⁻¹Γ_β`
  irreducible and rational. Its θ-twist is the conic `w² = θh_β(z)`. Then
  `∀ admissible θ, ConicLocallySoluble (θ h_β)` would give X-points by Hasse–Minkowski. That
  theorem is local and elementary, and could be proved in Lean.
- **Soundness.** Unchanged.
- **Completeness.** It would follow from (θ1)-(θ4) if the conic's Hilbert symbols matched them.
- **Lemma** (VERIFIED, derivation plus `caseB_parity.py`). Let `R ⊂ X_{β,θ}` be an irreducible
  curve of geometric genus 0 defined over ℚ, and `Γ = π(R)`.
  - (B) If `R` is deck-invariant, then `R̃ → Γ̃ ≅ ℙ¹` has exactly two branch points. These are
    the branches of `Γ` that meet `B = ΣL + ΣM` with odd multiplicity, and they form a Galois
    orbit, so they lie on `{L₁,L₂}`, `{L₃,L₄}`, `{M₁,M₂}` or `{M₃,M₄}`.
    - Multiplicities are constant on the six Galois orbits of nodes, so
      `Γ·L_c ≡ b − Σ_d m_cd` and `Γ·M_d ≡ a − Σ_c m_cd` take equal parity on all eight lines.
    - Enumerating all `2⁸` patterns finds no admissible one. **Case B never occurs over ℚ.**
  - (A) Otherwise `R ≠ deck R`, both are defined over ℚ, and `θ f(s)f(t)|_Γ ∈ ℚ(Γ)*²`. So `Γ`
    determines θ. Finding such a `Γ` for a given θ is as hard as finding a point.
- **Special values of the Picard lattice.** Only `θ ∈ ⟨−1, β⟩`. Admissibility leaves only
  `θ = 1`, the trivial witness. L7/L8 limit that to finitely many `(q, m)` per B: the genus of
  `θ(q) = 1`, and integral points on the hyperbola for `m = m₀k²` with bit-bounded `k`.
- **Verdict.** Impossible as stated (case B); case A is circular. Very low.

## 4. Route 3: explicit points on realistic inputs

- **Experiments** (VERIFIED computations):
  - **E1** (`e1_points.py 1 3 10 100000`): toy pairs satisfying (θ1)-(θ4).
    - `(β, θ) = (199, 257)`: the smallest point has height 74 (`s = −7`, `t = −11/74`).
    - Two pairs with `θ = 1889, 11953`: no point with `s₀` of height ≤ 10 and `t` of height ≤ 10⁵.
  - **E2** (`e2_realistic.py 7 12 3 1000`, `out_e2.txt`): 12 admissible `B` from the rs-pole §4.1
    sampler. θ has 22–25 digits.
    - On the one-curve fibre `C_{βθ}`, PARI `ellrank` gives Selmer rank 1 in 12/12 and finds no
      point in 12/12. PARI's lower bound 1 is the Selmer-parity value; it also prints `[1,1,0,[]]`
      for `d = 157`.
    - A naive search on X found nothing.
    - The exact Selmer certificate holds for the one-curve case at the first `m` in 0/12, so DL
      needs auxiliary primes.
- **Height estimate** (SPECULATIVE, BSD with `L′(1) ≈ 1`):
  - The generator of `C_{βθ}` has `ĥ ≈ 16/(Ω·Πc_p) ≈ 10^7.2 … 10^11.7`.
  - A point of X of height H gives an explicit point of log-height `O(log H)` on some rank-one
    curve `C_{nθ}` with `nθ ≥ θ`. So `log H ≳ 10⁷`.
  - A ℚ-conic with coefficients polynomial in `(β, θ)` would have a point of log-height
    `O(log θ)` (Legendre/Holzer bound, STANDARD).
  - Hence no explicit rational-curve construction can reach these points, independently of §3.
- **Verdict.** Points exist (by CR₃ itself) but only through existence theorems. Very low.

## 5. Route 4: isogenies and CM by ℤ[i]; Hasse principle for Kummer surfaces

- **Isogenies** (VERIFIED as a remark). Rational maps between Kummer surfaces induced by
  isogenies of the factors (the 2-isogeny, `1 + i`) send rational points forward only. Producing
  a point on X needs a point on the source, which is the same question.
- **CM symmetries.** `ℤ[i]` contributes exactly the `D4` graph curves of §1. They are defined
  over `ℚ(i, √±θ)` and are included in §2.
- **Hasse principle.**
  - Skorobogatov–Swinnerton-Dyer (Adv. Math. 2005) and Harpaz–Skorobogatov (ANT 2016) prove it
    for such Kummer surfaces conditionally on finiteness of Ш (STANDARD; see
    cr3-map-literature B4).
  - With `Br₁ = Br₀` (§2), "Brauer–Manin is the only obstruction for K3 surfaces"
    (Skorobogatov's conjecture, open) would also suffice.
  - Both are as deep as CR₃.
- **Verdict.** Very low.

## 6. Notes

- **(θ3) is the local condition at ℓ.** At `ℓ | θ` with `ℓ ≡ 1 (mod 4)` and `(β/ℓ) = −1`,
  `v_ℓ(f(s))` is even for every `s ∈ ℚ_ℓ`, so `X(ℚ_ℓ) = ∅` (VERIFIED). This is the local
  obstruction that the task statement mentions; admissibility removes it.
- **The manuscript's family is not checked.** For `w² = θ g_β(t₁)g_β(t₂)` (`E_ℓ`, non-CM),
  the root field `ℚ(√β, √−3β)` has the same `V4` orbit shape, and the argument of §3 should
  carry over (SPECULATIVE, not checked). The Lean proof uses the congruent family (Route K).

## Scripts (`scratch/el-k3/`, PARI via `~/pyenv/bin/python`)

| Script | Purpose | Time |
| --- | --- | --- |
| `ns_lattice.py` | NS(X̄): 40 curves, Gram matrix, Galois action → `ns_data.json` | ~1 min |
| `ns_invariants.py` | `NS^G` for θ generic, ±1, β → `ns_inv.json` | ~1 min |
| `ns_h1.py` | `H¹(G, NS)` | seconds |
| `caseB_parity.py` | the mod-2 enumeration of §3 | instant |
| `e1_points.py` | toy-pair point search | 40 s |
| `e2_realistic.py` | realistic inputs: ellrank, BSD estimate, naive search | ~2 s |
