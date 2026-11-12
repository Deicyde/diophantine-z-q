# glue-c10-link — the trace link of C10

**Main result.** The trace link `c_p = ½·β(σ)⁻¹a_σ·tr α_σ` is proved in Lean
(`GlueC10Link.trace_link`, `scratch/glue-c10-link/Link.lean`), over the descent glue's `rhoRep`
and `MatrixUnits2` and pkg-I3's `AbVar`, `V_ℓ` and `homT`. It discharges the trace hypotheses
`hr₃, hr₅` of `GlueC10.c10`:
- `c10_of_trace_link` applies `c10` verbatim, with `r_ℓ` the descended representation and
  `c := a_f`;
- `c10_of_squares` goes further and splits the input from `A` into three squares.

The only leaf added is Mumford §19 Thm 4 (`CharPolyIndepOfEll`), which is already in the
project. No `sorry`. All seven main theorems show only `propext`, `Classical.choice` and
`Quot.sound`. VERIFIED: `lake env lean`, no errors and no warnings.

**What compiles.**
- `tr ρ = 2·tr r`, from the matrix units. This was the assumed `h2` of `trace_half`.
- `tr ρ = β⁻¹a·tr T`.
- The ℓ-independent integer trace of `α' ∈ End(Ā)` on `E ⊗ V_ℓ(Ā)`. Finiteness comes from
  `dim V < ∞`, so `TateModuleFree` is not needed.
- `FrobCompare` (`T(σ)` conjugate to `V_ℓ(α')/N`) and the link.
- `c10_of_trace_link` and `c10_of_squares`.
- `FrobCompare` from three squares: the descent instantiation `T(σ) = μ_σ∘σ`, the
  Serre–Tate/Frobenius square and the Néron square. `μ'`, `F` and `μ̄'` are genuine pkg-I3
  `Hom`s.
- A non-vacuity example for `FrobCompare`.

**Finding.** The link gives an element `x_g ∈ C` for each Frobenius element, and `x_g = a_f(p)`
follows through `ι₅`. So no argument is needed that `c_p` is independent of the lift `σ` or the
place `v`. `3, 5 ∈ S` is now an explicit hypothesis.

**What remains from the surface `A`** (docs/research/glue-c10-link.md §3):
1. The descent instantiation at 3 and 5: `T_ℓ`, the projective relation, and matrix units
   commuting with `T_ℓ`.
2. The squares `hSq`: abstract isomorphisms `σ_*`, `red`, `red'`, `Ψ` with Serre–Tate
   specialization, Frobenius on reduced points, and the Néron reduction of `μ'`. Making these
   the actual maps needs `{}^σA`, the special fibre as an `AbVar` and the relative Frobenius,
   none of which is in Mathlib.
3. Continuity and semisimplicity of `r₃`.
4. The B1-B3 scalar identities in `C`.

Not from `A`: C9 (`h₅`), Eichler–Shimura (`hρ₃, hρ₅`), the modular side's continuity and
semisimplicity, Chebotarev and Brauer–Nesbitt.

**Integration.** `Link.lean` imports only built `ZInQKernel.HDecomp` modules and can move to
`ZInQKernel/HDecomp/C10/Link.lean` unchanged.
