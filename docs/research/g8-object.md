# g8-object: G8's `r_ℓ` as a Lean object, and the G8-G16 interface restated over it

Task g8-object, 2026-11-13. Lean files:
- `scratch/g8-object/part_obj.lean`: the object and the G15 restatement.
- `scratch/g8-object/part_link.lean`: the full interface and the restated `GluePieces2` field.
- `scratch/g8-object/part_split.lean`: `TmWild` split into a closed part, a `G_L`-clause and a
  statement about `A/L` (§4.1).
- `scratch/g8-object/part_ltcopy.lean`: a verbatim copy of three linked-tate Props.

`scratch/g8-object/build.sh` assembles these into one checked environment,
`scratch/g8-object/G8Object.lean`, together with verbatim copies of g0-mod-field, g14-trace,
g15-ram, g0-mod-galois' definitions and g0-assemble's `LinkedTateData`. `build_dev.sh` assembles
the small development file `Dev.lean`. The results log is `scratch/g8-object/log.md`; compiler
output is in `obj.out` and `dev.out`.

Marks: **VERIFIED** = compiled, or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = judgement. **UNVERIFIED** = a theorem number recalled without a source (there
is no network).

## 1. Result

**G8's representation is now a Lean object.** `G8Object.DescData.r : GaloisRep ℓ 2` is built from
G7's output (`G0Galois.G7Out`) and `dim = 4` (from T26). It is `ρ_ℓ|_{e₀₀V}` in a chosen basis,
the construction of g0-mod-galois' `g8Matrix_of_burnside`, now given as a definition.

**The G8-G16 interface is restated over this object, and each restated statement is proved
true of the construction from Props on G7's data.**

**`G15RamG` is proved for the constructed `r_ℓ`** from g15-ram's `g15RamG_of_localData`. g15-ram's
`LocalData` (a predicate on a bare `r`) is replaced by `LocalDataG`, a predicate on the descent
data `(Tm, a, β)`. `LocalDataG` implies `LocalData` for *every* `r` that carries G8's
intertwining, and the proof is in Lean.

VERIFIED: `lake env lean scratch/g8-object/G8Object.lean` (6 835 lines) exits 0 in 2 min with
0 errors and no `sorry`. All 56 `#print axioms` reports are `[propext, Classical.choice,
Quot.sound]`. They cover the 25 new theorems (§6) plus the copied sources' own reports.

Main theorems (all in namespace `G8Object`):

```lean
-- the object (part_obj.lean §A)
structure DescData (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] where
  Tm c ε a β u;  g7 : G0Galois.G7Out A ℓ Tm c ε a β u;  dim4 : finrank (Vb A ℓ) = 4
def DescData.r (D : DescData A ℓ) : GaloisRep ℓ 2            -- G8's r_ℓ
theorem DescData.intertwines : G0Galois.Intertwines (GlueDescent.rho D.Tm D.a D.β) D.r.mat D.e
theorem DescData.g8Out (hS hF hT hH hSS) (hB : BurnsideAbsIrred) :
    G0Galois.G8Out A ℓ (GlueDescent.rho D.Tm D.a D.β) D.r

-- G15 on the object (part_obj.lean §D)
theorem g15RamG_obj (M : ModObj A) (u : ℚ)
    (h5 : ∀ p (hp : p.Prime), p ≠ 5 → LocalDataG p M.D5.Tm M.D5.a M.D5.β)
    (h3 : LocalDataG 5 M.D3.Tm M.D3.a M.D3.β)
    (h2 : G2Out K (ramSet S_mul u)) (h35 : G3Out A 5 (ramSet S_mul u))
    (h33 : G3Out A 3 (ramSet S_mul u)) :
    G0ModNewform.G15RamG M.toModData u

-- the whole G12-G16 interface on the object (part_link.lean §E)
theorem interface_obj (hDF hM hS hF hT hH hSS hB) (Lk : LinkedObj A) (u : ℚ)
    (h12 : GalG12Out Lk.D5.r) (h5 h3 : LocalDataG …) (h2 h35 h33) :
    ∃ M : ModObj A, M.D5 = Lk.D5 ∧ M.D3 = Lk.D3 ∧ G12Spec M.toModData ∧
      G14TraceCompat M.toModData ∧ G15RamG M.toModData u
theorem modularConstituent_tail_obj (lv hJac hX hSw hL8 hAd hDF hM hS hF hT hH hSS hB)
    (Lk : LinkedObj A) (u) (h12) (h5 h3 h2 h35 h33) :
    ∃ N J, 0 < N ∧ IsJ1 N J ∧ (N : ℝ) ≤ Q_D·M² ∧ CommonConstituent A (J_K)

-- the restated GluePieces2 field (part_link.lean §F)
def LinkedTateObj : Prop          -- TateBridge35's data + LocalDataC on them
theorem linkedTateData_of_obj (hM : CharPolyIndepOfEll) (hO : LinkedTateObj) :
    HSyn.G0AssembleMod.LinkedTateData                 -- g0-assemble's field `linkedTateData`, verbatim
theorem linkedTateCore_of_obj (hO : LinkedTateObj) : HSyn.LinkedTate.LinkedTateCore
theorem linkedTateCoreDR_of_objDR (hO : LinkedTateObjDR) : HSyn.LinkedTate.LinkedTateCoreDR
theorem tateBridge35_of_objDR (hO : LinkedTateObjDR) … : ⟨TateBridge35's conclusion⟩

-- split form (part_split.lean; needs G4's bound [L:ℚ] ≤ D, which G7Data lacks: §4.1)
def LinkedTateObjS : Prop        -- TateBridge35's data + OnL + LocalDataS (no ℓ-adic operator)
theorem linkedTateDataD_of_S (hM : CharPolyIndepOfEll) (hS : LinkedTateObjS) : LinkedTateDataD
```

## 2. The object

`DescData A ℓ` bundles G7's output at `ℓ`:
- the operators `Tm σ = μ_σ ∘ σ` on `ℚ̄_ℓ ⊗ V_ℓ(A)`;
- the cocycle `c`, the scalars `a`, the sign cocycle `ε` and the cochain `β`;
- the matrix units `u`;
- `G0Galois.G7Out` (verbatim copy) and `finrank (Vb A ℓ) = 4`.

`DescData.ofG7Out hT …` builds the object from `G7Out` and T26 `TateModuleFree`. It uses
`finrank_Vb_of`, which is g0-mod-galois' argument in `g8`.

From these data (all VERIFIED):
- `D.rho` is `GlueDescent.rhoRep`, i.e. `ρ_ℓ(σ) = β(σ)⁻¹ a_σ Tm(σ)` (N5 L725-727).
- `D.rho_resQ`: `ρ` is the Tate action on `G_{L'}`.
- `D.basis` is a basis of `W = e₀₀ V`, which has dimension 2.
- `D.rW` is `ρ|_W`, and `D.m` gives its matrices.
- **`D.r := ⟨D.m.toHomUnits, D.continuous_toHom⟩`.** Continuity comes from `G7Out`'s weak
  continuity, through the functionals `b.coord i ∘ e₀₀`.
- `D.e` is `splitEquiv` followed by the basis.
- `D.intertwines` is G8 (i) on all of `G_ℚ`.
- `D.g8Out` is the whole of `G0Galois.G8Out`. It uses C2 (`PkgI3.C2_absolutelyIrreducible`,
  whose inputs are the leaves R9a, R9b, T26, T6 and glue-ssbc's `SemisimpleBaseChange`) and
  Burnside (`G0Galois.BurnsideAbsIrred`, a `GluePieces2` leaf).

**Every `r` with G8's output is pinned where it matters (VERIFIED).**
- `mat_eq_scalar_of_intertwines`: if `e` intertwines `ρ` with `r ⊕ r` and `ρ(g) = c·1`, then
  `r(g)` is the scalar matrix `c`.
- G11 and G15 only use values of `r` at elements where `ρ` is a scalar.
- So every statement below holds for every `r` that carries G8's intertwining, not only for
  `D.r`.
- `g11_of_intertwines`: G11 (`G0Galois.G11Out T r`) follows from `G2Out` and `G3Out` for any such
  `r`.

## 3. The restatements, each with its reason

| # | was | now | relation (VERIFIED in Lean) | reason |
|---|---|---|---|---|
| R1 | g0-mod-newform's `ModData` with free fields `r₅ r₃`; `G12Spec D`, `G14TraceCompat D`, `G15RamG D u` for arbitrary `D` | `ModObj A`: embeddings plus `D5 : DescData A 5`, `D3 : DescData A 3`. `M.toModData` has `r₅ = D5.r` and `r₃ = D3.r`. The three predicates are unchanged and are applied to `M.toModData` | `interface_obj` proves all three on `M.toModData`. `modularConstituent_tail_obj` discharges the tail's hypothesis `∃ D, G12Spec D ∧ G14TraceCompat D ∧ G15RamG D u` with `D = M.toModData` | g15-ram showed that `G15RamG D u` is false for arbitrary `D`. g14-trace showed that `G14TraceCompat` can fail when `r₃` is not linked to `r₅`. The `r_ℓ` must be the constructed ones. The embeddings `i, ιC, ι₅, ι₃` stay as data: they are choices, and `interface_obj` provides suitable ones |
| R2 | g15-ram's `LocalData p r` (on a bare `r`: `TwistShape p r F β_loc ∧ TwistUpper`) | `LocalDataG p Tm a β`, on G7's data. It consists of `TmWild` (`a = 1`, `Tm = 1` on `G_F ∩ P_p` through `decomp`) and `BetaUpper` or `BetaTame` (`β = 1` on `G^t_{ℚ_p} ∩ G_F`, `t > U₀`, resp. on `G_F ∩ P_p`), with the same `F`, the same `e(F)` bounds and the same split at `p ≤ D` | `localData_of_intertwines`: `LocalDataG → LocalData p r` for every `r` intertwined with `ρ = β⁻¹ a Tm`, with local twist `σ ↦ β(decomp σ)⁻¹` (`twistShape_of_tmWild`) | `LocalData` quantified over the bare `r`, so it could not be split further. g15-ram §3: "`r = β⁻¹·(Tate action)` cannot yet be stated". It can now. `TwistShape` becomes a statement about `Tm` and `a`, and `TwistUpper` becomes a statement about the cochain `β` |
| R3 | g0-assemble's `GluePieces2` field `linkedTateData : LinkedTateData` (row 28 of its table): ∃ data at 5, 3 with `G7Out`, and for **all** `r₅ r₃` with `G8Out` and all `i ιC ι₅` there is `ι₃` with `G14TraceCompat ∧ G15RamWild` | `LinkedTateObj`: g14-trace's `TateBridge35` data (one pair `aQ, βQ : G_ℚ → ℚ̄`, embeddings `j₅, j₃`, `G7Out` at 5 and 3 for `j_ℓ ∘ aQ`, `j_ℓ ∘ βQ`, `FrobTraceLink`, `ιC ∘ βQ = G7Data's β`), together with `LocalDataC` on these data (`ℓ = 5` at `p ≠ 5`, `ℓ = 3` at `p = 5`) | `linkedTateData_of_obj`: T7 + `LinkedTateObj` → `LinkedTateData`, the verbatim g0-assemble text. `linkedTateCore_of_obj`: `LinkedTateObj` → linked-tate's `LinkedTateCore`. `tateBridge35_of_objDR`: on fibre contexts, the data contain `TateBridge35`'s conclusion | `LinkedTateData` *assumed* the conclusions about `r₅`, `r₃`. `LinkedTateObj` assumes only statements about G7's data, and the conclusions are proved (G14 by g14-trace, G15 by g15-ram plus this task) |
| R4 | `LocalDataG`'s `β`-clauses on the `ℓ`-adic `j_ℓ ∘ βQ` | `LocalDataC`: `BetaUpperC`, `BetaTameC` on `G7Data`'s own `β : G_ℚ → ℂ^×` | `localDataG_of_C` (uses `ιC ∘ βQ = β` and the injectivity of `ιC` and `j_ℓ`) | the `β`-clauses become Props on one existing Lean object, `G7Data`'s cochain, independent of `ℓ` |

**Nothing is weakened; the replacement hypotheses are logically stronger.**
- R1 keeps the three predicates verbatim. Only the domain changes, from arbitrary `ModData` to
  the constructed object.
- R2, R3 and R4 replace a hypothesis by one that provably implies it (the arrows above). So each
  new hypothesis is *logically stronger* than the one it replaces. What it gains is content that
  is more primitive: statements about G7's data rather than about `r`, with the ramification
  theory proved. A stronger hypothesis can be false where the old one was true. §4.1 has such a
  case, caught by review and repaired: `LinkedTateObjS` without the premise `[L:ℚ] ≤ D`.
- The new hypotheses are true for Glazer's construction (§4, SPECULATIVE) but not for arbitrary
  `G7Out` data.
- **Non-vacuity (VERIFIED, weak):** `localDataG_triv` shows that `LocalDataG` holds for
  `Tm = 1`, `a = β = 1` with `F = ℚ_p`. This only shows `LocalDataG` is satisfiable on its own:
  `Tm = 1` is not compatible with `G7Out`'s `Tm = tate` on `G_{L'}`. Joint satisfiability with
  `G7Out` is not shown in Lean.

**`LocalDataG` implies linked-tate's `RhoRamWild` (VERIFIED).**
`rhoRamWild_of_localDataG` proves `LocalDataG p Tm a β → RhoRamWild p (β⁻¹ a Tm)`. The proof uses
g15-ram's closed local-field theorems:
- `UpperBreakFix`, from T20 and T21 through `ladicDVRModelZp`;
- `upperWild`;
- `wildFixTame`.

`RhoRamWild` is clauses (i)-(ii) of G15 for `ρ_ℓ` itself, so it is the conclusion form.
`LocalDataG` isolates what is left once the ramification theory is done: the behaviour of `Tm`,
`a` and `β` on `G_F` for one explicit finite `F`.

## 4. What remains (named Props), and why each is true of the construction

The remaining glue on this route is `LinkedTateObj` (or `LinkedTateObjDR`). It consists of:

1. **g14-trace's `TateBridge35` data**:
   - `G7Out` at 5 and 3 with linked scalars;
   - `FrobTraceLink`;
   - `ιC ∘ βQ = β`.

   This is unchanged from g14-trace (`tateBridge35_of_objDR`); g14-trace §2 explains why it is
   true.
2. **`TmWild p Tm_ℓ (j_ℓ ∘ aQ) F`** (glue). This step combines G7's `G_L`-clause, R6 and D2.
   N5 L814-822 at `p ≤ D`; L848-850 at `p > D`.
   - `F` is the Galois closure of `L_v(A[3])` (of `L_v(A[5])` if `p = 3`) at `p ≤ D`, and of
     `L_v` at `p > D`. So `F` contains `L_v`, and `decomp(G_F) ⊆ G_L`.
   - On `G_L`, `DescentDatum` gives `μ_σ = 1` and `a_σ = 1`, so `Tm` is the Galois action of `A/L`.
   - At `p ≤ D`, Raynaud (R6, `PkgI2.RaynaudCriterion`) makes `A` semistable over `F`. Wild
     inertia then acts trivially on `V_ℓ(A)` for `ℓ ≠ p` (D2, `PkgI2.D2_fixed_of_raynaud`).
   - At `p > D`, N5 says "the surface has good reduction".

   **Finding (SPECULATIVE, a wording point in N5):**
   - For `p > R` with `p ∈ T = S ∪ supp M_S(u)`, good reduction of `A` over `L_v` is not
     evident.
   - The needed conclusion still holds by a different argument. Abelian surfaces with QM by a
     division quaternion algebra have potentially good reduction everywhere (STANDARD; e.g.
     Morita 1970, Jordan's thesis 1986; locators UNVERIFIED). The finite image of inertia then
     has order divisible only by primes `≤ 2g + 1 = 5` (Serre–Tate 1968, §2; UNVERIFIED
     numbering), so wild inertia acts trivially once `p > 5`.
   - This is not a defect in the target, only in N5's justification at large bad primes.
   - `TmWild` is a statement about G7's data, not about `r`. `G7Out` pins `Tm` and `a` only on
     `G_{L'}`, and `F` cannot contain `L'_v`, because `e(F) ≤ (DG₀)!` does not depend on
     `[L':ℚ]`. Linking `Tm` on `G_L` to the Tate module of `A/L` (TateBridge's
     "`Tm_ℓ` from `m_σ`", which `TateBridge35` also leaves out) is the content still missing.
3. **`BetaUpperC p β F U₀` (`p ≤ D`) and `BetaTameC p β F` (`p > D`)** (glue on `G7Data`'s
   `β`). This step combines D3 and T16 (N5 L832-844) and L848-851.
   - At odd `p`, `β|_{G_F}` is a character whose square `χ` is tame, and a pro-`p` group has no
     quotient of order 2 (`GlueConductor.char_trivial_of_odd_pgroup`).
   - At `p = 2`, local reciprocity with the upper numbering theorem (T16) applies, together with
     `(U^{e+1})⁴ = U^{3e+1}` (D3) and `max(4D², 3e) ≤ U₀`.

   The statement is unchanged from g15-ram's `TwistUpper`/`TwistTame`, now stated on G7's cochain.
4. **Existence of `F`** with `IsFinGal F` and `e(F) ≤ (DG₀)!` (resp. `p ∤ e(F)`). This is inside
   `LocalDataC`, as it was inside g15-ram's `SmallPrimeData`/`LargePrimeData`.
   - `[L_v(A[3]) : ℚ_p] ≤ D·G₀`, and a normal closure has degree at most the factorial
     (N5 L797-798, L814-815).
   - At `p > D`, `L_v` is tame and so is its Galois closure (STANDARD).

### 4.1 `TmWild` split further (part 3, `part_split.lean`; VERIFIED)

`TmWild` is the one clause that mixes the `ℓ`-adic operators with the local field. It is split
into three pieces.

- **`ContainsL p L F`**: `F ⊇ j(L)` for an embedding `j : ℚ̄ → ℚ̄_p` with
  `j(decomp σ x) = σ(j x)`.
  - This is a closed condition on the chosen `F`. Such a `j` exists: it is the embedding that
    `Field.absoluteGaloisGroup.map` chooses (g0-mod-newform's `decomp_spec`).
  - `decomp_mem_fixing` (proved): it gives `decomp(G_F) ⊆ Fix(L)`.
- **`OnL L A Tm a ψ`** (glue, independent of `p`; G7's `G_L`-clause after the Tate functor):
  through `resQ L`, `a = 1` and `Tm = ψ⁻¹ ∘ tate_{A/L} ∘ ψ` for an isomorphism
  `ψ : V_ℓ(A_{L'}) ≅ V_ℓ(A)`.
  - It belongs with `TateBridge35`: it is the "`Tm_ℓ` from `m_σ`" content on `G_L`.
  - Why true (SPECULATIVE in its Lean details): `DescentDatum` has `a = 1` and `m_σ = σ` on
    `G_L`.
  - `resQ L` uses the embedding `ℚ̄ → L̄` that Mathlib chooses. Its restriction to `L` may be a
    nontrivial automorphism `σ₀` of the Galois field `L`. Then `V_ℓ(A_{L'})` is identified with
    `V_ℓ(A^{σ₀})`, and the `L`-rational isogeny `μ_{σ₀} : A^{σ₀} → A` (`L` is the Hom field)
    makes it `G_L`-isomorphic to `V_ℓ(A)`. So `ψ` exists in either case, which is why it is
    existential.
- **`WildTateTrivial p L A ℓ F`** (glue on `A/L` alone): for `σ ∈ G_F ∩ P_p` and `σ_L` with
  `resQ L σ_L = decomp σ`, `tate_A(σ_L) = 1`. This is R6 + D2 at `p ≤ D`, and potential good
  reduction at `p > D` (item 2 above).
  - What remains is the transport of the kernel's `PkgI2.RaynaudCriterion` and
    `D2_fixed_of_raynaud`, which are stated over a field with a DVR `O`, to `LadicCond`'s picture
    `G_{ℚ_p} → G_ℚ`. g15-decomp's `ZInQ.Contrib.G15.Ladic` (`Lj j = ℚ_p(j L)`,
    `decompEquivLj`, `mem_ramSet_iff`) is the natural starting point (SPECULATIVE).

`tmWild_of_split` (proved, using g0-mod-field's `resQ_range`) gives `TmWild` from these three.
`LocalDataS p L A ℓ β` is `LocalDataC` with `TmWild` replaced by `ContainsL ∧ WildTateTrivial`.
It mentions only `G7Data`'s `L`, `A` and `β` and local fields: **no `ℓ`-adic operator**.
`LinkedTateObjS` is `TateBridge35`'s data, `OnL` for `Tm₅` and `Tm₃`, and `LocalDataS`, **for
G7 data with `[L:ℚ] ≤ D`**.

**Finding (review, VERIFIED by reading; repaired).** `G0ModField.G7Data` does not contain G4's
bound `[L:ℚ] ≤ D`. `G4Out` has it (`scratch/g0-mod-field/ModField.lean` L403), and the
consumers' Props quantify over every `G7Data`. Without that premise, `LinkedTateObjS` is false
(the reviewer's counterexample, checked against `G7Data`'s clauses):
- Take Glazer's data and enlarge `L` to `L·ℚ(ζ_{2^k})`, with the same `A` (base changed), `μ`,
  `ε`, `χ`, `β`, and `L' := L·L'₀`.
- Every `G7Data` clause still holds. `2 ∈ T`, and `[L':ℚ] ≤ Q_D·M` allows `2^{k−1}` far beyond
  `(DG₀)!`.
- `ContainsL` forces `F ⊇ j(L)`, so `e(F) ≥ 2^{k−1} > (DG₀)!`.

The premise `Module.finrank ℚ L ≤ ZInQ.heightD` was therefore added to `LinkedTateObjS`. The
theorems are now:
- `linkedTateObjD_of_S : LinkedTateObjS → LinkedTateObjD`;
- `linkedTateDataD_of_S : T7 → LinkedTateObjS → LinkedTateDataD`;
- `linkedTateDataD_of_objD`;
- `linkedTateObjD_of_obj`.

Here `LinkedTateObjD` and `LinkedTateDataD` are the texts of `LinkedTateObj` and of
g0-assemble's `LinkedTateData` with that premise added.

The unrestricted `LinkedTateObj` (and `LinkedTateData`, `LinkedTateCore`) are not shown false,
because there `F` is existential and need not contain `L`. But N5's truth argument for the local
clauses uses `[L_v:ℚ_p] ≤ D` and `decomp(G_F) ⊆ G_L`, so their truth for every `G7Data` is not
established. **Recommendation:** add `Module.finrank ℚ L ≤ heightD` to `G7Data`.
g0-mod-field's producer `g7OutUnr_of_g4Out` has the bound from `G4Out`. With that change,
`LinkedTateDataD` feeds `afterG7_of`.

So the remaining glue on the split route is:
- `TateBridge35` + `OnL`: the Tate functor on G7's descent datum, at `ℓ = 5, 3`, on `G_ℚ` and on
  `G_L`;
- `WildTateTrivial`: R6/D2 transported to `LadicCond`;
- `BetaUpperC`/`BetaTameC`: T16/D3 on `G7Data`'s `β`;
- the existence of `F`.

On the object route (`interface_obj`), the other inputs are:
- the leaves R9a, R9b, T26, T6, T7 and Burnside, and glue-ssbc's proved `SemisimpleBaseChange`;
- g0-mod-newform's `DirichletOfFinite` (a `GluePieces2` field);
- G12's output `GalG12Out D5.r`. g0-mod-galois' `g12` proves it for any `r` with `G8Out`,
  `G9Out`, `G10Out` and `G11Out`, from its `GaloisPieces`;
- G2 and G3 (`G2Out`, `G3Out`). These are proved from `G7Data` (`galoisG2Out_of_g7Data`) and are
  part of `ModelG3G6`, respectively.

## 5. Check against `GluePieces2` and `LinkedTateData`

- **`LinkedTateData` (the field `linkedTateData`) is implied (VERIFIED).** It is copied verbatim from
  `scratch/g0-assemble/parts/87_afterg7.lean` L27-123, with `LocalRamWild`, `G15RamWild`,
  `g15RamG_of_wild` and `ModelG3G6`. `linkedTateData_of_obj` proves it from T7
  (`TextbookLeaves.t7`) and `LinkedTateObj`. So in g0-assemble's `afterG7_of` the field
  `linkedTateData` can be fed by `linkedTateData_of_obj t.t7 gp2.linkedTateObj`, with
  that field replaced by `LinkedTateObj`. The field count stays 27. The new field is logically
  stronger, and its content is more primitive (statements on G7's data only). See §4.1 for the
  `[L:ℚ] ≤ D` caveat that applies to both the old and the new field.
- **linked-tate's `LinkedTateCore` and `LinkedTateCoreDR` (concurrent task) are implied
  (VERIFIED).** They are copied verbatim from its commit dae5b706 (`lt_95_dae5b706.lean`).
  - `linkedTateCore_of_obj` and `linkedTateCoreDR_of_objDR` prove them.
  - The existential data are the same, except that `LinkedTateObj` has one extra conjunct,
    `∃ ιC, ιC ∘ βQ = β`. Its `RhoRamWild` clauses are derived from `LocalDataC`.
  - So `LinkedTateObj` can replace `LinkedTateCore` in linked-tate's reduction.
  - linked-tate proves `LinkedTateCore` from the `DR` form, `FibreSimple` and `QMEndRank`. The
    same works with `LinkedTateObjDR`, by `linkedTateCoreDR_of_objDR`.
- **g14-trace's `TateBridge35` is contained (VERIFIED).** On every fibre context,
  `LinkedTateObjDR`'s data witness `TateBridge35`'s conclusion over g0-mod-field's copies
  `GaloisCopy.G7Out` and `G14Bridge.FrobTraceLink` (`tateBridge35_of_objDR`). The kernel accepts
  the verbatim copies by unfolding.
- **Environment.** The check is not just a textual comparison: all these Props live in one
  compiled file, `G8Object.lean`. It does *not* use g0-assemble's `Leaves.lean` copies of the
  kernel names, so the identification with `G0Assemble.lean`'s constants is by identical text,
  as in g14-trace. The texts are produced by `sed` from the source files, so they are verbatim by
  construction (VERIFIED: `build.sh`).

Assembly notes (VERIFIED):
- G14Trace's imports must come first. With ModField's imports first, the E1 copy's
  `bcPt.map_one'` fails with "No goals"; g15-ram saw the same.
- ModField's file-level `open`s (`ZInQ LeafQM.AV GlueDescent GlueDescent.B2 …`) were active where
  g14-trace's `part_bridge.lean` and g0-assemble's `87_afterg7.lean` were appended in their own
  builds. Here they are re-issued inside sections around those copies, and the copied texts are
  unchanged.
- `G14Trace.lean` imports `ZInQKernel.Main`, which needs `lake build ZInQKernel.Main`. That builds
  the upstream helper `ZInQ.PoleValuation`.

## 6. Compile record

- `lake env lean scratch/g8-object/Dev.lean` (G15Ram + g0-mod-galois definitions + part_obj;
  45 s): exit 0, 0 errors. Axioms standard for the 7 part-1 theorems (VERIFIED, `dev.out`).
- `lake env lean scratch/g8-object/G8Object.lean` (1 min 11 s): exit 0, 0 errors, 0 `sorry`. All 56
  axiom reports are `[propext, Classical.choice, Quot.sound]` (VERIFIED, `obj.out`). The new
  ones are:
  - `DescData.intertwines`, `DescData.g8Out`, `mat_eq_scalar_of_intertwines`,
    `g11_of_intertwines`, `localData_of_intertwines`;
  - `g15RamG_obj`, `g15RamG_of_intertwines`, `LinkedObj.galG8Out5`, `interface_obj`,
    `modularConstituent_tail_obj`;
  - `localDataG_of_C`, `rhoRamWild_of_localDataG`, `localRamWild_of_rhoRamWild`;
  - `linkedTateData_of_obj`, `linkedTateCore_of_obj`, `linkedTateCoreDR_of_objDR`,
    `tateBridge35_of_objDR`, `localDataG_triv`;
  - `decomp_mem_fixing`, `tmWild_of_split`, `localDataC_of_S`, `linkedTateObjD_of_obj`,
    `linkedTateObjD_of_S`, `linkedTateDataD_of_objD`, `linkedTateDataD_of_S`.
- Review: one model review, read-only, no human review. It found the false `LinkedTateObjS`
  (repaired by adding the `[L:ℚ] ≤ D` premise), overclaims of the form "smaller" / "strictly more
  primitive" (reworded), and stale counts (updated).
