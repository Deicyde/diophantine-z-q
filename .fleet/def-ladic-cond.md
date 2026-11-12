# def-ladic-cond (fleet report)

**Main result.** The conductor exponent of a representation `ρ : G_{ℚ_p} → GL_n(k)` (with ℓ-adic
`ρ`, `ℓ ≠ p`, in mind) is now defined in Lean over genuine objects, and leaves R17 and L8 are
stated over it. Everything is in `scratch/def-ladic-cond/LadicCond.lean`, which imports Mathlib
only. VERIFIED: it compiles, with no `sorry`; all 16 theorems listed by `#print axioms` use only `propext`,
`Classical.choice` and `Quot.sound`.

- **Definition** (Serre–Tate 1968 §2): `a(ρ) = codim V^{I_p} + Sw(ρ)`.
  - `Sw` is computed at a finite Galois `L/ℚ_p` that is adapted to `ρ`, meaning `ρ = 1` on
    `P_p ∩ G_L`: `Sw_L(ρ) = ∑_{i≥1} (g_i/g_0) codim V^{G_i(L)∩P_p}`.
  - Inertia, wild inertia and the ramification groups are defined through the norm of Mathlib's
    `PadicAlgCl p`; Herbrand's `φ`, upper numbering and the absolute upper filtration as well.
    They transcribe pkg-I6's definitions to `G_{ℚ_p}` (`PkgI4.GQp`).
  - No lattices; Grothendieck's monodromy theorem is not needed.
- **Sanity facts, proved:**
  - unramified ⇒ `a = 0` (`condExp_eq_zero_of_unramified`);
  - agreement with Serre's finite-level Artin conductor `∑_{i≥0}(g_i/g_0) codim V^{G_i}`
    (pkg-I6's formula) when `ρ` factors through `Gal(L/ℚ_p)`, for every finite Galois `L`
    (`condAt_eq_artinAt_of_surj`). It assumes only the two standard surjectivity facts for
    restriction of `I_p` and `P_p`. Also proved along the way: `I_p ⊆ G_0`, `g_i ≠ 0`,
    `G_i(L) = 1` for large `i`, and that every finite `L ⊆ ℚ̄_p` has a uniformizer;
  - the choice of level reduces to one glue Prop, `SwanIndependent` (`condExp_eq_condAt`).
- **Leaves stated:**
  - `CarayolR17` / `CarayolR17'` (Carayol 1986, Théorème (A), weight 2, `p ≠ ℓ`, over pkg-I4's
    newforms and `AttachedTo`). The two forms are proved equivalent given `SwanIndependent` and
    `AdaptedExists`;
  - `SwanIntegral` = L8 (`Sw = ∫₀^∞ codim V^{G^u} du`).
- **Consumer, proved:** glue-conductor's D4(i) bound `a ≤ n(1+U)` from L8 when `ρ` is trivial on
  `G^u` for `u > U` (`condAt_le_of_upper`).

**What remains** (glue, stated but not proved):
- `SwanIndependent` (Herbrand, pkg-I6 I6.8/I6.9);
- `AdaptedExists` (`ρ(P_p)` is finite; values in a finite `E/ℚ_ℓ`);
- the two surjectivity facts (they need unramified-extension theory);
- a Lean bridge from `artinAt` to `PkgI6.artinConductor` on `𝓞_L ≃ₐ[ℤ_p] 𝓞_L`.

L8 is probably glue rather than a research leaf (SPECULATIVE): a change of variables plus
Herbrand. R17's theorem number and its coverage of `p | N` are UNVERIFIED. R17 also needs
Casselman's `a(π_p) = v_p(N)` and the WD/Serre–Tate comparison, both standard. Note:
`docs/research/def-ladic-cond.md`.
