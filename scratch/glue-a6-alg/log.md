# glue-a6-alg results log

## scratch/glue-a6-alg/Quat.lean
- §1: verbatim copy of scratch/rv-a6-route/QuatVal.lean (`quat_sq_dvd`), namespace GlueA6Alg.
- §2 `f3_indep`: over ZMod 3, I²=2, J²=0, JI=-IJ, Jx≠0 ⇒ x, Ix, Jx, IJx linearly independent. VERIFIED (compiles).
- §3 helpers (orbit map φ, reduction mod 3 `red`, `redMap`, `red_map`): VERIFIED (compiles).
- §3 `GlueA6Alg.core`: on V=(ZMod 3^{2k})^4 (k≥1), linear I,J,S with I²=2, J²=-3, JI=-IJ, SI=IS, SJ=JS,
  S²-2S+1=0 ⇒ S v = v whenever 3^k•v=0. VERIFIED: compiles, no sorry, axioms [propext, Classical.choice, Quot.sound].
  Proof route (differs from rv-a6-route §3 steps 1-2: no |T/JT| count): pick x with Jx ≢ 0 mod 3 (exists, else
  J=3J' on e₀ gives -3 ≡ 0 mod 9); f3_indep ⇒ x,Ix,Jx,IJx span V/3V; Nakayama by induction (3^{2k}=0) ⇒ orbit map
  φ_x : (ZMod q)^4 → V surjective, hence injective (finite); S x - x = φ_x(a); (S-1)²x = φ_x(a²-coords) ⇒ q | coords;
  quat_sq_dvd ⇒ a = 3^k a'; for v=φ_x(α) with 3^k v=0: 3^k α=0 and (S-1)v = φ_{φ_x a'}(3^k α)=0.
- §4 `GlueA6Alg.quatUnipotentTrivial : QuatUnipotentTrivial.{u}` (def verbatim from scratch/rv-a6-route/A6.lean §10).
  VERIFIED: compiles, no sorry, axioms [propext, Classical.choice, Quot.sound]. Transport: E = e extended by 0 off G[q];
  group endomorphisms become additive maps of V, hence ZMod q-linear (`AddMonoidHom.toZModLinearMap`); then `core`.
