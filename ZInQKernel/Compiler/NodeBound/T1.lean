import ZInQKernel.Compiler.NodeBound.Macros
namespace ZInQ.Compiler.NodeBound
open Natural Universal
example {P : List NatNode → Prop} (hP : Mono P) (C N K : Ex) : Up P (Natural.binomial .hierarchical C N K) 8 2
      (fun φ l => Cost 8 9 φ) := by
  apply Up.weaken
  case h =>
    unfold Natural.binomial
    up_norm
    iterate 300 (first
  | (up_lt)
  | up_bind
  | (intro _)
  | up_mono
  | up_prim
  | up_fin)
    trace_state
    sorry
  all_goals sorry
