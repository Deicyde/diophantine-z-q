import ZInQKernel.MainLiterature

/- This file checks the complete existing conditional headline, including all
   outer premises. It does not discharge any of those premises. -/
namespace ZInQ.Contract

theorem expectedHeadline :
    ZInQ.SixContactMin →
    ZInQ.Literature.TYZThm35ReadingA →
    ZInQ.Literature.HeckeContinuation →
    ZInQ.Literature.FunctionalEquation5 →
    ZInQ.Literature.GrossZagier →
    ZInQ.FrozenTarget :=
  @ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzThm35ReadingA_heckeContinuation_functionalEquation5_grossZagier

end ZInQ.Contract
