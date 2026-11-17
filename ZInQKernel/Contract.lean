import ZInQKernel.MainGreenTao

/- This file checks the complete existing conditional headline, including all
   outer premises. It does not discharge any of those premises. -/
namespace ZInQ.Contract

theorem expectedHeadline :
    ZInQ.SixContactMin →
    ZInQ.PoleCompleteness →
    ZInQ.FrozenTarget :=
  @ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness

end ZInQ.Contract
