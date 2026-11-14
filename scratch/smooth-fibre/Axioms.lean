import ZInQKernel.Contrib.SmoothFibre.Basic
#print axioms ZInQ.SmoothFibre.smoothFibreReduced
#print axioms ZInQ.SmoothFibre.isReduced_of_smooth_of_field
#print axioms ZInQ.SmoothFibre.isReduced_of_etale_of_isDomain
#check @ZInQ.SmoothFibre.isReduced_of_smooth_of_field
#check @ZInQ.SmoothFibre.isReduced_of_etale_of_isDomain
example : ZInQ.SmoothFibre.SmoothFibreReduced = (∀ (R A : Type) [CommRing R] [CommRing A] (φ : R →+* A), φ.Smooth →
    ∀ m : Ideal R, m.IsMaximal → (m.map φ).IsRadical) := rfl
