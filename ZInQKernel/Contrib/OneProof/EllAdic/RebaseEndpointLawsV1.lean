set_option autoImplicit false

/-! Endpoint equations for degree-one cohomology comparison. -/

universe u v

namespace RC53.EllAdic.EndpointComparison

/-- Cancel the specified comparison isomorphisms at the source of Ext. -/
theorem sourceAfterRebase {C : Type u} (H : C → C → Type v)
    (m : ∀ {A B D : C}, H A B → H B D → H A D) (i : ∀ A : C, H A A)
    (as : ∀ {A B D E : C} (f : H A B) (g : H B D) (k : H D E), m (m f g) k = m f (m g k))
    (il : ∀ {A B : C} (f : H A B), m (i A) f = f)
    (ir : ∀ {A B : C} (f : H A B), m f (i B) = f)
    {A B D E J : C} (a : H A B) (ai : H B A) (k : H A D) (t : H D E)
    (b : H E J) (bi : H J E) (c : H B J)
    (ha : m ai a = i B) (hb : m b bi = i E) (cc : m k (m t b) = m a c) :
    m (m ai k) t = m c bi :=
  calc
    m (m ai k) t = m ai (m k t) := as ai k t
    _ = m ai (m k (m t (i E))) := congrArg (fun z : H D E => m ai (m k z)) (ir t).symm
    _ = m ai (m k (m t (m b bi))) := congrArg (fun z : H E E => m ai (m k (m t z))) hb.symm
    _ = m ai (m (m k (m t b)) bi) :=
      congrArg (fun z : H A E => m ai z)
        ((as k (m t b) bi).trans (congrArg (fun z : H D E => m k z) (as t b bi))).symm
    _ = m ai (m (m a c) bi) := congrArg (fun z : H A J => m ai (m z bi)) cc
    _ = m (m ai a) (m c bi) :=
      (congrArg (fun z : H A E => m ai z) (as a c bi)).trans (as ai a (m c bi)).symm
    _ = m (i B) (m c bi) := congrArg (fun z : H B B => m z (m c bi)) ha
    _ = m c bi := il (m c bi)

/-- Cancel at the target of Ext and transport the specified residue diagonal. -/
theorem targetAfterRebase {C : Type u} (H : C → C → Type v)
    (m : ∀ {A B D : C}, H A B → H B D → H A D) (i : ∀ A : C, H A A)
    (as : ∀ {A B D E : C} (f : H A B) (g : H B D) (k : H D E), m (m f g) k = m f (m g k))
    (il : ∀ {A B : C} (f : H A B), m (i A) f = f)
    {A B D E J W U : C} (a : H A B) (k : H A D) (ki : H D A) (t : H D E)
    (b : H E J) (c : H B J) (r : H J U) (l : H U W) (d : H B W)
    (hk : m ki k = i D) (cc : m k (m t b) = m a c) (diag : m c (m r l) = d) :
    m ki (m a d) = m t (m b (m r l)) :=
  let e : m t b = m ki (m a c) :=
    (il (m t b)).symm.trans
      ((congrArg (fun z : H D D => m z (m t b)) hk.symm).trans
        ((as ki k (m t b)).trans (congrArg (fun z : H A J => m ki z) cc)))
  calc
    m ki (m a d) = m ki (m a (m c (m r l))) := congrArg (fun z : H B W => m ki (m a z)) diag.symm
    _ = m (m ki (m a c)) (m r l) :=
      ((as ki (m a c) (m r l)).trans
        (congrArg (fun z : H A W => m ki z) (as a c (m r l)))).symm
    _ = m (m t b) (m r l) := congrArg (fun z : H D J => m z (m r l)) e.symm
    _ = m t (m b (m r l)) := as t b (m r l)

end RC53.EllAdic.EndpointComparison
