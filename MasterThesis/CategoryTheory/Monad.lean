import MasterThesis.CategoryTheory.Adjunction

namespace mymon

structure Monad (C : Category) where
  m : Functor C C
  η : NatTrafo (Id_Functor C) m
  μ : NatTrafo (m ∘ m) m
  is_left_unit : ((μ ∘ (m * η)) ∘ (Natiso_functor_comp_id m)) = Id_Trafo m
  is_right_unit : ((μ ∘ (η * m)) ∘ (Natiso_id_comp_functor m)) = Id_Trafo m
  is_assoc : ((μ ∘ (m * μ)) ∘ (Natiso_functor_assoc m m m)) = (μ ∘ (μ * m))

def adjunction_mon {C D : Category} (F : Functor C D) (G : Functor D C) (ad : Adjunction F G) : Monad C :=
{
  m := G ∘ F
  η := ad.η
  μ :=  G * (ad.ε * F)
  is_left_unit := by
    apply NatTrafo.ext
    intro X
    dsimp [Id_Trafo, Natiso_functor_comp_id, Functor_comp, Functor_comp_trafo, Trafo_comp_functor, Trafo_vcomp_NatIso]
    have pw_coh := congrFun (congrArg NatTrafo.obj ad.coh1) X
    dsimp [Id_Trafo, Functor_comp_trafo, Trafo_comp_functor] at pw_coh
    rw [C.comp_id, <-G.map_id, <-G.map_comp, pw_coh]
  is_right_unit := by
    apply NatTrafo.ext
    intro X
    dsimp [vertical_comp, Id_Trafo, Natiso_id_comp_functor, Functor_comp, Functor_comp_trafo, Trafo_comp_functor, Trafo_vcomp_NatIso]
    have pw_coh := congrFun (congrArg NatTrafo.obj ad.coh2) (F.obj X)
    dsimp [vertical_comp, Id_Trafo, Functor_comp_trafo, Trafo_comp_functor] at pw_coh
    rw [C.comp_id, pw_coh]
  is_assoc := by
    apply NatTrafo.ext
    intro X
    dsimp [vertical_comp, Id_Trafo, Natiso_functor_assoc, Functor_comp, Functor_comp_trafo, Trafo_comp_functor, Trafo_vcomp_NatIso]
    rw [C.comp_id, <-G.map_comp, <-G.map_comp]
    have h : ∀ (Y : D.Obj),  D.comp (ad.ε.obj Y) (ad.ε.obj (F.obj (G.obj (Y)))) = D.comp (ad.ε.obj Y) (F.map (G.map (ad.ε.obj Y))) := by
      intro Y
      let h := ad.ε.is_nat (ad.ε.obj Y)
      dsimp [Functor_comp, Id_Functor] at h
      exact h
    rw [h (F.obj X)]
}

end mymon
