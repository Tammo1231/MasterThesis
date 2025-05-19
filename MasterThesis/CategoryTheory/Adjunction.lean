import MasterThesis.CategoryTheory.Category
import MasterThesis.CategoryTheory.Functor
import MasterThesis.CategoryTheory.NatTrafo

namespace mymon

structure Adjunction {C D : Category} (F : Functor C D) (G : Functor D C) where
  η : NatTrafo (Id_Functor C) (G ∘ F)
  ε : NatTrafo (F ∘ G) (Id_Functor D)
  coh1 : ((ε * F) ∘ (F * η)) = Id_Trafo F
  coh2 : ((G * ε) ∘ (η * G)) = Id_Trafo G

end mymon
