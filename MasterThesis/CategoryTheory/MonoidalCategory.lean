import MasterThesis.CategoryTheory.Adjunction

namespace mymon



structure MonoidalCategoryStruct extends Category where
  tensor : Functor (toCategory × toCategory) toCategory
  unit   : toCategory.Obj
  α      : NatIso ((tensor ∘ (tensor × (Id_Functor toCategory))) ∘ Cat_assoc_right toCategory toCategory toCategory) (tensor ∘ ((Id_Functor toCategory) × tensor))

def right_unitor_domain (C : MonoidalCategoryStruct) : Functor (C.toCategory) (C.toCategory) :=
  {
    obj := fun A => C.tensor.obj (A, C.unit)
    map := fun {A B} (f : C.Hom A B) => (C.tensor).map ((f : C.Hom A B) ×ₘ (C.id C.unit : C.Hom C.unit C.unit))
    map_id := fun A ↦ by
      dsimp
      rw [<-C.tensor.map_id (A, C.unit)]
      rfl
    map_comp := fun g f ↦ by
      rw [<- C.tensor.map_comp]
      dsimp [Cat_prod, mor_prod]
      rw [C.id_comp]
  }

def left_unitor_domain (C : MonoidalCategoryStruct) : Functor C.toCategory C.toCategory :=
{
  obj := fun A => C.tensor.obj (C.unit, A)
  map := fun {A B} (f : C.Hom A B) =>
    C.tensor.map ((C.id C.unit : C.Hom C.unit C.unit) ×ₘ (f : C.Hom A B))
  map_id := fun A ↦ by
    dsimp
    rw [← C.tensor.map_id (C.unit, A)]
    rfl
  map_comp := fun g f ↦ by
    rw [← C.tensor.map_comp]
    dsimp [Cat_prod, mor_prod]
    rw [C.id_comp]
}

structure MonoidalCategory extends MonoidalCategoryStruct where
  left_unit : NatIso (left_unitor_domain toMonoidalCategoryStruct) (Id_Functor toCategory)
  right_unit : NatIso (right_unitor_domain toMonoidalCategoryStruct) (Id_Functor toCategory)
/-  triangle : ∀ {A B : toCategory.Obj},
    (toMonoidalCategoryStruct.comp (toMonoidalCategoryStruct.tensor.map ((right_unit.obj A)×ₘ(toCategory.id B))) (toMonoidalCategoryStruct.α.obj (A, toMonoidalCategoryStruct.unit, B))) = (toMonoidalCategoryStruct.tensor.map ((toCategory.id A)×ₘ(left_unit.obj B)))-/

/- This has to be finished, but i may change my approach, so i will leave it as it is right now-/
end mymon
