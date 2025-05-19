namespace mymon

universe u v

/-- I should point out, that this is not the most general one can be. We could for example use Sort v and Sort u. That would allow our morphisms and objects to be Propositions etc as well. --/

structure CategoryStruct where
  Obj : Type u
  Hom : Obj → Obj → Type v
  id  : ∀ X, Hom X X
  comp : ∀ {X Y Z}, Hom Y Z → Hom X Y → Hom X Z

structure Category extends CategoryStruct where
  comp_assoc : ∀ {W X Y Z} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    toCategoryStruct.comp h (toCategoryStruct.comp g f) = toCategoryStruct.comp (toCategoryStruct.comp h g) f
  comp_id  : ∀ {X Y} (f : Hom X Y), toCategoryStruct.comp f (id X) = f
  id_comp : ∀ {X Y} (f : Hom X Y), toCategoryStruct.comp (id Y) f = f


def is_iso {C : Category} {X Y : C.Obj} (f : C.Hom X Y) : Prop :=
  ∃ (g : C.Hom Y X), C.comp g f = C.id X ∧ C.comp f g = C.id Y

class HasIsomorphisms (α : Type u) where
  is_iso : α → α → Prop

notation X " ≅ " Y => HasIsomorphisms.is_iso X Y

instance {C : Category} : HasIsomorphisms C.Obj where
  is_iso := fun X Y => ∃ f : C.Hom X Y, is_iso f

def Cat_prod (C D : Category) : Category :=
{
  Obj := C.Obj × D.Obj
  Hom := fun (X₁, Y₁) (X₂, Y₂) ↦ (C.Hom X₁ X₂) × (D.Hom Y₁ Y₂)
  id := fun (X, Y) ↦ (C.id X, D.id Y)
  comp := fun (f₂, g₂) (f₁, g₁) ↦ (C.comp f₂ f₁, D.comp g₂ g₁)
  comp_assoc := fun (f₁, g₁) (f₂, g₂) (f₃, g₃) ↦ by
    dsimp
    rw [C.comp_assoc, D.comp_assoc]
  comp_id := fun (f, g) ↦ by
    dsimp
    rw [C.comp_id, D.comp_id]
  id_comp := fun (f, g) ↦ by
    dsimp
    rw [C.id_comp, D.id_comp]
}

notation C " × " D => Cat_prod C D

def mor_prod {C D : Category} {X₁ X₂ : C.Obj} {Y₁ Y₂ : D.Obj}
  (f : C.Hom X₁ X₂) (g : D.Hom Y₁ Y₂) : (Cat_prod C D).Hom (X₁, Y₁) (X₂, Y₂) :=
  (f, g)

notation:80 f " ×ₘ " g => mor_prod f g
