import MasterThesis.CategoryTheory.Category
import MasterThesis.HEq
import Mathlib.Tactic.Use
import Batteries.Tactic.PermuteGoals
import Mathlib.Tactic.Lemma
namespace mymon

structure Functor (C : Category) (D : Category) where
  obj : C.Obj → D.Obj
  map : ∀ {X Y : C.Obj}, C.Hom X Y → D.Hom (obj X) (obj Y)
  map_id  : ∀ (X : C.Obj), map (C.id X) = D.id (obj X)
  map_comp : ∀ {X Y Z : C.Obj} (g : C.Hom Y Z) (f : C.Hom X Y),
              map (C.comp g f) = D.comp (map g) (map f)

theorem Fun_pres_iso {C D : Category} {X Y : C.Obj} (F : Functor C D) (f : C.Hom X Y) (h : is_iso f) : is_iso (F.map f) := by
  let f_inv := Classical.choose h
  obtain ⟨f.inv_left, f.inv_right⟩ := Classical.choose_spec (h)
  use (F.map f_inv)
  constructor
  . rw [<-F.map_comp, f.inv_left, F.map_id]
  rw [<-F.map_comp, f.inv_right, F.map_id]

structure Contravar_Functor (C : Category) (D : Category) where
  obj : C.Obj → D.Obj
  map : ∀ {X Y : C.Obj}, C.Hom X Y → D.Hom (obj Y) (obj X)
  map_id  : ∀ (X : C.Obj), map (C.id X) = D.id (obj X)
  map_comp : ∀ {X Y Z : C.Obj} (g : C.Hom Y Z) (f : C.Hom X Y),
              map (C.comp g f) = D.comp (map f) (map g)

/-- Composition of functors. -/

def Functor_prod {C D C' D' : Category} (F : Functor C D) (G : Functor C' D') : Functor (Cat_prod C C') (Cat_prod D D') :=
{
  obj := fun (X, Y) => (F.obj X, G.obj Y)
  map := fun (f, g) => (F.map f, G.map g)
  map_id := fun (X, Y) => by
    simp only [Cat_prod]
    congr
    . rw [F.map_id]
    rw [G.map_id]
  map_comp := fun (f₂, g₂) (f₁, g₁) => by
    simp only [Cat_prod]
    congr
    . rw [F.map_comp]
    rw [G.map_comp]
}

notation F " × " G => Functor_prod F G

def Functor_const {C D : Category} (X : D.Obj) : Functor C D where
  obj := fun _ => X
  map := fun _ => D.id X
  map_id := fun _ => rfl
  map_comp := fun _ _ => (D.id_comp (D.id X)).symm

def Functor_diag (C : Category) : Functor C (C × C) where
  obj := fun X => (X, X)
  map := fun f => (f, f)
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

notation "Δ" C => Functor_diag C

def Functor_comp
  {C : Category} {D : Category} {E : Category}
  (G : Functor D E) (F : Functor C D) : Functor C E :=
{
  obj := fun c ↦ G.obj (F.obj c)
  map := fun f ↦ G.map (F.map f)
  map_id := fun c ↦ by
    dsimp
    rw [F.map_id, G.map_id]
  map_comp := fun g f ↦ by
    dsimp
    rw [F.map_comp, G.map_comp]
}

notation G " ∘ " F => Functor_comp G F

/-- The identity functor. -/

def Id_Functor (C : Category) : Functor C C :=
{
  obj := fun c ↦ c
  map := fun f ↦ f
  map_id := fun c ↦ by rfl
  map_comp := fun g f ↦ by rfl
}

def Homtransport {C D : Category} (F G : Functor C D)
  {X Y Z W : C.Obj}
  (h_XY : F.obj X = G.obj Y) (h_ZW : F.obj Z = G.obj W)
  (f : C.Hom X Z) :
  D.Hom (G.obj Y) (G.obj W) := by
  have h : D.Hom (F.obj X) (F.obj Z) = D.Hom (G.obj Y) (F.obj Z) :=
    congrArg (fun A => D.Hom A (F.obj Z)) h_XY
  have h' : D.Hom (G.obj Y) (F.obj Z) = D.Hom (G.obj Y) (G.obj W) :=
    congrArg (fun B => D.Hom (G.obj Y) B) h_ZW
  have h'' : D.Hom (F.obj X) (F.obj Z) = D.Hom (G.obj Y) (G.obj W) := Eq.trans h h'
  exact (cast h'' (F.map f))

def hom_type_eq_left {C : Category} {X Y Z : C.Obj}
  (h : X = Y) :
  C.Hom X Z = C.Hom Y Z := congrArg (fun A => C.Hom A Z) h

def hom_type_eq_right {C : Category} {X Y Z : C.Obj}
  (h : Y = Z) : C.Hom X Y = C.Hom X Z := congrArg (fun A => C.Hom X A) h

def hom_type_eq {C : Category}
  {X Y Z W : C.Obj}
  (h_XY :  X = Y) (h_ZW : Z = W) :
  C.Hom X Z = C.Hom Y W := by
  have h : C.Hom X Z = C.Hom Y Z :=
    congrArg (fun A => C.Hom A Z) h_XY
  have h' : C.Hom Y Z = C.Hom Y  W :=
    congrArg (fun B => C.Hom Y B) h_ZW
  exact Eq.trans h h'

lemma cast_right_comp {D : Category} {A A' B C : D.Obj} (h : A = A') (f : D.Hom A B) (g : D.Hom B C) : D.comp g (cast (hom_type_eq_left h) f) = cast (hom_type_eq_left h) (D.comp g f):= by
  match h with
  | rfl => rfl

lemma cast_left_comp {D : Category} {A B C C' : D.Obj} (h : C = C') (f : D.Hom A B) (g : D.Hom B C) : D.comp (cast (hom_type_eq_right h) g) f = cast (hom_type_eq_right h) (D.comp g f):= by
  match h with
  | rfl => rfl

/- note to myself: This can obviously be done more generally. I will leave it like this for the moment though until i need the more general version-/
lemma cast_comp_outer {C : Category} {A A' B : C.Obj} (h : A = A') (f : C.Hom A B) (g : C.Hom B A) : C.comp (cast (hom_type_eq_right h) g) (cast (hom_type_eq_left h) f)
  = cast (hom_type_eq h h) (C.comp g f) := by
  match h with
  | rfl => rfl

lemma cast_comp_inner {D : Category} {A B B' C : D.Obj} (h : B = B') (f : D.Hom A B) (g : D.Hom B C) : D.comp (cast (hom_type_eq_left h) g) (cast (hom_type_eq_right h) f) = D.comp g f := by
  match h with
  | rfl => rfl

def congrArgHEq {α : Sort u} {β : α → Sort v} (f : (a : α) → β a) {x y : α} (h : x = y) : HEq (f x) (f y) :=
  h ▸ HEq.rfl

lemma cast_compose {D : Category} {A A' B B' C : D.Obj} (h₁ : A = A') (h₂ : B = B') (g : D.Hom B C) (f: D.Hom A B) : D.comp (cast (hom_type_eq_left h₂) g) (cast (hom_type_eq h₁ h₂) f) = cast (hom_type_eq_left h₁) (D.comp g f) := by
  cases h₁
  cases h₂
  rfl

lemma heq_map_cast {C D : Category} {F G : Functor C D}
  {X Y : C.Obj} (f : C.Hom X Y)
  (hX : F.obj X = G.obj X) (hY : F.obj Y = G.obj Y)
  (hmap : HEq (F.map f) (G.map f)) :
  G.map f = cast (hom_type_eq hX hY) (F.map f) := by
  obtain ⟨p, hp⟩ := heq_cast hmap
  have h : p = (hom_type_eq hX hY) := by
    rfl
  rw [h] at hp
  exact hp

/- This was the theorem that required all the work i have done before. And its very important, as it allows one to prove equality of two functors by showing that they are equal on objects and (heterogeneously) equal on morphisms -/

theorem Functor.ext {C D : Category} {F G : Functor C D}
  (h_obj : ∀ X, F.obj X = G.obj X)
  (h_map : ∀ {X Y} (f : C.Hom X Y), cast (hom_type_eq (h_obj X) (h_obj Y)) (F.map f) = G.map f) :
  F = G := by
  obtain ⟨F_obj, F_map, F_map_id, F_map_comp⟩ := F
  obtain ⟨G_obj, G_map, G_map_id, G_map_comp⟩ := G

  --this is not necessary, but writing F' instead of ⟨F_obj, F_map, F_map_id, F_map_comp⟩ is much cleaner

  let F' : Functor C D := ⟨F_obj, F_map, F_map_id, F_map_comp⟩
  let G' : Functor C D := ⟨G_obj, G_map, G_map_id, G_map_comp⟩
  have h_map' : ∀ {X Y} (f : C.Hom X Y), cast (hom_type_eq (h_obj X) (h_obj Y)) (F_map f) = G_map f := h_map
  have h_map_mirror : ∀ {X Y} (f : C.Hom X Y), cast (Eq.symm (hom_type_eq (h_obj X) (h_obj Y))) (G_map f) = F_map f := by
    intro X Y f
    rw [<-h_map']
    apply cast_cast
  congr
  . apply funext
    intro x
    exact (h_obj x)
  . apply HEq_funext
    intro X
    apply HEq_funext
    intro Y
    apply HEq_funext
    intro f
    rw [<-h_map' f]
    apply HEq.symm
    apply cast_heq
  . apply HEq_funext
    intro X
    let homeq := hom_type_eq (h_obj X) (h_obj X)
    have  h_left : cast (homeq) (F_map (C.id X)) = G_map (C.id X) := by
        exact h_map' (C.id X)
    have h_right : cast (homeq) (D.id (F_obj X)) = D.id (G_obj X) := by
      rw [<-F_map_id X, h_map', G_map_id X]
    have h_mirror : cast (Eq.symm (homeq)) (G_map (C.id X)) = F_map (C.id X) := by
        exact h_map_mirror (C.id X)
    have h_right_mirror : cast (Eq.symm (homeq)) (D.id (G_obj X)) = D.id (F_obj X) := by
      rw [<-G_map_id X, h_map_mirror, F_map_id X]
    have h_equiv : (F_map (C.id X) = D.id (F_obj X)) ↔ (G_map (C.id X) = D.id (G_obj X)) := by
      constructor
      . intro h
        let h' : cast (homeq) (F_map (C.id X)) = cast (homeq) (D.id (F_obj X)) := by
          exact cast_eq h (homeq)
        rw [<- h_left, <- h_right]
        exact h'
      . intro h
        let h' : cast (Eq.symm (homeq)) (G_map (C.id X)) =
           cast (Eq.symm (homeq)) (D.id (G_obj X)) := by
          exact cast_eq h (Eq.symm (homeq))
        rw [<-h_mirror, <-h_right_mirror]
        exact h'
    have h_prop : (F_map (C.id X) = D.id (F_obj X)) = (G_map (C.id X) = D.id (G_obj X)) :=
      propext h_equiv
    apply cast_heq
    apply Eq.symm
    exact h_prop
  . apply HEq_funext
    intro X
    apply HEq_funext
    intro Y
    apply HEq_funext
    intro Z
    apply HEq_funext
    intro g
    apply HEq_funext
    intro f
    let homeq := hom_type_eq (h_obj X) (h_obj Z)
    have p_left : cast (homeq) (F_map (C.comp g f)) = G_map (C.comp g f) :=
      h_map' (C.comp g f)
    have p_right : cast (homeq) (D.comp (F_map g) (F_map f)) = D.comp (G_map g) (G_map f):= by
      rw [<-F_map_comp, h_map', G_map_comp]
    have p_left_mirror : cast (Eq.symm (homeq)) (G_map (C.comp g f)) = F_map (C.comp g f) :=
      h_map_mirror (C.comp g f)
    have p_right_mirror : cast (Eq.symm (homeq)) (D.comp (G_map g) (G_map f)) = D.comp (F_map g) (F_map f):= by
      rw [<-G_map_comp, h_map_mirror, F_map_comp]
    have p_equiv : F_map (C.comp g f) = D.comp (F_map g) (F_map f) ↔ G_map (C.comp g f) = D.comp (G_map g) (G_map f) := by
      constructor
      . intro p
        let p' : cast (homeq) ((F_map (C.comp g f))) = cast (homeq) ((D.comp (F_map g) (F_map f))) := by
          exact cast_eq p (homeq)
        rw [<- p_left, <- p_right]
        exact p'
      . intro p
        let p' : cast (Eq.symm (homeq)) (G_map (C.comp g f)) = cast (Eq.symm (homeq)) (D.comp (G_map g) (G_map f)) := by
          exact cast_eq p (Eq.symm (homeq))
        rw [<- p_left_mirror, <- p_right_mirror]
        exact p'
    have p_prop : (F_map (C.comp g f) = D.comp (F_map g) (F_map f)) = (G_map (C.comp g f) = D.comp (G_map g) (G_map f)) :=
      propext p_equiv
    apply cast_heq
    apply Eq.symm
    exact p_prop

/- The category of categories is in fact a category-/

def Categorycat : Category :=
{
  Obj := Category
  Hom := fun C D ↦ Functor C D
  id := fun C ↦ Id_Functor C
  comp := fun G F ↦ G  ∘  F
  comp_assoc := fun F G H ↦ by
    dsimp
    apply Functor.ext
    pick_goal 2
    . intro C
      rfl
    . intro C D F
      rfl
  id_comp := by
    intro C D F
    dsimp
    apply Functor.ext
    pick_goal 2
    . intro X
      rfl
    . intro C D F
      rfl

  comp_id := by
    intro C D F
    dsimp
    apply Functor.ext
    pick_goal 2
    . intro X
      rfl
    . intro C D F
      rfl
}


def Cat_assoc_left (C D E : Category) : Functor ((C × D) × E) (C × (D × E)) :=
{
  obj := fun ((X, Y), Z) => (X, (Y, Z))
  map := fun ((f₁, f₂), f₃) => (f₁, (f₂, f₃))
  map_id := by
    intro X
    dsimp [Cat_prod]
  map_comp := by
    intro X Y Z g f
    dsimp [Cat_prod]
}

def Cat_assoc_right (C D E : Category) : Functor (C × (D × E)) ((C × D) × E) :=
{
  obj := fun (X, (Y, Z)) => ((X, Y), Z),
  map := fun (f₁, (f₂, f₃)) => ((f₁, f₂), f₃),
  map_id := by
    intro X
    dsimp [Cat_prod]
  map_comp := by
    intro X Y Z g f
    dsimp [Cat_prod]
}
