import MasterThesis.CategoryTheory.Category
import MasterThesis.CategoryTheory.Functor
import Mathlib.Tactic.NthRewrite
import Batteries.Tactic.PermuteGoals
import Mathlib.Tactic.Lemma
import Batteries.Logic
namespace mymon

structure NatTrafo
  {C : Category} {D : Category}
  (F G : Functor C D) where
  obj : ∀ X : C.Obj, D.Hom (F.obj X) (G.obj X)
  is_nat : ∀ {X Y : C.Obj} (f : C.Hom X Y),
    D.comp (G.map f) (obj X) = D.comp (obj Y) (F.map f)

theorem NatTrafo.ext {C D : Category} {F G : Functor C D}
  (η ε  : NatTrafo F G)
  (h : ∀ X, η.obj X =  ε.obj X) :
  η = ε := by
  cases η
  cases ε
  congr
  exact funext h

def Id_Trafo {C : Category} {D : Category}
  (F : Functor C D) : NatTrafo F F :=
{
  obj := fun X ↦ D.id (F.obj X)
  is_nat := fun f ↦ by
    dsimp
    rw [D.comp_id, D.id_comp]
}

structure NatIso {C D : Category} (F G : Functor C D) extends NatTrafo F G where
  is_iso : ∀ X, is_iso (obj X)

class HasNatIsomorphisms (C D : Category) where
  nat_iso : Functor C D → Functor C D → Prop

instance {C D : Category} : HasNatIsomorphisms C D where
  nat_iso := fun F G => ∃ _ : NatIso F G, True

notation F " ≃ " G => HasNatIsomorphisms.nat_iso F G

instance : HasIsomorphisms Category where
  is_iso := fun C D =>
    ∃ (F : Functor C D) (G : Functor D C),
      ((F ∘ G) ≃ Id_Functor D) ∧ ((G ∘ F) ≃ Id_Functor C )






#check Classical.choose

section Compositions

/-- Composition of a natural transformation with a functor from the left -/

def Functor_comp_trafo
  {C : Category} {D : Category} {E : Category}
  (H : Functor D E) {F G : Functor C D} (η : NatTrafo F G) :
  NatTrafo (H ∘ F) (H ∘ G) :=
  {
    obj := fun c ↦ H.map (η.obj c)
    is_nat := fun f ↦ by
      dsimp [Functor_comp]
      rw [←H.map_comp, ←H.map_comp, η.is_nat]
  }

infixr:70 " * " => Functor_comp_trafo

/-- Composition of a natural transformation with a functor from the right -/

def Trafo_comp_functor
  {C : Category} {D : Category} {E : Category}
  {F G : Functor D E} (η : NatTrafo F G) (H : Functor C D) :
  NatTrafo (F ∘ H) (G ∘ H) :=
{
  obj := fun c ↦ η.obj (H.obj c)
  is_nat := fun f ↦ by
    dsimp [Functor_comp]
    rw [η.is_nat]
}

infixr:70 " * " => Trafo_comp_functor

/-- Horizontal composition of natural transformations. -/

def horizontal_comp
  {C : Category} {D : Category} {E : Category}
  {J K : Functor D E} {F G : Functor C D}
  (ε : NatTrafo J K) (η : NatTrafo F G) :
  NatTrafo (J ∘ F) (K ∘ G) :=
{
  obj := fun c ↦ E.comp (ε.obj (G.obj c)) (J.map (η.obj c))
  is_nat := fun f ↦ by
    dsimp [Functor_comp]
    rw [E.comp_assoc, ε.is_nat, ←E.comp_assoc, ←J.map_comp, η.is_nat, J.map_comp, E.comp_assoc]
}

infixr:70 " * " => horizontal_comp

def Natiso_hcomp_Trafo
  {C : Category} {D : Category} {E : Category}
  {J K : Functor D E} {F G : Functor C D}
  (ε : NatIso J K) (η : NatTrafo F G) :
  NatTrafo (J ∘ F) (K ∘ G) :=
{
  obj := fun c ↦ E.comp (ε.obj (G.obj c)) (J.map (η.obj c))
  is_nat := fun f ↦ by
    dsimp [Functor_comp]
    rw [E.comp_assoc, ε.is_nat, ←E.comp_assoc, ←J.map_comp, η.is_nat, J.map_comp, E.comp_assoc]
}

infixr:70 " * " => Natiso_hcomp_Trafo

def Trafo_hcomp_Natiso
  {C : Category} {D : Category} {E : Category}
  {J K : Functor D E} {F G : Functor C D}
  (ε : NatTrafo J K) (η : NatIso F G) :
  NatTrafo (J ∘ F) (K ∘ G) :=
{
  obj := fun c ↦ E.comp (ε.obj (G.obj c)) (J.map (η.obj c))
  is_nat := fun f ↦ by
    dsimp [Functor_comp]
    rw [E.comp_assoc, ε.is_nat, ←E.comp_assoc, ←J.map_comp, η.is_nat, J.map_comp, E.comp_assoc]
}

infixr:70 " * " => Trafo_hcomp_Natiso

def Natiso_hcomp_Natiso
  {C : Category} {D : Category} {E : Category}
  {J K : Functor D E} {F G : Functor C D}
  (ε : NatIso J K) (η : NatIso F G) :
  NatIso (J ∘ F) (K ∘ G) :=
{
  obj := fun c ↦ E.comp (ε.obj (G.obj c)) (J.map (η.obj c))
  is_nat := fun f ↦ by
    dsimp [Functor_comp]
    rw [E.comp_assoc, ε.is_nat, ←E.comp_assoc, ←J.map_comp, η.is_nat, J.map_comp, E.comp_assoc]
  is_iso := by
    intro X
    dsimp
    let ε_inv := Classical.choose (ε.is_iso (G.obj X))
    obtain ⟨ε.inv_left, ε.inv_right⟩ := Classical.choose_spec (ε.is_iso (G.obj X))
    let h := Fun_pres_iso J (η.obj X) (η.is_iso X)
    let Jη_inv := Classical.choose h
    obtain ⟨Jη.inv_left, Jη.inv_right⟩ := Classical.choose_spec (h)
    use E.comp (Jη_inv) (ε_inv)
    constructor
    . rw [E.comp_assoc]
      nth_rw 2 [<-E.comp_assoc]
      rw [ε.inv_left, E.comp_id, Jη.inv_left]
      dsimp [Functor_comp]
    . rw [E.comp_assoc]
      nth_rw 2 [<-E.comp_assoc]
      rw [Jη.inv_right, E.comp_id, ε.inv_right]
      dsimp [Functor_comp]
}

infixr:70 " * " => Trafo_hcomp_Natiso


/- vertical composition of natural transformation-/
@[simp]
def vertical_comp {C : Category} {D : Category} {F G H : Functor C D} (ε : NatTrafo  G H) (η : NatTrafo F G) : NatTrafo F H :=
{
  obj := fun c ↦ D.comp (ε.obj c) (η.obj c)
  is_nat := fun f ↦ by
    dsimp
    rw [D.comp_assoc, ε.is_nat, <-D.comp_assoc, η.is_nat, D.comp_assoc]
}

infixr:80 " ∘ " => vertical_comp

def NatIso_vcomp_Trafo {C : Category} {D : Category} {F G H : Functor C D} (ε : NatIso  G H) (η : NatTrafo F G) : NatTrafo F H :=
{
  obj := fun c ↦ D.comp (ε.obj c) (η.obj c)
  is_nat := fun f ↦ by
    dsimp
    rw [D.comp_assoc, ε.is_nat, <-D.comp_assoc, η.is_nat, D.comp_assoc]
}

infixr:80 " ∘ " => NatIso_vcomp_Trafo

def Trafo_vcomp_NatIso {C : Category} {D : Category} {F G H : Functor C D} (ε : NatTrafo  G H) (η : NatIso F G) : NatTrafo F H :=
{
  obj := fun c ↦ D.comp (ε.obj c) (η.obj c)
  is_nat := fun f ↦ by
    dsimp
    rw [D.comp_assoc, ε.is_nat, <-D.comp_assoc, η.is_nat, D.comp_assoc]
}

infixr:80 " ∘ " => Trafo_vcomp_NatIso

def NatIso_vcomp_NatIso {C : Category} {D : Category} {F G H : Functor C D} (ε : NatIso G H) (η : NatIso F G) : NatIso F H :=
{
  obj := fun c ↦ D.comp (ε.obj c) (η.obj c)
  is_nat := fun f ↦ by
    dsimp
    rw [D.comp_assoc, ε.is_nat, <-D.comp_assoc, η.is_nat, D.comp_assoc]
  is_iso := by
    intro X
    dsimp
    let ε_inv := Classical.choose (ε.is_iso X)
    let η_inv := Classical.choose (η.is_iso X)
    obtain ⟨ε.inv_left, ε.inv_right⟩ := Classical.choose_spec (ε.is_iso X)
    obtain ⟨η.inv_left, η.inv_right⟩ := Classical.choose_spec (η.is_iso X)
    use D.comp (η_inv) (ε_inv)
    constructor
    . rw [D.comp_assoc]
      nth_rw 2 [<-D.comp_assoc]
      rw [ε.inv_left, D.comp_id, η.inv_left]
    rw [D.comp_assoc]
    nth_rw 2 [<-D.comp_assoc]
    rw [η.inv_right, D.comp_id, ε.inv_right]
}

infixr:80 " ∘ " => NatIso_vcomp_NatIso

end Compositions

theorem is_nat_iso_iff_inv {C : Category} {D : Category}
  {F G : Functor C D} (η : NatTrafo F G) :
  (∃ h : NatIso F G, h.toNatTrafo = η) ↔
  ∃ (ε : NatIso G F), (ε.toNatTrafo ∘ η) = Id_Trafo F ∧ (η ∘ ε.toNatTrafo) = Id_Trafo G := by
  constructor
  . intro h1
    obtain ⟨h, h_is_η⟩ := h1
    have h_is_η : h.obj = η.obj := congrArg NatTrafo.obj h_is_η
    let ε : NatIso G F :=
      {
        obj := fun X ↦ Classical.choose (h.is_iso X)
        is_nat := by
          intro X Y f
          dsimp
          have h1 := h.is_nat f
          let inv_X := Classical.choose (h.is_iso X)
          let inv_Y := Classical.choose (h.is_iso Y)

          -- Extract the proof that inv_X is the inverse of h_X

          obtain ⟨inv_X_left, inv_X_right⟩ := Classical.choose_spec (h.is_iso X)
          obtain ⟨inv_Y_left, inv_Y_right⟩ := Classical.choose_spec (h.is_iso Y)
          have h2 : G.map f = D.comp (D.comp (h.obj Y) (F.map f)) inv_X := by
            rw [←D.comp_id (G.map f), ←inv_X_right, D.comp_assoc]
            exact (congrArg (fun g ↦ D.comp g (Classical.choose (h.is_iso X))) h1)

          have h3 : D.comp inv_Y (G.map f) = D.comp inv_Y (D.comp (D.comp (h.obj Y) (F.map f)) inv_X):= congrArg (fun g ↦ D.comp (inv_Y) g) h2
          rw [D.comp_assoc, D.comp_assoc, inv_Y_left, D.id_comp] at h3
          exact Eq.symm h3
        is_iso := by
          intro X
          use h.obj X
          dsimp
          constructor
          . exact (Classical.choose_spec (h.is_iso X)).2
          exact (Classical.choose_spec (h.is_iso X)).1
      }
    use ε
    constructor
    . apply NatTrafo.ext
      intro X
      dsimp [vertical_comp, Id_Trafo]
      rw [<-h_is_η, (Classical.choose_spec (h.is_iso X)).1]
    apply NatTrafo.ext
    intro X
    dsimp [vertical_comp, Id_Trafo]
    rw [<-h_is_η, (Classical.choose_spec (h.is_iso X)).2]
  intro h1
  obtain ⟨ε, inv⟩ := h1
  let h : NatIso F G :=
  {
    obj := η.obj
    is_nat := η.is_nat
    is_iso := by
      intro X
      dsimp
      use (ε.obj X)
      constructor
      . let h := congrFun (congrArg NatTrafo.obj inv.1) X
        dsimp [vertical_comp, Id_Trafo] at h
        exact h
      . let h := congrFun (congrArg NatTrafo.obj inv.2) X
        dsimp [vertical_comp, Id_Trafo] at h
        exact h
  }
  use h

/- The category of functors with natural transformations as morphisms is a category-/

def Functorcat (C : Category) (D : Category) : Category :=
{
  Obj := Functor C D
  Hom := fun F G ↦ NatTrafo F G
  id := fun F ↦ Id_Trafo F
  comp := fun ε η ↦ ε ∘ η
  comp_assoc := fun η ε γ ↦ by
    dsimp
    apply NatTrafo.ext
    intro X
    dsimp [vertical_comp]
    rw [D.comp_assoc]
  comp_id :=fun η ↦ by
    dsimp
    apply NatTrafo.ext
    intro X
    dsimp [vertical_comp, Id_Trafo]
    rw [D.comp_id]
  id_comp := fun η ↦ by
    dsimp
    apply NatTrafo.ext
    intro X
    dsimp [vertical_comp, Id_Trafo]
    rw [D.id_comp]
}

def Natiso_functor_comp_id {C D : Category} (F : Functor C D) : NatIso F (F ∘ Id_Functor C) :=
{
  obj := fun X => D.id (F.obj X)
  is_nat := by
    intro X Y f
    dsimp [Id_Functor, Functor_comp]
    rw [D.id_comp, D.comp_id]
  is_iso := by
    intro X
    dsimp
    use (D.id (F.obj X))
    constructor
    . dsimp [Id_Functor, Functor_comp]
      rw [D.id_comp]
    . dsimp [Id_Functor, Functor_comp]
      rw [D.id_comp]
}
/- classical definition of a monad as described in Richter's book-/

lemma is_iso_functor_comp_id {C D : Category} (F : Functor C D) : F ≃ (F ∘ (Id_Functor C)) := by
  use Natiso_functor_comp_id F

def Natiso_id_comp_functor {C D : Category} (F : Functor C D) : NatIso F ((Id_Functor D) ∘ F) :=
{
  obj := fun X => D.id (F.obj X)
  is_nat := by
    intro X Y f
    dsimp [Id_Functor, Functor_comp]
    rw [D.id_comp, D.comp_id]
  is_iso := by
    intro X
    dsimp
    use (D.id (F.obj X))
    constructor
    . dsimp [Id_Functor, Functor_comp]
      rw [D.id_comp]
    . dsimp [Id_Functor, Functor_comp]
      rw [D.id_comp]
}

lemma is_iso_id_comp_functor {C D : Category} (F : Functor C D) : F ≃ ((Id_Functor D) ∘ F) := by
  use Natiso_id_comp_functor F

def Natiso_functor_assoc {C D E F : Category} (K : Functor C D) (L : Functor D E) (M : Functor E F) : NatIso ((M ∘ L) ∘ K) (M ∘ (L ∘ K)):=
{
  obj := fun X ↦ F.id ((M ∘ L ∘ K).obj X)
  is_nat := by
    intro X Y f
    dsimp [Functor_comp]
    rw [F.comp_id, F.id_comp]
  is_iso := by
    intro X
    dsimp
    use (F.id ((M ∘ L ∘ K).obj X))
    constructor
    . dsimp [Id_Functor, Functor_comp]
      rw [F.id_comp]
    . dsimp [Id_Functor, Functor_comp]
      rw [F.id_comp]
}

lemma iso_of_inverse_functors {C D : Category} (F : Functor C D) (G : Functor D C) (h₂ : (G ∘ F) = Id_Functor C) (h₁ : (F ∘ G) = Id_Functor D) : C ≅ D := by
  use F
  use G
  let (η : NatIso (F ∘ G) (Id_Functor D)) :=
    {
      obj := fun X ↦ cast (by rw [h₁]; rfl) (D.id X)
      is_nat := by
        intros X Y f
        have HX : (F ∘ G).obj X = ((Id_Functor D).obj X) := by rw [h₁]
        have HY : (F ∘ G).obj Y = ((Id_Functor D).obj Y):= by rw [h₁]
        have h_map : HEq ((F ∘ G).map f) ((Id_Functor D).map f) :=
          h₁ ▸ HEq.rfl
        let h_map_cast := heq_map_cast f (Eq.symm HX) (Eq.symm HY) (HEq.symm h_map)
        simp only [Id_Functor]
        rw [h_map_cast, cast_right_comp]
        swap
        . exact Eq.symm HX
        let h1 := cast_compose HX HY (cast (hom_type_eq_left (Eq.symm HY)) (D.id Y)) ((F ∘ G).map f)
        have h2 : D.comp (cast (hom_type_eq_left HY) (cast (hom_type_eq_left (Eq.symm HY)) (D.id Y))) (cast (hom_type_eq HX HY) ((F ∘ G).map f))= f := by
          rw [cast_cast, h_map_cast, cast_cast]
          dsimp [Id_Functor]
          rw [D.id_comp]
        rw [h2] at h1
        have h3 : cast (hom_type_eq_left (Eq.symm HX)) f = D.comp (cast (hom_type_eq_left (Eq.symm HY)) (D.id Y)) ((F ∘ G).map f) := by
          nth_rw 1 [h1]
          rw [cast_cast (hom_type_eq_left HX)]
        rw [D.comp_id, h3, h_map_cast]
      is_iso := by
        dsimp
        intro X
        have HX : (F ∘ G).obj X = ((Id_Functor D).obj X) := by rw [h₁]
        use cast (Eq.symm (hom_type_eq_right HX)) ((Id_Functor D).map (D.id X))
        constructor
        . dsimp [Id_Functor]
          have h_map : HEq ((F ∘ G).map (D.id X)) ((Id_Functor D).map (D.id X)) :=
          h₁ ▸ HEq.rfl
          let h_map_cast := heq_map_cast (D.id X) (Eq.symm HX) (Eq.symm HX) (HEq.symm h_map)
          dsimp [Id_Functor] at HX
          rw [cast_comp_outer, D.id_comp (D.id X)]
          unfold Functor_comp
          dsimp
          unfold Functor_comp at h_map_cast
          dsimp [Id_Functor] at h_map_cast
          rw [<-F.map_id, <-G.map_id, h_map_cast]
          exact Eq.symm HX
        . dsimp [Id_Functor]
          have h_map : HEq ((F ∘ G).map (D.id X)) ((Id_Functor D).map (D.id X)) :=
          h₁ ▸ HEq.rfl
          let h_map_cast := heq_map_cast (D.id X) (Eq.symm HX) (Eq.symm HX) (HEq.symm h_map)
          dsimp [Id_Functor] at HX
          --rw [(cast_comp_outer (Eq.symm HX) (D.id X) (D.id X)), D.id_comp (D.id X)]
          rw [cast_comp_inner (Eq.symm HX) (D.id X) (D.id X), D.id_comp (D.id X)]
          rfl
    }
  let (ε : NatIso (G ∘ F) (Id_Functor C)) :=
    {
      obj := fun X ↦ cast (by rw [h₂]; rfl) (C.id X)
      is_nat := by
        intros X Y f
        have HX : (G ∘ F).obj X = ((Id_Functor C).obj X) := by rw [h₂]
        have HY : (G ∘ F).obj Y = ((Id_Functor C).obj Y) := by rw [h₂]
        have h_map : HEq ((G ∘ F).map f) ((Id_Functor C).map f) :=
          h₂ ▸ HEq.rfl
        let h_map_cast := heq_map_cast f (Eq.symm HX) (Eq.symm HY) (HEq.symm h_map)
        simp only [Id_Functor]
        rw [h_map_cast, cast_right_comp]
        swap
        · exact Eq.symm HX
        let h1 := cast_compose HX HY (cast (hom_type_eq_left (Eq.symm HY)) (C.id Y)) ((G ∘ F).map f)
        have h2 : C.comp (cast (hom_type_eq_left HY) (cast (hom_type_eq_left (Eq.symm HY)) (C.id Y))) (cast (hom_type_eq HX HY) ((G ∘ F).map f)) = f := by
          rw [cast_cast, h_map_cast, cast_cast]
          dsimp [Id_Functor]
          rw [C.id_comp]
        rw [h2] at h1
        have h3 : cast (hom_type_eq_left (Eq.symm HX)) f = C.comp (cast (hom_type_eq_left (Eq.symm HY)) (C.id Y)) ((G ∘ F).map f) := by
          nth_rw 1 [h1]
          rw [cast_cast (hom_type_eq_left HX)]
        rw [C.comp_id, h3, h_map_cast]
      is_iso := by
        dsimp
        intro X
        have HX : (G ∘ F).obj X = ((Id_Functor C).obj X) := by rw [h₂]
        use cast (Eq.symm (hom_type_eq_right HX)) ((Id_Functor C).map (C.id X))
        constructor
        · dsimp [Id_Functor]
          have h_map : HEq ((G ∘ F).map (C.id X)) ((Id_Functor C).map (C.id X)) :=
            h₂ ▸ HEq.rfl
          let h_map_cast := heq_map_cast (C.id X) (Eq.symm HX) (Eq.symm HX) (HEq.symm h_map)
          dsimp [Id_Functor] at HX
          rw [cast_comp_outer (Eq.symm HX) (C.id X) (C.id X), C.id_comp (C.id X)]
          unfold Functor_comp
          dsimp
          unfold Functor_comp at h_map_cast
          dsimp [Id_Functor] at h_map_cast
          rw [<-G.map_id, <-F.map_id, h_map_cast]

        · dsimp [Id_Functor]
          have h_map : HEq ((G ∘ F).map (C.id X)) ((Id_Functor C).map (C.id X)) :=
            h₂ ▸ HEq.rfl
          let h_map_cast := heq_map_cast (C.id X) (Eq.symm HX) (Eq.symm HX) (HEq.symm h_map)
          dsimp [Id_Functor] at HX
          rw [cast_comp_inner (Eq.symm HX) (C.id X) (C.id X), C.id_comp (C.id X)]
          rfl
    }
  constructor
  . use η
  use ε

structure Equivalence {C D : Category} (h : C ≅ D) where
  functor    : Functor C D
  inverse    : Functor D C
  unitIso    : NatIso (functor ∘ inverse) (Id_Functor D)
  counitIso  : NatIso (inverse ∘ functor) (Id_Functor C)


lemma Catprod_assoc (C D E : Category) : ((C × D) × E) ≅ (C × (D × E)) := by
  let F := Cat_assoc_left C D E
  let G := Cat_assoc_right C D E
  have h₁ : (G ∘ F) = Id_Functor ((C × D) × E) := by
    apply Functor.ext
    swap
    . intro X
      dsimp [Cat_prod] at X
      dsimp [Functor_comp, Id_Functor, Cat_prod, Cat_assoc_right, Cat_assoc_left, F, G]
    intro X Y f
    dsimp [Cat_prod] at X f
    dsimp [Functor_comp, Id_Functor, Cat_prod, Cat_assoc_right, Cat_assoc_left, F, G]
  have h₂ : (F ∘ G) = Id_Functor (C × (D × E)) := by
    apply Functor.ext
    swap
    . intro X
      dsimp [Cat_prod] at X
      dsimp [Functor_comp, Id_Functor, Cat_prod, Cat_assoc_right, Cat_assoc_left, F, G]
    intro X Y f
    dsimp [Cat_prod] at X f
    dsimp [Functor_comp, Id_Functor, Cat_prod, Cat_assoc_right, Cat_assoc_left, F, G]
  exact iso_of_inverse_functors F G h₁ h₂
