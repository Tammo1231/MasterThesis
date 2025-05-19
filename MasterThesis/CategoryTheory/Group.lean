import MasterThesis.CategoryTheory.Category

namespace mymon

structure Group where
  obj : Type u
  mul : obj → obj → obj
  one : obj
  inv : obj → obj
  mul_assoc : ∀ a b c : obj, mul (mul a b) c = mul a (mul b c)
  one_mul   : ∀ a : obj, mul one a = a
  mul_one   : ∀ a : obj, mul a one = a
  left_inv  : ∀ a : obj, mul (inv a) a = one

/-- A group homomorphism between groups `G` and `H`. -/

structure GroupHom (G H : Group) where
  map_obj : G.obj → H.obj
  map_mul : ∀ a b : G.obj,
    map_obj (G.mul a b) = H.mul (map_obj a) (map_obj b)
  map_one : map_obj G.one = H.one
  map_inv : ∀ a : G.obj,
    map_obj (G.inv a) = H.inv (map_obj a)

def GroupHom_id (G : Group) : GroupHom G G :=
{
  map_obj := fun g ↦ g
  map_mul := fun a b ↦ by simp
  map_one := by simp
  map_inv := fun a ↦ by simp
}

def GroupHom_comp {G H W : Group} (f : GroupHom G H) (g : GroupHom H W) : GroupHom G W :=
{
  map_obj := fun a ↦ (g.map_obj ∘ f.map_obj) a
  map_mul := fun a b ↦ by
    dsimp
    rw [f.map_mul, g.map_mul]
  map_one := by
    dsimp
    rw [f.map_one, g.map_one]
  map_inv := fun a ↦ by
    dsimp
    rw [f.map_inv, g.map_inv]
}

theorem GroupHom.ext {G H : Group} {f g : GroupHom G H}
  (h : ∀ x : G.obj, f.map_obj x = g.map_obj x) : f = g :=
by
  cases f
  cases g
  congr
  funext x
  exact h x

/-This worked, but somehow Lean4 now all of the sudden refuses to compute u+1...-/

def GroupCat : Category :=
{
  Obj := Group
  Hom := fun G H ↦ GroupHom G H
  id := fun G ↦ GroupHom_id G
  comp := fun {G H W : Group} (g : GroupHom H W) (f : GroupHom G H) ↦
            GroupHom_comp f g
  comp_assoc := fun {G H W X : Group} f g h ↦ by
    apply GroupHom.ext
    intro x
    change h.map_obj (g.map_obj (f.map_obj x)) = ((h.map_obj ∘ g.map_obj) ∘ f.map_obj) x
    rfl
  comp_id := fun {G H} f ↦ by
    dsimp
    rfl
  id_comp := fun {G H} f ↦ by
    dsimp
    rfl
}

end mymon
