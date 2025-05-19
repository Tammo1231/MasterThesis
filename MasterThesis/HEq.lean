/- Why HEq? HEq stands for heterogeneous equality. This means that things are essentially the same, but have different, but provably equal types. type_eq_of_heq is a proof of this statement. The reason this exists, is that types not identified automatically even though they really are equal, i.e. they are `propositionally` the same, but not `definitionally`. I am not sure yet, if this is preventable, by using classes or telling lean to identify certain things. In a sense this document exists to test the limits of this approach.-/

import Mathlib.Tactic.Lemma

namespace mymon

theorem type_eq_of_heq {α β : Sort u} {a : α} {b : β} (h : HEq a b) : α = β :=
  by
  cases h
  rfl
/- This is really nice. Together with cast_heq this essentially states that HEq is just casting in disguise. This will become important later-/

lemma heq_cast {α β : Sort u} {a : α} {b : β} (h : HEq a b) :
  ∃ (p : α = β), b = cast p a := by
  cases h

  /- cases h essentially unfolds the property of the HEq that it is a structure consisting of a single constructor. -/

  exact ⟨rfl, rfl⟩

theorem pi_congr {α : Sort u} {β γ : α → Sort v}
  (h_pointwise : ∀ x, β x = γ x) :
  ((x : α) → β x) = ((x : α) → γ x) :=
  congrArg (fun T => (x : α) → T x) (funext h_pointwise)

-- This says that post composing pointiwse is the same as formally postcomposing the function (I need to explain this better)

theorem cast_fun_eq {α : Sort u} {β γ : α → Sort v}
    (f : ∀ x, β x) (h_pointwise : ∀ x, β x = γ x) :
    (fun x => cast (h_pointwise x) (f x)) = cast (pi_congr h_pointwise) f := by
  have h : β = γ := funext h_pointwise
  subst h
  rfl

-- function extensionality theorem for functions that are essentially the same but not of the same type

theorem HEq_funext {α : Sort u} {β γ : α → Sort v}
  {f : ∀ x, β x} {g : ∀ x, γ x}
  (hβγ : ∀ x, HEq (f x) (g x)) :
  HEq f g :=
by
  -- Step 1: Extract `β x = γ x`

  have h_type_eq : ∀ x, β x = γ x := fun x => type_eq_of_heq (hβγ x)

  -- Step 2: Define `f'`, a function with the same type as `g`

  let f' := fun x => cast (h_type_eq x) (f x)

  -- Step 3: Show `HEq (f' x) (g x)` for all `x`

  have h_pointwise : ∀ x, HEq (f' x) (g x) := fun x => by
      -- Transport the HEq relation through casting

      have h_cast : HEq (f' x) (f x) := cast_heq (h_type_eq x) (f x)
      exact HEq.trans h_cast (hβγ x)

  -- Step 4: Prove that `f` and `g` are equal for all `x`

  have h_eq : ∀ x, f' x = g x := fun x => eq_of_heq (h_pointwise x)

  -- Step 5: Apply function extensionality

  have h_fun_eq : f' = g := funext h_eq

  -- We essentially reduced the problem to the case where g is of a specific form

  have h : f' = cast (pi_congr h_type_eq) f := by exact cast_fun_eq f h_type_eq

  -- from here on out, we use case_heq and cast_fun_eq

  have h' : HEq f f' := by
    rw [h]
    apply HEq.symm
    apply cast_heq

  have h'' : HEq f' g := by
    rw [h_fun_eq]

  exact HEq.trans h' h''

/- Equality is preserved by casting. (Think of this as postcomposi with an isomorphism preserves equality)-/

def cast_eq {α β : Type u} {A B : α} (h : A = B) (h' : α = β) : cast h' A = cast h' B := congrArg (cast h') h

theorem cast_cast {α β : Sort u} (h : α = β) (x : α) :
  cast (Eq.symm h) (cast (h) x) = x := by
  subst h
  rfl

theorem HEq.symm {α β : Sort u} {a : α} {b : β} (h : HEq a b) : HEq b a := by
  cases h
  exact HEq.rfl
/- This is not needed for what comes after, but i think it gives a lot of character to HEq. If a and b have the same type, then the statement that they are heterogeneously equal, just means they are equal. In that sense, HEq is really an extension of Eq-/

theorem HEq_ext_eq {α : Sort u} (a b : α) (h: HEq a b) : a = b := by
  cases h
  rfl
