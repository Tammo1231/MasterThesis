import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits

set_option linter.style.longLine false

open Set CategoryTheory Opposite TopologicalSpace TopCat Presheaf

variable {X Y : TopCat}
variable (f : X ⟶ Y)
variable {F G : Presheaf Ab X}

namespace Supportofsection
/-- support of the section of a sheaf of abelian groups -/
def SupportOfSection (U : Opens X) (s : F.obj (op U)) : Set X :=
  fun x =>
    ∃ hx : x ∈ U, (germ F U x hx) s ≠ 0

/- This expresses the support of a section as a subset of U. This is important for many proofs-/
def relative_SupportOfSection (U : Opens X) (s : F.obj (op U)) :
  Set U := fun ⟨x, hxU⟩ => (ConcreteCategory.hom (F.germ U x hxU)) s ≠ 0

/- The relationship between the definitions-/
lemma SupportOfSection_iff_relative (U : Opens X) (s : F.obj (op U)) : SupportOfSection U s = (↑) '' relative_SupportOfSection U s := by
  ext x
  constructor
  · intro ⟨hxU, hxne⟩
    refine ⟨⟨x, hxU⟩, ?_, rfl⟩
    exact hxne
  · intro ⟨⟨y, hyU⟩, hy, hyx⟩
    cases hyx
    refine ⟨hyU, by exact hy⟩

lemma supportOfsection_iff_relative' (U : Opens X) (s : F.obj (op U)) : (↑)⁻¹' SupportOfSection U s = relative_SupportOfSection U s := by
  have h' : (Subtype.val : U → X) ⁻¹' SupportOfSection U s= (Subtype.val : U → X) ⁻¹' ((↑) '' relative_SupportOfSection U s) := by exact congrArg (fun S ↦ (Subtype.val : U → X) ⁻¹' S) (SupportOfSection_iff_relative U s)
  rw [h']
  exact (preimage_image_eq (relative_SupportOfSection U s) Subtype.val_injective)

/- If x is in the complement of the support of a section, then its germ is 0-/
lemma germ_eq_zero_of_mem_compl_support (U : Opens X) (s : F.obj (op U)) (x : U) (hx : x ∈ (((Subtype.val) ⁻¹' SupportOfSection U s)ᶜ)) : (ConcreteCategory.hom (germ F U x x.2) s) = 0 :=
by
  apply notMem_setOf_iff.1 at hx
  unfold SupportOfSection at hx
  change
    ¬ ∃ (hxU : (Subtype.val x : X) ∈ U),
        (ConcreteCategory.hom (germ F U (Subtype.val x) hxU) s) ≠ 0
    at hx
  push_neg at hx
  exact hx x.property


/- the support of a section is closed if considered as a subset of U-/
lemma support_closed
    {U : Opens X}
    (s : F.obj (op U)) :
    IsClosed ((Subtype.val : U → X) ⁻¹' SupportOfSection U s) := by
    apply isOpen_compl_iff.1
    apply isOpen_iff_forall_mem_open.2
    intro x hx
    have hx1 := germ_eq_zero_of_mem_compl_support U s x hx
    rw [<- map_zero (ConcreteCategory.hom (germ F U (x : X) x.property))] at hx1
    let ⟨W, hxW, iU, iV, heq⟩ := germ_eq F (U := U) (V := U) x x.2 x.2 s (0 : ToType (F.obj (op U))) hx1
    refine ⟨(Subtype.val) ⁻¹' W.carrier, ?_⟩
    constructor
    · intro y hy
      apply notMem_setOf_iff.1
      unfold SupportOfSection
      change ¬ (∃ (hyU : (Subtype.val y : X) ∈ U), (ConcreteCategory.hom (germ F U (Subtype.val y) hyU) s) ≠ 0)
      intro ⟨hyU, p⟩
      simp at p
      let Q := (germ_res_apply F iU y hy) s
      rw [<-Q, heq, map_zero, map_zero] at p
      exact p rfl
    exact ⟨W.isOpen.preimage continuous_subtype_val, hxW⟩

/- Sections with proper support respect the additive structure on the sections of the pushforward, i.e. they form a subgroup-/
lemma support_zero (U : Opens X) : SupportOfSection U (0 : F.obj (op U)) = (∅ : Set X) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxU, h⟩
    rw [map_zero] at h
    exact h rfl
  intro h
  exact False.elim h

/- The support of the inverse of a section  s is the same as the support of s -/
lemma SupportOfSection_neg (U : Opens X) (s : F.obj (op U)) : SupportOfSection U (-s) = SupportOfSection U s :=by
  ext x
  have forward (U : Opens X) (s : F.obj (op U)) :
    x ∈ SupportOfSection U (-s) →
    x ∈ SupportOfSection U s := by
    intro hx
    rcases hx with ⟨hxU, h⟩
    rw [map_neg] at h
    exact ⟨hxU, neg_ne_zero.1 h⟩
  constructor
  · intro hx
    exact forward U s hx
  intro hx
  rw [<-neg_neg s] at hx
  exact forward U (-s) hx

/- The support of the addition of sections is contained in the union of the repective supports-/
lemma SupportOfSection_add {U : Opens X} (s t : F.obj (op U)) : SupportOfSection U (s + t) ⊆ SupportOfSection U s ∪ SupportOfSection U t := by
  intro x hx
  rcases hx with ⟨hxU, hx⟩
  rw [map_add] at hx
  by_contra h
  have ⟨h₁, h₂⟩ : x ∉ SupportOfSection U s ∧ x ∉ SupportOfSection U t := by
    refine (not_or).1 ?_
    simpa [Set.mem_union] using h
  let h₁ := ((notMem_setOf_iff.1) h₁)
  push_neg at h₁
  let h₂ := (notMem_setOf_iff.1) h₂
  push_neg at h₂
  let h₁ := h₁ hxU
  let h₂ := h₂ hxU
  have h : (ConcreteCategory.hom (F.germ U x hxU)) s + (ConcreteCategory.hom (F.germ U x hxU)) t = 0 := by
    rw [h₁, h₂]
    simp
  exact (hx h)

/- The support of the rest riction of a section s is contained in the support of s-/
lemma SupportOfSection_res_eq
  (V U : Opens X) (i : V ⟶ U) (s : F.1 (op U)) :
  SupportOfSection V (F.2 i.op s) = SupportOfSection U s ∩ V := by
  ext x
  constructor
  · intro ⟨hxV, hx⟩
    unfold SupportOfSection
    apply mem_inter
    · constructor
      rw [<-germ_res_apply F i x hxV s]
      exact hx
    exact hxV
  intro ⟨⟨hxU, hx⟩, hxV⟩
  unfold SupportOfSection
  constructor
  · rw [germ_res_apply F i x hxV s]
    exact hx

/- Given family of sections s_i with a gluing s, the support of s is the union of the supports of the s i-/
lemma support_of_fam_eq_gluing {ι : Type*} (U : (i : ι) → Opens X) (sf : (i : ι) → ToType (F.obj (op (U i)))) (s : ToType (F.obj (op (iSup U)))) (hs : F.IsGluing U sf s) : SupportOfSection (iSup U) s = ⋃ i, SupportOfSection (U i) (sf i) := by
  ext x
  constructor
  · intro ⟨hxU, hx⟩
    simp at hxU
    rcases hxU with ⟨i, hxi⟩
    simp
    use i
    refine ⟨hxi, ?_⟩
    rw [<-hs, (germ_res_apply F (Opens.leSupr U i) x hxi s)]
    exact hx
  simp
  intro i ⟨hxi, hx⟩
  refine ⟨Opens.mem_iSup.2 ⟨i, hxi⟩,?_⟩
  rw [<-(germ_res_apply F (Opens.leSupr U i) x hxi s)]
  rw [hs]
  exact hx

end Supportofsection
