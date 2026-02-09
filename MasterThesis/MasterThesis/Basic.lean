import MasterThesis.MyTopology
import MasterThesis.SupportOfSection
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Topology.Sheaves.Functors

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace MyTopology Supportofsection CategoryTheory TopCat Opposite Presheaf

variable {X Y : TopCat}
variable (f : X ⟶ Y)
variable [T2Space Y] [LocallyCompactSpace Y]
variable {F G : Presheaf Ab X}

/- Locally compact spaces are compactly generated-/
instance : CompactlyGeneratedSpace Y := by infer_instance

/- A section over U of the pushforward has proper support if the restriction of f to its support with image in U is proper. We define this not in terms of these restrictions for technical reasons.-/
def HasProperSupport
  (U : Opens Y)
  (s : F.obj (op ((Opens.map f).obj U))) : Prop :=
∀ ⦃K : Set Y⦄, K ⊆ U.1 → IsCompact K →
  IsCompact (SupportOfSection ((Opens.map f).obj U) s ∩ f ⁻¹' K)

/- For the specific use of theorems in the mathlib, we define the restriction of f to the support of a section-/
def restr_to_supp (U : Opens Y) (s : F.obj (op ((Opens.map f).obj U))) :=
  have restr_maps : ∀ (x : X), x ∈ SupportOfSection ((Opens.map f).obj U) s → f x ∈ U.1 := by
    intro x ⟨hxU, hx⟩
    simpa
  Subtype.map f (fun x hx ↦ restr_maps x hx)


/- This is the classical definition of sections with proper support. It is just not very nice to use. We need the property for the proof that a glued section has proper support -/
theorem restr_to_supp_isproper (U : Opens Y) (s : F.obj (op ((Opens.map f).obj U))) (hf : HasProperSupport f U s) : IsProperMap (restr_to_supp f U s) := by
  haveI : LocallyCompactSpace U := IsOpen.locallyCompactSpace U.2
  /-for locally compact Hausdorff spaces, the usual definition of properness and the one from mathlib agree, so we use the classical one. A lot of the difficulty here is that you always need to be explicit about which subspace you are working in. Its not difficult really, but rather tedious-/
  apply (isProperMap_iff_isCompact_preimage).2
  constructor
  · apply Continuous.subtype_map
    · exact f.hom.continuous
    intro x ⟨hxU, hx⟩
    simpa
  intro K hK
  let hKU := Subtype.coe_image_subset U.1 K
  let hK := IsCompact.image hK continuous_subtype_val
  have H : SupportOfSection ((Opens.map f).obj U) s ∩ f ⁻¹' (Subtype.val '' K) = restr_to_supp f U s ⁻¹' K := by
    ext x
    constructor
    · intro hx
      unfold restr_to_supp
      simp
      use hx.1
      obtain ⟨y, hyK, fxy⟩ := hx.2
      convert hyK
      ext
      exact Eq.symm fxy
    intro hx
    obtain ⟨hxsupp, hx, eq⟩ := hx
    constructor
    · convert hxsupp.2
      exact Eq.symm eq
    use restr_to_supp f U s hxsupp
    constructor
    · exact hx
    rw [← eq]
    rfl
  have H' : Subtype.val ⁻¹' (SupportOfSection ((Opens.map f).obj U) s ∩ f ⁻¹' (Subtype.val '' K)) = restr_to_supp f U s ⁻¹' K := by
    rw [<-(Function.Injective.preimage_image Subtype.val_injective (restr_to_supp f U s ⁻¹' K))]
    rw[H]
  rw [<-H', Subtype.isCompact_iff]
  convert hf hKU hK
  simp

/- The conidition for a section to be proper is always closed in the appropriate subspace-/
lemma ProperSupport_closed {f : X ⟶ Y} {U : Opens Y} (s : F.obj (op ((Opens.map f).obj U))) (K : Set Y) (hK : IsCompact K) : IsClosed ((Subtype.val : f⁻¹'(U) → X) ⁻¹' (SupportOfSection ((Opens.map f).obj U) s ∩ f ⁻¹' K)) := by
  simp
  exact IsClosed.inter (support_closed s) (IsClosed.preimage continuous_subtype_val (IsClosed.preimage f.hom.continuous (IsCompact.isClosed hK)))


/- I essentially realized that we always want to check properness in f^-1(U) because we only know that the support of our section is closed in that set. Maybe i will take this as a definition at some point-/
def HasProperSupport_iff_subspace (U : Opens Y) (s : F.obj (op ((Opens.map f).obj U))) : HasProperSupport f U s ↔ ∀ ⦃K : Set Y⦄, K ⊆ U.1 → IsCompact K → IsCompact ((Subtype.val : f⁻¹'(U) → X) ⁻¹' (SupportOfSection ((Opens.map f).obj U) s ∩ f ⁻¹' K) ) := by
  constructor
  · intro h K hKU hK
    exact (Compact_iff_Compact_in_subspace
          (U := (ConcreteCategory.hom f) ⁻¹' (U : Set Y))
          (subset_trans Set.inter_subset_right (Set.preimage_mono hKU))).1 (h hKU hK)
  intro h K hKU hK

-- Let S be the set in X you want to prove compact
  let S : Set X :=
    SupportOfSection ((Opens.map f).obj U) s ∩ (ConcreteCategory.hom f) ⁻¹' K

    -- g is the inclusion of the subspace into X
  let g : ((ConcreteCategory.hom f) ⁻¹' (U : Set Y)) → X := Subtype.val

  -- you have H : IsCompact (g ⁻¹' S)   (this is your assumption in this direction)
  have h_range : S ⊆ Set.range g := by
    intro x hx
    refine ⟨⟨x, ?_⟩, rfl⟩
    -- need x ∈ f ⁻¹' U
    -- this is where you use your containment lemma:
    exact (subset_trans Set.inter_subset_right (Set.preimage_mono hKU)) hx
  have himage : g '' (g ⁻¹' S) = S := by
    simpa [g] using (image_preimage_eq_of_subset (f := g) h_range)
  have hImg : IsCompact (g '' (g ⁻¹' S)) :=
    IsCompact.image (h hKU hK) (by simpa [g] using (continuous_subtype_val))
  simp [S] at himage
  simp [S] at hImg
  have h'' : IsCompact (SupportOfSection ((Opens.map f).obj U) s ∩ (ConcreteCategory.hom f) ⁻¹' K) := by simpa [himage] using hImg
  exact h''

/- If supp(s)⊆supp(t) and t has proper support, then s has proper support-/
theorem ProperSection_monotone {F G : Presheaf Ab X} {f : X ⟶ Y} {U : Opens Y} (s : F.obj (op ((Opens.map f).obj U))) (t : G.obj (op ((Opens.map f).obj U))) (ht : HasProperSupport f U t) (hst : (SupportOfSection ((Opens.map f).obj U) s) ⊆ (SupportOfSection ((Opens.map f).obj U) t)) : HasProperSupport f U s := by
  apply (HasProperSupport_iff_subspace f U s).2
  intro K hKU hK
  let ht := (HasProperSupport_iff_subspace f U t).1 ht hKU hK
  apply IsCompact.of_isClosed_subset ht
  · apply ProperSupport_closed s K hK
  apply preimage_mono
  apply inter_subset_inter_left
  exact hst

/- Sections with proper support over an open set U form a subgroup of F(U). For this, we need that if K is compact in Y, then it is also closed. For that we take Y to be Haussdorff-/
def ProperSections_addsubgroup (F : Presheaf Ab X) (f : X ⟶ Y) (U : Opens Y) :
    AddSubgroup (F.obj (op ((Opens.map f).obj U))) :=
    { carrier := { s | HasProperSupport f U s }
      zero_mem' := by
        intro K hKU hK
        suffices hS :
          SupportOfSection ((Opens.map f).obj U) (0 : _) ∩ f ⁻¹' K = (∅ : Set X) by
            rw [hS]
            apply isCompact_empty
        rw [support_zero]
        simp
      add_mem' := by
        intro s t hs ht
        apply (HasProperSupport_iff_subspace f U (s+t)).2
        intro K hKU hK
        let hs := (HasProperSupport_iff_subspace f U s).1 hs hKU hK
        let ht := (HasProperSupport_iff_subspace f U t).1 ht hKU hK
        have h : IsCompact ((Subtype.val : f⁻¹' U → X)⁻¹' (((SupportOfSection ((Opens.map f).obj U) s ∪ SupportOfSection ((Opens.map f).obj U) t)) ∩ f ⁻¹' K)) := by
          rw [union_inter_distrib_right]
          simp
          rw [<-preimage_inter, <-preimage_inter]
          exact IsCompact.union hs ht
        apply IsCompact.of_isClosed_subset h
        · simp
          exact IsClosed.inter (support_closed (s+t)) (IsClosed.preimage continuous_subtype_val (IsClosed.preimage f.hom.continuous (IsCompact.isClosed hK)))
        apply preimage_mono
        apply inter_subset_inter_left
        exact SupportOfSection_add s t
      neg_mem' := by
        intro s hs K hKU hK
        rw [SupportOfSection_neg]
        exact hs hKU hK
      }

/- The restriction of a section with proper support has proper support-/
theorem Proper_sec_res_prop {f : X ⟶ Y} (V : Opens Y) (U : Opens Y) (i : V ⟶ U) (s : ProperSections_addsubgroup F f U) : (F.map ((Opens.map f).map i).op) s.1 ∈ ProperSections_addsubgroup F f V := by
  intro K hKV hK
  rw [SupportOfSection_res_eq]
  have h' : (f⁻¹' V) ∩ f⁻¹' K = f⁻¹' K := by
    apply inter_eq_self_of_subset_right
    exact preimage_mono hKV
  simp
  rw [inter_assoc, h']
  exact s.2 (le_trans hKV (leOfHom i)) hK

/- this is going to be the restriction map of the proper pushforward-/
def Propersection_restr {f : X ⟶ Y} (V : Opens Y) (U : Opens Y) (i : V ⟶ U) :
(ProperSections_addsubgroup F f U) →+ (ProperSections_addsubgroup F f V) :=
  {
  toFun := fun s ↦ ⟨(F.map ((Opens.map f).map i).op) s.1, Proper_sec_res_prop V U i s⟩
  map_zero' := by simp
  map_add' := by
    intro x y
    simp
  }

/- The proper pushforward of a presheaf-/
def ProperPush_func_obj (F : Presheaf Ab X) (f : X ⟶ Y) : Presheaf Ab Y :=
  {
    obj U := ⟨ProperSections_addsubgroup F f (unop U)⟩
    map {U V : (Opens Y)ᵒᵖ} i := AddCommGrpCat.ofHom (Propersection_restr V.unop U.unop i.unop)
    map_id U := by
      · ext s
        simp [Propersection_restr]
    map_comp f g:= by
      · ext s
        simp [Propersection_restr]
  }

/-The support of the image of a section under a natural transformation does not grow.-/
lemma Supp_im_le {F G : Presheaf Ab X} (α : F ⟶ G) {U : Opens X} (s : F.obj (op U)) : SupportOfSection U ((α.app (op U)) s) ⊆ SupportOfSection U s := by
  intro x ⟨hxU, hxs⟩
  use hxU
  by_contra h
  let H := stalkFunctor_map_germ_apply U x hxU α s
  rw [h] at H
  rw [map_zero] at H
  exact hxs (Eq.symm H)

/- Given a map of Presheaves, we obtain a map between the respective proper Pushforwards-/
def ProperPush_func_map {F G : Presheaf Ab X} (f : X ⟶ Y) (α : F ⟶ G) (U : Opens Y) : (ProperSections_addsubgroup F f U) →+ (ProperSections_addsubgroup G f U) :=
  {
    toFun s := ⟨(α.app (op ((Opens.map f).obj U))) s, ProperSection_monotone ((α.app (op ((Opens.map f).obj U))) s) s.1 s.2 (Supp_im_le (U := (Opens.map f).obj U) α s)⟩
    map_zero' := by simp
    map_add' := by intro s t; ext; simp
  }

/- The Functor that sends a Sheaf on X to its proper pushforward-/
@[simps!]
def ProperPushfwd (f : X ⟶ Y) : Presheaf Ab X ⥤ Presheaf Ab Y :=
  {
    obj F := ProperPush_func_obj F f
    map α :=  { app U :=  AddCommGrpCat.ofHom (ProperPush_func_map f α (unop U))
                naturality U V i := by ext s; simp [ProperPush_func_map, ProperPush_func_obj, Propersection_restr]
              }
    map_id F := by
      ext U s
      simp
      rfl
    map_comp α β:= by
      ext U s
      simp
      rfl
  }

@[simp]
theorem PropPushfoward_map_apply' (f : X ⟶ Y) {ℱ 𝒢 : X.Presheaf Ab} (α : ℱ ⟶ 𝒢) {U : (Opens Y)ᵒᵖ} : ((((ProperPushfwd f)).map α).app U) = AddCommGrpCat.ofHom (ProperPush_func_map f α (unop U)) := rfl

/-The map from the proper pushforward in to the pushforward-/
def ProperPush_into_Push (f : X ⟶ Y) : (ProperPushfwd f) ⟶ (pushforward Ab f) :=
  {
    app F :=
      {
        app U := AddCommGrpCat.ofHom (AddSubgroup.subtype (ProperSections_addsubgroup F f (unop U)))
        naturality {U V} i := by ext; simp
      }
    naturality {F G} α := by ext; simp; rfl
  }

/- This map is componentwise injective-/
lemma ProperPush_into_Push_app_injective (F : Presheaf Ab X) (f : X ⟶ Y) (U : Opens Y) : Function.Injective (((ProperPush_into_Push f).app F).app (op U)) := by
  apply AddSubgroup.subtype_injective

/- The properpushforward of a sheaf is a sheaf-/
theorem ProperPush_isSheaf (F : Presheaf Ab X) (f : X ⟶ Y) (hF : F.IsSheaf) : ((ProperPushfwd (f : X ⟶ Y)).obj F).IsSheaf := by
  apply (isSheaf_iff_isSheafUniqueGluing ((ProperPushfwd (f : X ⟶ Y)).obj F)).2
  intro ι U sf sf_comp
  /- The plan here is that we know already that the pushforward of a sheaf is a sheaf. therefore we obtain a section that glues the images of the inclusion. We show that that section is proper, i.e. in fact lies in the proper pushforward -/
  /- this is the family in question. I just noticed that mathlib has a theorem for this. Maybe i will adapt this later.-/
  let sf' := fun (i : ι) ↦ (((ProperPush_into_Push f).app F).app (op (U i))) (sf i)
  have sf'_comp : IsCompatible ((pushforward Ab f).obj F) U sf' := by
    intro i j
    simp [sf']
    let h := ((ProperPush_into_Push f).app F).naturality (((U i).infLELeft (U j)).op)
    have h' := congrArg (fun φ => φ (sf i)) h
    dsimp at h'
    rw [<-h']
    have h := ((ProperPush_into_Push f).app F).naturality (((U i).infLERight (U j)).op)
    have h' := congrArg (fun φ => φ (sf j)) h
    dsimp at h'
    rw [<-h']
    apply congrArg
    exact sf_comp i j
  /-This is the gluing in the pushforward-/
  let ⟨ιs, hιs, ιs_unique⟩  := ((isSheaf_iff_isSheafUniqueGluing ((pushforward Ab f).obj F)).1 (Sheaf.pushforward_sheaf_of_sheaf f hF)) U sf' sf'_comp
  /- this is the core of the proof. I might do it somewhere else if i need similar facts later.-/
  have ιs_proper : HasProperSupport f (iSup U) ιs := by
    intro K hKU hK
    apply (Compact_iff_Compact_in_subspace (f⁻¹' (iSup U).1) (subset_trans inter_subset_right (preimage_mono hKU))).2
  /- lean does not identify iSup and the union of opens definitionally, so we have do it manually-/
    rw [Opens.iSup_def U] at hKU
    let ⟨τ, τ_cover⟩ := IsCompact.elim_finite_subcover hK (fun i ↦ (U i).1) ((fun i ↦ (U i).2)) hKU
    rw [<-(iUnion_subtype (fun (i : ι) ↦ (i ∈ τ)) (fun i ↦ (U i).1))] at τ_cover
    let := rel_compact_cover K hK (fun (i:τ) ↦ (U i)) τ_cover
    obtain ⟨V, hKV, hV⟩ := this
    let sfprop (i : τ):= (sf i).2 (hV i).1 (hV i).2
    dsimp at sfprop
    have h : (SupportOfSection ((Opens.map f).obj (iSup U)) ιs) ∩ f⁻¹' K ⊆ ⋃ (i : τ) , SupportOfSection ((Opens.map f).obj (U i)) (sf' i.1) ∩ f⁻¹' (closure (V i)) := by
      have h : f⁻¹' K ⊆ ⋃ i, f⁻¹' (closure (V i)) := by
        rw [<-preimage_iUnion]
        apply Subset.trans (preimage_mono hKV) (preimage_mono (iUnion_mono (fun i ↦ by apply subset_closure)))
      have h' i : (SupportOfSection ((Opens.map f).obj (iSup U)) ιs) ∩ f⁻¹' (closure (V i)) = SupportOfSection ((Opens.map f).obj (U i)) (sf' i) ∩ f⁻¹' (closure (V i)) := by
        nth_rw 1 [<-inter_eq_self_of_subset_right (preimage_mono (hV i).1), <-inter_assoc, <- hιs i]
        simp
        rw [(SupportOfSection_res_eq ((Opens.map f).obj (U i)) ((Opens.map f).obj (iSup U)) ((Opens.map f).map (Opens.leSupr U i)) ιs)]
        simp
      apply Subset.trans (inter_subset_inter_right (SupportOfSection ((Opens.map f).obj (iSup U)) ιs) h)
      rw [inter_iUnion]
      simp [h']
    have hclVU : (⋃ (i : τ) , SupportOfSection ((Opens.map f).obj (U i)) (sf' i.1) ∩ f⁻¹' (closure (V i))) ⊆ f⁻¹' (iSup U).1 := by
      apply Subset.trans (b := (⋃ (i : τ) , f⁻¹' (closure (V i))))
      · apply iUnion_mono
        intro i
        exact inter_subset_right
      refine Set.iUnion_subset (fun i => ?_)
      intro x hx
      have h2 : f x ∈ U i := (hV i).1 hx
      apply Set.mem_iUnion.2
      use U i
      simp [h2]
    apply IsCompact.of_isClosed_subset ((Compact_iff_Compact_in_subspace (f⁻¹' (iSup U).1) hclVU).1 (isCompact_iUnion (fun (i : τ) ↦ sfprop i))) (ProperSupport_closed ιs K hK)
    apply preimage_mono
    simp
    exact h
  /-our candidate for the glued section as well as the proof that the restriction to U i is sf i-/
  use ⟨ιs, ιs_proper⟩
  have nat (i: ι) : ((ProperPush_into_Push f).app F).app (op (U i)) (((ProperPushfwd f).obj F).map (Opens.leSupr U i).op (⟨ιs, ιs_proper⟩)) = sf' i :=  by
    have h' := congrArg (fun φ => φ ⟨ιs, ιs_proper⟩) (((ProperPush_into_Push f).app F).naturality ((Opens.leSupr U i).op))
    dsimp at h'
    dsimp [ProperPush_into_Push]
    exact hιs i
  constructor
  · intro i
    apply ProperPush_into_Push_app_injective F f (U i)
    rw [nat i]
  /-This gluing is unique-/
  intro y hy
  have h : ((ProperPush_into_Push f).app F).app (op (iSup U)) y = ιs := by
    apply ιs_unique
    intro i
    have h' := congrArg (fun φ => φ y) (((ProperPush_into_Push f).app F).naturality (op (Opens.leSupr U i)))
    dsimp [AddCommGrpCat.Hom.hom] at h'
    simp [pushforward, iSup]
    rw [<-h']
    congr
    exact hy i
  apply ProperPush_into_Push_app_injective
  exact h





