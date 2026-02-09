import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Sets.Opens
set_option linter.style.longLine false

open Set TopologicalSpace

namespace MyTopology

variable {X : TopCat}

/- This exists in Mathlib, but this version is just more akin to what i want to use-/
lemma Compact_iff_Compact_in_subspace {K : Set X} (U : Set X) (hKU : K ⊆ U) : IsCompact K ↔ IsCompact ((Subtype.val : U → X)⁻¹' K) := by
  apply Iff.symm
  apply Iff.trans (Subtype.isCompact_iff)
  have h' : Subtype.val '' ((Subtype.val : U → X)⁻¹' K) = K := by
    apply image_preimage_eq_of_subset ?_
    simp
    · exact hKU
  simp [h']

variable [T2Space X] [LocallyCompactSpace X]

/- This is an important property of locally compact Hausdorff spaces (Remark : I am not sure whether Hausdorff is needed here). Given a finite cover U_i of a compact K, we can always refine that cover by opens V_i, such that the closure of V_i is compact and contained in U_i. One of the things i wanted here designwise, is to end up with the same indexing set ι. This makes the second part of the proof cumbersome, but conceptually, find for x in K an open set V_x, such that the closure of V_x is compact and contained in some U_i. These cover K, so we get a finite subcover. The rest is aestetic.  -/
lemma rel_compact_cover {α : Type*} {ι : Finset α} (K : Set X) (hK : IsCompact K) (U : (i : ι) → Opens X) (hKU : K ⊆ ⋃ i, (U i : Set X)) : ∃ (V : (i : ι) → Opens X), (K ⊆ ⋃ i, (V i : Set X)) ∧ (∀ (i : ι), (closure (V i) ⊆ (U i : Set X)) ∧ (IsCompact (closure (V i : Set X)))) := by
  classical
  /-construction of a compact contained in U i for each x ∈ K-/
  have V (x : K) :  ∃ (i : ι) (W : Opens X), x.1 ∈ W ∧ closure W ⊆ (U i : Set X) ∧ IsCompact (closure W.1) := by
    let hxU := hKU x.2
    rw [mem_iUnion] at hxU
    obtain ⟨i, hxi⟩ := hxU
    let ⟨K, hK, hxintK, hKUi⟩ := exists_compact_subset (U i).2 (hxi)
    use i, ⟨interior K, isOpen_interior⟩
    constructor
    · exact hxintK
    constructor
    · exact Subset.trans (IsClosed.closure_interior_subset (IsCompact.isClosed hK)) hKUi
    apply IsCompact.of_isClosed_subset
    · exact hK
    · exact isClosed_closure
    apply IsClosed.closure_interior_subset
    exact IsCompact.isClosed hK
  choose i_of cover h_props using V
  /-trivially, these cover K-/
  have hKcover : K ⊆ ⋃ x, cover x := by
    intro x hxK
    apply mem_iUnion.2
    use ⟨x, hxK⟩
    exact (h_props ⟨x, hxK⟩).1
  let subcover := IsCompact.elim_finite_subcover hK (fun x ↦ cover x) (fun x ↦ (cover x).2) hKcover
  rcases subcover with ⟨τ, hKcover⟩
  /- this is the finicky part, where i take the union over all V in the subcover that are contained in some U i and for all i who may not appear, we take the emptyset-/
  use fun i =>
  if h : ∃ x ∈ τ, i_of x = i
      then
      ⟨
      ⋃ (x : {x : τ // i_of x = i}), (cover x.1.1 : Set X),
      by
        apply isOpen_iUnion
        intro x
        exact (cover x).2
      ⟩
      else
      ⟨∅, isOpen_empty⟩
  constructor
  /-proof that this covers-/
  · intro x hxK
    /- Its a bit confusing here. this is the indexing set, which is also a subset of X, so x_i is an element ofXbut it serves the role of an index-/
    have := mem_iUnion.1 (hKcover hxK)
    simp only [mem_iUnion] at this
    obtain ⟨x_i, ⟨hx_i_in_τ, hx_in_cover_xi⟩⟩ := this
    apply mem_iUnion.2
    let i := i_of x_i
    use i
    dsimp
    split_ifs
    · apply mem_iUnion.2
      use ⟨⟨x_i, hx_i_in_τ⟩, rfl⟩
    rename_i h_neg
    exfalso
    exact h_neg (by use x_i, hx_i_in_τ)
  intro i
  /-proof of the desired properties-/
  constructor
  · by_cases h : ∃ x ∈ τ, i_of x = i
    · simp only [h]; dsimp
      rw [closure_iUnion_of_finite, iUnion_subset_iff]
      intro x'
      simp only [<-x'.2]
      exact (h_props x').2.1
    simp [h]
  · by_cases h : ∃ x ∈ τ, i_of x = i
    · simp only [h]; dsimp
      rw[closure_iUnion_of_finite]
      apply isCompact_iUnion
      intro x'
      exact (h_props x').2.2
    simp [h]



end MyTopology
