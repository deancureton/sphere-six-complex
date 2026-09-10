module

public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section
open Set Topology
namespace SphereSixComplex

public theorem isEmbedding_restrict_compact_separated
    {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y]
    (f : X → Y) (s K : Set X) (hK : IsCompact K) (hsK : s ⊆ K)
    (hf : ContinuousOn f K) (hinj : Set.InjOn f s)
    (hboundary : Disjoint (f '' (K \ s)) (f '' s)) :
    Topology.IsEmbedding (s.domRestrict f) := by
  let t : Set Y := f '' s
  let g : s → t := Set.codRestrict (s.domRestrict f) t (fun x ↦ ⟨x, x.2, rfl⟩)
  have hfs : Continuous (s.domRestrict f) :=
    continuousOn_iff_continuous_domRestrict.mp (hf.mono hsK)
  have hgcont : Continuous g := hfs.codRestrict _
  have hginj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply hinj x.2 y.2
    exact congrArg Subtype.val hxy
  have hgclosed : IsClosedMap g := by
    intro A hA
    let L : Set X := closure (Subtype.val '' A)
    have hvalAK : Subtype.val '' A ⊆ K := by
      rintro x ⟨a, ha, rfl⟩
      exact hsK a.2
    have hLK : L ⊆ K := closure_minimal hvalAK hK.isClosed
    have hLcompact : IsCompact L := hK.of_isClosed_subset isClosed_closure hLK
    have hfLclosed : IsClosed (f '' L) :=
      (hLcompact.image_of_continuousOn (hf.mono hLK)).isClosed
    apply isClosed_induced_iff.mpr
    refine ⟨f '' L, hfLclosed, ?_⟩
    ext z
    constructor
    · rintro ⟨x, hxL, hfx⟩
      have hxs : x ∈ s := by
        by_contra hxs
        have hxBoundary : f x ∈ f '' (K \ s) := ⟨x, ⟨hLK hxL, hxs⟩, rfl⟩
        have hzInterior : f x ∈ f '' s := hfx ▸ z.2
        exact Set.disjoint_left.mp hboundary hxBoundary hzInterior
      have hxClosure : (⟨x, hxs⟩ : s) ∈ closure A := closure_subtype.mpr hxL
      rw [hA.closure_eq] at hxClosure
      refine ⟨⟨x, hxs⟩, hxClosure, ?_⟩
      exact Subtype.ext hfx
    · rintro ⟨x, hxA, rfl⟩
      exact ⟨x, subset_closure ⟨x, hxA, rfl⟩, rfl⟩
  have hg : Topology.IsEmbedding g :=
    (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
      hgcont hginj hgclosed).isEmbedding
  exact Topology.IsEmbedding.subtypeVal.comp hg

end SphereSixComplex
