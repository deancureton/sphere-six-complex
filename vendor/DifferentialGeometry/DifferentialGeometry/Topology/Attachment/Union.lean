module

public import DifferentialGeometry.Topology.Attachment.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

namespace DifferentialGeometry.Topology

universe u v w u'

open Filter Function Set

section UnionRealization

variable {Y : Type v} [TopologicalSpace Y] {A : Type*} {B : Type*} [TopologicalSpace B]

def adjunctionUnionMap (X₀ : Set Y) (c : B → Y) :
    B ⊕ X₀ → {y : Y // y ∈ X₀ ∪ Set.range c} :=
  Sum.elim (fun d => ⟨c d, Or.inr ⟨d, rfl⟩⟩) (fun x => ⟨x, Or.inl x.2⟩)

omit [TopologicalSpace Y] [TopologicalSpace B] in
theorem adjunctionUnionMap_rel {X₀ : Set Y} (i : A → B) (c : B → Y) {φ : A → X₀}
    (hφ : ∀ a, (φ a : Y) = c (i a)) :
    ∀ a b : B ⊕ X₀, adjunctionRel i φ a b →
      adjunctionUnionMap X₀ c a = adjunctionUnionMap X₀ c b := by
  intro a b h
  rcases h with ⟨x, hx | hx⟩
  · rcases hx with ⟨ha, hb⟩
    subst a
    subst b
    apply Subtype.ext
    exact (hφ x).symm
  · rcases hx with ⟨hb, ha⟩
    subst a
    subst b
    apply Subtype.ext
    exact hφ x

def adjunctionRealization (X₀ : Set Y) (i : A → B) (c : B → Y) (φ : A → X₀)
    (hφ : ∀ a, (φ a : Y) = c (i a)) :
    AdjunctionSpace i φ → {y : Y // y ∈ X₀ ∪ Set.range c} :=
  Quot.lift (adjunctionUnionMap X₀ c) (adjunctionUnionMap_rel i c hφ)

theorem continuous_adjunctionUnionMap {X₀ : Set Y} (c : B → Y) (hc : Continuous c) :
    Continuous (adjunctionUnionMap X₀ c) := by
  dsimp [adjunctionUnionMap]
  exact Continuous.sumElim (hc.codRestrict (fun d => Or.inr ⟨d, rfl⟩))
    (continuous_subtype_val.codRestrict (fun x : X₀ => Or.inl x.2))

theorem continuous_adjunctionRealization {X₀ : Set Y} (i : A → B) (c : B → Y)
    (φ : A → X₀)
    (hφ : ∀ a, (φ a : Y) = c (i a)) (hc : Continuous c) :
    Continuous (adjunctionRealization X₀ i c φ hφ) := by
  dsimp [adjunctionRealization]
  exact continuous_quot_lift (adjunctionUnionMap_rel i c hφ)
    (continuous_adjunctionUnionMap c hc)

omit [TopologicalSpace Y] [TopologicalSpace B] in
theorem adjunctionRealization_surjective {X₀ : Set Y} (i : A → B) (c : B → Y)
    (φ : A → X₀)
    (hφ : ∀ a, (φ a : Y) = c (i a)) :
    Function.Surjective (adjunctionRealization X₀ i c φ hφ) := by
  intro ⟨y, hy⟩
  rcases hy with hy₀ | ⟨d, hd⟩
  · refine ⟨Quot.mk (adjunctionRel i φ) (Sum.inr ⟨y, hy₀⟩), ?_⟩
    apply Subtype.ext
    rfl
  · refine ⟨Quot.mk (adjunctionRel i φ) (Sum.inl d), ?_⟩
    apply Subtype.ext
    exact hd

omit [TopologicalSpace Y] [TopologicalSpace B] in
theorem portPrivate_c7517bea_adjunctionRealization_inl_inr {X₀ : Set Y} (i : A → B) (c : B → Y) (φ : A → X₀)
    (hφ : ∀ a, (φ a : Y) = c (i a))
    (hboundary : ∀ d : B, c d ∈ X₀ → d ∈ Set.range i) {d : B}
    {x : X₀} (h : adjunctionUnionMap X₀ c (Sum.inl d) = adjunctionUnionMap X₀ c (Sum.inr x)) :
    Quot.mk (adjunctionRel i φ) (Sum.inl d) = Quot.mk (adjunctionRel i φ) (Sum.inr x) := by
  have hcd : c d = (x : Y) := congrArg Subtype.val h
  have hx₀ : c d ∈ X₀ := by
    rw [hcd]
    exact x.2
  rcases hboundary d hx₀ with ⟨a, ha⟩
  calc
    Quot.mk (adjunctionRel i φ) (Sum.inl d) = Quot.mk (adjunctionRel i φ) (Sum.inl (i a)) := by
      rw [← ha]
    _ = Quot.mk (adjunctionRel i φ) (Sum.inr (φ a)) := by
      exact Quot.sound ⟨a, Or.inl ⟨rfl, rfl⟩⟩
    _ = Quot.mk (adjunctionRel i φ) (Sum.inr x) := by
      apply congrArg (fun t : X₀ => Quot.mk (adjunctionRel i φ) (Sum.inr t))
      apply Subtype.ext
      calc
        (φ a : Y) = c (i a) := hφ a
        _ = c d := by rw [ha]
        _ = (x : Y) := hcd

omit [TopologicalSpace Y] [TopologicalSpace B] in
theorem adjunctionRealization_injective {X₀ : Set Y} (i : A → B) (c : B → Y)
    (φ : A → X₀)
    (hφ : ∀ a, (φ a : Y) = c (i a)) (hc : Function.Injective c)
    (hboundary : ∀ d : B, c d ∈ X₀ → d ∈ Set.range i) :
    Function.Injective (adjunctionRealization X₀ i c φ hφ) := by
  intro z z' hzz'
  rcases Quot.exists_rep z with ⟨a, rfl⟩
  rcases Quot.exists_rep z' with ⟨b, rfl⟩
  change adjunctionUnionMap X₀ c a = adjunctionUnionMap X₀ c b at hzz'
  cases a with
  | inl d =>
      cases b with
      | inl d' =>
          exact congrArg (fun d : B => Quot.mk (adjunctionRel i φ) (Sum.inl d))
            (hc (congrArg Subtype.val hzz'))
      | inr x =>
          exact portPrivate_c7517bea_adjunctionRealization_inl_inr i c φ hφ hboundary hzz'
  | inr x =>
      cases b with
      | inl d =>
          exact (portPrivate_c7517bea_adjunctionRealization_inl_inr i c φ hφ hboundary hzz'.symm).symm
      | inr x' =>
          apply congrArg (fun t : X₀ => Quot.mk (adjunctionRel i φ) (Sum.inr t))
          ext
          simpa [adjunctionUnionMap] using congrArg Subtype.val hzz'

def portPrivate_c7517bea_unionInclusionLeft (A B : Set Y) : {y : Y // y ∈ A} → {y : Y // y ∈ A ∪ B} :=
  fun y => ⟨y, Or.inl y.2⟩

def portPrivate_c7517bea_unionInclusionRight (A B : Set Y) : {y : Y // y ∈ B} → {y : Y // y ∈ A ∪ B} :=
  fun y => ⟨y, Or.inr y.2⟩

theorem portPrivate_c7517bea_isClosed_image_of_isClosed_preimage_unionInclusionLeft {A B : Set Y}
    (hA : IsClosed A) {W : Set {y : Y // y ∈ A ∪ B}}
    (hW : IsClosed (portPrivate_c7517bea_unionInclusionLeft A B ⁻¹' W)) :
    IsClosed (portPrivate_c7517bea_unionInclusionLeft A B '' (portPrivate_c7517bea_unionInclusionLeft A B ⁻¹' W)) := by
  rw [isClosed_induced_iff] at hW
  rcases hW with ⟨u, hu, huW⟩
  have hset : portPrivate_c7517bea_unionInclusionLeft A B '' (portPrivate_c7517bea_unionInclusionLeft A B ⁻¹' W) =
      Subtype.val ⁻¹' (u ∩ A) := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      have hxy' : (x : Y) = (y : Y) := by
        simpa [portPrivate_c7517bea_unionInclusionLeft] using congrArg Subtype.val hxy
      have hyA : (y : Y) ∈ A := by
        rw [← hxy']
        exact x.2
      have hxu : (x : Y) ∈ u := by
        have hx' : x ∈ Subtype.val ⁻¹' u := by
          simpa [huW] using hx
        exact hx'
      exact ⟨by simpa [hxy'] using hxu, hyA⟩
    · intro hy
      rcases hy with ⟨hyu, hyA⟩
      refine ⟨⟨y, hyA⟩, ?_, ?_⟩
      · have hx' : (⟨y, hyA⟩ : {y : Y // y ∈ A}) ∈ Subtype.val ⁻¹' u := hyu
        simpa [huW] using hx'
      · apply Subtype.ext
        rfl
  rw [hset]
  exact (hu.inter hA).preimage continuous_subtype_val

theorem portPrivate_c7517bea_isClosed_image_of_isClosed_preimage_unionInclusionRight {A B : Set Y}
    (hB : IsClosed B) {W : Set {y : Y // y ∈ A ∪ B}}
    (hW : IsClosed (portPrivate_c7517bea_unionInclusionRight A B ⁻¹' W)) :
    IsClosed (portPrivate_c7517bea_unionInclusionRight A B '' (portPrivate_c7517bea_unionInclusionRight A B ⁻¹' W)) := by
  rw [isClosed_induced_iff] at hW
  rcases hW with ⟨u, hu, huW⟩
  have hset : portPrivate_c7517bea_unionInclusionRight A B '' (portPrivate_c7517bea_unionInclusionRight A B ⁻¹' W) =
      Subtype.val ⁻¹' (u ∩ B) := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      have hxy' : (x : Y) = (y : Y) := by
        simpa [portPrivate_c7517bea_unionInclusionRight] using congrArg Subtype.val hxy
      have hyB : (y : Y) ∈ B := by
        rw [← hxy']
        exact x.2
      have hxu : (x : Y) ∈ u := by
        have hx' : x ∈ Subtype.val ⁻¹' u := by
          simpa [huW] using hx
        exact hx'
      exact ⟨by simpa [hxy'] using hxu, hyB⟩
    · intro hy
      rcases hy with ⟨hyu, hyB⟩
      refine ⟨⟨y, hyB⟩, ?_, ?_⟩
      · have hx' : (⟨y, hyB⟩ : {y : Y // y ∈ B}) ∈ Subtype.val ⁻¹' u := hyu
        simpa [huW] using hx'
      · apply Subtype.ext
        rfl
  rw [hset]
  exact (hu.inter hB).preimage continuous_subtype_val

theorem portPrivate_c7517bea_isClosed_union_of_isClosed_preimage {A B : Set Y} (hA : IsClosed A)
    (hB : IsClosed B) {W : Set {y : Y // y ∈ A ∪ B}}
    (hWA : IsClosed (portPrivate_c7517bea_unionInclusionLeft A B ⁻¹' W))
    (hWB : IsClosed (portPrivate_c7517bea_unionInclusionRight A B ⁻¹' W)) : IsClosed W := by
  have hset : W = portPrivate_c7517bea_unionInclusionLeft A B '' (portPrivate_c7517bea_unionInclusionLeft A B ⁻¹' W) ∪
        portPrivate_c7517bea_unionInclusionRight A B '' (portPrivate_c7517bea_unionInclusionRight A B ⁻¹' W) := by
    ext y
    constructor
    · intro hy
      rcases y.2 with hyA | hyB
      · exact Or.inl ⟨⟨y, hyA⟩, ⟨by simpa [portPrivate_c7517bea_unionInclusionLeft] using hy, by ext; rfl⟩⟩
      · exact Or.inr ⟨⟨y, hyB⟩, ⟨by simpa [portPrivate_c7517bea_unionInclusionRight] using hy, by ext; rfl⟩⟩
    · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
      · rw [← hx.2]
        exact hx.1
      · rw [← hx.2]
        exact hx.1
  rw [hset]
  exact (portPrivate_c7517bea_isClosed_image_of_isClosed_preimage_unionInclusionLeft hA hWA).union
    (portPrivate_c7517bea_isClosed_image_of_isClosed_preimage_unionInclusionRight hB hWB)

omit [TopologicalSpace Y] [TopologicalSpace B] in
theorem portPrivate_c7517bea_adjunctionRealization_leftPreimage_eq {X₀ : Set Y} (i : A → B) (c : B → Y)
    (φ : A → X₀) (hφ : ∀ a, (φ a : Y) = c (i a)) (hc : Function.Injective c)
    (hboundary : ∀ d : B, c d ∈ X₀ → d ∈ Set.range i)
    {C : Set (AdjunctionSpace i φ)} :
    portPrivate_c7517bea_unionInclusionLeft X₀ (Set.range c) ⁻¹' (adjunctionRealization X₀ i c φ hφ '' C) =
      Sum.inr ⁻¹' (adjunctionMk i φ ⁻¹' C) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨z, hzC, hz⟩
    have hinj := adjunctionRealization_injective i c φ hφ hc hboundary
    have hz' : z = Quot.mk (adjunctionRel i φ) (Sum.inr x) :=
      hinj (by
        calc
          adjunctionRealization X₀ i c φ hφ z = ⟨x, Or.inl x.2⟩ := hz
          _ = adjunctionRealization X₀ i c φ hφ (Quot.mk (adjunctionRel i φ) (Sum.inr x)) := by
            simp [adjunctionRealization, adjunctionUnionMap])
    rw [hz'] at hzC
    exact hzC
  · intro hx
    refine ⟨Quot.mk (adjunctionRel i φ) (Sum.inr x), hx, ?_⟩
    rfl

omit [TopologicalSpace Y] [TopologicalSpace B] in
theorem portPrivate_c7517bea_adjunctionRealization_rightPreimage_eq {X₀ : Set Y} (i : A → B) (c : B → Y)
    (φ : A → X₀) (hφ : ∀ a, (φ a : Y) = c (i a)) (hc : Function.Injective c)
    (hboundary : ∀ d : B, c d ∈ X₀ → d ∈ Set.range i)
    {C : Set (AdjunctionSpace i φ)} :
    portPrivate_c7517bea_unionInclusionRight X₀ (Set.range c) ⁻¹' (adjunctionRealization X₀ i c φ hφ '' C) =
      (fun d : B => ⟨c d, ⟨d, rfl⟩⟩) '' (Sum.inl ⁻¹' (adjunctionMk i φ ⁻¹' C)) := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨z, hzC, hz⟩
    have hd₀ : ∃ d : B, c d = (y : Y) := y.2
    let d₀ : B := Classical.choose hd₀
    have hd₀spec : c d₀ = (y : Y) := Classical.choose_spec hd₀
    have hinj := adjunctionRealization_injective i c φ hφ hc hboundary
    have hz' : z = Quot.mk (adjunctionRel i φ) (Sum.inl d₀) :=
      hinj (by
        calc
          adjunctionRealization X₀ i c φ hφ z = ⟨y, Or.inr y.2⟩ := hz
          _ = adjunctionRealization X₀ i c φ hφ (Quot.mk (adjunctionRel i φ) (Sum.inl d₀)) := by
            simp [adjunctionRealization, adjunctionUnionMap, hd₀spec])
    have hd₀C : Quot.mk (adjunctionRel i φ) (Sum.inl d₀) ∈ C := by
      rw [← hz']
      exact hzC
    refine ⟨d₀, hd₀C, ?_⟩
    apply Subtype.ext
    exact hd₀spec
  · intro hy
    rcases hy with ⟨d, hdC, hdy⟩
    refine ⟨Quot.mk (adjunctionRel i φ) (Sum.inl d), hdC, ?_⟩
    change adjunctionUnionMap X₀ c (Sum.inl d) = ⟨y, Or.inr y.2⟩
    have hdy' : c d = (y : Y) := congrArg Subtype.val hdy
    dsimp [adjunctionUnionMap]
    apply Subtype.ext
    exact hdy'

theorem adjunctionRealization_isClosedMap {X₀ : Set Y} (i : A → B) (φ : A → X₀) (c : B → Y)
    (hφ : ∀ a, (φ a : Y) = c (i a)) (hc : Function.Injective c)
    (hcont : Continuous c) (hboundary : ∀ d : B, c d ∈ X₀ → d ∈ Set.range i)
    (hclosed : IsClosed X₀) [CompactSpace B] [T2Space Y] :
    IsClosedMap (adjunctionRealization X₀ i c φ hφ) := by
  intro C hC
  let Q : Set (B ⊕ X₀) := adjunctionMk i φ ⁻¹' C
  have hQ : IsClosed Q := hC.preimage (continuous_adjunctionMk i φ)
  have hPc : IsClosed (Sum.inl ⁻¹' Q) := hQ.preimage continuous_inl
  have hPx : IsClosed (Sum.inr ⁻¹' Q) := hQ.preimage continuous_inr
  have hclosedRange : IsClosed (Set.range c) := by
    rw [← image_univ]
    exact (isCompact_univ.image hcont).isClosed
  refine portPrivate_c7517bea_isClosed_union_of_isClosed_preimage hclosed hclosedRange ?_ ?_
  · rw [portPrivate_c7517bea_adjunctionRealization_leftPreimage_eq i c φ hφ hc hboundary]
    exact hPx
  · rw [portPrivate_c7517bea_adjunctionRealization_rightPreimage_eq i c φ hφ hc hboundary]
    let c' : B → Set.range c := fun d => ⟨c d, ⟨d, rfl⟩⟩
    have hc'inj : Function.Injective c' := by
      intro d d' h
      apply hc
      exact congrArg Subtype.val h
    have hc'surj : Function.Surjective c' := by
      intro y
      rcases y.2 with ⟨d, hd⟩
      refine ⟨d, ?_⟩
      apply Subtype.ext
      exact hd
    have hc'cont : Continuous c' := hcont.codRestrict (fun d => show c d ∈ Set.range c from ⟨d, rfl⟩)
    let hc'homeo : B ≃ₜ Set.range c :=
      Continuous.homeoOfEquivCompactToT2
        (f := Equiv.ofBijective c' ⟨hc'inj, hc'surj⟩) hc'cont
    have hc'closedMap : IsClosedMap c' := by
      change IsClosedMap (fun d : B => (hc'homeo d : Set.range c))
      exact hc'homeo.isClosedMap
    exact hc'closedMap (Sum.inl ⁻¹' Q) hPc

noncomputable def adjunctionHomeomorphUnionImage {X₀ : Set Y} (i : A → B) (φ : A → X₀) (c : B → Y)
    (hφ : ∀ a, (φ a : Y) = c (i a)) (hc : Function.Injective c) (hcont : Continuous c)
    (hboundary : ∀ d : B, c d ∈ X₀ → d ∈ Set.range i)
    (hclosed : IsClosed X₀) [CompactSpace B] [T2Space Y] :
    AdjunctionSpace i φ ≃ₜ {y : Y // y ∈ X₀ ∪ Set.range c} := by
  let f : AdjunctionSpace i φ → {y : Y // y ∈ X₀ ∪ Set.range c} :=
    adjunctionRealization X₀ i c φ hφ
  have hfcont : Continuous f := continuous_adjunctionRealization i c φ hφ hcont
  have hfclosed : IsClosedMap f := adjunctionRealization_isClosedMap i φ c hφ hc hcont hboundary hclosed
  have hfinj : Function.Injective f := adjunctionRealization_injective i c φ hφ hc hboundary
  have hfsurj : Function.Surjective f := adjunctionRealization_surjective i c φ hφ
  exact IsHomeomorph.homeomorph (f := f)
    (isHomeomorph_iff_continuous_isClosedMap_bijective.mpr ⟨hfcont, hfclosed, ⟨hfinj, hfsurj⟩⟩)

theorem adjunctionHomeomorphUnionImage_lower {X₀ : Set Y} (i : A → B) (φ : A → X₀) (c : B → Y)
    (hφ : ∀ a, (φ a : Y) = c (i a)) (hc : Function.Injective c) (hcont : Continuous c)
    (hboundary : ∀ d : B, c d ∈ X₀ → d ∈ Set.range i)
    (hclosed : IsClosed X₀) [CompactSpace B] [T2Space Y] (x : X₀) :
    (adjunctionHomeomorphUnionImage i φ c hφ hc hcont hboundary hclosed)
      (adjunctionLower φ x) = ⟨x, Or.inl x.2⟩ := by
  change adjunctionRealization X₀ i c φ hφ (adjunctionLower φ x) = ⟨x, Or.inl x.2⟩
  dsimp [adjunctionRealization, adjunctionUnionMap, adjunctionLower, adjunctionMk]

omit [TopologicalSpace Y] [TopologicalSpace B] in
theorem adjunctionRealization_lower {X₀ : Set Y} (i : A → B) (c : B → Y) {φ : A → X₀}
    (hφ : ∀ a, (φ a : Y) = c (i a)) (x : X₀) :
    adjunctionRealization X₀ i c φ hφ (adjunctionLower φ x) = ⟨x, Or.inl x.2⟩ := by
  dsimp [adjunctionRealization, adjunctionUnionMap, adjunctionLower, adjunctionMk]

noncomputable def cellAdjunctionHomeomorphUnionImage {n : ℕ} {X₀ : Set Y}
    (φ : CellBoundary n → X₀) (c : ClosedCell n → Y)
    (hφ : ∀ b, (φ b : Y) = c (cellBoundaryInclusion n b)) (hc : Function.Injective c)
    (hcont : Continuous c)
    (hinterior : Disjoint (c '' Set.range (cellInteriorInclusion n)) X₀)
    (hclosed : IsClosed X₀) [T2Space Y] :
    CellAdjunctionSpace n φ ≃ₜ {y : Y // y ∈ X₀ ∪ Set.range c} := by
  refine adjunctionHomeomorphUnionImage (i := cellBoundaryInclusion n) φ c hφ hc hcont ?_ hclosed
  intro d hd
  have hnot : ¬ ‖(d : EuclideanSpace ℝ (Fin n))‖ < 1 := by
    intro hlt
    exact (Set.disjoint_left.mp hinterior)
      ⟨cellInteriorInclusion n (⟨d, hlt⟩ : CellInterior n),
        ⟨⟨(⟨d, hlt⟩ : CellInterior n), rfl⟩, congrArg c (by ext; rfl)⟩⟩ hd
  have hEq : ‖(d : EuclideanSpace ℝ (Fin n))‖ = 1 := le_antisymm d.2 (le_of_not_gt hnot)
  exact ⟨⟨d, hEq⟩, by ext; rfl⟩

noncomputable def adjunctionHomeoOfLowerEquiv {A : Type v} {B : Type w} [TopologicalSpace B]
    {X : Type u} [TopologicalSpace X] {X' : Type u'} [TopologicalSpace X']
    (i : A → B) (φ : A → X) (h : X ≃ₜ X') :
    AdjunctionSpace i (h ∘ φ) ≃ₜ AdjunctionSpace i φ := by
  let F : AdjunctionSpace i (h ∘ φ) → AdjunctionSpace i φ :=
    Quot.lift (fun z : B ⊕ X' => Quot.mk (adjunctionRel i φ) (Sum.map id h.symm z)) (by
      intro a b hab
      rcases hab with ⟨x, hx | hx⟩
      · rcases hx with ⟨ha, hb⟩
        subst a
        subst b
        exact Quot.sound ⟨x, Or.inl ⟨rfl, by simp⟩⟩
      · rcases hx with ⟨hb, ha⟩
        subst a
        subst b
        exact Quot.sound ⟨x, Or.inr ⟨rfl, by simp⟩⟩)
  let G : AdjunctionSpace i φ → AdjunctionSpace i (h ∘ φ) :=
    Quot.lift (fun z : B ⊕ X => Quot.mk (adjunctionRel i (h ∘ φ)) (Sum.map id h z)) (by
      intro a b hab
      rcases hab with ⟨x, hx | hx⟩
      · rcases hx with ⟨ha, hb⟩
        subst a
        subst b
        exact Quot.sound ⟨x, Or.inl ⟨rfl, by simp⟩⟩
      · rcases hx with ⟨hb, ha⟩
        subst a
        subst b
        exact Quot.sound ⟨x, Or.inr ⟨rfl, by simp⟩⟩)
  exact
    { toFun := F
      invFun := G
      left_inv := by
        refine Quot.ind ?_
        intro z
        simp [F, G]
      right_inv := by
        refine Quot.ind ?_
        intro z
        simp [F, G]
      continuous_toFun := by
        dsimp [F]
        exact continuous_quot_lift (by
          intro a b hab
          rcases hab with ⟨x, hx | hx⟩
          · rcases hx with ⟨ha, hb⟩
            subst a
            subst b
            exact Quot.sound ⟨x, Or.inl ⟨rfl, by simp⟩⟩
          · rcases hx with ⟨hb, ha⟩
            subst a
            subst b
            exact Quot.sound ⟨x, Or.inr ⟨rfl, by simp⟩⟩)
          ((continuous_adjunctionMk i φ).comp (Continuous.sumMap continuous_id h.symm.continuous))
      continuous_invFun := by
        dsimp [G]
        exact continuous_quot_lift (by
          intro a b hab
          rcases hab with ⟨x, hx | hx⟩
          · rcases hx with ⟨ha, hb⟩
            subst a
            subst b
            exact Quot.sound ⟨x, Or.inl ⟨rfl, by simp⟩⟩
          · rcases hx with ⟨hb, ha⟩
            subst a
            subst b
            exact Quot.sound ⟨x, Or.inr ⟨rfl, by simp⟩⟩)
          ((continuous_adjunctionMk i (h ∘ φ)).comp (Continuous.sumMap continuous_id h.continuous)) }

end UnionRealization

end DifferentialGeometry.Topology
