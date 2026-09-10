module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Separation.Regular

/-!
# Gluing compact spaces along closed embeddings

This file develops the point-set topology needed to glue two compact Hausdorff spaces along two
copies of a common compact space.  The carrier is an ordinary quotient of the disjoint union.  Its
setoid relates points on the same side only when they are equal, and relates points on opposite
sides only when they come from the same point of the gluing space.

Mathlib gives compactness of an arbitrary quotient of a compact space, but Hausdorffness and
second countability require more work because this quotient map is generally not open.  We prove
the reusable closed-equivalence-relation criteria directly.  Applied to the sum-gluing relation,
they show that the two canonical maps are closed embeddings, while their restrictions away from
the gluing locus are open embeddings.

No manifold or smooth structure is used here.
-/

@[expose] public section

noncomputable section

open Function Set Topology TopologicalSpace

namespace SphereSixComplex
namespace ClosedEmbeddingGluing

universe u v w

section ClosedSetoid

variable {X : Type u} [TopologicalSpace X]

/-- The image of a closed set in a compact Hausdorff space under a quotient by a closed
equivalence relation is closed. -/
public theorem quotient_image_isClosed_of_rel_isClosed
    [CompactSpace X] [T2Space X] (s : Setoid X)
    (hrel : IsClosed {p : X × X | s p.1 p.2})
    {A : Set X} (hA : IsClosed A) :
    IsClosed ((Quotient.mk' : X → Quotient s) '' A) := by
  let q : X → Quotient s := Quotient.mk'
  let R : Set (X × X) := {p | s p.1 p.2}
  have hsat : q ⁻¹' (q '' A) = Prod.fst '' (R ∩ Prod.snd ⁻¹' A) := by
    ext x
    constructor
    · rintro ⟨a, ha, hqa⟩
      refine ⟨(x, a), ⟨?_, ha⟩, rfl⟩
      change s x a
      exact Quotient.eq.mp hqa.symm
    · rintro ⟨⟨x', a⟩, ⟨hxa, ha⟩, hxx'⟩
      change x' = x at hxx'
      subst x'
      exact ⟨a, ha, Quotient.eq.mpr (s.symm hxa)⟩
  apply isQuotientMap_quotient_mk'.isCoinducing.isClosed_preimage.mp
  rw [hsat]
  exact ((hrel.inter (hA.preimage continuous_snd)).isCompact.image continuous_fst).isClosed

/-- A quotient of a compact Hausdorff space by a closed equivalence relation is Hausdorff. -/
public theorem quotient_t2Space_of_rel_isClosed
    [CompactSpace X] [T2Space X] (s : Setoid X)
    (hrel : IsClosed {p : X × X | s p.1 p.2}) :
    T2Space (Quotient s) := by
  let q : X → Quotient s := Quotient.mk'
  have hclosed : ∀ {A : Set X}, IsClosed A → IsClosed (q '' A) := by
    intro A hA
    exact quotient_image_isClosed_of_rel_isClosed s hrel hA
  have hfiber : ∀ y : Quotient s, IsClosed (q ⁻¹' {y}) := by
    intro y
    induction y using Quotient.inductionOn' with
    | _ a =>
      have heq : q ⁻¹' {q a} =
          (fun x : X => (x, a)) ⁻¹' {p : X × X | s p.1 p.2} := by
        ext x
        change (q x = q a) ↔ s x a
        exact Quotient.eq
      change IsClosed (q ⁻¹' {q a})
      rw [heq]
      exact hrel.preimage (continuous_id.prodMk continuous_const)
  refine ⟨?_⟩
  intro y z hyz
  have hdisj : Disjoint (q ⁻¹' {y}) (q ⁻¹' {z}) := by
    rw [Set.disjoint_left]
    intro x hxy hxz
    exact hyz (hxy.symm.trans hxz)
  obtain ⟨U, V, hUo, hVo, hyU, hzV, hUV⟩ :=
    normal_separation (hfiber y) (hfiber z) hdisj
  let Uq : Set (Quotient s) := (q '' Uᶜ)ᶜ
  let Vq : Set (Quotient s) := (q '' Vᶜ)ᶜ
  refine ⟨Uq, Vq, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hclosed hUo.isClosed_compl).isOpen_compl
  · exact (hclosed hVo.isClosed_compl).isOpen_compl
  · intro hyc
    rcases hyc with ⟨x, hx, hqx⟩
    have hxf : x ∈ q ⁻¹' {y} := hqx
    exact hx (hyU hxf)
  · intro hzc
    rcases hzc with ⟨x, hx, hqx⟩
    have hxf : x ∈ q ⁻¹' {z} := hqx
    exact hx (hzV hxf)
  · rw [Set.disjoint_left]
    intro a haU haV
    rcases Quotient.mk_surjective a with ⟨x, rfl⟩
    have hxU : x ∈ U := by
      by_contra hx
      exact haU ⟨x, hx, rfl⟩
    have hxV : x ∈ V := by
      by_contra hx
      exact haV ⟨x, hx, rfl⟩
    exact Set.disjoint_left.mp hUV hxU hxV

/-- A quotient of a compact Hausdorff second-countable space by a closed equivalence relation is
second countable. -/
public theorem quotient_secondCountableTopology_of_rel_isClosed
    [CompactSpace X] [T2Space X] [SecondCountableTopology X] (s : Setoid X)
    (hrel : IsClosed {p : X × X | s p.1 p.2}) :
    SecondCountableTopology (Quotient s) := by
  let q : X → Quotient s := Quotient.mk'
  let cover (F : Finset (countableBasis X)) : Set X := ⋃ b ∈ F, (b : Set X)
  let down (F : Finset (countableBasis X)) : Set (Quotient s) := (q '' (cover F)ᶜ)ᶜ
  have hclosed : ∀ {A : Set X}, IsClosed A → IsClosed (q '' A) := by
    intro A hA
    exact quotient_image_isClosed_of_rel_isClosed s hrel hA
  have hfiber : ∀ y : Quotient s, IsClosed (q ⁻¹' {y}) := by
    intro y
    induction y using Quotient.inductionOn' with
    | _ a =>
      have heq : q ⁻¹' {q a} =
          (fun x : X => (x, a)) ⁻¹' {p : X × X | s p.1 p.2} := by
        ext x
        change (q x = q a) ↔ s x a
        exact Quotient.eq
      change IsClosed (q ⁻¹' {q a})
      rw [heq]
      exact hrel.preimage (continuous_id.prodMk continuous_const)
  have hcover_open : ∀ F, IsOpen (cover F) := by
    intro F
    exact isOpen_biUnion fun b _ => (isBasis_countableBasis X).isOpen b.2
  have hdown_open : ∀ F, IsOpen (down F) := by
    intro F
    exact (hclosed (hcover_open F).isClosed_compl).isOpen_compl
  let B : Set (Set (Quotient s)) := Set.range down
  have hB : IsTopologicalBasis B := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro _ ⟨F, rfl⟩
      exact hdown_open F
    · intro y O hyO hO
      have hpreO : IsOpen (q ⁻¹' O) := hO.preimage continuous_quotient_mk'
      let fib : Set X := q ⁻¹' {y}
      have hfib_compact : IsCompact fib := (hfiber y).isCompact
      have hex : ∀ x : fib, ∃ b : countableBasis X,
          x.1 ∈ (b : Set X) ∧ (b : Set X) ⊆ q ⁻¹' O := by
        intro x
        have hxO : x.1 ∈ q ⁻¹' O := by
          have hxy : q x.1 = y := x.2
          change q x.1 ∈ O
          rw [hxy]
          exact hyO
        obtain ⟨V, hVB, hxV, hVO⟩ :=
          (isBasis_countableBasis X).exists_subset_of_mem_open hxO hpreO
        exact ⟨⟨V, hVB⟩, hxV, hVO⟩
      choose b hbmem hbsub using hex
      obtain ⟨t, ht⟩ := hfib_compact.elim_finite_subcover
        (fun x : fib => (b x : Set X))
        (fun x => (isBasis_countableBasis X).isOpen (b x).2) (by
          intro x hx
          exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, hbmem ⟨x, hx⟩⟩)
      let F : Finset (countableBasis X) := t.image b
      refine ⟨down F, ⟨F, rfl⟩, ?_, ?_⟩
      · intro hybad
        rcases hybad with ⟨x, hxFc, hqx⟩
        have hxfib : x ∈ fib := hqx
        have hxcover : x ∈ cover F := by
          rcases Set.mem_iUnion.1 (ht hxfib) with ⟨z, hz⟩
          rcases Set.mem_iUnion.1 hz with ⟨hzt, hxbz⟩
          exact Set.mem_iUnion.2
            ⟨b z, Set.mem_iUnion.2 ⟨Finset.mem_image.2 ⟨z, hzt, rfl⟩, hxbz⟩⟩
        exact hxFc hxcover
      · intro a ha
        rcases Quotient.mk_surjective a with ⟨x, rfl⟩
        have hxcover : x ∈ cover F := by
          by_contra hx
          exact ha ⟨x, hx, rfl⟩
        rcases Set.mem_iUnion.1 hxcover with ⟨bz, hbz⟩
        rcases Set.mem_iUnion.1 hbz with ⟨hbzF, hxbz⟩
        rcases Finset.mem_image.1 hbzF with ⟨z, _, hz⟩
        rw [← hz] at hxbz
        exact hbsub z hxbz
  exact hB.secondCountableTopology (Set.countable_range down)

end ClosedSetoid

section SumGlueAlgebra

variable {X : Type u} {Y : Type v} {Z : Type w} (f : Z → X) (g : Z → Y)

/-- The direct relation on a sum that identifies exactly `f z` with `g z`. -/
public def sumGlueRel : X ⊕ Y → X ⊕ Y → Prop
  | .inl x, .inl x' => x = x'
  | .inr y, .inr y' => y = y'
  | .inl x, .inr y => ∃ z, f z = x ∧ g z = y
  | .inr y, .inl x => ∃ z, f z = x ∧ g z = y

public theorem sumGlueRel_refl (x : X ⊕ Y) : sumGlueRel f g x x := by
  cases x <;> rfl

public theorem sumGlueRel_symm {x y : X ⊕ Y} :
    sumGlueRel f g x y → sumGlueRel f g y x := by
  cases x <;> cases y <;> simp only [sumGlueRel, eq_comm] <;> exact id

public theorem sumGlueRel_trans (hf : Injective f) (hg : Injective g)
    {a b c : X ⊕ Y} : sumGlueRel f g a b → sumGlueRel f g b c → sumGlueRel f g a c := by
  rcases a with x | y <;> rcases b with x' | y' <;> rcases c with x'' | y'' <;>
    simp only [sumGlueRel]
  · exact Eq.trans
  · rintro rfl h
    exact h
  · rintro ⟨z, hzx, hzy⟩ ⟨z', hzx', hzy'⟩
    have : z = z' := hg (hzy.trans hzy'.symm)
    subst z'
    exact hzx.symm.trans hzx'
  · rintro ⟨z, hzx, hzy⟩ rfl
    exact ⟨z, hzx, hzy⟩
  · rintro ⟨z, hzx, hzy⟩ rfl
    exact ⟨z, hzx, hzy⟩
  · rintro ⟨z, hzx, hzy⟩ ⟨z', hzx', hzy'⟩
    have : z = z' := hf (hzx.trans hzx'.symm)
    subst z'
    exact hzy.symm.trans hzy'
  · rintro rfl h
    exact h
  · exact Eq.trans

/-- The setoid that glues `f z` to `g z` and makes no other identifications. -/
public def sumGlueSetoid (hf : Injective f) (hg : Injective g) : Setoid (X ⊕ Y) where
  r := sumGlueRel f g
  iseqv := ⟨sumGlueRel_refl f g, sumGlueRel_symm f g, sumGlueRel_trans f g hf hg⟩

/-- The quotient carrier obtained by gluing two spaces along injective maps from a common source. -/
public abbrev SumGlue (hf : Injective f) (hg : Injective g) :=
  Quotient (sumGlueSetoid f g hf hg)

/-- Canonical map from the left summand to the glued carrier. -/
public def toSumGlueLeft (hf : Injective f) (hg : Injective g) (x : X) : SumGlue f g hf hg :=
  Quotient.mk'' (.inl x)

/-- Canonical map from the right summand to the glued carrier. -/
public def toSumGlueRight (hf : Injective f) (hg : Injective g) (y : Y) : SumGlue f g hf hg :=
  Quotient.mk'' (.inr y)

public theorem toSumGlueLeft_injective (hf : Injective f) (hg : Injective g) :
    Injective (toSumGlueLeft f g hf hg) := by
  intro x x' h
  exact Quotient.eq.mp h

public theorem toSumGlueRight_injective (hf : Injective f) (hg : Injective g) :
    Injective (toSumGlueRight f g hf hg) := by
  intro y y' h
  exact Quotient.eq.mp h

public theorem toSumGlue_eq_iff (hf : Injective f) (hg : Injective g) (x : X) (y : Y) :
    toSumGlueLeft f g hf hg x = toSumGlueRight f g hf hg y ↔
      ∃ z, f z = x ∧ g z = y := by
  change (Quotient.mk'' (.inl x) : SumGlue f g hf hg) = Quotient.mk'' (.inr y) ↔ _
  rw [Quotient.eq]
  rfl

public theorem toSumGlue_commute (hf : Injective f) (hg : Injective g) (z : Z) :
    toSumGlueLeft f g hf hg (f z) = toSumGlueRight f g hf hg (g z) :=
  (toSumGlue_eq_iff f g hf hg _ _).2 ⟨z, rfl, rfl⟩

/-- Part of the left summand away from the gluing locus. -/
public abbrev LeftAway := {x : X // x ∉ Set.range f}

/-- Part of the right summand away from the gluing locus. -/
public abbrev RightAway := {y : Y // y ∉ Set.range g}

public def toSumGlueLeftAway (hf : Injective f) (hg : Injective g) (x : LeftAway f) :
    SumGlue f g hf hg :=
  toSumGlueLeft f g hf hg x.1

public def toSumGlueRightAway (hf : Injective f) (hg : Injective g) (y : RightAway g) :
    SumGlue f g hf hg :=
  toSumGlueRight f g hf hg y.1

public theorem range_toSumGlueLeftAway (hf : Injective f) (hg : Injective g) :
    Set.range (toSumGlueLeftAway f g hf hg) =
      (Set.range (toSumGlueRight f g hf hg))ᶜ := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩ haR
    rcases haR with ⟨y, hy⟩
    rcases (toSumGlue_eq_iff f g hf hg x.1 y).1 hy.symm with ⟨z, hzf, _⟩
    exact x.2 ⟨z, hzf⟩
  · intro haR
    rcases Quotient.mk_surjective a with ⟨b, rfl⟩
    rcases b with x | y
    · have hx : x ∉ Set.range f := by
        rintro ⟨z, rfl⟩
        exact haR ⟨g z, (toSumGlue_commute f g hf hg z).symm⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · exact False.elim (haR ⟨y, rfl⟩)

public theorem range_toSumGlueRightAway (hf : Injective f) (hg : Injective g) :
    Set.range (toSumGlueRightAway f g hf hg) =
      (Set.range (toSumGlueLeft f g hf hg))ᶜ := by
  ext a
  constructor
  · rintro ⟨y, rfl⟩ haL
    rcases haL with ⟨x, hx⟩
    rcases (toSumGlue_eq_iff f g hf hg x y.1).1 hx with ⟨z, _, hzg⟩
    exact y.2 ⟨z, hzg⟩
  · intro haL
    rcases Quotient.mk_surjective a with ⟨b, rfl⟩
    rcases b with x | y
    · exact False.elim (haL ⟨x, rfl⟩)
    · have hy : y ∉ Set.range g := by
        rintro ⟨z, rfl⟩
        exact haL ⟨f z, toSumGlue_commute f g hf hg z⟩
      exact ⟨⟨y, hy⟩, rfl⟩

end SumGlueAlgebra

section SumGlueTopology

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  (f : Z → X) (g : Z → Y)

/-- The gluing relation is closed when all three spaces are compact Hausdorff and the two maps are
continuous. -/
public theorem isClosed_sumGlueRel
    [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y] [CompactSpace Z]
    (hf : Continuous f) (hg : Continuous g) :
    IsClosed {p : (X ⊕ Y) × (X ⊕ Y) | sumGlueRel f g p.1 p.2} := by
  let dX : X → (X ⊕ Y) × (X ⊕ Y) := fun x => (.inl x, .inl x)
  let dY : Y → (X ⊕ Y) × (X ⊕ Y) := fun y => (.inr y, .inr y)
  let cLR : Z → (X ⊕ Y) × (X ⊕ Y) := fun z => (.inl (f z), .inr (g z))
  let cRL : Z → (X ⊕ Y) × (X ⊕ Y) := fun z => (.inr (g z), .inl (f z))
  have hdX : IsClosed (Set.range dX) :=
    (isCompact_range ((continuous_inl.comp continuous_id).prodMk
      (continuous_inl.comp continuous_id))).isClosed
  have hdY : IsClosed (Set.range dY) :=
    (isCompact_range ((continuous_inr.comp continuous_id).prodMk
      (continuous_inr.comp continuous_id))).isClosed
  have hcLR : IsClosed (Set.range cLR) :=
    (isCompact_range ((continuous_inl.comp hf).prodMk (continuous_inr.comp hg))).isClosed
  have hcRL : IsClosed (Set.range cRL) :=
    (isCompact_range ((continuous_inr.comp hg).prodMk (continuous_inl.comp hf))).isClosed
  have heq : {p : (X ⊕ Y) × (X ⊕ Y) | sumGlueRel f g p.1 p.2} =
      Set.range dX ∪ Set.range dY ∪ Set.range cLR ∪ Set.range cRL := by
    ext ⟨a, b⟩
    rcases a with x | y <;> rcases b with x' | y' <;>
      simp [sumGlueRel, dX, dY, cLR, cRL, eq_comm, and_comm]
  rw [heq]
  exact ((hdX.union hdY).union hcLR).union hcRL

variable (hf : Injective f) (hg : Injective g)

omit [TopologicalSpace Z] in
public theorem continuous_toSumGlueLeft : Continuous (toSumGlueLeft f g hf hg) :=
  continuous_quotient_mk'.comp continuous_inl

omit [TopologicalSpace Z] in
public theorem continuous_toSumGlueRight : Continuous (toSumGlueRight f g hf hg) :=
  continuous_quotient_mk'.comp continuous_inr

variable [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y] [CompactSpace Z]

/-- The sum-gluing carrier is Hausdorff. -/
public theorem sumGlue_t2Space (hfc : Continuous f) (hgc : Continuous g) :
    T2Space (SumGlue f g hf hg) :=
  quotient_t2Space_of_rel_isClosed (sumGlueSetoid f g hf hg)
    (isClosed_sumGlueRel f g hfc hgc)

/-- The sum-gluing carrier is second countable when both summands are second countable. -/
public theorem sumGlue_secondCountableTopology
    [SecondCountableTopology X] [SecondCountableTopology Y]
    (hfc : Continuous f) (hgc : Continuous g) :
    SecondCountableTopology (SumGlue f g hf hg) :=
  quotient_secondCountableTopology_of_rel_isClosed (sumGlueSetoid f g hf hg)
    (isClosed_sumGlueRel f g hfc hgc)

/-- The canonical map from the left summand is a closed embedding. -/
public theorem toSumGlueLeft_isClosedEmbedding (hfc : Continuous f) (hgc : Continuous g) :
    IsClosedEmbedding (toSumGlueLeft f g hf hg) := by
  let _ : T2Space (SumGlue f g hf hg) := sumGlue_t2Space f g hf hg hfc hgc
  exact (continuous_toSumGlueLeft f g hf hg).isClosedEmbedding
    (toSumGlueLeft_injective f g hf hg)

/-- The canonical map from the right summand is a closed embedding. -/
public theorem toSumGlueRight_isClosedEmbedding (hfc : Continuous f) (hgc : Continuous g) :
    IsClosedEmbedding (toSumGlueRight f g hf hg) := by
  let _ : T2Space (SumGlue f g hf hg) := sumGlue_t2Space f g hf hg hfc hgc
  exact (continuous_toSumGlueRight f g hf hg).isClosedEmbedding
    (toSumGlueRight_injective f g hf hg)

/-- Away from the gluing locus, the canonical map from the left summand is an open embedding. -/
public theorem toSumGlueLeftAway_isOpenEmbedding (hfc : Continuous f) (hgc : Continuous g) :
    IsOpenEmbedding (toSumGlueLeftAway f g hf hg) := by
  let _ : T2Space (SumGlue f g hf hg) := sumGlue_t2Space f g hf hg hfc hgc
  refine ⟨(toSumGlueLeft_isClosedEmbedding f g hf hg hfc hgc).isEmbedding.comp
    IsEmbedding.subtypeVal, ?_⟩
  rw [range_toSumGlueLeftAway f g hf hg]
  exact (toSumGlueRight_isClosedEmbedding f g hf hg hfc hgc).isClosed_range.isOpen_compl

/-- Away from the gluing locus, the canonical map from the right summand is an open embedding. -/
public theorem toSumGlueRightAway_isOpenEmbedding (hfc : Continuous f) (hgc : Continuous g) :
    IsOpenEmbedding (toSumGlueRightAway f g hf hg) := by
  let _ : T2Space (SumGlue f g hf hg) := sumGlue_t2Space f g hf hg hfc hgc
  refine ⟨(toSumGlueRight_isClosedEmbedding f g hf hg hfc hgc).isEmbedding.comp
    IsEmbedding.subtypeVal, ?_⟩
  rw [range_toSumGlueRightAway f g hf hg]
  exact (toSumGlueLeft_isClosedEmbedding f g hf hg hfc hgc).isClosed_range.isOpen_compl

end SumGlueTopology

end ClosedEmbeddingGluing
end SphereSixComplex
