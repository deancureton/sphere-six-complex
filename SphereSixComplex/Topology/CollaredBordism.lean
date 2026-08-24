module

public import Mathlib.Geometry.Manifold.Bordism
public import SphereSixComplex.Topology.CylinderSmoothEmbedding
public import SphereSixComplex.Topology.SmoothEmbeddingSum
public import SphereSixComplex.Topology.SmoothOpenEmbedding

/-!
# Smooth collared bordisms

This file packages elementary smooth bordism data without assuming a collar-neighbourhood or
manifold-gluing theorem.  A collar is an explicit diffeomorphism from `M × [0, 1)` onto an open
subset of the ambient manifold-with-boundary.  The half-open interval is represented as an open
submanifold of Mathlib's closed interval.  Its zero section is separately certified as a smooth
embedding because Mathlib's general composition theorem for smooth embeddings is currently a
declaration without a proof.

The ambient boundary is accounted for by an equality of point sets.  This is the strongest honest
formulation available before arbitrary manifold boundaries acquire a bundled smooth-submanifold
structure in Mathlib.

The `SmoothOpenEmbedding` packaging is inspired by the sphere-eversion design.
-/

@[expose] public section

noncomputable section

open Function Set
open scoped ContDiff Manifold Topology

namespace SphereSixComplex

universe uE uH uM uW

/-- Explicit smooth half-collar chart data for `M` inside `W`.

The chart identifies the standard half-open collar source `M × [0, 1)` with an open subset of
`W`, and the endpoint inclusion is the image of its zero section.  This standalone structure does
not claim that `W` is a manifold or that the zero section is its boundary; `SmoothCollaredBordism`
supplies those hypotheses together with compactness, boundarylessness of the ends, and exact
boundary accounting. -/
public structure SmoothCollar
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) (M : Type uM) (W : Type uW)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [TopologicalSpace W] [ChartedSpace (ModelProd H (EuclideanHalfSpace 1)) W] where
  /-- Diffeomorphism from the standard half-open collar to an open neighborhood in `W`. -/
  chart : SmoothOpenEmbedding (I.prod (𝓡∂ 1)) (CollarSource M) W
  /-- The actual zero-section inclusion is a codimension-one smooth embedding. -/
  inclusion_isSmoothEmbedding :
    Manifold.IsSmoothEmbedding I (I.prod (𝓡∂ 1)) ∞
      (fun x ↦ chart (collarSourceZeroSection M x))

namespace SmoothCollar

variable {E H M W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace W] [ChartedSpace (ModelProd H (EuclideanHalfSpace 1)) W]

/-- The embedded end underlying a collar. -/
public def inclusion (c : SmoothCollar I M W) : M → W :=
  fun x ↦ c.chart (collarSourceZeroSection M x)

@[simp]
public theorem inclusion_apply (c : SmoothCollar I M W) (x : M) :
    c.inclusion x = c.chart (collarSourceZeroSection M x) :=
  rfl

/-- A collar inclusion is smooth. -/
public theorem inclusion_contMDiff (c : SmoothCollar I M W) :
    ContMDiff I (I.prod (𝓡∂ 1)) ∞ c.inclusion :=
  c.inclusion_isSmoothEmbedding.contMDiff

/-- A collar inclusion is a topological embedding. -/
public theorem inclusion_isEmbedding (c : SmoothCollar I M W) :
    Topology.IsEmbedding c.inclusion :=
  c.inclusion_isSmoothEmbedding.isEmbedding

section Sum

variable {N V : Type*} [FiniteDimensional ℝ E]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [IsManifold (I.prod (𝓡∂ 1)) ∞ W]
  [TopologicalSpace V] [ChartedSpace (ModelProd H (EuclideanHalfSpace 1)) V]
  [IsManifold (I.prod (𝓡∂ 1)) ∞ V]

/-- Disjoint union of two explicit collars. -/
public def sum (c : SmoothCollar I M W) (d : SmoothCollar I N V) :
    SmoothCollar I (M ⊕ N) (W ⊕ V) where
  chart :=
    { target := (c.chart.sum d.chart).target
      toDiffeomorph :=
        (Diffeomorph.sumProdDistrib I (𝓡∂ 1) M N HalfCollarParameter ∞).trans
          (c.chart.sum d.chart).toDiffeomorph }
  inclusion_isSmoothEmbedding := by
    have h := SmoothEmbeddingSum.isSmoothEmbedding_sumMap
      c.inclusion_isSmoothEmbedding d.inclusion_isSmoothEmbedding
    have heq :
        (fun x ↦
          ({ target := (c.chart.sum d.chart).target
             toDiffeomorph :=
               (Diffeomorph.sumProdDistrib I (𝓡∂ 1) M N HalfCollarParameter ∞).trans
                 (c.chart.sum d.chart).toDiffeomorph } :
            SmoothOpenEmbedding (I.prod (𝓡∂ 1)) (CollarSource (M ⊕ N)) (W ⊕ V))
              (collarSourceZeroSection (M ⊕ N) x)) =
          Sum.map c.inclusion d.inclusion := by
      funext x
      cases x <;> rfl
    rw [heq]
    exact h

@[simp]
public theorem sum_inclusion_inl (c : SmoothCollar I M W) (d : SmoothCollar I N V)
    (x : M) : (c.sum d).inclusion (Sum.inl x) = Sum.inl (c.inclusion x) :=
  rfl

@[simp]
public theorem sum_inclusion_inr (c : SmoothCollar I M W) (d : SmoothCollar I N V)
    (x : N) : (c.sum d).inclusion (Sum.inr x) = Sum.inr (d.inclusion x) :=
  rfl

/-- The range of a disjoint-union collar is the union of the two component ranges. -/
public theorem range_sum_inclusion (c : SmoothCollar I M W) (d : SmoothCollar I N V) :
    range (c.sum d).inclusion =
      Sum.inl '' range c.inclusion ∪ Sum.inr '' range d.inclusion := by
  ext p
  constructor
  · rintro ⟨x, hx⟩
    cases x with
    | inl x =>
        change (c.sum d).inclusion (Sum.inl x) = p at hx
        rw [sum_inclusion_inl] at hx
        left
        exact ⟨c.inclusion x, ⟨x, rfl⟩, hx⟩
    | inr x =>
        change (c.sum d).inclusion (Sum.inr x) = p at hx
        rw [sum_inclusion_inr] at hx
        right
        exact ⟨d.inclusion x, ⟨x, rfl⟩, hx⟩
  · rintro (⟨_, ⟨x, rfl⟩, rfl⟩ | ⟨_, ⟨x, rfl⟩, rfl⟩)
    · exact ⟨Sum.inl x, sum_inclusion_inl c d x⟩
    · exact ⟨Sum.inr x, sum_inclusion_inr c d x⟩

end Sum

end SmoothCollar

/-- A compact smooth bordism with explicit collars and exact boundary accounting. -/
public structure SmoothCollaredBordism
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type uH} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) (M₀ M₁ : Type*)
    [TopologicalSpace M₀] [T2Space M₀] [SecondCountableTopology M₀]
    [ChartedSpace H M₀] [IsManifold I ∞ M₀] [CompactSpace M₀]
    [BoundarylessManifold I M₀]
    [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [ChartedSpace H M₁] [IsManifold I ∞ M₁] [CompactSpace M₁]
    [BoundarylessManifold I M₁] where
  /-- Carrier of the bordism. -/
  W : Type uW
  [topologicalSpaceW : TopologicalSpace W]
  [t2SpaceW : T2Space W]
  [secondCountableTopologyW : SecondCountableTopology W]
  [chartedSpaceW : ChartedSpace (ModelProd H (EuclideanHalfSpace 1)) W]
  [isManifoldW : IsManifold (I.prod (𝓡∂ 1)) ∞ W]
  [compactSpaceW : CompactSpace W]
  /-- Collar at the incoming end. -/
  incoming : SmoothCollar I M₀ W
  /-- Collar at the outgoing end. -/
  outgoing : SmoothCollar I M₁ W
  /-- The embedded zero sections are disjoint. -/
  ends_disjoint : Disjoint (range incoming.inclusion) (range outgoing.inclusion)
  /-- The embedded zero sections account for every boundary point, and no other point. -/
  boundary_eq : (I.prod (𝓡∂ 1)).boundary W =
    range incoming.inclusion ∪ range outgoing.inclusion

namespace SmoothCollaredBordism

variable {E : Type uE} {H : Type uH} {M₀ M₁ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M₀] [T2Space M₀] [SecondCountableTopology M₀]
  [ChartedSpace H M₀] [IsManifold I ∞ M₀] [CompactSpace M₀]
  [BoundarylessManifold I M₀]
  [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
  [ChartedSpace H M₁] [IsManifold I ∞ M₁] [CompactSpace M₁]
  [BoundarylessManifold I M₁]

public instance (B : SmoothCollaredBordism I M₀ M₁) : TopologicalSpace B.W :=
  B.topologicalSpaceW

public instance (B : SmoothCollaredBordism I M₀ M₁) : T2Space B.W :=
  B.t2SpaceW

public instance (B : SmoothCollaredBordism I M₀ M₁) : SecondCountableTopology B.W :=
  B.secondCountableTopologyW

public instance (B : SmoothCollaredBordism I M₀ M₁) :
    ChartedSpace (ModelProd H (EuclideanHalfSpace 1)) B.W :=
  B.chartedSpaceW

public instance (B : SmoothCollaredBordism I M₀ M₁) :
    IsManifold (I.prod (𝓡∂ 1)) ∞ B.W :=
  B.isManifoldW

public instance (B : SmoothCollaredBordism I M₀ M₁) : CompactSpace B.W :=
  B.compactSpaceW

/-- Reverse a collared bordism by exchanging its two explicitly collared ends. -/
public def reverse (B : SmoothCollaredBordism I M₀ M₁) :
    SmoothCollaredBordism I M₁ M₀ where
  W := B.W
  incoming := B.outgoing
  outgoing := B.incoming
  ends_disjoint := B.ends_disjoint.symm
  boundary_eq := by
    rw [B.boundary_eq, union_comm]

@[simp]
public theorem reverse_incoming (B : SmoothCollaredBordism I M₀ M₁) :
    B.reverse.incoming = B.outgoing :=
  rfl

@[simp]
public theorem reverse_outgoing (B : SmoothCollaredBordism I M₀ M₁) :
    B.reverse.outgoing = B.incoming :=
  rfl

section Cylinder

variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  [BoundarylessManifold I M]

/-- The standard half-open neighborhood at the initial end of a cylinder. -/
public def cylinderIncomingOpenEmbedding :
    SmoothOpenEmbedding (I.prod (𝓡∂ 1)) (CollarSource M) (M × CollarParameter) where
  target := CollarDomain M
  toDiffeomorph := collarSourceToDomain

/-- The reflected half-open neighborhood at the final end of a cylinder. -/
public def cylinderOutgoingOpenEmbedding :
    SmoothOpenEmbedding (I.prod (𝓡∂ 1)) (CollarSource M) (M × CollarParameter) where
  target := ReflectedCollarDomain M
  toDiffeomorph := collarSourceToReflectedDomain

/-- Initial collar of the cylinder. -/
public def cylinderIncomingCollar : SmoothCollar I M (M × CollarParameter) where
  chart := cylinderIncomingOpenEmbedding
  inclusion_isSmoothEmbedding := by
    change Manifold.IsSmoothEmbedding I (I.prod (𝓡∂ 1)) ∞
      (fun x : M ↦ (x, collarStart))
    exact isSmoothEmbedding_collarStartSection

/-- Final collar of the cylinder. -/
public def cylinderOutgoingCollar : SmoothCollar I M (M × CollarParameter) where
  chart := cylinderOutgoingOpenEmbedding
  inclusion_isSmoothEmbedding := by
    have hfun :
        (fun x : M ↦ cylinderOutgoingOpenEmbedding (I := I)
          (collarSourceZeroSection M x)) =
          (fun x : M ↦ (x, collarFinish)) := by
      funext x
      change (collarSourceToReflectedDomain (I₀ := I)
        (collarSourceZeroSection M x) : M × CollarParameter) = (x, collarFinish)
      simp [collarSourceZeroSection, halfCollarStart]
    rw [hfun]
    exact isSmoothEmbedding_collarFinishSection

omit [FiniteDimensional ℝ E] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [BoundarylessManifold I M] in
@[simp] public theorem cylinderIncomingCollar_inclusion (x : M) :
    (cylinderIncomingCollar (I := I) : SmoothCollar I M _).inclusion x =
      (x, collarStart) :=
  rfl

omit [FiniteDimensional ℝ E] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [BoundarylessManifold I M] in
@[simp] public theorem cylinderOutgoingCollar_inclusion (x : M) :
    (cylinderOutgoingCollar (I := I) : SmoothCollar I M _).inclusion x =
      (x, collarFinish) := by
  change (collarSourceToReflectedDomain (I₀ := I)
    (collarSourceZeroSection M x) : M × CollarParameter) = (x, collarFinish)
  simp [collarSourceZeroSection, halfCollarStart]

/-- The cylinder is an actual compact smooth collared bordism. -/
public def cylinder : SmoothCollaredBordism I M M where
  W := M × CollarParameter
  incoming := cylinderIncomingCollar
  outgoing := cylinderOutgoingCollar
  ends_disjoint := by
    rw [Set.disjoint_left]
    rintro p ⟨x, hx⟩ ⟨y, hy⟩
    rw [cylinderIncomingCollar_inclusion] at hx
    rw [cylinderOutgoingCollar_inclusion] at hy
    have h := congrArg (fun q : M × CollarParameter ↦ (q.2 : ℝ))
      (hy.trans hx.symm)
    norm_num [collarStart, collarFinish] at h
  boundary_eq := by
    rw [ModelWithCorners.boundary_of_boundaryless_left, boundary_Icc]
    ext p
    rcases p with ⟨x, t⟩
    simp only [Set.mem_union, Set.mem_range, cylinderIncomingCollar_inclusion,
      cylinderOutgoingCollar_inclusion]
    change (x ∈ (Set.univ : Set M) ∧ t ∈ ({⊥, ⊤} : Set CollarParameter)) ↔
      ((∃ y : M, (y, collarStart) = (x, t)) ∨
        ∃ y : M, (y, collarFinish) = (x, t))
    simp [collarStart, collarFinish, eq_comm]
    have hzero : (⊥ : CollarParameter) = 0 := Subtype.ext (by norm_num)
    have hone : (⊤ : CollarParameter) = 1 := Subtype.ext (by norm_num)
    rw [hzero, hone]

end Cylinder

section DisjointUnion

variable {N₀ N₁ : Type*}
  [TopologicalSpace N₀] [T2Space N₀] [SecondCountableTopology N₀]
  [ChartedSpace H N₀] [IsManifold I ∞ N₀] [CompactSpace N₀]
  [BoundarylessManifold I N₀]
  [TopologicalSpace N₁] [T2Space N₁] [SecondCountableTopology N₁]
  [ChartedSpace H N₁] [IsManifold I ∞ N₁] [CompactSpace N₁]
  [BoundarylessManifold I N₁]

/-- Disjoint union of smooth collared bordisms, including the induced collars and exact boundary
identity. -/
public def disjointUnion (B : SmoothCollaredBordism I M₀ M₁)
    (C : SmoothCollaredBordism I N₀ N₁) :
    SmoothCollaredBordism I (M₀ ⊕ N₀) (M₁ ⊕ N₁) where
  W := B.W ⊕ C.W
  incoming := B.incoming.sum C.incoming
  outgoing := B.outgoing.sum C.outgoing
  ends_disjoint := by
    rw [Set.disjoint_left]
    rintro p ⟨x, hx⟩ ⟨y, hy⟩
    cases x with
    | inl x =>
        rw [SmoothCollar.sum_inclusion_inl] at hx
        cases y with
        | inl y =>
            rw [SmoothCollar.sum_inclusion_inl] at hy
            exact Set.disjoint_left.1 B.ends_disjoint
              ⟨x, rfl⟩ ⟨y, Sum.inl.inj (hy.trans hx.symm)⟩
        | inr y =>
            rw [SmoothCollar.sum_inclusion_inr] at hy
            simpa using hy.trans hx.symm
    | inr x =>
        rw [SmoothCollar.sum_inclusion_inr] at hx
        cases y with
        | inl y =>
            rw [SmoothCollar.sum_inclusion_inl] at hy
            simpa using hy.trans hx.symm
        | inr y =>
            rw [SmoothCollar.sum_inclusion_inr] at hy
            exact Set.disjoint_left.1 C.ends_disjoint
              ⟨x, rfl⟩ ⟨y, Sum.inr.inj (hy.trans hx.symm)⟩
  boundary_eq := by
    rw [ModelWithCorners.boundary_disjointUnion, B.boundary_eq, C.boundary_eq]
    rw [SmoothCollar.range_sum_inclusion, SmoothCollar.range_sum_inclusion,
      image_union, image_union]
    ac_rfl

@[simp]
public theorem disjointUnion_incoming_inl (B : SmoothCollaredBordism I M₀ M₁)
    (C : SmoothCollaredBordism I N₀ N₁) (x : M₀) :
    (B.disjointUnion C).incoming.inclusion (Sum.inl x) =
      Sum.inl (B.incoming.inclusion x) :=
  rfl

@[simp]
public theorem disjointUnion_incoming_inr (B : SmoothCollaredBordism I M₀ M₁)
    (C : SmoothCollaredBordism I N₀ N₁) (x : N₀) :
    (B.disjointUnion C).incoming.inclusion (Sum.inr x) =
      Sum.inr (C.incoming.inclusion x) :=
  rfl

end DisjointUnion

universe uWG

/-- A fully universe-polymorphic compatibility interface for smooth collar gluing.

The concrete common-universe construction used by h-cobordism transitivity is provided later as
`SmoothCollaredBordism.QuotientGluing.smoothGlue`.  This stronger interface also allows the two
end types and the bordism carriers to live in independent universes; it is retained for callers
that specifically need that extra universe generality. -/
public def SmoothCollaredBordismGluingStatement : Prop :=
  ∀ {M₂ : Type*}
    [TopologicalSpace M₂] [T2Space M₂] [SecondCountableTopology M₂]
    [ChartedSpace H M₂] [IsManifold I ∞ M₂] [CompactSpace M₂]
    [BoundarylessManifold I M₂],
    SmoothCollaredBordism.{uE, uH, uWG} I M₀ M₁ →
      SmoothCollaredBordism.{uE, uH, uWG} I M₁ M₂ →
      Nonempty (SmoothCollaredBordism.{uE, uH, uWG} I M₀ M₂)

end SmoothCollaredBordism

end SphereSixComplex
