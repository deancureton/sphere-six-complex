module

public import SphereSixComplex.Topology.CollaredBordism

/-!
# Boundary locality for explicit collars

The boundary of the standard half-open collar is exactly its zero section.  Consequently, the
open target of a collar meets the ambient boundary precisely in the image of that zero section.
For a collared bordism this implies that either end-collar target is disjoint from the other end.
These facts let untouched collars descend through a later gluing operation.
-/

@[expose] public section

noncomputable section

open Function Set
open scoped ContDiff Manifold Topology

namespace SphereSixComplex

universe uE uH uM uW

/-- The only manifold-boundary point of the half-open collar parameter is its initial endpoint. -/
public theorem boundary_halfCollarParameter :
    (𝓡∂ 1).boundary HalfCollarParameter = {halfCollarStart} := by
  rw [ModelWithCorners.boundary_open, boundary_Icc]
  ext t
  simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro ht
    rcases ht with ht | ht
    · have hbot : (⊥ : CollarParameter) = collarStart := by
        apply Subtype.ext
        norm_num [collarStart]
      apply Subtype.ext
      simpa only [halfCollarStart] using ht.trans hbot
    · exfalso
      have hlt : ((t.1 : CollarParameter) : ℝ) < 1 := t.2
      have hone : ((t.1 : CollarParameter) : ℝ) = 1 := by
        have h := congrArg Subtype.val ht
        simpa using h
      linarith
  · intro ht
    left
    subst t
    have hbot : (⊥ : CollarParameter) = collarStart := by
      apply Subtype.ext
      norm_num [collarStart]
    simpa only [halfCollarStart] using hbot.symm

/-- The boundary of a standard collar source is its zero section. -/
public theorem boundary_collarSource
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
    [BoundarylessManifold I M] :
    (I.prod (𝓡∂ 1)).boundary (CollarSource M) =
      Set.range (collarSourceZeroSection M) := by
  rw [ModelWithCorners.boundary_of_boundaryless_left, boundary_halfCollarParameter]
  ext p
  constructor
  · intro hp
    rcases hp with ⟨_, ht⟩
    refine ⟨p.1, ?_⟩
    exact Prod.ext rfl ht.symm
  · rintro ⟨x, rfl⟩
    exact ⟨Set.mem_univ x, rfl⟩

namespace SmoothCollar

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M]
  {W : Type uW} [TopologicalSpace W]
  [ChartedSpace (ModelProd H (EuclideanHalfSpace 1)) W]
  [IsManifold (I.prod (𝓡∂ 1)) ∞ W]

/-- A collar chart carries precisely the zero-section boundary of its source to the ambient
boundary points lying in its open target. -/
public theorem target_boundary_eq_range_inclusion (c : SmoothCollar I M W) :
    {w : c.chart.target | w.1 ∈ (I.prod (𝓡∂ 1)).boundary W} =
      Set.range (fun x : M ↦
        ⟨c.inclusion x, c.chart.toDiffeomorph (collarSourceZeroSection M x) |>.2⟩) := by
  have hpre := c.chart.toDiffeomorph.preimage_boundary (n := ∞) (by simp)
  rw [ModelWithCorners.boundary_open, boundary_collarSource] at hpre
  ext w
  constructor
  · intro hw
    let p := c.chart.toDiffeomorph.symm w
    have hp : p ∈ Set.range (collarSourceZeroSection M) := by
      rw [← hpre]
      simpa [p] using hw
    rcases hp with ⟨x, hx⟩
    refine ⟨x, Subtype.ext ?_⟩
    change (c.chart.toDiffeomorph (collarSourceZeroSection M x) : W) = (w : W)
    rw [hx]
    exact congrArg Subtype.val (c.chart.toDiffeomorph.apply_symm_apply w)
  · rintro ⟨x, rfl⟩
    change c.inclusion x ∈ (I.prod (𝓡∂ 1)).boundary W
    have hp : collarSourceZeroSection M x ∈
        Set.range (collarSourceZeroSection M) := ⟨x, rfl⟩
    rw [← hpre] at hp
    exact hp

/-- Inside the ambient manifold, a collar target meets the boundary exactly in the collar's
specified end inclusion. -/
public theorem target_inter_boundary_eq_range_inclusion (c : SmoothCollar I M W) :
    (c.chart.target : Set W) ∩ (I.prod (𝓡∂ 1)).boundary W =
      Set.range c.inclusion := by
  ext w
  constructor
  · rintro ⟨hwT, hwB⟩
    have hw : (⟨w, hwT⟩ : c.chart.target) ∈
        {z : c.chart.target | z.1 ∈ (I.prod (𝓡∂ 1)).boundary W} := hwB
    rw [c.target_boundary_eq_range_inclusion] at hw
    rcases hw with ⟨x, hx⟩
    exact ⟨x, congrArg Subtype.val hx⟩
  · rintro ⟨x, rfl⟩
    refine ⟨c.chart.toDiffeomorph (collarSourceZeroSection M x) |>.2, ?_⟩
    have hw :
        (⟨c.inclusion x,
          c.chart.toDiffeomorph (collarSourceZeroSection M x) |>.2⟩ : c.chart.target) ∈
          {z : c.chart.target | z.1 ∈ (I.prod (𝓡∂ 1)).boundary W} := by
      rw [c.target_boundary_eq_range_inclusion]
      exact ⟨x, rfl⟩
    exact hw

end SmoothCollar

namespace SmoothCollaredBordism

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M₀ M₁ : Type uM}
  [TopologicalSpace M₀] [T2Space M₀] [SecondCountableTopology M₀]
  [ChartedSpace H M₀] [IsManifold I ∞ M₀] [CompactSpace M₀]
  [BoundarylessManifold I M₀]
  [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
  [ChartedSpace H M₁] [IsManifold I ∞ M₁] [CompactSpace M₁]
  [BoundarylessManifold I M₁]

/-- The incoming collar target cannot contain a point of the outgoing end. -/
public theorem incoming_target_disjoint_outgoing
    (B : SmoothCollaredBordism.{uE, uH, uW} I M₀ M₁) :
    Disjoint (B.incoming.chart.target : Set B.W) (Set.range B.outgoing.inclusion) := by
  rw [Set.disjoint_left]
  intro w hwT hwO
  have hwB : w ∈ (I.prod (𝓡∂ 1)).boundary B.W := by
    rw [B.boundary_eq]
    exact Or.inr hwO
  have hwI : w ∈ Set.range B.incoming.inclusion := by
    rw [← B.incoming.target_inter_boundary_eq_range_inclusion]
    exact ⟨hwT, hwB⟩
  exact Set.disjoint_left.1 B.ends_disjoint hwI hwO

/-- The outgoing collar target cannot contain a point of the incoming end. -/
public theorem outgoing_target_disjoint_incoming
    (B : SmoothCollaredBordism.{uE, uH, uW} I M₀ M₁) :
    Disjoint (B.outgoing.chart.target : Set B.W) (Set.range B.incoming.inclusion) := by
  rw [Set.disjoint_left]
  intro w hwT hwI
  have hwB : w ∈ (I.prod (𝓡∂ 1)).boundary B.W := by
    rw [B.boundary_eq]
    exact Or.inl hwI
  have hwO : w ∈ Set.range B.outgoing.inclusion := by
    rw [← B.outgoing.target_inter_boundary_eq_range_inclusion]
    exact ⟨hwT, hwB⟩
  exact Set.disjoint_left.1 B.ends_disjoint hwI hwO

end SmoothCollaredBordism

end SphereSixComplex
