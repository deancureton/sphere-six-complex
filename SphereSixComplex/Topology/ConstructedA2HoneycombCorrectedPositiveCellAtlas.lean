module

public import SphereSixComplex.Topology.ConstructedA2HoneycombCorrectedHexagonalCell

@[expose] public section

noncomputable section

open Function Set Topology Matrix

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

public theorem constructedA2CorrectedHexagonCenter_mem
    (v : ToricLattice) :
    constructedA2CorrectedPlaneCenter v ∈ constructedA2CorrectedPlaneCell v := by
  have h := (constructedA2CorrectedHexagonHomeomorph_mem_closed_iff v 0).mpr
    (Metric.mem_closedBall_self zero_le_one)
  simpa [constructedA2CorrectedHexagonHomeomorph,
    constructedA2SquareToHexagonRadial] using h

public noncomputable def constructedA2CorrectedPositiveHexagonMap
    {r : ℝ} (hr : 0 < r) (v : ToricLattice) (x : Fin 2 → ℝ) :
    constructedPositiveCentralFiber r := by
  classical
  exact if hx : constructedA2CorrectedHexagonHomeomorph v x ∈
      constructedA2CorrectedPlaneCell v then
    (constructedA2CorrectedFiniteQuotientCellHomeomorph hr v
      ⟨constructedA2CorrectedHexagonHomeomorph v x, hx⟩ :
        constructedPositiveCentralCell r v)
  else constructedA2CorrectedFiniteQuotientCellHomeomorph hr v
      ⟨constructedA2CorrectedPlaneCenter v,
        constructedA2CorrectedHexagonCenter_mem v⟩

public theorem constructedA2CorrectedPositiveHexagonMap_of_mem_closedBall
    {r : ℝ} (hr : 0 < r) (v : ToricLattice) (x : Fin 2 → ℝ)
    (hx : x ∈ Metric.closedBall 0 1) :
    constructedA2CorrectedPositiveHexagonMap hr v x =
      (constructedA2CorrectedFiniteQuotientCellHomeomorph hr v
        ⟨constructedA2CorrectedHexagonHomeomorph v x,
          (constructedA2CorrectedHexagonHomeomorph_mem_closed_iff v x).mpr hx⟩ :
            constructedPositiveCentralCell r v) := by
  classical
  rw [constructedA2CorrectedPositiveHexagonMap, dite_eq_left]

public theorem constructedA2CorrectedPositiveHexagonMap_continuousOn
    {r : ℝ} (hr : 0 < r) (v : ToricLattice) :
    ContinuousOn (constructedA2CorrectedPositiveHexagonMap hr v)
      (Metric.closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let F : Metric.closedBall (0 : Fin 2 → ℝ) 1 →
      constructedPositiveCentralFiber r := fun x ↦
    (constructedA2CorrectedFiniteQuotientCellHomeomorph hr v
      ⟨constructedA2CorrectedHexagonHomeomorph v x.1,
        (constructedA2CorrectedHexagonHomeomorph_mem_closed_iff v x.1).mpr x.2⟩ :
          constructedPositiveCentralCell r v)
  have hF : Continuous F := by
    apply Continuous.subtype_val
    exact (constructedA2CorrectedFiniteQuotientCellHomeomorph hr v).continuous.comp
      ((constructedA2CorrectedHexagonHomeomorph v).continuous.comp
        continuous_subtype_val |>.subtype_mk _)
  convert hF using 1
  funext x
  exact constructedA2CorrectedPositiveHexagonMap_of_mem_closedBall hr v x.1 x.2

public theorem constructedA2CorrectedPositiveHexagonMap_injOn_closedBall
    {r : ℝ} (hr : 0 < r) (v : ToricLattice) :
    Set.InjOn (constructedA2CorrectedPositiveHexagonMap hr v)
      (Metric.closedBall 0 1) := by
  intro x hx y hy hxy
  rw [constructedA2CorrectedPositiveHexagonMap_of_mem_closedBall hr v x hx,
    constructedA2CorrectedPositiveHexagonMap_of_mem_closedBall hr v y hy] at hxy
  have hsub :
      (⟨constructedA2CorrectedHexagonHomeomorph v x,
          (constructedA2CorrectedHexagonHomeomorph_mem_closed_iff v x).mpr hx⟩ :
        constructedA2CorrectedPlaneCell v) =
      ⟨constructedA2CorrectedHexagonHomeomorph v y,
          (constructedA2CorrectedHexagonHomeomorph_mem_closed_iff v y).mpr hy⟩ :=
    (constructedA2CorrectedFiniteQuotientCellHomeomorph hr v).injective
      (Subtype.ext hxy)
  exact (constructedA2CorrectedHexagonHomeomorph v).injective
    (congrArg Subtype.val hsub)

public def constructedA2CorrectedPositiveHexagonalCell
    {r : ℝ} (hr : 0 < r) (v : ToricLattice) :
    PartialEquiv (Fin 2 → ℝ) (constructedPositiveCentralFiber r) :=
  Set.InjOn.toPartialEquiv (constructedA2CorrectedPositiveHexagonMap hr v)
    (Metric.ball 0 1)
    ((constructedA2CorrectedPositiveHexagonMap_injOn_closedBall hr v).mono
      Metric.ball_subset_closedBall)

public theorem constructedA2CorrectedPositiveHexagonalCell_source_eq
    {r : ℝ} (hr : 0 < r) (v : ToricLattice) :
    (constructedA2CorrectedPositiveHexagonalCell hr v).source =
      Metric.ball 0 1 := rfl

public theorem constructedA2CorrectedPositiveHexagonalCell_continuousOn
    {r : ℝ} (hr : 0 < r) (v : ToricLattice) :
    ContinuousOn (constructedA2CorrectedPositiveHexagonalCell hr v)
      (Metric.closedBall 0 1) :=
  constructedA2CorrectedPositiveHexagonMap_continuousOn hr v

public theorem constructedA2CorrectedPositiveHexagonMap_isEmbedding
    {r : ℝ} (hr : 0 < r) (v : ToricLattice) :
    Topology.IsEmbedding
      ((Metric.ball (0 : Fin 2 → ℝ) 1).domRestrict
        (constructedA2CorrectedPositiveHexagonMap hr v)) := by
  let G : Metric.ball (0 : Fin 2 → ℝ) 1 →
      constructedA2CorrectedPlaneCell v := fun x ↦
    ⟨constructedA2CorrectedHexagonHomeomorph v x.1,
      (constructedA2CorrectedHexagonHomeomorph_mem_closed_iff v x.1).mpr
        (Metric.ball_subset_closedBall x.2)⟩
  have hG : Topology.IsEmbedding G := by
    apply Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
    change Topology.IsEmbedding (fun x : Metric.ball (0 : Fin 2 → ℝ) 1 ↦
      constructedA2CorrectedHexagonHomeomorph v x.1)
    exact (constructedA2CorrectedHexagonHomeomorph v).isEmbedding.comp
      Topology.IsEmbedding.subtypeVal
  have hcell : Topology.IsEmbedding
      (fun y : constructedA2CorrectedPlaneCell v ↦
        ((constructedA2CorrectedFiniteQuotientCellHomeomorph hr v y :
          constructedPositiveCentralCell r v) : constructedPositiveCentralFiber r)) :=
    Topology.IsEmbedding.subtypeVal.comp
      (constructedA2CorrectedFiniteQuotientCellHomeomorph hr v).isEmbedding
  have hcomp := hcell.comp hG
  convert hcomp using 1
  funext x
  exact constructedA2CorrectedPositiveHexagonMap_of_mem_closedBall hr v x.1
    (Metric.ball_subset_closedBall x.2)

public theorem constructedA2CorrectedPositiveHexagonalCell_continuousOn_symm
    {r : ℝ} (hr : 0 < r) (v : ToricLattice) :
    ContinuousOn (constructedA2CorrectedPositiveHexagonalCell hr v).symm
      (constructedA2CorrectedPositiveHexagonalCell hr v).target := by
  let e := constructedA2CorrectedPositiveHexagonalCell hr v
  let lift : e.target → Metric.ball (0 : Fin 2 → ℝ) 1 :=
    fun q ↦ ⟨e.symm q, e.map_target q.2⟩
  have hlift : Continuous lift := by
    apply (constructedA2CorrectedPositiveHexagonMap_isEmbedding hr v).continuous_iff.mpr
    have heq :
        (Metric.ball (0 : Fin 2 → ℝ) 1).domRestrict
            (constructedA2CorrectedPositiveHexagonMap hr v) ∘ lift =
          (Subtype.val : e.target → constructedPositiveCentralFiber r) := by
      funext q
      exact e.right_inv q.2
    rw [heq]
    exact continuous_subtype_val
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun q : e.target ↦ (lift q : Fin 2 → ℝ))
  exact continuous_subtype_val.comp hlift

public theorem constructedA2CorrectedPositiveHexagonalCell_closedBall_image
    {r : ℝ} (hr : 0 < r) (v : ToricLattice) :
    constructedA2CorrectedPositiveHexagonalCell hr v '' Metric.closedBall 0 1 =
      constructedPositiveCentralCell r v := by
  apply Set.Subset.antisymm
  · rintro q ⟨x, hx, rfl⟩
    change constructedA2CorrectedPositiveHexagonMap hr v x ∈
      constructedPositiveCentralCell r v
    rw [constructedA2CorrectedPositiveHexagonMap_of_mem_closedBall hr v x hx]
    exact (constructedA2CorrectedFiniteQuotientCellHomeomorph hr v
      ⟨constructedA2CorrectedHexagonHomeomorph v x,
        (constructedA2CorrectedHexagonHomeomorph_mem_closed_iff v x).mpr hx⟩).2
  · intro q hq
    let z : constructedPositiveCentralCell r v := ⟨q, hq⟩
    let y := (constructedA2CorrectedFiniteQuotientCellHomeomorph hr v).symm z
    let x := (constructedA2CorrectedHexagonHomeomorph v).symm y.1
    have hx : x ∈ Metric.closedBall 0 1 := by
      apply (constructedA2CorrectedHexagonHomeomorph_mem_closed_iff v x).mp
      change constructedA2CorrectedHexagonHomeomorph v
        ((constructedA2CorrectedHexagonHomeomorph v).symm y.1) ∈
          constructedA2CorrectedPlaneCell v
      rw [(constructedA2CorrectedHexagonHomeomorph v).apply_symm_apply]
      exact y.2
    refine ⟨x, hx, ?_⟩
    change constructedA2CorrectedPositiveHexagonMap hr v x = q
    rw [constructedA2CorrectedPositiveHexagonMap_of_mem_closedBall hr v x hx]
    have hz : constructedA2CorrectedFiniteQuotientCellHomeomorph hr v
        ⟨constructedA2CorrectedHexagonHomeomorph v x,
          (constructedA2CorrectedHexagonHomeomorph_mem_closed_iff v x).mpr hx⟩ = z := by
      apply (constructedA2CorrectedFiniteQuotientCellHomeomorph hr v).symm.injective
      rw [(constructedA2CorrectedFiniteQuotientCellHomeomorph hr v).symm_apply_apply]
      change (⟨constructedA2CorrectedHexagonHomeomorph v x,
        (constructedA2CorrectedHexagonHomeomorph_mem_closed_iff v x).mpr hx⟩ :
          constructedA2CorrectedPlaneCell v) = y
      apply Subtype.ext
      exact (constructedA2CorrectedHexagonHomeomorph v).apply_symm_apply y.1
    simpa [z] using congrArg Subtype.val hz

public theorem constructedA2CorrectedPositiveHexagonalCell_mapsTo_boundary
    {r : ℝ} (hr : 0 < r) (v : ToricLattice) :
    MapsTo (constructedA2CorrectedPositiveHexagonalCell hr v) (Metric.sphere 0 1)
      (constructedPositiveCentralCell r v) := by
  intro x hx
  apply (constructedA2CorrectedPositiveHexagonalCell_closedBall_image hr v).subset
  exact ⟨x, Metric.sphere_subset_closedBall hx, rfl⟩

public theorem constructedA2CorrectedPositiveHexagonalCell_sphere_image
    {r : ℝ} (hr : 0 < r) (v : ToricLattice) :
    constructedA2CorrectedPositiveHexagonalCell hr v '' Metric.sphere 0 1 =
      constructedPositiveCentralCell r v \
        (constructedA2CorrectedPositiveHexagonalCell hr v).target := by
  let e := constructedA2CorrectedPositiveHexagonalCell hr v
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    constructor
    · exact constructedA2CorrectedPositiveHexagonalCell_mapsTo_boundary hr v hx
    · intro htarget
      change constructedA2CorrectedPositiveHexagonMap hr v x ∈ e.target at htarget
      rcases htarget with ⟨y, hy, hxy⟩
      have hxclosed := Metric.sphere_subset_closedBall hx
      have hyclosed := Metric.ball_subset_closedBall hy
      have heq := constructedA2CorrectedPositiveHexagonMap_injOn_closedBall hr v
        hxclosed hyclosed hxy.symm
      have hlt : dist x 0 < 1 := by
        rw [heq]
        exact Metric.mem_ball.mp hy
      linarith [Metric.mem_sphere.mp hx]
  · rintro ⟨hqcell, hqtarget⟩
    obtain ⟨x, hxclosed, hxq⟩ :=
      Set.ext_iff.mp (constructedA2CorrectedPositiveHexagonalCell_closedBall_image hr v) q
        |>.mpr hqcell
    have hxnot : x ∉ Metric.ball 0 1 := by
      intro hx
      apply hqtarget
      change q ∈ constructedA2CorrectedPositiveHexagonMap hr v '' Metric.ball 0 1
      exact ⟨x, hx, hxq⟩
    have hxsphere : x ∈ Metric.sphere 0 1 := by
      rw [← Metric.closedBall_sdiff_ball]
      exact ⟨hxclosed, hxnot⟩
    exact ⟨x, hxsphere, hxq⟩

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end
