module

public import SphereSixComplex.Topology.ConstructedNormalizedPolarHoneycombReduction
public import Mathlib.Algebra.Order.Round
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Pi.Interval

/-!
# Periodic planar cells for the constructed A₂ honeycomb

The axial-coordinate Voronoi hexagons give the planar side of the locally finite closed-cover
construction.  The only remaining input is the cellwise toric chart and its overlap
compatibility with these explicit hexagons.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Geometry.CuspCombinatorics

/-- The closed hexagon centred at an integral axial coordinate. -/
public def constructedA2PlaneCell (v : ToricLattice) : Set (Fin 2 → ℝ) :=
  {x | |x 0 - (v 0 : ℝ)| ≤ 2 / 3 ∧
    |x 1 - (v 1 : ℝ)| ≤ 2 / 3 ∧
    |(x 0 - x 1) - ((v 0 : ℝ) - (v 1 : ℝ))| ≤ 2 / 3}

private def constructedA2PlaneBoundingSquare (v : ToricLattice) : Set (Fin 2 → ℝ) :=
  {x | |x 0 - (v 0 : ℝ)| ≤ 2 / 3 ∧ |x 1 - (v 1 : ℝ)| ≤ 2 / 3}

public theorem constructedA2PlaneCell_isClosed (v : ToricLattice) :
    IsClosed (constructedA2PlaneCell v) := by
  apply IsClosed.inter
  · exact isClosed_le ((continuous_apply 0).sub continuous_const).abs continuous_const
  apply IsClosed.inter
  · exact isClosed_le ((continuous_apply 1).sub continuous_const).abs continuous_const
  · exact isClosed_le
      (((continuous_apply 0).sub (continuous_apply 1)).sub continuous_const).abs
      continuous_const

private theorem constructedA2PlaneBoundingSquares_locallyFinite :
    LocallyFinite constructedA2PlaneBoundingSquare := by
  intro x
  let U : Set (Fin 2 → ℝ) := {y | |y 0 - x 0| < 1 ∧ |y 1 - x 1| < 1}
  have hUopen : IsOpen U :=
    (isOpen_lt ((continuous_apply 0).sub continuous_const).abs continuous_const).inter
      (isOpen_lt ((continuous_apply 1).sub continuous_const).abs continuous_const)
  have hxU : x ∈ U := by simp [U]
  let lo : ToricLattice := fun i ↦ round (x i) - 3
  let hi : ToricLattice := fun i ↦ round (x i) + 3
  refine ⟨U, hUopen.mem_nhds hxU, (Set.finite_Icc lo hi).subset ?_⟩
  intro v hv
  obtain ⟨y, hy, hyU⟩ := hv
  have hx0 := abs_le.mp (abs_sub_round (x 0))
  have hx1 := abs_le.mp (abs_sub_round (x 1))
  have hy0 := abs_le.mp hy.1
  have hy1 := abs_le.mp hy.2
  have hU0 := abs_lt.mp hyU.1
  have hU1 := abs_lt.mp hyU.2
  constructor
  · intro i
    fin_cases i
    · change round (x 0) - 3 ≤ v 0
      have hreal : ((round (x 0) - 3 : ℤ) : ℝ) ≤ (v 0 : ℝ) := by
        norm_num only [Int.cast_sub, Int.cast_ofNat]
        linarith [hx0.1, hy0.2, hU0.2]
      exact_mod_cast hreal
    · change round (x 1) - 3 ≤ v 1
      have hreal : ((round (x 1) - 3 : ℤ) : ℝ) ≤ (v 1 : ℝ) := by
        norm_num only [Int.cast_sub, Int.cast_ofNat]
        linarith [hx1.1, hy1.2, hU1.2]
      exact_mod_cast hreal
  · intro i
    fin_cases i
    · change v 0 ≤ round (x 0) + 3
      have hreal : (v 0 : ℝ) ≤ ((round (x 0) + 3 : ℤ) : ℝ) := by
        norm_num only [Int.cast_add, Int.cast_ofNat]
        linarith [hx0.2, hy0.1, hU0.1]
      exact_mod_cast hreal
    · change v 1 ≤ round (x 1) + 3
      have hreal : (v 1 : ℝ) ≤ ((round (x 1) + 3 : ℤ) : ℝ) := by
        norm_num only [Int.cast_add, Int.cast_ofNat]
        linarith [hx1.2, hy1.1, hU1.1]
      exact_mod_cast hreal

public theorem constructedA2PlaneCells_locallyFinite :
    LocallyFinite constructedA2PlaneCell :=
  constructedA2PlaneBoundingSquares_locallyFinite.subset fun _ _ hx ↦ ⟨hx.1, hx.2.1⟩

public theorem iUnion_constructedA2PlaneCell :
    ⋃ v, constructedA2PlaneCell v = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  let a : ℤ := round (x 0)
  let b : ℤ := round (x 1)
  let dx : ℝ := x 0 - a
  let dy : ℝ := x 1 - b
  have hdx : |dx| ≤ 1 / 2 := abs_sub_round (x 0)
  have hdy : |dy| ≤ 1 / 2 := abs_sub_round (x 1)
  have hdxlo : -(1 / 2) ≤ dx := (abs_le.mp hdx).1
  have hdxhi : dx ≤ 1 / 2 := (abs_le.mp hdx).2
  have hdylo : -(1 / 2) ≤ dy := (abs_le.mp hdy).1
  have hdyhi : dy ≤ 1 / 2 := (abs_le.mp hdy).2
  by_cases hhi : dx - dy > 2 / 3
  · have hsplit : 1 / 3 ≤ dx ∨ -dy ≥ 1 / 3 := by
      by_contra h
      simp only [not_or, not_le] at h
      linarith
    rcases hsplit with hdx' | hdy'
    · let v : ToricLattice := fun i ↦ if i = 0 then a + 1 else b
      apply Set.mem_iUnion.mpr
      refine ⟨v, ?_⟩
      have hv0 : v 0 = a + 1 := by simp [v]
      have hv1 : v 1 = b := by simp [v]
      simp only [constructedA2PlaneCell, Set.mem_ofPred_eq]
      rw [hv0, hv1]
      norm_num [dx, dy] at ⊢
      refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩,
        hdy.trans (by norm_num), abs_le.mpr ⟨by linarith, by linarith⟩⟩
    · let v : ToricLattice := fun i ↦ if i = 1 then b - 1 else a
      apply Set.mem_iUnion.mpr
      refine ⟨v, ?_⟩
      have hv0 : v 0 = a := by simp [v]
      have hv1 : v 1 = b - 1 := by simp [v]
      simp only [constructedA2PlaneCell, Set.mem_ofPred_eq]
      rw [hv0, hv1]
      norm_num [dx, dy] at ⊢
      refine ⟨hdx.trans (by norm_num), abs_le.mpr ⟨by linarith, by linarith⟩,
        abs_le.mpr ⟨by linarith, by linarith⟩⟩
  · by_cases hlo : dx - dy < -(2 / 3)
    · have hsplit : -dx ≥ 1 / 3 ∨ dy ≥ 1 / 3 := by
        by_contra h
        simp only [not_or, not_le] at h
        linarith
      rcases hsplit with hdx' | hdy'
      · let v : ToricLattice := fun i ↦ if i = 0 then a - 1 else b
        apply Set.mem_iUnion.mpr
        refine ⟨v, ?_⟩
        have hv0 : v 0 = a - 1 := by simp [v]
        have hv1 : v 1 = b := by simp [v]
        simp only [constructedA2PlaneCell, Set.mem_ofPred_eq]
        rw [hv0, hv1]
        norm_num [dx, dy] at ⊢
        refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩,
          hdy.trans (by norm_num), abs_le.mpr ⟨by linarith, by linarith⟩⟩
      · let v : ToricLattice := fun i ↦ if i = 1 then b + 1 else a
        apply Set.mem_iUnion.mpr
        refine ⟨v, ?_⟩
        have hv0 : v 0 = a := by simp [v]
        have hv1 : v 1 = b + 1 := by simp [v]
        simp only [constructedA2PlaneCell, Set.mem_ofPred_eq]
        rw [hv0, hv1]
        norm_num [dx, dy] at ⊢
        refine ⟨hdx.trans (by norm_num), abs_le.mpr ⟨by linarith, by linarith⟩,
          abs_le.mpr ⟨by linarith, by linarith⟩⟩
    · let v : ToricLattice := fun i ↦ if i = 0 then a else b
      apply Set.mem_iUnion.mpr
      refine ⟨v, ?_⟩
      have hv0 : v 0 = a := by simp [v]
      have hv1 : v 1 = b := by simp [v]
      simp only [constructedA2PlaneCell, Set.mem_ofPred_eq]
      rw [hv0, hv1]
      refine ⟨hdx.trans (by norm_num), hdy.trans (by norm_num), ?_⟩
      rw [show (x 0 - x 1) - ((a : ℝ) - (b : ℝ)) = dx - dy by
        dsimp only [dx, dy]
        ring]
      exact abs_le.mpr ⟨le_of_not_gt hlo, le_of_not_gt hhi⟩

/-- The exact residual after constructing the periodic planar cover: cell charts into the
explicit toric components, with the equality relation preserved on every overlap. -/
public structure ConstructedA2HoneycombCellChartResidual (r : ℝ) where
  cellHomeomorph : ∀ v, constructedA2PlaneCell v ≃ₜ constructedPositiveCentralCell r v
  compatible : ∀ v w (x : constructedA2PlaneCell v) (y : constructedA2PlaneCell w),
    (x : Fin 2 → ℝ) = (y : Fin 2 → ℝ) ↔
      (cellHomeomorph v x : constructedPositiveCentralFiber r) = cellHomeomorph w y

/-- The explicit periodic A₂ planar cover and compatible toric cell charts assemble the
`ConstructedHoneycombCellData` required by the polar-honeycomb construction. -/
public def constructedA2HoneycombCellData
    {r : ℝ} (H : ConstructedA2HoneycombCellChartResidual r) :
    ConstructedHoneycombCellData r where
  planeCell := constructedA2PlaneCell
  planeCell_cover := iUnion_constructedA2PlaneCell
  planeCell_closed := constructedA2PlaneCell_isClosed
  planeCell_locallyFinite := constructedA2PlaneCells_locallyFinite
  cellHomeomorph := H.cellHomeomorph
  cellHomeomorph_compatible := H.compatible

public theorem constructedA2HoneycombCellData_nonempty_of_chartResidual
    {r : ℝ} (H : Nonempty (ConstructedA2HoneycombCellChartResidual r)) :
    Nonempty (ConstructedHoneycombCellData r) :=
  H.map constructedA2HoneycombCellData

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end

end
