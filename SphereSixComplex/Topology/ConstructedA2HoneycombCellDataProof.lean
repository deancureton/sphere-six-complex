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
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

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

/-! ## Explicit positive toric charts of one central cell -/

/-- The compact square used in each of the six positive affine charts around a central ray. -/
public abbrev ConstructedA2CellSquare :=
  {p : Fin 2 → ℝ // ∀ i, p i ∈ Set.Icc (0 : ℝ) 1}

/-- The six maximal cones around the central ray `v`, in cyclic order. -/
public def constructedA2CellChart (v : ToricLattice) : Fin 6 → ChartIndex :=
  ![(false, v), (true, v - e₁), (false, v - e₁),
    (true, v - e₁ - e₂), (false, v - e₂), (true, v - e₂)]

/-- The affine coordinate which vanishes on the component indexed by `v`. -/
public def constructedA2CellZeroCoordinate : Fin 6 → Fin 3 :=
  ![0, 0, 1, 2, 2, 1]

public theorem constructedA2CellChart_zeroRay (v : ToricLattice) (i : Fin 6) :
    a2Triangle (constructedA2CellChart v i).1 (constructedA2CellChart v i).2
      (constructedA2CellZeroCoordinate i) = v := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [constructedA2CellChart, constructedA2CellZeroCoordinate,
      a2Triangle, e₁, e₂, sub_eq_add_neg] <;> rfl

/-- Every affine chart containing the ray `v` is one of the six cyclic charts above. -/
public theorem constructedA2CellChart_surjective (v : ToricLattice) :
    Function.Surjective (fun i ↦ ⟨constructedA2CellChart v i,
      ⟨constructedA2CellZeroCoordinate i, constructedA2CellChart_zeroRay v i⟩⟩ :
      Fin 6 → {a : ChartIndex // v ∈ Set.range (a2Triangle a.1 a.2)}) := by
  rintro ⟨⟨upper, w⟩, j, hj⟩
  cases upper <;> fin_cases j
  · refine ⟨0, ?_⟩
    apply Subtype.ext
    simpa [constructedA2CellChart, chartAtCentralRay] using congrArg Prod.snd
      (chart_eq_chartAtCentralRay_of_vertex v (false, w) 0 hj).symm
  · refine ⟨2, ?_⟩
    apply Subtype.ext
    simpa [constructedA2CellChart, chartAtCentralRay] using congrArg Prod.snd
      (chart_eq_chartAtCentralRay_of_vertex v (false, w) 1 hj).symm
  · refine ⟨4, ?_⟩
    apply Subtype.ext
    simpa [constructedA2CellChart, chartAtCentralRay] using congrArg Prod.snd
      (chart_eq_chartAtCentralRay_of_vertex v (false, w) 2 hj).symm
  · refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa [constructedA2CellChart, chartAtCentralRay] using congrArg Prod.snd
      (chart_eq_chartAtCentralRay_of_vertex v (true, w) 0 hj).symm
  · refine ⟨5, ?_⟩
    apply Subtype.ext
    simpa [constructedA2CellChart, chartAtCentralRay] using congrArg Prod.snd
      (chart_eq_chartAtCentralRay_of_vertex v (true, w) 1 hj).symm
  · refine ⟨3, ?_⟩
    apply Subtype.ext
    simpa [constructedA2CellChart, chartAtCentralRay] using congrArg Prod.snd
      (chart_eq_chartAtCentralRay_of_vertex v (true, w) 2 hj).symm

/-- Coordinate order which makes consecutive positive charts use the same square convention. -/
public def constructedA2OrientedCoordinates (i : Fin 6) (z : Fin 2 → ℂ) : Fin 2 → ℂ :=
  if i = 1 ∨ i = 2 ∨ i = 3 then ![z 1, z 0] else z

@[simp]
public theorem constructedA2OrientedCoordinates_involutive (i : Fin 6) (z : Fin 2 → ℂ) :
    constructedA2OrientedCoordinates i (constructedA2OrientedCoordinates i z) = z := by
  by_cases hi : i = 1 ∨ i = 2 ∨ i = 3
  · funext j
    fin_cases j <;> simp [constructedA2OrientedCoordinates, hi]
  · simp [constructedA2OrientedCoordinates, hi]

public theorem constructedA2OrientedCoordinates_continuous (i : Fin 6) :
    Continuous (constructedA2OrientedCoordinates i) := by
  unfold constructedA2OrientedCoordinates
  split_ifs
  · fun_prop
  · exact continuous_id

/-- The two free affine coordinates, with a zero inserted at the component coordinate. -/
public def constructedA2CellLiftCoordinates (i : Fin 6) (z : Fin 2 → ℂ) : RawCoordinates :=
  ![![0, z 0, z 1], ![0, z 1, z 0], ![z 1, 0, z 0],
    ![z 1, z 0, 0], ![z 0, z 1, 0], ![z 0, 0, z 1]] i

@[simp]
public theorem constructedA2CellLiftCoordinates_zero (i : Fin 6) (z : Fin 2 → ℂ) :
    constructedA2CellLiftCoordinates i z (constructedA2CellZeroCoordinate i) = 0 := by
  fin_cases i <;> rfl

public theorem constructedA2CellLiftCoordinates_table (i : Fin 6) (z : Fin 2 → ℂ) :
    constructedA2CellLiftCoordinates i z =
      ![![0, z 0, z 1], ![0, z 1, z 0], ![z 1, 0, z 0],
        ![z 1, z 0, 0], ![z 0, z 1, 0], ![z 0, 0, z 1]] i := by
  rfl

public theorem constructedA2CellLiftCoordinates_continuous (i : Fin 6) :
    Continuous (constructedA2CellLiftCoordinates i) := by
  fin_cases i <;> unfold constructedA2CellLiftCoordinates <;> fun_prop

/-- Remove the vanishing component coordinate, inverse to the cyclic lift convention. -/
public def constructedA2CellRemoveCoordinates (i : Fin 6) (z : RawCoordinates) : Fin 2 → ℂ :=
  ![![z 1, z 2], ![z 2, z 1], ![z 2, z 0],
    ![z 1, z 0], ![z 0, z 1], ![z 0, z 2]] i

/-- The original affine-coordinate index selected by a free square coordinate. -/
public def constructedA2CellRemoveIndex (i : Fin 6) : Fin 2 → Fin 3 :=
  ![![1, 2], ![2, 1], ![2, 0], ![1, 0], ![0, 1], ![0, 2]] i

@[simp]
public theorem constructedA2CellRemoveCoordinates_apply (i : Fin 6)
    (z : RawCoordinates) (k : Fin 2) :
    constructedA2CellRemoveCoordinates i z k = z (constructedA2CellRemoveIndex i k) := by
  fin_cases i <;> fin_cases k <;> rfl

@[simp]
public theorem constructedA2CellRemoveCoordinates_lift (i : Fin 6) (z : Fin 2 → ℂ) :
    constructedA2CellRemoveCoordinates i (constructedA2CellLiftCoordinates i z) = z := by
  fin_cases i <;> ext j <;> fin_cases j <;> rfl

public theorem constructedA2CellLiftCoordinates_remove (i : Fin 6) (z : RawCoordinates)
    (hz : z (constructedA2CellZeroCoordinate i) = 0) :
    constructedA2CellLiftCoordinates i (constructedA2CellRemoveCoordinates i z) = z := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [constructedA2CellLiftCoordinates, constructedA2CellRemoveCoordinates,
      constructedA2CellZeroCoordinate] at hz ⊢ <;> simpa using hz.symm

/-- The carrier point represented by one positive square chart. -/
public def constructedA2CellSquareCarrierPoint
    (v : ToricLattice) (i : Fin 6) (p : ConstructedA2CellSquare) : Carrier :=
  inclusion (constructedA2CellChart v i)
    (constructedA2CellLiftCoordinates i fun k ↦ (p.1 k : ℂ))

public theorem constructedA2CellSquareCarrierPoint_continuous (v : ToricLattice) (i : Fin 6) :
    Continuous (constructedA2CellSquareCarrierPoint v i) := by
  exact (inclusion_isOpenEmbedding (constructedA2CellChart v i)).continuous.comp
    ((constructedA2CellLiftCoordinates_continuous i).comp
      (continuous_pi fun k ↦ Complex.continuous_ofReal.comp
        ((continuous_apply k).comp continuous_subtype_val)))

public theorem constructedA2CellSquareCarrierPoint_mem_component
    (v : ToricLattice) (i : Fin 6) (p : ConstructedA2CellSquare) :
    constructedA2CellSquareCarrierPoint v i p ∈ carrierCentralComponent v := by
  exact ⟨constructedA2CellChart v i, constructedA2CellZeroCoordinate i,
    constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)),
    constructedA2CellChart_zeroRay v i,
    constructedA2CellLiftCoordinates_zero i _, rfl⟩

public theorem constructedA2CellSquareCarrierPoint_mem_positive
    (v : ToricLattice) (i : Fin 6) (p : ConstructedA2CellSquare) :
    constructedA2CellSquareCarrierPoint v i p ∈ carrierPositivePart := by
  rw [constructedA2CellSquareCarrierPoint, inclusion_mem_carrierPositivePart_iff]
  refine ⟨fun j ↦ (constructedA2CellLiftCoordinates i
      (fun k ↦ (p.1 k : ℂ)) j).re, ?_, ?_⟩
  · intro j
    fin_cases i <;> fin_cases j <;>
      simp [constructedA2CellLiftCoordinates_table] <;> exact (p.2 _).1
  · funext j
    fin_cases i <;> fin_cases j <;>
      simp [constructedA2CellLiftCoordinates_table]

public theorem constructedA2CellSquareCarrierPoint_height
    (v : ToricLattice) (i : Fin 6) (p : ConstructedA2CellSquare) :
    carrierHeight (constructedA2CellSquareCarrierPoint v i p) = 0 := by
  rw [constructedA2CellSquareCarrierPoint, carrierHeight_inclusion, rawHeight_eq_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (constructedA2CellZeroCoordinate i))
  exact constructedA2CellLiftCoordinates_zero i _

/-- A square chart as a point of the local positive central cell. -/
public def constructedA2CellSquarePoint {r : ℝ} (hr : 0 < r)
    (v : ToricLattice) (i : Fin 6) (p : ConstructedA2CellSquare) :
    constructedPositiveCentralCell r v := by
  let x := constructedA2CellSquareCarrierPoint v i p
  let q : LocalCarrier constructedModel r := ⟨x, by
    change carrierHeight x ∈ Metric.ball 0 r
    rw [constructedA2CellSquareCarrierPoint_height]
    exact Metric.mem_ball_self hr⟩
  let qpos : constructedLocalPositivePart r := ⟨q,
    (mem_constructedLocalPositivePart_iff r q).mpr
      (constructedA2CellSquareCarrierPoint_mem_positive v i p)⟩
  exact ⟨⟨qpos, by
      change carrierHeight x = 0
      exact constructedA2CellSquareCarrierPoint_height v i p⟩,
    constructedA2CellSquareCarrierPoint_mem_component v i p⟩

public theorem constructedA2CellSquarePoint_continuous {r : ℝ} (hr : 0 < r)
    (v : ToricLattice) (i : Fin 6) :
    Continuous (constructedA2CellSquarePoint hr v i) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact constructedA2CellSquareCarrierPoint_continuous v i

public theorem constructedA2CellSquare_isCompact :
    IsCompact {p : Fin 2 → ℝ | ∀ i, p i ∈ Set.Icc (0 : ℝ) 1} :=
  isCompact_pi_infinite fun _ ↦ CompactIccSpace.isCompact_Icc

public instance constructedA2CellSquare_compactSpace : CompactSpace ConstructedA2CellSquare :=
  isCompact_iff_compactSpace.mp constructedA2CellSquare_isCompact

/-- The six compact positive affine charts projected onto one central toric cell. -/
public def constructedA2CellSquareProjection {r : ℝ} (hr : 0 < r) (v : ToricLattice) :
    Fin 6 × ConstructedA2CellSquare → constructedPositiveCentralCell r v :=
  fun p ↦ constructedA2CellSquarePoint hr v p.1 p.2

public theorem constructedA2CellSquareProjection_continuous {r : ℝ} (hr : 0 < r)
    (v : ToricLattice) : Continuous (constructedA2CellSquareProjection hr v) :=
  continuous_prod_of_discrete_left.mpr (constructedA2CellSquarePoint_continuous hr v)

/-- The six unit positive charts cover the whole positive central cell. -/
public theorem constructedA2CellSquareProjection_surjective {r : ℝ} (hr : 0 < r)
    (v : ToricLattice) : Function.Surjective (constructedA2CellSquareProjection hr v) := by
  intro q
  let x : Carrier := q.1.1.1.1
  have hxzero : carrierHeight x = 0 := by
    exact q.1.property
  obtain ⟨a, ha⟩ := carrierCentralFiber_unitPolydisc_cover x hxzero
  have hav : v ∈ Set.range (a2Triangle a.1 a.2) := by
    by_contra hnot
    exact Set.disjoint_left.mp
      (otherCarrierCentralComponent_disjoint_chart a v hnot) q.property ha.1
  obtain ⟨i, hi⟩ := constructedA2CellChart_surjective v ⟨a, hav⟩
  have haeq : constructedA2CellChart v i = a := congrArg Subtype.val hi
  subst a
  change x ∈ (toricChart (constructedA2CellChart v i)).source ∧
    (∀ j, ‖toricChart (constructedA2CellChart v i) x j‖ ≤ 1) at ha
  rw [toricChart_source] at ha
  obtain ⟨z, hzx⟩ := ha.1
  have hzpos : inclusion (constructedA2CellChart v i) z ∈ carrierPositivePart := by
    rw [hzx]
    exact (mem_constructedLocalPositivePart_iff r q.1.1).mp q.1.1.property
  obtain ⟨u, hu, hzu⟩ :=
    (inclusion_mem_carrierPositivePart_iff (constructedA2CellChart v i) z).mp hzpos
  have hxcomponent : x ∈ carrierCentralComponent v := q.property
  have hzzero : z (constructedA2CellZeroCoordinate i) = 0 := by
    have hcomponent := (carrierCentralComponent_in_chart
      (constructedA2CellChart v i) (constructedA2CellZeroCoordinate i)
      (inclusion (constructedA2CellChart v i) z) (by
        rw [toricChart_source]
        exact Set.mem_range_self z)).mp
      (by
        rw [hzx]
        simpa only [constructedA2CellChart_zeroRay] using hxcomponent)
    rw [toricChart_inclusion] at hcomponent
    simpa [rawToComplexModel] using hcomponent
  let p : ConstructedA2CellSquare :=
    ⟨fun k ↦ (constructedA2CellRemoveCoordinates i z k).re, by
      intro k
      constructor
      · have hnonneg := hu (constructedA2CellRemoveIndex i k)
        simpa [hzu] using hnonneg
      · have hbound := ha.2 (constructedA2CellRemoveIndex i k)
        rw [← hzx, toricChart_inclusion] at hbound
        have hbound' : |u (constructedA2CellRemoveIndex i k)| ≤ 1 := by
          simpa [rawToComplexModel, hzu, Complex.norm_real] using hbound
        simpa [hzu] using (abs_le.mp hbound').2⟩
  have hp : (fun k ↦ (p.1 k : ℂ)) = constructedA2CellRemoveCoordinates i z := by
    funext k
    change ((constructedA2CellRemoveCoordinates i z k).re : ℂ) =
      constructedA2CellRemoveCoordinates i z k
    rw [hzu]
    simp
  refine ⟨(i, p), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change inclusion (constructedA2CellChart v i)
      (constructedA2CellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
    x
  rw [← hzx]
  congr 1
  rw [hp]
  rw [constructedA2CellLiftCoordinates_remove i z hzzero]

/-! ## A finite quotient model for the planar hexagon -/

/-- The six vertices of the axial Voronoi hexagon, relative to its lattice centre. -/
public def constructedA2PlaneVertexOffset : Fin 6 → Fin 2 → ℝ :=
  ![![2 / 3, 0], ![2 / 3, 2 / 3], ![0, 2 / 3],
    ![-2 / 3, 0], ![-2 / 3, -2 / 3], ![0, -2 / 3]]

/-- The midpoint of the edge ending at the indicated cyclic vertex. -/
public def constructedA2PlaneMidpointOffset (i : Fin 6) : Fin 2 → ℝ :=
  ![![1 / 3, -1 / 3], ![2 / 3, 1 / 3], ![1 / 3, 2 / 3],
    ![-1 / 3, 1 / 3], ![-2 / 3, -1 / 3], ![-1 / 3, -2 / 3]] i

/-- The midpoint of the following edge in cyclic order. -/
public def constructedA2PlaneNextMidpointOffset (i : Fin 6) : Fin 2 → ℝ :=
  ![![2 / 3, 1 / 3], ![1 / 3, 2 / 3], ![-1 / 3, 1 / 3],
    ![-2 / 3, -1 / 3], ![-1 / 3, -2 / 3], ![1 / 3, -1 / 3]] i

public def constructedA2CellNextIndex : Fin 6 → Fin 6 := ![1, 2, 3, 4, 5, 0]

public def constructedA2PlaneNextVertexOffset : Fin 6 → Fin 2 → ℝ :=
  ![![2 / 3, 2 / 3], ![0, 2 / 3], ![-2 / 3, 0],
    ![-2 / 3, -2 / 3], ![0, -2 / 3], ![2 / 3, 0]]

/-- The standard square parametrization of one of the six triangular sectors of a cell. -/
public def constructedA2PlaneTile (v : ToricLattice) (i : Fin 6)
    (p : ConstructedA2CellSquare) : Fin 2 → ℝ :=
  (fun k ↦ (v k : ℝ)) +
    ((1 - max (p.1 0) (p.1 1)) • constructedA2PlaneVertexOffset i +
      max (p.1 1 - p.1 0) 0 • constructedA2PlaneMidpointOffset i +
      max (p.1 0 - p.1 1) 0 • constructedA2PlaneNextMidpointOffset i)

public theorem constructedA2PlaneTile_continuous (v : ToricLattice) (i : Fin 6) :
    Continuous (constructedA2PlaneTile v i) := by
  have h0 : Continuous (fun p : ConstructedA2CellSquare ↦ p.1 0) :=
    (continuous_apply 0).comp continuous_subtype_val
  have h1 : Continuous (fun p : ConstructedA2CellSquare ↦ p.1 1) :=
    (continuous_apply 1).comp continuous_subtype_val
  exact continuous_const.add
    ((((continuous_const.sub (h0.max h1)).smul continuous_const).add
      (((h1.sub h0).max continuous_const).smul continuous_const)).add
      (((h0.sub h1).max continuous_const).smul continuous_const))

public theorem constructedA2PlaneTile_of_le (v : ToricLattice) (i : Fin 6)
    (p : ConstructedA2CellSquare) (hp : p.1 0 ≤ p.1 1) :
    constructedA2PlaneTile v i p =
      (fun k ↦ (v k : ℝ)) + ((1 - p.1 1) • constructedA2PlaneVertexOffset i +
        (p.1 1 - p.1 0) • constructedA2PlaneMidpointOffset i) := by
  simp [constructedA2PlaneTile, max_eq_right hp, max_eq_left (sub_nonneg.mpr hp),
    max_eq_right (sub_nonpos.mpr hp)]

public theorem constructedA2PlaneTile_of_ge (v : ToricLattice) (i : Fin 6)
    (p : ConstructedA2CellSquare) (hp : p.1 1 ≤ p.1 0) :
    constructedA2PlaneTile v i p =
      (fun k ↦ (v k : ℝ)) + ((1 - p.1 0) • constructedA2PlaneVertexOffset i +
        (p.1 0 - p.1 1) • constructedA2PlaneNextMidpointOffset i) := by
  simp [constructedA2PlaneTile, max_eq_left hp, max_eq_right (sub_nonpos.mpr hp),
    max_eq_left (sub_nonneg.mpr hp)]

public theorem constructedA2PlaneTile_mem (v : ToricLattice) (i : Fin 6)
    (p : ConstructedA2CellSquare) :
    constructedA2PlaneTile v i p ∈ constructedA2PlaneCell v := by
  have hp0 := p.2 0
  have hp1 := p.2 1
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · rw [constructedA2PlaneTile_of_le v i p hp]
    fin_cases i <;>
      simp only [constructedA2PlaneCell, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset]
    all_goals
      constructor
      · apply abs_le.mpr
        constructor <;> norm_num <;> linarith [hp0.1, hp0.2, hp1.1, hp1.2]
      constructor
      · apply abs_le.mpr
        constructor <;> norm_num <;> linarith [hp0.1, hp0.2, hp1.1, hp1.2]
      · apply abs_le.mpr
        constructor <;> norm_num <;> linarith [hp0.1, hp0.2, hp1.1, hp1.2]
  · rw [constructedA2PlaneTile_of_ge v i p hp]
    fin_cases i <;>
      simp only [constructedA2PlaneCell, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, constructedA2PlaneVertexOffset, constructedA2PlaneNextMidpointOffset]
    all_goals
      constructor
      · apply abs_le.mpr
        constructor <;> norm_num <;> linarith [hp0.1, hp0.2, hp1.1, hp1.2]
      constructor
      · apply abs_le.mpr
        constructor <;> norm_num <;> linarith [hp0.1, hp0.2, hp1.1, hp1.2]
      · apply abs_le.mpr
        constructor <;> norm_num <;> linarith [hp0.1, hp0.2, hp1.1, hp1.2]

@[simp]
public theorem constructedA2PlaneVertexOffset_nextIndex (i : Fin 6) :
    constructedA2PlaneVertexOffset (constructedA2CellNextIndex i) =
      constructedA2PlaneNextVertexOffset i := by
  fin_cases i <;> rfl

@[simp]
public theorem constructedA2PlaneMidpointOffset_nextIndex (i : Fin 6) :
    constructedA2PlaneMidpointOffset (constructedA2CellNextIndex i) =
      constructedA2PlaneNextMidpointOffset i := by
  fin_cases i <;> rfl

public theorem constructedA2PlaneNextMidpointOffset_eq (i : Fin 6) :
    constructedA2PlaneNextMidpointOffset i =
      (1 / 2 : ℝ) • (constructedA2PlaneVertexOffset i +
        constructedA2PlaneNextVertexOffset i) := by
  fin_cases i <;> ext k <;> fin_cases k <;>
    norm_num [constructedA2PlaneNextMidpointOffset, constructedA2PlaneVertexOffset,
      constructedA2PlaneNextVertexOffset]

public theorem exists_constructedA2PlaneTile_of_sector (v : ToricLattice)
    (i : Fin 6) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β ≤ 1) :
    ∃ j p, constructedA2PlaneTile v j p =
      (fun k ↦ (v k : ℝ)) +
        (α • constructedA2PlaneVertexOffset i +
          β • constructedA2PlaneNextVertexOffset i) := by
  rcases le_total β α with hβα | hαβ'
  · let p : ConstructedA2CellSquare :=
      ⟨![1 - α + β, 1 - α - β], by
        intro k
        fin_cases k
        · change 0 ≤ 1 - α + β ∧ 1 - α + β ≤ 1
          constructor <;> linarith
        · change 0 ≤ 1 - α - β ∧ 1 - α - β ≤ 1
          constructor <;> linarith⟩
    have hp : p.1 1 ≤ p.1 0 := by
      change 1 - α - β ≤ 1 - α + β
      linarith
    refine ⟨i, p, ?_⟩
    rw [constructedA2PlaneTile_of_ge v i p hp,
      constructedA2PlaneNextMidpointOffset_eq]
    ext k
    simp only [p, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  · let p : ConstructedA2CellSquare :=
      ⟨![1 - α - β, 1 + α - β], by
        intro k
        fin_cases k
        · change 0 ≤ 1 - α - β ∧ 1 - α - β ≤ 1
          constructor <;> linarith
        · change 0 ≤ 1 + α - β ∧ 1 + α - β ≤ 1
          constructor <;> linarith⟩
    have hp : p.1 0 ≤ p.1 1 := by
      change 1 - α - β ≤ 1 + α - β
      linarith
    refine ⟨constructedA2CellNextIndex i, p, ?_⟩
    rw [constructedA2PlaneTile_of_le v (constructedA2CellNextIndex i) p hp,
      constructedA2PlaneVertexOffset_nextIndex, constructedA2PlaneMidpointOffset_nextIndex,
      constructedA2PlaneNextMidpointOffset_eq]
    ext k
    simp only [p, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring

/-- The six planar square sectors projected onto their explicit axial hexagon. -/
public def constructedA2PlaneSquareProjection (v : ToricLattice) :
    Fin 6 × ConstructedA2CellSquare → constructedA2PlaneCell v :=
  fun a ↦ ⟨constructedA2PlaneTile v a.1 a.2, constructedA2PlaneTile_mem v a.1 a.2⟩

public theorem constructedA2PlaneSquareProjection_surjective (v : ToricLattice) :
    Function.Surjective (constructedA2PlaneSquareProjection v) := by
  intro x
  let dx : ℝ := x.1 0 - (v 0 : ℝ)
  let dy : ℝ := x.1 1 - (v 1 : ℝ)
  have hx0 : |dx| ≤ 2 / 3 := by simpa [dx] using x.2.1
  have hx1 : |dy| ≤ 2 / 3 := by simpa [dy] using x.2.2.1
  have hxd : |dx - dy| ≤ 2 / 3 := by
    simpa [dx, dy, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using x.2.2.2
  have hsector (i : Fin 6) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
      (hαβ : α + β ≤ 1)
      (hx : x.1 = (fun k ↦ (v k : ℝ)) +
        (α • constructedA2PlaneVertexOffset i +
          β • constructedA2PlaneNextVertexOffset i)) :
      ∃ a, constructedA2PlaneSquareProjection v a = x := by
    obtain ⟨j, p, hp⟩ :=
      exists_constructedA2PlaneTile_of_sector v i α β hα hβ hαβ
    refine ⟨(j, p), Subtype.ext ?_⟩
    exact hp.trans hx.symm
  by_cases hdx : 0 ≤ dx
  · by_cases hdy : 0 ≤ dy
    · rcases le_total dy dx with hdyx | hxdy
      · apply hsector 0 ((3 / 2 : ℝ) * (dx - dy)) ((3 / 2 : ℝ) * dy)
        · positivity
        · positivity
        · have := (abs_le.mp hx0).2
          linarith
        · ext k
          fin_cases k <;>
            simp [dx, dy, constructedA2PlaneVertexOffset,
              constructedA2PlaneNextVertexOffset] <;> ring
      · apply hsector 1 ((3 / 2 : ℝ) * dx) ((3 / 2 : ℝ) * (dy - dx))
        · positivity
        · positivity
        · have := (abs_le.mp hx1).2
          linarith
        · ext k
          fin_cases k <;>
            simp [dx, dy, constructedA2PlaneVertexOffset,
              constructedA2PlaneNextVertexOffset] <;> ring
    · have hdy' : dy ≤ 0 := le_of_not_ge hdy
      apply hsector 5 (-(3 / 2 : ℝ) * dy) ((3 / 2 : ℝ) * dx)
      · nlinarith
      · positivity
      · have := (abs_le.mp hxd).2
        linarith
      · ext k
        fin_cases k <;>
          simp [dx, dy, constructedA2PlaneVertexOffset,
            constructedA2PlaneNextVertexOffset] <;> ring
  · have hdx' : dx ≤ 0 := le_of_not_ge hdx
    by_cases hdy : 0 ≤ dy
    · apply hsector 2 ((3 / 2 : ℝ) * dy) (-(3 / 2 : ℝ) * dx)
      · positivity
      · nlinarith
      · have := (abs_le.mp hxd).1
        linarith
      · ext k
        fin_cases k <;>
          simp [dx, dy, constructedA2PlaneVertexOffset,
            constructedA2PlaneNextVertexOffset] <;> ring
    · have hdy' : dy ≤ 0 := le_of_not_ge hdy
      rcases le_total dx dy with hxdy | hdyx
      · apply hsector 3 ((3 / 2 : ℝ) * (dy - dx)) (-(3 / 2 : ℝ) * dy)
        · positivity
        · nlinarith
        · have := (abs_le.mp hx0).1
          linarith
        · ext k
          fin_cases k <;>
            simp [dx, dy, constructedA2PlaneVertexOffset,
              constructedA2PlaneNextVertexOffset] <;> ring
      · apply hsector 4 (-(3 / 2 : ℝ) * dx) ((3 / 2 : ℝ) * (dx - dy))
        · nlinarith
        · positivity
        · have := (abs_le.mp hx1).1
          linarith
        · ext k
          fin_cases k <;>
            simp [dx, dy, constructedA2PlaneVertexOffset,
              constructedA2PlaneNextVertexOffset] <;> ring

public theorem constructedA2PlaneSquareProjection_continuous (v : ToricLattice) :
    Continuous (constructedA2PlaneSquareProjection v) :=
  (continuous_prod_of_discrete_left.mpr (constructedA2PlaneTile_continuous v)).subtype_mk _

public theorem constructedA2CellSquareProjection_isQuotientMap {r : ℝ} (hr : 0 < r)
    (v : ToricLattice) : Topology.IsQuotientMap (constructedA2CellSquareProjection hr v) :=
  Topology.IsQuotientMap.of_surjective_continuous
    (constructedA2CellSquareProjection_surjective hr v)
    (constructedA2CellSquareProjection_continuous hr v)

/-- Quotient maps out of a common space with identical fibres have homeomorphic targets. -/
public noncomputable def constructedA2HomeomorphOfQuotientMaps
    {W A B : Type*} [TopologicalSpace W] [TopologicalSpace A] [TopologicalSpace B]
    {f : W → A} {g : W → B} (hf : Topology.IsQuotientMap f)
    (hg : Topology.IsQuotientMap g) (hfg : ∀ x y, f x = f y ↔ g x = g y) : A ≃ₜ B := by
  let F := LocallyFiniteClosedCover.descend f g hf.surjective
  let E : A ≃ B := Equiv.ofBijective F
    ⟨LocallyFiniteClosedCover.descend_injective f g hf.surjective
      (fun x y h ↦ (hfg x y).mpr h),
      LocallyFiniteClosedCover.descend_surjective f g hf.surjective
        (fun x y h ↦ (hfg x y).mp h) hg.surjective⟩
  refine
    { toEquiv := E
      continuous_toFun :=
        LocallyFiniteClosedCover.descend_continuous f g hf.surjective hf hg.continuous
          (fun x y h ↦ (hfg x y).mp h)
      continuous_invFun := ?_ }
  apply hg.continuous_iff.mpr
  change Continuous (E.symm ∘ g)
  have hcomp : E.symm ∘ g = f := by
    funext x
    apply E.injective
    change E (E.symm (g x)) = E (f x)
    rw [E.apply_symm_apply]
    exact (LocallyFiniteClosedCover.descend_apply f g hf.surjective
      (fun x y h ↦ (hfg x y).mp h) x).symm
  rw [hcomp]
  exact hf.continuous

public theorem constructedA2HomeomorphOfQuotientMaps_apply
    {W A B : Type*} [TopologicalSpace W] [TopologicalSpace A] [TopologicalSpace B]
    {f : W → A} {g : W → B} (hf : Topology.IsQuotientMap f)
    (hg : Topology.IsQuotientMap g) (hfg : ∀ x y, f x = f y ↔ g x = g y)
    (x : W) : constructedA2HomeomorphOfQuotientMaps hf hg hfg (f x) = g x :=
  (hfg _ _).mp (Function.surjInv_eq hf.surjective (f x))

/-- The remaining finite calculation: the explicit planar and toric square maps have the same
fibres across all cells. -/
public structure ConstructedA2HoneycombFiniteQuotientResidual (r : ℝ) (hr : 0 < r) where
  sameFibres : ∀ v w a b,
    (constructedA2PlaneSquareProjection v a : Fin 2 → ℝ) =
        constructedA2PlaneSquareProjection w b ↔
      ((constructedA2CellSquareProjection hr v a :
          constructedPositiveCentralCell r v) : constructedPositiveCentralFiber r) =
        constructedA2CellSquareProjection hr w b

public theorem constructedA2PlaneSquareProjection_isQuotientMap (v : ToricLattice) :
    Topology.IsQuotientMap (constructedA2PlaneSquareProjection v) :=
  Topology.IsQuotientMap.of_surjective_continuous
    (constructedA2PlaneSquareProjection_surjective v)
    (constructedA2PlaneSquareProjection_continuous v)

/-- The actual cell homeomorphism obtained from the common finite quotient. -/
public noncomputable def constructedA2FiniteQuotientCellHomeomorph
    {r : ℝ} (hr : 0 < r) (H : ConstructedA2HoneycombFiniteQuotientResidual r hr)
    (v : ToricLattice) :
    constructedA2PlaneCell v ≃ₜ constructedPositiveCentralCell r v :=
  constructedA2HomeomorphOfQuotientMaps
    (constructedA2PlaneSquareProjection_isQuotientMap v)
    (constructedA2CellSquareProjection_isQuotientMap hr v)
    (fun a b ↦ by simpa only [Subtype.ext_iff] using H.sameFibres v v a b)

public theorem constructedA2FiniteQuotientCellHomeomorph_apply
    {r : ℝ} (hr : 0 < r) (H : ConstructedA2HoneycombFiniteQuotientResidual r hr)
    (v : ToricLattice) (a : Fin 6 × ConstructedA2CellSquare) :
    constructedA2FiniteQuotientCellHomeomorph hr H v
        (constructedA2PlaneSquareProjection v a) =
      constructedA2CellSquareProjection hr v a :=
  constructedA2HomeomorphOfQuotientMaps_apply
    (constructedA2PlaneSquareProjection_isQuotientMap v)
    (constructedA2CellSquareProjection_isQuotientMap hr v)
    (fun x y ↦ by simpa only [Subtype.ext_iff] using H.sameFibres v v x y) a

/-- The exact residual after constructing the periodic planar cover: cell charts into the
explicit toric components, with the equality relation preserved on every overlap. -/
public structure ConstructedA2HoneycombCellChartResidual (r : ℝ) where
  cellHomeomorph : ∀ v, constructedA2PlaneCell v ≃ₜ constructedPositiveCentralCell r v
  compatible : ∀ v w (x : constructedA2PlaneCell v) (y : constructedA2PlaneCell w),
    (x : Fin 2 → ℝ) = (y : Fin 2 → ℝ) ↔
      (cellHomeomorph v x : constructedPositiveCentralFiber r) = cellHomeomorph w y

/-- The one finite same-fibres calculation produces both the cell homeomorphisms and their
overlap compatibility. -/
public noncomputable def constructedA2HoneycombCellChartResidualOfFiniteQuotient
    {r : ℝ} (hr : 0 < r) (H : ConstructedA2HoneycombFiniteQuotientResidual r hr) :
    ConstructedA2HoneycombCellChartResidual r where
  cellHomeomorph := constructedA2FiniteQuotientCellHomeomorph hr H
  compatible := by
    intro v w x y
    obtain ⟨a, rfl⟩ := constructedA2PlaneSquareProjection_surjective v x
    obtain ⟨b, rfl⟩ := constructedA2PlaneSquareProjection_surjective w y
    rw [constructedA2FiniteQuotientCellHomeomorph_apply hr H,
      constructedA2FiniteQuotientCellHomeomorph_apply hr H]
    exact H.sameFibres v w a b

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

public theorem constructedA2HoneycombCellData_nonempty_of_finiteQuotient
    {r : ℝ} (hr : 0 < r)
    (H : Nonempty (ConstructedA2HoneycombFiniteQuotientResidual r hr)) :
    Nonempty (ConstructedHoneycombCellData r) :=
  H.map fun h ↦ constructedA2HoneycombCellData
    (constructedA2HoneycombCellChartResidualOfFiniteQuotient hr h)

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end

end
