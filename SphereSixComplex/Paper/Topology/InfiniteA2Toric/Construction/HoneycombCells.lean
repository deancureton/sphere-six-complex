module

public import SphereSixComplex.Paper.Topology.ConstructedNormalizedPolarHoneycombReduction
public import Mathlib.Algebra.Order.Round
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Pi.Interval
public import SphereSixComplex.Prerequisites.Topology.LocallyFiniteClosedCover

/-!
# Periodic planar cells for the constructed A₂ honeycomb

The axial-coordinate Voronoi hexagons give the planar side of the locally finite closed-cover
construction.  The only remaining input is the cellwise toric chart and its overlap
compatibility with these explicit hexagons.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SphereSixComplex.Geometry.InfiniteA2Toric

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

namespace Construction

/-- The closed hexagon centred at an integral axial coordinate. -/
public def planeCell (v : ToricLattice) : Set (Fin 2 → ℝ) :=
  {x | |x 0 - (v 0 : ℝ)| ≤ 2 / 3 ∧
    |x 1 - (v 1 : ℝ)| ≤ 2 / 3 ∧
    |(x 0 - x 1) - ((v 0 : ℝ) - (v 1 : ℝ))| ≤ 2 / 3}






/-! ## Explicit positive toric charts of one central cell -/

/-- The compact square used in each of the six positive affine charts around a central ray. -/
public abbrev CellSquare :=
  {p : Fin 2 → ℝ // ∀ i, p i ∈ Set.Icc (0 : ℝ) 1}

/-- The six maximal cones around the central ray `v`, in cyclic order. -/
public def cellChart (v : ToricLattice) : Fin 6 → ChartIndex :=
  ![(false, v), (true, v - e₁), (false, v - e₁),
    (true, v - e₁ - e₂), (false, v - e₂), (true, v - e₂)]

/-- The affine coordinate which vanishes on the component indexed by `v`. -/
public def cellZeroCoordinate : Fin 6 → Fin 3 :=
  ![0, 0, 1, 2, 2, 1]

public theorem cellChart_zeroRay (v : ToricLattice) (i : Fin 6) :
    a2Triangle (cellChart v i).1 (cellChart v i).2
      (cellZeroCoordinate i) = v := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [cellChart, cellZeroCoordinate,
      a2Triangle, e₁, e₂, sub_eq_add_neg] <;> rfl

/-- Every affine chart containing the ray `v` is one of the six cyclic charts above. -/
public theorem surjective_cellChart (v : ToricLattice) :
    Function.Surjective (fun i ↦ ⟨cellChart v i,
      ⟨cellZeroCoordinate i, cellChart_zeroRay v i⟩⟩ :
      Fin 6 → {a : ChartIndex // v ∈ Set.range (a2Triangle a.1 a.2)}) := by
  rintro ⟨⟨upper, w⟩, j, hj⟩
  cases upper <;> fin_cases j
  · refine ⟨0, ?_⟩
    apply Subtype.ext
    simpa [cellChart, chartAtCentralRay] using congrArg Prod.snd
      (chart_eq_chartAtCentralRay_of_vertex v (false, w) 0 hj).symm
  · refine ⟨2, ?_⟩
    apply Subtype.ext
    simpa [cellChart, chartAtCentralRay] using congrArg Prod.snd
      (chart_eq_chartAtCentralRay_of_vertex v (false, w) 1 hj).symm
  · refine ⟨4, ?_⟩
    apply Subtype.ext
    simpa [cellChart, chartAtCentralRay] using congrArg Prod.snd
      (chart_eq_chartAtCentralRay_of_vertex v (false, w) 2 hj).symm
  · refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa [cellChart, chartAtCentralRay] using congrArg Prod.snd
      (chart_eq_chartAtCentralRay_of_vertex v (true, w) 0 hj).symm
  · refine ⟨5, ?_⟩
    apply Subtype.ext
    simpa [cellChart, chartAtCentralRay] using congrArg Prod.snd
      (chart_eq_chartAtCentralRay_of_vertex v (true, w) 1 hj).symm
  · refine ⟨3, ?_⟩
    apply Subtype.ext
    simpa [cellChart, chartAtCentralRay] using congrArg Prod.snd
      (chart_eq_chartAtCentralRay_of_vertex v (true, w) 2 hj).symm




/-- The two free affine coordinates, with a zero inserted at the component coordinate. -/
public def cellLiftCoordinates (i : Fin 6) (z : Fin 2 → ℂ) : RawCoordinates :=
  ![![0, z 0, z 1], ![0, z 1, z 0], ![z 1, 0, z 0],
    ![z 1, z 0, 0], ![z 0, z 1, 0], ![z 0, 0, z 1]] i

@[simp]
public theorem cellLiftCoordinates_zero (i : Fin 6) (z : Fin 2 → ℂ) :
    cellLiftCoordinates i z (cellZeroCoordinate i) = 0 := by
  fin_cases i <;> rfl

public theorem cellLiftCoordinates_table (i : Fin 6) (z : Fin 2 → ℂ) :
    cellLiftCoordinates i z =
      ![![0, z 0, z 1], ![0, z 1, z 0], ![z 1, 0, z 0],
        ![z 1, z 0, 0], ![z 0, z 1, 0], ![z 0, 0, z 1]] i := by
  rfl

public theorem continuous_cellLiftCoordinates (i : Fin 6) :
    Continuous (cellLiftCoordinates i) := by
  fin_cases i <;> unfold cellLiftCoordinates <;> fun_prop

/-- Remove the vanishing component coordinate, inverse to the cyclic lift convention. -/
public def cellRemoveCoordinates (i : Fin 6) (z : RawCoordinates) : Fin 2 → ℂ :=
  ![![z 1, z 2], ![z 2, z 1], ![z 2, z 0],
    ![z 1, z 0], ![z 0, z 1], ![z 0, z 2]] i

/-- The original affine-coordinate index selected by a free square coordinate. -/
public def cellRemoveIndex (i : Fin 6) : Fin 2 → Fin 3 :=
  ![![1, 2], ![2, 1], ![2, 0], ![1, 0], ![0, 1], ![0, 2]] i

@[simp]
public theorem cellRemoveCoordinates_apply (i : Fin 6)
    (z : RawCoordinates) (k : Fin 2) :
    cellRemoveCoordinates i z k = z (cellRemoveIndex i k) := by
  fin_cases i <;> fin_cases k <;> rfl

@[simp]
public theorem cellRemoveCoordinates_lift (i : Fin 6) (z : Fin 2 → ℂ) :
    cellRemoveCoordinates i (cellLiftCoordinates i z) = z := by
  fin_cases i <;> ext j <;> fin_cases j <;> rfl

public theorem cellLiftCoordinates_remove (i : Fin 6) (z : RawCoordinates)
    (hz : z (cellZeroCoordinate i) = 0) :
    cellLiftCoordinates i (cellRemoveCoordinates i z) = z := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [cellLiftCoordinates, cellRemoveCoordinates,
      cellZeroCoordinate] at hz ⊢ <;> simpa using hz.symm

/-- The carrier point represented by one positive square chart. -/
public def cellSquareCarrierPoint
    (v : ToricLattice) (i : Fin 6) (p : CellSquare) : Carrier :=
  inclusion (cellChart v i)
    (cellLiftCoordinates i fun k ↦ (p.1 k : ℂ))

public theorem continuous_cellSquareCarrierPoint (v : ToricLattice) (i : Fin 6) :
    Continuous (cellSquareCarrierPoint v i) := by
  exact (inclusion_isOpenEmbedding (cellChart v i)).continuous.comp
    ((continuous_cellLiftCoordinates i).comp
      (continuous_pi fun k ↦ Complex.continuous_ofReal.comp
        ((continuous_apply k).comp continuous_subtype_val)))

public theorem cellSquareCarrierPoint_mem_component
    (v : ToricLattice) (i : Fin 6) (p : CellSquare) :
    cellSquareCarrierPoint v i p ∈ carrierCentralComponent v := by
  exact ⟨cellChart v i, cellZeroCoordinate i,
    cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ)),
    cellChart_zeroRay v i,
    cellLiftCoordinates_zero i _, rfl⟩

public theorem cellSquareCarrierPoint_mem_positive
    (v : ToricLattice) (i : Fin 6) (p : CellSquare) :
    cellSquareCarrierPoint v i p ∈ carrierPositivePart := by
  rw [cellSquareCarrierPoint, inclusion_mem_carrierPositivePart_iff]
  refine ⟨fun j ↦ (cellLiftCoordinates i
      (fun k ↦ (p.1 k : ℂ)) j).re, ?_, ?_⟩
  · intro j
    fin_cases i <;> fin_cases j <;>
      simp [cellLiftCoordinates_table] <;> exact (p.2 _).1
  · funext j
    fin_cases i <;> fin_cases j <;>
      simp [cellLiftCoordinates_table]

public theorem cellSquareCarrierPoint_height
    (v : ToricLattice) (i : Fin 6) (p : CellSquare) :
    carrierHeight (cellSquareCarrierPoint v i p) = 0 := by
  rw [cellSquareCarrierPoint, carrierHeight_inclusion, rawHeight_eq_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (cellZeroCoordinate i))
  exact cellLiftCoordinates_zero i _

/-- A square chart as a point of the local positive central cell. -/
public def cellSquarePoint {r : ℝ} (hr : 0 < r)
    (v : ToricLattice) (i : Fin 6) (p : CellSquare) :
    constructedPositiveCentralCell r v := by
  let x := cellSquareCarrierPoint v i p
  let q : localCarrier constructedModel r := ⟨x, by
    change carrierHeight x ∈ Metric.ball 0 r
    rw [cellSquareCarrierPoint_height]
    exact Metric.mem_ball_self hr⟩
  let qpos : constructedLocalPositivePart r := ⟨q,
    (mem_constructedLocalPositivePart_iff r q).mpr
      (cellSquareCarrierPoint_mem_positive v i p)⟩
  exact ⟨⟨qpos, by
      change carrierHeight x = 0
      exact cellSquareCarrierPoint_height v i p⟩,
    cellSquareCarrierPoint_mem_component v i p⟩

public theorem continuous_cellSquarePoint {r : ℝ} (hr : 0 < r)
    (v : ToricLattice) (i : Fin 6) :
    Continuous (cellSquarePoint hr v i) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact continuous_cellSquareCarrierPoint v i

public theorem isCompact_cellSquare :
    IsCompact {p : Fin 2 → ℝ | ∀ i, p i ∈ Set.Icc (0 : ℝ) 1} :=
  isCompact_pi_infinite fun _ ↦ CompactIccSpace.isCompact_Icc

public instance cellSquare_compactSpace : CompactSpace CellSquare :=
  isCompact_iff_compactSpace.mp isCompact_cellSquare

/-- The six compact positive affine charts projected onto one central toric cell. -/
public def cellSquareProjection {r : ℝ} (hr : 0 < r) (v : ToricLattice) :
    Fin 6 × CellSquare → constructedPositiveCentralCell r v :=
  fun p ↦ cellSquarePoint hr v p.1 p.2

public theorem continuous_cellSquareProjection {r : ℝ} (hr : 0 < r)
    (v : ToricLattice) : Continuous (cellSquareProjection hr v) :=
  continuous_prod_of_discrete_left.mpr (continuous_cellSquarePoint hr v)

/-- The six unit positive charts cover the whole positive central cell. -/
public theorem surjective_cellSquareProjection {r : ℝ} (hr : 0 < r)
    (v : ToricLattice) : Function.Surjective (cellSquareProjection hr v) := by
  intro q
  let x : Carrier := q.1.1.1.1
  have hxzero : carrierHeight x = 0 := by
    exact q.1.property
  obtain ⟨a, ha⟩ := carrierCentralFiber_unitPolydisc_cover x hxzero
  have hav : v ∈ Set.range (a2Triangle a.1 a.2) := by
    by_contra hnot
    exact Set.disjoint_left.mp
      (otherCarrierCentralComponent_disjoint_chart a v hnot) q.property ha.1
  obtain ⟨i, hi⟩ := surjective_cellChart v ⟨a, hav⟩
  have haeq : cellChart v i = a := congrArg Subtype.val hi
  subst a
  change x ∈ (toricChart (cellChart v i)).source ∧
    (∀ j, ‖toricChart (cellChart v i) x j‖ ≤ 1) at ha
  rw [toricChart_source] at ha
  obtain ⟨z, hzx⟩ := ha.1
  have hzpos : inclusion (cellChart v i) z ∈ carrierPositivePart := by
    rw [hzx]
    exact (mem_constructedLocalPositivePart_iff r q.1.1).mp q.1.1.property
  obtain ⟨u, hu, hzu⟩ :=
    (inclusion_mem_carrierPositivePart_iff (cellChart v i) z).mp hzpos
  have hxcomponent : x ∈ carrierCentralComponent v := q.property
  have hzzero : z (cellZeroCoordinate i) = 0 := by
    have hcomponent := (carrierCentralComponent_in_chart
      (cellChart v i) (cellZeroCoordinate i)
      (inclusion (cellChart v i) z) (by
        rw [toricChart_source]
        exact Set.mem_range_self z)).mp
      (by
        rw [hzx]
        simpa only [cellChart_zeroRay] using hxcomponent)
    rw [toricChart_inclusion] at hcomponent
    simpa [rawToComplexModel] using hcomponent
  let p : CellSquare :=
    ⟨fun k ↦ (cellRemoveCoordinates i z k).re, by
      intro k
      constructor
      · have hnonneg := hu (cellRemoveIndex i k)
        simpa [hzu] using hnonneg
      · have hbound := ha.2 (cellRemoveIndex i k)
        rw [← hzx, toricChart_inclusion] at hbound
        have hbound' : |u (cellRemoveIndex i k)| ≤ 1 := by
          simpa [rawToComplexModel, hzu, Complex.norm_real] using hbound
        simpa [hzu] using (abs_le.mp hbound').2⟩
  have hp : (fun k ↦ (p.1 k : ℂ)) = cellRemoveCoordinates i z := by
    funext k
    change ((cellRemoveCoordinates i z k).re : ℂ) =
      cellRemoveCoordinates i z k
    rw [hzu]
    simp
  refine ⟨(i, p), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change inclusion (cellChart v i)
      (cellLiftCoordinates i (fun k ↦ (p.1 k : ℂ))) =
    x
  rw [← hzx]
  congr 1
  rw [hp]
  rw [cellLiftCoordinates_remove i z hzzero]

/-! ## A finite quotient model for the planar hexagon -/

/-- The six vertices of the axial Voronoi hexagon, relative to its lattice centre. -/
public def planeVertexOffset : Fin 6 → Fin 2 → ℝ :=
  ![![2 / 3, 0], ![2 / 3, 2 / 3], ![0, 2 / 3],
    ![-2 / 3, 0], ![-2 / 3, -2 / 3], ![0, -2 / 3]]

/-- The midpoint of the edge ending at the indicated cyclic vertex. -/
public def planeMidpointOffset (i : Fin 6) : Fin 2 → ℝ :=
  ![![1 / 3, -1 / 3], ![2 / 3, 1 / 3], ![1 / 3, 2 / 3],
    ![-1 / 3, 1 / 3], ![-2 / 3, -1 / 3], ![-1 / 3, -2 / 3]] i

/-- The midpoint of the following edge in cyclic order. -/
public def planeNextMidpointOffset (i : Fin 6) : Fin 2 → ℝ :=
  ![![2 / 3, 1 / 3], ![1 / 3, 2 / 3], ![-1 / 3, 1 / 3],
    ![-2 / 3, -1 / 3], ![-1 / 3, -2 / 3], ![1 / 3, -1 / 3]] i

public def cellNextIndex : Fin 6 → Fin 6 := ![1, 2, 3, 4, 5, 0]

public def planeNextVertexOffset : Fin 6 → Fin 2 → ℝ :=
  ![![2 / 3, 2 / 3], ![0, 2 / 3], ![-2 / 3, 0],
    ![-2 / 3, -2 / 3], ![0, -2 / 3], ![2 / 3, 0]]

/-- The standard square parametrization of one of the six triangular sectors of a cell. -/
public def planeTile (v : ToricLattice) (i : Fin 6)
    (p : CellSquare) : Fin 2 → ℝ :=
  (fun k ↦ (v k : ℝ)) +
    ((1 - max (p.1 0) (p.1 1)) • planeVertexOffset i +
      max (p.1 1 - p.1 0) 0 • planeMidpointOffset i +
      max (p.1 0 - p.1 1) 0 • planeNextMidpointOffset i)

public theorem continuous_planeTile (v : ToricLattice) (i : Fin 6) :
    Continuous (planeTile v i) := by
  have h0 : Continuous (fun p : CellSquare ↦ p.1 0) :=
    (continuous_apply 0).comp continuous_subtype_val
  have h1 : Continuous (fun p : CellSquare ↦ p.1 1) :=
    (continuous_apply 1).comp continuous_subtype_val
  exact continuous_const.add
    ((((continuous_const.sub (h0.max h1)).smul continuous_const).add
      (((h1.sub h0).max continuous_const).smul continuous_const)).add
      (((h0.sub h1).max continuous_const).smul continuous_const))

public theorem planeTile_of_le (v : ToricLattice) (i : Fin 6)
    (p : CellSquare) (hp : p.1 0 ≤ p.1 1) :
    planeTile v i p =
      (fun k ↦ (v k : ℝ)) + ((1 - p.1 1) • planeVertexOffset i +
        (p.1 1 - p.1 0) • planeMidpointOffset i) := by
  simp [planeTile, max_eq_right hp, max_eq_left (sub_nonneg.mpr hp),
    max_eq_right (sub_nonpos.mpr hp)]

public theorem planeTile_of_ge (v : ToricLattice) (i : Fin 6)
    (p : CellSquare) (hp : p.1 1 ≤ p.1 0) :
    planeTile v i p =
      (fun k ↦ (v k : ℝ)) + ((1 - p.1 0) • planeVertexOffset i +
        (p.1 0 - p.1 1) • planeNextMidpointOffset i) := by
  simp [planeTile, max_eq_left hp, max_eq_right (sub_nonpos.mpr hp),
    max_eq_left (sub_nonneg.mpr hp)]

public theorem planeTile_mem (v : ToricLattice) (i : Fin 6)
    (p : CellSquare) :
    planeTile v i p ∈ planeCell v := by
  have hp0 := p.2 0
  have hp1 := p.2 1
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · rw [planeTile_of_le v i p hp]
    fin_cases i <;>
      simp only [planeCell, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, planeVertexOffset, planeMidpointOffset]
    all_goals
      constructor
      · apply abs_le.mpr
        constructor <;> norm_num <;> linarith [hp0.1, hp0.2, hp1.1, hp1.2]
      constructor
      · apply abs_le.mpr
        constructor <;> norm_num <;> linarith [hp0.1, hp0.2, hp1.1, hp1.2]
      · apply abs_le.mpr
        constructor <;> norm_num <;> linarith [hp0.1, hp0.2, hp1.1, hp1.2]
  · rw [planeTile_of_ge v i p hp]
    fin_cases i <;>
      simp only [planeCell, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, planeVertexOffset, planeNextMidpointOffset]
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
public theorem planeVertexOffset_nextIndex (i : Fin 6) :
    planeVertexOffset (cellNextIndex i) =
      planeNextVertexOffset i := by
  fin_cases i <;> rfl

@[simp]
public theorem planeMidpointOffset_nextIndex (i : Fin 6) :
    planeMidpointOffset (cellNextIndex i) =
      planeNextMidpointOffset i := by
  fin_cases i <;> rfl

public theorem planeNextMidpointOffset_eq (i : Fin 6) :
    planeNextMidpointOffset i =
      (1 / 2 : ℝ) • (planeVertexOffset i +
        planeNextVertexOffset i) := by
  fin_cases i <;> ext k <;> fin_cases k <;>
    norm_num [planeNextMidpointOffset, planeVertexOffset,
      planeNextVertexOffset]

public theorem exists_planeTile_of_sector (v : ToricLattice)
    (i : Fin 6) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β ≤ 1) :
    ∃ j p, planeTile v j p =
      (fun k ↦ (v k : ℝ)) +
        (α • planeVertexOffset i +
          β • planeNextVertexOffset i) := by
  rcases le_total β α with hβα | hαβ'
  · let p : CellSquare :=
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
    rw [planeTile_of_ge v i p hp,
      planeNextMidpointOffset_eq]
    ext k
    simp only [p, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  · let p : CellSquare :=
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
    refine ⟨cellNextIndex i, p, ?_⟩
    rw [planeTile_of_le v (cellNextIndex i) p hp,
      planeVertexOffset_nextIndex, planeMidpointOffset_nextIndex,
      planeNextMidpointOffset_eq]
    ext k
    simp only [p, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring

/-- The six planar square sectors projected onto their explicit axial hexagon. -/
public def planeSquareProjection (v : ToricLattice) :
    Fin 6 × CellSquare → planeCell v :=
  fun a ↦ ⟨planeTile v a.1 a.2, planeTile_mem v a.1 a.2⟩

public theorem surjective_planeSquareProjection (v : ToricLattice) :
    Function.Surjective (planeSquareProjection v) := by
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
        (α • planeVertexOffset i +
          β • planeNextVertexOffset i)) :
      ∃ a, planeSquareProjection v a = x := by
    obtain ⟨j, p, hp⟩ :=
      exists_planeTile_of_sector v i α β hα hβ hαβ
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
            simp [dx, dy, planeVertexOffset,
              planeNextVertexOffset] <;> ring
      · apply hsector 1 ((3 / 2 : ℝ) * dx) ((3 / 2 : ℝ) * (dy - dx))
        · positivity
        · positivity
        · have := (abs_le.mp hx1).2
          linarith
        · ext k
          fin_cases k <;>
            simp [dx, dy, planeVertexOffset,
              planeNextVertexOffset] <;> ring
    · have hdy' : dy ≤ 0 := le_of_not_ge hdy
      apply hsector 5 (-(3 / 2 : ℝ) * dy) ((3 / 2 : ℝ) * dx)
      · nlinarith
      · positivity
      · have := (abs_le.mp hxd).2
        linarith
      · ext k
        fin_cases k <;>
          simp [dx, dy, planeVertexOffset,
            planeNextVertexOffset] <;> ring
  · have hdx' : dx ≤ 0 := le_of_not_ge hdx
    by_cases hdy : 0 ≤ dy
    · apply hsector 2 ((3 / 2 : ℝ) * dy) (-(3 / 2 : ℝ) * dx)
      · positivity
      · nlinarith
      · have := (abs_le.mp hxd).1
        linarith
      · ext k
        fin_cases k <;>
          simp [dx, dy, planeVertexOffset,
            planeNextVertexOffset] <;> ring
    · have hdy' : dy ≤ 0 := le_of_not_ge hdy
      rcases le_total dx dy with hxdy | hdyx
      · apply hsector 3 ((3 / 2 : ℝ) * (dy - dx)) (-(3 / 2 : ℝ) * dy)
        · positivity
        · nlinarith
        · have := (abs_le.mp hx0).1
          linarith
        · ext k
          fin_cases k <;>
            simp [dx, dy, planeVertexOffset,
              planeNextVertexOffset] <;> ring
      · apply hsector 4 (-(3 / 2 : ℝ) * dx) ((3 / 2 : ℝ) * (dx - dy))
        · nlinarith
        · positivity
        · have := (abs_le.mp hx1).1
          linarith
        · ext k
          fin_cases k <;>
            simp [dx, dy, planeVertexOffset,
              planeNextVertexOffset] <;> ring


public theorem isQuotientMap_cellSquareProjection {r : ℝ} (hr : 0 < r)
    (v : ToricLattice) : Topology.IsQuotientMap (cellSquareProjection hr v) :=
  Topology.IsQuotientMap.of_surjective_continuous
    (surjective_cellSquareProjection hr v)
    (continuous_cellSquareProjection hr v)












end Construction

end SphereSixComplex.Geometry.InfiniteA2Toric

end

end
