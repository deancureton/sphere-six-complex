module

public import SphereSixComplex.Geometry.PaperStarPieceTopology
public import Mathlib.Analysis.Convex.PathConnected

/-!
# Connectedness of the local cusp filling

The positive-radius local toric carrier is connected because its intersection with each affine
toric chart is star-convex in the chart coordinates, and all chart intersections share a point of
the dense torus.  Connectedness then descends to the actual local cusp quotient.
-/

open TopologicalSpace Topology

namespace SphereSixComplex.Geometry

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open StandardInfiniteA2ToricModel CuspCombinatorics CuspFilling CuspLocalPhaseAction
open CuspPuncturedCollarBridge CuspPhaseEstimates CuspPeriodExpansion

noncomputable section

private def toricCuspCoordinateRegion (r : ℝ) : Set ComplexModel :=
  {z | ‖z 0 * z 1 * z 2‖ < r}

private theorem toricCuspCoordinateRegion_starConvex (r : ℝ) :
    StarConvex ℝ 0 (toricCuspCoordinateRegion r) := by
  intro z hz a b ha hb hab
  change ‖(a • (0 : ComplexModel) + b • z) 0 *
    (a • (0 : ComplexModel) + b • z) 1 *
    (a • (0 : ComplexModel) + b • z) 2‖ < r
  simp only [smul_zero, zero_add, PiLp.smul_apply, Complex.real_smul, norm_mul,
    Complex.norm_real]
  have hb1 : b ≤ 1 := by linarith
  have habs : |b| ≤ 1 := by simpa [abs_of_nonneg hb] using hb1
  have hcube : |b| * |b| * |b| ≤ 1 := by nlinarith [abs_nonneg b]
  calc
    |b| * ‖z 0‖ * (|b| * ‖z 1‖) * (|b| * ‖z 2‖) =
        (|b| * |b| * |b|) * (‖z 0‖ * ‖z 1‖ * ‖z 2‖) := by ring
    _ ≤ 1 * (‖z 0‖ * ‖z 1‖ * ‖z 2‖) := by gcongr
    _ = ‖z 0 * z 1 * z 2‖ := by simp only [one_mul, norm_mul]
    _ < r := hz

private theorem toricCuspCoordinateRegion_isConnected {r : ℝ} (hr : 0 < r) :
    IsConnected (toricCuspCoordinateRegion r) := by
  have hzero : (0 : ComplexModel) ∈ toricCuspCoordinateRegion r := by
    simpa [toricCuspCoordinateRegion] using hr
  exact ((toricCuspCoordinateRegion_starConvex r).isPathConnected hzero).isConnected

private def toricChartCuspRegion (M : Model) (r : ℝ) (upper : Bool)
    (v : ToricLattice) : Set M.Carrier :=
  (M.toricChart upper v).source ∩ cuspNeighborhood M r

private noncomputable def toricChartCuspParametrization
    (M : Model) (r : ℝ) (upper : Bool) (v : ToricLattice) :
    toricCuspCoordinateRegion r → M.Carrier := fun z =>
  ((M.toricChart upper v).toOpenPartialHomeomorph.toHomeomorphSourceTarget.symm
    ⟨z, by
      change (z : ComplexModel) ∈ (M.toricChart upper v).target
      rw [M.toricChart_target]
      trivial⟩ : (M.toricChart upper v).source)

private theorem toricChartCuspParametrization_continuous
    (M : Model) (r : ℝ) (upper : Bool) (v : ToricLattice) :
    Continuous (toricChartCuspParametrization M r upper v) := by
  exact continuous_subtype_val.comp
    ((M.toricChart upper v).toOpenPartialHomeomorph.toHomeomorphSourceTarget.symm.continuous.comp
      (Continuous.subtype_mk continuous_subtype_val _))

private theorem toricChartCuspParametrization_range
    (M : Model) (r : ℝ) (upper : Bool) (v : ToricLattice) :
    Set.range (toricChartCuspParametrization M r upper v) =
      toricChartCuspRegion M r upper v := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    let q := (M.toricChart upper v).toOpenPartialHomeomorph.toHomeomorphSourceTarget.symm
      ⟨z, by
        change (z : ComplexModel) ∈ (M.toricChart upper v).target
        rw [M.toricChart_target]
        trivial⟩
    have hsource : (q : M.Carrier) ∈ (M.toricChart upper v).source := q.property
    refine ⟨hsource, ?_⟩
    change M.t (q : M.Carrier) ∈ Metric.ball 0 r
    rw [Metric.mem_ball, dist_zero_right, M.toricChart_t upper v q hsource]
    have hchart : M.toricChart upper v q = z := by
      exact congrArg Subtype.val
        ((M.toricChart upper v).toOpenPartialHomeomorph.toHomeomorphSourceTarget.apply_symm_apply
          ⟨z, by
            change (z : ComplexModel) ∈ (M.toricChart upper v).target
            rw [M.toricChart_target]
            trivial⟩)
    rw [hchart]
    exact z.property
  · rintro ⟨hsource, hcusp⟩
    let z : toricCuspCoordinateRegion r :=
      ⟨M.toricChart upper v p, by
        rw [toricCuspCoordinateRegion, Set.mem_ofPred_eq, ← M.toricChart_t upper v p hsource]
        simpa [mem_cuspNeighborhood_iff, Metric.mem_ball, dist_zero_right] using hcusp⟩
    refine ⟨z, ?_⟩
    change ((M.toricChart upper v).toOpenPartialHomeomorph.toHomeomorphSourceTarget.symm
      ⟨z, by
        change (z : ComplexModel) ∈ (M.toricChart upper v).target
        rw [M.toricChart_target]
        trivial⟩ : (M.toricChart upper v).source) = p
    exact congrArg Subtype.val
      ((M.toricChart upper v).toOpenPartialHomeomorph.toHomeomorphSourceTarget.symm_apply_apply
        ⟨p, hsource⟩)

private theorem toricChartCuspRegion_isConnected
    (M : Model) {r : ℝ} (hr : 0 < r) (upper : Bool) (v : ToricLattice) :
    IsConnected (toricChartCuspRegion M r upper v) := by
  let _ : ConnectedSpace (toricCuspCoordinateRegion r) :=
    isConnected_iff_connectedSpace.mp (toricCuspCoordinateRegion_isConnected hr)
  rw [← toricChartCuspParametrization_range]
  exact isConnected_range (toricChartCuspParametrization_continuous M r upper v)

private noncomputable def commonDenseTorusPoint (r : ℝ) (hr : 0 < r) : DenseTorus :=
  fun i ↦ if _ : i = 2 then Units.mk0 ((r / 2 : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.mpr (div_ne_zero hr.ne' (by norm_num))) else 1

private theorem commonDenseTorusPoint_last (r : ℝ) (hr : 0 < r) :
    ((commonDenseTorusPoint r hr 2 : ℂˣ) : ℂ) = ((r / 2 : ℝ) : ℂ) := by
  simp [commonDenseTorusPoint]

private theorem commonDenseTorusPoint_mem
    (M : Model) {r : ℝ} (hr : 0 < r) (a : Bool × ToricLattice) :
    M.torusEmbedding (commonDenseTorusPoint r hr) ∈
      toricChartCuspRegion M r a.1 a.2 := by
  constructor
  · exact M.torus_mem_toricChart a.1 a.2 _
  · change M.t (M.torusEmbedding (commonDenseTorusPoint r hr)) ∈ Metric.ball 0 r
    rw [Metric.mem_ball, dist_zero_right, M.t_torus, commonDenseTorusPoint_last,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    exact half_lt_self hr

private theorem cuspNeighborhood_eq_iUnion_toricChartCuspRegion (M : Model) (r : ℝ) :
    (cuspNeighborhood M r : Set M.Carrier) =
      ⋃ a : Bool × ToricLattice, toricChartCuspRegion M r a.1 a.2 := by
  ext p
  constructor
  · intro hp
    obtain ⟨upper, v, hsource⟩ := M.toricChart_cover p
    exact Set.mem_iUnion.mpr ⟨(upper, v), hsource, hp⟩
  · rintro hp
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hp
    exact ha.2

/-- Every positive-radius neighborhood in the standard toric model is connected. -/
public theorem localCarrier_connected (M : Model) {r : ℝ} (hr : 0 < r) :
    ConnectedSpace (LocalCarrier M r) := by
  have hinter :
      (⋂ a : Bool × ToricLattice, toricChartCuspRegion M r a.1 a.2).Nonempty := by
    refine ⟨M.torusEmbedding (commonDenseTorusPoint r hr), Set.mem_iInter.mpr ?_⟩
    exact commonDenseTorusPoint_mem M hr
  have hpre :
      IsPreconnected (⋃ a : Bool × ToricLattice, toricChartCuspRegion M r a.1 a.2) :=
    isPreconnected_iUnion hinter fun a ↦
      (toricChartCuspRegion_isConnected M hr a.1 a.2).isPreconnected
  have hconn :
      IsConnected (⋃ a : Bool × ToricLattice, toricChartCuspRegion M r a.1 a.2) := by
    refine ⟨?_, hpre⟩
    exact ⟨M.torusEmbedding (commonDenseTorusPoint r hr),
      Set.mem_iUnion.mpr ⟨(false, 0), commonDenseTorusPoint_mem M hr _⟩⟩
  rw [← cuspNeighborhood_eq_iUnion_toricChartCuspRegion] at hconn
  exact isConnected_iff_connectedSpace.mp hconn

/-- The actual phase-corrected local cusp quotient is connected. -/
public theorem actualLocalCuspFilling_connected
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    ConnectedSpace (actualLocalCuspFilling W) := by
  let C :=
    CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  let _ : MulAction (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) :=
    (C.toCuspActionData W.localWitness.fixedPoint).psiAction
  let _ : ConnectedSpace (LocalCarrier M W.localWitness.radius) :=
    localCarrier_connected M W.localWitness.radius_pos
  exact Quotient.mk_surjective.connectedSpace continuous_quot_mk

namespace PaperAnalyticData

variable (A : PaperAnalyticData)

/-- Each of the three concrete filling pieces is connected. -/
public theorem starFilling_connected (i : Fin 3) : ConnectedSpace (A.starFillingType i) := by
  fin_cases i
  · exact actualLocalCuspFilling_connected A.starCuspWitness
  · exact A.orderThreeFilling_connected A.starSeparation.orderThree.radius_pos
      A.starSeparation.orderThree.radius_lt_one
  · exact A.orderFourFilling_connected A.starSeparation.orderFour.radius_pos
      A.starSeparation.orderFour.radius_lt_one

/-- Every piece of the concrete four-piece star is connected. -/
public theorem starPiece_connected (i : Option (Fin 3)) :
    ConnectedSpace (A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.U i) := by
  cases i with
  | none => exact A.centralFamily_connected
  | some i => exact A.starFilling_connected i

end PaperAnalyticData

end


end SphereSixComplex.Geometry
