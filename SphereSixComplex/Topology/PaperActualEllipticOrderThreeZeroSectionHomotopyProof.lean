module

public import SphereSixComplex.Topology.PaperActualEllipticOrderThreePrincipalGaugeHomotopyProof
public import SphereSixComplex.Topology.PaperGeometricCentralPeripheral

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Topology
open SphereSixComplex.Periods.SourceAutomaticBranch
open SphereSixComplex.TriangleGroup

variable (A : PaperAnalyticData)

private theorem homotopyTrans_trace
    {Y : Type*} [TopologicalSpace Y]
    {f g h : C(unitInterval, Y)}
    (H : ContinuousMap.Homotopy f g)
    (K : ContinuousMap.Homotopy g h)
    (hH : ∀ s : unitInterval, H (s, 0) = H (s, 1))
    (hK : ∀ s : unitInterval, K (s, 0) = K (s, 1))
    (s : unitInterval) :
    H.trans K (s, 0) = H.trans K (s, 1) := by
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hH _
  · exact hK _

private theorem orderThreeCayleyChartRadialHomotopy_trace
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1) (s : unitInterval) :
    A.orderThreeCayleyChartRadialHomotopy c hc hc1 (s, 0) =
      A.orderThreeCayleyChartRadialHomotopy c hc hc1 (s, 1) := by
  apply Subtype.ext
  change ellipticChartFunction A.modular.sourceCoordinate.coordinate fuchsianOneFixedPoint
      (A.orderThreeAlignedCayleyRadialPoint c (s, 0)) =
    ellipticChartFunction A.modular.sourceCoordinate.coordinate fuchsianOneFixedPoint
      (A.orderThreeAlignedCayleyRadialPoint c (s, 1))
  congr 1
  unfold orderThreeAlignedCayleyRadialPoint
  rw [show localDegreeCirclePoint A.orderThreeFillingRelationCayleyBaseValue 0 =
      localDegreeCirclePoint A.orderThreeFillingRelationCayleyBaseValue 1 by
    unfold localDegreeCirclePoint
    norm_num]

private theorem exactLocalFactorizationCircleHomotopyTwoPunctures_trace
    (u : ℂ → ℂ) (n : ℕ) (a b : ℂ) (ha : a ≠ 0)
    (hu : ContinuousOn u (Metric.closedBall (0 : ℂ) ‖a‖))
    (hune : ∀ z ∈ Metric.closedBall (0 : ℂ) ‖a‖, u z ≠ 0)
    (hbound : ∀ z ∈ Metric.closedBall (0 : ℂ) ‖a‖,
      ‖a‖ ^ n * ‖u z‖ < ‖b‖)
    (s : unitInterval) :
    exactLocalFactorizationCircleHomotopyTwoPunctures
        u n a b ha hu hune hbound (s, 0) =
      exactLocalFactorizationCircleHomotopyTwoPunctures
        u n a b ha hu hune hbound (s, 1) := by
  apply Subtype.ext
  change localDegreeCirclePoint a 0 ^ n * u (localDegreeRadialPoint a (s, 0)) =
    localDegreeCirclePoint a 1 ^ n * u (localDegreeRadialPoint a (s, 1))
  rw [show localDegreeCirclePoint a 0 = localDegreeCirclePoint a 1 by
    unfold localDegreeCirclePoint
    norm_num]
  congr 2
  unfold localDegreeRadialPoint
  rw [show localDegreeCirclePoint a 0 = localDegreeCirclePoint a 1 by
    unfold localDegreeCirclePoint
    norm_num]

private theorem positiveTripleCoefficientHomotopy_trace
    (d : ℂ) (hd : d ≠ 0) (hd1 : ‖d‖ < 1) (s : unitInterval) :
    positiveTripleCoefficientHomotopy d hd hd1 (s, 0) =
      positiveTripleCoefficientHomotopy d hd hd1 (s, 1) := by
  apply Subtype.ext
  change positiveTripleCoefficientHomotopyValue d (s, 0) =
    positiveTripleCoefficientHomotopyValue d (s, 1)
  unfold positiveTripleCoefficientHomotopyValue
  norm_num
  have he : Complex.exp ((2 : ℂ) * Real.pi * 3 * Complex.I) = 1 := by
    rw [show (2 : ℂ) * Real.pi * 3 * Complex.I =
      (3 : ℕ) * (2 * Real.pi * Complex.I) by norm_num; ring]
    exact Complex.exp_nat_mul_two_pi_mul_I 3
  rw [he, mul_one]

private theorem orderThreeActualCayleyBaseCoordinate_tripleHomotopy_with_trace :
    ∃ H : ContinuousMap.Homotopy
        (twoPunctureComplementOneMap.comp
          (A.orderThreeCayleyChartCircleMap
            A.orderThreeFillingRelationCayleyBaseValue
            (norm_pos_iff.mpr A.orderThreeFillingRelationCayleyBaseValue_ne_zero)
            (by
              rw [A.orderThreeFillingRelationCayleyBaseValue_norm]
              exact A.orderThreeActualEllipticBoundaryBase.1.2.2)))
        twicePuncturedCounterclockwiseZeroTriple.toContinuousMap,
      ∀ s : unitInterval, H (s, 0) = H (s, 1) := by
  obtain ⟨u, a, c, hc, hc1, haeq, hu, hune, hfac, hbound⟩ :=
    A.exists_orderThreeCayleyBaseCoordinate_alignedSmallCircleData
  subst a
  let a : ℂ := (c : ℂ) * A.orderThreeFillingRelationCayleyBaseValue
  have ha : a ≠ 0 := by
    dsimp [a]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne')
      A.orderThreeFillingRelationCayleyBaseValue_ne_zero
  have hbound' : ∀ z ∈ Metric.closedBall (0 : ℂ) ‖a‖,
      ‖a‖ ^ 3 * ‖u z‖ < ‖(1 : ℂ)‖ := by
    simpa [a] using hbound
  have har : ‖a‖ < A.starSeparation.orderThree.radius := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    exact (mul_lt_mul_of_pos_right hc1
      (norm_pos_iff.mpr
        A.orderThreeFillingRelationCayleyBaseValue_ne_zero)).trans (by
          rw [A.orderThreeFillingRelationCayleyBaseValue_norm]
          simpa using A.orderThreeActualEllipticBoundaryBase.1.2.2)
  have hsmall :
      A.orderThreeCayleyChartCircleMap a (norm_pos_iff.mpr ha) har =
        factorizedLocalDegreeCircleTwoPunctures
          u 3 a 1 ha hu hune hbound' := by
    ext t
    change ellipticChartFunction A.modular.sourceCoordinate.coordinate
        fuchsianOneFixedPoint (localDegreeCirclePoint a t) =
      localDegreeCirclePoint a t ^ 3 * u (localDegreeCirclePoint a t)
    exact hfac _ (by
      rw [Metric.mem_closedBall, dist_zero_right, localDegreeCirclePoint_norm])
  let Hrad := A.orderThreeCayleyChartRadialHomotopy c hc hc1
  have htarget :
      A.orderThreeCayleyChartCircleMap
          ((c : ℂ) * A.orderThreeFillingRelationCayleyBaseValue)
          (by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
            exact mul_pos hc
              (norm_pos_iff.mpr
                A.orderThreeFillingRelationCayleyBaseValue_ne_zero))
          (by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
            exact (mul_lt_mul_of_pos_right hc1
              (norm_pos_iff.mpr
                A.orderThreeFillingRelationCayleyBaseValue_ne_zero)).trans (by
                  rw [A.orderThreeFillingRelationCayleyBaseValue_norm]
                  simpa using A.orderThreeActualEllipticBoundaryBase.1.2.2)) =
        factorizedLocalDegreeCircleTwoPunctures
          u 3 a 1 ha hu hune hbound' := by
    exact hsmall
  let Hlocal := exactLocalFactorizationCircleHomotopyTwoPunctures
    u 3 a 1 ha hu hune hbound'
  let Hfirst := (Hrad.cast rfl htarget).trans Hlocal
  have hHfirst : ∀ s : unitInterval, Hfirst (s, 0) = Hfirst (s, 1) := by
    intro s
    apply homotopyTrans_trace
    · intro r
      exact A.orderThreeCayleyChartRadialHomotopy_trace c hc hc1 r
    · intro r
      exact exactLocalFactorizationCircleHomotopyTwoPunctures_trace
        u 3 a 1 ha hu hune hbound' r
  let Hmap := twoPunctureComplementOneHomotopyMap Hfirst
  let d : ℂ := a ^ 3 * u 0
  have hzero : (0 : ℂ) ∈ Metric.closedBall 0 ‖a‖ := by
    rw [Metric.mem_closedBall, dist_self]
    exact norm_nonneg a
  have hd : d ≠ 0 :=
    mul_ne_zero (pow_ne_zero 3 ha) (hune 0 hzero)
  have hd1 : ‖d‖ < 1 := by
    dsimp [d]
    rw [norm_mul, norm_pow]
    simpa using hbound' 0 hzero
  have hfrozen :
      twoPunctureComplementOneMap.comp
          (frozenLocalDegreeCircleTwoPunctures
            u 3 a 1 ha hune hbound') =
        twicePuncturedPositiveTripleCircle d hd hd1 := by
    simpa [d] using
      frozenLocalDegreeCircleTwoPunctures_map_eq_positiveTriple
        u a ha hune hbound'
  let Hcoefficient := positiveTripleCoefficientHomotopy d hd hd1
  let H := (Hmap.cast rfl hfrozen).trans Hcoefficient
  refine ⟨H, ?_⟩
  intro s
  apply homotopyTrans_trace
  · intro r
    exact congrArg twoPunctureComplementOneHomeomorph (hHfirst r)
  · intro r
    exact positiveTripleCoefficientHomotopy_trace d hd hd1 r

/-- The zero-section lift of the actual order-three base-coordinate loop. -/
public noncomputable def orderThreeZeroSectionBaseMap :
    C(unitInterval, A.CentralFamily) :=
  A.markedBaseToCentralZeroSection.comp A.orderThreeFillingRelationBaseCoordinateMap

/-- The zero-section lift of the standard positive three-turn zero meridian. -/
public noncomputable def orderThreeZeroSectionTriplePath :
    Path (A.centralZeroSection A.markedPuncturedBasepoint)
      (A.centralZeroSection A.markedPuncturedBasepoint) :=
  twicePuncturedCounterclockwiseZeroTriple.map
    A.markedBaseToCentralZeroSection.continuous

/-- The cubic base homotopy lifts literally through the global zero section. -/
public theorem orderThreeZeroSectionBase_tripleHomotopy :
    Nonempty (ContinuousMap.Homotopy A.orderThreeZeroSectionBaseMap
      A.orderThreeZeroSectionTriplePath.toContinuousMap) := by
  rcases A.orderThreeActualCayleyBaseCoordinate_tripleHomotopy with ⟨H⟩
  let H' := H.cast A.orderThreeFillingRelationBaseCoordinateMap_eq_cayley.symm rfl
  exact ⟨{
    toFun := fun st ↦ A.markedBaseToCentralZeroSection (H' st)
    continuous_toFun := A.markedBaseToCentralZeroSection.continuous.comp H'.continuous
    map_zero_left := by
      intro t
      exact congrArg A.markedBaseToCentralZeroSection (H'.map_zero_left t)
    map_one_left := by
      intro t
      exact congrArg A.markedBaseToCentralZeroSection (H'.map_one_left t) }⟩

/-- The lifted cubic base homotopy is a genuine free-loop homotopy: its two endpoint traces
agree throughout. -/
public theorem orderThreeZeroSectionBase_tripleHomotopy_with_trace :
    ∃ H : ContinuousMap.Homotopy A.orderThreeZeroSectionBaseMap
        A.orderThreeZeroSectionTriplePath.toContinuousMap,
      ∀ s : unitInterval, H (s, 0) = H (s, 1) := by
  rcases A.orderThreeActualCayleyBaseCoordinate_tripleHomotopy_with_trace with
    ⟨H, htrace⟩
  let H' := H.cast A.orderThreeFillingRelationBaseCoordinateMap_eq_cayley.symm rfl
  let K : ContinuousMap.Homotopy A.orderThreeZeroSectionBaseMap
      A.orderThreeZeroSectionTriplePath.toContinuousMap :=
    { toFun := fun st ↦ A.markedBaseToCentralZeroSection (H' st)
      continuous_toFun := A.markedBaseToCentralZeroSection.continuous.comp H'.continuous
      map_zero_left := by
        intro t
        exact congrArg A.markedBaseToCentralZeroSection (H'.map_zero_left t)
      map_one_left := by
        intro t
        exact congrArg A.markedBaseToCentralZeroSection (H'.map_one_left t) }
  refine ⟨K, ?_⟩
  intro s
  exact congrArg A.markedBaseToCentralZeroSection (htrace s)

/-- The lifted positive three-turn circle is the cube of the inverse marked central meridian. -/
public theorem orderThreeZeroSectionTriplePath_class :
    Path.Homotopic.Quotient.mk A.orderThreeZeroSectionTriplePath =
      A.markedZeroCentralMeridianClass⁻¹ ^ 3 := by
  have h := congrArg
    (FundamentalGroup.map A.markedBaseToCentralZeroSection
      twicePuncturedComplexBasepoint)
    twicePuncturedCounterclockwiseZeroTriple_class
  rw [map_pow, map_inv, A.markedBaseToCentralZeroSection_map_zero] at h
  change (Path.Homotopic.Quotient.mk
      twicePuncturedCounterclockwiseZeroTriple).map
        A.markedBaseToCentralZeroSection = _ at h
  rw [← Path.Homotopic.Quotient.mk_map] at h
  exact h

/-- Rebase the lifted three-turn zero-section circle at the selected actual cusp point. -/
public noncomputable def orderThreeActualCuspZeroSectionTriplePath :
    Path A.actualCuspCentralBase A.actualCuspCentralBase :=
  A.actualCuspMarkedCentralWhisker.symm.trans
    (A.orderThreeZeroSectionTriplePath.trans A.actualCuspMarkedCentralWhisker)

/-- At the actual cusp basepoint, the zero-section part of the order-three loop is exactly
the cube of the geometric first central meridian. -/
public theorem orderThreeActualCuspZeroSectionTriplePath_class :
    Path.Homotopic.Quotient.mk A.orderThreeActualCuspZeroSectionTriplePath =
      A.geometricCentralRhoOne ^ 3 := by
  have h := congrArg A.markedCentralToActualCuspEquiv
    A.orderThreeZeroSectionTriplePath_class
  rw [map_pow] at h
  exact h

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
