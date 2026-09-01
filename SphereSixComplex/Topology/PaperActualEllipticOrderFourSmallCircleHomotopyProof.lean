module

public import SphereSixComplex.Topology.ExactLocalFactorizationCircleHomotopy
public import SphereSixComplex.Topology.PaperActualEllipticOrderFourBaseCoordinateLocalDegreeProof

/-!
# The small order-four base-coordinate circle

The quartic analytic branch supplies a sufficiently small Cayley circle whose affine image is
freely homotopic, inside the twice-punctured target, to a positive four-turn circle.
-/

@[expose] public section

noncomputable section

open Complex Filter Metric Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Topology
open SphereSixComplex.Periods.SourceAutomaticBranch
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.GlobalTorusFamily

variable (A : PaperAnalyticData)

/-- Every noncentral Cayley point in the selected order-four collar has affine coordinate
different from both punctures. -/
public theorem orderFourCayleyChartFunction_sub_one_ne_zero_neg_one
    {w : ℂ} (hw0 : 0 < ‖w‖)
    (hwr : ‖w‖ < A.starSeparation.orderFour.radius) :
    ellipticChartFunction A.modular.sourceCoordinate.coordinate
          fuchsianTwoFixedPoint w - 1 ≠ 0 ∧
      ellipticChartFunction A.modular.sourceCoordinate.coordinate
          fuchsianTwoFixedPoint w - 1 ≠ -1 := by
  have hw1 : ‖w‖ < 1 :=
    hwr.trans A.starSeparation.orderFour.radius_lt_one
  let z : UpperHalfPlane :=
    UpperHalfPlane.ofComplex (cayleyRawInverse fuchsianTwoFixedPoint w)
  have hcay :
      ((orderFourCayleyHomeomorph z :
        SphereSixComplex.Geometry.EllipticLocalCoordinates.ComplexUnitDisc) : ℂ) = w := by
    exact cayleyCoordinate_rawInverse hw1
  have hzreg : IsRegularBasePoint
      (U := A.modular.modularParameter.toTriangleUniformization) z := by
    exact A.starSeparation.orderFour.sourceData.1 z
      (by simpa [hcay] using hw0) (by simpa [hcay] using hwr)
  have hmem := (A.regularCoordinate ⟨z, hzreg⟩).property
  simp only [RegularCoordinateBase, Set.mem_compl_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or] at hmem
  have hraw :
      ellipticChartFunction A.modular.sourceCoordinate.coordinate
          fuchsianTwoFixedPoint w ≠ 0 ∧
        ellipticChartFunction A.modular.sourceCoordinate.coordinate
          fuchsianTwoFixedPoint w ≠ 1 := by
    simpa [ellipticChartFunction, regularCoordinate, z] using hmem
  constructor
  · intro h
    apply hraw.2
    linear_combination h
  · intro h
    apply hraw.1
    linear_combination h

public theorem orderFourFillingRelationCayleyBaseValue_norm :
    ‖A.orderFourFillingRelationCayleyBaseValue‖ =
      (A.orderFourActualEllipticBoundaryBase.1 : ℝ) := by
  rw [orderFourFillingRelationCayleyBaseValue, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos A.orderFourActualEllipticBoundaryBase.1.2.1]
  rw [Circle.norm_coe, mul_one]

/-- The affine coordinate of a positive Cayley circle contained in the selected collar. -/
public noncomputable def orderFourCayleyChartSubOneCircleMap
    (a : ℂ) (ha0 : 0 < ‖a‖)
    (har : ‖a‖ < A.starSeparation.orderFour.radius) :
    C(unitInterval, TwoPunctureComplement (-1 : ℂ)) where
  toFun t :=
    ⟨ellipticChartFunction A.modular.sourceCoordinate.coordinate
        fuchsianTwoFixedPoint (localDegreeCirclePoint a t) - 1,
      A.orderFourCayleyChartFunction_sub_one_ne_zero_neg_one
        (by simpa [localDegreeCirclePoint_norm] using ha0)
        (by simpa [localDegreeCirclePoint_norm] using har)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [continuous_iff_continuousAt]
    intro t
    have hnorm : ‖localDegreeCirclePoint a t‖ < 1 :=
      (by simpa [localDegreeCirclePoint_norm] using
        har.trans A.starSeparation.orderFour.radius_lt_one)
    exact ((ellipticChartFunction_analyticAt_of_norm_lt_one
      A.modular.sourceCoordinate.coordinate_holomorphic hnorm).continuousAt.comp
        (localDegreeCirclePoint_continuous a).continuousAt).sub continuousAt_const

/-- The straight positive rescaling from the actual Cayley circle to a smaller aligned circle. -/
public def orderFourAlignedCayleyRadialPoint (c : ℝ)
    (p : unitInterval × unitInterval) : ℂ :=
  (((1 - (p.1 : ℝ)) + (p.1 : ℝ) * c : ℝ) : ℂ) *
    localDegreeCirclePoint A.orderFourFillingRelationCayleyBaseValue p.2

public theorem orderFourAlignedCayleyRadialPoint_continuous (c : ℝ) :
    Continuous (A.orderFourAlignedCayleyRadialPoint c) := by
  unfold orderFourAlignedCayleyRadialPoint localDegreeCirclePoint
  fun_prop

public theorem orderFourAlignedCayleyRadialPoint_norm_pos_lt
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (p : unitInterval × unitInterval) :
    0 < ‖A.orderFourAlignedCayleyRadialPoint c p‖ ∧
      ‖A.orderFourAlignedCayleyRadialPoint c p‖ <
        A.starSeparation.orderFour.radius := by
  let s : ℝ := p.1
  let d : ℝ := (1 - s) + s * c
  have hs0 : 0 ≤ s := p.1.property.1
  have hs1 : s ≤ 1 := p.1.property.2
  have hd0 : 0 < d := by
    dsimp [d]
    nlinarith
  have hd1 : d ≤ 1 := by
    dsimp [d]
    nlinarith
  have hbase0 : 0 < ‖A.orderFourFillingRelationCayleyBaseValue‖ :=
    norm_pos_iff.mpr A.orderFourFillingRelationCayleyBaseValue_ne_zero
  have hbaser : ‖A.orderFourFillingRelationCayleyBaseValue‖ <
      A.starSeparation.orderFour.radius := by
    rw [A.orderFourFillingRelationCayleyBaseValue_norm]
    exact A.orderFourActualEllipticBoundaryBase.1.2.2
  rw [orderFourAlignedCayleyRadialPoint, norm_mul,
    localDegreeCirclePoint_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hd0]
  exact ⟨mul_pos hd0 hbase0,
    (mul_le_of_le_one_left hbase0.le hd1).trans_lt hbaser⟩

/-- Radial shrinking of the complete Cayley base circle, already mapped to the twice-punctured
affine coordinate line. -/
public noncomputable def orderFourCayleyChartRadialHomotopy
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    ContinuousMap.Homotopy
      (A.orderFourCayleyChartSubOneCircleMap
        A.orderFourFillingRelationCayleyBaseValue
        (norm_pos_iff.mpr A.orderFourFillingRelationCayleyBaseValue_ne_zero)
        (by
          rw [A.orderFourFillingRelationCayleyBaseValue_norm]
          exact A.orderFourActualEllipticBoundaryBase.1.2.2))
      (A.orderFourCayleyChartSubOneCircleMap
        ((c : ℂ) * A.orderFourFillingRelationCayleyBaseValue)
        (by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
          exact mul_pos hc
            (norm_pos_iff.mpr A.orderFourFillingRelationCayleyBaseValue_ne_zero))
        (by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
          exact (mul_lt_mul_of_pos_right hc1
            (norm_pos_iff.mpr
              A.orderFourFillingRelationCayleyBaseValue_ne_zero)).trans (by
              rw [A.orderFourFillingRelationCayleyBaseValue_norm]
              simpa using A.orderFourActualEllipticBoundaryBase.1.2.2))) where
  toFun p :=
    ⟨ellipticChartFunction A.modular.sourceCoordinate.coordinate
          fuchsianTwoFixedPoint (A.orderFourAlignedCayleyRadialPoint c p) - 1,
      A.orderFourCayleyChartFunction_sub_one_ne_zero_neg_one
        (A.orderFourAlignedCayleyRadialPoint_norm_pos_lt hc hc1 p).1
        (A.orderFourAlignedCayleyRadialPoint_norm_pos_lt hc hc1 p).2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [continuous_iff_continuousAt]
    intro p
    have hnorm : ‖A.orderFourAlignedCayleyRadialPoint c p‖ < 1 :=
      (A.orderFourAlignedCayleyRadialPoint_norm_pos_lt hc hc1 p).2.trans
        A.starSeparation.orderFour.radius_lt_one
    exact ((ellipticChartFunction_analyticAt_of_norm_lt_one
      A.modular.sourceCoordinate.coordinate_holomorphic hnorm).continuousAt.comp
        (A.orderFourAlignedCayleyRadialPoint_continuous c).continuousAt).sub continuousAt_const
  map_zero_left t := by
    apply Subtype.ext
    change ellipticChartFunction A.modular.sourceCoordinate.coordinate
        fuchsianTwoFixedPoint
          (A.orderFourAlignedCayleyRadialPoint c (0, t)) - 1 =
      ellipticChartFunction A.modular.sourceCoordinate.coordinate
        fuchsianTwoFixedPoint
          (localDegreeCirclePoint
            A.orderFourFillingRelationCayleyBaseValue t) - 1
    simp [orderFourAlignedCayleyRadialPoint]
  map_one_left t := by
    apply Subtype.ext
    change ellipticChartFunction A.modular.sourceCoordinate.coordinate
        fuchsianTwoFixedPoint
          (A.orderFourAlignedCayleyRadialPoint c (1, t)) - 1 =
      ellipticChartFunction A.modular.sourceCoordinate.coordinate
          fuchsianTwoFixedPoint
        (localDegreeCirclePoint
          ((c : ℂ) * A.orderFourFillingRelationCayleyBaseValue) t) - 1
    congr 1
    simp [orderFourAlignedCayleyRadialPoint, localDegreeCirclePoint]
    ring

/-- On some nonzero Cayley circle, the order-four affine coordinate is connected through
nonzero values of norm less than one to its frozen-unit four-turn circle. -/
public theorem exists_orderFourCayleyBaseCoordinate_smallCircleHomotopy :
    ∃ (u : ℂ → ℂ) (a : ℂ)
      (ha : a ≠ 0)
      (hu : ContinuousOn u (closedBall (0 : ℂ) ‖a‖))
      (hune : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0)
      (hbound : ∀ z ∈ closedBall (0 : ℂ) ‖a‖,
        ‖a‖ ^ 4 * ‖u z‖ < ‖(-1 : ℂ)‖),
      (∀ t : unitInterval,
        ellipticChartFunction A.modular.sourceCoordinate.coordinate
            fuchsianTwoFixedPoint (localDegreeCirclePoint a t) - 1 =
          (factorizedLocalDegreeCircleTwoPunctures
            u 4 a (-1) ha hu hune hbound t).1) ∧
      Nonempty (ContinuousMap.Homotopy
        (factorizedLocalDegreeCircleTwoPunctures
          u 4 a (-1) ha hu hune hbound)
        (frozenLocalDegreeCircleTwoPunctures
          u 4 a (-1) ha hune hbound)) := by
  obtain ⟨u, hu, hu0, hfactor⟩ :=
    A.exists_orderFourCayleyRegularCoordinate_quarticUnit
  let G : ℂ → ℂ := fun z ↦
    ellipticChartFunction A.modular.sourceCoordinate.coordinate
      fuchsianTwoFixedPoint z - 1
  obtain ⟨a, ha, huc, hune, hfac, hbound⟩ :=
    exists_factorizationCircleData G u 4 (by norm_num) hu hu0 hfactor
  have hbound' : ∀ z ∈ closedBall (0 : ℂ) ‖a‖,
      ‖a‖ ^ 4 * ‖u z‖ < ‖(-1 : ℂ)‖ := by
    simpa using hbound
  refine ⟨u, a, ha, huc, hune, hbound', ?_, ?_⟩
  · intro t
    change G (localDegreeCirclePoint a t) =
      localDegreeCirclePoint a t ^ 4 * u (localDegreeCirclePoint a t)
    exact hfac (localDegreeCirclePoint a t) (by
      rw [mem_closedBall, dist_zero_right, localDegreeCirclePoint_norm])
  · exact ⟨exactLocalFactorizationCircleHomotopyTwoPunctures
      u 4 a (-1) ha huc hune hbound'⟩

/-- The small circle can be chosen as a positive radial rescaling of the actual Cayley circle. -/
public theorem exists_orderFourCayleyBaseCoordinate_alignedSmallCircleData :
    ∃ (u : ℂ → ℂ) (a : ℂ) (c : ℝ),
      0 < c ∧ c < 1 ∧
      a = (c : ℂ) * A.orderFourFillingRelationCayleyBaseValue ∧
      ContinuousOn u (closedBall (0 : ℂ) ‖a‖) ∧
      (∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0) ∧
      (∀ z ∈ closedBall (0 : ℂ) ‖a‖,
        ellipticChartFunction A.modular.sourceCoordinate.coordinate
          fuchsianTwoFixedPoint z - 1 = z ^ 4 * u z) ∧
      (∀ z ∈ closedBall (0 : ℂ) ‖a‖, ‖a‖ ^ 4 * ‖u z‖ < 1) := by
  let G : ℂ → ℂ := fun z ↦
    ellipticChartFunction A.modular.sourceCoordinate.coordinate
      fuchsianTwoFixedPoint z - 1
  obtain ⟨u, hu, hu0, hfactor⟩ :=
    A.exists_orderFourCayleyRegularCoordinate_quarticUnit
  let a₀ := A.orderFourFillingRelationCayleyBaseValue
  have ha₀ : a₀ ≠ 0 := A.orderFourFillingRelationCayleyBaseValue_ne_zero
  have ha₀norm : 0 < ‖a₀‖ := norm_pos_iff.mpr ha₀
  obtain ⟨b, hb, hblt, hub, huneb, hfacb, hboundb⟩ :=
    exists_factorizationCircleData_lt G u 4 (by norm_num) hu hu0 hfactor ‖a₀‖ ha₀norm
  let c : ℝ := ‖b‖ / ‖a₀‖
  have hc : 0 < c := div_pos (norm_pos_iff.mpr hb) ha₀norm
  have hc1 : c < 1 := (div_lt_one ha₀norm).mpr hblt
  let a : ℂ := (c : ℂ) * a₀
  have hanorm : ‖a‖ = ‖b‖ := by
    change ‖(c : ℂ) * a₀‖ = ‖b‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    change (‖b‖ / ‖a₀‖) * ‖a₀‖ = ‖b‖
    exact div_mul_cancel₀ _ ha₀norm.ne'
  refine ⟨u, a, c, hc, hc1, rfl, ?_, ?_, ?_, ?_⟩
  · simpa [hanorm] using hub
  · simpa [hanorm] using huneb
  · simpa [G, hanorm] using hfacb
  · simpa [hanorm] using hboundb

/-- The actual complete Cayley base circle is freely homotopic in the twice-punctured affine
line to a frozen-unit positive four-turn circle. -/
public theorem exists_orderFourActualCayleyBaseCoordinate_fourTurnHomotopy :
    ∃ (u : ℂ → ℂ) (a : ℂ)
      (ha : a ≠ 0)
      (hune : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0)
      (hbound : ∀ z ∈ closedBall (0 : ℂ) ‖a‖,
        ‖a‖ ^ 4 * ‖u z‖ < ‖(-1 : ℂ)‖),
      Nonempty (ContinuousMap.Homotopy
        (A.orderFourCayleyChartSubOneCircleMap
          A.orderFourFillingRelationCayleyBaseValue
          (norm_pos_iff.mpr A.orderFourFillingRelationCayleyBaseValue_ne_zero)
          (by
            rw [A.orderFourFillingRelationCayleyBaseValue_norm]
            exact A.orderFourActualEllipticBoundaryBase.1.2.2))
        (frozenLocalDegreeCircleTwoPunctures
          u 4 a (-1) ha hune hbound)) := by
  obtain ⟨u, a, c, hc, hc1, haeq, hu, hune, hfac, hbound⟩ :=
    A.exists_orderFourCayleyBaseCoordinate_alignedSmallCircleData
  subst a
  let a : ℂ := (c : ℂ) * A.orderFourFillingRelationCayleyBaseValue
  have ha : a ≠ 0 := by
    dsimp [a]
    exact mul_ne_zero (ofReal_ne_zero.mpr hc.ne')
      A.orderFourFillingRelationCayleyBaseValue_ne_zero
  have hbound' : ∀ z ∈ closedBall (0 : ℂ) ‖a‖,
      ‖a‖ ^ 4 * ‖u z‖ < ‖(-1 : ℂ)‖ := by
    simpa [a] using hbound
  have har : ‖a‖ < A.starSeparation.orderFour.radius := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    exact (mul_lt_mul_of_pos_right hc1
      (norm_pos_iff.mpr
        A.orderFourFillingRelationCayleyBaseValue_ne_zero)).trans (by
          rw [A.orderFourFillingRelationCayleyBaseValue_norm]
          simpa using A.orderFourActualEllipticBoundaryBase.1.2.2)
  have hsmall :
      A.orderFourCayleyChartSubOneCircleMap a (norm_pos_iff.mpr ha) har =
        factorizedLocalDegreeCircleTwoPunctures
          u 4 a (-1) ha hu hune hbound' := by
    ext t
    change ellipticChartFunction A.modular.sourceCoordinate.coordinate
        fuchsianTwoFixedPoint (localDegreeCirclePoint a t) - 1 =
      localDegreeCirclePoint a t ^ 4 * u (localDegreeCirclePoint a t)
    exact hfac _ (by
      rw [mem_closedBall, dist_zero_right, localDegreeCirclePoint_norm])
  let Hrad := A.orderFourCayleyChartRadialHomotopy c hc hc1
  have htarget :
      A.orderFourCayleyChartSubOneCircleMap
          ((c : ℂ) * A.orderFourFillingRelationCayleyBaseValue)
          (by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
            exact mul_pos hc
              (norm_pos_iff.mpr
                A.orderFourFillingRelationCayleyBaseValue_ne_zero))
          (by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
            exact (mul_lt_mul_of_pos_right hc1
              (norm_pos_iff.mpr
                A.orderFourFillingRelationCayleyBaseValue_ne_zero)).trans (by
                  rw [A.orderFourFillingRelationCayleyBaseValue_norm]
                  simpa using A.orderFourActualEllipticBoundaryBase.1.2.2)) =
        factorizedLocalDegreeCircleTwoPunctures
          u 4 a (-1) ha hu hune hbound' := by
    exact hsmall
  let Hlocal :=
    exactLocalFactorizationCircleHomotopyTwoPunctures
      u 4 a (-1) ha hu hune hbound'
  refine ⟨u, a, ha, hune, hbound', ?_⟩
  exact ⟨(Hrad.cast rfl htarget).trans Hlocal⟩

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
