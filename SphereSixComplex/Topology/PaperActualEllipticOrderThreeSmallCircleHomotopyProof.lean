module

public import SphereSixComplex.Topology.ExactLocalFactorizationCircleHomotopy
public import SphereSixComplex.Topology.PaperActualEllipticOrderThreeBaseCoordinateLocalDegreeProof

/-!
# The small order-three base-coordinate circle

The cubic analytic branch supplies a sufficiently small Cayley circle whose affine image is
freely homotopic, inside the twice-punctured target, to a positive three-turn circle.
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

/-- Every noncentral Cayley point in the selected order-three collar has affine coordinate
different from both punctures. -/
public theorem orderThreeCayleyChartFunction_ne_zero_one
    {w : ℂ} (hw0 : 0 < ‖w‖)
    (hwr : ‖w‖ < A.starSeparation.orderThree.radius) :
    ellipticChartFunction A.modular.sourceCoordinate.coordinate
        fuchsianOneFixedPoint w ≠ 0 ∧
      ellipticChartFunction A.modular.sourceCoordinate.coordinate
        fuchsianOneFixedPoint w ≠ 1 := by
  have hw1 : ‖w‖ < 1 :=
    hwr.trans A.starSeparation.orderThree.radius_lt_one
  let z : UpperHalfPlane :=
    UpperHalfPlane.ofComplex (cayleyRawInverse fuchsianOneFixedPoint w)
  have hcay :
      ((orderThreeCayleyHomeomorph z :
        SphereSixComplex.Geometry.EllipticLocalCoordinates.ComplexUnitDisc) : ℂ) = w := by
    exact cayleyCoordinate_rawInverse hw1
  have hzreg : IsRegularBasePoint
      (U := A.modular.modularParameter.toTriangleUniformization) z := by
    exact A.starSeparation.orderThree.sourceData.1 z
      (by simpa [hcay] using hw0) (by simpa [hcay] using hwr)
  have hmem := (A.regularCoordinate ⟨z, hzreg⟩).property
  simp only [RegularCoordinateBase, Set.mem_compl_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or] at hmem
  simpa [ellipticChartFunction, regularCoordinate, z] using hmem

public theorem orderThreeFillingRelationCayleyBaseValue_norm :
    ‖A.orderThreeFillingRelationCayleyBaseValue‖ =
      (A.orderThreeActualEllipticBoundaryBase.1 : ℝ) := by
  rw [orderThreeFillingRelationCayleyBaseValue, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos A.orderThreeActualEllipticBoundaryBase.1.2.1]
  rw [Circle.norm_coe, mul_one]

/-- The affine coordinate of a positive Cayley circle contained in the selected collar. -/
public noncomputable def orderThreeCayleyChartCircleMap
    (a : ℂ) (ha0 : 0 < ‖a‖)
    (har : ‖a‖ < A.starSeparation.orderThree.radius) :
    C(unitInterval, TwoPunctureComplement (1 : ℂ)) where
  toFun t :=
    ⟨ellipticChartFunction A.modular.sourceCoordinate.coordinate
        fuchsianOneFixedPoint (localDegreeCirclePoint a t),
      A.orderThreeCayleyChartFunction_ne_zero_one
        (by simpa [localDegreeCirclePoint_norm] using ha0)
        (by simpa [localDegreeCirclePoint_norm] using har)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [continuous_iff_continuousAt]
    intro t
    have hnorm : ‖localDegreeCirclePoint a t‖ < 1 :=
      (by simpa [localDegreeCirclePoint_norm] using
        har.trans A.starSeparation.orderThree.radius_lt_one)
    simpa [Function.comp_def] using
      (ellipticChartFunction_analyticAt_of_norm_lt_one
        A.modular.sourceCoordinate.coordinate_holomorphic hnorm).continuousAt.comp
          (localDegreeCirclePoint_continuous a).continuousAt

/-- The straight positive rescaling from the actual Cayley circle to a smaller aligned circle. -/
public def orderThreeAlignedCayleyRadialPoint (c : ℝ)
    (p : unitInterval × unitInterval) : ℂ :=
  (((1 - (p.1 : ℝ)) + (p.1 : ℝ) * c : ℝ) : ℂ) *
    localDegreeCirclePoint A.orderThreeFillingRelationCayleyBaseValue p.2

public theorem orderThreeAlignedCayleyRadialPoint_continuous (c : ℝ) :
    Continuous (A.orderThreeAlignedCayleyRadialPoint c) := by
  unfold orderThreeAlignedCayleyRadialPoint localDegreeCirclePoint
  fun_prop

public theorem orderThreeAlignedCayleyRadialPoint_norm_pos_lt
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (p : unitInterval × unitInterval) :
    0 < ‖A.orderThreeAlignedCayleyRadialPoint c p‖ ∧
      ‖A.orderThreeAlignedCayleyRadialPoint c p‖ <
        A.starSeparation.orderThree.radius := by
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
  have hbase0 : 0 < ‖A.orderThreeFillingRelationCayleyBaseValue‖ :=
    norm_pos_iff.mpr A.orderThreeFillingRelationCayleyBaseValue_ne_zero
  have hbaser : ‖A.orderThreeFillingRelationCayleyBaseValue‖ <
      A.starSeparation.orderThree.radius := by
    rw [A.orderThreeFillingRelationCayleyBaseValue_norm]
    exact A.orderThreeActualEllipticBoundaryBase.1.2.2
  rw [orderThreeAlignedCayleyRadialPoint, norm_mul,
    localDegreeCirclePoint_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hd0]
  exact ⟨mul_pos hd0 hbase0,
    (mul_le_of_le_one_left hbase0.le hd1).trans_lt hbaser⟩

/-- Radial shrinking of the complete Cayley base circle, already mapped to the twice-punctured
affine coordinate line. -/
public noncomputable def orderThreeCayleyChartRadialHomotopy
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    ContinuousMap.Homotopy
      (A.orderThreeCayleyChartCircleMap
        A.orderThreeFillingRelationCayleyBaseValue
        (norm_pos_iff.mpr A.orderThreeFillingRelationCayleyBaseValue_ne_zero)
        (by
          rw [A.orderThreeFillingRelationCayleyBaseValue_norm]
          exact A.orderThreeActualEllipticBoundaryBase.1.2.2))
      (A.orderThreeCayleyChartCircleMap
        ((c : ℂ) * A.orderThreeFillingRelationCayleyBaseValue)
        (by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
          exact mul_pos hc
            (norm_pos_iff.mpr A.orderThreeFillingRelationCayleyBaseValue_ne_zero))
        (by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
          exact (mul_lt_mul_of_pos_right hc1
            (norm_pos_iff.mpr
              A.orderThreeFillingRelationCayleyBaseValue_ne_zero)).trans (by
              rw [A.orderThreeFillingRelationCayleyBaseValue_norm]
              simpa using A.orderThreeActualEllipticBoundaryBase.1.2.2))) where
  toFun p :=
    ⟨ellipticChartFunction A.modular.sourceCoordinate.coordinate
        fuchsianOneFixedPoint (A.orderThreeAlignedCayleyRadialPoint c p),
      A.orderThreeCayleyChartFunction_ne_zero_one
        (A.orderThreeAlignedCayleyRadialPoint_norm_pos_lt hc hc1 p).1
        (A.orderThreeAlignedCayleyRadialPoint_norm_pos_lt hc hc1 p).2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [continuous_iff_continuousAt]
    intro p
    have hnorm : ‖A.orderThreeAlignedCayleyRadialPoint c p‖ < 1 :=
      (A.orderThreeAlignedCayleyRadialPoint_norm_pos_lt hc hc1 p).2.trans
        A.starSeparation.orderThree.radius_lt_one
    simpa [Function.comp_def] using
      (ellipticChartFunction_analyticAt_of_norm_lt_one
        A.modular.sourceCoordinate.coordinate_holomorphic hnorm).continuousAt.comp
          (A.orderThreeAlignedCayleyRadialPoint_continuous c).continuousAt
  map_zero_left t := by
    apply Subtype.ext
    change ellipticChartFunction A.modular.sourceCoordinate.coordinate
        fuchsianOneFixedPoint
          (A.orderThreeAlignedCayleyRadialPoint c (0, t)) =
      ellipticChartFunction A.modular.sourceCoordinate.coordinate
        fuchsianOneFixedPoint
          (localDegreeCirclePoint
            A.orderThreeFillingRelationCayleyBaseValue t)
    simp [orderThreeAlignedCayleyRadialPoint]
  map_one_left t := by
    apply Subtype.ext
    change ellipticChartFunction A.modular.sourceCoordinate.coordinate
        fuchsianOneFixedPoint
          (A.orderThreeAlignedCayleyRadialPoint c (1, t)) =
      ellipticChartFunction A.modular.sourceCoordinate.coordinate
          fuchsianOneFixedPoint
        (localDegreeCirclePoint
          ((c : ℂ) * A.orderThreeFillingRelationCayleyBaseValue) t)
    congr 1
    simp [orderThreeAlignedCayleyRadialPoint, localDegreeCirclePoint]
    ring

/-- On some nonzero Cayley circle, the order-three affine coordinate is connected through
nonzero values of norm less than one to its frozen-unit three-turn circle. -/
public theorem exists_orderThreeCayleyBaseCoordinate_smallCircleHomotopy :
    ∃ (u : ℂ → ℂ) (a : ℂ)
      (ha : a ≠ 0)
      (hu : ContinuousOn u (closedBall (0 : ℂ) ‖a‖))
      (hune : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0)
      (hbound : ∀ z ∈ closedBall (0 : ℂ) ‖a‖,
        ‖a‖ ^ 3 * ‖u z‖ < ‖(1 : ℂ)‖),
      (∀ t : unitInterval,
        ellipticChartFunction A.modular.sourceCoordinate.coordinate
            fuchsianOneFixedPoint (localDegreeCirclePoint a t) =
          (factorizedLocalDegreeCircleTwoPunctures
            u 3 a 1 ha hu hune hbound t).1) ∧
      Nonempty (ContinuousMap.Homotopy
        (factorizedLocalDegreeCircleTwoPunctures
          u 3 a 1 ha hu hune hbound)
        (frozenLocalDegreeCircleTwoPunctures
          u 3 a 1 ha hune hbound)) := by
  obtain ⟨u, hu, hu0, hfactor⟩ :=
    A.exists_orderThreeCayleyRegularCoordinate_cubicUnit
  let G : ℂ → ℂ :=
    ellipticChartFunction A.modular.sourceCoordinate.coordinate
      fuchsianOneFixedPoint
  obtain ⟨a, ha, huc, hune, hfac, hbound⟩ :=
    exists_cubicFactorizationCircleData G u hu hu0 hfactor
  have hbound' : ∀ z ∈ closedBall (0 : ℂ) ‖a‖,
      ‖a‖ ^ 3 * ‖u z‖ < ‖(1 : ℂ)‖ := by
    simpa using hbound
  refine ⟨u, a, ha, huc, hune, hbound', ?_, ?_⟩
  · intro t
    change G (localDegreeCirclePoint a t) =
      localDegreeCirclePoint a t ^ 3 * u (localDegreeCirclePoint a t)
    exact hfac (localDegreeCirclePoint a t) (by
      rw [mem_closedBall, dist_zero_right, localDegreeCirclePoint_norm])
  · exact ⟨exactLocalFactorizationCircleHomotopyTwoPunctures
      u 3 a 1 ha huc hune hbound'⟩

/-- The small circle can be chosen as a positive radial rescaling of the actual Cayley circle. -/
public theorem exists_orderThreeCayleyBaseCoordinate_alignedSmallCircleData :
    ∃ (u : ℂ → ℂ) (a : ℂ) (c : ℝ),
      0 < c ∧ c < 1 ∧
      a = (c : ℂ) * A.orderThreeFillingRelationCayleyBaseValue ∧
      ContinuousOn u (closedBall (0 : ℂ) ‖a‖) ∧
      (∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0) ∧
      (∀ z ∈ closedBall (0 : ℂ) ‖a‖,
        ellipticChartFunction A.modular.sourceCoordinate.coordinate
          fuchsianOneFixedPoint z = z ^ 3 * u z) ∧
      (∀ z ∈ closedBall (0 : ℂ) ‖a‖, ‖a‖ ^ 3 * ‖u z‖ < 1) := by
  let G : ℂ → ℂ :=
    ellipticChartFunction A.modular.sourceCoordinate.coordinate
      fuchsianOneFixedPoint
  obtain ⟨u, hu, hu0, hfactor⟩ :=
    A.exists_orderThreeCayleyRegularCoordinate_cubicUnit
  let a₀ := A.orderThreeFillingRelationCayleyBaseValue
  have ha₀ : a₀ ≠ 0 := A.orderThreeFillingRelationCayleyBaseValue_ne_zero
  have ha₀norm : 0 < ‖a₀‖ := norm_pos_iff.mpr ha₀
  obtain ⟨b, hb, hblt, hub, huneb, hfacb, hboundb⟩ :=
    exists_cubicFactorizationCircleData_lt G u hu hu0 hfactor ‖a₀‖ ha₀norm
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
line to a frozen-unit positive three-turn circle. -/
public theorem exists_orderThreeActualCayleyBaseCoordinate_threeTurnHomotopy :
    ∃ (u : ℂ → ℂ) (a : ℂ)
      (ha : a ≠ 0)
      (hune : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0)
      (hbound : ∀ z ∈ closedBall (0 : ℂ) ‖a‖,
        ‖a‖ ^ 3 * ‖u z‖ < ‖(1 : ℂ)‖),
      Nonempty (ContinuousMap.Homotopy
        (A.orderThreeCayleyChartCircleMap
          A.orderThreeFillingRelationCayleyBaseValue
          (norm_pos_iff.mpr A.orderThreeFillingRelationCayleyBaseValue_ne_zero)
          (by
            rw [A.orderThreeFillingRelationCayleyBaseValue_norm]
            exact A.orderThreeActualEllipticBoundaryBase.1.2.2))
        (frozenLocalDegreeCircleTwoPunctures
          u 3 a 1 ha hune hbound)) := by
  obtain ⟨u, a, c, hc, hc1, haeq, hu, hune, hfac, hbound⟩ :=
    A.exists_orderThreeCayleyBaseCoordinate_alignedSmallCircleData
  subst a
  let a : ℂ := (c : ℂ) * A.orderThreeFillingRelationCayleyBaseValue
  have ha : a ≠ 0 := by
    dsimp [a]
    exact mul_ne_zero (ofReal_ne_zero.mpr hc.ne')
      A.orderThreeFillingRelationCayleyBaseValue_ne_zero
  have hbound' : ∀ z ∈ closedBall (0 : ℂ) ‖a‖,
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
      rw [mem_closedBall, dist_zero_right, localDegreeCirclePoint_norm])
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
  let Hlocal :=
    exactLocalFactorizationCircleHomotopyTwoPunctures
      u 3 a 1 ha hu hune hbound'
  refine ⟨u, a, ha, hune, hbound', ?_⟩
  exact ⟨(Hrad.cast rfl htarget).trans Hlocal⟩

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
