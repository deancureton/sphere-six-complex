module

public import SphereSixComplex.Topology.PaperActualCuspBaseRelation
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# The actual cusp loop in the central family

The angular cusp loop has a concrete representative in the regular vector-bundle quotient.
Scaling that representative's fibre coordinate to zero gives a free homotopy to the zero-section
lift of its normalized base loop.  Keeping the trace of the moving basepoint turns this free
homotopy into an exact based-loop identity.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex

/-- Symmetry reverses composition in the path-homotopy groupoid. -/
public theorem homotopicQuotient_symm_trans
    {X : Type*} [TopologicalSpace X] {x y z : X}
    (p : Path.Homotopic.Quotient x y)
    (q : Path.Homotopic.Quotient y z) :
    (p.trans q).symm = q.symm.trans p.symm := by
  rcases Path.Homotopic.Quotient.mk_surjective p with ⟨p, rfl⟩
  rcases Path.Homotopic.Quotient.mk_surjective q with ⟨q, rfl⟩
  simpa only [← Path.Homotopic.Quotient.mk_trans,
    ← Path.Homotopic.Quotient.mk_symm] using
      congrArg Path.Homotopic.Quotient.mk (Path.trans_symm p q)

/-- Symmetry is involutive in the path-homotopy groupoid. -/
public theorem homotopicQuotient_symm_symm
    {X : Type*} [TopologicalSpace X] {x y : X}
    (p : Path.Homotopic.Quotient x y) : p.symm.symm = p := by
  rcases Path.Homotopic.Quotient.mk_surjective p with ⟨p, rfl⟩
  simpa only [← Path.Homotopic.Quotient.mk_symm] using
    congrArg Path.Homotopic.Quotient.mk (Path.symm_symm p)

/-- A free homotopy between two loops identifies the first loop with the second loop whiskered
by the trace of their common endpoint. -/
public theorem loopClass_eq_whiskered_of_freeHomotopy
    {X : Type*} [TopologicalSpace X] {x y : X}
    (L₀ : Path x x) (L₁ : Path y y)
    (H : ContinuousMap.Homotopy L₀.toContinuousMap L₁.toContinuousMap)
    (htrace :
      (H.evalAt 0).cast L₀.source.symm L₁.source.symm =
        (H.evalAt 1).cast L₀.target.symm L₁.target.symm) :
    Path.Homotopic.Quotient.mk L₀ =
      Path.Homotopic.Quotient.mk
        (((H.evalAt 0).cast L₀.source.symm L₁.source.symm).trans
          (L₁.trans
            ((H.evalAt 0).cast L₀.source.symm L₁.source.symm).symm)) := by
  let W₀ : Path x y :=
    (H.evalAt 0).cast L₀.source.symm L₁.source.symm
  let W₁ : Path x y :=
    (H.evalAt 1).cast L₀.target.symm L₁.target.symm
  have hraw := Path.Homotopic.map_trans_evalAt H (Path.id)
  have h := hraw.pathCast L₀.source.symm L₁.target.symm
  have hleft :
      (((Path.id.map L₀.continuous).trans (H.evalAt 1)).cast
        L₀.source.symm L₁.target.symm) = L₀.trans W₁ := by
    apply Path.ext
    funext t
    rfl
  have hright :
      (((H.evalAt 0).trans (Path.id.map L₁.continuous)).cast
        L₀.source.symm L₁.target.symm) = W₀.trans L₁ := by
    apply Path.ext
    funext t
    rfl
  rw [hleft, hright] at h
  have hq := Path.Homotopic.Quotient.eq.mpr h
  change W₀ = W₁ at htrace
  rw [← htrace] at hq
  simp only [Path.Homotopic.Quotient.mk_trans] at hq
  simp only [Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm]
  change Path.Homotopic.Quotient.mk L₀ =
    (Path.Homotopic.Quotient.mk W₀).trans
      ((Path.Homotopic.Quotient.mk L₁).trans
        (Path.Homotopic.Quotient.mk W₀).symm)
  calc
    Path.Homotopic.Quotient.mk L₀ =
        (Path.Homotopic.Quotient.mk L₀).trans
          (Path.Homotopic.Quotient.refl x) :=
      (Path.Homotopic.Quotient.trans_refl _).symm
    _ = (Path.Homotopic.Quotient.mk L₀).trans
        ((Path.Homotopic.Quotient.mk W₀).trans
          (Path.Homotopic.Quotient.mk W₀).symm) := by
      rw [Path.Homotopic.Quotient.trans_symm]
    _ = ((Path.Homotopic.Quotient.mk L₀).trans
          (Path.Homotopic.Quotient.mk W₀)).trans
        (Path.Homotopic.Quotient.mk W₀).symm := by
      rw [Path.Homotopic.Quotient.trans_assoc]
    _ = ((Path.Homotopic.Quotient.mk W₀).trans
          (Path.Homotopic.Quotient.mk L₁)).trans
        (Path.Homotopic.Quotient.mk W₀).symm := by
      rw [hq]
    _ = (Path.Homotopic.Quotient.mk W₀).trans
        ((Path.Homotopic.Quotient.mk L₁).trans
          (Path.Homotopic.Quotient.mk W₀).symm) :=
      Path.Homotopic.Quotient.trans_assoc _ _ _

end SphereSixComplex

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.Topology
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.GlobalTorusFamily
open CuspPeriodExpansion CuspPuncturedCollarBridge

variable (A : PaperAnalyticData)

/-- The actual cusp coordinate, regarded as a loop in the marked ordinary quotient base. -/
public noncomputable def actualCuspAngularMarkedBaseLoop :
    Path
      (A.puncturedBaseHomeomorphTwicePuncturedComplex.symm
        (A.centralFamilyCoordinate A.actualCuspCentralBase))
      (A.puncturedBaseHomeomorphTwicePuncturedComplex.symm
        (A.centralFamilyCoordinate A.actualCuspCentralBase)) :=
  A.actualCuspAngularCoordinateLoop.map
    A.puncturedBaseHomeomorphTwicePuncturedComplex.symm.continuous

/-- The same coordinate loop lifted along the literal zero section. -/
public noncomputable def actualCuspAngularZeroSectionLoop :
    Path
      (A.centralZeroSection
        (A.puncturedBaseHomeomorphTwicePuncturedComplex.symm
          (A.centralFamilyCoordinate A.actualCuspCentralBase)))
      (A.centralZeroSection
        (A.puncturedBaseHomeomorphTwicePuncturedComplex.symm
          (A.centralFamilyCoordinate A.actualCuspCentralBase))) :=
  A.actualCuspAngularMarkedBaseLoop.map A.centralZeroSection.continuous

/-- A regular-source representative of the actual cusp coordinate at time `t`. -/
public def actualCuspAngularRegularBasePoint (t : unitInterval) :
    RegularBase (U := A.paperTriangleUniformization) :=
  ⟨A.cuspCoordinate.lift (A.actualCuspAngularLiftPoint t).1.2,
    A.starCuspWitness.lift_regular
      (additiveCuspRadiusCover_halfPlane
        A.starCuspWitness.localWitness.radius_le (A.actualCuspAngularLiftPoint t))
      (A.actualCuspAngularLiftPoint t).2⟩

public theorem actualCuspAngularMarkedBaseLoop_apply (t : unitInterval) :
    A.actualCuspAngularMarkedBaseLoop t =
      regularBaseQuotientMap (U := A.paperTriangleUniformization)
        (A.actualCuspAngularRegularBasePoint t) := by
  apply A.puncturedBaseHomeomorphTwicePuncturedComplex.injective
  unfold actualCuspAngularMarkedBaseLoop
  change A.puncturedBaseHomeomorphTwicePuncturedComplex
      (A.puncturedBaseHomeomorphTwicePuncturedComplex.symm
        (A.actualCuspAngularCoordinateLoop t)) = _
  rw [A.puncturedBaseHomeomorphTwicePuncturedComplex.apply_symm_apply,
    A.puncturedBaseHomeomorphTwicePuncturedComplex_mk]
  apply Subtype.ext
  exact A.actualCuspAngularCoordinateLoop_apply t

/-- Pointwise zero-fibre representative of the actual cusp path. -/
public noncomputable def actualCuspAngularZeroCentralPoint
    (t : unitInterval) : A.CentralFamily :=
  actualPuncturedGlobalCuspPoint A.starCuspWitness
    (A.actualCuspAngularLiftPoint t).1.2
    (additiveCuspRadiusCover_halfPlane
      A.starCuspWitness.localWitness.radius_le (A.actualCuspAngularLiftPoint t))
    (A.actualCuspAngularLiftPoint t).2 0

public theorem actualCuspAngularZeroSectionLoop_apply (t : unitInterval) :
    A.actualCuspAngularZeroSectionLoop t =
      A.actualCuspAngularZeroCentralPoint t := by
  change A.centralZeroSection (A.actualCuspAngularMarkedBaseLoop t) = _
  rw [A.actualCuspAngularMarkedBaseLoop_apply]
  change puncturedGlobalZeroSection A.periods
      (regularBaseQuotientMap (U := A.paperTriangleUniformization)
        (A.actualCuspAngularRegularBasePoint t)) = _
  rw [puncturedGlobalZeroSection_mk]
  rfl

/-- Scale the actual cusp fibre coordinate linearly to zero. -/
public noncomputable def actualCuspAngularCentralZeroHomotopyValue
    (u t : unitInterval) : A.CentralFamily :=
  actualPuncturedGlobalCuspPoint A.starCuspWitness
    (A.actualCuspAngularLiftPoint t).1.2
    (additiveCuspRadiusCover_halfPlane
      A.starCuspWitness.localWitness.radius_le (A.actualCuspAngularLiftPoint t))
    (A.actualCuspAngularLiftPoint t).2
    ((1 - (u : ℝ)) • (A.actualCuspAngularLiftPoint t).1.1)

public theorem continuous_actualCuspAngularCentralZeroHomotopyValue :
    Continuous (fun p : unitInterval × unitInterval =>
      A.actualCuspAngularCentralZeroHomotopyValue p.1 p.2) := by
  change Continuous (fun p : unitInterval × unitInterval =>
    Quotient.mk _ (Quotient.mk _
      (A.actualCuspAngularRegularBasePoint p.2,
        (1 - (p.1 : ℝ)) • (A.actualCuspAngularLiftPoint p.2).1.1)))
  apply continuous_quot_mk.comp
  apply continuous_quot_mk.comp
  apply Continuous.prodMk
  · unfold actualCuspAngularRegularBasePoint
    apply Continuous.subtype_mk
    apply A.cuspCoordinate.lift_holomorphic.continuousOn.comp_continuous
    · unfold actualCuspAngularLiftPoint
      fun_prop
    · intro p
      exact additiveCuspRadiusCover_halfPlane
        A.starCuspWitness.localWitness.radius_le (A.actualCuspAngularLiftPoint p.2)
  · unfold actualCuspAngularLiftPoint
    fun_prop

public theorem actualCuspAngularCentralZeroHomotopyValue_zero
    (t : unitInterval) :
    A.actualCuspAngularCentralZeroHomotopyValue 0 t =
      A.actualCuspAngularCentralLoop t := by
  unfold actualCuspAngularCentralZeroHomotopyValue
  unfold actualCuspAngularCentralLoop actualCuspAngularProjectedLoop
  change actualPuncturedGlobalCuspPoint A.starCuspWitness
      (A.actualCuspAngularLiftPoint t).1.2 _ _
      ((1 - ((0 : unitInterval) : ℝ)) •
        (A.actualCuspAngularLiftPoint t).1.1) =
    A.actualCuspOverlapToCentral
      (A.actualCuspBoundaryProjection (A.actualCuspAngularLiftPoint t))
  rw [A.actualCuspOverlapToCentral_boundaryProjection]
  change actualPuncturedGlobalCuspPoint A.starCuspWitness
      (A.actualCuspAngularLiftPoint t).1.2 _ _
      ((1 - (0 : ℝ)) • (A.actualCuspAngularLiftPoint t).1.1) =
    additiveCuspCoverToGlobal A.starCuspWitness
      (A.actualCuspAngularLiftPoint t)
  simp only [sub_zero, one_smul]
  rfl

public theorem actualCuspAngularCentralZeroHomotopyValue_one
    (t : unitInterval) :
    A.actualCuspAngularCentralZeroHomotopyValue 1 t =
      A.actualCuspAngularZeroSectionLoop t := by
  rw [A.actualCuspAngularZeroSectionLoop_apply]
  unfold actualCuspAngularCentralZeroHomotopyValue
    actualCuspAngularZeroCentralPoint
  change actualPuncturedGlobalCuspPoint A.starCuspWitness
      (A.actualCuspAngularLiftPoint t).1.2 _ _
      ((1 - (1 : ℝ)) • (A.actualCuspAngularLiftPoint t).1.1) = _
  simp only [sub_self, zero_smul]

/-- The free homotopy from the actual cusp loop to its zero-section projection. -/
public noncomputable def actualCuspAngularCentralZeroHomotopy :
    ContinuousMap.Homotopy A.actualCuspAngularCentralLoop.toContinuousMap
      A.actualCuspAngularZeroSectionLoop.toContinuousMap where
  toFun p := A.actualCuspAngularCentralZeroHomotopyValue p.1 p.2
  continuous_toFun := A.continuous_actualCuspAngularCentralZeroHomotopyValue
  map_zero_left t := A.actualCuspAngularCentralZeroHomotopyValue_zero t
  map_one_left t := A.actualCuspAngularCentralZeroHomotopyValue_one t

/-- The moving basepoint of the fibre-scaling homotopy is the explicit vertical segment from
the selected cusp point to the zero section over the same ordinary base point. -/
public noncomputable def actualCuspToZeroSectionPath :
    Path A.actualCuspCentralBase
      (A.centralZeroSection
        (A.puncturedBaseHomeomorphTwicePuncturedComplex.symm
          (A.centralFamilyCoordinate A.actualCuspCentralBase))) :=
  ((A.actualCuspAngularCentralZeroHomotopy).evalAt 0).cast
    A.actualCuspAngularCentralLoop.source.symm
    A.actualCuspAngularZeroSectionLoop.source.symm

public theorem actualCuspAngularCentralZeroHomotopy_trace :
    ((A.actualCuspAngularCentralZeroHomotopy).evalAt 0).cast
        A.actualCuspAngularCentralLoop.source.symm
        A.actualCuspAngularZeroSectionLoop.source.symm =
      ((A.actualCuspAngularCentralZeroHomotopy).evalAt 1).cast
        A.actualCuspAngularCentralLoop.target.symm
        A.actualCuspAngularZeroSectionLoop.target.symm := by
  apply Path.ext
  funext u
  change A.actualCuspAngularCentralZeroHomotopyValue u 0 =
    A.actualCuspAngularCentralZeroHomotopyValue u 1
  unfold actualCuspAngularCentralZeroHomotopyValue
  have hshift := puncturedGlobalCuspPoint_shift
    A.cuspCoordinate
    A.actualCuspBoundaryCoverBase.1.2
    (additiveCuspRadiusCover_halfPlane
      A.starCuspWitness.localWitness.radius_le A.actualCuspBoundaryCoverBase)
    (A.starCuspWitness.lift_regular
      (additiveCuspRadiusCover_halfPlane
        A.starCuspWitness.localWitness.radius_le A.actualCuspBoundaryCoverBase)
      A.actualCuspBoundaryCoverBase.2)
    (A.starCuspWitness.lift_regular
      (additiveCuspRadiusCover_halfPlane
        A.starCuspWitness.localWitness.radius_le (A.actualCuspAngularLiftPoint 1))
      (A.actualCuspAngularLiftPoint 1).2)
    ((1 - (u : ℝ)) • A.actualCuspBoundaryCoverBase.1.1)
  unfold actualPuncturedGlobalCuspPoint
  simpa [actualCuspAngularLiftPoint] using hshift.symm

/-- In the actual central family, the selected cusp loop is the zero-section coordinate loop
whiskered by the literal vertical contraction of its fibre coordinate. -/
public theorem actualCuspAngularCentralLoop_class_eq_zeroSectionWhisker :
    Path.Homotopic.Quotient.mk A.actualCuspAngularCentralLoop =
      Path.Homotopic.Quotient.mk
        (A.actualCuspToZeroSectionPath.trans
          (A.actualCuspAngularZeroSectionLoop.trans
            A.actualCuspToZeroSectionPath.symm)) := by
  exact loopClass_eq_whiskered_of_freeHomotopy
    A.actualCuspAngularCentralLoop A.actualCuspAngularZeroSectionLoop
    A.actualCuspAngularCentralZeroHomotopy
    (actualCuspAngularCentralZeroHomotopy_trace A)

/-! ## Rebase the central loop at the marked ordinary basepoint -/

/-- The coherent base path from `1/2` to the actual exterior cusp coordinate. -/
public noncomputable def actualCuspCommonCoordinateWhisker :
    Path twicePuncturedComplexBasepoint
      (A.centralFamilyCoordinate A.actualCuspCentralBase) :=
  paperStandardExteriorBridge.trans A.actualCuspExteriorTwiceWhisker

/-- Insert the marked ordinary base into the central family along its zero section. -/
public noncomputable def markedBaseToCentralZeroSection :
    C(TwicePuncturedComplex, A.CentralFamily) :=
  A.centralZeroSection.comp
    (⟨A.puncturedBaseHomeomorphTwicePuncturedComplex.symm,
      A.puncturedBaseHomeomorphTwicePuncturedComplex.symm.continuous⟩ :
      C(TwicePuncturedComplex,
        PuncturedOrbifoldBase (U := A.paperTriangleUniformization)))

@[simp]
public theorem markedBaseToCentralZeroSection_basepoint :
    A.markedBaseToCentralZeroSection twicePuncturedComplexBasepoint =
      A.centralZeroSection A.markedPuncturedBasepoint := rfl

/-- The common coordinate whisker, lifted along the zero section. -/
public noncomputable def actualCuspCommonZeroSectionWhisker :
    Path (A.centralZeroSection A.markedPuncturedBasepoint)
      (A.centralZeroSection
        (A.puncturedBaseHomeomorphTwicePuncturedComplex.symm
          (A.centralFamilyCoordinate A.actualCuspCentralBase))) :=
  A.actualCuspCommonCoordinateWhisker.map
    A.markedBaseToCentralZeroSection.continuous

/-- The actual common-base coordinate loop lifted along the zero section. -/
public noncomputable def actualCuspCommonZeroSectionLoop :
    Path (A.centralZeroSection A.markedPuncturedBasepoint)
      (A.centralZeroSection A.markedPuncturedBasepoint) :=
  A.actualCuspCommonCoordinateLoop.map
    A.markedBaseToCentralZeroSection.continuous

public theorem actualCuspAngularZeroSectionLoop_eq_map :
    A.actualCuspAngularZeroSectionLoop =
      A.actualCuspAngularCoordinateLoop.map
        A.markedBaseToCentralZeroSection.continuous := by
  apply Path.ext
  funext t
  rfl

/-- The zero-section lift of the common coordinate loop is its explicit whiskered form. -/
public theorem actualCuspCommonZeroSectionLoop_class_eq_whisker :
    Path.Homotopic.Quotient.mk A.actualCuspCommonZeroSectionLoop =
      Path.Homotopic.Quotient.mk
        (A.actualCuspCommonZeroSectionWhisker.trans
          (A.actualCuspAngularZeroSectionLoop.trans
            A.actualCuspCommonZeroSectionWhisker.symm)) := by
  change Path.Homotopic.Quotient.mk
      (A.actualCuspCommonCoordinateLoop.map
        A.markedBaseToCentralZeroSection.continuous) =
    Path.Homotopic.Quotient.mk
      ((A.actualCuspCommonCoordinateWhisker.map
          A.markedBaseToCentralZeroSection.continuous).trans
        ((A.actualCuspAngularCoordinateLoop.map
            A.markedBaseToCentralZeroSection.continuous).trans
          (A.actualCuspCommonCoordinateWhisker.map
            A.markedBaseToCentralZeroSection.continuous).symm))
  unfold actualCuspCommonCoordinateLoop actualCuspCommonCoordinateWhisker
    actualCuspExteriorWhiskeredTwiceLoop
  simp only [Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm, Path.map_trans, ← Path.map_symm]
  rw [homotopicQuotient_symm_trans]
  simp only [Path.Homotopic.Quotient.trans_assoc]

public theorem markedBaseToCentralZeroSection_map_zero :
    FundamentalGroup.map A.markedBaseToCentralZeroSection
        twicePuncturedComplexBasepoint
        TwicePuncturedComplex.zeroMeridianClass =
      A.markedZeroCentralMeridianClass := by
  rw [A.markedZeroCentralMeridianClass_eq_pathLoopClass]
  unfold TwicePuncturedComplex.zeroMeridianClass
  rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]
  apply congrArg Path.Homotopic.Quotient.mk
  apply Path.ext
  funext t
  rfl

public theorem markedBaseToCentralZeroSection_map_one :
    FundamentalGroup.map A.markedBaseToCentralZeroSection
        twicePuncturedComplexBasepoint
        TwicePuncturedComplex.oneMeridianClass =
      A.markedOneCentralMeridianClass := by
  rw [A.markedOneCentralMeridianClass_eq_pathLoopClass]
  unfold TwicePuncturedComplex.oneMeridianClass
  rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]
  apply congrArg Path.Homotopic.Quotient.mk
  apply Path.ext
  funext t
  rfl

/-- The planar pair-of-pants relation, lifted into the actual central family along the literal
zero section. -/
public theorem actualCuspCommonZeroSectionLoop_class_eq_finiteProduct :
    Path.Homotopic.Quotient.mk A.actualCuspCommonZeroSectionLoop =
      A.markedZeroCentralMeridianClass⁻¹ *
        A.markedOneCentralMeridianClass⁻¹ := by
  have h := congrArg
    (FundamentalGroup.map A.markedBaseToCentralZeroSection
      twicePuncturedComplexBasepoint)
    A.actualCuspCommonCoordinateLoop_class_eq_finiteProduct
  rw [FundamentalGroup.map_apply, map_mul, map_inv, map_inv,
    A.markedBaseToCentralZeroSection_map_zero,
    A.markedBaseToCentralZeroSection_map_one] at h
  change (Path.Homotopic.Quotient.mk
      A.actualCuspCommonCoordinateLoop).map
        A.markedBaseToCentralZeroSection =
    A.markedZeroCentralMeridianClass⁻¹ *
      A.markedOneCentralMeridianClass⁻¹
  convert h using 1
  rfl

/-- The path from the marked zero-section basepoint to the selected actual cusp point. -/
public noncomputable def actualCuspMarkedCentralWhisker :
    Path (A.centralZeroSection A.markedPuncturedBasepoint)
      A.actualCuspCentralBase :=
  A.actualCuspCommonZeroSectionWhisker.trans A.actualCuspToZeroSectionPath.symm

/-- The actual angular cusp loop, now based at the marked zero-section point. -/
public noncomputable def actualCuspMarkedCentralLoop :
    Path (A.centralZeroSection A.markedPuncturedBasepoint)
      (A.centralZeroSection A.markedPuncturedBasepoint) :=
  A.actualCuspMarkedCentralWhisker.trans
    (A.actualCuspAngularCentralLoop.trans A.actualCuspMarkedCentralWhisker.symm)

/-- Fibre contraction removes the vertical portion of the common whisker, leaving precisely the
zero-section lift of the normalized common-base loop. -/
public theorem actualCuspMarkedCentralLoop_class_eq_zeroSectionLoop :
    Path.Homotopic.Quotient.mk A.actualCuspMarkedCentralLoop =
      Path.Homotopic.Quotient.mk A.actualCuspCommonZeroSectionLoop := by
  rw [A.actualCuspCommonZeroSectionLoop_class_eq_whisker]
  have hcusp := A.actualCuspAngularCentralLoop_class_eq_zeroSectionWhisker
  unfold actualCuspMarkedCentralLoop actualCuspMarkedCentralWhisker
  simp only [Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm]
  simp only [Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm] at hcusp
  rw [hcusp]
  rw [homotopicQuotient_symm_trans]
  simp only [Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc
      (Path.Homotopic.Quotient.mk A.actualCuspToZeroSectionPath).symm
      (Path.Homotopic.Quotient.mk A.actualCuspToZeroSectionPath),
    Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]
  rw [homotopicQuotient_symm_symm]
  rw [← Path.Homotopic.Quotient.trans_assoc
      (Path.Homotopic.Quotient.mk A.actualCuspToZeroSectionPath).symm
      (Path.Homotopic.Quotient.mk A.actualCuspToZeroSectionPath)
      (Path.Homotopic.Quotient.mk A.actualCuspCommonZeroSectionWhisker).symm,
    Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]

/-- At the actual marked central basepoint, the cusp loop is the product of the two
counterclockwise finite meridians. -/
public theorem actualCuspMarkedCentralLoop_class_eq_finiteProduct :
    Path.Homotopic.Quotient.mk A.actualCuspMarkedCentralLoop =
      A.markedZeroCentralMeridianClass⁻¹ *
        A.markedOneCentralMeridianClass⁻¹ := by
  rw [A.actualCuspMarkedCentralLoop_class_eq_zeroSectionLoop,
    A.actualCuspCommonZeroSectionLoop_class_eq_finiteProduct]

end SphereSixComplex.Geometry.PaperAnalyticData

end
