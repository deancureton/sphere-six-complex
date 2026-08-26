module

public import SphereSixComplex.Topology.PaperGeometricCentralPeripheral
public import SphereSixComplex.Topology.PaperCentralFundamentalGroupGeneration

/-!
# Geometric monodromy in the actual central family

The selected cusp additive coordinate gives a literal path in the regular torus family.  Its
endpoint is the `g₀` deck translate, so the actual angular cusp loop has the prescribed outer
triangle-group monodromy without any universal-cover marking.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.Topology SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.LatticeData
open SphereSixComplex.Geometry.ComplexTorus SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open CuspPeriodExpansion CuspPuncturedCollarBridge
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

variable (A : PaperAnalyticData)

/-- The chosen actual cusp point before either of the two central-family quotients. -/
public def actualCuspRegularCoverPoint :
    RegularBase (U := A.paperTriangleUniformization) × ComplexTwoSpace :=
  (A.actualCuspAngularRegularBasePoint 0, A.actualCuspBoundaryCoverBase.1.1)

/-- The same point after the varying period-lattice quotient. -/
public noncomputable def actualCuspRegularRepresentative : RegularTotalSpace A.periods :=
  regularFamilyCoverProjection A.periods A.actualCuspRegularCoverPoint

/-- The chosen regular-family representative projects to the actual cusp point. -/
public theorem actualCuspRegularRepresentative_projects :
    regularFamilyQuotientMap A.periods A.actualCuspRegularRepresentative =
      A.actualCuspCentralBase := by
  have hpoint :
      ((additiveCuspBundleHomeomorph A.starCuspWitness
        A.actualCuspBoundaryCoverBase).1 :
          RegularBase (U := A.paperTriangleUniformization) × ComplexTwoSpace) =
        A.actualCuspRegularCoverPoint := by
    unfold actualCuspRegularCoverPoint actualCuspAngularRegularBasePoint
    apply Prod.ext
    · apply Subtype.ext
      change A.cuspCoordinate.lift A.actualCuspBoundaryCoverBase.1.2 =
        A.cuspCoordinate.lift (A.actualCuspAngularLiftPoint 0).1.2
      rw [A.actualCuspAngularLiftPoint_zero]
    · rfl
  calc
    _ = additiveCuspCoverToGlobal A.starCuspWitness
        A.actualCuspBoundaryCoverBase := by
      symm
      rw [additiveCuspCoverToGlobal_eq_quotientProjections]
      change regularFamilyQuotientMap A.periods
          (regularFamilyCoverProjection A.periods
            ((additiveCuspBundleHomeomorph A.starCuspWitness
              A.actualCuspBoundaryCoverBase).1 :
                RegularBase (U := A.paperTriangleUniformization) × ComplexTwoSpace)) = _
      rw [hpoint]
      rfl
    _ = A.actualCuspOverlapToCentral
        (A.actualCuspBoundaryProjection A.actualCuspBoundaryCoverBase) :=
      (A.actualCuspOverlapToCentral_boundaryProjection
        A.actualCuspBoundaryCoverBase).symm
    _ = A.actualCuspCentralBase := by
      rw [A.actualCuspBoundaryCoverBase_projects]
      rfl

/-- The literal regular-family lift of the actual angular cusp path. -/
public noncomputable def actualCuspRegularDeckPathPoint (t : unitInterval) :
    RegularTotalSpace A.periods :=
  regularFamilyCoverProjection A.periods
    (A.actualCuspAngularRegularBasePoint t, A.actualCuspBoundaryCoverBase.1.1)

public theorem continuous_actualCuspRegularDeckPathPoint :
    Continuous A.actualCuspRegularDeckPathPoint := by
  apply (regularFamilyCoverProjection A.periods).continuous.comp
  apply Continuous.prodMk
  · unfold actualCuspAngularRegularBasePoint actualCuspAngularLiftPoint
    apply Continuous.subtype_mk
    apply A.cuspCoordinate.lift_holomorphic.continuousOn.comp_continuous
    · fun_prop
    · intro t
      exact additiveCuspRadiusCover_halfPlane
        A.starCuspWitness.localWitness.radius_le (A.actualCuspAngularLiftPoint t)
  · exact continuous_const

@[simp]
public theorem actualCuspRegularDeckPathPoint_zero :
    A.actualCuspRegularDeckPathPoint 0 = A.actualCuspRegularRepresentative := by
  rfl

/-- The endpoint of the literal cusp lift is exactly the parabolic `g₀` deck translate. -/
public theorem actualCuspRegularDeckPathPoint_one :
    A.actualCuspRegularDeckPathPoint 1 =
      regularFamilyDeckMap A.periods g₀ A.actualCuspRegularRepresentative := by
  let s := A.actualCuspBoundaryCoverBase.1.2
  have hs : s ∈ cuspHalfPlane A.cuspCoordinate.height :=
    additiveCuspRadiusCover_halfPlane
      A.starCuspWitness.localWitness.radius_le A.actualCuspBoundaryCoverBase
  unfold actualCuspRegularDeckPathPoint actualCuspRegularRepresentative
    actualCuspRegularCoverPoint actualCuspAngularRegularBasePoint
  rw [← regularFamilyCoverProjection_regularDeckMap]
  apply Quotient.sound
  change MulAction.orbitRel
    (FamilyPeriodGroup (regularParameterMap A.periods))
    (RegularBase (U := A.paperTriangleUniformization) × ComplexTwoSpace) _ _
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨1, ?_⟩
  apply Prod.ext
  · apply Subtype.ext
    simpa [actualCuspAngularLiftPoint, regularDeckMap, s] using
      (A.cuspCoordinate.lift_shift s hs).symm
  · simp [actualCuspAngularLiftPoint, regularDeckMap, periodTransport_gZero]

/-- The actual angular cusp path, retained as a path to a labelled regular-family deck
translate. -/
public noncomputable def actualCuspRegularDeckPath :
    Path A.actualCuspRegularRepresentative
      (regularFamilyDeckMap A.periods g₀ A.actualCuspRegularRepresentative) where
  toFun := A.actualCuspRegularDeckPathPoint
  continuous_toFun := A.continuous_actualCuspRegularDeckPathPoint
  source' := A.actualCuspRegularDeckPathPoint_zero
  target' := A.actualCuspRegularDeckPathPoint_one

/-- Projection of the literal deck path to the outer quotient, before rebasing at the
definitionally equal actual cusp point. -/
public noncomputable def actualCuspRegularDeckLoop :
    Path
      (regularFamilyQuotientMap A.periods A.actualCuspRegularRepresentative)
      (regularFamilyQuotientMap A.periods A.actualCuspRegularRepresentative) :=
  (A.actualCuspRegularDeckPath.map
    (regularFamilyQuotientMap A.periods).continuous).cast rfl
      (regularFamilyQuotientMap_deck A.periods
        A.actualCuspRegularRepresentative g₀).symm

/-- Projecting the literal regular-family lift gives the actual angular central loop, after the
forced equality of the displayed basepoints. -/
public theorem actualCuspAngularCentralLoop_eq_actualRegularDeckLoop :
    A.actualCuspAngularCentralLoop =
      A.actualCuspRegularDeckLoop.cast
          A.actualCuspRegularRepresentative_projects.symm
      A.actualCuspRegularRepresentative_projects.symm := by
  apply Path.ext
  funext t
  change A.actualCuspOverlapToCentral
      (A.actualCuspAngularProjectedLoop t) =
    regularFamilyQuotientMap A.periods (A.actualCuspRegularDeckPathPoint t)
  change A.actualCuspOverlapToCentral
      (A.actualCuspBoundaryProjection (A.actualCuspAngularLiftPoint t)) = _
  rw [A.actualCuspOverlapToCentral_boundaryProjection]
  rfl

/-- Outer triangle-group monodromy at the actual cusp representative. -/
public noncomputable def actualCuspOuterDeckHom :
    FundamentalGroup A.CentralFamily A.actualCuspCentralBase →*
      Deltaᵐᵒᵖ := by
  let _ := regularFamilyDeckAction A.periods
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  exact hp.fundamentalGroupToMulOpposite
    ⟨A.actualCuspRegularRepresentative,
      A.actualCuspRegularRepresentative_projects⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual cusp meridian has outer deck label `g₀`. -/
public theorem actualCuspCentralMeridian_outerDeck :
    letI := regularFamilyDeckAction A.periods
    let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
    hp.fundamentalGroupToMulOpposite
        ⟨A.actualCuspRegularRepresentative,
          A.actualCuspRegularRepresentative_projects⟩
        A.actualCuspCentralMeridian = MulOpposite.op g₀ := by
  let _ := regularFamilyDeckAction A.periods
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  let e : (regularFamilyQuotientMap A.periods) ⁻¹' {A.actualCuspCentralBase} :=
    ⟨A.actualCuspRegularRepresentative,
      A.actualCuspRegularRepresentative_projects⟩
  change hp.fundamentalGroupToMulOpposite e
      A.actualCuspCentralMeridian = MulOpposite.op g₀
  rw [A.actualCuspCentralMeridian_eq_angularLoop,
    A.actualCuspAngularCentralLoop_eq_actualRegularDeckLoop]
  apply (hp.fundamentalGroupToMulOpposite_apply_eq_Iff).mpr
  change regularFamilyDeckMap A.periods g₀ A.actualCuspRegularRepresentative = _
  let e' : (regularFamilyQuotientMap A.periods) ⁻¹' {A.actualCuspCentralBase} :=
    ⟨regularFamilyDeckMap A.periods g₀ A.actualCuspRegularRepresentative, by
      exact (regularFamilyQuotientMap_deck A.periods
        A.actualCuspRegularRepresentative g₀).trans
          A.actualCuspRegularRepresentative_projects⟩
  let Γ : Path.Homotopic.Quotient A.actualCuspRegularRepresentative
      (regularFamilyDeckMap A.periods g₀ A.actualCuspRegularRepresentative) :=
    Path.Homotopic.Quotient.mk A.actualCuspRegularDeckPath
  have hm := hp.isCoveringMap.monodromy_eq_of_map_eq
    (ex := e) (ey := e') Γ (by
      change (Path.Homotopic.Quotient.mk A.actualCuspRegularDeckPath).map
          (regularFamilyQuotientMap A.periods) =
        (Path.Homotopic.Quotient.mk
          (A.actualCuspRegularDeckLoop.cast
              A.actualCuspRegularRepresentative_projects.symm
              A.actualCuspRegularRepresentative_projects.symm)).cast _ _
      rw [← Path.Homotopic.Quotient.mk_map]
      unfold actualCuspRegularDeckLoop
      simp only [Path.Homotopic.Quotient.mk_cast,
        Path.Homotopic.Quotient.cast_cast]
      simp only [Path.Homotopic.Quotient.cast_rfl_rfl])
  simpa only [MulOpposite.unop_op] using congrArg Subtype.val hm.symm

public theorem actualCuspOuterDeckHom_meridian :
    A.actualCuspOuterDeckHom A.actualCuspCentralMeridian = MulOpposite.op g₀ := by
  exact A.actualCuspCentralMeridian_outerDeck

end SphereSixComplex.Geometry.PaperAnalyticData

end
