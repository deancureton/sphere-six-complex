module

public import SphereSixComplex.Paper.Topology.PaperGeometricCentralPeripheral
public import SphereSixComplex.Paper.Topology.PaperCentralFundamentalGroupGeneration

/-!
# Geometric monodromy in the actual central family

The selected cusp additive coordinate gives a literal path in the regular torus family.  Its
endpoint is the `g₀` deck translate, so the actual angular cusp loop has the prescribed outer
triangle-group monodromy without any universal-cover marking.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex
open SphereSixComplex.Topology SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.LatticeData
open SphereSixComplex.Geometry.ComplexTorus SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open CuspPeriodExpansion CuspCollar
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

variable (A : AnalyticData)

/-- The chosen actual cusp point before either of the two central-family quotients. -/
public def cuspRegularCoverPoint :
    RegularBase (U := A.paperTriangleUniformization) × ComplexTwoSpace :=
  (A.cuspAngularRegularBasePoint 0, A.cuspBoundaryCoverBase.1.1)

/-- The same point after the varying period-lattice quotient. -/
public noncomputable def cuspRegularRepresentative : RegularTotalSpace A.periods :=
  regularFamilyCoverProjection A.periods A.cuspRegularCoverPoint

/-- The chosen regular-family representative projects to the actual cusp point. -/
public theorem cuspRegularRepresentative_projects :
    regularFamilyQuotientMap A.periods A.cuspRegularRepresentative =
      A.cuspCentralBase := by
  have hpoint :
      ((additiveCuspBundleHomeomorph A.starCuspWitness
        A.cuspBoundaryCoverBase).1 :
          RegularBase (U := A.paperTriangleUniformization) × ComplexTwoSpace) =
        A.cuspRegularCoverPoint := by
    unfold cuspRegularCoverPoint cuspAngularRegularBasePoint
    apply Prod.ext
    · apply Subtype.ext
      change A.cuspCoordinate.lift A.cuspBoundaryCoverBase.1.2 =
        A.cuspCoordinate.lift (A.cuspAngularLiftPoint 0).1.2
      rw [A.cuspAngularLiftPoint_zero]
    · rfl
  calc
    _ = additiveCuspCoverToGlobal A.starCuspWitness
        A.cuspBoundaryCoverBase := by
      symm
      rw [additiveCuspCoverToGlobal_eq_quotientProjections]
      change regularFamilyQuotientMap A.periods
          (regularFamilyCoverProjection A.periods
            ((additiveCuspBundleHomeomorph A.starCuspWitness
              A.cuspBoundaryCoverBase).1 :
                RegularBase (U := A.paperTriangleUniformization) × ComplexTwoSpace)) = _
      rw [hpoint]
      rfl
    _ = A.cuspOverlapToCentral
        (A.cuspBoundaryProjection A.cuspBoundaryCoverBase) :=
      (A.cuspOverlapToCentral_boundaryProjection
        A.cuspBoundaryCoverBase).symm
    _ = A.cuspCentralBase := by
      rw [A.cuspBoundaryCoverBase_projects]
      rfl

/-- The literal regular-family lift of the actual angular cusp path. -/
public noncomputable def cuspRegularDeckPathPoint (t : unitInterval) :
    RegularTotalSpace A.periods :=
  regularFamilyCoverProjection A.periods
    (A.cuspAngularRegularBasePoint t, A.cuspBoundaryCoverBase.1.1)

public theorem continuous_cuspRegularDeckPathPoint :
    Continuous A.cuspRegularDeckPathPoint := by
  apply (regularFamilyCoverProjection A.periods).continuous.comp
  apply Continuous.prodMk
  · unfold cuspAngularRegularBasePoint cuspAngularLiftPoint
    apply Continuous.subtype_mk
    apply A.cuspCoordinate.lift_holomorphic.continuousOn.comp_continuous
    · fun_prop
    · intro t
      exact additiveCuspRadiusCover_halfPlane
        A.starCuspWitness.localWitness.radius_le (A.cuspAngularLiftPoint t)
  · exact continuous_const

@[simp]
public theorem cuspRegularDeckPathPoint_zero :
    A.cuspRegularDeckPathPoint 0 = A.cuspRegularRepresentative := by
  rfl

/-- The endpoint of the literal cusp lift is exactly the parabolic `g₀` deck translate. -/
public theorem cuspRegularDeckPathPoint_one :
    A.cuspRegularDeckPathPoint 1 =
      regularFamilyDeckMap A.periods g₀ A.cuspRegularRepresentative := by
  let s := A.cuspBoundaryCoverBase.1.2
  have hs : s ∈ cuspHalfPlane A.cuspCoordinate.height :=
    additiveCuspRadiusCover_halfPlane
      A.starCuspWitness.localWitness.radius_le A.cuspBoundaryCoverBase
  unfold cuspRegularDeckPathPoint cuspRegularRepresentative
    cuspRegularCoverPoint cuspAngularRegularBasePoint
  rw [← regularFamilyCoverProjection_regularDeckMap]
  apply Quotient.sound
  change MulAction.orbitRel
    (FamilyPeriodGroup (regularParameterMap A.periods))
    (RegularBase (U := A.paperTriangleUniformization) × ComplexTwoSpace) _ _
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨1, ?_⟩
  apply Prod.ext
  · apply Subtype.ext
    simpa [cuspAngularLiftPoint, regularDeckMap, s] using
      (A.cuspCoordinate.lift_shift s hs).symm
  · simp [cuspAngularLiftPoint, regularDeckMap, periodTransport_gZero]

/-- The actual angular cusp path, retained as a path to a labelled regular-family deck
translate. -/
public noncomputable def cuspRegularDeckPath :
    Path A.cuspRegularRepresentative
      (regularFamilyDeckMap A.periods g₀ A.cuspRegularRepresentative) where
  toFun := A.cuspRegularDeckPathPoint
  continuous_toFun := A.continuous_cuspRegularDeckPathPoint
  source' := A.cuspRegularDeckPathPoint_zero
  target' := A.cuspRegularDeckPathPoint_one

/-- Projection of the literal deck path to the outer quotient, before rebasing at the
definitionally equal actual cusp point. -/
public noncomputable def cuspRegularDeckLoop :
    Path
      (regularFamilyQuotientMap A.periods A.cuspRegularRepresentative)
      (regularFamilyQuotientMap A.periods A.cuspRegularRepresentative) :=
  (A.cuspRegularDeckPath.map
    (regularFamilyQuotientMap A.periods).continuous).cast rfl
      (regularFamilyQuotientMap_deck A.periods
        A.cuspRegularRepresentative g₀).symm

/-- Projecting the literal regular-family lift gives the actual angular central loop, after the
forced equality of the displayed basepoints. -/
public theorem cuspAngularCentralLoop_eq_actualRegularDeckLoop :
    A.cuspAngularCentralLoop =
      A.cuspRegularDeckLoop.cast
          A.cuspRegularRepresentative_projects.symm
      A.cuspRegularRepresentative_projects.symm := by
  apply Path.ext
  funext t
  change A.cuspOverlapToCentral
      (A.cuspAngularProjectedLoop t) =
    regularFamilyQuotientMap A.periods (A.cuspRegularDeckPathPoint t)
  change A.cuspOverlapToCentral
      (A.cuspBoundaryProjection (A.cuspAngularLiftPoint t)) = _
  rw [A.cuspOverlapToCentral_boundaryProjection]
  rfl

/-- Outer triangle-group monodromy at the actual cusp representative. -/
public noncomputable def cuspOuterDeckHom :
    FundamentalGroup A.CentralFamily A.cuspCentralBase →*
      Deltaᵐᵒᵖ := by
  let _ := regularFamilyDeckAction A.periods
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  exact hp.fundamentalGroupToMulOpposite
    ⟨A.cuspRegularRepresentative,
      A.cuspRegularRepresentative_projects⟩

/-- The actual cusp meridian has outer deck label `g₀`. -/
public theorem cuspCentralMeridian_outerDeck :
    letI := regularFamilyDeckAction A.periods
    let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
    hp.fundamentalGroupToMulOpposite
        ⟨A.cuspRegularRepresentative,
          A.cuspRegularRepresentative_projects⟩
        A.cuspCentralMeridian = MulOpposite.op g₀ := by
  let _ := regularFamilyDeckAction A.periods
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  let e : (regularFamilyQuotientMap A.periods) ⁻¹' {A.cuspCentralBase} :=
    ⟨A.cuspRegularRepresentative,
      A.cuspRegularRepresentative_projects⟩
  change hp.fundamentalGroupToMulOpposite e
      A.cuspCentralMeridian = MulOpposite.op g₀
  rw [A.cuspCentralMeridian_eq_angularLoop,
    A.cuspAngularCentralLoop_eq_actualRegularDeckLoop]
  apply (hp.fundamentalGroupToMulOpposite_apply_eq_Iff).mpr
  change regularFamilyDeckMap A.periods g₀ A.cuspRegularRepresentative = _
  let e' : (regularFamilyQuotientMap A.periods) ⁻¹' {A.cuspCentralBase} :=
    ⟨regularFamilyDeckMap A.periods g₀ A.cuspRegularRepresentative, by
      exact (regularFamilyQuotientMap_deck A.periods
        A.cuspRegularRepresentative g₀).trans
          A.cuspRegularRepresentative_projects⟩
  let Γ : Path.Homotopic.Quotient A.cuspRegularRepresentative
      (regularFamilyDeckMap A.periods g₀ A.cuspRegularRepresentative) :=
    Path.Homotopic.Quotient.mk A.cuspRegularDeckPath
  have hm := hp.isCoveringMap.monodromy_eq_of_map_eq
    (ex := e) (ey := e') Γ (by
      change (Path.Homotopic.Quotient.mk A.cuspRegularDeckPath).map
          (regularFamilyQuotientMap A.periods) =
        (Path.Homotopic.Quotient.mk
          (A.cuspRegularDeckLoop.cast
              A.cuspRegularRepresentative_projects.symm
              A.cuspRegularRepresentative_projects.symm)).cast _ _
      rw [← Path.Homotopic.Quotient.mk_map]
      unfold cuspRegularDeckLoop
      rw [Path.Homotopic.Quotient.mk_cast]
      rw [Path.Homotopic.Quotient.mk_cast]
      apply eq_of_heq
      symm
      exact (Path.Homotopic.Quotient.cast_heq _ _).trans
        ((Path.Homotopic.Quotient.cast_heq _ _).trans
          (Path.Homotopic.Quotient.cast_heq _ _)))
  simpa only [MulOpposite.unop_op] using congrArg Subtype.val hm.symm

public theorem cuspOuterDeckHom_meridian :
    A.cuspOuterDeckHom A.cuspCentralMeridian = MulOpposite.op g₀ := by
  exact A.cuspCentralMeridian_outerDeck

end SphereSixComplex.Geometry.AnalyticData

end
