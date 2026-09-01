module

public import SphereSixComplex.Topology.PaperActualEllipticOrderFourFullLoopHomotopyProof

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.Periods
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.Geometry.EllipticPuncturedCollarGaugeHomeomorph
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

variable (A : PaperAnalyticData)

/-- Transport both endpoints of an endpoint-relative path homotopy along one equality. -/
public def pathHomotopy_castEndpoints
    {X : Type*} [TopologicalSpace X] {x y : X} (h : x = y)
    {p q : Path y y} (H : Path.Homotopy p q) :
    Path.Homotopy (p.cast h h) (q.cast h h) := by
  subst h
  exact H

/-- The punctured order-four Cayley disc, retaining precisely the inequalities needed by the
restricted product chart. -/
public abbrev OrderFourCayleyPuncturedDisc :=
  {z : ComplexUnitDisc //
    0 < ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ < A.starSeparation.orderFour.radius}

public noncomputable def orderFourCayleyPuncturedBasepoint :
    A.OrderFourCayleyPuncturedDisc :=
  ⟨⟨A.orderFourFillingRelationCayleyBaseValue, by
      rw [A.orderFourFillingRelationCayleyBaseValue_norm]
      exact A.orderFourActualEllipticBoundaryBase.1.2.2.trans
        A.starSeparation.orderFour.radius_lt_one⟩, by
    rw [A.orderFourFillingRelationCayleyBaseValue_norm]
    exact A.orderFourActualEllipticBoundaryBase.1.2⟩

/-- The actual Cayley loop, now as a loop in the punctured Cayley disc. -/
public noncomputable def orderFourFillingRelationCayleyPuncturedLoop :
    Path A.orderFourCayleyPuncturedBasepoint A.orderFourCayleyPuncturedBasepoint where
  toFun t := ⟨A.orderFourFillingRelationCayleyDiscLoop t, by
    have hnorm : ‖((A.orderFourFillingRelationCayleyDiscLoop t : ComplexUnitDisc) : ℂ)‖ =
        (A.orderFourActualEllipticBoundaryBase.1 : ℝ) := by
      change ‖((A.orderFourFillingRelationCayleyLoop t).1 : ℂ)‖ = _
      have hpoint : (A.orderFourFillingRelationCayleyLoop t).1 =
          localDegreeCirclePoint A.orderFourFillingRelationCayleyBaseValue t := by
        simp [orderFourFillingRelationCayleyLoop, puncturedComplexIntegerCircle,
          puncturedComplexIntegerCirclePoint, localDegreeCirclePoint]
      rw [hpoint, localDegreeCirclePoint_norm,
        A.orderFourFillingRelationCayleyBaseValue_norm]
    rw [hnorm]
    exact A.orderFourActualEllipticBoundaryBase.1.2⟩
  continuous_toFun := by
    exact Continuous.subtype_mk A.orderFourFillingRelationCayleyDiscLoop.continuous _
  source' := by
    apply Subtype.ext
    exact A.orderFourFillingRelationCayleyDiscLoop.source
  target' := by
    apply Subtype.ext
    exact A.orderFourFillingRelationCayleyDiscLoop.target

/-- The tautological inclusion of punctured Cayley-disc times torus into the restricted
order-four product carrier. -/
public noncomputable def orderFourPuncturedProductCarrierMap :
    letI := A.orderFourActualEllipticBoundaryAction
    C(A.OrderFourCayleyPuncturedDisc × A.orderFourTorus,
      (orderFourCyclicPuncturedProductData A.periods
        A.starSeparation.orderFour.radius A.starSeparation.orderFour.radius_pos
        A.starSeparation.orderFour.radius_lt_one).carrier.carrier) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  exact
    { toFun := fun zq => ⟨(zq.1.1, zq.2), zq.1.2⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd }

/-- Realize the restricted punctured product chart inside the regular total space. -/
public noncomputable def orderFourPuncturedProductToRegularMap :
    letI := A.orderFourActualEllipticBoundaryAction
    C((orderFourCyclicPuncturedProductData A.periods
        A.starSeparation.orderFour.radius A.starSeparation.orderFour.radius_pos
        A.starSeparation.orderFour.radius_lt_one).carrier.carrier,
      RegularTotalSpace A.periods) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let hproper : SourceActionProperlyDiscontinuous
      (U := A.modular.modularParameter.toTriangleUniformization) :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  exact
    { toFun := fun q => orderFourCollarToRegular A.periods
        hproper
        A.starSeparation.orderFour.sourceData
        ((orderFourPuncturedProductHomeomorph A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction
          A.starSeparation.orderFour.radius A.starSeparation.orderFour.radius_pos
          A.starSeparation.orderFour.radius_lt_one).symm q)
      continuous_toFun := by
        let _ := A.totalSpaceCharts
        exact
          (orderFourCollarToRegular_isOpenEmbedding A.periods
            hproper
            A.starSeparation.orderFour.sourceData).continuous.comp
              (orderFourPuncturedProductHomeomorph A.periods
                A.modular.modularParameter.toTriangleUniformization_sourceAction
                A.starSeparation.orderFour.radius A.starSeparation.orderFour.radius_pos
                A.starSeparation.orderFour.radius_lt_one).symm.continuous }

/-- The punctured product coordinates realize the actual regular filling loop pointwise. -/
public theorem orderFourRegularLoop_eq_puncturedProductRealization
    (t : unitInterval) :
    letI := A.orderFourActualEllipticBoundaryAction
    A.orderFourPuncturedProductToRegularMap
        (A.orderFourPuncturedProductCarrierMap
          (A.orderFourFillingRelationCayleyPuncturedLoop t,
            A.orderFourPrincipalGaugeWithOffsetPath t)) =
      A.orderFourFillingRelationRegularLoop t := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let hproper : SourceActionProperlyDiscontinuous
      (U := A.modular.modularParameter.toTriangleUniformization) :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let q := (orderFourPuncturedProductHomeomorph A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    A.starSeparation.orderFour.radius A.starSeparation.orderFour.radius_pos
    A.starSeparation.orderFour.radius_lt_one).symm
      (A.orderFourPuncturedProductCarrierMap
        (A.orderFourFillingRelationCayleyPuncturedLoop t,
          A.orderFourPrincipalGaugeWithOffsetPath t))
  apply regularFamilyInclusion_injective A.periods
  have hmap : A.orderFourPuncturedProductToRegularMap
      (A.orderFourPuncturedProductCarrierMap
        (A.orderFourFillingRelationCayleyPuncturedLoop t,
          A.orderFourPrincipalGaugeWithOffsetPath t)) =
      orderFourCollarToRegular A.periods hproper
        A.starSeparation.orderFour.sourceData q := by rfl
  rw [hmap]
  have hinc := regularFamilyInclusion_orderFourCollarToRegular A.periods hproper
    A.starSeparation.orderFour.sourceData q
  rw [hinc]
  apply (orderFourRealPeriodProductHomeomorph A.periods).injective
  rw [A.orderFourRegularLoop_cayleyGaugeProductCoordinate]
  exact congrArg Subtype.val
    ((orderFourPuncturedProductHomeomorph A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      A.starSeparation.orderFour.radius A.starSeparation.orderFour.radius_pos
      A.starSeparation.orderFour.radius_lt_one).apply_symm_apply
        (A.orderFourPuncturedProductCarrierMap
          (A.orderFourFillingRelationCayleyPuncturedLoop t,
            A.orderFourPrincipalGaugeWithOffsetPath t)))

/-- The punctured-product realization, expressed on a genuine product so the product-loop
splitting homotopy remains inside the admissible carrier. -/
public noncomputable def orderFourPuncturedProductRegularRealizationMap :
    letI := A.orderFourActualEllipticBoundaryAction
    C(A.OrderFourCayleyPuncturedDisc × A.orderFourTorus,
      RegularTotalSpace A.periods) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  exact
    { toFun := fun zq => A.orderFourPuncturedProductToRegularMap
        (A.orderFourPuncturedProductCarrierMap zq)
      continuous_toFun := A.orderFourPuncturedProductToRegularMap.continuous.comp
        A.orderFourPuncturedProductCarrierMap.continuous }

/-- The fibre-then-base factorization of the actual order-four filling loop, realized through
the restricted punctured product chart. -/
public noncomputable def orderFourRegularFiberThenBaseLoop :
    letI := A.orderFourActualEllipticBoundaryAction
    Path
      (A.orderFourCollarRegularRepresentativeMap
        A.orderFourActualEllipticBoundaryBase)
      (A.orderFourCollarRegularRepresentativeMap
        A.orderFourActualEllipticBoundaryBase) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let p := A.orderFourFillingRelationCayleyPuncturedLoop
  let q := A.orderFourPrincipalGaugeWithOffsetPath
  let f := A.orderFourPuncturedProductRegularRealizationMap
  let x := A.orderFourCayleyPuncturedBasepoint
  let y := A.orderFourFillingRelationPrincipalGaugeLoop 0 +
    Quotient.mk _ A.orderFourActualEllipticBoundaryBase.2.2
  let raw := (((Path.refl x).prod q).trans
    (p.prod (Path.refl y))).map f.continuous
  have hbase : A.orderFourCollarRegularRepresentativeMap
      A.orderFourActualEllipticBoundaryBase = f (x, y) := by
    exact A.orderFourFillingRelationRegularLoop.source.symm |>.trans
      ((A.orderFourRegularLoop_eq_puncturedProductRealization 0).symm.trans
        (congrArg f (Prod.ext p.source q.source)))
  exact raw.cast hbase hbase

/-- The actual order-four regular filling loop is endpoint-relatively homotopic to its
fibre-then-base factorization, with the entire homotopy realized through the restricted
punctured product carrier. -/
public theorem orderFourRegularLoop_homotopic_fiberThenBase :
    letI := A.orderFourActualEllipticBoundaryAction
    Nonempty (Path.Homotopy A.orderFourFillingRelationRegularLoop
      A.orderFourRegularFiberThenBaseLoop) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let p := A.orderFourFillingRelationCayleyPuncturedLoop
  let q := A.orderFourPrincipalGaugeWithOffsetPath
  let f := A.orderFourPuncturedProductRegularRealizationMap
  let x := A.orderFourCayleyPuncturedBasepoint
  let y := A.orderFourFillingRelationPrincipalGaugeLoop 0 +
    Quotient.mk _ A.orderFourActualEllipticBoundaryBase.2.2
  let raw := (((Path.refl x).prod q).trans
    (p.prod (Path.refl y))).map f.continuous
  have hbase : A.orderFourCollarRegularRepresentativeMap
      A.orderFourActualEllipticBoundaryBase = f (x, y) := by
    exact A.orderFourFillingRelationRegularLoop.source.symm |>.trans
      ((A.orderFourRegularLoop_eq_puncturedProductRealization 0).symm.trans
        (congrArg f (Prod.ext p.source q.source)))
  rcases productLoop_map_homotopic_fiberThenBase p q f with ⟨H⟩
  let H' := pathHomotopy_castEndpoints hbase H
  refine ⟨H'.cast ?_ ?_⟩
  · apply Path.ext
    funext t
    exact A.orderFourRegularLoop_eq_puncturedProductRealization t
  · rfl

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
