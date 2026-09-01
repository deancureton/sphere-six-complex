module

public import SphereSixComplex.Topology.PaperActualEllipticOrderThreeCorrectedFibreRepresentativeProof
public import SphereSixComplex.Topology.PaperSectionSevenAffinePrincipalGaugeRadialBaseSquare

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.LatticeData
open SphereSixComplex.Periods
open SphereSixComplex.Topology
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.Geometry.EllipticPuncturedCollarGaugeHomeomorph
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

variable (A : PaperAnalyticData)

/-- The actual three-turn Cayley circle, retaining its radius bound as a point of the unit
disc. -/
public noncomputable def orderThreeFillingRelationCayleyDiscLoop :
    Path
      (⟨A.orderThreeFillingRelationCayleyBaseValue, by
        rw [A.orderThreeFillingRelationCayleyBaseValue_norm]
        exact A.orderThreeActualEllipticBoundaryBase.1.2.2.trans
          A.starSeparation.orderThree.radius_lt_one⟩ : ComplexUnitDisc)
      (⟨A.orderThreeFillingRelationCayleyBaseValue, by
        rw [A.orderThreeFillingRelationCayleyBaseValue_norm]
        exact A.orderThreeActualEllipticBoundaryBase.1.2.2.trans
          A.starSeparation.orderThree.radius_lt_one⟩ : ComplexUnitDisc) where
  toFun t := ⟨(A.orderThreeFillingRelationCayleyLoop t).1, by
    have hpoint : (A.orderThreeFillingRelationCayleyLoop t).1 =
        localDegreeCirclePoint A.orderThreeFillingRelationCayleyBaseValue t := by
      simp [orderThreeFillingRelationCayleyLoop, puncturedComplexIntegerCircle,
        puncturedComplexIntegerCirclePoint, localDegreeCirclePoint]
    rw [hpoint]
    rw [localDegreeCirclePoint_norm, A.orderThreeFillingRelationCayleyBaseValue_norm]
    exact A.orderThreeActualEllipticBoundaryBase.1.2.2.trans
      A.starSeparation.orderThree.radius_lt_one⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact A.orderThreeFillingRelationCayleyLoop.continuous.subtype_val
  source' := by
    apply Subtype.ext
    change (A.orderThreeFillingRelationCayleyLoop 0).1 =
      A.orderThreeFillingRelationCayleyBaseValue
    exact congrArg Subtype.val A.orderThreeFillingRelationCayleyLoop.source
  target' := by
    apply Subtype.ext
    change (A.orderThreeFillingRelationCayleyLoop 1).1 =
      A.orderThreeFillingRelationCayleyBaseValue
    exact congrArg Subtype.val A.orderThreeFillingRelationCayleyLoop.target

/-- Add the fixed collar offset to the based principal-gauge loop. -/
public noncomputable def orderThreePrincipalGaugeWithOffsetPath :
    letI := A.orderThreeActualEllipticBoundaryAction
    Path
      (A.orderThreeFillingRelationPrincipalGaugeLoop 0 +
        Quotient.mk _ A.orderThreeActualEllipticBoundaryBase.2.2)
      (A.orderThreeFillingRelationPrincipalGaugeLoop 0 +
        Quotient.mk _ A.orderThreeActualEllipticBoundaryBase.2.2) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  exact
    { toFun := A.orderThreePrincipalGaugeWithOffsetMap
      continuous_toFun := A.orderThreePrincipalGaugeWithOffsetMap.continuous
      source' := rfl
      target' := by
        rw [orderThreePrincipalGaugeWithOffsetMap]
        exact congrArg
          (fun q ↦ q + Quotient.mk _ A.orderThreeActualEllipticBoundaryBase.2.2)
          A.orderThreeFillingRelationPrincipalGaugeLoop.target }

/-- The full regular filling loop has exactly the Cayley-disc and offset principal-gauge
coordinates, including their subtype data. -/
public theorem orderThreeRegularLoop_cayleyGaugeProductCoordinate
    (t : unitInterval) :
    letI := A.orderThreeActualEllipticBoundaryAction
    orderThreeRealPeriodProductHomeomorph A.periods
        (regularFamilyInclusion A.periods
          (A.orderThreeFillingRelationRegularLoop t)) =
      (A.orderThreeFillingRelationCayleyDiscLoop t,
        A.orderThreePrincipalGaugeWithOffsetPath t) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  have hcoord := A.orderThreeFillingRelationRegularLoop_localProductCoordinate t
  apply Prod.ext
  · apply Subtype.ext
    rw [orderThreeRealPeriodProductHomeomorph_fst]
    rw [familyTotalSpaceBase_regularFamilyInclusion]
    let hproper : SourceActionProperlyDiscontinuous
        (U := A.modular.modularParameter.toTriangleUniformization) :=
      sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction
    let lift := A.orderThreeActualEllipticBoundaryDeckStraightLift
      A.orderThreeActualEllipticBoundaryDeckData.fillingRelation t
    have hb : (regularTotalSpaceBase A.periods
        (A.orderThreeCollarRegularRepresentativeMap lift)).1 =
        familyTotalSpaceBase A.periods
          (A.orderThreeCollarInverseRepresentative lift).1 := by
      convert orderThreeCollarToRegular_principalGauge_base A.periods hproper
        A.modular.modularParameter.toTriangleUniformization_sourceAction
        A.starSeparation.orderThree.sourceData
        (A.orderThreeCollarInverseRepresentative lift) using 1
      all_goals congr 1
    change ((orderThreeCayleyHomeomorph
      (regularTotalSpaceBase A.periods
        (A.orderThreeFillingRelationRegularLoop t)).1 :
        ComplexUnitDisc) : ℂ) = _
    rw [show A.orderThreeFillingRelationRegularLoop t =
      A.orderThreeCollarRegularRepresentativeMap lift by rfl]
    rw [hb]
    exact A.orderThreeFillingRelationCayleyLoop_apply t
  · change ((orderThreeRealPeriodProductHomeomorph A.periods
        (regularFamilyInclusion A.periods
          (A.orderThreeFillingRelationRegularLoop t))).2) =
      A.orderThreeFillingRelationPrincipalGaugeLoop t +
        Quotient.mk _ A.orderThreeActualEllipticBoundaryBase.2.2
    exact congrArg Prod.snd hcoord

public structure OrderThreePuncturedProductProperData : Type where
  proper : SourceActionProperlyDiscontinuous
    (U := A.modular.modularParameter.toTriangleUniformization)

public def orderThreePuncturedProductProperData :
    A.OrderThreePuncturedProductProperData where
  proper := sourceActionProperlyDiscontinuous_of_eq
    A.modular.modularParameter.toTriangleUniformization_sourceAction

/-- The punctured Cayley collar in which the actual order-three filling loop lies. -/
public abbrev OrderThreeCayleyPuncturedDisc :=
  {z : ComplexUnitDisc //
    0 < ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ < A.starSeparation.orderThree.radius}

public noncomputable def orderThreeCayleyPuncturedBasepoint :
    A.OrderThreeCayleyPuncturedDisc :=
  ⟨⟨A.orderThreeFillingRelationCayleyBaseValue, by
      rw [A.orderThreeFillingRelationCayleyBaseValue_norm]
      exact A.orderThreeActualEllipticBoundaryBase.1.2.2.trans
        A.starSeparation.orderThree.radius_lt_one⟩, by
    rw [A.orderThreeFillingRelationCayleyBaseValue_norm]
    exact A.orderThreeActualEllipticBoundaryBase.1.2⟩

/-- The actual three-turn Cayley loop in the punctured collar. -/
public noncomputable def orderThreeFillingRelationCayleyPuncturedLoop :
    Path A.orderThreeCayleyPuncturedBasepoint A.orderThreeCayleyPuncturedBasepoint where
  toFun t := ⟨A.orderThreeFillingRelationCayleyDiscLoop t, by
    have hnorm : ‖((A.orderThreeFillingRelationCayleyDiscLoop t : ComplexUnitDisc) : ℂ)‖ =
        (A.orderThreeActualEllipticBoundaryBase.1 : ℝ) := by
      change ‖((A.orderThreeFillingRelationCayleyLoop t).1 : ℂ)‖ = _
      have hpoint : (A.orderThreeFillingRelationCayleyLoop t).1 =
          localDegreeCirclePoint A.orderThreeFillingRelationCayleyBaseValue t := by
        simp [orderThreeFillingRelationCayleyLoop, puncturedComplexIntegerCircle,
          puncturedComplexIntegerCirclePoint, localDegreeCirclePoint]
      rw [hpoint, localDegreeCirclePoint_norm,
        A.orderThreeFillingRelationCayleyBaseValue_norm]
    rw [hnorm]
    exact A.orderThreeActualEllipticBoundaryBase.1.2⟩
  continuous_toFun := by
    exact Continuous.subtype_mk A.orderThreeFillingRelationCayleyDiscLoop.continuous _
  source' := by
    apply Subtype.ext
    exact A.orderThreeFillingRelationCayleyDiscLoop.source
  target' := by
    apply Subtype.ext
    exact A.orderThreeFillingRelationCayleyDiscLoop.target

/-- Include the punctured Cayley collar times its torus in the restricted product carrier. -/
public noncomputable def orderThreePuncturedProductCarrierMap :
    letI := A.orderThreeActualEllipticBoundaryAction
    C(A.OrderThreeCayleyPuncturedDisc × A.orderThreeTorus,
      (orderThreeCyclicPuncturedProductData A.periods
        A.starSeparation.orderThree.radius A.starSeparation.orderThree.radius_pos
        A.starSeparation.orderThree.radius_lt_one).carrier.carrier) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  exact
    { toFun := fun zq => ⟨(zq.1.1, zq.2), zq.1.2⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd }

/-- Realize the restricted order-three product chart in the regular total space. -/
public noncomputable def orderThreePuncturedProductToRegularMap :
    letI := A.orderThreeActualEllipticBoundaryAction
    C((orderThreeCyclicPuncturedProductData A.periods
        A.starSeparation.orderThree.radius A.starSeparation.orderThree.radius_pos
        A.starSeparation.orderThree.radius_lt_one).carrier.carrier,
      RegularTotalSpace A.periods) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  exact
    { toFun := fun q => orderThreeCollarToRegular A.periods
        A.orderThreePuncturedProductProperData.proper
        A.starSeparation.orderThree.sourceData
        ((orderThreePuncturedProductHomeomorph A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction
          A.starSeparation.orderThree.radius A.starSeparation.orderThree.radius_pos
          A.starSeparation.orderThree.radius_lt_one).symm q)
      continuous_toFun := by
        let _ := A.totalSpaceCharts
        exact
          (orderThreeCollarToRegular_isOpenEmbedding A.periods
            A.orderThreePuncturedProductProperData.proper
            A.starSeparation.orderThree.sourceData).continuous.comp
              (orderThreePuncturedProductHomeomorph A.periods
                A.modular.modularParameter.toTriangleUniformization_sourceAction
                A.starSeparation.orderThree.radius A.starSeparation.orderThree.radius_pos
                A.starSeparation.orderThree.radius_lt_one).symm.continuous }

/-- The punctured product coordinates recover the actual regular filling loop pointwise. -/
public theorem orderThreeRegularLoop_eq_puncturedProductRealization
    (t : unitInterval) :
    letI := A.orderThreeActualEllipticBoundaryAction
    A.orderThreePuncturedProductToRegularMap
        (A.orderThreePuncturedProductCarrierMap
          (A.orderThreeFillingRelationCayleyPuncturedLoop t,
            A.orderThreePrincipalGaugeWithOffsetPath t)) =
      A.orderThreeFillingRelationRegularLoop t := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let hproper : SourceActionProperlyDiscontinuous
      (U := A.modular.modularParameter.toTriangleUniformization) :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let q := (orderThreePuncturedProductHomeomorph A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    A.starSeparation.orderThree.radius A.starSeparation.orderThree.radius_pos
    A.starSeparation.orderThree.radius_lt_one).symm
      (A.orderThreePuncturedProductCarrierMap
        (A.orderThreeFillingRelationCayleyPuncturedLoop t,
          A.orderThreePrincipalGaugeWithOffsetPath t))
  apply regularFamilyInclusion_injective A.periods
  have hmap : A.orderThreePuncturedProductToRegularMap
      (A.orderThreePuncturedProductCarrierMap
        (A.orderThreeFillingRelationCayleyPuncturedLoop t,
          A.orderThreePrincipalGaugeWithOffsetPath t)) =
      orderThreeCollarToRegular A.periods hproper
        A.starSeparation.orderThree.sourceData q := by rfl
  rw [hmap]
  have hinc := regularFamilyInclusion_orderThreeCollarToRegular A.periods hproper
    A.starSeparation.orderThree.sourceData q
  rw [hinc]
  apply (orderThreeRealPeriodProductHomeomorph A.periods).injective
  rw [A.orderThreeRegularLoop_cayleyGaugeProductCoordinate]
  exact congrArg Subtype.val
    ((orderThreePuncturedProductHomeomorph A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      A.starSeparation.orderThree.radius A.starSeparation.orderThree.radius_pos
      A.starSeparation.orderThree.radius_lt_one).apply_symm_apply
        (A.orderThreePuncturedProductCarrierMap
          (A.orderThreeFillingRelationCayleyPuncturedLoop t,
            A.orderThreePrincipalGaugeWithOffsetPath t)))

/-- Realize punctured product coordinates directly in the central quotient. -/
public noncomputable def orderThreePuncturedProductToCentralMap :
    letI := A.orderThreeActualEllipticBoundaryAction
    C(A.OrderThreeCayleyPuncturedDisc × A.orderThreeTorus, A.CentralFamily) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let q : C(RegularTotalSpace A.periods, A.CentralFamily) :=
    ⟨A.centralQuotientProjection,
      A.centralQuotientProjection_isLocalHomeomorph.continuous⟩
  exact q.comp (A.orderThreePuncturedProductToRegularMap.comp
    A.orderThreePuncturedProductCarrierMap)

/-- Remove the constant collar offset without moving the Cayley coordinate. -/
public def orderThreePuncturedProduct_offsetHomotopy :
    letI := A.orderThreeActualEllipticBoundaryAction
    ContinuousMap.Homotopy
      ((A.orderThreeFillingRelationCayleyPuncturedLoop.prod
        A.orderThreePrincipalGaugeWithOffsetPath).toContinuousMap)
      ((A.orderThreeFillingRelationCayleyPuncturedLoop.prod
        A.orderThreeFillingRelationPrincipalGaugeLoop).toContinuousMap) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let H := A.orderThreePrincipalGaugeOffsetHomotopy
  exact
    { toFun := fun st ↦
        (A.orderThreeFillingRelationCayleyPuncturedLoop st.2, H st)
      continuous_toFun :=
        (A.orderThreeFillingRelationCayleyPuncturedLoop.continuous.comp
          continuous_snd).prodMk H.continuous
      map_zero_left := by
        intro t
        apply Prod.ext
        · rfl
        · exact H.map_zero_left t
      map_one_left := by
        intro t
        apply Prod.ext
        · rfl
        · exact H.map_one_left t }

/-- In the punctured collar, the actual coordinate loop is freely homotopic to its fibre-first
product splitting. -/
public theorem orderThreePuncturedProduct_freeHomotopy_fiberThenBase :
    letI := A.orderThreeActualEllipticBoundaryAction
    Nonempty (ContinuousMap.Homotopy
      ((A.orderThreeFillingRelationCayleyPuncturedLoop.prod
        A.orderThreePrincipalGaugeWithOffsetPath).toContinuousMap)
      ((((Path.refl A.orderThreeCayleyPuncturedBasepoint).prod
          A.orderThreeFillingRelationPrincipalGaugeLoop).trans
        (A.orderThreeFillingRelationCayleyPuncturedLoop.prod
          (Path.refl (A.orderThreeFillingRelationPrincipalGaugeLoop 0)))).toContinuousMap)) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  rcases productLoop_homotopic_fiberThenBase
      A.orderThreeFillingRelationCayleyPuncturedLoop
      A.orderThreeFillingRelationPrincipalGaugeLoop with ⟨Hsplit⟩
  exact ⟨A.orderThreePuncturedProduct_offsetHomotopy.trans
    (pathHomotopyToFreeHomotopy Hsplit)⟩

/-- Splitting before removing the collar offset is endpoint-relative and therefore preserves
the endpoint-trace condition required by the final free-homotopy criterion. -/
public theorem orderThreePuncturedProductWithOffset_homotopic_fiberThenBase :
    letI := A.orderThreeActualEllipticBoundaryAction
    Nonempty (Path.Homotopy
      ((A.orderThreeFillingRelationCayleyPuncturedLoop.prod
        A.orderThreePrincipalGaugeWithOffsetPath).map
          A.orderThreePuncturedProductToCentralMap.continuous)
      (((((Path.refl A.orderThreeCayleyPuncturedBasepoint).prod
          A.orderThreePrincipalGaugeWithOffsetPath).trans
        (A.orderThreeFillingRelationCayleyPuncturedLoop.prod
          (Path.refl (A.orderThreePrincipalGaugeWithOffsetPath 0)))).map
            A.orderThreePuncturedProductToCentralMap.continuous))) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  exact productLoop_map_homotopic_fiberThenBase
    A.orderThreeFillingRelationCayleyPuncturedLoop
    A.orderThreePrincipalGaugeWithOffsetPath
    A.orderThreePuncturedProductToCentralMap

/-- Pointwise identification of the realized product loop with the projected actual regular
filling loop. -/
public theorem orderThreePuncturedProductToCentralMap_apply_filling
    (t : unitInterval) :
    letI := A.orderThreeActualEllipticBoundaryAction
    A.orderThreePuncturedProductToCentralMap
        (A.orderThreeFillingRelationCayleyPuncturedLoop t,
          A.orderThreePrincipalGaugeWithOffsetPath t) =
      A.centralQuotientProjection (A.orderThreeFillingRelationRegularLoop t) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  unfold orderThreePuncturedProductToCentralMap
  change A.centralQuotientProjection
      (A.orderThreePuncturedProductToRegularMap
        (A.orderThreePuncturedProductCarrierMap
          (A.orderThreeFillingRelationCayleyPuncturedLoop t,
            A.orderThreePrincipalGaugeWithOffsetPath t))) = _
  rw [A.orderThreeRegularLoop_eq_puncturedProductRealization]

/-- The central realization of the local product splitting has an endpoint-relative homotopy
from the actual projected filling loop before its harmless endpoint cast. -/
public theorem orderThreeProjectedRegularLoop_homotopic_localFiberThenBase :
    letI := A.orderThreeActualEllipticBoundaryAction
    Nonempty (Path.Homotopy
      ((A.orderThreeFillingRelationCayleyPuncturedLoop.prod
        A.orderThreePrincipalGaugeWithOffsetPath).map
          A.orderThreePuncturedProductToCentralMap.continuous)
      (((((Path.refl A.orderThreeCayleyPuncturedBasepoint).prod
          A.orderThreePrincipalGaugeWithOffsetPath).trans
        (A.orderThreeFillingRelationCayleyPuncturedLoop.prod
          (Path.refl (A.orderThreePrincipalGaugeWithOffsetPath 0)))).map
            A.orderThreePuncturedProductToCentralMap.continuous))) :=
  A.orderThreePuncturedProductWithOffset_homotopic_fiberThenBase

public theorem orderThreeActualEllipticCentralBase_eq_puncturedProductBase :
    letI := A.orderThreeActualEllipticBoundaryAction
    A.orderThreeActualEllipticCentralBase =
      A.orderThreePuncturedProductToCentralMap
        (A.orderThreeCayleyPuncturedBasepoint,
          A.orderThreePrincipalGaugeWithOffsetPath 0) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  symm
  calc
    A.orderThreePuncturedProductToCentralMap
          (A.orderThreeCayleyPuncturedBasepoint,
            A.orderThreePrincipalGaugeWithOffsetPath 0) =
        A.centralQuotientProjection
          (A.orderThreeFillingRelationRegularLoop 0) :=
      by
        convert A.orderThreePuncturedProductToCentralMap_apply_filling 0 using 1
        exact congrArg
          (fun z ↦ A.orderThreePuncturedProductToCentralMap
            (z, A.orderThreePrincipalGaugeWithOffsetPath 0))
          A.orderThreeFillingRelationCayleyPuncturedLoop.source.symm
    _ = A.centralQuotientProjection
          (A.orderThreeCollarRegularRepresentativeMap
            A.orderThreeActualEllipticBoundaryBase) := by
      exact congrArg A.centralQuotientProjection
        A.orderThreeFillingRelationRegularLoop.source
    _ = A.orderThreeActualEllipticCentralBase :=
      A.orderThreeCollarRegularRepresentative_base_projects

/-- The fibre-first local splitting, cast to the displayed order-three boundary basepoint. -/
public noncomputable def orderThreeLocalFiberThenBaseCentralPath :
    letI := A.orderThreeActualEllipticBoundaryAction
    Path A.orderThreeActualEllipticCentralBase A.orderThreeActualEllipticCentralBase := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  exact (((((Path.refl A.orderThreeCayleyPuncturedBasepoint).prod
      A.orderThreePrincipalGaugeWithOffsetPath).trans
    (A.orderThreeFillingRelationCayleyPuncturedLoop.prod
      (Path.refl (A.orderThreePrincipalGaugeWithOffsetPath 0)))).map
        A.orderThreePuncturedProductToCentralMap.continuous).cast
          A.orderThreeActualEllipticCentralBase_eq_puncturedProductBase
          A.orderThreeActualEllipticCentralBase_eq_puncturedProductBase)

/-- The endpoint-cast central realization of the product loop is literally the projected actual
regular filling loop. -/
public theorem orderThreePuncturedProductCentralPath_eq_projectedRegularLoop :
    letI := A.orderThreeActualEllipticBoundaryAction
    (((A.orderThreeFillingRelationCayleyPuncturedLoop.prod
        A.orderThreePrincipalGaugeWithOffsetPath).map
          A.orderThreePuncturedProductToCentralMap.continuous).cast
            A.orderThreeActualEllipticCentralBase_eq_puncturedProductBase
            A.orderThreeActualEllipticCentralBase_eq_puncturedProductBase) =
      ((A.orderThreeFillingRelationRegularLoop.map
        A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
          A.orderThreeCollarRegularRepresentative_base_projects.symm
          A.orderThreeCollarRegularRepresentative_base_projects.symm) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  apply Path.ext
  funext t
  exact A.orderThreePuncturedProductToCentralMap_apply_filling t

/-- The projected actual filling loop admits an endpoint-relative homotopy to the local
fibre-first splitting.  Hence the associated free homotopy automatically has identical endpoint
traces. -/
public theorem orderThreeProjectedRegularLoop_pathHomotopic_localFiberThenBase :
    letI := A.orderThreeActualEllipticBoundaryAction
    Nonempty (Path.Homotopy
      ((A.orderThreeFillingRelationRegularLoop.map
        A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
          A.orderThreeCollarRegularRepresentative_base_projects.symm
          A.orderThreeCollarRegularRepresentative_base_projects.symm)
      A.orderThreeLocalFiberThenBaseCentralPath) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  rcases A.orderThreePuncturedProductWithOffset_homotopic_fiberThenBase with ⟨H⟩
  let H' := H.pathCast
    A.orderThreeActualEllipticCentralBase_eq_puncturedProductBase
    A.orderThreeActualEllipticCentralBase_eq_puncturedProductBase
  exact ⟨H'.cast
    A.orderThreePuncturedProductCentralPath_eq_projectedRegularLoop rfl⟩

public theorem orderThreeProjectedRegularLoop_freeHomotopy_localFiberThenBase_trace :
    letI := A.orderThreeActualEllipticBoundaryAction
    ∃ H : ContinuousMap.Homotopy
      ((A.orderThreeFillingRelationRegularLoop.map
        A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
          A.orderThreeCollarRegularRepresentative_base_projects.symm
          A.orderThreeCollarRegularRepresentative_base_projects.symm).toContinuousMap
      A.orderThreeLocalFiberThenBaseCentralPath.toContinuousMap,
      (H.evalAt 0).cast
          ((A.orderThreeFillingRelationRegularLoop.map
            A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
              A.orderThreeCollarRegularRepresentative_base_projects.symm
              A.orderThreeCollarRegularRepresentative_base_projects.symm).source.symm
          A.orderThreeLocalFiberThenBaseCentralPath.source.symm =
        (H.evalAt 1).cast
          ((A.orderThreeFillingRelationRegularLoop.map
            A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
              A.orderThreeCollarRegularRepresentative_base_projects.symm
              A.orderThreeCollarRegularRepresentative_base_projects.symm).target.symm
          A.orderThreeLocalFiberThenBaseCentralPath.target.symm := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  rcases A.orderThreeProjectedRegularLoop_pathHomotopic_localFiberThenBase with ⟨H⟩
  exact ⟨pathHomotopyToFreeHomotopy H, pathHomotopyToFreeHomotopy_trace H⟩

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
