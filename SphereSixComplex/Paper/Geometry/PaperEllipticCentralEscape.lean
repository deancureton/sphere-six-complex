module

public import SphereSixComplex.Paper.Geometry.PaperStarCollarPairProperness
public import SphereSixComplex.Paper.Geometry.OrbifoldCoordinate

/-!
# Elliptic collars escape compact subsets at the central end

The invariant orbifold coordinate maps central compact sets to compact sets avoiding the two
elliptic values. Continuity at each elliptic center then gives a positive Cayley-radius lower
bound along its collar.
-/

open CategoryTheory TopologicalSpace Topology
open scoped ContDiff Manifold

namespace SphereSixComplex

noncomputable section

namespace Geometry

open Set SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
open SphereSixComplex.TriangleGroup.FuchsianProperFreeness
open TorusFamily AnalyticTorusFamily GlobalTorusFamily ComplexTorus
open EllipticVaryingFamilyQuotient EllipticCayleyHomeomorph
open EllipticLocalCoordinates EllipticLogarithmicGauge
open EllipticLocalTrivialization
open EllipticLinearCollarGlobalDescent
open EllipticLogarithmicGauge EquivariantQuotientHomeomorph
open AnalyticData

/-- The canonical projection from the regular torus family to the paper's central quotient. -/
@[expose] public noncomputable def AnalyticData.centralQuotientProjection
    (P : AnalyticData) : RegularTotalSpace P.periods → P.CentralFamily := by
  let _ := regularFamilyDeckAction P.periods
  exact quotientProjection

/-- The central quotient projection is a local homeomorphism. -/
public theorem AnalyticData.centralQuotientProjection_isLocalHomeomorph
    (P : AnalyticData) : IsLocalHomeomorph P.centralQuotientProjection := by
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      P.modular.modularParameter.toTriangleUniformization_sourceAction
  let _ := regularBaseChartedSpace hproper
  let _ : LocallyCompactSpace
      (RegularBase (U := P.modular.modularParameter.toTriangleUniformization)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold globalDeckBaseModel regularSmoothnessOrder
      (RegularBase (U := P.modular.modularParameter.toTriangleUniformization)) :=
    regularBase_isManifold hproper
  let _ := familyIsCancelSMul (regularParameterMap P.periods)
  let _ := familyContinuousConstSMul (regularParameterMap P.periods)
    fun a ↦ (regularPeriodSection_contMDiff P.periods hproper a
      regularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (regularParameterMap P.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap P.periods)
      (regularParameterMap_compactUniformLowerBound P.periods))
  let htotal := regularTotalSpace_isManifold_and_projection_isLocalDiffeomorph
    P.periods hproper regularSmoothnessOrder
  let _ : IsManifold globalDeckTotalModel regularSmoothnessOrder
      (RegularTotalSpace P.periods) := htotal.1
  let _ : LocallyCompactSpace (RegularTotalSpace P.periods) :=
    Manifold.locallyCompact_of_finiteDimensional globalDeckTotalModel
  let _ : T2Space (RegularTotalSpace P.periods) := by infer_instance
  let _ := regularFamilyDeckAction P.periods
  let _ : IsCancelSMul Delta (RegularTotalSpace P.periods) :=
    regularFamilyDeckAction_isCancelSMul_of_fuchsian P.periods
      P.modular.modularParameter.toTriangleUniformization_sourceAction hproper
  let _ : ProperlyDiscontinuousSMul Delta (RegularTotalSpace P.periods) :=
    regularFamilyDeckAction_properlyDiscontinuous_of_source P.periods hproper
  let _ : ContinuousConstSMul Delta (RegularTotalSpace P.periods) :=
    regularFamilyDeckAction_continuousConstSMul P.periods hproper
  rw [centralQuotientProjection.eq_def]
  exact quotientProjection_isLocalHomeomorph

public theorem AnalyticData.centralQuotientProjection_surjective
    (P : AnalyticData) : Function.Surjective P.centralQuotientProjection := by
  rw [centralQuotientProjection.eq_def]
  exact Quotient.mk_surjective

public theorem AnalyticData.orderThreeStarToCentral_mk
    (P : AnalyticData)
    (q : (orderThreeAffinePuncturedCarrier P.periods
      P.modular.modularParameter.toTriangleUniformization_sourceAction
      P.starSeparation.orderThree.radius).carrier) :
    P.starToCentral (1 : Fin 3) (Quotient.mk _ q) =
      P.centralQuotientProjection
        (orderThreeCollarToRegular P.periods
          (sourceActionProperlyDiscontinuous_of_eq
            P.modular.modularParameter.toTriangleUniformization_sourceAction)
          P.starSeparation.orderThree.sourceData
          (orderThreePuncturedCollarGaugeEquiv P.periods
            P.starSeparation.orderThree.radius q)) := by
  let _ := P.totalSpaceCharts
  change P.orderThreePuncturedCollarToCentralFamily
      P.starSeparation.orderThree.sourceData (Quotient.mk _ q) = _
  rw [orderThreePuncturedCollarToCentralFamily.eq_def,
    centralQuotientProjection.eq_def]
  rfl

public theorem AnalyticData.orderFourStarToCentral_mk
    (P : AnalyticData)
    (q : (orderFourAffinePuncturedCarrier P.periods
      P.modular.modularParameter.toTriangleUniformization_sourceAction
      P.starSeparation.orderFour.radius).carrier) :
    P.starToCentral (2 : Fin 3) (Quotient.mk _ q) =
      P.centralQuotientProjection
        (orderFourCollarToRegular P.periods
          (sourceActionProperlyDiscontinuous_of_eq
            P.modular.modularParameter.toTriangleUniformization_sourceAction)
          P.starSeparation.orderFour.sourceData
          (orderFourPuncturedCollarGaugeEquiv P.periods
            P.starSeparation.orderFour.radius q)) := by
  let _ := P.totalSpaceCharts
  change P.orderFourPuncturedCollarToCentralFamily
      P.starSeparation.orderFour.sourceData (Quotient.mk _ q) = _
  rw [orderFourPuncturedCollarToCentralFamily.eq_def,
    centralQuotientProjection.eq_def]
  rfl

public theorem AnalyticData.orderThreeStarCollarRadius_mk
    (P : AnalyticData)
    (q : (orderThreeAffinePuncturedCarrier P.periods
      P.modular.modularParameter.toTriangleUniformization_sourceAction
      P.starSeparation.orderThree.radius).carrier) :
    P.starCollarRadius (1 : Fin 3) (Quotient.mk _ q) =
      orderThreeFamilyRadius P.periods q := by
  change P.orderThreeFillingRadius P.starSeparation.orderThree.radius
      (P.orderThreePuncturedCollarToFilling
        P.starSeparation.orderThree.radius (Quotient.mk _ q)) = _
  rw [P.orderThreePuncturedCollarToFilling_mk]
  rfl

public theorem AnalyticData.orderFourStarCollarRadius_mk
    (P : AnalyticData)
    (q : (orderFourAffinePuncturedCarrier P.periods
      P.modular.modularParameter.toTriangleUniformization_sourceAction
      P.starSeparation.orderFour.radius).carrier) :
    P.starCollarRadius (2 : Fin 3) (Quotient.mk _ q) =
      orderFourFamilyRadius P.periods q := by
  change P.orderFourFillingRadius P.starSeparation.orderFour.radius
      (P.orderFourPuncturedCollarToFilling
        P.starSeparation.orderFour.radius (Quotient.mk _ q)) = _
  rw [P.orderFourPuncturedCollarToFilling_mk]
  rfl

private theorem centralOrbitRadius_lowerBound
    (P : AnalyticData) (e : UpperHalfPlane ≃ₜ ComplexUnitDisc)
    (K : Set P.CentralFamily) (hK : IsCompact K)
    (hmiss : ∀ q : RegularTotalSpace P.periods,
      P.modular.sourceCoordinate.coordinate (regularTotalSpaceBase P.periods q).1 ≠
        P.modular.sourceCoordinate.coordinate (e.symm ComplexUnitDisc.center)) :
    ∃ a : ℝ, 0 < a ∧ ∀ q : RegularTotalSpace P.periods,
      P.centralQuotientProjection q ∈ K →
      a ≤ ‖(e (regularTotalSpaceBase P.periods q).1).1‖ := by
  let c := P.modular.sourceCoordinate.coordinate
  let C := orbifoldCoordinate P.periods
  have hC (q : RegularTotalSpace P.periods) :
      C (P.centralQuotientProjection q) = c (regularTotalSpaceBase P.periods q).1 :=
    P.modular.induced_coordinate _
  let B := C '' K
  have hB : IsCompact B := hK.image (continuous_orbifoldCoordinate _)
  have hc : c (e.symm ComplexUnitDisc.center) ∉ B := by
    rintro ⟨y, _, hy⟩
    obtain ⟨q, rfl⟩ := P.centralQuotientProjection_surjective y
    exact hmiss q ((hC q).symm.trans hy)
  have hopen : IsOpen ((fun z : ComplexUnitDisc ↦ c (e.symm z)) ⁻¹' Bᶜ) :=
    hB.isClosed.isOpen_compl.preimage
      (P.modular.sourceCoordinate.coordinate_holomorphic.continuous.comp e.symm.continuous)
  obtain ⟨a, ha, hball⟩ := Metric.isOpen_iff.mp hopen ComplexUnitDisc.center hc
  refine ⟨a, ha, ?_⟩
  intro q hq
  by_contra h
  have hnear : e (regularTotalSpaceBase P.periods q).1 ∈
      Metric.ball ComplexUnitDisc.center a := by
    change dist ((e (regularTotalSpaceBase P.periods q).1).1 : ℂ) 0 < a
    simpa only [dist_zero_right] using lt_of_not_ge h
  have hnot := hball hnear
  apply hnot
  change c (e.symm (e (regularTotalSpaceBase P.periods q).1)) ∈ B
  rw [Homeomorph.symm_apply_apply]
  exact ⟨P.centralQuotientProjection q, hq, hC q⟩

/-- Central compact sets give a uniform positive order-three Cayley radius. -/
public theorem AnalyticData.orderThreeCentralOrbitRadius_lowerBound
    (P : AnalyticData) (K : Set P.CentralFamily) (hK : IsCompact K) :
    ∃ a : ℝ, 0 < a ∧ ∀ q : RegularTotalSpace P.periods,
      P.centralQuotientProjection q ∈ K →
      a ≤ ‖(orderThreeCayleyHomeomorph
        (regularTotalSpaceBase P.periods q).1).1‖ := by
  apply centralOrbitRadius_lowerBound P orderThreeCayleyHomeomorph K hK
  intro q heq
  have hcenter : orderThreeCayleyHomeomorph.symm ComplexUnitDisc.center = fuchsianOneFixedPoint :=
    orderThreeCayleyHomeomorph.symm_apply_eq.mpr orderThreeCayleyHomeomorph_fixedPoint.symm
  rw [hcenter] at heq
  obtain ⟨g, hg⟩ := (P.modular.sourceCoordinate.coordinate_eq_iff_orbit _ _).mp heq
  let U := P.modular.modularParameter.toTriangleUniformization
  have hreg := isRegularBasePoint_smul (U := U) g
    (regularTotalSpaceBase P.periods q).property
  have hnot := (isRegularBasePoint_iff_not_mem_orbits _).mp hreg
  have hsource := P.modular.modularParameter.toTriangleUniformization_sourceAction
  have hfixed := (ellipticFixedPoints_eq_of_fuchsian hsource).1
  have heqU : U.sourceAction g • (regularTotalSpaceBase P.periods q).1 = U.zOne := by
    rw [hsource, hfixed]
    exact hg
  apply hnot
  left
  rw [heqU]
  simp only [sourceOrbitSet.eq_def, Set.mem_iUnion, Set.mem_singleton_iff]
  exact ⟨1, by simp⟩

/-- Central compact sets give a uniform positive order-four Cayley radius. -/
public theorem AnalyticData.orderFourCentralOrbitRadius_lowerBound
    (P : AnalyticData) (K : Set P.CentralFamily) (hK : IsCompact K) :
    ∃ a : ℝ, 0 < a ∧ ∀ q : RegularTotalSpace P.periods,
      P.centralQuotientProjection q ∈ K →
      a ≤ ‖(orderFourCayleyHomeomorph
        (regularTotalSpaceBase P.periods q).1).1‖ := by
  apply centralOrbitRadius_lowerBound P orderFourCayleyHomeomorph K hK
  intro q heq
  have hcenter : orderFourCayleyHomeomorph.symm ComplexUnitDisc.center = fuchsianTwoFixedPoint :=
    orderFourCayleyHomeomorph.symm_apply_eq.mpr orderFourCayleyHomeomorph_fixedPoint.symm
  rw [hcenter] at heq
  obtain ⟨g, hg⟩ := (P.modular.sourceCoordinate.coordinate_eq_iff_orbit _ _).mp heq
  let U := P.modular.modularParameter.toTriangleUniformization
  have hreg := isRegularBasePoint_smul (U := U) g
    (regularTotalSpaceBase P.periods q).property
  have hnot := (isRegularBasePoint_iff_not_mem_orbits _).mp hreg
  have hsource := P.modular.modularParameter.toTriangleUniformization_sourceAction
  have hfixed := (ellipticFixedPoints_eq_of_fuchsian hsource).2
  have heqU : U.sourceAction g • (regularTotalSpaceBase P.periods q).1 = U.zTwo := by
    rw [hsource, hfixed]
    exact hg
  apply hnot
  right
  rw [heqU]
  simp only [sourceOrbitSet.eq_def, Set.mem_iUnion, Set.mem_singleton_iff]
  exact ⟨1, by simp⟩

/-- Compact subsets of the central piece stay a positive distance from the missing order-three
elliptic fibre along the actual affine collar. -/
public theorem AnalyticData.orderThreeCentralPositiveLowerTrap
    (P : AnalyticData) :
    ∀ K : Set P.CentralFamily, IsCompact K →
      ∃ a : ℝ, 0 < a ∧ ∀ s : P.StarCollarSource (1 : Fin 3),
        P.starToCentral (1 : Fin 3) s ∈ K →
          a ≤ P.starCollarRadius (1 : Fin 3) s := by
  intro K hK
  obtain ⟨a, ha, haBound⟩ := P.orderThreeCentralOrbitRadius_lowerBound K hK
  refine ⟨a, ha, ?_⟩
  intro s hsK
  induction s using Quotient.inductionOn with
  | _ q =>
      let hproper : SourceActionProperlyDiscontinuous :=
        sourceActionProperlyDiscontinuous_of_eq
          P.modular.modularParameter.toTriangleUniformization_sourceAction
      let qlin := orderThreePuncturedCollarGaugeEquiv P.periods
        P.starSeparation.orderThree.radius q
      let qreg := orderThreeCollarToRegular P.periods hproper
        P.starSeparation.orderThree.sourceData qlin
      have hqregK : P.centralQuotientProjection qreg ∈ K := by
        rw [← P.orderThreeStarToCentral_mk q]
        exact hsK
      have hbase : ‖(orderThreeCayleyHomeomorph
          (regularTotalSpaceBase P.periods qreg).1).1‖ =
          orderThreeFamilyRadius P.periods qlin := by
        rw [orderThreeFamilyRadius.eq_def]
        exact congrArg (fun z : UpperHalfPlane ↦
          ‖(orderThreeCayleyHomeomorph z).1‖)
          (orderThreeCollarToRegular_base P.periods hproper
            P.modular.modularParameter.toTriangleUniformization_sourceAction
            P.starSeparation.orderThree.sourceData qlin)
      calc
        a ≤ ‖(orderThreeCayleyHomeomorph
            (regularTotalSpaceBase P.periods qreg).1).1‖ :=
          haBound qreg hqregK
        _ = orderThreeFamilyRadius P.periods qlin := hbase
        _ = orderThreeFamilyRadius P.periods q :=
          orderThreeFamilyRadius_principalGauge P.periods q
        _ = P.starCollarRadius (1 : Fin 3) (Quotient.mk _ q) :=
          (P.orderThreeStarCollarRadius_mk q).symm

/-- Compact subsets of the central piece stay a positive distance from the missing order-four
elliptic fibre along the actual affine collar. -/
public theorem AnalyticData.orderFourCentralPositiveLowerTrap
    (P : AnalyticData) :
    ∀ K : Set P.CentralFamily, IsCompact K →
      ∃ a : ℝ, 0 < a ∧ ∀ s : P.StarCollarSource (2 : Fin 3),
        P.starToCentral (2 : Fin 3) s ∈ K →
          a ≤ P.starCollarRadius (2 : Fin 3) s := by
  intro K hK
  obtain ⟨a, ha, haBound⟩ := P.orderFourCentralOrbitRadius_lowerBound K hK
  refine ⟨a, ha, ?_⟩
  intro s hsK
  induction s using Quotient.inductionOn with
  | _ q =>
      let hproper : SourceActionProperlyDiscontinuous :=
        sourceActionProperlyDiscontinuous_of_eq
          P.modular.modularParameter.toTriangleUniformization_sourceAction
      let qlin := orderFourPuncturedCollarGaugeEquiv P.periods
        P.starSeparation.orderFour.radius q
      let qreg := orderFourCollarToRegular P.periods hproper
        P.starSeparation.orderFour.sourceData qlin
      have hqregK : P.centralQuotientProjection qreg ∈ K := by
        rw [← P.orderFourStarToCentral_mk q]
        exact hsK
      have hbase : ‖(orderFourCayleyHomeomorph
          (regularTotalSpaceBase P.periods qreg).1).1‖ =
          orderFourFamilyRadius P.periods qlin := by
        rw [orderFourFamilyRadius.eq_def]
        exact congrArg (fun z : UpperHalfPlane ↦
          ‖(orderFourCayleyHomeomorph z).1‖)
          (orderFourCollarToRegular_base P.periods hproper
            P.modular.modularParameter.toTriangleUniformization_sourceAction
            P.starSeparation.orderFour.sourceData qlin)
      calc
        a ≤ ‖(orderFourCayleyHomeomorph
            (regularTotalSpaceBase P.periods qreg).1).1‖ :=
          haBound qreg hqregK
        _ = orderFourFamilyRadius P.periods qlin := hbase
        _ = orderFourFamilyRadius P.periods q :=
          orderFourFamilyRadius_principalGauge P.periods q
        _ = P.starCollarRadius (2 : Fin 3) (Quotient.mk _ q) :=
          (P.orderFourStarCollarRadius_mk q).symm

public theorem AnalyticData.orderThreeCollarPairMap_isProper
    (P : AnalyticData) :
    IsProperMap (P.openEmbeddingStarData.collarPairMap (1 : Fin 3)) :=
  P.orderThreeCollarPairMap_isProper_of_centralLowerTrap
    P.orderThreeCentralPositiveLowerTrap

public theorem AnalyticData.orderFourCollarPairMap_isProper
    (P : AnalyticData) :
    IsProperMap (P.openEmbeddingStarData.collarPairMap (2 : Fin 3)) :=
  P.orderFourCollarPairMap_isProper_of_centralLowerTrap
    P.orderFourCentralPositiveLowerTrap

end Geometry

end

end SphereSixComplex
