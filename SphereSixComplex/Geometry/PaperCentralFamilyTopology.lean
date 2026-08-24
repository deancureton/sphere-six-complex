module

public import SphereSixComplex.Geometry.PaperAnalyticData
public import SphereSixComplex.Geometry.FuchsianRegularTorusFamily
public import SphereSixComplex.Geometry.ComplexModelRechart
public import SphereSixComplex.Geometry.EllipticCayleyHomeomorph
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.SetTheory.Cardinal.Free
public import Mathlib.Topology.Bases

/-!
# Topology of the paper's central family

The regular Fuchsian base is the upper half-plane with two countable orbits removed.  A Cayley
homeomorphism followed by the standard homeomorphism from the unit disc to the complex plane
identifies it with the complement of a countable subset of `ℂ`.  This proves connectedness of the
regular base and hence of both successive quotient families.  The same module records the complex
manifold charts and second-countability of the selected central piece.
-/

open scoped Manifold

namespace SphereSixComplex.Geometry.GlobalTorusFamily

open Set Metric
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry ComplexTorus TorusFamily AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

noncomputable section

variable {U : TriangleUniformization}

local instance : Countable Delta :=
  Monoid.Coprod.mk_surjective.countable

/-- The open complex unit disc is homeomorphic to the complex plane. -/
@[expose] public noncomputable def complexUnitDiscHomeomorphComplex :
    ComplexUnitDisc ≃ₜ ℂ :=
  (Homeomorph.setCongr (by
    apply Set.ext
    intro z
    change (‖z‖ < 1) ↔ dist z 0 < 1
    rw [dist_zero_right])).trans Homeomorph.unitBall.symm

/-- A Cayley coordinate followed by radial rescaling identifies the upper half-plane with `ℂ`. -/
@[expose] public noncomputable def upperHalfPlaneHomeomorphComplex
    (a : UpperHalfPlane) : UpperHalfPlane ≃ₜ ℂ :=
  (cayleyHomeomorph a).trans complexUnitDiscHomeomorphComplex

/-- The two deleted elliptic orbits, transported to the complex plane. -/
@[expose] public noncomputable def regularBadSet (U : TriangleUniformization) : Set ℂ :=
  upperHalfPlaneHomeomorphComplex U.zOne ''
    (sourceOrbitSet (U := U) U.zOne ∪ sourceOrbitSet (U := U) U.zTwo)

/-- Every orbit of the triangle group is countable. -/
public theorem sourceOrbitSet_countable (p : UpperHalfPlane) :
    (sourceOrbitSet (U := U) p).Countable := by
  rw [sourceOrbitSet]
  simpa only [iUnion_singleton_eq_range] using
    (Set.countable_range fun g : Delta => U.sourceAction g • p)

/-- The transported union of the two elliptic orbits is countable. -/
public theorem regularBadSet_countable (U : TriangleUniformization) :
    (regularBadSet U).Countable :=
  ((sourceOrbitSet_countable U.zOne).union
    (sourceOrbitSet_countable U.zTwo)).image _

/-- The regular base is homeomorphic to the complement of the transported elliptic orbits. -/
@[expose] public noncomputable def regularBaseHomeomorphComplexComplement
    (U : TriangleUniformization) :
    RegularBase (U := U) ≃ₜ ↥((regularBadSet U)ᶜ) :=
  (upperHalfPlaneHomeomorphComplex U.zOne).subtype
    (p := fun z => IsRegularBasePoint (U := U) z)
    (q := fun w => w ∈ (regularBadSet U)ᶜ)
    (fun z => by
      rw [isRegularBasePoint_iff_not_mem_orbits]
      simp only [regularBadSet, Set.mem_compl_iff, Set.mem_image]
      constructor
      · intro hz h
        obtain ⟨w, hw, heq⟩ := h
        have hwz : w = z :=
          (upperHalfPlaneHomeomorphComplex U.zOne).injective heq
        exact hz (hwz ▸ hw)
      · intro hz hw
        exact hz ⟨z, hw, rfl⟩)

/-- Removing the two countable elliptic orbits leaves the regular base connected. -/
public theorem regularBase_connected (U : TriangleUniformization) :
    ConnectedSpace (RegularBase (U := U)) := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  have hpath : IsPathConnected (regularBadSet U)ᶜ :=
    (regularBadSet_countable U).isPathConnected_compl_of_one_lt_rank hrank
  have hconnected : ConnectedSpace ↥((regularBadSet U)ᶜ) :=
    isConnected_iff_connectedSpace.mp hpath.isConnected
  exact (regularBaseHomeomorphComplexComplement U).connectedSpace_iff.mpr hconnected

/-- The regular base inherits second-countability from the upper half-plane. -/
public theorem regularBase_secondCountable (U : TriangleUniformization) :
    SecondCountableTopology (RegularBase (U := U)) := by
  exact TopologicalSpace.secondCountableTopology_induced
    (RegularBase (U := U)) UpperHalfPlane Subtype.val

/-- The varying torus family over the regular base is connected. -/
public theorem regularTotalSpace_connected (F : PeriodFunctions U) :
    ConnectedSpace (RegularTotalSpace F) := by
  let _ : ConnectedSpace (RegularBase (U := U)) := regularBase_connected U
  infer_instance

/-- The quotient of the regular torus family by the triangle group is connected. -/
public theorem puncturedGlobalFamily_connected (F : PeriodFunctions U) :
    letI := regularFamilyDeckAction F
    ConnectedSpace (PuncturedGlobalFamily F) := by
  let _ : ConnectedSpace (RegularBase (U := U)) := regularBase_connected U
  let _ := regularFamilyDeckAction F
  infer_instance

/-- The varying torus family over the regular base is second countable. -/
public theorem regularTotalSpace_secondCountable (F : PeriodFunctions U) :
    SecondCountableTopology (RegularTotalSpace F) := by
  let _ : SecondCountableTopology (RegularBase (U := U)) :=
    regularBase_secondCountable U
  let _ := familyContinuousConstSMul (regularParameterMap F)
    (fun a => (periodSection_contMDiff F a 0).continuous.comp continuous_subtype_val)
  exact ContinuousConstSMul.secondCountableTopology

/-- For an explicit Fuchsian parameter, the punctured global quotient is second countable. -/
public theorem fuchsianPuncturedGlobalFamily_secondCountable
    (P : FuchsianModularParameter)
    (F : PeriodFunctions P.toTriangleUniformization) :
    let hproper : SourceActionProperlyDiscontinuous :=
      sourceActionProperlyDiscontinuous_of_eq P.toTriangleUniformization_sourceAction
    letI := regularBaseChartedSpace hproper
    letI : LocallyCompactSpace (RegularBase (U := P.toTriangleUniformization)) :=
      (isOpen_isRegularBasePoint hproper).locallyCompactSpace
    letI : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder
        (RegularBase (U := P.toTriangleUniformization)) :=
      regularBase_isManifold hproper
    letI := familyIsCancelSMul (regularParameterMap F)
    letI := familyContinuousConstSMul (regularParameterMap F)
      fun a => (regularPeriodSection_contMDiff F hproper a RegularSmoothnessOrder).continuous
    letI := familyProperlyDiscontinuousSMul (regularParameterMap F)
      (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap F)
        (regularParameterMap_compactUniformLowerBound F))
    letI : LocallyCompactSpace (RegularTotalSpace F) :=
      Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
    letI := regularFamilyDeckAction F
    SecondCountableTopology (PuncturedGlobalFamily F) := by
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq P.toTriangleUniformization_sourceAction
  let _ := regularBaseChartedSpace hproper
  let _ : LocallyCompactSpace (RegularBase (U := P.toTriangleUniformization)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder
      (RegularBase (U := P.toTriangleUniformization)) :=
    regularBase_isManifold hproper
  let _ := familyIsCancelSMul (regularParameterMap F)
  let _ := familyContinuousConstSMul (regularParameterMap F)
    fun a => (regularPeriodSection_contMDiff F hproper a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (regularParameterMap F)
    (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap F)
      (regularParameterMap_compactUniformLowerBound F))
  have htotal := regularTotalSpace_isManifold_and_projection_isLocalDiffeomorph F hproper
    RegularSmoothnessOrder
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder (RegularTotalSpace F) :=
    htotal.1
  let _ : LocallyCompactSpace (RegularTotalSpace F) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ := regularFamilyDeckAction F
  let _ : ContinuousConstSMul Delta (RegularTotalSpace F) :=
    regularFamilyDeckAction_continuousConstSMul F hproper
  let _ : SecondCountableTopology (RegularTotalSpace F) :=
    regularTotalSpace_secondCountable F
  exact ContinuousConstSMul.secondCountableTopology

end

end SphereSixComplex.Geometry.GlobalTorusFamily

namespace SphereSixComplex.Geometry

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.TorusFamily SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

noncomputable section

namespace PaperAnalyticData

variable (A : PaperAnalyticData)

/-- Product-model charts on the selected central family. -/
@[expose, instance_reducible] public noncomputable def centralFamilyProductCharts :
    ChartedSpace (ModelProd ℂ ComplexTwoSpace) A.CentralFamily := by
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let _ := regularBaseChartedSpace hproper
  let _ : LocallyCompactSpace
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
    regularBase_isManifold hproper
  let _ := familyIsCancelSMul (regularParameterMap A.periods)
  let _ := familyContinuousConstSMul (regularParameterMap A.periods)
    fun a => (regularPeriodSection_contMDiff A.periods hproper a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (regularParameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap A.periods)
      (regularParameterMap_compactUniformLowerBound A.periods))
  let htotal := regularTotalSpace_isManifold_and_projection_isLocalDiffeomorph
    A.periods hproper RegularSmoothnessOrder
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (RegularTotalSpace A.periods) := htotal.1
  let _ : LocallyCompactSpace (RegularTotalSpace A.periods) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ := regularFamilyDeckAction A.periods
  let _ : IsCancelSMul Delta (RegularTotalSpace A.periods) :=
    regularFamilyDeckAction_isCancelSMul_of_fuchsian A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction hproper
  let _ : ProperlyDiscontinuousSMul Delta (RegularTotalSpace A.periods) :=
    regularFamilyDeckAction_properlyDiscontinuous_of_source A.periods hproper
  let _ : ContinuousConstSMul Delta (RegularTotalSpace A.periods) :=
    regularFamilyDeckAction_continuousConstSMul A.periods hproper
  infer_instance

/-- Complex threefold charts on the selected central family. -/
@[expose, instance_reducible] public noncomputable def centralFamilyComplexCharts :
    ChartedSpace ComplexModel A.CentralFamily := by
  let _ := A.centralFamilyProductCharts
  exact globalDeckComplexCharts

/-- The selected central family is a complex three-manifold. -/
public theorem centralFamily_isManifold :
    @IsManifold ℂ inferInstance ComplexModel inferInstance inferInstance ComplexModel
      inferInstance (modelWithCornersSelf ℂ ComplexModel) RegularSmoothnessOrder
      A.CentralFamily inferInstance A.centralFamilyComplexCharts := by
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let _ := A.centralFamilyProductCharts
  have hmanifold :=
    (fuchsianPuncturedGlobalFamily_isManifold_and_projection_isLocalDiffeomorph
      A.modular.modularParameter A.periods).1
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder A.CentralFamily := hmanifold
  exact globalDeckComplexManifold

/-- The selected central family is connected. -/
public theorem centralFamily_connected : ConnectedSpace A.CentralFamily := by
  let _ := regularFamilyDeckAction A.periods
  exact puncturedGlobalFamily_connected A.periods

/-- The selected central family is second countable. -/
public theorem centralFamily_secondCountable : SecondCountableTopology A.CentralFamily := by
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let _ := regularBaseChartedSpace hproper
  let _ : LocallyCompactSpace
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
    regularBase_isManifold hproper
  let _ := familyIsCancelSMul (regularParameterMap A.periods)
  let _ := familyContinuousConstSMul (regularParameterMap A.periods)
    fun a => (regularPeriodSection_contMDiff A.periods hproper a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (regularParameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap A.periods)
      (regularParameterMap_compactUniformLowerBound A.periods))
  let _ : LocallyCompactSpace (RegularTotalSpace A.periods) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ := regularFamilyDeckAction A.periods
  exact fuchsianPuncturedGlobalFamily_secondCountable
    A.modular.modularParameter A.periods

end PaperAnalyticData

end

end SphereSixComplex.Geometry
