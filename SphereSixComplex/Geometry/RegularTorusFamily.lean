module

public import SphereSixComplex.Geometry.RegularBaseTopology
public import SphereSixComplex.TriangleGroup.FuchsianProperFreeness
import all SphereSixComplex.Geometry.TorusFamily

/-!
# The analytic torus family over the regular base

The period family restricts to the complement of the two elliptic orbits. Its compact-uniform
lower bound and holomorphic period sections give the resulting lattice quotient a complex
manifold structure with locally biholomorphic projection.
-/

open scoped Manifold

namespace SphereSixComplex.Geometry.GlobalTorusFamily

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.TorusFamily SphereSixComplex.Geometry.AnalyticTorusFamily

public noncomputable section

variable {U : TriangleUniformization}

public abbrev RegularSmoothnessOrder : WithTop ℕ∞ := (⊤ : ℕ∞)

/-- Compact-uniform nondegeneracy restricts from the upper half-plane to the regular base. -/
public theorem regularParameterMap_compactUniformLowerBound (F : PeriodFunctions U) :
    CompactUniformLowerBound (regularParameterMap F) := by
  rw [CompactUniformLowerBound.eq_def]
  intro K hK
  obtain ⟨c, hc, hbound⟩ := parameterMap_compactUniformLowerBound F
    (Subtype.val '' K) (hK.image continuous_subtype_val)
  refine ⟨c, hc, ?_⟩
  intro b hb a
  exact hbound b.1 ⟨b, hb, rfl⟩ a

/-- Every period section remains complex smooth after restriction to the regular base. -/
public theorem regularPeriodSection_contMDiff
    (F : PeriodFunctions U) (hproper : SourceActionProperlyDiscontinuous (U := U))
    (a : IntegerPeriods) (n : WithTop ℕ∞) :
    letI := regularBaseChartedSpace hproper
    ContMDiff GlobalDeckBaseModel GlobalDeckFiberModel n
      (fun z : RegularBase (U := U) ↦ periodVector (regularParameterMap F z).1 a) := by
  let _ := regularBaseChartedSpace hproper
  have hval : ContMDiff GlobalDeckBaseModel GlobalDeckBaseModel n
      (fun z : RegularBase (U := U) ↦ z.1) := by
    change ContMDiff GlobalDeckBaseModel GlobalDeckBaseModel n
      (Subtype.val : regularBaseOpen hproper → UpperHalfPlane)
    exact contMDiff_subtype_val
  exact (periodSection_contMDiff F a n).comp hval

/-- The inherited complex atlas makes the regular base a manifold at every smoothness order. -/
public theorem regularBase_isManifold_of_order
    (hproper : SourceActionProperlyDiscontinuous (U := U)) (n : WithTop ℕ∞) :
    letI := regularBaseChartedSpace hproper
    IsManifold GlobalDeckBaseModel n (RegularBase (U := U)) := by
  let _ := regularBaseChartedSpace hproper
  change IsManifold GlobalDeckBaseModel n (regularBaseOpen hproper)
  infer_instance

/-- The varying-lattice quotient over the regular base is a complex manifold, and its quotient
projection is locally biholomorphic. -/
public theorem regularTotalSpace_isManifold_and_projection_isLocalDiffeomorph
    (F : PeriodFunctions U) (hproper : SourceActionProperlyDiscontinuous (U := U))
    (n : WithTop ℕ∞) :
    letI := regularBaseChartedSpace hproper
    letI : LocallyCompactSpace (RegularBase (U := U)) :=
      (isOpen_isRegularBasePoint hproper).locallyCompactSpace
    letI : IsManifold GlobalDeckBaseModel n (RegularBase (U := U)) :=
      regularBase_isManifold_of_order hproper n
    letI := familyIsCancelSMul (regularParameterMap F)
    letI := familyContinuousConstSMul (regularParameterMap F)
      fun a ↦ (regularPeriodSection_contMDiff F hproper a n).continuous
    letI := familyProperlyDiscontinuousSMul (regularParameterMap F)
      (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap F)
        (regularParameterMap_compactUniformLowerBound F))
    IsManifold GlobalDeckTotalModel n (RegularTotalSpace F) ∧
      IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
        (projection (regularParameterMap F)) := by
  let _ := regularBaseChartedSpace hproper
  let _ : LocallyCompactSpace (RegularBase (U := U)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold GlobalDeckBaseModel n (RegularBase (U := U)) :=
    regularBase_isManifold_of_order hproper n
  exact TorusFamily.totalSpace_isManifold_and_projection_isLocalDiffeomorph
    GlobalDeckBaseModel n (regularParameterMap F)
      (regularPeriodSection_contMDiff F hproper · n)
      (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap F)
        (regularParameterMap_compactUniformLowerBound F))

/-- A smooth lifted deck transformation descends through the locally biholomorphic lattice
projection to a smooth map of the regular torus family. -/
public theorem regularFamilyDeckMap_contMDiff_of_projection_isLocalDiffeomorph
    (F : PeriodFunctions U)
    [ChartedSpace ℂ (RegularBase (U := U))]
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (RegularTotalSpace F)]
    [IsManifold GlobalDeckTotalModel RegularSmoothnessOrder (RegularTotalSpace F)]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder
      (projection (regularParameterMap F))) (g : Delta)
    (hdeck : ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (regularDeckMap F g)) :
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (regularFamilyDeckMap F g) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ p =>
    let π : RegularBase (U := U) × ComplexTwoSpace → RegularTotalSpace F :=
      projection (regularParameterMap F)
    let s := (hprojection p).localInverse
    have hs : ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
        s (π p) :=
      (hprojection p).localInverse_contMDiffAt
    have hsp : s (π p) = p :=
      (hprojection p).localInverse_left_inv (hprojection p).localInverse_mem_target
    have hdeck : ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
        (regularDeckMap F g ∘ s) (π p) :=
      hdeck.contMDiffAt.comp (π p) hs
    have hrhs : ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
        (π ∘ regularDeckMap F g ∘ s) (π p) :=
      (hprojection (regularDeckMap F g p)).contMDiffAt.comp_of_eq hdeck (by simp [hsp])
    have hright := (hprojection p).localInverse_eventuallyEq_right
    have hevent : Filter.EventuallyEq (nhds (π p)) (regularFamilyDeckMap F g)
        (π ∘ regularDeckMap F g ∘ s) := by
      filter_upwards [hright] with x hx
      calc
        regularFamilyDeckMap F g x = regularFamilyDeckMap F g (π (s x)) :=
          congrArg _ hx.symm
        _ = π (regularDeckMap F g (s x)) := regularFamilyDeckMap_mk F g (s x)
    exact hrhs.congr_of_eventuallyEq hevent

/-- Every deck transformation of the actual torus quotient over the regular base is complex
smooth. -/
public theorem regularFamilyDeckMap_contMDiff
    (F : PeriodFunctions U) (hproper : SourceActionProperlyDiscontinuous (U := U))
    (g : Delta) :
    letI := regularBaseChartedSpace hproper
    letI : LocallyCompactSpace (RegularBase (U := U)) :=
      (isOpen_isRegularBasePoint hproper).locallyCompactSpace
    letI : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder (RegularBase (U := U)) :=
      regularBase_isManifold hproper
    letI := familyIsCancelSMul (regularParameterMap F)
    letI := familyContinuousConstSMul (regularParameterMap F)
      fun a ↦ (regularPeriodSection_contMDiff F hproper a RegularSmoothnessOrder).continuous
    letI := familyProperlyDiscontinuousSMul (regularParameterMap F)
      (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap F)
        (regularParameterMap_compactUniformLowerBound F))
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (regularFamilyDeckMap F g) := by
  let _ := regularBaseChartedSpace hproper
  let _ : LocallyCompactSpace (RegularBase (U := U)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder (RegularBase (U := U)) :=
    regularBase_isManifold hproper
  let _ := familyIsCancelSMul (regularParameterMap F)
  let _ := familyContinuousConstSMul (regularParameterMap F)
    fun a ↦ (regularPeriodSection_contMDiff F hproper a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (regularParameterMap F)
    (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap F)
      (regularParameterMap_compactUniformLowerBound F))
  have htotal := regularTotalSpace_isManifold_and_projection_isLocalDiffeomorph F hproper
    RegularSmoothnessOrder
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder (RegularTotalSpace F) :=
    htotal.1
  exact regularFamilyDeckMap_contMDiff_of_projection_isLocalDiffeomorph F htotal.2 g
    (regularDeckMap_contMDiff F hproper g)

/-- Lattice-equivalent points in the vector-bundle cover have the same base point. -/
public theorem regularTotalSpaceBase_respects (F : PeriodFunctions U)
    (p q : RegularBase (U := U) × ComplexTwoSpace)
    (h : MulAction.orbitRel (FamilyPeriodGroup (regularParameterMap F)) _ p q) :
    p.1 = q.1 := by
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
    obtain ⟨a, ha⟩ := h
    simpa only [family_smul_fst] using congrArg Prod.fst ha.symm

/-- The base point of a regular torus-family point; lattice translations preserve it. -/
@[expose] public noncomputable def regularTotalSpaceBase (F : PeriodFunctions U) :
    RegularTotalSpace F → RegularBase (U := U) :=
  Quotient.lift Prod.fst (regularTotalSpaceBase_respects F)

@[simp]
public theorem regularTotalSpaceBase_mk (F : PeriodFunctions U)
    (p : RegularBase (U := U) × ComplexTwoSpace) :
    regularTotalSpaceBase F (Quotient.mk _ p) = p.1 :=
  rfl

/-- The base map of the regular torus family is continuous. -/
public theorem regularTotalSpaceBase_continuous (F : PeriodFunctions U) :
    Continuous (regularTotalSpaceBase F) :=
  continuous_quot_lift (regularTotalSpaceBase_respects F) continuous_fst

/-- The descended triangle-group action covers the regular source action. -/
public theorem regularTotalSpaceBase_familyDeckMap
    (F : PeriodFunctions U) (g : Delta) (x : RegularTotalSpace F) :
    regularTotalSpaceBase F (regularFamilyDeckMap F g x) =
      regularSourceEquiv g (regularTotalSpaceBase F x) := by
  induction x using Quotient.inductionOn with
  | _ p => rfl

/-- Freeness of the regular source action implies freeness on the torus family. -/
public theorem regularFamilyDeckAction_isCancelSMul_of_fuchsian
    (F : PeriodFunctions U) (hsource : U.sourceAction = fuchsianSourceAction)
    (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    letI := regularFamilyDeckAction F
    IsCancelSMul Delta (RegularTotalSpace F) := by
  let _ := regularFamilyDeckAction F
  let _ := FuchsianProperFreeness.regularSourceMulAction U
  let _ : IsCancelSMul Delta (RegularBase (U := U)) :=
    FuchsianProperFreeness.regularSource_isCancelSMul_of_fuchsian hsource hproper
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro g x hfixed
  apply IsCancelSMul.eq_one_of_smul (P := RegularBase (U := U))
    (x := regularTotalSpaceBase F x)
  change regularSourceEquiv g (regularTotalSpaceBase F x) = regularTotalSpaceBase F x
  rw [← regularTotalSpaceBase_familyDeckMap F g x]
  exact congrArg (regularTotalSpaceBase F) hfixed

/-- Proper discontinuity of the source action transfers to the torus-family deck action. -/
public theorem regularFamilyDeckAction_properlyDiscontinuous_of_source
    (F : PeriodFunctions U) (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    letI := regularFamilyDeckAction F
    ProperlyDiscontinuousSMul Delta (RegularTotalSpace F) := by
  let _ := regularFamilyDeckAction F
  constructor
  intro K L hK hL
  let baseProjection : RegularTotalSpace F → UpperHalfPlane :=
    fun x ↦ (regularTotalSpaceBase F x).1
  have hcontinuous : Continuous baseProjection :=
    continuous_subtype_val.comp (regularTotalSpaceBase_continuous F)
  have hKbase : IsCompact (baseProjection '' K) := hK.image hcontinuous
  have hLbase : IsCompact (baseProjection '' L) := hL.image hcontinuous
  rw [SourceActionProperlyDiscontinuous.eq_def] at hproper
  apply (hproper hKbase hLbase).subset
  intro g hg
  rcases hg with ⟨q, ⟨p, hpK, hpq⟩, hqL⟩
  refine ⟨baseProjection q, ?_, ⟨q, hqL, rfl⟩⟩
  refine ⟨baseProjection p, ⟨p, hpK, rfl⟩, ?_⟩
  have hbase := congrArg (regularTotalSpaceBase F) hpq
  change regularTotalSpaceBase F (regularFamilyDeckMap F g p) =
    regularTotalSpaceBase F q at hbase
  rw [regularTotalSpaceBase_familyDeckMap] at hbase
  exact congrArg Subtype.val hbase

/-- Smoothness of every descended deck map makes the regular family action continuous. -/
public theorem regularFamilyDeckAction_continuousConstSMul
    (F : PeriodFunctions U) (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    letI := regularBaseChartedSpace hproper
    letI : LocallyCompactSpace (RegularBase (U := U)) :=
      (isOpen_isRegularBasePoint hproper).locallyCompactSpace
    letI : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder (RegularBase (U := U)) :=
      regularBase_isManifold hproper
    letI := familyIsCancelSMul (regularParameterMap F)
    letI := familyContinuousConstSMul (regularParameterMap F)
      fun a ↦ (regularPeriodSection_contMDiff F hproper a RegularSmoothnessOrder).continuous
    letI := familyProperlyDiscontinuousSMul (regularParameterMap F)
      (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap F)
        (regularParameterMap_compactUniformLowerBound F))
    letI : LocallyCompactSpace (RegularTotalSpace F) :=
      Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
    letI := regularFamilyDeckAction F
    ContinuousConstSMul Delta (RegularTotalSpace F) := by
  let _ := regularBaseChartedSpace hproper
  let _ : LocallyCompactSpace (RegularBase (U := U)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder (RegularBase (U := U)) :=
    regularBase_isManifold hproper
  let _ := familyIsCancelSMul (regularParameterMap F)
  let _ := familyContinuousConstSMul (regularParameterMap F)
    fun a ↦ (regularPeriodSection_contMDiff F hproper a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (regularParameterMap F)
    (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap F)
      (regularParameterMap_compactUniformLowerBound F))
  let _ : LocallyCompactSpace (RegularTotalSpace F) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ := regularFamilyDeckAction F
  refine ⟨fun g ↦ ?_⟩
  exact (regularFamilyDeckMap_contMDiff F hproper g).continuous

/-- Under the explicit Fuchsian identification and source properness, the paper's punctured global
family is a complex threefold and its deck quotient projection is locally biholomorphic. -/
public theorem puncturedGlobalFamily_isManifold_and_projection_isLocalDiffeomorph
    (F : PeriodFunctions U) (hsource : U.sourceAction = fuchsianSourceAction)
    (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    letI := regularBaseChartedSpace hproper
    letI : LocallyCompactSpace (RegularBase (U := U)) :=
      (isOpen_isRegularBasePoint hproper).locallyCompactSpace
    letI : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder (RegularBase (U := U)) :=
      regularBase_isManifold hproper
    letI := familyIsCancelSMul (regularParameterMap F)
    letI := familyContinuousConstSMul (regularParameterMap F)
      fun a ↦ (regularPeriodSection_contMDiff F hproper a RegularSmoothnessOrder).continuous
    letI := familyProperlyDiscontinuousSMul (regularParameterMap F)
      (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap F)
        (regularParameterMap_compactUniformLowerBound F))
    letI : LocallyCompactSpace (RegularTotalSpace F) :=
      Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
    letI := regularFamilyDeckAction F
    letI := regularFamilyDeckAction_isCancelSMul_of_fuchsian F hsource hproper
    letI := regularFamilyDeckAction_properlyDiscontinuous_of_source F hproper
    letI := regularFamilyDeckAction_continuousConstSMul F hproper
    IsManifold GlobalDeckTotalModel RegularSmoothnessOrder (PuncturedGlobalFamily F) ∧
      IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
        (quotientProjection (M := RegularTotalSpace F) (G := Delta)) := by
  let _ := regularBaseChartedSpace hproper
  let _ : LocallyCompactSpace (RegularBase (U := U)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder (RegularBase (U := U)) :=
    regularBase_isManifold hproper
  let _ := familyIsCancelSMul (regularParameterMap F)
  let _ := familyContinuousConstSMul (regularParameterMap F)
    fun a ↦ (regularPeriodSection_contMDiff F hproper a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (regularParameterMap F)
    (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap F)
      (regularParameterMap_compactUniformLowerBound F))
  let _ : LocallyCompactSpace (RegularTotalSpace F) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ := regularFamilyDeckAction F
  let _ : IsCancelSMul Delta (RegularTotalSpace F) :=
    regularFamilyDeckAction_isCancelSMul_of_fuchsian F hsource hproper
  let _ : ProperlyDiscontinuousSMul Delta (RegularTotalSpace F) :=
    regularFamilyDeckAction_properlyDiscontinuous_of_source F hproper
  let _ : ContinuousConstSMul Delta (RegularTotalSpace F) :=
    regularFamilyDeckAction_continuousConstSMul F hproper
  have htotal := regularTotalSpace_isManifold_and_projection_isLocalDiffeomorph F hproper
    RegularSmoothnessOrder
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder (RegularTotalSpace F) :=
    htotal.1
  exact orbitQuotient_isManifold_and_projection_isLocalDiffeomorph_of_contMDiff_smul
    GlobalDeckTotalModel RegularSmoothnessOrder
      (fun g ↦ regularFamilyDeckMap_contMDiff F hproper g)

end

end SphereSixComplex.Geometry.GlobalTorusFamily
