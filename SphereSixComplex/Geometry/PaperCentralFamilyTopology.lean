module

public import SphereSixComplex.Geometry.PaperAnalyticData
public import SphereSixComplex.Geometry.FuchsianRegularTorusFamily
public import SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
public import SphereSixComplex.Geometry.ComplexModelRechart
public import SphereSixComplex.Geometry.EllipticCayleyHomeomorph
public import SphereSixComplex.Geometry.EllipticLocalTrivialization
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
open SphereSixComplex.Geometry.EllipticLocalTrivialization
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

/-- Removing the two countable elliptic orbits leaves the regular base path connected.  This
stronger form supplies actual paths between lifts of the two elliptic deck generators. -/
public theorem regularBase_pathConnected (U : TriangleUniformization) :
    PathConnectedSpace (RegularBase (U := U)) := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  have hpath : IsPathConnected (regularBadSet U)ᶜ :=
    (regularBadSet_countable U).isPathConnected_compl_of_one_lt_rank hrank
  let _ : PathConnectedSpace ↥((regularBadSet U)ᶜ) :=
    isPathConnected_iff_pathConnectedSpace.mp hpath
  exact (regularBaseHomeomorphComplexComplement U).symm.surjective.pathConnectedSpace
    (regularBaseHomeomorphComplexComplement U).symm.continuous

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

/-- The regular varying torus family is path connected, so a lift can be joined to each of its
triangle-group deck translates before projecting to the global quotient. -/
public theorem regularTotalSpace_pathConnected (F : PeriodFunctions U) :
    PathConnectedSpace (RegularTotalSpace F) := by
  let _ : PathConnectedSpace (RegularBase (U := U)) := regularBase_pathConnected U
  infer_instance

/-- The quotient of the regular torus family by the triangle group is connected. -/
public theorem puncturedGlobalFamily_connected (F : PeriodFunctions U) :
    letI := regularFamilyDeckAction F
    ConnectedSpace (PuncturedGlobalFamily F) := by
  let _ : ConnectedSpace (RegularBase (U := U)) := regularBase_connected U
  let _ := regularFamilyDeckAction F
  infer_instance

/-- The punctured global family is path connected as the quotient of the path-connected regular
torus family. -/
public theorem puncturedGlobalFamily_pathConnected (F : PeriodFunctions U) :
    letI := regularFamilyDeckAction F
    PathConnectedSpace (PuncturedGlobalFamily F) := by
  let _ : PathConnectedSpace (RegularTotalSpace F) := regularTotalSpace_pathConnected F
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
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
open SphereSixComplex.TriangleGroup.FuchsianProperFreeness

noncomputable section

namespace PaperAnalyticData

variable (A : PaperAnalyticData)

/-- Compact subsets of the regular source base have compact inverse image in the regular torus
family.  This is obtained by identifying the regular family with the regular open part of the
unexcised varying family, whose projection is already known to be proper. -/
public theorem regularTotalSpaceBase_isCompact_preimage
    {K : Set (RegularBase
      (U := A.modular.modularParameter.toTriangleUniformization))}
    (hK : IsCompact K) :
    IsCompact (regularTotalSpaceBase A.periods ⁻¹' K) := by
  let U := A.modular.modularParameter.toTriangleUniformization
  let hproper : SourceActionProperlyDiscontinuous (U := U) :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let K₀ : Set UpperHalfPlane := Subtype.val '' K
  have hK₀ : IsCompact K₀ := hK.image continuous_subtype_val
  let H : Set (TotalSpace (parameterMap A.periods)) :=
    EllipticWholeFiberCompactCover.familyTotalSpaceBase A.periods ⁻¹' K₀
  have hH : IsCompact H :=
    EllipticWholeFiberCompactCover.familyTotalSpaceBase_isCompact_preimage A.periods hK₀
  let e := regularFamilyPartHomeomorph A.periods hproper
  have hregular (q : H) :
      IsRegularBasePoint (U := U)
        (EllipticWholeFiberCompactCover.familyTotalSpaceBase A.periods q.1) := by
    obtain ⟨z, hzK, hz⟩ := q.2
    rw [← hz]
    exact z.property
  let f : H → RegularTotalSpace A.periods := fun q ↦ e.symm ⟨q.1, hregular q⟩
  have hf : Continuous f :=
    e.symm.continuous.comp
      (continuous_subtype_val.subtype_mk fun q ↦ hregular q)
  have himage : f '' Set.univ = regularTotalSpaceBase A.periods ⁻¹' K := by
    ext x
    constructor
    · rintro ⟨q, -, rfl⟩
      have hinc : regularFamilyInclusion A.periods (f q) = q.1 := by
        exact congrArg Subtype.val (e.apply_symm_apply ⟨q.1, hregular q⟩)
      have hbase := congrArg
        (EllipticWholeFiberCompactCover.familyTotalSpaceBase A.periods) hinc
      rw [familyTotalSpaceBase_regularFamilyInclusion] at hbase
      obtain ⟨z, hzK, hz⟩ := q.2
      have hzbase : regularTotalSpaceBase A.periods (f q) = z := by
        apply Subtype.ext
        exact hbase.trans hz.symm
      change regularTotalSpaceBase A.periods (f q) ∈ K
      rw [hzbase]
      exact hzK
    · intro hx
      let q : H := ⟨regularFamilyInclusion A.periods x, by
        change EllipticWholeFiberCompactCover.familyTotalSpaceBase A.periods
            (regularFamilyInclusion A.periods x) ∈ K₀
        rw [familyTotalSpaceBase_regularFamilyInclusion]
        exact ⟨regularTotalSpaceBase A.periods x, hx, rfl⟩⟩
      refine ⟨q, Set.mem_univ q, ?_⟩
      apply e.injective
      change ⟨regularFamilyInclusion A.periods (f q), _⟩ = e x
      apply Subtype.ext
      exact congrArg Subtype.val (e.apply_symm_apply ⟨q.1, hregular q⟩)
  rw [← himage]
  let _ : CompactSpace H := isCompact_iff_compactSpace.mp hH
  exact isCompact_univ.image hf

/-- The orbit space of the full upper-half-plane base, retaining the elliptic orbit points. -/
public abbrev FullBaseOrbitSpace (A : PaperAnalyticData) :=
  letI := triangleSourceMulAction A.modular.modularParameter.toTriangleUniformization
  OrbitQuotient (M := UpperHalfPlane) (G := Delta)

/-- The exact source orbifold coordinate identifies the full Fuchsian orbit space with the
complex affine line. -/
@[expose] public noncomputable def fullBaseOrbitHomeomorphComplex :
    A.FullBaseOrbitSpace ≃ₜ ℂ := by
  let U := A.modular.modularParameter.toTriangleUniformization
  let _ := triangleSourceMulAction U
  let C := A.modular.sourceCoordinate
  let f : C(UpperHalfPlane, ℂ) :=
    ⟨C.coordinate, C.coordinate_holomorphic.continuous⟩
  let e : Quotient (MulAction.orbitRel Delta UpperHalfPlane) ≃ₜ
      Quotient (Setoid.ker f) :=
    Homeomorph.Quotient.congrRight fun z w ↦ by
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨g, hg⟩
        calc
          C.coordinate z = C.coordinate (U.sourceAction g • w) := congrArg C.coordinate hg.symm
          _ = C.coordinate w := by
            rw [A.modular.modularParameter.toTriangleUniformization_sourceAction]
            exact C.coordinate_invariant g w
      · intro hzw
        obtain ⟨g, hg⟩ := (C.coordinate_eq_iff_orbit z w).mp hzw
        refine ⟨g⁻¹, ?_⟩
        change U.sourceAction g⁻¹ • w = z
        rw [A.modular.modularParameter.toTriangleUniformization_sourceAction]
        calc
          fuchsianSourceAction g⁻¹ • w =
              fuchsianSourceAction g⁻¹ • (fuchsianSourceAction g • z) :=
            congrArg _ hg.symm
          _ = z := by rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have hf : Topology.IsQuotientMap f := C.coordinate_isQuotientMap
  exact e.trans hf.homeomorph

@[simp]
public theorem fullBaseOrbitHomeomorphComplex_mk (z : UpperHalfPlane) :
    A.fullBaseOrbitHomeomorphComplex (Quotient.mk _ z) =
      A.modular.sourceCoordinate.coordinate z := by
  rfl

@[simp]
public theorem fullBaseOrbitHomeomorphComplex_orderThree :
    A.fullBaseOrbitHomeomorphComplex
        (Quotient.mk _ A.modular.modularParameter.toTriangleUniformization.zOne) = 0 := by
  rw [A.fullBaseOrbitHomeomorphComplex_mk]
  exact A.modular.sourceCoordinate.coordinate_at_one

@[simp]
public theorem fullBaseOrbitHomeomorphComplex_orderFour :
    A.fullBaseOrbitHomeomorphComplex
        (Quotient.mk _ A.modular.modularParameter.toTriangleUniformization.zTwo) = 1 := by
  rw [A.fullBaseOrbitHomeomorphComplex_mk]
  exact A.modular.sourceCoordinate.coordinate_at_two

/-- A sufficiently small normalized-coordinate ball about zero is represented by any prescribed
positive order-three Cayley collar.  This is the quotient-openness bridge from the global
orbifold coordinate to the explicit elliptic coordinate used by the filling. -/
public theorem exists_orderThree_fullBaseCoordinate_ball_cayley
    (r : ℝ) (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ Q : A.FullBaseOrbitSpace,
      dist (A.fullBaseOrbitHomeomorphComplex Q) 0 < ε →
        ∃ z : UpperHalfPlane,
          ‖(EllipticCayleyHomeomorph.orderThreeCayleyHomeomorph z).1‖ < r ∧
            Q = Quotient.mk _ z := by
  let U := A.modular.modularParameter.toTriangleUniformization
  let hsource : U.sourceAction = fuchsianSourceAction :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  let _ := triangleSourceMulAction U
  let _ : ContinuousConstSMul Delta UpperHalfPlane := ⟨fun g => by
    change Continuous (fun z : UpperHalfPlane => U.sourceAction g • z)
    rw [hsource]
    exact (fuchsianSourceAction_contMDiff g 0).continuous⟩
  let S : Set UpperHalfPlane :=
    {z | ‖(EllipticCayleyHomeomorph.orderThreeCayleyHomeomorph z).1‖ < r}
  have hSopen : IsOpen S := by
    exact isOpen_lt
      (continuous_norm.comp
        (continuous_subtype_val.comp
          EllipticCayleyHomeomorph.orderThreeCayleyHomeomorph.continuous))
      continuous_const
  let q : UpperHalfPlane → A.FullBaseOrbitSpace := Quotient.mk _
  let V : Set A.FullBaseOrbitSpace := q '' S
  have hVopen : IsOpen V := isOpenMap_quotient_mk'_mul S hSopen
  have hfixed := ellipticFixedPoints_eq_of_fuchsian hsource
  have hcenterS : fuchsianOneFixedPoint ∈ S := by
    change ‖(EllipticCayleyHomeomorph.orderThreeCayleyHomeomorph
      fuchsianOneFixedPoint).1‖ < r
    rw [EllipticLocalTrivialization.orderThreeCayleyHomeomorph_fixedPoint]
    simpa [SphereSixComplex.Geometry.EllipticLocalCoordinates.discCenter] using hr
  have hzero : (0 : ℂ) ∈ A.fullBaseOrbitHomeomorphComplex '' V := by
    refine ⟨q fuchsianOneFixedPoint, ⟨fuchsianOneFixedPoint, hcenterS, rfl⟩, ?_⟩
    change A.fullBaseOrbitHomeomorphComplex
        (Quotient.mk _ fuchsianOneFixedPoint) = 0
    rw [← hfixed.1, A.fullBaseOrbitHomeomorphComplex_orderThree]
  have hopen : IsOpen (A.fullBaseOrbitHomeomorphComplex '' V) :=
    A.fullBaseOrbitHomeomorphComplex.isOpenMap V hVopen
  obtain ⟨ε, hε, hball⟩ := (Metric.isOpen_iff.mp hopen) 0 hzero
  refine ⟨ε, hε, ?_⟩
  intro Q hQ
  have hQball : A.fullBaseOrbitHomeomorphComplex Q ∈ Metric.ball (0 : ℂ) ε := by
    simpa only [Metric.mem_ball, dist_zero_right] using hQ
  obtain ⟨Q', hQ'V, hcoord⟩ := hball hQball
  obtain ⟨z, hzS, rfl⟩ := hQ'V
  refine ⟨z, hzS, ?_⟩
  exact A.fullBaseOrbitHomeomorphComplex.injective hcoord.symm

/-- A sufficiently small normalized-coordinate ball about one is represented by any prescribed
positive order-four Cayley collar. -/
public theorem exists_orderFour_fullBaseCoordinate_ball_cayley
    (r : ℝ) (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ Q : A.FullBaseOrbitSpace,
      dist (A.fullBaseOrbitHomeomorphComplex Q) 1 < ε →
        ∃ z : UpperHalfPlane,
          ‖(EllipticCayleyHomeomorph.orderFourCayleyHomeomorph z).1‖ < r ∧
            Q = Quotient.mk _ z := by
  let U := A.modular.modularParameter.toTriangleUniformization
  let hsource : U.sourceAction = fuchsianSourceAction :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  let _ := triangleSourceMulAction U
  let _ : ContinuousConstSMul Delta UpperHalfPlane := ⟨fun g => by
    change Continuous (fun z : UpperHalfPlane => U.sourceAction g • z)
    rw [hsource]
    exact (fuchsianSourceAction_contMDiff g 0).continuous⟩
  let S : Set UpperHalfPlane :=
    {z | ‖(EllipticCayleyHomeomorph.orderFourCayleyHomeomorph z).1‖ < r}
  have hSopen : IsOpen S := by
    exact isOpen_lt
      (continuous_norm.comp
        (continuous_subtype_val.comp
          EllipticCayleyHomeomorph.orderFourCayleyHomeomorph.continuous))
      continuous_const
  let q : UpperHalfPlane → A.FullBaseOrbitSpace := Quotient.mk _
  let V : Set A.FullBaseOrbitSpace := q '' S
  have hVopen : IsOpen V := isOpenMap_quotient_mk'_mul S hSopen
  have hfixed := ellipticFixedPoints_eq_of_fuchsian hsource
  have hcenterS : fuchsianTwoFixedPoint ∈ S := by
    change ‖(EllipticCayleyHomeomorph.orderFourCayleyHomeomorph
      fuchsianTwoFixedPoint).1‖ < r
    rw [EllipticLocalTrivialization.orderFourCayleyHomeomorph_fixedPoint]
    simpa [SphereSixComplex.Geometry.EllipticLocalCoordinates.discCenter] using hr
  have hone : (1 : ℂ) ∈ A.fullBaseOrbitHomeomorphComplex '' V := by
    refine ⟨q fuchsianTwoFixedPoint, ⟨fuchsianTwoFixedPoint, hcenterS, rfl⟩, ?_⟩
    change A.fullBaseOrbitHomeomorphComplex
        (Quotient.mk _ fuchsianTwoFixedPoint) = 1
    rw [← hfixed.2, A.fullBaseOrbitHomeomorphComplex_orderFour]
  have hopen : IsOpen (A.fullBaseOrbitHomeomorphComplex '' V) :=
    A.fullBaseOrbitHomeomorphComplex.isOpenMap V hVopen
  obtain ⟨ε, hε, hball⟩ := (Metric.isOpen_iff.mp hopen) 1 hone
  refine ⟨ε, hε, ?_⟩
  intro Q hQ
  have hQball : A.fullBaseOrbitHomeomorphComplex Q ∈ Metric.ball (1 : ℂ) ε := by
    simpa only [Metric.mem_ball] using hQ
  obtain ⟨Q', hQ'V, hcoord⟩ := hball hQball
  obtain ⟨z, hzS, rfl⟩ := hQ'V
  refine ⟨z, hzS, ?_⟩
  exact A.fullBaseOrbitHomeomorphComplex.injective hcoord.symm

/-- A compact part of the full quotient base, bounded away from both elliptic values.  The
outer closed ball also cuts off the affine cusp end. -/
@[expose] public noncomputable def fullBaseCompactCore (R ε : ℝ) :
    Set A.FullBaseOrbitSpace :=
  A.fullBaseOrbitHomeomorphComplex ⁻¹'
    (Metric.closedBall 0 R \ (Metric.ball 0 ε ∪ Metric.ball 1 ε))

/-- The explicit bounded-away-from-the-ends core of the quotient base is compact. -/
public theorem fullBaseCompactCore_isCompact (R ε : ℝ) :
    IsCompact (A.fullBaseCompactCore R ε) := by
  apply A.fullBaseOrbitHomeomorphComplex.isCompact_preimage.mpr
  exact (ProperSpace.isCompact_closedBall (0 : ℂ) R).diff
    (Metric.isOpen_ball.union Metric.isOpen_ball)

/-- The quotient-coordinate description of membership in the compact base core. -/
public theorem mk_mem_fullBaseCompactCore_iff (R ε : ℝ) (z : UpperHalfPlane) :
    (Quotient.mk _ z : A.FullBaseOrbitSpace) ∈ A.fullBaseCompactCore R ε ↔
      A.modular.sourceCoordinate.coordinate z ∈ Metric.closedBall 0 R ∧
      A.modular.sourceCoordinate.coordinate z ∉ Metric.ball 0 ε ∧
      A.modular.sourceCoordinate.coordinate z ∉ Metric.ball 1 ε := by
  simp [fullBaseCompactCore]

/-- Avoiding the two normalized elliptic values forces a source point to lie in the regular
base. -/
public theorem isRegularBasePoint_of_sourceCoordinate_ne
    (z : UpperHalfPlane)
    (hzero : A.modular.sourceCoordinate.coordinate z ≠ 0)
    (hone : A.modular.sourceCoordinate.coordinate z ≠ 1) :
    IsRegularBasePoint
      (U := A.modular.modularParameter.toTriangleUniformization) z := by
  let U := A.modular.modularParameter.toTriangleUniformization
  rw [isRegularBasePoint_iff_not_mem_orbits]
  rintro (hz | hz)
  · simp only [sourceOrbitSet, Set.mem_iUnion, Set.mem_singleton_iff] at hz
    obtain ⟨g, hg⟩ := hz
    apply hzero
    calc
      A.modular.sourceCoordinate.coordinate z =
          A.modular.sourceCoordinate.coordinate (U.sourceAction g • U.zOne) :=
        congrArg A.modular.sourceCoordinate.coordinate hg
      _ = A.modular.sourceCoordinate.coordinate U.zOne := by
        rw [A.modular.modularParameter.toTriangleUniformization_sourceAction]
        exact A.modular.sourceCoordinate.coordinate_invariant g U.zOne
      _ = 0 := A.modular.sourceCoordinate.coordinate_at_one
  · simp only [sourceOrbitSet, Set.mem_iUnion, Set.mem_singleton_iff] at hz
    obtain ⟨g, hg⟩ := hz
    apply hone
    calc
      A.modular.sourceCoordinate.coordinate z =
          A.modular.sourceCoordinate.coordinate (U.sourceAction g • U.zTwo) :=
        congrArg A.modular.sourceCoordinate.coordinate hg
      _ = A.modular.sourceCoordinate.coordinate U.zTwo := by
        rw [A.modular.modularParameter.toTriangleUniformization_sourceAction]
        exact A.modular.sourceCoordinate.coordinate_invariant g U.zTwo
      _ = 1 := A.modular.sourceCoordinate.coordinate_at_two

/-- A compact set of regular quotient-coordinate values is covered by the coordinate image of
one compact set upstairs.  This is the finite-sheet-selection consequence of the exact covering
map away from the two elliptic values. -/
public theorem exists_compact_source_coordinate_cover
    {K : Set ℂ} (hK : IsCompact K) (hregular : K ⊆ ({0, 1} : Set ℂ)ᶜ) :
    ∃ L : Set UpperHalfPlane, IsCompact L ∧
      L ⊆ A.modular.sourceCoordinate.coordinate ⁻¹' K ∧
      K ⊆ A.modular.sourceCoordinate.coordinate '' L := by
  classical
  let C := A.modular.sourceCoordinate
  have hsurj : Function.Surjective C.coordinate := C.coordinate_isQuotientMap.surjective
  let x (y : K) : UpperHalfPlane := Classical.choose (hsurj y.1)
  have hx (y : K) : C.coordinate (x y) = y.1 :=
    Classical.choose_spec (hsurj y.1)
  let i (y : K) : C.coordinate ⁻¹' ({y.1} : Set ℂ) :=
    ⟨x y, by simpa [Set.mem_preimage] using hx y⟩
  let cov (y : K) := C.regular_covering y.1 (hregular y.2)
  let t (y : K) :
      Bundle.Trivialization (C.coordinate ⁻¹' ({y.1} : Set ℂ)) C.coordinate := by
    let _ : Nonempty (C.coordinate ⁻¹' ({y.1} : Set ℂ)) := ⟨i y⟩
    exact (cov y).toTrivialization
  have htmem (y : K) : y.1 ∈ (t y).baseSet := by
    let _ : Nonempty (C.coordinate ⁻¹' ({y.1} : Set ℂ)) := ⟨i y⟩
    exact (cov y).mem_toTrivialization_baseSet
  choose B hBcompact hyB hBsub using fun y : K ↦
    exists_compact_subset (t y).open_baseSet (htmem y)
  let localSection (y : K) (z : B y) : UpperHalfPlane :=
    (t y).invFun (z.1, i y)
  have hsection_continuous (y : K) : Continuous (localSection y) := by
    apply (t y).continuousOn_invFun.comp_continuous
      (continuous_subtype_val.prodMk continuous_const)
    intro z
    exact (t y).mem_target.mpr (hBsub y z.2)
  let S (y : K) : Set UpperHalfPlane := localSection y '' Set.univ
  have hScompact (y : K) : IsCompact (S y) := by
    let _ : CompactSpace (B y) := isCompact_iff_compactSpace.mp (hBcompact y)
    exact isCompact_univ.image (hsection_continuous y)
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun y : K ↦ interior (B y)) (fun _ ↦ isOpen_interior) (by
      intro y hy
      exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hyB ⟨y, hy⟩⟩)
  let L₀ : Set UpperHalfPlane := ⋃ y ∈ s, S y
  have hL₀compact : IsCompact L₀ :=
    s.isCompact_biUnion fun y _ ↦ hScompact y
  let L : Set UpperHalfPlane := L₀ ∩ C.coordinate ⁻¹' K
  refine ⟨L, hL₀compact.inter_right (hK.isClosed.preimage C.coordinate_holomorphic.continuous),
    Set.inter_subset_right, ?_⟩
  intro y hy
  obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp (hs hy)
  let z : B j := ⟨y, interior_subset hyj⟩
  have hcoordinate : C.coordinate (localSection j z) = y :=
    (t j).proj_symm_apply' (hBsub j z.2)
  refine ⟨localSection j z, ⟨Set.mem_iUnion₂.mpr
    ⟨j, hj, ⟨z, Set.mem_univ z, rfl⟩⟩, ?_⟩, hcoordinate⟩
  change C.coordinate (localSection j z) ∈ K
  rw [hcoordinate]
  exact hy

/-- Every positive-width compact quotient-base core is covered by the quotient image of a compact
set of regular source representatives. -/
public theorem exists_compact_regular_source_cover_fullBaseCompactCore
    (R ε : ℝ) (hε : 0 < ε) :
    ∃ L : Set UpperHalfPlane, IsCompact L ∧
      (∀ z ∈ L, (Quotient.mk _ z : A.FullBaseOrbitSpace) ∈
        A.fullBaseCompactCore R ε) ∧
      (∀ z ∈ L, IsRegularBasePoint
        (U := A.modular.modularParameter.toTriangleUniformization) z) ∧
      A.fullBaseCompactCore R ε ⊆
        (fun z : UpperHalfPlane ↦
          (Quotient.mk _ z : A.FullBaseOrbitSpace)) '' L := by
  let K : Set ℂ :=
    Metric.closedBall 0 R \ (Metric.ball 0 ε ∪ Metric.ball 1 ε)
  have hKcompact : IsCompact K :=
    (ProperSpace.isCompact_closedBall (0 : ℂ) R).diff
      (Metric.isOpen_ball.union Metric.isOpen_ball)
  have hKregular : K ⊆ ({0, 1} : Set ℂ)ᶜ := by
    intro y hy
    have hzero : y ≠ 0 := by
      intro h
      apply hy.2
      left
      rw [h]
      exact Metric.mem_ball_self hε
    have hone : y ≠ 1 := by
      intro h
      apply hy.2
      right
      rw [h]
      exact Metric.mem_ball_self hε
    simp [Set.mem_compl_iff, hzero, hone]
  obtain ⟨L, hLcompact, hLsub, hLcover⟩ :=
    A.exists_compact_source_coordinate_cover hKcompact hKregular
  refine ⟨L, hLcompact, ?_, ?_, ?_⟩
  · intro z hz
    change A.modular.sourceCoordinate.coordinate z ∈ K
    exact hLsub hz
  · intro z hz
    have hzK := hLsub hz
    exact A.isRegularBasePoint_of_sourceCoordinate_ne z
      (fun hzero ↦ (hKregular hzK) (by simp [hzero]))
      (fun hone ↦ (hKregular hzK) (by simp [hone]))
  · intro q hq
    have hqK : A.fullBaseOrbitHomeomorphComplex q ∈ K := hq
    obtain ⟨z, hzL, hz⟩ := hLcover hqK
    refine ⟨z, hzL, ?_⟩
    apply A.fullBaseOrbitHomeomorphComplex.injective
    rw [A.fullBaseOrbitHomeomorphComplex_mk]
    exact hz

/-- Forget the torus coordinate of the central family while retaining the full base orbit. -/
@[expose] public noncomputable def centralBaseOrbit :
    A.CentralFamily → A.FullBaseOrbitSpace := by
  let U := A.modular.modularParameter.toTriangleUniformization
  let _ := triangleSourceMulAction U
  let _ := regularFamilyDeckAction A.periods
  refine Quotient.map (fun x => (regularTotalSpaceBase A.periods x).1) ?_
  intro x y hxy
  change MulAction.orbitRel Delta (RegularTotalSpace A.periods) x y at hxy
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hxy
  change MulAction.orbitRel Delta UpperHalfPlane
    (regularTotalSpaceBase A.periods x).1 (regularTotalSpaceBase A.periods y).1
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  obtain ⟨g, hg⟩ := hxy
  refine ⟨g, ?_⟩
  calc
    U.sourceAction g • (regularTotalSpaceBase A.periods y).1 =
        (regularTotalSpaceBase A.periods
          (regularFamilyDeckMap A.periods g y)).1 :=
      congrArg Subtype.val
        (regularTotalSpaceBase_familyDeckMap A.periods g y).symm
    _ = (regularTotalSpaceBase A.periods x).1 :=
      congrArg (fun z ↦ (regularTotalSpaceBase A.periods z).1) hg

@[simp]
public theorem centralBaseOrbit_mk (x : RegularTotalSpace A.periods) :
    A.centralBaseOrbit (Quotient.mk _ x) =
      Quotient.mk _ (regularTotalSpaceBase A.periods x).1 :=
  rfl

/-- The base-orbit projection of the central family is continuous. -/
public theorem centralBaseOrbit_continuous : Continuous A.centralBaseOrbit := by
  rw [centralBaseOrbit.eq_def]
  exact continuous_quot_map _
    (continuous_subtype_val.comp (regularTotalSpaceBase_continuous A.periods))

/-- The normalized complex coordinate of the base orbit underlying a central-family point. -/
@[expose] public noncomputable def centralBaseCoordinate : A.CentralFamily → ℂ :=
  A.fullBaseOrbitHomeomorphComplex ∘ A.centralBaseOrbit

@[simp]
public theorem centralBaseCoordinate_mk (x : RegularTotalSpace A.periods) :
    A.centralBaseCoordinate (Quotient.mk _ x) =
      A.modular.sourceCoordinate.coordinate (regularTotalSpaceBase A.periods x).1 := by
  simp [centralBaseCoordinate]

/-- The normalized base coordinate on the central family is continuous. -/
public theorem centralBaseCoordinate_continuous : Continuous A.centralBaseCoordinate :=
  A.fullBaseOrbitHomeomorphComplex.continuous.comp A.centralBaseOrbit_continuous

/-- The part of the central family lying over the explicit bounded quotient-base core. -/
@[expose] public noncomputable def centralBaseCompactCore (R ε : ℝ) :
    Set A.CentralFamily :=
  A.centralBaseOrbit ⁻¹' A.fullBaseCompactCore R ε

/-- Positive-width bounded quotient-base cores have compact total space in the actual descended
regular torus family. -/
public theorem centralBaseCompactCore_isCompact
    (R ε : ℝ) (hε : 0 < ε) :
    IsCompact (A.centralBaseCompactCore R ε) := by
  let U := A.modular.modularParameter.toTriangleUniformization
  obtain ⟨L, hLcompact, hLcore, hLregular, hLcover⟩ :=
    A.exists_compact_regular_source_cover_fullBaseCompactCore R ε hε
  let K : Set (RegularBase (U := U)) := Subtype.val ⁻¹' L
  have hKcompact : IsCompact K := by
    apply Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hLcompact
    intro z hz
    exact ⟨⟨z, hLregular z hz⟩, rfl⟩
  let P : Set (RegularTotalSpace A.periods) :=
    regularTotalSpaceBase A.periods ⁻¹' K
  have hPcompact : IsCompact P :=
    A.regularTotalSpaceBase_isCompact_preimage hKcompact
  let _ := triangleSourceMulAction U
  let _ := regularFamilyDeckAction A.periods
  let q : RegularTotalSpace A.periods → A.CentralFamily := Quotient.mk _
  have hset : A.centralBaseCompactCore R ε = q '' P := by
    ext C
    constructor
    · intro hC
      induction C using Quotient.inductionOn with
      | _ x =>
          change A.centralBaseOrbit (Quotient.mk _ x) ∈
            A.fullBaseCompactCore R ε at hC
          rw [A.centralBaseOrbit_mk] at hC
          obtain ⟨z, hzL, hzq⟩ := hLcover hC
          have hrel := Quotient.exact hzq
          change MulAction.orbitRel Delta UpperHalfPlane z
            (regularTotalSpaceBase A.periods x).1 at hrel
          rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
          obtain ⟨g, hg⟩ := hrel
          let x' := regularFamilyDeckMap A.periods g x
          have hx'base : regularTotalSpaceBase A.periods x' =
              ⟨z, hLregular z hzL⟩ := by
            rw [regularTotalSpaceBase_familyDeckMap]
            apply Subtype.ext
            exact hg
          have hx'P : x' ∈ P := by
            change regularTotalSpaceBase A.periods x' ∈ K
            change (regularTotalSpaceBase A.periods x').1 ∈ L
            rw [hx'base]
            exact hzL
          refine ⟨x', hx'P, ?_⟩
          apply Quotient.sound
          change MulAction.orbitRel Delta (RegularTotalSpace A.periods) x' x
          rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
          exact ⟨g, rfl⟩
    · rintro ⟨x, hxP, rfl⟩
      change A.centralBaseOrbit (Quotient.mk _ x) ∈
        A.fullBaseCompactCore R ε
      rw [A.centralBaseOrbit_mk]
      apply hLcore
      exact hxP
  rw [hset]
  exact hPcompact.image continuous_quotient_mk'

/-- A central-family point never lies over the deleted order-three elliptic orbit. -/
public theorem centralBaseOrbit_ne_orderThree (C : A.CentralFamily) :
    A.centralBaseOrbit C ≠
      (Quotient.mk _ A.modular.modularParameter.toTriangleUniformization.zOne :
        A.FullBaseOrbitSpace) := by
  let U := A.modular.modularParameter.toTriangleUniformization
  let _ := triangleSourceMulAction U
  let _ := regularFamilyDeckAction A.periods
  induction C using Quotient.inductionOn with
  | _ x =>
      intro h
      rw [A.centralBaseOrbit_mk] at h
      have hrel := Quotient.exact h
      change MulAction.orbitRel Delta UpperHalfPlane
        (regularTotalSpaceBase A.periods x).1 U.zOne at hrel
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
      obtain ⟨g, hg⟩ := hrel
      have hnot := (isRegularBasePoint_iff_not_mem_orbits
        (U := U) (regularTotalSpaceBase A.periods x).1).mp
          (regularTotalSpaceBase A.periods x).property
      apply hnot
      left
      simp only [sourceOrbitSet, Set.mem_iUnion, Set.mem_singleton_iff]
      exact ⟨g, hg.symm⟩

/-- A central-family point never lies over the deleted order-four elliptic orbit. -/
public theorem centralBaseOrbit_ne_orderFour (C : A.CentralFamily) :
    A.centralBaseOrbit C ≠
      (Quotient.mk _ A.modular.modularParameter.toTriangleUniformization.zTwo :
        A.FullBaseOrbitSpace) := by
  let U := A.modular.modularParameter.toTriangleUniformization
  let _ := triangleSourceMulAction U
  let _ := regularFamilyDeckAction A.periods
  induction C using Quotient.inductionOn with
  | _ x =>
      intro h
      rw [A.centralBaseOrbit_mk] at h
      have hrel := Quotient.exact h
      change MulAction.orbitRel Delta UpperHalfPlane
        (regularTotalSpaceBase A.periods x).1 U.zTwo at hrel
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
      obtain ⟨g, hg⟩ := hrel
      have hnot := (isRegularBasePoint_iff_not_mem_orbits
        (U := U) (regularTotalSpaceBase A.periods x).1).mp
          (regularTotalSpaceBase A.periods x).property
      apply hnot
      right
      simp only [sourceOrbitSet, Set.mem_iUnion, Set.mem_singleton_iff]
      exact ⟨g, hg.symm⟩

/-- The deleted order-three orbit is exactly the missing normalized value zero. -/
public theorem centralBaseCoordinate_ne_zero (C : A.CentralFamily) :
    A.centralBaseCoordinate C ≠ 0 := by
  intro h
  apply A.centralBaseOrbit_ne_orderThree C
  apply A.fullBaseOrbitHomeomorphComplex.injective
  change A.centralBaseCoordinate C = _
  rw [h, A.fullBaseOrbitHomeomorphComplex_orderThree]

/-- The deleted order-four orbit is exactly the missing normalized value one. -/
public theorem centralBaseCoordinate_ne_one (C : A.CentralFamily) :
    A.centralBaseCoordinate C ≠ 1 := by
  intro h
  apply A.centralBaseOrbit_ne_orderFour C
  apply A.fullBaseOrbitHomeomorphComplex.injective
  change A.centralBaseCoordinate C = _
  rw [h, A.fullBaseOrbitHomeomorphComplex_orderFour]

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

/-- The selected central family quotient is Hausdorff. -/
public theorem centralFamily_t2 : T2Space A.CentralFamily := by
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
    fun a => (periodSection_contMDiff A.periods a RegularSmoothnessOrder).continuous.comp
      continuous_subtype_val
  let _ := familyProperlyDiscontinuousSMul (regularParameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap A.periods)
      (regularParameterMap_compactUniformLowerBound A.periods))
  have htotal := regularTotalSpace_isManifold_and_projection_isLocalDiffeomorph
    A.periods hproper RegularSmoothnessOrder
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (RegularTotalSpace A.periods) := htotal.1
  let _ : LocallyCompactSpace (RegularTotalSpace A.periods) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ : T2Space (RegularTotalSpace A.periods) := by infer_instance
  let _ := regularFamilyDeckAction A.periods
  let _ : ProperlyDiscontinuousSMul Delta (RegularTotalSpace A.periods) :=
    regularFamilyDeckAction_properlyDiscontinuous_of_source A.periods hproper
  let _ : ContinuousConstSMul Delta (RegularTotalSpace A.periods) :=
    regularFamilyDeckAction_continuousConstSMul A.periods hproper
  infer_instance

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
