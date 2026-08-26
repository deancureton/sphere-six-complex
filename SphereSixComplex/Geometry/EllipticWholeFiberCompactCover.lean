module

public import SphereSixComplex.Geometry.EllipticWholeFiberTrivialization
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import all SphereSixComplex.Geometry.Quotient
import all SphereSixComplex.Geometry.TorusFamily

/-!
# Compact covers of the elliptic fibres

The central torus fibre is the image of a compact real period cube.  Consequently the pointwise
local inverse charts admit a finite subcover.  The transition formula below identifies the exact
lattice condition required for their fixed-torus-valued maps to agree off the central fibre.
-/

open scoped Manifold ContDiff

namespace SphereSixComplex.Geometry.EllipticWholeFiberCompactCover

open Filter Set SphereSixComplex.Geometry
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.EllipticLocalTrivialization
open SphereSixComplex.Geometry.EllipticWholeFiberTrivialization
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticFixedPointCriterion
open SphereSixComplex.TriangleGroup SphereSixComplex.Periods

noncomputable section

variable {U : TriangleUniformization} (F : PeriodFunctions U)

/-- Fibrewise period translations preserve the base coordinate. -/
public theorem familyTotalSpaceBase_respects
    (p q : UpperHalfPlane × ComplexTwoSpace)
    (h : MulAction.orbitRel (FamilyPeriodGroup (parameterMap F)) _ p q) :
    p.1 = q.1 := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  obtain ⟨g, hg⟩ := h
  simpa only [family_smul_fst] using congrArg Prod.fst hg.symm

/-- The base point of the global varying-torus quotient. -/
@[expose] public noncomputable def familyTotalSpaceBase :
    TotalSpace (parameterMap F) → UpperHalfPlane :=
  Quotient.lift Prod.fst (familyTotalSpaceBase_respects F)

@[simp]
public theorem familyTotalSpaceBase_mk (p : UpperHalfPlane × ComplexTwoSpace) :
    familyTotalSpaceBase F (Quotient.mk _ p) = p.1 :=
  rfl

@[simp]
public theorem familyTotalSpaceBase_projection (p : UpperHalfPlane × ComplexTwoSpace) :
    familyTotalSpaceBase F (projection (parameterMap F) p) = p.1 := by
  rw [projection.eq_def]
  exact familyTotalSpaceBase_mk F p

/-- The fibre of the varying torus quotient over a specified base point. -/
@[expose] public def familyFiber (z : UpperHalfPlane) :
    Set (TotalSpace (parameterMap F)) :=
  Set.range fun v : ComplexTwoSpace ↦ projection (parameterMap F) (z, v)

/-- Parametrization of one fibre by the real coordinates of its period basis. -/
@[expose] public noncomputable def familyFiberRealParam (z : UpperHalfPlane) :
    RealPeriods → TotalSpace (parameterMap F) := fun r ↦
  projection (parameterMap F)
    (z, (fullRankDomain (parameterMap F z)).realEquiv r)

public theorem familyFiberRealParam_continuous (z : UpperHalfPlane) :
    Continuous (familyFiberRealParam F z) := by
  change Continuous (fun r : RealPeriods ↦ projection (parameterMap F)
    (z, (fullRankDomain (parameterMap F z)).realEquiv r))
  rw [projection.eq_def, quotientProjection.eq_def]
  exact continuous_quot_mk.comp
    (continuous_const.prodMk (fullRankDomain (parameterMap F z)).realEquiv.continuous)

/-- The closed unit cube in real period coordinates covers the entire quotient fibre. -/
public theorem familyFiber_eq_image_unitCube (z : UpperHalfPlane) :
    familyFiber F z = familyFiberRealParam F z '' Set.Icc 0 1 := by
  apply Set.Subset.antisymm
  · rintro q ⟨v, rfl⟩
    let hfull := fullRankDomain (parameterMap F z)
    let r : RealPeriods := hfull.realEquiv.symm v
    let a : IntegerPeriods := fun i ↦ ⌊ r i ⌋
    let u : RealPeriods := r - integerToReal a
    have hu : u ∈ Set.Icc (0 : RealPeriods) 1 := by
      constructor
      · intro i
        exact sub_nonneg.mpr (Int.floor_le (r i))
      · intro i
        change r i - integerToReal a i ≤ (1 : ℝ)
        rw [show integerToReal a i = (a i : ℝ) by rfl]
        exact le_of_lt (sub_lt_iff_lt_add.mpr <| by
          simpa [add_comm] using Int.lt_floor_add_one (r i))
    refine ⟨u, hu, ?_⟩
    change projection (parameterMap F) (z, hfull.realEquiv u) =
      projection (parameterMap F) (z, v)
    rw [projection.eq_def, quotientProjection.eq_def]
    apply Quotient.sound
    change (MulAction.orbitRel (FamilyPeriodGroup (parameterMap F))
      (UpperHalfPlane × ComplexTwoSpace))
      (z, hfull.realEquiv u) (z, v)
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    let g : FamilyPeriodGroup (parameterMap F) := Multiplicative.ofAdd (-a)
    refine ⟨g, ?_⟩
    apply Prod.ext
    · rfl
    · change periodVector (parameterMap F z).1 (-a) + v = hfull.realEquiv u
      rw [show periodVector (parameterMap F z).1 (-a) =
          -periodVector (parameterMap F z).1 a by
        have ha := periodVector_add (parameterMap F z).1 (-a) a
        rw [neg_add_cancel, periodVector_zero] at ha
        exact eq_neg_of_add_eq_zero_left ha.symm]
      rw [← hfull.map_integer]
      change -hfull.realEquiv (integerToReal a) + v =
        hfull.realEquiv (r - integerToReal a)
      rw [map_sub, hfull.realEquiv.apply_symm_apply]
      abel
  · rintro q ⟨r, _hr, rfl⟩
    exact ⟨(fullRankDomain (parameterMap F z)).realEquiv r, rfl⟩

/-- Every fibre of the varying torus quotient is compact. -/
public theorem familyFiber_isCompact (z : UpperHalfPlane) :
    IsCompact (familyFiber F z) := by
  rw [familyFiber_eq_image_unitCube F z]
  exact isCompact_Icc.image (familyFiberRealParam_continuous F z)

/-- Every point of the varying torus family lies in the fibre over its descended base point. -/
public theorem mem_familyFiber_familyTotalSpaceBase
    (q : TotalSpace (parameterMap F)) :
    q ∈ familyFiber F (familyTotalSpaceBase F q) := by
  induction q using Quotient.inductionOn with
  | _ p =>
      exact ⟨p.2, rfl⟩

/-- Simultaneous fundamental-cube parametrization of the varying torus family. -/
@[expose] public noncomputable def familyFundamentalCubeParam
    (p : UpperHalfPlane × RealPeriods) : TotalSpace (parameterMap F) :=
  projection (parameterMap F)
    (p.1, (fullRankDomain (parameterMap F p.1)).realEquiv p.2)

/-- The fundamental-cube parametrization varies continuously with the base point. -/
public theorem familyFundamentalCubeParam_continuous :
    Continuous (familyFundamentalCubeParam F) := by
  have h : Continuous (fun p : UpperHalfPlane × RealPeriods ↦
      projection (parameterMap F)
        (p.1, periodRealLinear (parameterMap F p.1).1 p.2)) := by
    rw [projection.eq_def, quotientProjection.eq_def]
    exact continuous_quot_mk.comp
      (continuous_fst.prodMk (periodRealLinear_parameterMap_continuous F))
  convert h using 1
  funext p
  rw [familyFundamentalCubeParam.eq_def, fullRankDomain.eq_def]
  rw [FullRank.ofSetupInequalities_realEquiv_apply]

/-- The inverse image of a compact base set is covered exactly by its compact family of real
fundamental cubes.  This is the uniform compactness statement needed to control collar ends. -/
public theorem familyTotalSpaceBase_preimage_eq_fundamentalCube_image
    (K : Set UpperHalfPlane) :
    familyTotalSpaceBase F ⁻¹' K =
      familyFundamentalCubeParam F '' (K ×ˢ Set.Icc (0 : RealPeriods) 1) := by
  ext q
  constructor
  · intro hq
    have hfiber := mem_familyFiber_familyTotalSpaceBase F q
    rw [familyFiber_eq_image_unitCube F (familyTotalSpaceBase F q)] at hfiber
    obtain ⟨r, hr, hparam⟩ := hfiber
    exact ⟨(familyTotalSpaceBase F q, r), ⟨hq, hr⟩, hparam⟩
  · rintro ⟨p, hp, rfl⟩
    change familyTotalSpaceBase F
      (projection (parameterMap F)
        (p.1, (fullRankDomain (parameterMap F p.1)).realEquiv p.2)) ∈ K
    simpa using hp.1

/-- The base projection of the varying torus family has compact inverse images of compact sets.
This strengthens pointwise compactness of the fibres to the uniform compactness needed at the
boundary of a gluing collar. -/
public theorem familyTotalSpaceBase_isCompact_preimage
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    IsCompact (familyTotalSpaceBase F ⁻¹' K) := by
  rw [familyTotalSpaceBase_preimage_eq_fundamentalCube_image F K]
  exact (hK.prod isCompact_Icc).image (familyFundamentalCubeParam_continuous F)

/-- The base projection of the varying compact tori is proper. -/
public theorem familyTotalSpaceBase_isProperMap :
    IsProperMap (familyTotalSpaceBase F) := by
  rw [isProperMap_iff_isCompact_preimage]
  exact ⟨continuous_quot_lift (familyTotalSpaceBase_respects F) continuous_fst,
    fun _ hK ↦ familyTotalSpaceBase_isCompact_preimage F hK⟩

public theorem familyTotalSpaceBase_eq_of_mem_familyFiber
    {z : UpperHalfPlane} {q : TotalSpace (parameterMap F)}
    (hq : q ∈ familyFiber F z) : familyTotalSpaceBase F q = z := by
  obtain ⟨v, rfl⟩ := hq
  exact familyTotalSpaceBase_projection F (z, v)

section FinitePointwiseCovers

variable [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]

/-- Finitely many order-three pointwise quotient charts cover the entire central torus fibre. -/
public theorem exists_finite_orderThree_local_chart_cover :
    ∀ hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
        (projection (parameterMap F)),
      ∃ s : Finset ComplexTwoSpace, familyFiber F U.zOne ⊆
        ⋃ v ∈ s, (orderThreeFamilyLocalDiffeomorph F hprojection v).source := by
  intro hprojection
  apply (familyFiber_isCompact F U.zOne).elim_finite_subcover
    (fun v ↦ (orderThreeFamilyLocalDiffeomorph F hprojection v).source)
  · exact fun v ↦ orderThreeFamilyLocalDiffeomorph_open_source F hprojection v
  · rintro q ⟨v, rfl⟩
    exact Set.mem_iUnion.mpr ⟨v,
      orderThreeFamilyLocalDiffeomorph_center_mem_source F hprojection v⟩

/-- Finitely many order-four pointwise quotient charts cover the entire central torus fibre. -/
public theorem exists_finite_orderFour_local_chart_cover :
    ∀ hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
        (projection (parameterMap F)),
      ∃ s : Finset ComplexTwoSpace, familyFiber F U.zTwo ⊆
        ⋃ v ∈ s, (orderFourFamilyLocalDiffeomorph F hprojection v).source := by
  intro hprojection
  apply (familyFiber_isCompact F U.zTwo).elim_finite_subcover
    (fun v ↦ (orderFourFamilyLocalDiffeomorph F hprojection v).source)
  · exact fun v ↦ orderFourFamilyLocalDiffeomorph_open_source F hprojection v
  · rintro q ⟨v, rfl⟩
    exact Set.mem_iUnion.mpr ⟨v,
      orderFourFamilyLocalDiffeomorph_center_mem_source F hprojection v⟩

end FinitePointwiseCovers

/-- A varying period translation disappears in the fixed torus exactly when that period vector
belongs to the fixed lattice.  This is the coefficient-level chart-agreement condition. -/
public theorem fixedTorus_translation_eq_iff
    (z₀ z : UpperHalfPlane) (n : IntegerPeriods) (v : ComplexTwoSpace) :
    (Quotient.mk _ (periodVector (parameterMap F z).1 n + v) :
      AdditiveTorus (parameterMap F z₀).1) = Quotient.mk _ v ↔
      ∃ m : IntegerPeriods,
        periodVector (parameterMap F z₀).1 m = periodVector (parameterMap F z).1 n := by
  rw [quotient_eq_iff_exists_period]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, add_right_cancel hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, congrArg (fun w ↦ w + v) hm⟩

/-- On the central fibre every family-period translation is killed by the fixed-torus
projection. -/
public theorem fixedTorus_translation_eq_at_center
    (z₀ : UpperHalfPlane) (n : IntegerPeriods) (v : ComplexTwoSpace) :
    (Quotient.mk _ (periodVector (parameterMap F z₀).1 n + v) :
      AdditiveTorus (parameterMap F z₀).1) = Quotient.mk _ v := by
  rw [fixedTorus_translation_eq_iff F z₀ z₀ n v]
  exact ⟨n, rfl⟩

section LocalInverseTransitions

variable [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]

/-- Two local inverses of the family quotient that are both defined at a point differ near that
point by one constant family-period translation. -/
public theorem familyLocalInverses_differ_by_period
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (z₀ : UpperHalfPlane)
    (v w : ComplexTwoSpace) (q : TotalSpace (parameterMap F))
    (hqv : q ∈ (hprojection (z₀, v)).localInverse.source)
    (hqw : q ∈ (hprojection (z₀, w)).localInverse.source) :
    ∃ g : FamilyPeriodGroup (parameterMap F),
      (hprojection (z₀, v)).localInverse q =
          g • (hprojection (z₀, w)).localInverse q ∧
        (hprojection (z₀, v)).localInverse =ᶠ[nhds q]
          fun y ↦ g • (hprojection (z₀, w)).localInverse y := by
  let _ : IsCancelSMul (FamilyPeriodGroup (parameterMap F))
      (UpperHalfPlane × ComplexTwoSpace) :=
    familyIsCancelSMul (parameterMap F)
  let _ : ContinuousConstSMul (FamilyPeriodGroup (parameterMap F))
      (UpperHalfPlane × ComplexTwoSpace) :=
    familyContinuousConstSMul (parameterMap F)
      (fun a ↦ (periodSection_contMDiff F a ω).continuous)
  let _ : ProperlyDiscontinuousSMul (FamilyPeriodGroup (parameterMap F))
      (UpperHalfPlane × ComplexTwoSpace) :=
    familyProperlyDiscontinuousSMul (parameterMap F)
      (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap F)
        (parameterMap_compactUniformLowerBound F))
  let l₁ := (hprojection (z₀, v)).localInverse
  let l₂ := (hprojection (z₀, w)).localInverse
  have hproj₁ : projection (parameterMap F) (l₁ q) = q :=
    (hprojection (z₀, v)).localInverse_right_inv hqv
  have hproj₂ : projection (parameterMap F) (l₂ q) = q :=
    (hprojection (z₀, w)).localInverse_right_inv hqw
  have heq :
      quotientProjection (M := UpperHalfPlane × ComplexTwoSpace)
          (G := FamilyPeriodGroup (parameterMap F)) (l₁ q) =
        quotientProjection (M := UpperHalfPlane × ComplexTwoSpace)
          (G := FamilyPeriodGroup (parameterMap F)) (l₂ q) := by
    rw [← projection.eq_def]
    exact hproj₁.trans hproj₂.symm
  let hp : IsQuotientCoveringMap
      (quotientProjection : (UpperHalfPlane × ComplexTwoSpace) →
        TotalSpace (parameterMap F)) (FamilyPeriodGroup (parameterMap F)) :=
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (hp.apply_eq_iff_mem_orbit.mp heq)
  refine ⟨g, hg.symm, eventuallyEq_const_smul_of_tendsto g ?_ ?_ hg.symm ?_⟩
  · exact ((hprojection (z₀, w)).localInverse.contMDiffOn_toFun.contMDiffAt
      ((hprojection (z₀, w)).localInverse.open_source.mem_nhds hqw)).continuousAt
  · exact ((hprojection (z₀, v)).localInverse.contMDiffOn_toFun.contMDiffAt
      ((hprojection (z₀, v)).localInverse.open_source.mem_nhds hqv)).continuousAt
  · have hlocal := (Filter.eventuallyEq_of_mem
        ((hprojection (z₀, w)).localInverse.open_source.mem_nhds hqw)
        (hprojection (z₀, w)).localInverse_eqOn_right).trans
        (Filter.eventuallyEq_of_mem
          ((hprojection (z₀, v)).localInverse.open_source.mem_nhds hqv)
          (hprojection (z₀, v)).localInverse_eqOn_right).symm
    simpa only [projection.eq_def] using hlocal

/-- A local inverse of the family quotient has the base coordinate descended from its source
point. -/
public theorem familyLocalInverse_fst
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (p : UpperHalfPlane × ComplexTwoSpace)
    (q : TotalSpace (parameterMap F))
    (hq : q ∈ (hprojection p).localInverse.source) :
    ((hprojection p).localInverse q).1 = familyTotalSpaceBase F q := by
  calc
    ((hprojection p).localInverse q).1 =
        familyTotalSpaceBase F
          (projection (parameterMap F) ((hprojection p).localInverse q)) :=
      (familyTotalSpaceBase_projection F ((hprojection p).localInverse q)).symm
    _ = familyTotalSpaceBase F q :=
      congrArg (familyTotalSpaceBase F) ((hprojection p).localInverse_right_inv hq)

omit [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))] in
/-- The fixed-torus projections of two points related by a family deck translation agree exactly
when the varying translation vector belongs to the fixed lattice. -/
public theorem fixedTorus_projection_family_smul_eq_iff
    (z₀ : UpperHalfPlane) (g : FamilyPeriodGroup (parameterMap F))
    (p : UpperHalfPlane × ComplexTwoSpace) :
    (Quotient.mk _ (g • p).2 : AdditiveTorus (parameterMap F z₀).1) =
        Quotient.mk _ p.2 ↔
      ∃ m : IntegerPeriods,
        periodVector (parameterMap F z₀).1 m =
          periodVector (parameterMap F p.1).1 g.coeff := by
  rw [family_smul_snd]
  exact fixedTorus_translation_eq_iff F z₀ p.1 g.coeff p.2

/-- Equality of two order-three pointwise product maps is exactly the fixed-lattice condition for
the deck coefficient relating their local lifts. -/
public theorem orderThree_pointwise_transition_eq_iff
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (v w : ComplexTwoSpace)
    (q : TotalSpace (parameterMap F))
    (g : FamilyPeriodGroup (parameterMap F))
    (hlift : orderThreeLocalLift F hprojection v q =
      g • orderThreeLocalLift F hprojection w q) :
    orderThreePointwiseProductMap F hprojection v q =
        orderThreePointwiseProductMap F hprojection w q ↔
      ∃ m : IntegerPeriods,
        periodVector (parameterMap F U.zOne).1 m =
          periodVector
            (parameterMap F (orderThreeLocalLift F hprojection w q).1).1 g.coeff := by
  rw [orderThreePointwiseProductMap.eq_def, orderThreePointwiseProductMap.eq_def, hlift]
  constructor
  · intro h
    have hsnd := congrArg Prod.snd h
    change (Quotient.mk _ (g • orderThreeLocalLift F hprojection w q).2 :
      AdditiveTorus (parameterMap F U.zOne).1) =
        Quotient.mk _ (orderThreeLocalLift F hprojection w q).2 at hsnd
    exact (fixedTorus_projection_family_smul_eq_iff F U.zOne g
      (orderThreeLocalLift F hprojection w q)).mp hsnd
  · intro h
    apply Prod.ext
    · change orderThreeCayleyDiffeomorph ω
        (g • orderThreeLocalLift F hprojection w q).1 =
          orderThreeCayleyDiffeomorph ω (orderThreeLocalLift F hprojection w q).1
      rw [family_smul_fst]
    · change (Quotient.mk _ (g • orderThreeLocalLift F hprojection w q).2 :
        AdditiveTorus (parameterMap F U.zOne).1) =
          Quotient.mk _ (orderThreeLocalLift F hprojection w q).2
      exact (fixedTorus_projection_family_smul_eq_iff F U.zOne g
        (orderThreeLocalLift F hprojection w q)).mpr h

/-- The analogous coefficient-level transition criterion at the order-four fibre. -/
public theorem orderFour_pointwise_transition_eq_iff
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (v w : ComplexTwoSpace)
    (q : TotalSpace (parameterMap F))
    (g : FamilyPeriodGroup (parameterMap F))
    (hlift : orderFourLocalLift F hprojection v q =
      g • orderFourLocalLift F hprojection w q) :
    orderFourPointwiseProductMap F hprojection v q =
        orderFourPointwiseProductMap F hprojection w q ↔
      ∃ m : IntegerPeriods,
        periodVector (parameterMap F U.zTwo).1 m =
          periodVector
            (parameterMap F (orderFourLocalLift F hprojection w q).1).1 g.coeff := by
  rw [orderFourPointwiseProductMap.eq_def, orderFourPointwiseProductMap.eq_def, hlift]
  constructor
  · intro h
    have hsnd := congrArg Prod.snd h
    change (Quotient.mk _ (g • orderFourLocalLift F hprojection w q).2 :
      AdditiveTorus (parameterMap F U.zTwo).1) =
        Quotient.mk _ (orderFourLocalLift F hprojection w q).2 at hsnd
    exact (fixedTorus_projection_family_smul_eq_iff F U.zTwo g
      (orderFourLocalLift F hprojection w q)).mp hsnd
  · intro h
    apply Prod.ext
    · change orderFourCayleyDiffeomorph ω
        (g • orderFourLocalLift F hprojection w q).1 =
          orderFourCayleyDiffeomorph ω (orderFourLocalLift F hprojection w q).1
      rw [family_smul_fst]
    · change (Quotient.mk _ (g • orderFourLocalLift F hprojection w q).2 :
        AdditiveTorus (parameterMap F U.zTwo).1) =
          Quotient.mk _ (orderFourLocalLift F hprojection w q).2
      exact (fixedTorus_projection_family_smul_eq_iff F U.zTwo g
        (orderFourLocalLift F hprojection w q)).mpr h

/-- The pointwise order-three charts already agree at every point of the central fibre where both
are defined; the residual issue is agreement on an open neighbourhood. -/
public theorem orderThree_pointwise_maps_agree_on_central_fiber
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (v w : ComplexTwoSpace)
    (q : TotalSpace (parameterMap F)) (hq : q ∈ familyFiber F U.zOne)
    (hqv : q ∈ (orderThreeFamilyLocalDiffeomorph F hprojection v).source)
    (hqw : q ∈ (orderThreeFamilyLocalDiffeomorph F hprojection w).source) :
    orderThreePointwiseProductMap F hprojection v q =
      orderThreePointwiseProductMap F hprojection w q := by
  obtain ⟨g, hgq, _hg⟩ :=
    familyLocalInverses_differ_by_period F hprojection U.zOne v w q hqv hqw
  have hlift : orderThreeLocalLift F hprojection v q =
      g • orderThreeLocalLift F hprojection w q := by
    exact hgq
  apply (orderThree_pointwise_transition_eq_iff F hprojection v w q g hlift).mpr
  refine ⟨g.coeff, ?_⟩
  rw [show (orderThreeLocalLift F hprojection w q).1 = U.zOne by
    exact (familyLocalInverse_fst F hprojection (U.zOne, w) q hqw).trans
      (familyTotalSpaceBase_eq_of_mem_familyFiber F hq)]

/-- The analogous central-fibre agreement for the order-four pointwise charts. -/
public theorem orderFour_pointwise_maps_agree_on_central_fiber
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (v w : ComplexTwoSpace)
    (q : TotalSpace (parameterMap F)) (hq : q ∈ familyFiber F U.zTwo)
    (hqv : q ∈ (orderFourFamilyLocalDiffeomorph F hprojection v).source)
    (hqw : q ∈ (orderFourFamilyLocalDiffeomorph F hprojection w).source) :
    orderFourPointwiseProductMap F hprojection v q =
      orderFourPointwiseProductMap F hprojection w q := by
  obtain ⟨g, hgq, _hg⟩ :=
    familyLocalInverses_differ_by_period F hprojection U.zTwo v w q hqv hqw
  have hlift : orderFourLocalLift F hprojection v q =
      g • orderFourLocalLift F hprojection w q := by
    exact hgq
  apply (orderFour_pointwise_transition_eq_iff F hprojection v w q g hlift).mpr
  refine ⟨g.coeff, ?_⟩
  rw [show (orderFourLocalLift F hprojection w q).1 = U.zTwo by
    exact (familyLocalInverse_fst F hprojection (U.zTwo, w) q hqw).trans
      (familyTotalSpaceBase_eq_of_mem_familyFiber F hq)]

/-- Under a constant local sheet transition, overlap agreement of the order-three pointwise maps
is equivalent to local membership of its varying period vector in the fixed central lattice. -/
public theorem orderThree_pointwise_eventuallyEq_iff_lattice
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (v w : ComplexTwoSpace)
    (q : TotalSpace (parameterMap F))
    (g : FamilyPeriodGroup (parameterMap F))
    (htransition : orderThreeLocalLift F hprojection v =ᶠ[nhds q]
      fun y ↦ g • orderThreeLocalLift F hprojection w y) :
    orderThreePointwiseProductMap F hprojection v =ᶠ[nhds q]
        orderThreePointwiseProductMap F hprojection w ↔
      ∀ᶠ y in nhds q, ∃ m : IntegerPeriods,
        periodVector (parameterMap F U.zOne).1 m =
          periodVector
            (parameterMap F (orderThreeLocalLift F hprojection w y).1).1 g.coeff := by
  constructor
  · intro hmaps
    filter_upwards [htransition, hmaps] with y htrans hmap
    exact (orderThree_pointwise_transition_eq_iff F hprojection v w y g htrans).mp hmap
  · intro hlattice
    filter_upwards [htransition, hlattice] with y htrans hy
    exact (orderThree_pointwise_transition_eq_iff F hprojection v w y g htrans).mpr hy

/-- The order-four overlap has the same exact fixed-lattice criterion. -/
public theorem orderFour_pointwise_eventuallyEq_iff_lattice
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (v w : ComplexTwoSpace)
    (q : TotalSpace (parameterMap F))
    (g : FamilyPeriodGroup (parameterMap F))
    (htransition : orderFourLocalLift F hprojection v =ᶠ[nhds q]
      fun y ↦ g • orderFourLocalLift F hprojection w y) :
    orderFourPointwiseProductMap F hprojection v =ᶠ[nhds q]
        orderFourPointwiseProductMap F hprojection w ↔
      ∀ᶠ y in nhds q, ∃ m : IntegerPeriods,
        periodVector (parameterMap F U.zTwo).1 m =
          periodVector
            (parameterMap F (orderFourLocalLift F hprojection w y).1).1 g.coeff := by
  constructor
  · intro hmaps
    filter_upwards [htransition, hmaps] with y htrans hmap
    exact (orderFour_pointwise_transition_eq_iff F hprojection v w y g htrans).mp hmap
  · intro hlattice
    filter_upwards [htransition, hlattice] with y htrans hy
    exact (orderFour_pointwise_transition_eq_iff F hprojection v w y g htrans).mpr hy

/-- At every overlap of order-three local inverse charts, a constant transition coefficient exists,
and fixed-torus chart agreement is precisely its local lattice-preservation condition. -/
public theorem orderThree_overlap_agreement_exact_obstruction
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (v w : ComplexTwoSpace)
    (q : TotalSpace (parameterMap F))
    (hqv : q ∈ (orderThreeFamilyLocalDiffeomorph F hprojection v).source)
    (hqw : q ∈ (orderThreeFamilyLocalDiffeomorph F hprojection w).source) :
    ∃ g : FamilyPeriodGroup (parameterMap F),
      (orderThreePointwiseProductMap F hprojection v =ᶠ[nhds q]
          orderThreePointwiseProductMap F hprojection w ↔
        ∀ᶠ y in nhds q, ∃ m : IntegerPeriods,
          periodVector (parameterMap F U.zOne).1 m =
            periodVector
              (parameterMap F (orderThreeLocalLift F hprojection w y).1).1 g.coeff) := by
  obtain ⟨g, _hgq, hg⟩ :=
    familyLocalInverses_differ_by_period F hprojection U.zOne v w q hqv hqw
  exact ⟨g, orderThree_pointwise_eventuallyEq_iff_lattice F hprojection v w q g hg⟩

/-- The exact analogous obstruction on order-four chart overlaps. -/
public theorem orderFour_overlap_agreement_exact_obstruction
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (v w : ComplexTwoSpace)
    (q : TotalSpace (parameterMap F))
    (hqv : q ∈ (orderFourFamilyLocalDiffeomorph F hprojection v).source)
    (hqw : q ∈ (orderFourFamilyLocalDiffeomorph F hprojection w).source) :
    ∃ g : FamilyPeriodGroup (parameterMap F),
      (orderFourPointwiseProductMap F hprojection v =ᶠ[nhds q]
          orderFourPointwiseProductMap F hprojection w ↔
        ∀ᶠ y in nhds q, ∃ m : IntegerPeriods,
          periodVector (parameterMap F U.zTwo).1 m =
            periodVector
              (parameterMap F (orderFourLocalLift F hprojection w y).1).1 g.coeff) := by
  obtain ⟨g, _hgq, hg⟩ :=
    familyLocalInverses_differ_by_period F hprojection U.zTwo v w q hqv hqw
  exact ⟨g, orderFour_pointwise_eventuallyEq_iff_lattice F hprojection v w q g hg⟩

end LocalInverseTransitions

end

end SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
