module

public import SphereSixComplex.Geometry.PaperCentralFamilyTopology
public import SphereSixComplex.Geometry.QuotientDeckFundamentalGroup
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# Fundamental-group generators from a fixed fibre of the global torus family

At a regular base point, the rank-four period lattice quotient is an honest complex torus.  Its
universal cover is `ℂ²`, so covering-space monodromy identifies its fundamental group with the
period lattice.  This file maps that fibre into the punctured global family and retains the
resulting lattice homomorphism explicitly.  It is the translation-generator part of the paper's
van Kampen presentation, before elliptic meridians and filling relations are imposed.
-/

@[expose] public section

noncomputable section

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.ComplexTorus SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.AnalyticTorusFamily

namespace SphereSixComplex.Geometry.GlobalTorusFamily

variable {U : TriangleUniformization} (F : PeriodFunctions U)

/-- The outer quotient map from the regular torus family to the punctured global family. -/
public def regularFamilyQuotientMap :
    C(RegularTotalSpace F, PuncturedGlobalFamily F) := by
  let _ := regularFamilyDeckAction F
  exact ⟨quotientProjection, continuous_quot_mk⟩

/-- The outer triangle-group quotient is an honest quotient covering on the regular family. -/
public theorem regularFamilyQuotientMap_isQuotientCoveringMap
    (hsource : U.sourceAction = fuchsianSourceAction)
    (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    letI := regularFamilyDeckAction F
    IsQuotientCoveringMap (regularFamilyQuotientMap F) Delta := by
  let _ := regularBaseChartedSpace hproper
  let _ : LocallyCompactSpace (RegularBase (U := U)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder
      (RegularBase (U := U)) := regularBase_isManifold hproper
  let _ := familyIsCancelSMul (regularParameterMap F)
  let _ := familyContinuousConstSMul (regularParameterMap F)
    (fun a ↦ (regularPeriodSection_contMDiff F hproper a
      RegularSmoothnessOrder).continuous)
  let _ := familyProperlyDiscontinuousSMul (regularParameterMap F)
    (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap F)
      (regularParameterMap_compactUniformLowerBound F))
  have htotal := regularTotalSpace_isManifold_and_projection_isLocalDiffeomorph
    F hproper RegularSmoothnessOrder
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (RegularTotalSpace F) := htotal.1
  let _ : LocallyCompactSpace (RegularTotalSpace F) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ := regularFamilyDeckAction F
  let _ : IsCancelSMul Delta (RegularTotalSpace F) :=
    regularFamilyDeckAction_isCancelSMul_of_fuchsian F hsource hproper
  let _ : ProperlyDiscontinuousSMul Delta (RegularTotalSpace F) :=
    regularFamilyDeckAction_properlyDiscontinuous_of_source F hproper
  let _ : ContinuousConstSMul Delta (RegularTotalSpace F) :=
    regularFamilyDeckAction_continuousConstSMul F hproper
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

/-- A chosen path from a point of the regular torus family to its translate by a triangle-group
element.  Its endpoints retain the deck transformation which the projected loop represents. -/
public def regularDeckPath (x : RegularTotalSpace F) (g : Delta) :
    Path x (regularFamilyDeckMap F g x) := by
  let _ : PathConnectedSpace (RegularTotalSpace F) := regularTotalSpace_pathConnected F
  exact PathConnectedSpace.somePath _ _

/-- Deck translates have the same image in the outer triangle-group quotient. -/
public theorem regularFamilyQuotientMap_deck
    (x : RegularTotalSpace F) (g : Delta) :
    regularFamilyQuotientMap F (regularFamilyDeckMap F g x) =
      regularFamilyQuotientMap F x := by
  let _ := regularFamilyDeckAction F
  apply Quotient.sound
  change MulAction.orbitRel Delta (RegularTotalSpace F)
    (regularFamilyDeckMap F g x) x
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨g, rfl⟩

/-- Projecting a path to its deck translate gives a based loop in the punctured global family. -/
public def regularDeckLoop (x : RegularTotalSpace F) (g : Delta) :
    Path (regularFamilyQuotientMap F x) (regularFamilyQuotientMap F x) :=
  ((regularDeckPath F x g).map (regularFamilyQuotientMap F).continuous).cast rfl
    (regularFamilyQuotientMap_deck F x g).symm

/-- The fundamental-group element represented by the projected deck path. -/
public def regularDeckMeridian (x : RegularTotalSpace F) (g : Delta) :
    FundamentalGroup (PuncturedGlobalFamily F) (regularFamilyQuotientMap F x) :=
  Path.Homotopic.Quotient.mk (regularDeckLoop F x g)

/-- The complex torus over one point of the regular source base. -/
public abbrev FiberTorus (b : RegularBase (U := U)) :=
  Torus (regularParameterMap F b).1

/-- Include a fixed torus fibre into the varying torus family before the triangle-group
quotient. -/
public def fiberTorusToRegularTotalSpace (b : RegularBase (U := U)) :
    FiberTorus F b → RegularTotalSpace F :=
  Quotient.lift (fun z : ComplexTwoSpace => Quotient.mk _ (b, z)) (by
    intro z w hzw
    apply Quotient.sound
    change MulAction.orbitRel (PeriodGroup (regularParameterMap F b).1)
      ComplexTwoSpace z w at hzw
    change MulAction.orbitRel (FamilyPeriodGroup (regularParameterMap F))
      (RegularBase (U := U) × ComplexTwoSpace) (b, z) (b, w)
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hzw ⊢
    obtain ⟨g, hg⟩ := hzw
    obtain ⟨a, ha⟩ := g.toAdd.property
    let q : FamilyPeriodGroup (regularParameterMap F) := Multiplicative.ofAdd a
    refine ⟨q, ?_⟩
    apply Prod.ext
    · rfl
    · change periodVector (regularParameterMap F b).1 a + w = z
      change (g.toAdd : ComplexTwoSpace) + w = z at hg
      change periodVector (regularParameterMap F b).1 a =
        (g.toAdd : ComplexTwoSpace) at ha
      rw [ha]
      exact hg)

@[simp]
public theorem fiberTorusToRegularTotalSpace_mk
    (b : RegularBase (U := U)) (z : ComplexTwoSpace) :
    fiberTorusToRegularTotalSpace F b (Quotient.mk _ z) = Quotient.mk _ (b, z) :=
  rfl

/-- The fixed-fibre inclusion is continuous for the two quotient topologies. -/
public theorem fiberTorusToRegularTotalSpace_continuous (b : RegularBase (U := U)) :
    Continuous (fiberTorusToRegularTotalSpace F b) := by
  apply continuous_quot_lift
  exact continuous_quot_mk.comp (continuous_const.prodMk continuous_id)

/-- The fixed-fibre inclusion as a continuous map. -/
public def fiberTorusToRegularTotalSpaceContinuousMap
    (b : RegularBase (U := U)) : C(FiberTorus F b, RegularTotalSpace F) :=
  ⟨fiberTorusToRegularTotalSpace F b, fiberTorusToRegularTotalSpace_continuous F b⟩

/-- Include a fixed torus fibre into the punctured global family, including the outer
triangle-group quotient. -/
public def fiberTorusToPuncturedGlobalFamily
    (b : RegularBase (U := U)) : C(FiberTorus F b, PuncturedGlobalFamily F) := by
  let _ := regularFamilyDeckAction F
  exact
    ⟨fun q => quotientProjection (M := RegularTotalSpace F) (G := Delta)
        (fiberTorusToRegularTotalSpace F b q),
      continuous_quot_mk.comp (fiberTorusToRegularTotalSpace_continuous F b)⟩

@[simp]
public theorem fiberTorusToPuncturedGlobalFamily_mk
    (b : RegularBase (U := U)) (z : ComplexTwoSpace) :
    fiberTorusToPuncturedGlobalFamily F b (Quotient.mk _ z) =
      Quotient.mk _ (Quotient.mk _ (b, z)) :=
  rfl

/-- Full rank identifies integral coefficients with the actual period lattice in the selected
fibre. -/
public def fiberPeriodLatticeEquiv (b : RegularBase (U := U)) :
    IntegerPeriods ≃+ periodLattice (regularParameterMap F b).1 :=
  AddMonoidHom.ofInjective
    (periodHom_injective (FullRank.ofSetupInequalities _ (regularParameterMap F b).2))

/-- Covering monodromy identifies the fundamental group of the selected torus fibre with its
rank-four integral period lattice.  The opposite group from monodromy is removed using
commutativity of the lattice. -/
public def fiberTorusFundamentalGroupEquiv
    (b : RegularBase (U := U)) (z : ComplexTwoSpace) :
    IntegerPeriods ≃+ Additive
      (FundamentalGroup (FiberTorus F b)
        (torusProjection (regularParameterMap F b).1 z)) := by
  let _ : ProperlyDiscontinuousSMul
      (PeriodGroup (regularParameterMap F b).1) ComplexTwoSpace :=
    periodLattice_properlyDiscontinuousSMul
      (FullRank.ofSetupInequalities _ (regularParameterMap F b).2)
  let hp : IsQuotientCoveringMap
      (torusProjection (regularParameterMap F b).1)
      (PeriodGroup (regularParameterMap F b).1) :=
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
  let e : (torusProjection (regularParameterMap F b).1) ⁻¹'
      {torusProjection (regularParameterMap F b).1 z} := ⟨z, rfl⟩
  let E : Multiplicative IntegerPeriods ≃*
      FundamentalGroup (FiberTorus F b)
        (torusProjection (regularParameterMap F b).1 z) :=
    (fiberPeriodLatticeEquiv F b).toMultiplicative.trans
      (MulOpposite.opMulEquiv.trans (hp.fundamentalGroupEquiv e).symm)
  exact (AddEquiv.refl IntegerPeriods).trans E.toAdditive

/-- The actual period-lattice deck transformation associated to integral coefficients. -/
public def fiberPeriodGroupElement
    (b : RegularBase (U := U)) (a : IntegerPeriods) :
    PeriodGroup (regularParameterMap F b).1 :=
  Multiplicative.ofAdd ((fiberPeriodLatticeEquiv F b) a)

@[simp]
public theorem fiberPeriodGroupElement_smul
    (b : RegularBase (U := U)) (a : IntegerPeriods) (z : ComplexTwoSpace) :
    fiberPeriodGroupElement F b a • z =
      periodVector (regularParameterMap F b).1 a + z :=
  rfl

/-- The straight path in `ℂ²` from a chosen lift to its translate by an integral period. -/
public noncomputable def fiberPeriodLiftPath
    (b : RegularBase (U := U)) (z : ComplexTwoSpace) (a : IntegerPeriods) :
    Path z (fiberPeriodGroupElement F b a • z) :=
  Path.segment z (fiberPeriodGroupElement F b a • z)

/-- A labelled period translate has the same image in its fixed torus fibre. -/
public theorem fiberPeriodLoop_endpoint
    (b : RegularBase (U := U)) (z : ComplexTwoSpace) (a : IntegerPeriods) :
    torusProjection (regularParameterMap F b).1
      (fiberPeriodGroupElement F b a • z) =
      torusProjection (regularParameterMap F b).1 z := by
  apply Quotient.sound
  change MulAction.orbitRel (PeriodGroup (regularParameterMap F b).1) ComplexTwoSpace
    (fiberPeriodGroupElement F b a • z) z
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨fiberPeriodGroupElement F b a, rfl⟩

/-- Projecting the straight period segment gives a loop in the selected fixed torus fibre. -/
public noncomputable def fiberPeriodLoop
    (b : RegularBase (U := U)) (z : ComplexTwoSpace) (a : IntegerPeriods) :
    Path (torusProjection (regularParameterMap F b).1 z)
      (torusProjection (regularParameterMap F b).1 z) :=
  ((fiberPeriodLiftPath F b z a).map
      (show Continuous (torusProjection (regularParameterMap F b).1) from
        continuous_quot_mk)).cast rfl
    (fiberPeriodLoop_endpoint F b z a).symm

@[simp]
public theorem fiberPeriodLoop_apply
    (b : RegularBase (U := U)) (z : ComplexTwoSpace) (a : IntegerPeriods)
    (t : unitInterval) :
    fiberPeriodLoop F b z a t =
      torusProjection (regularParameterMap F b).1 (fiberPeriodLiftPath F b z a t) := by
  unfold fiberPeriodLoop
  rw [Path.cast_coe]
  rfl

/-- The fundamental-group class of the projected straight period segment. -/
public noncomputable def fiberPeriodClass
    (b : RegularBase (U := U)) (z : ComplexTwoSpace) (a : IntegerPeriods) :
    Additive (FundamentalGroup (FiberTorus F b)
      (torusProjection (regularParameterMap F b).1 z)) :=
  Additive.ofMul (Path.Homotopic.Quotient.mk (fiberPeriodLoop F b z a))

/-! ## Straightening paths in the labelled vector-bundle cover -/

/-- Reparameterize a path so that it is completed on the first half of the interval and is
constant on the second half. -/
public def frontLoadedParameter (t : unitInterval) : unitInterval :=
  ⟨min (2 * (t : ℝ)) 1, by
    constructor
    · exact le_min (mul_nonneg (by norm_num) t.2.1) zero_le_one
    · exact min_le_right _ _⟩

public theorem frontLoadedParameter_continuous : Continuous frontLoadedParameter := by
  apply Continuous.subtype_mk
  fun_prop

@[simp]
public theorem frontLoadedParameter_zero : frontLoadedParameter 0 = 0 := by
  apply Subtype.ext
  norm_num [frontLoadedParameter]

@[simp]
public theorem frontLoadedParameter_one : frontLoadedParameter 1 = 1 := by
  apply Subtype.ext
  norm_num [frontLoadedParameter]

/-- The front-loaded reparameterization of a path in the labelled vector-bundle cover. -/
public def frontLoadedRegularCoverPath
    {p q : RegularBase (U := U) × ComplexTwoSpace} (P : Path p q) : Path p q :=
  P.reparam frontLoadedParameter frontLoadedParameter_continuous
    frontLoadedParameter_zero frontLoadedParameter_one

/-- Retain only the base component of a path, along the zero section. -/
public def regularCoverBaseZeroPath
    {b c : RegularBase (U := U)} {z : ComplexTwoSpace}
    (P : Path (b, (0 : ComplexTwoSpace)) (c, z)) :
    Path (b, (0 : ComplexTwoSpace)) (c, (0 : ComplexTwoSpace)) :=
  (P.map continuous_fst).map (continuous_id.prodMk continuous_const)

/-- The straight vertical segment to the endpoint of a path in the vector-bundle cover. -/
public def regularCoverEndpointVerticalPath
    {b c : RegularBase (U := U)} {z : ComplexTwoSpace}
    (_P : Path (b, (0 : ComplexTwoSpace)) (c, z)) :
    Path (c, (0 : ComplexTwoSpace)) (c, z) :=
  (Path.segment (0 : ComplexTwoSpace) z).map
    (continuous_const.prodMk continuous_id)

/-- The path obtained by first following the base along the zero section and then moving
vertically in the endpoint fibre. -/
public def regularCoverStraightenedPath
    {b c : RegularBase (U := U)} {z : ComplexTwoSpace}
    (P : Path (b, (0 : ComplexTwoSpace)) (c, z)) :
    Path (b, (0 : ComplexTwoSpace)) (c, z) :=
  (regularCoverBaseZeroPath P).trans (regularCoverEndpointVerticalPath P)

public theorem regularCoverStraightenedPath_fst
    {b c : RegularBase (U := U)} {z : ComplexTwoSpace}
    (P : Path (b, (0 : ComplexTwoSpace)) (c, z)) (t : unitInterval) :
    (regularCoverStraightenedPath P t).1 =
      (frontLoadedRegularCoverPath P t).1 := by
  rw [regularCoverStraightenedPath, Path.trans_apply]
  split_ifs with ht
  · change (P ⟨2 * (t : ℝ), by
        constructor <;> nlinarith [t.2.1, t.2.2]⟩).1 =
      (P (frontLoadedParameter t)).1
    congr 2
    apply Subtype.ext
    simp only [frontLoadedParameter]
    rw [min_eq_left]
    nlinarith
  · change c = (P (frontLoadedParameter t)).1
    have hparam : frontLoadedParameter t = 1 := by
      apply Subtype.ext
      change min (2 * (t : ℝ)) 1 = 1
      rw [min_eq_right]
      nlinarith
    rw [hparam]
    exact congrArg Prod.fst P.target.symm

/-- Any path in the labelled vector-bundle cover that starts on the zero section is homotopic
relative endpoints to its base path on the zero section followed by one vertical segment. -/
public def regularCoverPathHomotopyStraightened
    {b c : RegularBase (U := U)} {z : ComplexTwoSpace}
    (P : Path (b, (0 : ComplexTwoSpace)) (c, z)) :
    Path.Homotopy (frontLoadedRegularCoverPath P) (regularCoverStraightenedPath P) where
  toFun st :=
    ((frontLoadedRegularCoverPath P st.2).1,
      ((1 - (st.1 : ℝ) : ℝ) : ℂ) • (frontLoadedRegularCoverPath P st.2).2 +
        (((st.1 : ℝ) : ℂ) • (regularCoverStraightenedPath P st.2).2))
  continuous_toFun := by fun_prop
  map_zero_left t := by simp
  map_one_left t := by
    apply Prod.ext
    · exact (regularCoverStraightenedPath_fst P t).symm
    · simp
  prop' s t ht := by
    rcases ht with rfl | ht
    · apply Prod.ext
      · rfl
      · change (((1 - (s : ℝ) : ℝ) : ℂ) •
            (frontLoadedRegularCoverPath P 0).2 +
          ((s : ℝ) : ℂ) • (regularCoverStraightenedPath P 0).2) =
            (frontLoadedRegularCoverPath P 0).2
        rw [(frontLoadedRegularCoverPath P).source,
          (regularCoverStraightenedPath P).source]
        simp
    · rw [Set.mem_singleton_iff] at ht
      subst t
      apply Prod.ext
      · rfl
      · change (((1 - (s : ℝ) : ℝ) : ℂ) •
            (frontLoadedRegularCoverPath P 1).2 +
          ((s : ℝ) : ℂ) • (regularCoverStraightenedPath P 1).2) =
            (frontLoadedRegularCoverPath P 1).2
        rw [(frontLoadedRegularCoverPath P).target,
          (regularCoverStraightenedPath P).target]
        change (((1 - (s : ℝ) : ℝ) : ℂ) • z + ((s : ℝ) : ℂ) • z) = z
        rw [← add_smul]
        have hs : (((1 - (s : ℝ) : ℝ) : ℂ) + ((s : ℝ) : ℂ)) = 1 := by
          push_cast
          ring
        rw [hs, one_smul]

/-- Hence the original path itself is homotopic relative endpoints to the straightened path. -/
public theorem regularCoverPath_homotopic_straightened
    {b c : RegularBase (U := U)} {z : ComplexTwoSpace}
    (P : Path (b, (0 : ComplexTwoSpace)) (c, z)) :
    Path.Homotopic P (regularCoverStraightenedPath P) :=
  (show Path.Homotopic P (frontLoadedRegularCoverPath P) from
    ⟨Path.Homotopy.reparam P frontLoadedParameter frontLoadedParameter_continuous
      frontLoadedParameter_zero frontLoadedParameter_one⟩).trans
    ⟨regularCoverPathHomotopyStraightened P⟩

/-- A loop in the labelled vector-bundle cover based on its zero section contracts fibrewise to
the loop obtained by forgetting its fibre coordinate. -/
public theorem regularCoverLoop_homotopic_baseZero
    {b : RegularBase (U := U)}
    (P : Path (b, (0 : ComplexTwoSpace)) (b, (0 : ComplexTwoSpace))) :
    Path.Homotopic P (regularCoverBaseZeroPath P) := by
  refine ⟨{
    toFun := fun st ↦
      ((P st.2).1, (((1 - (st.1 : ℝ) : ℝ) : ℂ) • (P st.2).2))
    continuous_toFun := by fun_prop
    map_zero_left := by intro t; simp
    map_one_left := by intro t; apply Prod.ext <;> simp [regularCoverBaseZeroPath]
    prop' := ?_
  }⟩
  intro s t ht
  rcases ht with rfl | ht
  · change ((P 0).1, (((1 - (s : ℝ) : ℝ) : ℂ) • (P 0).2)) = P 0
    rw [P.source]
    simp
  · rw [Set.mem_singleton_iff] at ht
    subst t
    change ((P 1).1, (((1 - (s : ℝ) : ℝ) : ℂ) • (P 1).2)) = P 1
    rw [P.target]
    simp

/-- The covering-monodromy equivalence sends an integral coefficient to the concrete projected
straight segment ending at that exact period translate. -/
public theorem fiberTorusFundamentalGroupEquiv_apply_eq_fiberPeriodClass
    (b : RegularBase (U := U)) (z : ComplexTwoSpace) (a : IntegerPeriods) :
    fiberTorusFundamentalGroupEquiv F b z a = fiberPeriodClass F b z a := by
  let _ : ProperlyDiscontinuousSMul
      (PeriodGroup (regularParameterMap F b).1) ComplexTwoSpace :=
    periodLattice_properlyDiscontinuousSMul
      (FullRank.ofSetupInequalities _ (regularParameterMap F b).2)
  let hp : IsQuotientCoveringMap
      (torusProjection (regularParameterMap F b).1)
      (PeriodGroup (regularParameterMap F b).1) :=
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
  let e : (torusProjection (regularParameterMap F b).1) ⁻¹'
      {torusProjection (regularParameterMap F b).1 z} := ⟨z, rfl⟩
  apply Additive.toMul.injective
  change ((fiberPeriodLatticeEquiv F b).toMultiplicative.trans
      (MulOpposite.opMulEquiv.trans (hp.fundamentalGroupEquiv e).symm))
        (Multiplicative.ofAdd a) =
    Path.Homotopic.Quotient.mk (fiberPeriodLoop F b z a)
  apply (hp.fundamentalGroupEquiv e).injective
  simp only [MulEquiv.trans_apply]
  rw [MulEquiv.apply_symm_apply]
  change MulOpposite.op (Multiplicative.ofAdd ((fiberPeriodLatticeEquiv F b) a)) =
    (hp.fundamentalGroupToMulOpposite e)
      (Path.Homotopic.Quotient.mk (fiberPeriodLoop F b z a))
  symm
  rw [hp.fundamentalGroupToMulOpposite_apply_eq_Iff]
  have hend : torusProjection (regularParameterMap F b).1
        (fiberPeriodGroupElement F b a • z) =
      torusProjection (regularParameterMap F b).1 z := by
    apply Quotient.sound
    change MulAction.orbitRel (PeriodGroup (regularParameterMap F b).1)
      ComplexTwoSpace (fiberPeriodGroupElement F b a • z) z
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    exact ⟨fiberPeriodGroupElement F b a, rfl⟩
  let e' : (torusProjection (regularParameterMap F b).1) ⁻¹'
      {torusProjection (regularParameterMap F b).1 z} :=
    ⟨fiberPeriodGroupElement F b a • z, hend⟩
  have hm : hp.isCoveringMap.monodromy
        (Path.Homotopic.Quotient.mk (fiberPeriodLoop F b z a)) e = e' :=
    hp.isCoveringMap.monodromy_eq_of_map_eq
      (Path.Homotopic.Quotient.mk (fiberPeriodLiftPath F b z a)) (by rfl)
  exact congrArg Subtype.val hm.symm

/-- The additive lattice homomorphism represented by loops in one fixed torus fibre. -/
public def fiberTorusTranslation
    (b : RegularBase (U := U)) (z : ComplexTwoSpace) :
    IntegerPeriods →+ Additive
      (FundamentalGroup (FiberTorus F b)
        (torusProjection (regularParameterMap F b).1 z)) :=
  (fiberTorusFundamentalGroupEquiv F b z).toAddMonoidHom

/-- The abstractly defined fixed-fibre translation homomorphism is represented by the concrete
straight period loop above. -/
public theorem fiberTorusTranslation_apply_eq_fiberPeriodClass
    (b : RegularBase (U := U)) (z : ComplexTwoSpace) (a : IntegerPeriods) :
    fiberTorusTranslation F b z a = fiberPeriodClass F b z a :=
  fiberTorusFundamentalGroupEquiv_apply_eq_fiberPeriodClass F b z a

/-- Before inclusion into the filled threefold, the four fibre translations give every element
of the torus fundamental group. -/
public theorem fiberTorusTranslation_bijective
    (b : RegularBase (U := U)) (z : ComplexTwoSpace) :
    Function.Bijective (fiberTorusTranslation F b z) :=
  (fiberTorusFundamentalGroupEquiv F b z).bijective

/-! ## Transporting a labelled period loop through the regular family -/

/-- The quotient projection from the globally labelled regular vector-bundle cover. -/
public def regularFamilyCoverProjection :
    C(RegularBase (U := U) × ComplexTwoSpace, RegularTotalSpace F) :=
  ⟨quotientProjection
      (M := RegularBase (U := U) × ComplexTwoSpace)
      (G := FamilyPeriodGroup (regularParameterMap F)), continuous_quot_mk⟩

/-- The family-period deck transformation carrying a globally labelled integral coefficient. -/
public def regularFamilyPeriodGroupElement (a : IntegerPeriods) :
    FamilyPeriodGroup (regularParameterMap F) := by
  change Multiplicative IntegerPeriods
  exact Multiplicative.ofAdd a

@[simp]
public theorem regularFamilyPeriodGroupElement_coeff (a : IntegerPeriods) :
    (regularFamilyPeriodGroupElement F a).coeff = a := rfl

@[simp]
public theorem regularFamilyPeriodGroupElement_smul
    (p : RegularBase (U := U) × ComplexTwoSpace) (a : IntegerPeriods) :
    regularFamilyPeriodGroupElement F a • p =
      (p.1, periodVector (regularParameterMap F p.1).1 a + p.2) := rfl

/-- The family-period quotient projection intertwines the lifted and descended triangle-group
deck transformations. -/
public theorem regularFamilyCoverProjection_regularDeckMap
    (g : Delta) (p : RegularBase (U := U) × ComplexTwoSpace) :
    regularFamilyCoverProjection F (regularDeckMap F g p) =
      regularFamilyDeckMap F g (regularFamilyCoverProjection F p) := by
  rfl

/-- Under source properness, the regular vector-bundle cover is the quotient covering of the
regular torus family by the globally labelled period lattice. -/
public theorem regularFamilyCoverProjection_isQuotientCoveringMap
    (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    IsQuotientCoveringMap (regularFamilyCoverProjection F)
      (FamilyPeriodGroup (regularParameterMap F)) := by
  let _ : LocallyCompactSpace (RegularBase (U := U)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ := familyIsCancelSMul (regularParameterMap F)
  let _ := familyContinuousConstSMul (regularParameterMap F)
    (fun a ↦ ((periodSection_contMDiff F a 0).continuous.comp continuous_subtype_val))
  let _ := familyProperlyDiscontinuousSMul (regularParameterMap F)
    (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap F)
      (regularParameterMap_compactUniformLowerBound F))
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

/-- The underlying covering-map form of the labelled period quotient. -/
public theorem regularFamilyCoverProjection_isCoveringMap
    (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    IsCoveringMap (regularFamilyCoverProjection F) :=
  (regularFamilyCoverProjection_isQuotientCoveringMap F hproper).isCoveringMap

/-- Lift a path in the regular torus family from a prescribed representative in its vector-bundle
cover. -/
public def regularFamilyPathLift
    {x y : RegularTotalSpace F} (W : Path x y)
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (p : RegularBase (U := U) × ComplexTwoSpace)
    (hp : regularFamilyCoverProjection F p = x) :
    Path p ((regularFamilyCoverProjection_isCoveringMap F hproper).liftPath
      W p (W.source.trans hp.symm) 1) :=
  ⟨(regularFamilyCoverProjection_isCoveringMap F hproper).liftPath
      W p (W.source.trans hp.symm),
    (regularFamilyCoverProjection_isCoveringMap F hproper).liftPath_zero _ _ _, rfl⟩

/-- The chosen lift projects pointwise to the original path. -/
public theorem regularFamilyPathLift_projects
    {x y : RegularTotalSpace F} (W : Path x y)
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (p : RegularBase (U := U) × ComplexTwoSpace)
    (hp : regularFamilyCoverProjection F p = x) :
    ∀ t, regularFamilyCoverProjection F
        (regularFamilyPathLift F W hproper p hp t) = W t := by
  intro t
  exact congrFun
    ((regularFamilyCoverProjection_isCoveringMap F hproper).liftPath_lifts
      W p (W.source.trans hp.symm)) t

/-- The straight lift of a globally labelled integral period at an arbitrary point of the
regular vector-bundle cover. -/
public def regularFamilyPeriodLiftPath
    (p : RegularBase (U := U) × ComplexTwoSpace) (a : IntegerPeriods) :
    Path p (p.1, periodVector (regularParameterMap F p.1).1 a + p.2) where
  toFun t := (p.1, (t : ℝ) • periodVector (regularParameterMap F p.1).1 a + p.2)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

/-- Translation by a labelled family period is invisible after the varying-lattice quotient. -/
public theorem regularFamilyProjection_period_smul
    (p : RegularBase (U := U) × ComplexTwoSpace) (a : IntegerPeriods) :
    regularFamilyCoverProjection F
        (p.1, periodVector (regularParameterMap F p.1).1 a + p.2) =
      regularFamilyCoverProjection F p := by
  apply Quotient.sound
  change MulAction.orbitRel (FamilyPeriodGroup (regularParameterMap F)) _
    (p.1, periodVector (regularParameterMap F p.1).1 a + p.2) p
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨Multiplicative.ofAdd a, rfl⟩

/-- The straight labelled-period loop in the regular torus family. -/
public def regularFamilyPeriodLoop
    (p : RegularBase (U := U) × ComplexTwoSpace) (a : IntegerPeriods) :
    Path (regularFamilyCoverProjection F p) (regularFamilyCoverProjection F p) :=
  ((regularFamilyPeriodLiftPath F p a).map
    (regularFamilyCoverProjection F).continuous).cast rfl
    (regularFamilyProjection_period_smul F p a).symm

@[simp]
public theorem regularFamilyPeriodLoop_apply
    (p : RegularBase (U := U) × ComplexTwoSpace) (a : IntegerPeriods)
    (t : unitInterval) :
    regularFamilyPeriodLoop F p a t =
      regularFamilyCoverProjection F (regularFamilyPeriodLiftPath F p a t) := by
  unfold regularFamilyPeriodLoop
  rw [Path.cast_coe]
  rfl

/-- After the outer quotient, applying a triangle-group deck transformation to a period loop
transports its integral label by `rhoLambda`. -/
public theorem regularFamilyPeriodLoop_deck
    (g : Delta) (p : RegularBase (U := U) × ComplexTwoSpace)
    (a : IntegerPeriods) :
    (((regularFamilyPeriodLoop F (regularDeckMap F g p) (rhoLambda g a)).map
      (regularFamilyQuotientMap F).continuous).cast
        ((regularFamilyQuotientMap_deck F
          (regularFamilyCoverProjection F p) g).symm.trans
            (congrArg (regularFamilyQuotientMap F)
              (regularFamilyCoverProjection_regularDeckMap F g p).symm))
        ((regularFamilyQuotientMap_deck F
          (regularFamilyCoverProjection F p) g).symm.trans
            (congrArg (regularFamilyQuotientMap F)
              (regularFamilyCoverProjection_regularDeckMap F g p).symm))) =
      (regularFamilyPeriodLoop F p a).map
        (regularFamilyQuotientMap F).continuous := by
  apply Path.ext
  funext t
  change regularFamilyQuotientMap F
      (regularFamilyCoverProjection F
        ((regularDeckMap F g p).1,
          (t : ℝ) • periodVector
              (regularParameterMap F (regularDeckMap F g p).1).1 (rhoLambda g a) +
            (regularDeckMap F g p).2)) =
    regularFamilyQuotientMap F
      (regularFamilyCoverProjection F
        (p.1, (t : ℝ) • periodVector (regularParameterMap F p.1).1 a + p.2))
  rw [show
      ((regularDeckMap F g p).1,
          (t : ℝ) • periodVector
              (regularParameterMap F (regularDeckMap F g p).1).1 (rhoLambda g a) +
            (regularDeckMap F g p).2) =
        regularDeckMap F g
          (p.1, (t : ℝ) • periodVector (regularParameterMap F p.1).1 a + p.2) by
    apply Prod.ext
    · rfl
    · change (t : ℝ) • periodVector
            (parameterMap F (U.sourceAction g • p.1.1)).1 (rhoLambda g a) +
          periodTransport g (parameterMap F p.1.1) p.2 =
        periodTransport g (parameterMap F p.1.1)
          ((t : ℝ) • periodVector (parameterMap F p.1.1).1 a + p.2)
      have hequivariant := parameterMap_equivariant F g
      change ∀ z, parameterMap F (U.sourceAction g • z) =
        rhoParameters g (parameterMap F z) at hequivariant
      rw [map_add, map_smul, periodTransport_periodVector,
        hequivariant p.1.1]]
  rw [regularFamilyCoverProjection_regularDeckMap]
  exact regularFamilyQuotientMap_deck F _ g

/-- The projected labelled-period loop is independent of the chosen representative of its
starting point in the regular family-period cover. -/
public theorem regularFamilyPeriodLoop_eq_of_projection_eq
    (p q : RegularBase (U := U) × ComplexTwoSpace) (a : IntegerPeriods)
    (h : regularFamilyCoverProjection F p = regularFamilyCoverProjection F q) :
    (regularFamilyPeriodLoop F p a).cast h.symm h.symm =
      regularFamilyPeriodLoop F q a := by
  apply Path.ext
  funext t
  apply Quotient.sound
  have hpq : MulAction.orbitRel (FamilyPeriodGroup (regularParameterMap F)) _ p q :=
    Quotient.exact h
  change MulAction.orbitRel (FamilyPeriodGroup (regularParameterMap F)) _
    ((regularFamilyPeriodLiftPath F p a) t)
    ((regularFamilyPeriodLiftPath F q a) t)
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hpq ⊢
  obtain ⟨g, hg⟩ := hpq
  refine ⟨g, ?_⟩
  have hbase : p.1 = q.1 := by
    simpa only [family_smul_fst] using congrArg Prod.fst hg.symm
  apply Prod.ext
  · exact hbase.symm
  · have hsnd := congrArg Prod.snd hg
    simp only [family_smul_snd] at hsnd ⊢
    change periodVector (regularParameterMap F q.1).1 g.coeff +
        ((t : ℝ) • periodVector (regularParameterMap F q.1).1 a + q.2) =
      (t : ℝ) • periodVector (regularParameterMap F p.1).1 a + p.2
    rw [hbase]
    rw [← hsnd]
    abel

/-- Moving a labelled period loop along a path in the vector-bundle cover gives a free homotopy
between the endpoint loops. -/
public def regularFamilyPeriodLoopHomotopyAlong
    {p₀ p₁ : RegularBase (U := U) × ComplexTwoSpace}
    (P : Path p₀ p₁) (a : IntegerPeriods) :
    ContinuousMap.Homotopy
      (regularFamilyPeriodLoop F p₀ a).toContinuousMap
      (regularFamilyPeriodLoop F p₁ a).toContinuousMap where
  toFun st := regularFamilyCoverProjection F
    ((P st.1).1,
      (st.2 : ℝ) • periodVector (regularParameterMap F (P st.1).1).1 a + (P st.1).2)
  continuous_toFun := by
    apply (regularFamilyCoverProjection F).continuous.comp
    apply Continuous.prodMk
    · exact continuous_fst.comp (P.continuous.comp continuous_fst)
    · have hp : Continuous (fun b : RegularBase (U := U) =>
          periodVector (regularParameterMap F b).1 a) :=
        (periodSection_contMDiff F a 0).continuous.comp continuous_subtype_val
      exact ((continuous_subtype_val.comp continuous_snd).smul
        (hp.comp (continuous_fst.comp (P.continuous.comp continuous_fst)))).add
          (continuous_snd.comp (P.continuous.comp continuous_fst))
  map_zero_left t := by
    change regularFamilyCoverProjection F
        ((P 0).1, (t : ℝ) •
          periodVector (regularParameterMap F (P 0).1).1 a + (P 0).2) =
      regularFamilyCoverProjection F
        (p₀.1, (t : ℝ) • periodVector (regularParameterMap F p₀.1).1 a + p₀.2)
    rw [P.source]
  map_one_left t := by
    change regularFamilyCoverProjection F
        ((P 1).1, (t : ℝ) •
          periodVector (regularParameterMap F (P 1).1).1 a + (P 1).2) =
      regularFamilyCoverProjection F
        (p₁.1, (t : ℝ) • periodVector (regularParameterMap F p₁.1).1 a + p₁.2)
    rw [P.target]

/-- The path in the regular torus family projected from a controlled vector-bundle-cover path. -/
public def regularFamilyCoverWhisker
    {p₀ p₁ : RegularBase (U := U) × ComplexTwoSpace}
    (P : Path p₀ p₁) :
    Path (regularFamilyCoverProjection F p₀) (regularFamilyCoverProjection F p₁) :=
  P.map (regularFamilyCoverProjection F).continuous

/-- A path from a regular-family point to its `g`-translate becomes a loop after the outer
triangle-group quotient. -/
public def regularFamilyDeckPathLoop
    (g : Delta) (p : RegularBase (U := U) × ComplexTwoSpace)
    (W : Path (regularFamilyCoverProjection F p)
      (regularFamilyDeckMap F g (regularFamilyCoverProjection F p))) :
    Path
      (regularFamilyQuotientMap F (regularFamilyCoverProjection F p))
      (regularFamilyQuotientMap F (regularFamilyCoverProjection F p)) :=
  (W.map (regularFamilyQuotientMap F).continuous).cast rfl
    (regularFamilyQuotientMap_deck F (regularFamilyCoverProjection F p) g).symm

public theorem regularFamilyPeriodLoopHomotopyAlong_evalAt_zero
    {p₀ p₁ : RegularBase (U := U) × ComplexTwoSpace}
    (P : Path p₀ p₁) (a : IntegerPeriods) :
    ((regularFamilyPeriodLoopHomotopyAlong F P a).evalAt 0).cast
        (regularFamilyPeriodLoop F p₀ a).source.symm
        (regularFamilyPeriodLoop F p₁ a).source.symm =
      regularFamilyCoverWhisker F P := by
  apply Path.ext
  funext t
  change regularFamilyCoverProjection F
      ((P t).1, (0 : ℝ) • periodVector (regularParameterMap F (P t).1).1 a + (P t).2) =
    regularFamilyCoverProjection F (P t)
  simp

public theorem regularFamilyPeriodLoopHomotopyAlong_evalAt_one
    {p₀ p₁ : RegularBase (U := U) × ComplexTwoSpace}
    (P : Path p₀ p₁) (a : IntegerPeriods) :
    ((regularFamilyPeriodLoopHomotopyAlong F P a).evalAt 1).cast
        (regularFamilyPeriodLoop F p₀ a).target.symm
        (regularFamilyPeriodLoop F p₁ a).target.symm =
      regularFamilyCoverWhisker F P := by
  apply Path.ext
  funext t
  change regularFamilyCoverProjection F
      ((P t).1, (1 : ℝ) • periodVector (regularParameterMap F (P t).1).1 a + (P t).2) =
    regularFamilyCoverProjection F (P t)
  simpa using regularFamilyProjection_period_smul F (P t) a

/-- A globally labelled period loop is invariant under basepoint transport along a controlled
path in the regular vector-bundle cover. -/
public theorem regularFamilyPeriodLoop_transport
    {p₀ p₁ : RegularBase (U := U) × ComplexTwoSpace}
    (P : Path p₀ p₁) (a : IntegerPeriods) :
    pathLoopClass (regularFamilyPeriodLoop F p₀ a) =
      whiskeredLoopClass (regularFamilyCoverWhisker F P)
        (regularFamilyPeriodLoop F p₁ a) := by
  let L₀ := regularFamilyPeriodLoop F p₀ a
  let L₁ := regularFamilyPeriodLoop F p₁ a
  let W := regularFamilyCoverWhisker F P
  let H := regularFamilyPeriodLoopHomotopyAlong F P a
  have hraw := Path.Homotopic.map_trans_evalAt H (Path.id)
  have h := hraw.pathCast L₀.source.symm L₁.target.symm
  have hleft :
      (((Path.id.map L₀.continuous).trans (H.evalAt 1)).cast
        L₀.source.symm L₁.target.symm) = L₀.trans W := by
    apply Path.ext
    funext t
    change ((Path.id.map L₀.continuous).trans (H.evalAt 1)) t =
      (L₀.trans W) t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs with ht
    · rfl
    · change regularFamilyCoverProjection F
          ((P ⟨2 * (t : ℝ) - 1, by
              constructor <;> linarith [t.2.1, t.2.2]⟩).1,
            (1 : ℝ) • periodVector
                (regularParameterMap F
                  (P ⟨2 * (t : ℝ) - 1, by
                    constructor <;> linarith [t.2.1, t.2.2]⟩).1).1 a +
              (P ⟨2 * (t : ℝ) - 1, by
                constructor <;> linarith [t.2.1, t.2.2]⟩).2) =
          regularFamilyCoverProjection F
            (P ⟨2 * (t : ℝ) - 1, by
              constructor <;> linarith [t.2.1, t.2.2]⟩)
      simpa using regularFamilyProjection_period_smul F
        (P ⟨2 * (t : ℝ) - 1, by
          constructor <;> linarith [t.2.1, t.2.2]⟩) a
  have hright :
      (((H.evalAt 0).trans (Path.id.map L₁.continuous)).cast
        L₀.source.symm L₁.target.symm) = W.trans L₁ := by
    apply Path.ext
    funext t
    change ((H.evalAt 0).trans (Path.id.map L₁.continuous)) t =
      (W.trans L₁) t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs with ht
    · change regularFamilyCoverProjection F
          ((P ⟨2 * (t : ℝ), by
              constructor <;> linarith [t.2.1, t.2.2]⟩).1,
            (0 : ℝ) • periodVector
                (regularParameterMap F
                  (P ⟨2 * (t : ℝ), by
                    constructor <;> linarith [t.2.1, t.2.2]⟩).1).1 a +
              (P ⟨2 * (t : ℝ), by
                constructor <;> linarith [t.2.1, t.2.2]⟩).2) =
          regularFamilyCoverProjection F
            (P ⟨2 * (t : ℝ), by
              constructor <;> linarith [t.2.1, t.2.2]⟩)
      simp
    · rfl
  rw [hleft, hright] at h
  have hq := Path.Homotopic.Quotient.eq.mpr h
  change Path.Homotopic.Quotient.mk L₀ =
    Path.Homotopic.Quotient.mk (W.trans (L₁.trans W.symm))
  simp only [Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm] at hq ⊢
  rw [← Path.Homotopic.Quotient.trans_assoc]
  rw [show Path.Homotopic.Quotient.trans
      (Path.Homotopic.Quotient.mk W) (Path.Homotopic.Quotient.mk L₁) =
        Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.mk L₀) (Path.Homotopic.Quotient.mk W) from hq.symm]
  rw [Path.Homotopic.Quotient.trans_assoc]
  rw [Path.Homotopic.Quotient.trans_symm]
  rw [Path.Homotopic.Quotient.trans_refl]

/-- The same transport identity after applying any continuous map out of the regular torus
family. -/
public theorem regularFamilyPeriodLoop_transport_map
    {p₀ p₁ : RegularBase (U := U) × ComplexTwoSpace}
    (P : Path p₀ p₁) (a : IntegerPeriods)
    {Y : Type*} [TopologicalSpace Y] (f : C(RegularTotalSpace F, Y)) :
    pathLoopClass ((regularFamilyPeriodLoop F p₀ a).map f.continuous) =
      whiskeredLoopClass ((regularFamilyCoverWhisker F P).map f.continuous)
        ((regularFamilyPeriodLoop F p₁ a).map f.continuous) := by
  have h := congrArg (FundamentalGroup.map f (regularFamilyCoverProjection F p₀))
    (regularFamilyPeriodLoop_transport F P a)
  rw [FundamentalGroup.map_apply] at h
  change (Path.Homotopic.Quotient.mk (regularFamilyPeriodLoop F p₀ a)).map f =
    (Path.Homotopic.Quotient.mk
      ((regularFamilyCoverWhisker F P).trans
        ((regularFamilyPeriodLoop F p₁ a).trans
          (regularFamilyCoverWhisker F P).symm))).map f at h
  rw [← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_map] at h
  change Path.Homotopic.Quotient.mk
      ((regularFamilyPeriodLoop F p₀ a).map f.continuous) =
    Path.Homotopic.Quotient.mk
      (((regularFamilyCoverWhisker F P).map f.continuous).trans
        (((regularFamilyPeriodLoop F p₁ a).map f.continuous).trans
          ((regularFamilyCoverWhisker F P).map f.continuous).symm))
  simpa only [Path.map_trans, ← Path.map_symm] using h

/-- A labelled period loop is invariant under transport along an arbitrary path in the
period-quotient family.  The path is lifted once to the vector-bundle cover; changing the
resulting endpoint representative only translates it by an integral period and hence does not
change the labelled loop. -/
public theorem regularFamilyPeriodLoop_transport_of_path
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    {p₀ p₁ : RegularBase (U := U) × ComplexTwoSpace}
    (W : Path (regularFamilyCoverProjection F p₀)
      (regularFamilyCoverProjection F p₁))
    (a : IntegerPeriods) :
    pathLoopClass (regularFamilyPeriodLoop F p₀ a) =
      whiskeredLoopClass W (regularFamilyPeriodLoop F p₁ a) := by
  let P := regularFamilyPathLift F W hproper p₀ rfl
  let q := P 1
  have hq : regularFamilyCoverProjection F q =
      regularFamilyCoverProjection F p₁ := by
    calc
      regularFamilyCoverProjection F q = W 1 :=
        regularFamilyPathLift_projects F W hproper p₀ rfl 1
      _ = regularFamilyCoverProjection F p₁ := W.target
  have hW : (regularFamilyCoverWhisker F P).cast rfl hq.symm = W := by
    apply Path.ext
    funext t
    exact regularFamilyPathLift_projects F W hproper p₀ rfl t
  have hloop := regularFamilyPeriodLoop_eq_of_projection_eq F q p₁ a hq
  have htransport := regularFamilyPeriodLoop_transport F P a
  rw [← hW]
  convert htransport using 1
  rw [← hloop]
  unfold whiskeredLoopClass
  apply congrArg pathLoopClass
  apply Path.ext
  funext t
  rfl

/-- The arbitrary-path transport identity after applying a continuous map out of the regular
torus family. -/
public theorem regularFamilyPeriodLoop_transport_map_of_path
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    {p₀ p₁ : RegularBase (U := U) × ComplexTwoSpace}
    (W : Path (regularFamilyCoverProjection F p₀)
      (regularFamilyCoverProjection F p₁))
    (a : IntegerPeriods)
    {Y : Type*} [TopologicalSpace Y] (f : C(RegularTotalSpace F, Y)) :
    pathLoopClass ((regularFamilyPeriodLoop F p₀ a).map f.continuous) =
      whiskeredLoopClass (W.map f.continuous)
        ((regularFamilyPeriodLoop F p₁ a).map f.continuous) := by
  have h := congrArg (FundamentalGroup.map f (regularFamilyCoverProjection F p₀))
    (regularFamilyPeriodLoop_transport_of_path F hproper W a)
  rw [FundamentalGroup.map_apply] at h
  change (Path.Homotopic.Quotient.mk (regularFamilyPeriodLoop F p₀ a)).map f =
    (Path.Homotopic.Quotient.mk
      (W.trans ((regularFamilyPeriodLoop F p₁ a).trans W.symm))).map f at h
  rw [← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_map] at h
  change Path.Homotopic.Quotient.mk
      ((regularFamilyPeriodLoop F p₀ a).map f.continuous) =
    Path.Homotopic.Quotient.mk
      ((W.map f.continuous).trans
        (((regularFamilyPeriodLoop F p₁ a).map f.continuous).trans
          (W.map f.continuous).symm))
  simpa only [Path.map_trans, ← Path.map_symm] using h

/-- A genuine path to the `g`-deck translate acts on labelled period loops by `rhoLambda g`.

The inverse conjugation on the left is intentional: Mathlib's fundamental-group multiplication
composes path representatives in reverse order.  Thus this is the exact Lean translation of the
paper's usual-convention formula `ρ T(a) ρ⁻¹ = T(ρΛ(g)a)`. -/
public theorem regularFamilyDeckPathLoop_conjugates_period
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (g : Delta) (p : RegularBase (U := U) × ComplexTwoSpace)
    (W : Path (regularFamilyCoverProjection F p)
      (regularFamilyDeckMap F g (regularFamilyCoverProjection F p)))
    (a : IntegerPeriods) :
    (pathLoopClass (regularFamilyDeckPathLoop F g p W))⁻¹ *
        pathLoopClass ((regularFamilyPeriodLoop F p a).map
          (regularFamilyQuotientMap F).continuous) *
        pathLoopClass (regularFamilyDeckPathLoop F g p W) =
      pathLoopClass ((regularFamilyPeriodLoop F p (rhoLambda g a)).map
        (regularFamilyQuotientMap F).continuous) := by
  let P := regularFamilyPathLift F W hproper p rfl
  let q := P 1
  have hq : regularFamilyCoverProjection F q =
      regularFamilyCoverProjection F (regularDeckMap F g p) := by
    calc
      regularFamilyCoverProjection F q = W 1 :=
        regularFamilyPathLift_projects F W hproper p rfl 1
      _ = regularFamilyDeckMap F g (regularFamilyCoverProjection F p) := W.target
      _ = regularFamilyCoverProjection F (regularDeckMap F g p) :=
        (regularFamilyCoverProjection_regularDeckMap F g p).symm
  let houter : regularFamilyQuotientMap F (regularFamilyCoverProjection F q) =
      regularFamilyQuotientMap F (regularFamilyCoverProjection F p) :=
    (congrArg (regularFamilyQuotientMap F) hq).trans
      ((congrArg (regularFamilyQuotientMap F)
          (regularFamilyCoverProjection_regularDeckMap F g p)).trans
        (regularFamilyQuotientMap_deck F
          (regularFamilyCoverProjection F p) g))
  have hliftLoop :
      (((regularFamilyCoverWhisker F P).map
        (regularFamilyQuotientMap F).continuous).cast rfl houter.symm) =
        regularFamilyDeckPathLoop F g p W := by
    apply Path.ext
    funext t
    exact congrArg (regularFamilyQuotientMap F)
      (regularFamilyPathLift_projects F W hproper p rfl t)
  have hendpoint :
      (((regularFamilyPeriodLoop F q (rhoLambda g a)).map
          (regularFamilyQuotientMap F).continuous).cast
            houter.symm houter.symm) =
        (regularFamilyPeriodLoop F p a).map
          (regularFamilyQuotientMap F).continuous := by
    have hloop := regularFamilyPeriodLoop_eq_of_projection_eq F q
      (regularDeckMap F g p) (rhoLambda g a) hq
    have hdeck := regularFamilyPeriodLoop_deck F g p a
    apply Path.ext
    funext t
    calc
      regularFamilyQuotientMap F (regularFamilyPeriodLoop F q (rhoLambda g a) t) =
          regularFamilyQuotientMap F
            (((regularFamilyPeriodLoop F q (rhoLambda g a)).cast
              hq.symm hq.symm) t) := rfl
      _ = regularFamilyQuotientMap F
          (regularFamilyPeriodLoop F (regularDeckMap F g p) (rhoLambda g a) t) :=
        congrArg (regularFamilyQuotientMap F)
          (congrArg (fun L : Path _ _ ↦ L t) hloop)
      _ = regularFamilyQuotientMap F (regularFamilyPeriodLoop F p a t) :=
        congrArg (fun L : Path _ _ ↦ L t) hdeck
  have htransport := regularFamilyPeriodLoop_transport_map F P
    (rhoLambda g a) (regularFamilyQuotientMap F)
  calc
    (pathLoopClass (regularFamilyDeckPathLoop F g p W))⁻¹ *
          pathLoopClass ((regularFamilyPeriodLoop F p a).map
            (regularFamilyQuotientMap F).continuous) *
          pathLoopClass (regularFamilyDeckPathLoop F g p W) =
        (pathLoopClass (((regularFamilyCoverWhisker F P).map
          (regularFamilyQuotientMap F).continuous).cast rfl houter.symm))⁻¹ *
          pathLoopClass (((regularFamilyPeriodLoop F q (rhoLambda g a)).map
            (regularFamilyQuotientMap F).continuous).cast houter.symm houter.symm) *
          pathLoopClass (((regularFamilyCoverWhisker F P).map
            (regularFamilyQuotientMap F).continuous).cast rfl houter.symm) := by
              rw [hliftLoop, hendpoint]
    _ = whiskeredLoopClass
          ((regularFamilyCoverWhisker F P).map
            (regularFamilyQuotientMap F).continuous)
          ((regularFamilyPeriodLoop F q (rhoLambda g a)).map
            (regularFamilyQuotientMap F).continuous) :=
      (whiskeredLoopClass_eq_conjugate_cast _ _ houter).symm
    _ = pathLoopClass ((regularFamilyPeriodLoop F p (rhoLambda g a)).map
          (regularFamilyQuotientMap F).continuous) := htransport.symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Conjugation of a labelled period depends only on the outer deck label of the loop.

This is the class-level form of `regularFamilyDeckPathLoop_conjugates_period`: an arbitrary
based loop is lifted through the regular-family covering, and its endpoint is identified from
the covering monodromy.  It is useful when the loop is specified geometrically rather than by
an already chosen path between two deck-related representatives. -/
public theorem fundamentalGroup_conjugates_period_of_outerDeck
    (hsource : U.sourceAction = fuchsianSourceAction)
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (g : Delta) (p : RegularBase (U := U) × ComplexTwoSpace)
    (delta : FundamentalGroup (PuncturedGlobalFamily F)
      (regularFamilyQuotientMap F (regularFamilyCoverProjection F p)))
    (hdelta :
      letI := regularFamilyDeckAction F
      let hp := regularFamilyQuotientMap_isQuotientCoveringMap F hsource hproper
      hp.fundamentalGroupToMulOpposite
          ⟨regularFamilyCoverProjection F p, rfl⟩ delta = MulOpposite.op g)
    (a : IntegerPeriods) :
    delta⁻¹ *
        pathLoopClass ((regularFamilyPeriodLoop F p a).map
          (regularFamilyQuotientMap F).continuous) *
        delta =
      pathLoopClass ((regularFamilyPeriodLoop F p (rhoLambda g a)).map
        (regularFamilyQuotientMap F).continuous) := by
  let _ := regularFamilyDeckAction F
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap F hsource hproper
  let x := regularFamilyCoverProjection F p
  let e : (regularFamilyQuotientMap F) ⁻¹'
      {regularFamilyQuotientMap F x} := ⟨x, rfl⟩
  induction delta using Quotient.ind with
  | _ P =>
      have hmove := (hp.fundamentalGroupToMulOpposite_apply_eq_Iff).mp hdelta
      have hend : regularFamilyDeckMap F g x =
          hp.isCoveringMap.liftPath P x (P.source.trans rfl) 1 := by
        have hmono :
            (hp.isCoveringMap.monodromy
                (Path.Homotopic.Quotient.mk P) e : RegularTotalSpace F) =
              hp.isCoveringMap.liftPath P x (P.source.trans rfl) 1 := rfl
        change regularFamilyDeckMap F g x =
          (hp.isCoveringMap.monodromy
            (Path.Homotopic.Quotient.mk P) e : RegularTotalSpace F) at hmove
        have hmove' : regularFamilyDeckMap F g x =
            (hp.isCoveringMap.monodromy
              (Path.Homotopic.Quotient.mk P) e : RegularTotalSpace F) := by
          simpa only [MulOpposite.unop_op] using hmove
        exact hmove'.trans hmono
      let W : Path x (regularFamilyDeckMap F g x) := {
        toFun := hp.isCoveringMap.liftPath P x (P.source.trans rfl)
        continuous_toFun := by fun_prop
        source' := hp.isCoveringMap.liftPath_zero P x (P.source.trans rfl)
        target' := hend.symm
      }
      have hloop : regularFamilyDeckPathLoop F g p W = P := by
        apply Path.ext
        funext t
        change regularFamilyQuotientMap F
            (hp.isCoveringMap.liftPath P x (P.source.trans rfl) t) = P t
        exact congrFun
          (hp.isCoveringMap.liftPath_lifts P x (P.source.trans rfl)) t
      have hconj :=
        regularFamilyDeckPathLoop_conjugates_period F hproper g p W a
      rw [hloop] at hconj
      exact eq_of_heq (heq_of_eq hconj)

set_option backward.isDefEq.respectTransparency.types false in
/-- Basepoint-equality form of `fundamentalGroup_conjugates_period_of_outerDeck`. -/
public theorem fundamentalGroup_conjugates_period_of_outerDeck_of_baseEq
    (hsource : U.sourceAction = fuchsianSourceAction)
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (g : Delta) (p : RegularBase (U := U) × ComplexTwoSpace)
    {z : PuncturedGlobalFamily F}
    (hbase : regularFamilyQuotientMap F (regularFamilyCoverProjection F p) = z)
    (delta : FundamentalGroup (PuncturedGlobalFamily F) z)
    (hdelta :
      letI := regularFamilyDeckAction F
      let hp := regularFamilyQuotientMap_isQuotientCoveringMap F hsource hproper
      hp.fundamentalGroupToMulOpposite
          ⟨regularFamilyCoverProjection F p, hbase⟩ delta = MulOpposite.op g)
    (a : IntegerPeriods) :
    delta⁻¹ *
        (show FundamentalGroup (PuncturedGlobalFamily F) z from
          Path.Homotopic.Quotient.cast
            (pathLoopClass ((regularFamilyPeriodLoop F p a).map
              (regularFamilyQuotientMap F).continuous)) hbase.symm hbase.symm) *
        delta =
      (show FundamentalGroup (PuncturedGlobalFamily F) z from
        Path.Homotopic.Quotient.cast
          (pathLoopClass ((regularFamilyPeriodLoop F p (rhoLambda g a)).map
            (regularFamilyQuotientMap F).continuous)) hbase.symm hbase.symm) := by
  subst z
  exact fundamentalGroup_conjugates_period_of_outerDeck F hsource hproper g p delta hdelta a

end SphereSixComplex.Geometry.GlobalTorusFamily
