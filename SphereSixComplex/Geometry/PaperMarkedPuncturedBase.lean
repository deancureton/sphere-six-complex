module

public import SphereSixComplex.Topology.PaperSectionSevenEllipticBaseCoordinate
public import SphereSixComplex.Topology.TwicePuncturedComplexFundamentalGroupGeneration
public import SphereSixComplex.TriangleGroup.FuchsianProperFreeness
public import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph

/-!
# The marked ordinary base and zero section of the central family

The normalized Fuchsian coordinate identifies the regular source orbit quotient with the
twice-punctured complex plane.  The zero vector descends through both quotient stages and gives
a literal section of the central torus family over that ordinary base.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContDiff Manifold
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.GlobalTorusFamily

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianProperFreeness
open SphereSixComplex.Geometry.ComplexTorus SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.AnalyticTorusFamily

variable {U : TriangleUniformization} (F : PeriodFunctions U)

local instance regularBaseDeckAction : MulAction Delta (RegularBase (U := U)) :=
  regularSourceMulAction U

local instance regularTotalDeckAction : MulAction Delta (RegularTotalSpace F) :=
  regularFamilyDeckAction F

/-- The regular upper-half-plane locus modulo the triangle-group action. -/
public abbrev PuncturedOrbifoldBase :=
  letI := regularSourceMulAction U
  OrbitQuotient (M := RegularBase (U := U)) (G := Delta)

/-- Quotient map from the regular source to the ordinary punctured base. -/
public noncomputable def regularBaseQuotientMap :
    C(RegularBase (U := U), PuncturedOrbifoldBase (U := U)) := by
  let _ := regularSourceMulAction U
  exact ⟨quotientProjection, continuous_quot_mk⟩

/-- Away from the two elliptic fixed-point orbits, the source quotient is an honest quotient
covering. -/
public theorem regularBaseQuotientMap_isQuotientCoveringMap
    (hsource : U.sourceAction = fuchsianSourceAction)
    (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    letI := regularSourceMulAction U
    IsQuotientCoveringMap (regularBaseQuotientMap (U := U)) Delta := by
  let _ : MulAction Delta (RegularBase (U := U)) := regularSourceMulAction U
  let _ : LocallyCompactSpace (RegularBase (U := U)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : ContinuousConstSMul Delta (RegularBase (U := U)) :=
    ⟨fun g ↦ by
      apply Continuous.subtype_mk
      exact (U.sourceAction_contMDiff g ∞).continuous.comp continuous_subtype_val⟩
  let _ : IsCancelSMul Delta (RegularBase (U := U)) :=
    regularSource_isCancelSMul_of_fuchsian hsource hproper
  let _ : ProperlyDiscontinuousSMul Delta (RegularBase (U := U)) := by
    constructor
    intro K L hK hL
    have hK' : IsCompact ((fun z : RegularBase (U := U) ↦ z.1) '' K) :=
      hK.image continuous_subtype_val
    have hL' : IsCompact ((fun z : RegularBase (U := U) ↦ z.1) '' L) :=
      hL.image continuous_subtype_val
    apply (hproper hK' hL').subset
    intro g hg
    rcases hg with ⟨z, ⟨w, hwK, hwz⟩, hzL⟩
    refine ⟨z.1, ?_, ⟨z, hzL, rfl⟩⟩
    refine ⟨w.1, ⟨w, hwK, rfl⟩, ?_⟩
    exact congrArg Subtype.val hwz
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

/-- The zero section before the varying period-lattice quotient. -/
public def regularFamilyZeroSection :
    C(RegularBase (U := U), RegularTotalSpace F) :=
  ⟨fun b ↦ Quotient.mk _ (b, 0),
    continuous_quot_mk.comp (continuous_id.prodMk continuous_const)⟩

@[simp]
public theorem regularFamilyZeroSection_apply (b : RegularBase (U := U)) :
    regularFamilyZeroSection F b = Quotient.mk _ (b, 0) := rfl

/-- Triangle-group transport preserves the zero section exactly. -/
public theorem regularFamilyZeroSection_equivariant (g : Delta)
    (b : RegularBase (U := U)) :
    regularFamilyDeckMap F g (regularFamilyZeroSection F b) =
      regularFamilyZeroSection F (regularSourceEquiv g b) := by
  rw [regularFamilyZeroSection_apply, regularFamilyDeckMap_mk,
    regularFamilyZeroSection_apply]
  apply congrArg (fun p : RegularBase (U := U) × ComplexTwoSpace ↦
    (Quotient.mk _ p : RegularTotalSpace F))
  apply Prod.ext
  · rfl
  · exact map_zero (periodTransport g (regularParameterMap F b))

/-- The zero section descended through the outer triangle-group quotient. -/
public noncomputable def puncturedGlobalZeroSection :
    C(PuncturedOrbifoldBase (U := U), PuncturedGlobalFamily F) := by
  refine ⟨Quotient.lift
    (fun b ↦ quotientProjection (M := RegularTotalSpace F) (G := Delta)
      (regularFamilyZeroSection F b)) ?_, ?_⟩
  · intro a b hab
    change MulAction.orbitRel Delta (RegularBase (U := U)) a b at hab
    apply Quotient.sound
    change MulAction.orbitRel Delta (RegularTotalSpace F)
      (regularFamilyZeroSection F a) (regularFamilyZeroSection F b)
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hab ⊢
    obtain ⟨g, rfl⟩ := hab
    exact ⟨g, regularFamilyZeroSection_equivariant F g b⟩
  · apply continuous_quot_lift
    exact continuous_quot_mk.comp (regularFamilyZeroSection F).continuous

public theorem puncturedGlobalZeroSection_mk (b : RegularBase (U := U)) :
    puncturedGlobalZeroSection F (regularBaseQuotientMap (U := U) b) =
      quotientProjection (M := RegularTotalSpace F) (G := Delta)
        (regularFamilyZeroSection F b) := rfl

/-- Forget the torus coordinate after both quotient stages. -/
public noncomputable def puncturedGlobalBaseProjection :
    C(PuncturedGlobalFamily F, PuncturedOrbifoldBase (U := U)) := by
  refine ⟨Quotient.map (regularTotalSpaceBase F) ?_, ?_⟩
  · intro x y hxy
    change MulAction.orbitRel Delta (RegularTotalSpace F) x y at hxy
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hxy
    change MulAction.orbitRel Delta (RegularBase (U := U))
      (regularTotalSpaceBase F x) (regularTotalSpaceBase F y)
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    obtain ⟨g, hg⟩ := hxy
    refine ⟨g, ?_⟩
    calc
      regularSourceEquiv g (regularTotalSpaceBase F y) =
          regularTotalSpaceBase F (regularFamilyDeckMap F g y) :=
        (regularTotalSpaceBase_familyDeckMap F g y).symm
      _ = regularTotalSpaceBase F x := congrArg (regularTotalSpaceBase F) hg
  · exact continuous_quot_map _ (regularTotalSpaceBase_continuous F)

@[simp]
public theorem puncturedGlobalBaseProjection_zeroSection
    (q : PuncturedOrbifoldBase (U := U)) :
    puncturedGlobalBaseProjection F (puncturedGlobalZeroSection F q) = q := by
  induction q using Quotient.inductionOn with
  | _ b => rfl

end SphereSixComplex.Geometry.GlobalTorusFamily

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Topology
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.TriangleGroup.FuchsianProperFreeness

variable (A : PaperAnalyticData)

public abbrev paperTriangleUniformization :=
  A.modular.modularParameter.toTriangleUniformization

/-- The exact normalized coordinate identifies the ordinary punctured quotient base with
`ℂ \ {0,1}`. -/
public noncomputable def puncturedBaseHomeomorphTwicePuncturedComplex :
    PuncturedOrbifoldBase (U := A.paperTriangleUniformization) ≃ₜ
      TwicePuncturedComplex := by
  let _ := regularSourceMulAction A.paperTriangleUniformization
  let f : C(RegularBase (U := A.paperTriangleUniformization),
      TwicePuncturedComplex) :=
    ⟨A.regularCoordinate, A.regularCoordinate_isLocalHomeomorph.continuous⟩
  let e : Quotient (MulAction.orbitRel Delta
      (RegularBase (U := A.paperTriangleUniformization))) ≃ₜ
      Quotient (Setoid.ker f) :=
    Homeomorph.Quotient.congrRight fun z w ↦ by
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      change (∃ g : Delta, g • w = z) ↔ f z = f w
      rw [Subtype.ext_iff]
      dsimp only [f]
      change (∃ g : Delta, g • w = z) ↔
        A.modular.sourceCoordinate.coordinate z =
          A.modular.sourceCoordinate.coordinate w
      constructor
      · rintro ⟨g, hg⟩
        change regularSourceEquiv g w = z at hg
        calc
          A.modular.sourceCoordinate.coordinate z =
              A.modular.sourceCoordinate.coordinate
                (A.paperTriangleUniformization.sourceAction g • w) :=
            congrArg A.modular.sourceCoordinate.coordinate
              (congrArg Subtype.val hg).symm
          _ = A.modular.sourceCoordinate.coordinate w := by
            rw [A.modular.modularParameter.toTriangleUniformization_sourceAction]
            exact A.modular.sourceCoordinate.coordinate_invariant g w
      · intro hzw
        obtain ⟨g, hg⟩ :=
          (A.modular.sourceCoordinate.coordinate_eq_iff_orbit z w).mp hzw
        refine ⟨g⁻¹, ?_⟩
        change regularSourceEquiv g⁻¹ w = z
        apply Subtype.ext
        change A.paperTriangleUniformization.sourceAction g⁻¹ • w.1 = z.1
        rw [A.modular.modularParameter.toTriangleUniformization_sourceAction]
        calc
          fuchsianSourceAction g⁻¹ • w.1 =
              fuchsianSourceAction g⁻¹ • (fuchsianSourceAction g • z.1) :=
            congrArg _ hg.symm
          _ = z.1 := by
            rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have hfq : Topology.IsQuotientMap f :=
    A.regularCoordinate_isLocalHomeomorph.isOpenMap.isQuotientMap
      f.continuous (by simpa only [f] using A.regularCoordinate_surjective)
  exact e.trans hfq.homeomorph

@[simp]
public theorem puncturedBaseHomeomorphTwicePuncturedComplex_mk
    (z : RegularBase (U := A.paperTriangleUniformization)) :
    A.puncturedBaseHomeomorphTwicePuncturedComplex
        (regularBaseQuotientMap (U := A.paperTriangleUniformization) z) =
      A.regularCoordinate z := rfl

/-- The holomorphic zero section of the actual central family over its ordinary punctured base. -/
public noncomputable def centralZeroSection :
    C(PuncturedOrbifoldBase (U := A.paperTriangleUniformization), A.CentralFamily) :=
  puncturedGlobalZeroSection A.periods

/-- The actual central-family coordinate recovers the marked ordinary base along the zero
section. -/
public theorem centralFamilyCoordinate_zeroSection
    (q : PuncturedOrbifoldBase (U := A.paperTriangleUniformization)) :
    A.centralFamilyCoordinate (A.centralZeroSection q) =
      A.puncturedBaseHomeomorphTwicePuncturedComplex q := by
  induction q using Quotient.inductionOn with
  | _ z => rfl

/-- The common marked point `1/2` in the ordinary quotient base. -/
public noncomputable def markedPuncturedBasepoint :
    PuncturedOrbifoldBase (U := A.paperTriangleUniformization) :=
  A.puncturedBaseHomeomorphTwicePuncturedComplex.symm
    twicePuncturedComplexBasepoint

/-- The two actual finite-puncture meridians transported through the exact quotient
coordinate. -/
public noncomputable def markedZeroBaseMeridian :
    Path A.markedPuncturedBasepoint A.markedPuncturedBasepoint :=
  twicePuncturedClockwiseZeroMeridian.map
    A.puncturedBaseHomeomorphTwicePuncturedComplex.symm.continuous

public noncomputable def markedOneBaseMeridian :
    Path A.markedPuncturedBasepoint A.markedPuncturedBasepoint :=
  twicePuncturedClockwiseOneMeridian.map
    A.puncturedBaseHomeomorphTwicePuncturedComplex.symm.continuous

/-- The marked finite meridians lifted along the literal zero section. -/
public noncomputable def markedZeroCentralMeridian :
    Path (A.centralZeroSection A.markedPuncturedBasepoint)
      (A.centralZeroSection A.markedPuncturedBasepoint) :=
  A.markedZeroBaseMeridian.map A.centralZeroSection.continuous

public noncomputable def markedOneCentralMeridian :
    Path (A.centralZeroSection A.markedPuncturedBasepoint)
      (A.centralZeroSection A.markedPuncturedBasepoint) :=
  A.markedOneBaseMeridian.map A.centralZeroSection.continuous

/-! ## The induced marked fundamental-group classes -/

/-- The exact coordinate homeomorphism on based fundamental groups. -/
public noncomputable def puncturedBaseFundamentalGroupEquiv :
    FundamentalGroup (PuncturedOrbifoldBase
        (U := A.paperTriangleUniformization)) A.markedPuncturedBasepoint ≃*
      FundamentalGroup TwicePuncturedComplex twicePuncturedComplexBasepoint :=
  TauCeti.FundamentalGroup.homeomorphMulEquivOfEq
    A.puncturedBaseHomeomorphTwicePuncturedComplex (by
      simp only [markedPuncturedBasepoint]
      exact A.puncturedBaseHomeomorphTwicePuncturedComplex.apply_symm_apply _)

/-- The two finite-puncture classes in the actual ordinary quotient base.  Defining them
through the based homeomorphism records the endpoint transport forced by `e (e⁻¹ b) = b`.
They are represented by `markedZeroBaseMeridian` and `markedOneBaseMeridian`, respectively. -/
public noncomputable def markedZeroBaseMeridianClass :
    FundamentalGroup (PuncturedOrbifoldBase
      (U := A.paperTriangleUniformization)) A.markedPuncturedBasepoint :=
  A.puncturedBaseFundamentalGroupEquiv.symm
    TwicePuncturedComplex.zeroMeridianClass

public noncomputable def markedOneBaseMeridianClass :
    FundamentalGroup (PuncturedOrbifoldBase
      (U := A.paperTriangleUniformization)) A.markedPuncturedBasepoint :=
  A.puncturedBaseFundamentalGroupEquiv.symm
    TwicePuncturedComplex.oneMeridianClass

@[simp]
public theorem puncturedBaseFundamentalGroupEquiv_zero :
    A.puncturedBaseFundamentalGroupEquiv A.markedZeroBaseMeridianClass =
      TwicePuncturedComplex.zeroMeridianClass :=
  A.puncturedBaseFundamentalGroupEquiv.apply_symm_apply _

@[simp]
public theorem puncturedBaseFundamentalGroupEquiv_one :
    A.puncturedBaseFundamentalGroupEquiv A.markedOneBaseMeridianClass =
      TwicePuncturedComplex.oneMeridianClass :=
  A.puncturedBaseFundamentalGroupEquiv.apply_symm_apply _

public theorem markedZeroBaseMeridianClass_eq_pathLoopClass :
    A.markedZeroBaseMeridianClass =
      Path.Homotopic.Quotient.mk A.markedZeroBaseMeridian := by
  unfold markedZeroBaseMeridianClass puncturedBaseFundamentalGroupEquiv
    markedZeroBaseMeridian TwicePuncturedComplex.zeroMeridianClass
  rw [TauCeti.FundamentalGroup.homeomorphMulEquivOfEq_symm_apply,
    FundamentalGroup.mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map]
  rfl

public theorem markedOneBaseMeridianClass_eq_pathLoopClass :
    A.markedOneBaseMeridianClass =
      Path.Homotopic.Quotient.mk A.markedOneBaseMeridian := by
  unfold markedOneBaseMeridianClass puncturedBaseFundamentalGroupEquiv
    markedOneBaseMeridian TwicePuncturedComplex.oneMeridianClass
  rw [TauCeti.FundamentalGroup.homeomorphMulEquivOfEq_symm_apply,
    FundamentalGroup.mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map]
  rfl

/-- The two exact finite-puncture meridians generate the actual ordinary quotient base. -/
public theorem markedBaseMeridians_generate :
    Subgroup.closure ({A.markedZeroBaseMeridianClass,
        A.markedOneBaseMeridianClass} :
      Set (FundamentalGroup (PuncturedOrbifoldBase
        (U := A.paperTriangleUniformization)) A.markedPuncturedBasepoint)) = ⊤ := by
  let K := Subgroup.closure ({A.markedZeroBaseMeridianClass,
    A.markedOneBaseMeridianClass} :
      Set (FundamentalGroup (PuncturedOrbifoldBase
        (U := A.paperTriangleUniformization)) A.markedPuncturedBasepoint))
  apply top_unique
  intro γ _
  have himage : A.puncturedBaseFundamentalGroupEquiv γ ∈
      Subgroup.closure ({TwicePuncturedComplex.zeroMeridianClass,
        TwicePuncturedComplex.oneMeridianClass} :
        Set (FundamentalGroup TwicePuncturedComplex
          twicePuncturedComplexBasepoint)) := by
    rw [TwicePuncturedComplex.markedMeridians_generate]
    trivial
  have hmap : A.puncturedBaseFundamentalGroupEquiv γ ∈
      K.map A.puncturedBaseFundamentalGroupEquiv.toMonoidHom := by
    rw [MonoidHom.map_closure]
    have hset : A.puncturedBaseFundamentalGroupEquiv.toMonoidHom ''
        ({A.markedZeroBaseMeridianClass, A.markedOneBaseMeridianClass} :
          Set (FundamentalGroup (PuncturedOrbifoldBase
            (U := A.paperTriangleUniformization)) A.markedPuncturedBasepoint)) =
        ({TwicePuncturedComplex.zeroMeridianClass,
          TwicePuncturedComplex.oneMeridianClass} :
          Set (FundamentalGroup TwicePuncturedComplex
            twicePuncturedComplexBasepoint)) := by
      ext x
      simp [eq_comm]
    rw [hset]
    exact himage
  obtain ⟨δ, hδ, hδeq⟩ := hmap
  have : δ = γ := A.puncturedBaseFundamentalGroupEquiv.injective hδeq
  exact this ▸ hδ

/-- Inclusion of the marked base fundamental group along the literal zero section. -/
public noncomputable def centralZeroSectionFundamentalGroupMap :
    FundamentalGroup (PuncturedOrbifoldBase
        (U := A.paperTriangleUniformization)) A.markedPuncturedBasepoint →*
      FundamentalGroup A.CentralFamily
        (A.centralZeroSection A.markedPuncturedBasepoint) :=
  FundamentalGroup.map A.centralZeroSection A.markedPuncturedBasepoint

/-- The two finite-puncture classes in the actual central family, along its zero section. -/
public noncomputable def markedZeroCentralMeridianClass :
    FundamentalGroup A.CentralFamily
      (A.centralZeroSection A.markedPuncturedBasepoint) :=
  A.centralZeroSectionFundamentalGroupMap A.markedZeroBaseMeridianClass

public noncomputable def markedOneCentralMeridianClass :
    FundamentalGroup A.CentralFamily
      (A.centralZeroSection A.markedPuncturedBasepoint) :=
  A.centralZeroSectionFundamentalGroupMap A.markedOneBaseMeridianClass

@[simp]
public theorem centralZeroSectionFundamentalGroupMap_zero :
    A.centralZeroSectionFundamentalGroupMap A.markedZeroBaseMeridianClass =
      A.markedZeroCentralMeridianClass := rfl

@[simp]
public theorem centralZeroSectionFundamentalGroupMap_one :
    A.centralZeroSectionFundamentalGroupMap A.markedOneBaseMeridianClass =
      A.markedOneCentralMeridianClass := rfl

public theorem markedZeroCentralMeridianClass_eq_pathLoopClass :
    A.markedZeroCentralMeridianClass =
      Path.Homotopic.Quotient.mk A.markedZeroCentralMeridian := by
  unfold markedZeroCentralMeridianClass
  rw [A.markedZeroBaseMeridianClass_eq_pathLoopClass]
  unfold centralZeroSectionFundamentalGroupMap markedZeroCentralMeridian
  rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]

public theorem markedOneCentralMeridianClass_eq_pathLoopClass :
    A.markedOneCentralMeridianClass =
      Path.Homotopic.Quotient.mk A.markedOneCentralMeridian := by
  unfold markedOneCentralMeridianClass
  rw [A.markedOneBaseMeridianClass_eq_pathLoopClass]
  unfold centralZeroSectionFundamentalGroupMap markedOneCentralMeridian
  rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]

/-- Every zero-section loop belongs to the subgroup generated by the two marked central
meridians. -/
public theorem centralZeroSectionFundamentalGroupMap_range_le_markedClosure :
    A.centralZeroSectionFundamentalGroupMap.range ≤
      Subgroup.closure ({A.markedZeroCentralMeridianClass,
        A.markedOneCentralMeridianClass} :
        Set (FundamentalGroup A.CentralFamily
          (A.centralZeroSection A.markedPuncturedBasepoint))) := by
  intro γ hγ
  obtain ⟨δ, rfl⟩ := hγ
  let K := Subgroup.closure ({A.markedZeroCentralMeridianClass,
    A.markedOneCentralMeridianClass} :
      Set (FundamentalGroup A.CentralFamily
        (A.centralZeroSection A.markedPuncturedBasepoint)))
  have hle : Subgroup.closure ({A.markedZeroBaseMeridianClass,
      A.markedOneBaseMeridianClass} :
      Set (FundamentalGroup (PuncturedOrbifoldBase
        (U := A.paperTriangleUniformization)) A.markedPuncturedBasepoint)) ≤
      K.comap A.centralZeroSectionFundamentalGroupMap := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases hx with rfl | rfl
    · apply Subgroup.subset_closure
      simp
    · apply Subgroup.subset_closure
      simp
  apply hle
  rw [A.markedBaseMeridians_generate]
  trivial

end SphereSixComplex.Geometry.PaperAnalyticData

end
