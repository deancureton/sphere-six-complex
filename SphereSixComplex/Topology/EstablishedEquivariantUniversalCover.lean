module

public import SphereSixComplex.Topology.EstablishedEquivariantUniversalCoverProof
public import SphereSixComplex.Geometry.FuchsianPuncturedGlobalFamilyNiceness
public import SphereSixComplex.Periods.FuchsianUniformizationBridge
public import SphereSixComplex.Topology.PaperGeometricCentralCore
public import SphereSixComplex.Topology.TwicePuncturedComplexFreeFundamentalGroupProof
import TauCeti.Topology.Homotopy.Covering

/-!
# The paper's punctured-family affine fundamental group

The definitions of the two-meridian deck group, the affine deck extension and the equivariant
affine universal cover are in `EstablishedEquivariantUniversalCoverDefs`, and are re-exported
here, so every module path using them is unchanged.

This module proves injectivity of the paper's canonical affine presentation and derives the
equivariant universal cover.

## What is assumed, and why in this form

The geometric period loops and the two marked meridians define a canonical homomorphism from
`IntegerPeriods ⋊ FreeGroup (Fin 2)` to the fundamental group.  The torus-lattice kernel is
faithful by the two explicit quotient coverings, and the ordinary base projection recovers the
free component.  The sole retained input is the classical relation-free van Kampen theorem for
the two marked meridians of `\mathbb C \setminus \{0,1\}`.

The based-path cover also needs the base to be path connected, locally path connected and
semilocally simply connected.  None of the three is assumed: over a Fuchsian modular parameter the
family is a complex manifold and connected, so all three follow
(`Geometry.FuchsianPuncturedGlobalFamilyNiceness`).

The explicit affine mapping-torus covers prove the corresponding cyclic statements on both
elliptic collars; the global free relation is supplied at the ordinary twice-punctured base.

The covering space is not assumed.  The resulting fundamental-group equivalence is transported
onto Tau Ceti's based-path universal cover.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex

namespace AffineTorusCorePiOneData

variable {G Λ : Type*} [Group G] [AddCommGroup Λ]
variable (M : TwoMeridianDeckGroup →* Multiplicative (AddAut Λ))
variable (C : AffineTorusCorePiOneData G Λ (firstFreeMonodromy M) (secondFreeMonodromy M))

public def freeMeridianHom : TwoMeridianDeckGroup →* G :=
  FreeGroup.lift fun i ↦ if i = 0 then C.rhoOne else C.rhoTwo

public theorem freeMeridianHom_conjugate (g : TwoMeridianDeckGroup) (a : Λ) :
    freeMeridianHom M C g * Additive.toMul (C.translation a) *
        (freeMeridianHom M C g)⁻¹ =
      Additive.toMul (C.translation ((M g).toAdd a)) := by
  induction g using FreeGroup.induction_on generalizing a with
  | C1 => simp
  | of i =>
      fin_cases i
      · simpa [freeMeridianHom, firstFreeMonodromy, firstMeridian] using C.conjugate_one a
      · simpa [freeMeridianHom, secondFreeMonodromy, secondMeridian] using C.conjugate_two a
  | inv_of i hi =>
      let g := FreeGroup.of i
      have h := hi ((M g).toAdd.symm a)
      have hM : (M g).toAdd ((M g).toAdd.symm a) = a := (M g).toAdd.apply_symm_apply a
      rw [hM] at h
      rw [map_inv, map_inv]
      calc
        (freeMeridianHom M C g)⁻¹ * Additive.toMul (C.translation a) *
              ((freeMeridianHom M C g)⁻¹)⁻¹ =
            (freeMeridianHom M C g)⁻¹ *
              (freeMeridianHom M C g *
                Additive.toMul (C.translation ((M g).toAdd.symm a)) *
                (freeMeridianHom M C g)⁻¹) *
              ((freeMeridianHom M C g)⁻¹)⁻¹ := by rw [h]
        _ = Additive.toMul (C.translation ((M g).toAdd.symm a)) := by group
  | mul g h hg hh =>
      rw [map_mul, map_mul]
      calc
        (freeMeridianHom M C g * freeMeridianHom M C h) *
              Additive.toMul (C.translation a) *
              (freeMeridianHom M C g * freeMeridianHom M C h)⁻¹ =
            freeMeridianHom M C g *
              (freeMeridianHom M C h * Additive.toMul (C.translation a) *
                (freeMeridianHom M C h)⁻¹) *
              (freeMeridianHom M C g)⁻¹ := by group
        _ = freeMeridianHom M C g *
              Additive.toMul (C.translation ((M h).toAdd a)) *
              (freeMeridianHom M C g)⁻¹ := by rw [hh]
        _ = Additive.toMul (C.translation ((M g).toAdd ((M h).toAdd a))) := hg _
        _ = Additive.toMul (C.translation (((M g) * (M h)).toAdd a)) := rfl

public def freeAffinePresentationHom : FreeTwoMeridianAffineDeck Λ M →* G :=
  SemidirectProduct.lift C.translation.toMultiplicative (freeMeridianHom M C) (by
    intro g
    apply MonoidHom.ext
    intro a
    exact (freeMeridianHom_conjugate M C g a.toAdd).symm)

@[simp]
public theorem freeAffinePresentationHom_translation (a : Λ) :
    freeAffinePresentationHom M C
        (Additive.toMul (freeAffineTranslation (M := M) a)) =
      Additive.toMul (C.translation a) := by
  change Additive.toMul (C.translation a) * 1 = _
  simp

@[simp]
public theorem freeAffinePresentationHom_inl (a : Multiplicative Λ) :
    freeAffinePresentationHom M C (SemidirectProduct.inl a) =
      Additive.toMul (C.translation a.toAdd) := by
  rw [← ofAdd_toAdd a]
  exact freeAffinePresentationHom_translation M C a.toAdd

@[simp]
public theorem freeAffinePresentationHom_inr (g : TwoMeridianDeckGroup) :
    freeAffinePresentationHom M C (SemidirectProduct.inr g) =
      freeMeridianHom M C g := by
  simp [freeAffinePresentationHom, SemidirectProduct.lift]
  exact map_one C.translation.toMultiplicative

@[simp]
public theorem freeAffinePresentationHom_first :
    freeAffinePresentationHom M C
        (freeAffineLift (Λ := Λ) (M := M) firstMeridian) = C.rhoOne := by
  simp [freeAffinePresentationHom, freeAffineLift, SemidirectProduct.lift, freeMeridianHom,
    firstMeridian]
  exact map_one C.translation.toMultiplicative

@[simp]
public theorem freeAffinePresentationHom_second :
    freeAffinePresentationHom M C
        (freeAffineLift (Λ := Λ) (M := M) secondMeridian) = C.rhoTwo := by
  simp [freeAffinePresentationHom, freeAffineLift, SemidirectProduct.lift, freeMeridianHom,
    secondMeridian]
  exact map_one C.translation.toMultiplicative

public theorem freeAffinePresentationHom_surjective :
    Function.Surjective (freeAffinePresentationHom M C) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← C.generators_generate, Subgroup.closure_le]
  intro g hg
  rcases hg with ⟨a, rfl⟩ | hg
  · exact ⟨Additive.toMul (freeAffineTranslation (M := M) a), by simp⟩
  · rcases hg with rfl | rfl
    · exact ⟨freeAffineLift firstMeridian, by simp⟩
    · exact ⟨freeAffineLift secondMeridian, by simp⟩

end AffineTorusCorePiOneData

namespace Geometry.GlobalTorusFamily

open Periods TriangleGroup Geometry.ComplexTorus
open SphereSixComplex.LatticeData SphereSixComplex.Topology
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

/-- The free two-meridian monodromy of the paper's punctured global family. -/
public noncomputable abbrev paperPuncturedGlobalFamilyFreeMonodromy :
    TwoMeridianDeckGroup →* Multiplicative (AddAut Lattice) :=
  freeTwoMeridianMonodromy (twoMeridianOrbifoldMap g₁ g₂)
    integralOrbifoldPeriodMonodromy

public theorem firstFreeMonodromy_paperPuncturedGlobalFamilyFreeMonodromy :
    firstFreeMonodromy paperPuncturedGlobalFamilyFreeMonodromy = paperMonodromyOne := by
  apply AddMonoidHom.ext
  intro a
  simp [firstFreeMonodromy, paperPuncturedGlobalFamilyFreeMonodromy,
    freeTwoMeridianMonodromy, integralOrbifoldPeriodMonodromy,
    paperMonodromyOne]

public theorem secondFreeMonodromy_paperPuncturedGlobalFamilyFreeMonodromy :
    secondFreeMonodromy paperPuncturedGlobalFamilyFreeMonodromy = paperMonodromyTwo := by
  apply AddMonoidHom.ext
  intro a
  simp [secondFreeMonodromy, paperPuncturedGlobalFamilyFreeMonodromy,
    freeTwoMeridianMonodromy, integralOrbifoldPeriodMonodromy,
    paperMonodromyTwo]

/-- The geometric translations and marked meridians as affine core data at the actual cusp
basepoint. -/
public noncomputable def paperPuncturedGlobalFamilyAffineCorePiOneData
    (A : PaperAnalyticData) :
    AffineTorusCorePiOneData
      (FundamentalGroup A.CentralFamily A.actualCuspCentralBase)
      Lattice (firstFreeMonodromy paperPuncturedGlobalFamilyFreeMonodromy)
        (secondFreeMonodromy paperPuncturedGlobalFamilyFreeMonodromy) where
  translation := A.correctedActualCuspCentralTranslation
  rhoOne := A.geometricCentralRhoOne
  rhoTwo := A.geometricCentralRhoTwo
  conjugate_one a := by
    rw [firstFreeMonodromy_paperPuncturedGlobalFamilyFreeMonodromy]
    exact A.geometricCentralRhoOne_conjugates_correctedTranslation a
  conjugate_two a := by
    rw [secondFreeMonodromy_paperPuncturedGlobalFamilyFreeMonodromy]
    exact A.geometricCentralRhoTwo_conjugates_correctedTranslation a
  generators_generate := A.actualCuspGeometricCorePiOneData.generators_generate

@[simp]
public theorem paperPuncturedGlobalFamilyAffineCorePiOneData_translation
    (A : PaperAnalyticData) :
    (paperPuncturedGlobalFamilyAffineCorePiOneData A).translation =
      A.correctedActualCuspCentralTranslation := by
  rfl

@[simp]
public theorem paperPuncturedGlobalFamilyAffineCorePiOneData_rhoOne
    (A : PaperAnalyticData) :
    (paperPuncturedGlobalFamilyAffineCorePiOneData A).rhoOne =
      A.geometricCentralRhoOne := by
  rfl

@[simp]
public theorem paperPuncturedGlobalFamilyAffineCorePiOneData_rhoTwo
    (A : PaperAnalyticData) :
    (paperPuncturedGlobalFamilyAffineCorePiOneData A).rhoTwo =
      A.geometricCentralRhoTwo := by
  rfl

private theorem regularFamilyTranslationAtZero_injective
    (A : PaperAnalyticData) :
    Function.Injective
      (regularFamilyTranslationAtZero A.periods A.markedRegularBaseLift) := by
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let hp := regularFamilyCoverProjection_isQuotientCoveringMap A.periods hproper
  intro a b hab
  have hdeck := congrArg
    (hp.fundamentalGroupToMulOpposite
      ⟨(A.markedRegularBaseLift, (0 : ComplexTwoSpace)), rfl⟩)
    (congrArg Additive.toMul hab)
  rw [regularFamilyTranslationAtZero_deck A.periods hproper,
    regularFamilyTranslationAtZero_deck A.periods hproper] at hdeck
  exact congrArg (fun z ↦ z.unop.coeff) hdeck

private theorem centralTranslationAtZero_injective
    (A : PaperAnalyticData) :
    Function.Injective
      (centralTranslationAtZero A.periods A.markedRegularBaseLift) := by
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let _ := regularFamilyDeckAction A.periods
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction hproper
  intro a b hab
  apply regularFamilyTranslationAtZero_injective A
  apply Additive.toMul.injective
  apply TauCeti.IsCoveringMap.map_injective hp.isCoveringMap
  exact congrArg Additive.toMul hab

private theorem markedCentralTranslation_injective
    (A : PaperAnalyticData) :
    Function.Injective A.markedCentralTranslation := by
  intro a b hab
  apply centralTranslationAtZero_injective A
  apply Additive.toMul.injective
  apply A.markedCentralBaseEquiv.injective
  exact congrArg Additive.toMul hab

private theorem geometricCentralTranslation_injective
    (A : PaperAnalyticData) :
    Function.Injective A.geometricCentralTranslation := by
  intro a b hab
  apply markedCentralTranslation_injective A
  apply Additive.toMul.injective
  apply A.markedCentralToActualCuspEquiv.injective
  exact congrArg Additive.toMul hab

private theorem actualCuspCentralTranslation_injective
    (A : PaperAnalyticData) :
    Function.Injective A.actualCuspCentralTranslation := by
  obtain ⟨g, hg⟩ := A.exists_geometricCentralTranslationReindexing
  intro a b hab
  apply (rhoLambda g).injective
  apply geometricCentralTranslation_injective A
  apply Additive.toMul.injective
  rw [hg, hg]
  simpa using congrArg Additive.toMul hab

public theorem correctedActualCuspCentralTranslation_injective
    (A : PaperAnalyticData) :
    Function.Injective A.correctedActualCuspCentralTranslation := by
  intro a b hab
  apply (rhoLambda
    ((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)).injective
  apply actualCuspCentralTranslation_injective A
  exact hab

/-- Projection of the marked central-family fundamental group to the exactly normalized
twice-punctured affine base. -/
public noncomputable def markedCentralBaseProjection
    (A : PaperAnalyticData) :
    FundamentalGroup A.CentralFamily
        (A.centralZeroSection A.markedPuncturedBasepoint) →*
      FundamentalGroup TwicePuncturedComplex twicePuncturedComplexBasepoint :=
  FundamentalGroup.mapOfEq
    ⟨A.centralFamilyCoordinate, A.centralFamilyCoordinate_continuous⟩ (by
      change A.centralFamilyCoordinate
        (A.centralZeroSection A.markedPuncturedBasepoint) = _
      rw [A.centralFamilyCoordinate_zeroSection]
      simp [PaperAnalyticData.markedPuncturedBasepoint])

public theorem markedCentralBaseProjection_zero
    (A : PaperAnalyticData) :
    markedCentralBaseProjection A A.markedZeroCentralMeridianClass =
      TwicePuncturedComplex.zeroMeridianClass := by
  rw [A.markedZeroCentralMeridianClass_eq_pathLoopClass]
  unfold markedCentralBaseProjection
  rw [FundamentalGroup.mapOfEq_apply]
  unfold PaperAnalyticData.markedZeroCentralMeridian
    PaperAnalyticData.markedZeroBaseMeridian
    TwicePuncturedComplex.zeroMeridianClass
  rw [← Path.Homotopic.Quotient.mk_map]
  apply congrArg Path.Homotopic.Quotient.mk
  apply Path.ext
  funext t
  rw [Path.cast_coe]
  change A.centralFamilyCoordinate
      (A.centralZeroSection
        (A.puncturedBaseHomeomorphTwicePuncturedComplex.symm
          (twicePuncturedClockwiseZeroMeridian t))) =
    twicePuncturedClockwiseZeroMeridian t
  rw [A.centralFamilyCoordinate_zeroSection]
  exact A.puncturedBaseHomeomorphTwicePuncturedComplex.apply_symm_apply _

public theorem markedCentralBaseProjection_one
    (A : PaperAnalyticData) :
    markedCentralBaseProjection A A.markedOneCentralMeridianClass =
      TwicePuncturedComplex.oneMeridianClass := by
  rw [A.markedOneCentralMeridianClass_eq_pathLoopClass]
  unfold markedCentralBaseProjection
  rw [FundamentalGroup.mapOfEq_apply]
  unfold PaperAnalyticData.markedOneCentralMeridian
    PaperAnalyticData.markedOneBaseMeridian
    TwicePuncturedComplex.oneMeridianClass
  rw [← Path.Homotopic.Quotient.mk_map]
  apply congrArg Path.Homotopic.Quotient.mk
  apply Path.ext
  funext t
  rw [Path.cast_coe]
  change A.centralFamilyCoordinate
      (A.centralZeroSection
        (A.puncturedBaseHomeomorphTwicePuncturedComplex.symm
          (twicePuncturedClockwiseOneMeridian t))) =
    twicePuncturedClockwiseOneMeridian t
  rw [A.centralFamilyCoordinate_zeroSection]
  exact A.puncturedBaseHomeomorphTwicePuncturedComplex.apply_symm_apply _

private theorem centralFamilyCoordinate_periodLoop
    (A : PaperAnalyticData) (a : Lattice) (t : unitInterval) :
    A.centralFamilyCoordinate
      (regularFamilyQuotientMap A.periods
        (regularFamilyPeriodLoop A.periods
          (A.markedRegularBaseLift, (0 : ComplexTwoSpace)) a t)) =
      twicePuncturedComplexBasepoint := by
  rw [regularFamilyPeriodLoop_apply]
  change A.centralFamilyCoordinate
      (A.centralQuotientProjection
        (regularFamilyCoverProjection A.periods
          (regularFamilyPeriodLiftPath A.periods
            (A.markedRegularBaseLift, 0) a t))) = _
  rw [A.centralFamilyCoordinate_centralQuotientProjection]
  change A.regularCoordinate A.markedRegularBaseLift =
    twicePuncturedComplexBasepoint
  exact A.markedRegularBaseLift_coordinate

public theorem markedCentralBaseProjection_translation
    (A : PaperAnalyticData) (a : Lattice) :
    markedCentralBaseProjection A
        (Additive.toMul (A.markedCentralTranslation a)) = 1 := by
  unfold PaperAnalyticData.markedCentralTranslation
  simp only [AddMonoidHom.comp_apply, MonoidHom.coe_toAdditive,
    Function.comp_apply, toMul_ofMul]
  unfold PaperAnalyticData.markedCentralBaseEquiv
  change markedCentralBaseProjection A
      (SphereSixComplex.Topology.fundamentalGroupMulEquivOfEq _
        (Additive.toMul (centralTranslationAtZero A.periods
          A.markedRegularBaseLift a))) = 1
  rw [SphereSixComplex.Topology.fundamentalGroupMulEquivOfEq_apply]
  unfold markedCentralBaseProjection
  rw [FundamentalGroup.mapOfEq_apply]
  unfold centralTranslationAtZero
  simp only [AddMonoidHom.comp_apply, MonoidHom.coe_toAdditive,
    Function.comp_apply, toMul_ofMul]
  rw [FundamentalGroup.map_apply]
  rw [regularFamilyTranslationAtZero_apply_eq_periodLoop]
  simp only [← Path.Homotopic.Quotient.mk_map]
  apply Path.Homotopic.Quotient.eq.mpr
  exact ⟨{
    toFun := fun _ ↦ twicePuncturedComplexBasepoint
    continuous_toFun := continuous_const
    map_zero_left := fun t ↦ (centralFamilyCoordinate_periodLoop A a t).symm
    map_one_left := by intro t; rfl
    prop' := fun _ t _ ↦ (centralFamilyCoordinate_periodLoop A a t).symm
  }⟩

/-- The actual central-family projection to the free group on the two marked base meridians. -/
public noncomputable def paperPuncturedGlobalFamilyBaseProjection
    (A : PaperAnalyticData) :
    FundamentalGroup A.CentralFamily A.actualCuspCentralBase →*
      TwoMeridianDeckGroup :=
  (TwicePuncturedComplex.markedMeridianMulEquiv
      TwicePuncturedComplex.establishedMarkedMeridianHom_injective).symm.toMonoidHom.comp
    ((markedCentralBaseProjection A).comp
      A.markedCentralToActualCuspEquiv.symm.toMonoidHom)

public theorem paperPuncturedGlobalFamilyBaseProjection_rhoOne
    (A : PaperAnalyticData) :
    paperPuncturedGlobalFamilyBaseProjection A A.geometricCentralRhoOne =
      firstMeridian⁻¹ := by
  unfold paperPuncturedGlobalFamilyBaseProjection
    PaperAnalyticData.geometricCentralRhoOne
  simp only [MonoidHom.comp_apply]
  change (TwicePuncturedComplex.markedMeridianMulEquiv
      TwicePuncturedComplex.establishedMarkedMeridianHom_injective).symm
    (markedCentralBaseProjection A
      (A.markedCentralToActualCuspEquiv.symm
        (A.markedCentralToActualCuspEquiv
          A.markedZeroCentralMeridianClass⁻¹))) = firstMeridian⁻¹
  rw [A.markedCentralToActualCuspEquiv.symm_apply_apply,
    map_inv, markedCentralBaseProjection_zero, map_inv]
  apply congrArg Inv.inv
  exact (TwicePuncturedComplex.markedMeridianMulEquiv
    TwicePuncturedComplex.establishedMarkedMeridianHom_injective).symm_apply_eq.mpr
      TwicePuncturedComplex.markedMeridianHom_first.symm

public theorem paperPuncturedGlobalFamilyBaseProjection_rhoTwo
    (A : PaperAnalyticData) :
    paperPuncturedGlobalFamilyBaseProjection A A.geometricCentralRhoTwo =
      secondMeridian⁻¹ := by
  unfold paperPuncturedGlobalFamilyBaseProjection
    PaperAnalyticData.geometricCentralRhoTwo
  simp only [MonoidHom.comp_apply]
  change (TwicePuncturedComplex.markedMeridianMulEquiv
      TwicePuncturedComplex.establishedMarkedMeridianHom_injective).symm
    (markedCentralBaseProjection A
      (A.markedCentralToActualCuspEquiv.symm
        (A.markedCentralToActualCuspEquiv
          A.markedOneCentralMeridianClass⁻¹))) = secondMeridian⁻¹
  rw [A.markedCentralToActualCuspEquiv.symm_apply_apply,
    map_inv, markedCentralBaseProjection_one, map_inv]
  apply congrArg Inv.inv
  exact (TwicePuncturedComplex.markedMeridianMulEquiv
    TwicePuncturedComplex.establishedMarkedMeridianHom_injective).symm_apply_eq.mpr
      TwicePuncturedComplex.markedMeridianHom_second.symm

public theorem paperPuncturedGlobalFamilyBaseProjection_translation
    (A : PaperAnalyticData) (a : Lattice) :
    paperPuncturedGlobalFamilyBaseProjection A
        (Additive.toMul (A.correctedActualCuspCentralTranslation a)) = 1 := by
  have hm : Additive.toMul (A.correctedActualCuspCentralTranslation a) ∈
      Set.range (fun b ↦ Additive.toMul (A.geometricCentralTranslation b)) := by
    rw [A.geometricCentralTranslation_range_eq_actualCuspCentralTranslation,
      ← A.correctedActualCuspCentralTranslation_range_eq_actual]
    exact ⟨a, rfl⟩
  obtain ⟨b, hb⟩ := hm
  rw [← hb]
  unfold paperPuncturedGlobalFamilyBaseProjection
    PaperAnalyticData.geometricCentralTranslation
  simp only [MonoidHom.comp_apply, AddMonoidHom.comp_apply,
    MonoidHom.coe_toAdditive, Function.comp_apply, toMul_ofMul]
  change (TwicePuncturedComplex.markedMeridianMulEquiv
      TwicePuncturedComplex.establishedMarkedMeridianHom_injective).symm
    (markedCentralBaseProjection A
      (A.markedCentralToActualCuspEquiv.symm
        (A.markedCentralToActualCuspEquiv
          (Additive.toMul (A.markedCentralTranslation b))))) = 1
  rw [A.markedCentralToActualCuspEquiv.symm_apply_apply,
    markedCentralBaseProjection_translation, map_one]

/-- Generator-wise inversion of the free two-meridian group. -/
public def freeMeridianInversion : TwoMeridianDeckGroup →* TwoMeridianDeckGroup :=
  FreeGroup.lift fun i ↦ (FreeGroup.of i)⁻¹

@[simp]
public theorem freeMeridianInversion_of (i : Fin 2) :
    freeMeridianInversion (FreeGroup.of i) = (FreeGroup.of i)⁻¹ := by
  simp [freeMeridianInversion]

public theorem freeMeridianInversion_involutive (g : TwoMeridianDeckGroup) :
    freeMeridianInversion (freeMeridianInversion g) = g := by
  induction g using FreeGroup.induction_on with
  | C1 => simp
  | of i => simp
  | inv_of i hi => simp
  | mul g h hg hh => simp [hg, hh]

public theorem freeMeridianInversion_injective :
    Function.Injective freeMeridianInversion := by
  intro g h hgh
  have := congrArg freeMeridianInversion hgh
  simpa only [freeMeridianInversion_involutive] using this

/-- The canonical affine presentation map determined by the geometric period loops and the two
marked meridians. -/
public noncomputable def paperPuncturedGlobalFamilyAffinePresentation
    (A : PaperAnalyticData) :
    FreeTwoMeridianAffineDeck Lattice paperPuncturedGlobalFamilyFreeMonodromy →*
      FundamentalGroup A.CentralFamily A.actualCuspCentralBase :=
  AffineTorusCorePiOneData.freeAffinePresentationHom
    paperPuncturedGlobalFamilyFreeMonodromy
    (paperPuncturedGlobalFamilyAffineCorePiOneData A)

public theorem paperPuncturedGlobalFamilyBaseProjection_freeMeridianHom
    (A : PaperAnalyticData) :
    (paperPuncturedGlobalFamilyBaseProjection A).comp
      (AffineTorusCorePiOneData.freeMeridianHom
        paperPuncturedGlobalFamilyFreeMonodromy
        (paperPuncturedGlobalFamilyAffineCorePiOneData A)) =
      freeMeridianInversion := by
  ext i
  fin_cases i
  · simp [AffineTorusCorePiOneData.freeMeridianHom,
      paperPuncturedGlobalFamilyAffineCorePiOneData,
      firstMeridian, paperPuncturedGlobalFamilyBaseProjection_rhoOne]
  · simp [AffineTorusCorePiOneData.freeMeridianHom,
      paperPuncturedGlobalFamilyAffineCorePiOneData,
      secondMeridian, paperPuncturedGlobalFamilyBaseProjection_rhoTwo]

public theorem paperPuncturedGlobalFamilyBaseProjection_presentation
    (A : PaperAnalyticData)
    (d : FreeTwoMeridianAffineDeck Lattice
      paperPuncturedGlobalFamilyFreeMonodromy) :
    paperPuncturedGlobalFamilyBaseProjection A
        (paperPuncturedGlobalFamilyAffinePresentation A d) =
      freeMeridianInversion d.right := by
  rw [← SemidirectProduct.inl_left_mul_inr_right d]
  rw [map_mul, map_mul]
  unfold paperPuncturedGlobalFamilyAffinePresentation
  rw [AffineTorusCorePiOneData.freeAffinePresentationHom_inl,
    AffineTorusCorePiOneData.freeAffinePresentationHom_inr]
  change paperPuncturedGlobalFamilyBaseProjection A
      (Additive.toMul
        (A.correctedActualCuspCentralTranslation d.left.toAdd)) *
    paperPuncturedGlobalFamilyBaseProjection A
      (AffineTorusCorePiOneData.freeMeridianHom
        paperPuncturedGlobalFamilyFreeMonodromy
        (paperPuncturedGlobalFamilyAffineCorePiOneData A) d.right) = _
  rw [paperPuncturedGlobalFamilyBaseProjection_translation, one_mul]
  simpa using DFunLike.congr_fun
    (paperPuncturedGlobalFamilyBaseProjection_freeMeridianHom A) d.right

/-- The canonical affine presentation is injective.  Its free component is recovered by the
ordinary base projection, while its lattice component is faithful by the two explicit quotient
coverings. -/
public theorem paperPuncturedGlobalFamilyAffinePresentation_injective
    (A : PaperAnalyticData) :
    Function.Injective (paperPuncturedGlobalFamilyAffinePresentation A) := by
  intro d e hde
  have hright : d.right = e.right := by
    apply freeMeridianInversion_injective
    rw [← paperPuncturedGlobalFamilyBaseProjection_presentation A d,
      ← paperPuncturedGlobalFamilyBaseProjection_presentation A e]
    exact congrArg (paperPuncturedGlobalFamilyBaseProjection A) hde
  apply SemidirectProduct.ext
  · rw [← SemidirectProduct.inl_left_mul_inr_right d,
      ← SemidirectProduct.inl_left_mul_inr_right e,
      map_mul, map_mul] at hde
    unfold paperPuncturedGlobalFamilyAffinePresentation at hde
    rw [AffineTorusCorePiOneData.freeAffinePresentationHom_inl,
      AffineTorusCorePiOneData.freeAffinePresentationHom_inr,
      AffineTorusCorePiOneData.freeAffinePresentationHom_inl,
      AffineTorusCorePiOneData.freeAffinePresentationHom_inr] at hde
    change Additive.toMul
        (A.correctedActualCuspCentralTranslation d.left.toAdd) *
        AffineTorusCorePiOneData.freeMeridianHom
          paperPuncturedGlobalFamilyFreeMonodromy
          (paperPuncturedGlobalFamilyAffineCorePiOneData A) d.right =
      Additive.toMul
        (A.correctedActualCuspCentralTranslation e.left.toAdd) *
        AffineTorusCorePiOneData.freeMeridianHom
          paperPuncturedGlobalFamilyFreeMonodromy
          (paperPuncturedGlobalFamilyAffineCorePiOneData A) e.right at hde
    rw [hright] at hde
    apply Multiplicative.toAdd.injective
    apply correctedActualCuspCentralTranslation_injective A
    apply Additive.toMul.injective
    exact mul_right_cancel hde
  · exact hright

/-- The paper's punctured-family affine fundamental-group classification, derived from the
canonical presentation and its proved injectivity. -/
public noncomputable def establishedPuncturedGlobalFamilyAffineFundamentalGroup
    (A : PaperAnalyticData) :
    PuncturedGlobalFamilyAffineFundamentalGroup A.periods where
  base := A.actualCuspCentralBase
  identification := MulEquiv.ofBijective (paperPuncturedGlobalFamilyAffinePresentation A)
    ⟨paperPuncturedGlobalFamilyAffinePresentation_injective A,
      AffineTorusCorePiOneData.freeAffinePresentationHom_surjective
        paperPuncturedGlobalFamilyFreeMonodromy
        (paperPuncturedGlobalFamilyAffineCorePiOneData A)⟩

/-- The equivariant universal-cover classification for a punctured Fuchsian affine torus family.

This is now a theorem: the affine fundamental-group identification above is transported onto
Tau Ceti's based-path universal cover, which is simply connected and whose fundamental-group
action is a quotient covering map.  The conclusion supplies only the universal cover and its
affine deck action. -/
public noncomputable def establishedPuncturedGlobalFamilyEquivariantUniversalCover
    (A : PaperAnalyticData) :
    ChosenEquivariantAffineUniversalCover IntegerPeriods Delta A.CentralFamily
      (twoMeridianOrbifoldMap g₁ g₂) integralOrbifoldPeriodMonodromy :=
  letI := fuchsianPuncturedGlobalFamily_locallyPathConnected A.modular.modularParameter A.periods
  letI := fuchsianPuncturedGlobalFamily_pathConnected A.modular.modularParameter A.periods
  letI := fuchsianPuncturedGlobalFamily_semilocallySimplyConnected
    A.modular.modularParameter A.periods
  puncturedGlobalFamilyEquivariantUniversalCover_of_fundamentalGroup A.periods
    (establishedPuncturedGlobalFamilyAffineFundamentalGroup A)

end Geometry.GlobalTorusFamily

end SphereSixComplex

end
