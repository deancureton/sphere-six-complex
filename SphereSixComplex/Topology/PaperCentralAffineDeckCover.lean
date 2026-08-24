module

public import SphereSixComplex.Geometry.PaperCentralFamilyTopology
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# The affine intermediate cover of the paper's central family

The varying period lattice and the triangle group combine into a semidirect product acting on
the regular vector-bundle cover.  Its orbit relation is exactly the fibre relation of the
two-stage projection to the central family.  The domain still has the punctured regular base, so
this is an intermediate regular cover rather than the simply connected cover.
-/

@[expose] public section

open Topology

namespace SphereSixComplex.Geometry.GlobalTorusFamily

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.ComplexTorus SphereSixComplex.Geometry.TorusFamily

noncomputable section

/-- Integral monodromy on the multiplicative period lattice. -/
public def regularPeriodMonodromy :
    Delta →* MulAut (Multiplicative IntegerPeriods) where
  toFun g := (rhoLambda g).toAddEquiv.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro a
    apply Multiplicative.toAdd.injective
    rw [map_one]
    rfl
  map_mul' g h := by
    apply MulEquiv.ext
    intro a
    apply Multiplicative.toAdd.injective
    change rhoLambda (g * h) a.toAdd = rhoLambda g (rhoLambda h a.toAdd)
    rw [map_mul]
    rfl

/-- The split affine extension of the triangle group by the integral period lattice. -/
public abbrev CentralIntermediateDeckGroup :=
  (Multiplicative IntegerPeriods) ⋊[regularPeriodMonodromy] Delta

/-- Regard an untagged period-lattice element as an element of a specified family-period group. -/
public def asRegularFamilyPeriod {U : TriangleUniformization}
    (F : PeriodFunctions U) (a : Multiplicative IntegerPeriods) :
    FamilyPeriodGroup (regularParameterMap F) :=
  a

variable {U : TriangleUniformization}

/-- The combined affine action before either the lattice or triangle-group quotient is taken. -/
@[instance_reducible] public noncomputable def centralIntermediateDeckAction
    (F : PeriodFunctions U) :
    MulAction CentralIntermediateDeckGroup
      (RegularBase (U := U) × ComplexTwoSpace) where
  smul d p := asRegularFamilyPeriod F d.left • regularDeckMap F d.right p
  one_smul p := by
    change (1 : FamilyPeriodGroup (regularParameterMap F)) • regularDeckMap F 1 p = p
    rw [regularDeckMap_one, one_smul]
  mul_smul d e p := by
    change asRegularFamilyPeriod F (d.left * regularPeriodMonodromy d.right e.left) •
        regularDeckMap F (d.right * e.right) p =
      asRegularFamilyPeriod F d.left •
        regularDeckMap F d.right
          (asRegularFamilyPeriod F e.left • regularDeckMap F e.right p)
    rw [regularDeckMap_mul, regularDeckMap_family_smul]
    change (asRegularFamilyPeriod F d.left *
        transportRegularFamilyPeriod F d.right (asRegularFamilyPeriod F e.left)) •
        regularDeckMap F d.right (regularDeckMap F e.right p) =
      asRegularFamilyPeriod F d.left •
        transportRegularFamilyPeriod F d.right (asRegularFamilyPeriod F e.left) •
          regularDeckMap F d.right (regularDeckMap F e.right p)
    rw [mul_smul]

/-- The lattice subgroup in the affine deck group. -/
public def centralIntermediateTranslation :
    IntegerPeriods →+ Additive CentralIntermediateDeckGroup where
  toFun a := Additive.ofMul
    (SemidirectProduct.inl (φ := regularPeriodMonodromy) (Multiplicative.ofAdd a))
  map_zero' := by
    apply Additive.toMul.injective
    change SemidirectProduct.inl (φ := regularPeriodMonodromy)
      (Multiplicative.ofAdd 0) = 1
    exact (SemidirectProduct.inl (φ := regularPeriodMonodromy)).map_one
  map_add' a b := by
    apply Additive.toMul.injective
    change SemidirectProduct.inl (φ := regularPeriodMonodromy)
        (Multiplicative.ofAdd (a + b)) =
      SemidirectProduct.inl (Multiplicative.ofAdd a) *
        SemidirectProduct.inl (Multiplicative.ofAdd b)
    exact (SemidirectProduct.inl (φ := regularPeriodMonodromy)).map_mul
      (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)

/-- The lattice subgroup embeds in the affine deck group. -/
public theorem centralIntermediateTranslation_injective :
    Function.Injective centralIntermediateTranslation := by
  intro a b h
  have h' := congrArg SemidirectProduct.left (congrArg Additive.toMul h)
  change Multiplicative.ofAdd a = Multiplicative.ofAdd b at h'
  exact Multiplicative.ofAdd.injective h'

/-- Projection of the affine deck group to the triangle group. -/
public def centralIntermediateBaseProjection : CentralIntermediateDeckGroup →* Delta :=
  SemidirectProduct.rightHom

/-- The canonical splitting by pure triangle-group deck transformations. -/
public def centralIntermediateLift : Delta →* CentralIntermediateDeckGroup :=
  SemidirectProduct.inr

public theorem centralIntermediateBaseProjection_surjective :
    Function.Surjective centralIntermediateBaseProjection :=
  SemidirectProduct.rightHom_surjective

/-- The split lift of the order-three generator still has order three.  It is therefore not the
unwrapped puncture meridian required for the central universal cover. -/
public theorem centralIntermediateLift_gOne_pow_three :
    (centralIntermediateLift g₁) ^ 3 = 1 := by
  rw [← map_pow, g₁_pow_three, map_one]

/-- The split lift of the order-four generator still has order four.  It is therefore not the
unwrapped puncture meridian required for the central universal cover. -/
public theorem centralIntermediateLift_gTwo_pow_four :
    (centralIntermediateLift g₂) ^ 4 = 1 := by
  rw [← map_pow, g₂_pow_four, map_one]

/-- The kernel of the base projection is exactly the period-translation subgroup. -/
public theorem centralIntermediateBaseProjection_ker (d : CentralIntermediateDeckGroup) :
    centralIntermediateBaseProjection d = 1 ↔
      ∃ a, Additive.toMul (centralIntermediateTranslation a) = d := by
  constructor
  · intro h
    refine ⟨d.left.toAdd, ?_⟩
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd d.left.toAdd = d.left
      rfl
    · exact h.symm
  · rintro ⟨a, rfl⟩
    rfl

/-- Conjugation by a lifted triangle-group element is the integral monodromy action. -/
public theorem centralIntermediate_conjugate (g : Delta) (a : IntegerPeriods) :
    centralIntermediateLift g * Additive.toMul (centralIntermediateTranslation a) *
        (centralIntermediateLift g)⁻¹ =
      Additive.toMul (centralIntermediateTranslation (rhoLambda g a)) := by
  symm
  change SemidirectProduct.inl (φ := regularPeriodMonodromy)
      (Multiplicative.ofAdd (rhoLambda g a)) =
    SemidirectProduct.inr g * SemidirectProduct.inl (Multiplicative.ofAdd a) *
      (SemidirectProduct.inr g)⁻¹
  convert SemidirectProduct.inl_aut (φ := regularPeriodMonodromy) g
    (Multiplicative.ofAdd a) using 1
  · change SemidirectProduct.inl (Multiplicative.ofAdd (rhoLambda g a)) =
      SemidirectProduct.inl (regularPeriodMonodromy g (Multiplicative.ofAdd a))
    rfl
  · rw [map_inv]

end

end SphereSixComplex.Geometry.GlobalTorusFamily

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.ComplexTorus SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily

noncomputable section

variable (A : PaperAnalyticData)

/-- The two successive quotient projections, regarded as one affine projection. -/
public noncomputable def centralIntermediateProjection :
    RegularBase (U := A.modular.modularParameter.toTriangleUniformization) × ComplexTwoSpace →
      A.CentralFamily := by
  let _ := regularFamilyDeckAction A.periods
  exact quotientProjection ∘ projection (regularParameterMap A.periods)

/-- The affine projection is a quotient map. -/
public theorem centralIntermediateProjection_isQuotientMap :
    IsQuotientMap A.centralIntermediateProjection := by
  let _ := regularFamilyDeckAction A.periods
  change IsQuotientMap ((Quotient.mk _) ∘ (Quotient.mk _))
  exact isQuotientMap_quotient_mk'.comp isQuotientMap_quotient_mk'

/-- Two points have the same image precisely when they differ by one combined affine deck
transformation. -/
public theorem centralIntermediateProjection_eq_iff
    (p q : RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace) :
    letI := centralIntermediateDeckAction A.periods
    A.centralIntermediateProjection p = A.centralIntermediateProjection q ↔
      ∃ d : CentralIntermediateDeckGroup, d • q = p := by
  let _ := regularFamilyDeckAction A.periods
  let _ := centralIntermediateDeckAction A.periods
  change Quotient.mk _ (Quotient.mk _ p) = Quotient.mk _ (Quotient.mk _ q) ↔ _
  rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    change regularFamilyDeckMap A.periods g (Quotient.mk _ q) = Quotient.mk _ p at hg
    rw [regularFamilyDeckMap_mk] at hg
    rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hg
    obtain ⟨a, ha⟩ := hg
    let a' : Multiplicative IntegerPeriods := a
    refine ⟨⟨a'⁻¹, g⟩, ?_⟩
    change a⁻¹ • regularDeckMap A.periods g q = p
    rw [← ha, inv_smul_smul]
  · rintro ⟨d, hd⟩
    refine ⟨d.right, ?_⟩
    change regularFamilyDeckMap A.periods d.right (Quotient.mk _ q) = Quotient.mk _ p
    rw [regularFamilyDeckMap_mk]
    apply Quotient.sound
    change MulAction.orbitRel (FamilyPeriodGroup (regularParameterMap A.periods)) _
      (regularDeckMap A.periods d.right q) p
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    refine ⟨(asRegularFamilyPeriod A.periods d.left)⁻¹, ?_⟩
    have hd' : asRegularFamilyPeriod A.periods d.left •
        regularDeckMap A.periods d.right q = p := hd
    rw [← hd', inv_smul_smul]

/-- The affine projection is constant on combined deck orbits. -/
public theorem centralIntermediateProjection_smul
    (d : CentralIntermediateDeckGroup)
    (p : RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace) :
    letI := centralIntermediateDeckAction A.periods
    A.centralIntermediateProjection (d • p) = A.centralIntermediateProjection p := by
  let _ := centralIntermediateDeckAction A.periods
  exact (A.centralIntermediateProjection_eq_iff (d • p) p).2 ⟨d, rfl⟩

end

end SphereSixComplex.Geometry.PaperAnalyticData
