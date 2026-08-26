module

public import SphereSixComplex.Geometry.ComplexTorus
public import SphereSixComplex.Periods.Domain
public import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Families of complex tori

This file constructs the fibrewise period action on `B × ℂ²`.  Proper discontinuity of a
varying lattice is recorded by the compact-uniform escape condition which is exactly needed in
the quotient construction.
-/

open scoped Manifold

namespace SphereSixComplex.Geometry.TorusFamily

open SphereSixComplex.Geometry SphereSixComplex.Geometry.ComplexTorus
  SphereSixComplex.Periods

public noncomputable section

variable {B : Type*}

/-- A tagged copy of `ℤ⁴`, used so that the action remembers its period family. -/
@[expose] public def FamilyPeriodGroup (_x : B → PeriodDomain) :=
  Multiplicative IntegerPeriods

public instance (x : B → PeriodDomain) : Group (FamilyPeriodGroup x) :=
  inferInstanceAs (Group (Multiplicative IntegerPeriods))

/-- The integral coefficient underlying a tagged family-period element. -/
@[expose] public def FamilyPeriodGroup.coeff {x : B → PeriodDomain}
    (g : FamilyPeriodGroup x) :
    IntegerPeriods :=
  Multiplicative.toAdd g

@[simp]
public theorem FamilyPeriodGroup.coeff_one (x : B → PeriodDomain) :
    (1 : FamilyPeriodGroup x).coeff = 0 :=
  by rfl

@[simp]
public theorem FamilyPeriodGroup.coeff_mul {x : B → PeriodDomain}
    (g h : FamilyPeriodGroup x) : (g * h).coeff = g.coeff + h.coeff :=
  by rfl

/-- The fibrewise period translation action on the trivial bundle `B × ℂ²`. -/
public instance familySMul (x : B → PeriodDomain) :
    SMul (FamilyPeriodGroup x) (B × ComplexTwoSpace) where
  smul g p := (p.1, periodVector (x p.1).1 g.coeff + p.2)

@[simp]
public theorem family_smul_fst (x : B → PeriodDomain) (g : FamilyPeriodGroup x)
    (p : B × ComplexTwoSpace) : (g • p).1 = p.1 :=
  rfl

@[simp]
public theorem family_smul_snd (x : B → PeriodDomain) (g : FamilyPeriodGroup x)
    (p : B × ComplexTwoSpace) :
    (g • p).2 = periodVector (x p.1).1 g.coeff + p.2 :=
  rfl

public instance familyMulAction (x : B → PeriodDomain) :
    MulAction (FamilyPeriodGroup x) (B × ComplexTwoSpace) where
  one_smul p := by
    apply Prod.ext
    · rfl
    · rw [family_smul_snd, FamilyPeriodGroup.coeff_one]
      rw [periodVector_zero, zero_add]
  mul_smul g h p := by
    apply Prod.ext
    · rfl
    · rw [family_smul_snd, family_smul_snd, family_smul_snd,
        FamilyPeriodGroup.coeff_mul]
      change periodVector (x p.1).1 (g.coeff + h.coeff) + p.2 =
        periodVector (x p.1).1 g.coeff +
          (periodVector (x p.1).1 h.coeff + p.2)
      rw [periodVector_add]
      exact add_assoc _ _ _

/-- Every fibrewise period action is free because every point of the period domain has full
rank. -/
public theorem familyIsCancelSMul (x : B → PeriodDomain) :
    IsCancelSMul (FamilyPeriodGroup x) (B × ComplexTwoSpace) where
  right_cancel' g h p heq := by
    apply Multiplicative.toAdd.injective
    have hsnd := congrArg Prod.snd heq
    rw [family_smul_snd, family_smul_snd] at hsnd
    have hv := add_right_cancel hsnd
    let hfull := FullRank.ofSetupInequalities (x p.1).1 (x p.1).2
    have hr : integerToReal g.coeff = integerToReal h.coeff := hfull.realEquiv.injective <| by
      rw [hfull.map_integer, hfull.map_integer]
      exact hv
    exact integerToReal_injective hr

/-- Continuity of all period sections makes every fibrewise translation continuous. -/
public theorem familyContinuousConstSMul [TopologicalSpace B] (x : B → PeriodDomain)
    (hperiod : ∀ a : IntegerPeriods, Continuous fun b ↦ periodVector (x b).1 a) :
    ContinuousConstSMul (FamilyPeriodGroup x) (B × ComplexTwoSpace) where
  continuous_const_smul g := by
    apply Continuous.prodMk continuous_fst
    exact (hperiod g.coeff).comp continuous_fst |>.add continuous_snd

/-- Compact-uniform properness of a varying period family.  This is the precise finiteness
condition needed for proper discontinuity of the fibrewise action. -/
@[expose] public def CompactlyUniformPeriods [TopologicalSpace B] (x : B → PeriodDomain) : Prop :=
  ∀ {K L : Set (B × ComplexTwoSpace)}, IsCompact K → IsCompact L →
    {g : FamilyPeriodGroup x | ((g • ·) '' K ∩ L).Nonempty}.Finite

/-- Compact-uniform properness supplies the quotient API's properly-discontinuous instance. -/
public theorem familyProperlyDiscontinuousSMul [TopologicalSpace B] (x : B → PeriodDomain)
    (hproper : CompactlyUniformPeriods x) :
    ProperlyDiscontinuousSMul (FamilyPeriodGroup x) (B × ComplexTwoSpace) where
  finite_disjoint_inter_image := hproper

/-- The total space of the family of complex tori. -/
public abbrev TotalSpace (x : B → PeriodDomain) :=
  OrbitQuotient (M := B × ComplexTwoSpace) (G := FamilyPeriodGroup x)

/-- The quotient projection from the trivial vector bundle to the torus family. -/
@[expose] public def projection (x : B → PeriodDomain) :
    B × ComplexTwoSpace → TotalSpace x :=
  quotientProjection

section Smooth

variable {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℂ EB]
  [TopologicalSpace HB] (IB : ModelWithCorners ℂ EB HB)
  [TopologicalSpace B] [ChartedSpace HB B]

/-- Smoothness of all period sections makes every fibrewise period translation smooth. -/
public theorem familyTranslation_contMDiff (x : B → PeriodDomain) (n : WithTop ℕ∞)
    (hperiod : ∀ a : IntegerPeriods,
      ContMDiff IB (modelWithCornersSelf ℂ ComplexTwoSpace) n
        (fun b ↦ periodVector (x b).1 a))
    (g : FamilyPeriodGroup x) :
    ContMDiff (IB.prod (modelWithCornersSelf ℂ ComplexTwoSpace))
      (IB.prod (modelWithCornersSelf ℂ ComplexTwoSpace)) n
      (fun p : B × ComplexTwoSpace ↦ g • p) := by
  apply contMDiff_fst.prodMk
  exact ((hperiod g.coeff).comp contMDiff_fst).add contMDiff_snd

/-- A compact-uniform smooth period family has a complex-manifold total space, and its quotient
projection is a local diffeomorphism. -/
public theorem totalSpace_isManifold_and_projection_isLocalDiffeomorph
    (n : WithTop ℕ∞) [T2Space B] [LocallyCompactSpace B] [IsManifold IB n B]
    (x : B → PeriodDomain)
    (hperiod : ∀ a : IntegerPeriods,
      ContMDiff IB (modelWithCornersSelf ℂ ComplexTwoSpace) n
        (fun b ↦ periodVector (x b).1 a))
    (hproper : CompactlyUniformPeriods x) :
    letI := familyIsCancelSMul x
    letI := familyContinuousConstSMul x fun a ↦ (hperiod a).continuous
    letI := familyProperlyDiscontinuousSMul x hproper
    IsManifold (IB.prod (modelWithCornersSelf ℂ ComplexTwoSpace)) n (TotalSpace x) ∧
      IsLocalDiffeomorph (IB.prod (modelWithCornersSelf ℂ ComplexTwoSpace))
        (IB.prod (modelWithCornersSelf ℂ ComplexTwoSpace)) n (projection x) := by
  let _ := familyIsCancelSMul x
  let _ := familyContinuousConstSMul x fun a ↦ (hperiod a).continuous
  let _ := familyProperlyDiscontinuousSMul x hproper
  let _ : IsManifold (IB.prod (modelWithCornersSelf ℂ ComplexTwoSpace)) n
      (B × ComplexTwoSpace) := IsManifold.prod B ComplexTwoSpace
  exact orbitQuotient_isManifold_and_projection_isLocalDiffeomorph_of_contMDiff_smul
    (IB.prod (modelWithCornersSelf ℂ ComplexTwoSpace)) n
    (familyTranslation_contMDiff IB x n hperiod)

/-- At order one the quotient projection of a compact-uniform holomorphic period family is
locally holomorphic. -/
public theorem totalSpace_isManifold_and_projection_mdifferentiable
    [T2Space B] [LocallyCompactSpace B] [IsManifold IB 1 B]
    (x : B → PeriodDomain)
    (hperiod : ∀ a : IntegerPeriods,
      ContMDiff IB (modelWithCornersSelf ℂ ComplexTwoSpace) 1
        (fun b ↦ periodVector (x b).1 a))
    (hproper : CompactlyUniformPeriods x) :
    letI := familyIsCancelSMul x
    letI := familyContinuousConstSMul x fun a ↦ (hperiod a).continuous
    letI := familyProperlyDiscontinuousSMul x hproper
    IsManifold (IB.prod (modelWithCornersSelf ℂ ComplexTwoSpace)) 1 (TotalSpace x) ∧
      MDifferentiable (IB.prod (modelWithCornersSelf ℂ ComplexTwoSpace))
        (IB.prod (modelWithCornersSelf ℂ ComplexTwoSpace)) (projection x) := by
  let _ := familyIsCancelSMul x
  let _ := familyContinuousConstSMul x fun a ↦ (hperiod a).continuous
  let _ := familyProperlyDiscontinuousSMul x hproper
  let _ : IsManifold (IB.prod (modelWithCornersSelf ℂ ComplexTwoSpace)) 1
      (B × ComplexTwoSpace) := IsManifold.prod B ComplexTwoSpace
  exact orbitQuotient_isManifold_and_projection_mdifferentiable_of_contMDiff_smul
    (IB.prod (modelWithCornersSelf ℂ ComplexTwoSpace))
    (familyTranslation_contMDiff IB x 1 hperiod)

end Smooth

end

end SphereSixComplex.Geometry.TorusFamily
