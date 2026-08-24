module

public import SphereSixComplex.Periods.Uniformization.ExactSourceAssembly
import all SphereSixComplex.Periods.Uniformization.ExactSourceAssembly
public import SphereSixComplex.Periods.Uniformization.ScalarTriangleReflection
import all SphereSixComplex.Periods.Uniformization.ScalarTriangleReflection
public import SphereSixComplex.TriangleGroup.FuchsianTriangleCover
import all SphereSixComplex.TriangleGroup.FuchsianTriangleCover
public import Mathlib.Analysis.Complex.OpenMapping
import all Mathlib.Analysis.Complex.OpenMapping

@[expose] public section

/-!
# Formal assembly of a globally reflected scalar coordinate

The analytic continuation step naturally produces a scalar function on the complex upper
half-plane together with the three Schwarz-reflection identities.  This file discharges two
global obligations formally:

* the three reflection identities imply invariance under every element of `C₃ * C₄`;
* holomorphicity and the distinct normalized values `0` and `1` imply openness by the complex
  open-mapping theorem.

Thus the final Schwarz construction need not carry either group invariance or openness as an
extra field.
-/

open Complex Set Topology UpperHalfPlane
open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

open SphereSixComplex.TriangleGroup
open SphereSixComplex.Periods.TriangleReflections
open SphereSixComplex.Periods.ExactSourceAssembly
open SphereSixComplex.TriangleGroup.FuchsianTriangleCover

/-- Invariance of a scalar function under one element of the source triangle group. -/
def ScalarInvariant (F : ℂ → ℂ) (g : Delta) : Prop :=
  ∀ z : UpperHalfPlane,
    F (((fuchsianSourceAction g • z : UpperHalfPlane) : ℂ)) = F (z : ℂ)

theorem scalarInvariant_one (F : ℂ → ℂ) : ScalarInvariant F 1 := by
  intro z
  simp [ScalarInvariant]

theorem ScalarInvariant.mul {F : ℂ → ℂ} {g h : Delta}
    (hg : ScalarInvariant F g) (hh : ScalarInvariant F h) :
    ScalarInvariant F (g * h) := by
  intro z
  rw [map_mul, mul_smul]
  exact (hg (fuchsianSourceAction h • z)).trans (hh z)

theorem ScalarInvariant.pow {F : ℂ → ℂ} {g : Delta}
    (hg : ScalarInvariant F g) (n : ℕ) : ScalarInvariant F (g ^ n) := by
  induction n with
  | zero => simpa using scalarInvariant_one F
  | succ n ih => simpa [pow_succ] using ih.mul hg

private theorem multiplicativeZMod_eq_generator_pow_scalar {k : ℕ} [NeZero k]
    (x : Multiplicative (ZMod k)) :
    x = Multiplicative.ofAdd (1 : ZMod k) ^ x.toAdd.val := by
  apply Multiplicative.toAdd.injective
  simp

/-- The two generator identities imply invariance under the entire free product. -/
theorem scalarInvariant_all (F : ℂ → ℂ)
    (h₁ : ScalarInvariant F g₁) (h₂ : ScalarInvariant F g₂) :
    ∀ g : Delta, ScalarInvariant F g := by
  intro g
  induction g using Monoid.Coprod.induction_on with
  | inl a =>
      rw [multiplicativeZMod_eq_generator_pow_scalar a, map_pow]
      rw [show Monoid.Coprod.inl (Multiplicative.ofAdd (1 : ZMod 3)) = g₁ by
        exact SphereSixComplex.TriangleGroup.g₁.eq_def.symm]
      exact h₁.pow _
  | inr a =>
      rw [multiplicativeZMod_eq_generator_pow_scalar a, map_pow]
      rw [show Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ZMod 4)) = g₂ by
        exact SphereSixComplex.TriangleGroup.g₂.eq_def.symm]
      exact h₂.pow _
  | mul g h hg hh => exact hg.mul hh

/-- Three global Schwarz-reflection laws imply source-group invariance. -/
theorem scalarInvariant_all_of_reflections (F : ℂ → ℂ)
    (hright : ∀ z : ℂ, F (sourceRight z) = (starRingEnd ℂ) (F z))
    (hcircle : ∀ z : ℂ, F (sourceCircle z) = (starRingEnd ℂ) (F z))
    (hleft : ∀ z : ℂ, F (sourceLeft z) = (starRingEnd ℂ) (F z)) :
    ∀ g : Delta, ScalarInvariant F g := by
  apply scalarInvariant_all F
  · exact invariant_g1_of_scalar_side_reflections F hright hcircle
  · exact invariant_g2_of_scalar_side_reflections F hcircle hleft

/-- Exact fibres on the doubled fundamental region imply exact fibres globally. -/
theorem scalar_eq_iff_orbit_of_fundamental
    (F : ℂ → ℂ) (hinv : ∀ g : Delta, ScalarInvariant F g)
    (hfund : ∀ z w : UpperHalfPlane,
      z ∈ orientedFundamentalRegion → w ∈ orientedFundamentalRegion →
      F (z : ℂ) = F (w : ℂ) →
        ∃ g : Delta, fuchsianSourceAction g • z = w) :
    ∀ z w : UpperHalfPlane,
      F (z : ℂ) = F (w : ℂ) ↔
        ∃ g : Delta, fuchsianSourceAction g • z = w := by
  intro z w
  constructor
  · intro hzw
    obtain ⟨gz, hgz⟩ := exists_smul_mem_orientedFundamentalRegion z
    obtain ⟨gw, hgw⟩ := exists_smul_mem_orientedFundamentalRegion w
    have htranslated :
        F ((fuchsianSourceAction gz • z : UpperHalfPlane) : ℂ) =
          F ((fuchsianSourceAction gw • w : UpperHalfPlane) : ℂ) := by
      rw [hinv gz z, hinv gw w]
      exact hzw
    obtain ⟨k, hk⟩ := hfund _ _ hgz hgw htranslated
    refine ⟨gw⁻¹ * k * gz, ?_⟩
    rw [map_mul, map_mul, mul_smul, mul_smul, hk]
    rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  · rintro ⟨g, rfl⟩
    exact (hinv g z).symm

/-- Surjectivity on the doubled fundamental region implies global surjectivity. -/
theorem scalar_surjective_of_fundamental
    (F : ℂ → ℂ)
    (hfund : ∀ q : ℂ, ∃ z : UpperHalfPlane,
      z ∈ orientedFundamentalRegion ∧ F (z : ℂ) = q) :
    Function.Surjective (fun z : UpperHalfPlane ↦ F (z : ℂ)) := by
  intro q
  obtain ⟨z, -, hz⟩ := hfund q
  exact ⟨z, hz⟩

/-- The scalar upper half-plane, as a subset of `ℂ`. -/
def scalarUpperHalfPlane : Set ℂ := {z | 0 < z.im}

theorem scalarUpperHalfPlane_isOpen : IsOpen scalarUpperHalfPlane := by
  exact isOpen_lt continuous_const Complex.continuous_im

theorem scalarUpperHalfPlane_isPreconnected : IsPreconnected scalarUpperHalfPlane := by
  exact (convex_halfSpace_im_gt 0).isPreconnected

/-- A holomorphic scalar function with two distinct values restricts to an open map on the upper
half-plane. -/
theorem isOpenMap_upperHalfPlane_of_differentiableOn_of_ne
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F scalarUpperHalfPlane)
    (z w : UpperHalfPlane) (hzw : F z ≠ F w) :
    IsOpenMap (fun u : UpperHalfPlane ↦ F (u : ℂ)) := by
  have hAnalytic : AnalyticOnNhd ℂ F scalarUpperHalfPlane :=
    hF.analyticOnNhd scalarUpperHalfPlane_isOpen
  rcases hAnalytic.is_constant_or_isOpen scalarUpperHalfPlane_isPreconnected with
      hconstant | hopen
  · obtain ⟨c, hc⟩ := hconstant
    exact (hzw ((hc z z.im_pos).trans (hc w w.im_pos).symm)).elim
  · intro s hs
    have hcoeOpen : IsOpen (((↑) : UpperHalfPlane → ℂ) '' s) :=
      UpperHalfPlane.isOpenEmbedding_coe.isOpenMap s hs
    have hcoeSub : ((↑) : UpperHalfPlane → ℂ) '' s ⊆ scalarUpperHalfPlane := by
      rintro _ ⟨u, -, rfl⟩
      exact u.im_pos
    have himageOpen := hopen _ hcoeSub hcoeOpen
    convert himageOpen using 1
    ext q
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨(u : ℂ), ⟨u, hu, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨u, hu, rfl⟩

/-- The remaining output of the global Schwarz construction after invariance and openness have
been discharged formally. -/
structure ReflectedScalarCoordinateCore where
  scalar : ℂ → ℂ
  scalar_holomorphic : DifferentiableOn ℂ scalar scalarUpperHalfPlane
  reflection_right : ∀ z, scalar (sourceRight z) = (starRingEnd ℂ) (scalar z)
  reflection_circle : ∀ z, scalar (sourceCircle z) = (starRingEnd ℂ) (scalar z)
  reflection_left : ∀ z, scalar (sourceLeft z) = (starRingEnd ℂ) (scalar z)
  scalar_surjective : Function.Surjective (fun z : UpperHalfPlane ↦ scalar (z : ℂ))
  scalar_eq_iff_orbit : ∀ z w : UpperHalfPlane,
    scalar (z : ℂ) = scalar (w : ℂ) ↔
      ∃ g : Delta, fuchsianSourceAction g • z = w
  scalar_at_one : scalar fuchsianOneFixedPoint = 0
  scalar_at_two : scalar fuchsianTwoFixedPoint = 1
  regular_localHomeomorph :
    IsLocalHomeomorph
      (sourceRegularValueSet.restrictPreimage
        (fun z : UpperHalfPlane ↦ scalar (z : ℂ)))
  branch_one : HasExactHolomorphicBranchAt
    (fun z : UpperHalfPlane ↦ scalar (z : ℂ)) fuchsianOneFixedPoint 0 3
  branch_two : HasExactHolomorphicBranchAt
    (fun z : UpperHalfPlane ↦ scalar (z : ℂ)) fuchsianTwoFixedPoint 1 4
  cusp : HasExactFuchsianCusp
    { coordinate := fun z : UpperHalfPlane ↦ scalar (z : ℂ)
      coordinate_holomorphic := by
        rw [UpperHalfPlane.mdifferentiable_iff]
        exact scalar_holomorphic.congr fun z hz ↦ by
          simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
      coordinate_invariant := by
        intro g z
        exact scalarInvariant_all_of_reflections scalar reflection_right reflection_circle
          reflection_left g z }

namespace ReflectedScalarCoordinateCore

variable (K : ReflectedScalarCoordinateCore)

/-- Assemble the reduced exact-source core from a globally reflected scalar function. -/
def toSourceCoordinateCore : SourceCoordinateCore where
  coordinate := fun z ↦ K.scalar (z : ℂ)
  coordinate_holomorphic := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    exact K.scalar_holomorphic.congr fun z hz ↦ by
      simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  coordinate_invariant := by
    intro g z
    exact scalarInvariant_all_of_reflections K.scalar K.reflection_right K.reflection_circle
      K.reflection_left g z
  coordinate_surjective := K.scalar_surjective
  coordinate_isOpenMap := by
    apply isOpenMap_upperHalfPlane_of_differentiableOn_of_ne K.scalar K.scalar_holomorphic
      fuchsianOneFixedPoint fuchsianTwoFixedPoint
    rw [K.scalar_at_one, K.scalar_at_two]
    norm_num
  coordinate_eq_iff_orbit := K.scalar_eq_iff_orbit
  coordinate_at_one := K.scalar_at_one
  coordinate_at_two := K.scalar_at_two
  regular_localHomeomorph := K.regular_localHomeomorph
  branch_one := K.branch_one
  branch_two := K.branch_two
  cusp := K.cusp

/-- The final exact source coordinate obtained from the global scalar-reflection package. -/
def toExactFuchsianOrbifoldCoordinate : ExactFuchsianOrbifoldCoordinate :=
  K.toSourceCoordinateCore.toExactFuchsianOrbifoldCoordinate


end ReflectedScalarCoordinateCore

/-- A still more local assembly interface: surjectivity and fibre separation need only be checked
on the doubled orientation-preserving fundamental region. -/
structure ReflectedScalarFundamentalCore where
  scalar : ℂ → ℂ
  scalar_holomorphic : DifferentiableOn ℂ scalar scalarUpperHalfPlane
  reflection_right : ∀ z, scalar (sourceRight z) = (starRingEnd ℂ) (scalar z)
  reflection_circle : ∀ z, scalar (sourceCircle z) = (starRingEnd ℂ) (scalar z)
  reflection_left : ∀ z, scalar (sourceLeft z) = (starRingEnd ℂ) (scalar z)
  fundamental_surjective : ∀ q : ℂ, ∃ z : UpperHalfPlane,
    z ∈ orientedFundamentalRegion ∧ scalar (z : ℂ) = q
  fundamental_fibres : ∀ z w : UpperHalfPlane,
    z ∈ orientedFundamentalRegion → w ∈ orientedFundamentalRegion →
    scalar (z : ℂ) = scalar (w : ℂ) →
      ∃ g : Delta, fuchsianSourceAction g • z = w
  scalar_at_one : scalar fuchsianOneFixedPoint = 0
  scalar_at_two : scalar fuchsianTwoFixedPoint = 1
  regular_localHomeomorph :
    IsLocalHomeomorph
      (sourceRegularValueSet.restrictPreimage
        (fun z : UpperHalfPlane ↦ scalar (z : ℂ)))
  branch_one : HasExactHolomorphicBranchAt
    (fun z : UpperHalfPlane ↦ scalar (z : ℂ)) fuchsianOneFixedPoint 0 3
  branch_two : HasExactHolomorphicBranchAt
    (fun z : UpperHalfPlane ↦ scalar (z : ℂ)) fuchsianTwoFixedPoint 1 4
  cusp : HasExactFuchsianCusp
    { coordinate := fun z : UpperHalfPlane ↦ scalar (z : ℂ)
      coordinate_holomorphic := by
        rw [UpperHalfPlane.mdifferentiable_iff]
        exact scalar_holomorphic.congr fun z hz ↦ by
          simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
      coordinate_invariant := by
        intro g z
        exact scalarInvariant_all_of_reflections scalar reflection_right reflection_circle
          reflection_left g z }

namespace ReflectedScalarFundamentalCore

variable (K : ReflectedScalarFundamentalCore)

def toReflectedScalarCoordinateCore : ReflectedScalarCoordinateCore where
  scalar := K.scalar
  scalar_holomorphic := K.scalar_holomorphic
  reflection_right := K.reflection_right
  reflection_circle := K.reflection_circle
  reflection_left := K.reflection_left
  scalar_surjective := scalar_surjective_of_fundamental K.scalar K.fundamental_surjective
  scalar_eq_iff_orbit := by
    apply scalar_eq_iff_orbit_of_fundamental K.scalar
      (scalarInvariant_all_of_reflections K.scalar K.reflection_right K.reflection_circle
        K.reflection_left)
    exact K.fundamental_fibres
  scalar_at_one := K.scalar_at_one
  scalar_at_two := K.scalar_at_two
  regular_localHomeomorph := K.regular_localHomeomorph
  branch_one := K.branch_one
  branch_two := K.branch_two
  cusp := K.cusp

def toExactFuchsianOrbifoldCoordinate : ExactFuchsianOrbifoldCoordinate :=
  K.toReflectedScalarCoordinateCore.toExactFuchsianOrbifoldCoordinate


end ReflectedScalarFundamentalCore

end SphereSixComplex.Periods.SourceChamberTopology
