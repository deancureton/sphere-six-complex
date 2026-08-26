module

public import Mathlib.Topology.Homotopy.Lifting
public import SphereSixComplex.Geometry.EquivariantQuotientHomeomorph

/-!
# Equivariance of covering-space homotopy lifts

Uniqueness of lifts makes the homotopy lift of invariant base data equivariant.  This is the
covering-space mechanism behind the lifted affine radial deformation.
-/

@[expose] public section

noncomputable section

open scoped ContinuousMap

namespace SphereSixComplex

open Geometry.EquivariantQuotientHomeomorph

universe u v w

variable {G : Type*} [Group G]
variable {E : Type u} {X : Type v} {B : Type w}
  [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace B]

/-- A covering homotopy lift is equivariant when its projection and initial lift are equivariant
and the base homotopy is invariant. -/
public theorem IsCoveringMap.liftHomotopy_equivariant
    (totalAction : MulAction G E) (parameterAction : MulAction G B)
    (totalContinuous : letI := totalAction; ContinuousConstSMul G E)
    {p : E → X} (cov : IsCoveringMap p)
    (p_invariant : ∀ g e, p (actionMap totalAction g e) = p e)
    (H : C(unitInterval × B, X)) (f : C(B, E))
    (H0 : ∀ b, H (0, b) = p (f b))
    (H_invariant : ∀ g t b,
      H (t, actionMap parameterAction g b) = H (t, b))
    (f_equivariant : ∀ g b, f (actionMap parameterAction g b) =
      actionMap totalAction g (f b)) :
    ∀ g t b, cov.liftHomotopy H f H0 (t, actionMap parameterAction g b) =
      actionMap totalAction g (cov.liftHomotopy H f H0 (t, b)) := by
  intro g t b
  let _ := totalAction
  let _ : ContinuousConstSMul G E := totalContinuous
  let left : unitInterval → E :=
    fun s ↦ cov.liftHomotopy H f H0 (s, actionMap parameterAction g b)
  let right : unitInterval → E :=
    fun s ↦ actionMap totalAction g (cov.liftHomotopy H f H0 (s, b))
  have hleft : Continuous left :=
    (cov.liftHomotopy H f H0).continuous.comp
      (continuous_id.prodMk continuous_const)
  have hright : Continuous right :=
    (continuous_const_smul g).comp
      ((cov.liftHomotopy H f H0).continuous.comp
        (continuous_id.prodMk continuous_const))
  have hcomp : p ∘ left = p ∘ right := by
    funext s
    change p (cov.liftHomotopy H f H0
      (s, actionMap parameterAction g b)) =
        p (actionMap totalAction g (cov.liftHomotopy H f H0 (s, b)))
    rw [p_invariant]
    rw [show p (cov.liftHomotopy H f H0
      (s, actionMap parameterAction g b)) =
        H (s, actionMap parameterAction g b) from
      congr_fun (cov.liftHomotopy_lifts H f H0) _]
    rw [show p (cov.liftHomotopy H f H0 (s, b)) = H (s, b) from
      congr_fun (cov.liftHomotopy_lifts H f H0) _]
    exact H_invariant g s b
  have hzero : left 0 = right 0 := by
    change cov.liftHomotopy H f H0
      (0, actionMap parameterAction g b) =
        actionMap totalAction g (cov.liftHomotopy H f H0 (0, b))
    rw [cov.liftHomotopy_zero H f H0, cov.liftHomotopy_zero H f H0,
      f_equivariant]
  have heq : left = right := cov.eq_of_comp_eq hleft hright hcomp 0 hzero
  exact congr_fun heq t

end SphereSixComplex
