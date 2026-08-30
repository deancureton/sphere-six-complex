module

public import SphereSixComplex.Periods.Uniformization.EstablishedExactFuchsianOrbifoldCoordinate
public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Continuous descent through the exact Fuchsian quotient

An invariant continuous function on the upper half-plane is constant on the exact orbit fibres.
The quotient-map field of `ExactFuchsianOrbifoldCoordinate` therefore descends it uniquely to the
affine quotient coordinate.
-/

noncomputable section

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup

/-- The exact quotient coordinate as a bundled continuous map. -/
@[expose] public def ExactFuchsianOrbifoldCoordinate.continuousCoordinate
    (C : ExactFuchsianOrbifoldCoordinate) : C(UpperHalfPlane, ℂ) :=
  ⟨C.coordinate, C.coordinate_holomorphic.continuous⟩

/-- The bundled exact quotient coordinate is a quotient map. -/
public theorem ExactFuchsianOrbifoldCoordinate.continuousCoordinate_isQuotientMap
    (C : ExactFuchsianOrbifoldCoordinate) :
    Topology.IsQuotientMap C.continuousCoordinate :=
  C.coordinate_isQuotientMap

/-- The continuous function on the affine quotient induced by an invariant continuous function
on the source upper half-plane. -/
@[expose] public noncomputable def ExactFuchsianOrbifoldCoordinate.descendInvariantContinuous
    (C : ExactFuchsianOrbifoldCoordinate) (f : UpperHalfPlane → ℂ)
    (hf : Continuous f)
    (hinvariant : ∀ g z, f (fuchsianSourceAction g • z) = f z) :
    C(ℂ, ℂ) :=
  C.continuousCoordinate_isQuotientMap.lift ⟨f, hf⟩
    (show Function.FactorsThrough f C.continuousCoordinate from by
      intro z w hzw
      obtain ⟨g, rfl⟩ := (C.coordinate_eq_iff_orbit z w).mp hzw
      exact (hinvariant g z).symm)

/-- Pulling the descended function back by the quotient coordinate recovers the original
invariant function. -/
public theorem ExactFuchsianOrbifoldCoordinate.descendInvariantContinuous_comp
    (C : ExactFuchsianOrbifoldCoordinate) (f : UpperHalfPlane → ℂ)
    (hf : Continuous f)
    (hinvariant : ∀ g z, f (fuchsianSourceAction g • z) = f z) (z : UpperHalfPlane) :
    C.descendInvariantContinuous f hf hinvariant (C.coordinate z) = f z := by
  have hfactor : Function.FactorsThrough f C.continuousCoordinate := by
    intro x y hxy
    obtain ⟨g, rfl⟩ := (C.coordinate_eq_iff_orbit x y).mp hxy
    exact (hinvariant g x).symm
  have hcomp := C.continuousCoordinate_isQuotientMap.lift_comp ⟨f, hf⟩ hfactor
  exact ContinuousMap.congr_fun hcomp z

/-- The continuous descent is the unique function with the prescribed pullback. -/
public theorem ExactFuchsianOrbifoldCoordinate.descendInvariantContinuous_unique
    (C : ExactFuchsianOrbifoldCoordinate) (f : UpperHalfPlane → ℂ)
    (hf : Continuous f)
    (hinvariant : ∀ g z, f (fuchsianSourceAction g • z) = f z)
    (F : ℂ → ℂ) (hF : ∀ z, F (C.coordinate z) = f z) :
    F = C.descendInvariantContinuous f hf hinvariant := by
  funext q
  obtain ⟨z, rfl⟩ := C.coordinate_isQuotientMap.surjective q
  rw [hF, C.descendInvariantContinuous_comp]

end SphereSixComplex.Periods
