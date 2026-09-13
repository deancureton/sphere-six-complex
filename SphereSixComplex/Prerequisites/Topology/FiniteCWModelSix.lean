module

public import SphereSixComplex.Prerequisites.Topology.IntegralHomologyEuler
public import SphereSixComplex.Prerequisites.Topology.SmoothRecognition
public import Mathlib.Topology.Homotopy.Equiv

@[expose] public section
noncomputable section
open AlgebraicTopology CategoryTheory Set
open scoped ContinuousMap
namespace SphereSixComplex

namespace IntegralHomologyFiniteSix

/-- Homological finiteness and the dimension bound transport through a homotopy equivalence. -/
public theorem homotopyEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (hX : IntegralHomologyFiniteSix X) (e : X ≃ₕ Y) : IntegralHomologyFiniteSix Y where
  finite_homology k := by
    let _ : Module.Finite ℤ (IntegralSingularHomology k X) := hX.finite_homology k
    exact Module.Finite.equiv
      (integralSingularHomologyEquivOfHomotopyEquiv k e).toIntLinearEquiv
  subsingleton_homology_of_six_lt k hk := by
    let h := hX.subsingleton_homology_of_six_lt k hk
    let eH := integralSingularHomologyEquivOfHomotopyEquiv k e
    exact ⟨fun x y ↦ eH.symm.injective (@Subsingleton.elim _ h _ _)⟩

end IntegralHomologyFiniteSix

end SphereSixComplex
