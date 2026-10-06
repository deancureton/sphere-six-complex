module

public import DifferentialGeometry.Topology.Morse.Strip.Defs
public import DifferentialGeometry.Topology.Morse.CriticalPoint
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff

noncomputable abbrev morseModelI (n : ℕ) :
    ModelWithCorners ℝ (Fin n → ℝ) (EuclideanSpace ℝ (Fin n)) :=
  (𝓡 n).transContinuousLinearEquiv (EuclideanSpace.equiv (Fin n) ℝ)

instance morseModelI_boundaryless (n : ℕ) : (morseModelI n).Boundaryless := by
  refine ⟨?_⟩
  rw [ModelWithCorners.transContinuousLinearEquiv_range,
    ModelWithCorners.Boundaryless.range_eq_univ, Set.image_univ, Set.range_eq_univ]
  exact (EuclideanSpace.equiv (Fin n) ℝ).surjective

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem contMDiff_morseModelI_iff {f : M → ℝ} :
    ContMDiff (morseModelI n) 𝓘(ℝ, ℝ) ∞ f ↔ ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f :=
  ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left _

theorem isCriticalPointAt_morseModelI_iff {f : M → ℝ}
    {x : M} :
    Morse.IsCriticalPointAt (morseModelI n) f x ↔ Morse.IsCriticalPointAt (𝓡 n) f x :=
  Morse.isCriticalPointAt_transContinuousLinearEquiv_iff
    (𝓡 n) (EuclideanSpace.equiv (Fin n) ℝ) f x

end DifferentialGeometry.Topology
