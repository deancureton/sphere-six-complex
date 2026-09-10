module

public import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Bounded removable singularities

This file packages Mathlib's removable-singularity theorem in the local bounded form used by
analytic gluing arguments.
-/

open Filter Set

noncomputable section

namespace SphereSixComplex.Analysis

/-- Extend a function across one point by its punctured-neighborhood limit. -/
@[expose] public def boundedRemovableExtension {E : Type*} [TopologicalSpace E] [Nonempty E]
    (f : ℂ → E) (c : ℂ) : ℂ → E :=
  Function.update f c (limUnder (nhdsWithin c {c}ᶜ) f)

/-- The removable extension agrees with the original function away from the filled point. -/
public theorem boundedRemovableExtension_eq {E : Type*} [TopologicalSpace E] [Nonempty E]
    (f : ℂ → E) (c z : ℂ) (hz : z ≠ c) :
    boundedRemovableExtension f c z = f z := by
  simp [boundedRemovableExtension, hz]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A bounded holomorphic function on a punctured neighborhood extends holomorphically across
the missing point. -/
public theorem differentiableOn_boundedRemovableExtension
    {f : ℂ → E} {s : Set ℂ} {c : ℂ}
    (hs : s ∈ nhds c)
    (hf : DifferentiableOn ℂ f (s \ {c}))
    (hbounded : ∃ C : ℝ, ∀ z ∈ s \ {c}, ‖f z‖ ≤ C) :
    DifferentiableOn ℂ (boundedRemovableExtension f c) s := by
  unfold boundedRemovableExtension
  apply Complex.differentiableOn_update_limUnder_of_bddAbove hs hf
  obtain ⟨C, hC⟩ := hbounded
  refine ⟨C, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hC z hz

end SphereSixComplex.Analysis
