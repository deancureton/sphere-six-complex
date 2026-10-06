module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import Mathlib.Topology.ContinuousMap.Basic

@[expose] public section

namespace DifferentialGeometry.Topology.Morse

open Manifold

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def sublevel (f : M → ℝ) (a : ℝ) : Set M :=
  f ⁻¹' Set.Iic a

def superlevel (f : M → ℝ) (a : ℝ) : Set M :=
  f ⁻¹' Set.Ici a

def sublevelStrip (f : M → ℝ) (a b : ℝ) : Set M :=
  f ⁻¹' Set.Icc a b

abbrev SublevelSpace (f : M → ℝ) (a : ℝ) : Type _ :=
  {x : M // x ∈ sublevel f a}

noncomputable def sublevelInclusion {M : Type*} [TopologicalSpace M] (f : M → ℝ) {a b : ℝ}
    (hab : a ≤ b) : C(SublevelSpace f a, SublevelSpace f b) :=
  ContinuousMap.mk (fun x => ⟨x.1, by
    change f x.1 ≤ b
    exact le_trans (by change f x.1 ≤ a; exact x.2) hab⟩) (by
    exact Continuous.subtype_mk continuous_subtype_val (by
      intro x
      change f x.1 ≤ b
      exact le_trans (by change f x.1 ≤ a; exact x.2) hab))

def IsCriticalPointAt (I : ModelWithCorners ℝ E H) (f : M → ℝ) (x : M) : Prop :=
  mfderiv I 𝓘(ℝ, ℝ) f x = 0

def criticalPoints (I : ModelWithCorners ℝ E H) (f : M → ℝ) : Set M :=
  {x | IsCriticalPointAt I f x}

def chartHessianBilinAt (g : E → ℝ) (y : E) : LinearMap.BilinForm ℝ E :=
  { toFun := fun x => (fderiv ℝ (fderiv ℝ g) y x).toLinearMap
    map_add' := by
      intro x y
      ext z
      simp
    map_smul' := by
      intro a x
      ext z
      simp }

def chartHessianAt (g : E → ℝ) (y : E) : QuadraticForm ℝ E :=
  (chartHessianBilinAt g y).toQuadraticMap

def chartHessian (g : E → ℝ) : QuadraticForm ℝ E :=
  chartHessianAt g 0

def IsNondegenerateCriticalPointAt (I : ModelWithCorners ℝ E H) (f : M → ℝ) (x : M) : Prop :=
  IsCriticalPointAt I f x ∧
    (QuadraticMap.associated (R := ℝ)
      (chartHessianAt (g := fun y => f ((extChartAt I x).symm y))
        (extChartAt I x x))).SeparatingLeft

end
end DifferentialGeometry.Topology.Morse
