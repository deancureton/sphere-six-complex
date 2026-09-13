module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas

@[expose] public section

open Filter Topology
open scoped OnePoint

namespace ContinuousMap

variable {K X : Type*} [NormedDivisionRing K] [ProperSpace K] [TopologicalSpace X]

/-- Two continuous charts related by inversion define a map from the one-point compactification. -/
def onePointOfInv (f g : C(K, X)) (h : ∀ z ≠ 0, f z = g z⁻¹) : C(OnePoint K, X) :=
  OnePoint.continuousMapMk f (g 0) (by
    rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    apply (g.continuous.continuousAt.tendsto.comp tendsto_inv₀_cobounded).congr'
    filter_upwards [show ∀ᶠ z : K in Bornology.cobounded K, z ≠ 0 from by
      rw [Metric.cobounded_eq_cocompact]
      exact isCompact_singleton.compl_mem_cocompact] with z hz
    exact (h z hz).symm)

@[simp] theorem onePointOfInv_coe (f g : C(K, X)) (h : ∀ z ≠ 0, f z = g z⁻¹) (z : K) :
    onePointOfInv f g h z = f z := rfl

@[simp] theorem onePointOfInv_infty (f g : C(K, X)) (h : ∀ z ≠ 0, f z = g z⁻¹) :
    onePointOfInv f g h ∞ = g 0 := rfl

end ContinuousMap
end
