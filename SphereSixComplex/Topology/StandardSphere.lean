module

public import SphereSixComplex.ComplexStructure
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# Standard topological and smooth facts about the six-sphere

This file records the baseline facts already supported by mathlib for the standard unit sphere.
-/

@[expose] public section

open Set
open scoped ContDiff Manifold

namespace SphereSixComplex

/-- The unit six-sphere is nonempty. -/
public theorem sixSphere_nonempty : Nonempty SixSphere :=
  Set.Nonempty.to_subtype (NormedSpace.sphere_nonempty.mpr (by norm_num))

/-- The unit six-sphere is compact as a subset of its ambient Euclidean space. -/
public theorem sixSphere_isCompact :
    IsCompact (Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1) :=
  isCompact_sphere 0 1

/-- The unit six-sphere carries mathlib's compact-space instance. -/
public theorem sixSphere_compactSpace : CompactSpace SixSphere := inferInstance

/-- The ambient Euclidean space has rank greater than one. -/
private theorem one_lt_rank_euclideanSpace_fin_seven :
    1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 7)) := by
  rw [← Module.finrank_eq_rank]
  norm_num [finrank_euclideanSpace_fin]

/-- The unit six-sphere is path-connected as a subset of its ambient Euclidean space. -/
public theorem sixSphere_isPathConnected :
    IsPathConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1) :=
  isPathConnected_sphere one_lt_rank_euclideanSpace_fin_seven 0 (by norm_num)

/-- The unit six-sphere is connected as a subset of its ambient Euclidean space. -/
public theorem sixSphere_isConnected :
    IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1) :=
  sixSphere_isPathConnected.isConnected

/-- The subtype representing the unit six-sphere is path-connected. -/
public theorem sixSphere_pathConnectedSpace : PathConnectedSpace SixSphere :=
  isPathConnected_iff_pathConnectedSpace.mp sixSphere_isPathConnected

/-- The subtype representing the unit six-sphere is connected. -/
public theorem sixSphere_connectedSpace : ConnectedSpace SixSphere :=
  isConnected_iff_connectedSpace.mp sixSphere_isConnected

/-- The standard six-sphere has mathlib's smooth real six-manifold structure. -/
public theorem sixSphere_isManifold :
    IsManifold 𝓘(ℝ, RealModel) ∞ SixSphere := inferInstance

end SphereSixComplex
