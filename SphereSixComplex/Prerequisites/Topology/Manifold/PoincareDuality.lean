module

public import SphereSixComplex.Prerequisites.Topology.SingularHomology.ModuleComparison
import DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.Manifold

/-!
# Integral Poincaré duality for simply connected compact manifolds

The cap-product theorem and the compact-support comparison are proved in
DifferentialGeometry. The coefficient-category comparison identifies their groups
with this project's integral singular homology and cohomology.
-/

@[expose] public section
noncomputable section
open scoped Manifold

namespace SphereSixComplex
open IntegralSingularComparison

/-- Integral duality for a compact simply connected real C¹ manifold. -/
public theorem PoincareDuality.nonempty_addEquiv_of_simplyConnected (E X : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X] [ChartedSpace E X]
    [IsManifold 𝓘(ℝ, E) 1 X] [SimplyConnectedSpace X] [CompactSpace X]
    (k m : ℕ) (hkm : k + m = Module.finrank ℝ E) :
    Nonempty (SphereSixComplex.IntegralSingularCohomology k X ≃+
      SphereSixComplex.IntegralSingularHomology m X) := by
  obtain ⟨_, _, _, D, ⟨_, hbij⟩, _⟩ :=
    DifferentialGeometry.Topology.exists_integralCompactlySupportedCohomology_cap_bijective_of_simplyConnected
      (E := E) (M := X) k m hkm
  let e := LinearEquiv.ofBijective
    (DifferentialGeometry.Topology.integralCompactlySupportedToSingularCohomology k X)
    (DifferentialGeometry.Topology.integralCompactlySupportedToSingularCohomology_bijective
      (X := X) k)
  exact ⟨(cohomologyEquiv X k).symm.trans
    (e.symm.toAddEquiv.trans ((LinearEquiv.ofBijective D hbij).toAddEquiv.trans
      (homologyIso X m).addCommGroupIsoToAddEquiv))⟩

end SphereSixComplex
