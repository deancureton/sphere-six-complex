module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.LiftedSimplex
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CarrierMaps
public import Mathlib.Topology.Algebra.Monoid.FunOnFinite

@[expose] public section

/-! # The same original face maps on lifted simplex bodies -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

/-- The original barycentric coordinate pushforward as a continuous linear
map on the lifted finite coordinate spaces. -/
def liftedSimplexLinearMap (n m : ℕ) (f : Fin (n + 1) → Fin (m + 1)) :
    liftedSimplexSpace.{u} n →L[ℝ] liftedSimplexSpace.{u} m :=
  (ContinuousLinearEquiv.ulift : liftedSimplexSpace.{u} m ≃L[ℝ] (Fin (m + 1) → ℝ)).symm.toContinuousLinearMap ∘L
    (⟨FunOnFinite.linearMap ℝ ℝ f, FunOnFinite.continuous_linearMap ℝ ℝ f⟩ :
      (Fin (n + 1) → ℝ) →L[ℝ] (Fin (m + 1) → ℝ)) ∘L
        (ContinuousLinearEquiv.ulift : liftedSimplexSpace.{u} n ≃L[ℝ] (Fin (n + 1) → ℝ)).toContinuousLinearMap

/-- Its original vertex action is exactly the specified vertex map. -/
theorem liftedSimplexLinearMap_vertex (n m : ℕ) (f : Fin (n + 1) → Fin (m + 1)) (i : Fin (n + 1)) :
    liftedSimplexLinearMap.{u} n m f (liftedSimplexVertex n i) = liftedSimplexVertex m (f i) := by
  apply ULift.ext
  exact FunOnFinite.linearMap_piSingle ℝ ℝ f i 1

/-- This same map preserves the actual simplex bodies. -/
theorem liftedSimplexLinearMap_body (n m : ℕ) (f : Fin (n + 1) → Fin (m + 1)) :
    MapsTo (liftedSimplexLinearMap.{u} n m f) (liftedSimplexBody n) (liftedSimplexBody m) := by
  rintro _ ⟨t, rfl⟩
  refine ⟨Convexity.StdSimplex.map f t, ?_⟩
  apply ULift.ext
  change (⇑(t.weights.mapDomain f)) =
    Finsupp.equivFunOnFinite (Finsupp.mapDomain f (Finsupp.equivFunOnFinite.symm t.weights))
  rw [Finsupp.equivFunOnFinite_symm_coe]
  rfl

/-- Restriction of the original coordinate map to the original simplex bodies. -/
def liftedSimplexBodyMap (n m : ℕ) (f : Fin (n + 1) → Fin (m + 1)) :
    C(liftedSimplexBody.{u} n, liftedSimplexBody.{u} m) :=
  singularPairRestriction ⟨liftedSimplexLinearMap n m f, (liftedSimplexLinearMap n m f).continuous⟩
    (liftedSimplexLinearMap_body n m f)

/-- Under the exact original homeomorphisms, the body map is the original
barycentric simplex map, including every boundary face. -/
theorem liftedSimplexBodyMap_apply (n m : ℕ) (f : Fin (n + 1) → Fin (m + 1))
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    liftedSimplexBodyMap.{u} n m f (liftedSimplexHomeomorph.{u} n t) =
      liftedSimplexHomeomorph.{u} m (Convexity.StdSimplex.map f t) := by
  apply Subtype.ext
  apply ULift.ext
  change Finsupp.equivFunOnFinite
      (Finsupp.mapDomain f (Finsupp.equivFunOnFinite.symm t.weights)) =
    (⇑(t.weights.mapDomain f))
  rw [Finsupp.equivFunOnFinite_symm_coe]
  rfl

end DifferentialGeometry.Topology
