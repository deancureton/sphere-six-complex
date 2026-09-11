module

public import SphereSixComplex.Prerequisites.Topology.MayerVietoris

/-!
# The Hurewicz--Whitehead recognition gap

This file isolates the map-level content missing from the current topological API.  Mathlib has
singular homology and homotopy invariance, so homotopy equivalences can be proved to induce
isomorphisms on integral homology. It defines higher cubical homotopy groups, but currently has no
induced-map API or Hurewicz homomorphism for them, and it has no homological Whitehead theorem or CW
approximation theorem for topological manifolds. In particular, the abstract degreewise group
isomorphisms in
`HasIntegralHomologyOfSixSphere` do not construct a single map to the sphere.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory ContinuousMap

namespace SphereSixComplex

/-- A map-level integral homology equivalence.  Unlike
`HasIntegralHomologyOfSixSphere`, this records one coherent continuous map in every degree. -/
public def IsIntegralHomologyEquivalence {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) : Prop :=
  ∀ k : ℕ, IsIso (((singularHomologyFunctor AddCommGrpCat k).obj
    (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f))

/-- Homotopic maps induce the same map on integral singular homology. -/
public theorem integralSingularHomologyMap_eq_of_homotopic
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (h : f.Homotopic g) (k : ℕ) :
    ((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom f) =
      ((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom g) :=
  TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    h.some (AddCommGrpCat.of ℤ) k



/-- Every homotopy equivalence is an integral homology equivalence. -/
public theorem homotopyEquiv_isIntegralHomologyEquivalence
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) :
    IsIntegralHomologyEquivalence e.toFun := by
  intro k
  let F := (singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom e.toFun
  let g : TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom e.invFun
  let i : F.obj (TopCat.of X) ≅ F.obj (TopCat.of Y) :=
    CategoryTheory.Iso.mk (F.map f) (F.map g) (by
      rw [← F.map_comp, ← F.map_id]
      exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
        e.left_inv.some (AddCommGrpCat.of ℤ) k) (by
      rw [← F.map_comp, ← F.map_id]
      exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
        e.right_inv.some (AddCommGrpCat.of ℤ) k)
  exact i.isIso_hom




/-- The precise map-level Whitehead property needed after constructing a homology comparison map.
It is deliberately separated from the abstract homology-sphere condition: proving it for simply
connected CW-type spaces requires Hurewicz maps and the homological Whitehead theorem, which are not
yet available in mathlib's topological-space API. -/
public def IntegralHomologyWhiteheadProperty (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] : Prop :=
  ∀ (f : C(X, Y)), IsIntegralHomologyEquivalence f →
    ∃ e : X ≃ₕ Y, e.toFun = f




end SphereSixComplex
