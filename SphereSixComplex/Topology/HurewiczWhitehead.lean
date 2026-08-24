module

public import SphereSixComplex.Topology.MayerVietoris

/-!
# The Hurewicz--Whitehead recognition gap

This file isolates the map-level content missing from the current topological API.  Mathlib has
singular homology and homotopy invariance, so homotopy equivalences can be proved to induce
isomorphisms on integral homology.  It does not currently define higher homotopy groups or the
Hurewicz homomorphism, and it has no Whitehead theorem or CW approximation theorem for topological
manifolds.  In particular, the abstract degreewise group isomorphisms in
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

/-- Being an integral homology equivalence is invariant under homotopy of maps. -/
public theorem isIntegralHomologyEquivalence_iff_of_homotopic
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (h : f.Homotopic g) :
    IsIntegralHomologyEquivalence f ↔ IsIntegralHomologyEquivalence g := by
  constructor
  · intro hf k
    rw [← integralSingularHomologyMap_eq_of_homotopic h k]
    exact hf k
  · intro hg k
    rw [integralSingularHomologyMap_eq_of_homotopic h k]
    exact hg k

/-- Integral homology equivalences are closed under composition. -/
public theorem IsIntegralHomologyEquivalence.comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : C(X, Y)} {g : C(Y, Z)}
    (hg : IsIntegralHomologyEquivalence g) (hf : IsIntegralHomologyEquivalence f) :
    IsIntegralHomologyEquivalence (g.comp f) := by
  intro k
  change IsIso (((singularHomologyFunctor AddCommGrpCat k).obj
    (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f ≫ TopCat.ofHom g))
  rw [Functor.map_comp]
  let _ := hf k
  let _ := hg k
  infer_instance

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

/-- The identity map is an integral homology equivalence. -/
public theorem isIntegralHomologyEquivalence_id (X : Type) [TopologicalSpace X] :
    IsIntegralHomologyEquivalence (ContinuousMap.id X) :=
  homotopyEquiv_isIntegralHomologyEquivalence (ContinuousMap.HomotopyEquiv.refl X)

/-- A coherent map-level comparison with the standard sphere. -/
public def HasIntegralHomologyComparisonToSixSphere (X : Type) [TopologicalSpace X] : Prop :=
  ∃ f : C(X, SixSphere), IsIntegralHomologyEquivalence f

/-- A map-level comparison implies the weaker abstract degreewise homology-sphere contract. -/
public theorem HasIntegralHomologyComparisonToSixSphere.hasIntegralHomologyOfSixSphere
    {X : Type} [TopologicalSpace X]
    (h : HasIntegralHomologyComparisonToSixSphere X) : HasIntegralHomologyOfSixSphere X := by
  obtain ⟨f, hf⟩ := h
  intro k
  let _ := hf k
  let F := (singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)
  exact ⟨(asIso (F.map (TopCat.ofHom f))).addCommGroupIsoToAddEquiv⟩

/-- The precise map-level Whitehead property needed after constructing a homology comparison map.
It is deliberately separated from the abstract homology-sphere condition: proving it for simply
connected CW-type spaces requires higher homotopy groups, Hurewicz, and Whitehead, which are not
yet available in mathlib's topological-space API. -/
public def IntegralHomologyWhiteheadProperty (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] : Prop :=
  ∀ (f : C(X, Y)), IsIntegralHomologyEquivalence f →
    ∃ e : X ≃ₕ Y, e.toFun = f

/-- A coherent homology comparison and the map-level Whitehead property produce the desired
homotopy equivalence. -/
public theorem homotopyEquivSixSphere_of_comparison_of_whitehead
    {X : Type} [TopologicalSpace X]
    (hComparison : HasIntegralHomologyComparisonToSixSphere X)
    (hWhitehead : IntegralHomologyWhiteheadProperty X SixSphere) :
    Nonempty (X ≃ₕ SixSphere) := by
  obtain ⟨f, hf⟩ := hComparison
  obtain ⟨e, _⟩ := hWhitehead f hf
  exact ⟨e⟩

/-- The original recognition obligation follows once the two genuinely stronger map-level steps
are supplied: construction of one coherent comparison map and Whitehead's theorem for that map. -/
public theorem homologyToHomotopySixSphere_of_comparison_of_whitehead
    {X : Type} [TopologicalSpace X] [ChartedSpace RealModel X]
    (hComparison : SmoothSimplyConnectedIntegralHomologySixSphere X →
      HasIntegralHomologyComparisonToSixSphere X)
    (hWhitehead : IntegralHomologyWhiteheadProperty X SixSphere) :
    HomologyToHomotopySixSphereObligation X := by
  intro hX
  exact homotopyEquivSixSphere_of_comparison_of_whitehead (hComparison hX) hWhitehead

/-- Homotopy equivalence to the sphere supplies a coherent comparison map. -/
public theorem hasIntegralHomologyComparisonToSixSphere_of_homotopyEquiv
    {X : Type} [TopologicalSpace X] (e : X ≃ₕ SixSphere) :
    HasIntegralHomologyComparisonToSixSphere X :=
  ⟨e.toFun, homotopyEquiv_isIntegralHomologyEquivalence e⟩

end SphereSixComplex
