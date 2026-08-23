module

public import SphereSixComplex.Topology.HomologySphere
public import SphereSixComplex.Topology.SphereSimplyConnected
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Geometry.Manifold.PoincareConjecture

/-!
# Smooth recognition of the six-sphere

This file packages the inputs to six-dimensional smooth sphere recognition.  Mathlib states the
generalized and smooth Poincaré conjectures, but does not yet prove the dimension-six case, nor the
Whitehead--Hurewicz step from simply connected integral homology spheres to homotopy spheres.
Accordingly, those two implications are exposed as exact obligations rather than postulated.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory ContinuousMap
open scoped ContDiff Manifold

namespace SphereSixComplex

/-- Integral singular homology is invariant under a homotopy equivalence. -/
public noncomputable def integralSingularHomologyEquivOfHomotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (k : ℕ) (e : X ≃ₕ Y) :
    IntegralSingularHomology k X ≃+ IntegralSingularHomology k Y := by
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
  exact i.addCommGroupIsoToAddEquiv

/-- Degreewise integral homology-sphere data transports through a homotopy equivalence. -/
public theorem HasIntegralHomologyOfSixSphere.homotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (hX : HasIntegralHomologyOfSixSphere X) (e : X ≃ₕ Y) :
    HasIntegralHomologyOfSixSphere Y := by
  intro k
  obtain ⟨h⟩ := hX k
  exact ⟨(integralSingularHomologyEquivOfHomotopyEquiv k e).symm.trans h⟩

/-- A compact connected smooth manifold modelled on real six-space. -/
public structure CompactConnectedSmoothSixManifold (X : Type) [TopologicalSpace X]
    [ChartedSpace RealModel X] : Prop where
  /-- Smoothness of the given atlas. -/
  isManifold : IsManifold 𝓘(ℝ, RealModel) ∞ X
  /-- Compactness of the underlying space. -/
  compact : CompactSpace X
  /-- Connectedness of the underlying space. -/
  connected : ConnectedSpace X

/-- A compact connected smooth six-manifold with the integral singular homology of `S⁶`. -/
public structure SmoothIntegralHomologySixSphere (X : Type) [TopologicalSpace X]
    [ChartedSpace RealModel X] : Prop extends CompactConnectedSmoothSixManifold X where
  /-- Degreewise integral singular homology agrees with the standard six-sphere. -/
  integralHomology : HasIntegralHomologyOfSixSphere X

/-- The recognition input consisting of a simply connected smooth integral homology six-sphere. -/
public structure SmoothSimplyConnectedIntegralHomologySixSphere (X : Type) [TopologicalSpace X]
    [ChartedSpace RealModel X] : Prop extends SmoothIntegralHomologySixSphere X where
  /-- The underlying space is simply connected. -/
  simplyConnected : SimplyConnectedSpace X

/-- A compact connected smooth six-manifold homotopy equivalent to the standard six-sphere. -/
public structure SmoothHomotopySixSphere (X : Type) [TopologicalSpace X]
    [ChartedSpace RealModel X] : Prop extends CompactConnectedSmoothSixManifold X where
  /-- A homotopy equivalence to the standard six-sphere. -/
  homotopyEquiv : Nonempty (X ≃ₕ SixSphere)

/-- Smooth diffeomorphism to the standard six-sphere, using the fixed real six-dimensional model. -/
public abbrev SmoothDiffeomorphicToSixSphere (X : Type) [TopologicalSpace X]
    [ChartedSpace RealModel X] : Prop :=
  Nonempty (Diffeomorph 𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel) X SixSphere ∞)

/-- The missing Whitehead--Hurewicz recognition step for a particular smooth six-manifold. -/
public def HomologyToHomotopySixSphereObligation (X : Type) [TopologicalSpace X]
    [ChartedSpace RealModel X] : Prop :=
  SmoothSimplyConnectedIntegralHomologySixSphere X → Nonempty (X ≃ₕ SixSphere)

/-- The missing dimension-six smooth Poincaré step for a particular smooth six-manifold. -/
public def HomotopyToDiffeomorphismSixSphereObligation (X : Type) [TopologicalSpace X]
    [ChartedSpace RealModel X] : Prop :=
  IsManifold 𝓘(ℝ, RealModel) ∞ X →
    Nonempty (X ≃ₕ SixSphere) → SmoothDiffeomorphicToSixSphere X

/-- The exact combined smooth-recognition obligation for a simply connected integral homology
six-sphere. -/
public def SmoothSixSphereRecognitionObligation (X : Type) [TopologicalSpace X]
    [ChartedSpace RealModel X] : Prop :=
  SmoothSimplyConnectedIntegralHomologySixSphere X → SmoothDiffeomorphicToSixSphere X

/-- The simply connected homology-sphere contract supplies the previously defined topological
recognition data. -/
public theorem SmoothSimplyConnectedIntegralHomologySixSphere.toRecognitionInput
    {X : Type} [TopologicalSpace X] [ChartedSpace RealModel X]
    (h : SmoothSimplyConnectedIntegralHomologySixSphere X) : SixSphereRecognitionInput X := by
  let _ : SimplyConnectedSpace X := h.simplyConnected
  exact ⟨inferInstance, inferInstance, inferInstance, h.integralHomology⟩

/-- Solving the two isolated recognition obligations solves smooth sphere recognition. -/
public theorem smoothSixSphereRecognition_of_obligations
    {X : Type} [TopologicalSpace X] [ChartedSpace RealModel X]
    (hHomotopy : HomologyToHomotopySixSphereObligation X)
    (hSmooth : HomotopyToDiffeomorphismSixSphereObligation X) :
    SmoothSixSphereRecognitionObligation X := by
  intro hX
  exact hSmooth hX.isManifold (hHomotopy hX)

/-- Connectedness transports through a homeomorphism. -/
public theorem connectedSpace_of_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [ConnectedSpace X] (h : X ≃ₜ Y) : ConnectedSpace Y := by
  exact h.connectedSpace_iff.mp inferInstance

/-- The compact connected smooth-manifold contract transports through a diffeomorphism, once the
target atlas is known to be a manifold atlas. -/
public theorem CompactConnectedSmoothSixManifold.diffeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace RealModel X] [ChartedSpace RealModel Y]
    (hX : CompactConnectedSmoothSixManifold X) (hY : IsManifold 𝓘(ℝ, RealModel) ∞ Y)
    (d : Diffeomorph 𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel) X Y ∞) :
    CompactConnectedSmoothSixManifold Y := by
  let _ : CompactSpace X := hX.compact
  let _ : ConnectedSpace X := hX.connected
  exact ⟨hY, d.toHomeomorph.compactSpace, connectedSpace_of_homeomorph d.toHomeomorph⟩

/-- Smooth integral homology-sphere data transports through a diffeomorphism. -/
public theorem SmoothIntegralHomologySixSphere.diffeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace RealModel X] [ChartedSpace RealModel Y]
    (hX : SmoothIntegralHomologySixSphere X) (hY : IsManifold 𝓘(ℝ, RealModel) ∞ Y)
    (d : Diffeomorph 𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel) X Y ∞) :
    SmoothIntegralHomologySixSphere Y where
  toCompactConnectedSmoothSixManifold :=
    hX.toCompactConnectedSmoothSixManifold.diffeomorph hY d
  integralHomology := hX.integralHomology.homeomorph d.toHomeomorph

/-- Simply connected smooth integral homology-sphere data transports through a diffeomorphism. -/
public theorem SmoothSimplyConnectedIntegralHomologySixSphere.diffeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace RealModel X] [ChartedSpace RealModel Y]
    (hX : SmoothSimplyConnectedIntegralHomologySixSphere X)
    (hY : IsManifold 𝓘(ℝ, RealModel) ∞ Y)
    (d : Diffeomorph 𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel) X Y ∞) :
    SmoothSimplyConnectedIntegralHomologySixSphere Y := by
  let _ : SimplyConnectedSpace X := hX.simplyConnected
  exact
    { toSmoothIntegralHomologySixSphere :=
        hX.toSmoothIntegralHomologySixSphere.diffeomorph hY d
      simplyConnected := simplyConnectedSpace_of_homeomorph d.toHomeomorph }

/-- The smooth homotopy-sphere contract transports through a diffeomorphism. -/
public theorem SmoothHomotopySixSphere.diffeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace RealModel X] [ChartedSpace RealModel Y]
    (hX : SmoothHomotopySixSphere X) (hY : IsManifold 𝓘(ℝ, RealModel) ∞ Y)
    (d : Diffeomorph 𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel) X Y ∞) :
    SmoothHomotopySixSphere Y := by
  obtain ⟨e⟩ := hX.homotopyEquiv
  exact
    { toCompactConnectedSmoothSixManifold :=
        hX.toCompactConnectedSmoothSixManifold.diffeomorph hY d
      homotopyEquiv := ⟨d.symm.toHomeomorph.toHomotopyEquiv.trans e⟩ }

/-- Mathlib's stated smooth Poincaré property, specialized to dimension six and a fixed carrier. -/
public abbrev MathlibSmoothPoincareSixStatement (X : Type) [TopologicalSpace X] : Prop :=
  ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere X 6

/-- Mathlib's dimension-six smooth Poincaré statement implies the fixed-atlas smooth recognition
step used here. -/
public theorem homotopyToDiffeomorphismSixSphere_of_mathlibSmoothPoincare
    {X : Type} [TopologicalSpace X] [ChartedSpace RealModel X]
    (h : MathlibSmoothPoincareSixStatement X) :
    HomotopyToDiffeomorphismSixSphereObligation X := by
  intro hM hE
  obtain ⟨e⟩ := hE
  simpa only [RealModel, SixSphere] using h inferInstance hM e

/-- The standard sphere satisfies the compact connected smooth integral homology contract. -/
public theorem sixSphere_smoothIntegralHomologySixSphere :
    SmoothIntegralHomologySixSphere SixSphere where
  isManifold := sixSphere_isManifold
  compact := sixSphere_compactSpace
  connected := sixSphere_connectedSpace
  integralHomology := sixSphere_hasIntegralHomologyOfSixSphere

/-- The standard sphere is tautologically a smooth homotopy six-sphere. -/
public theorem sixSphere_smoothHomotopySixSphere : SmoothHomotopySixSphere SixSphere where
  isManifold := sixSphere_isManifold
  compact := sixSphere_compactSpace
  connected := sixSphere_connectedSpace
  homotopyEquiv := ⟨ContinuousMap.HomotopyEquiv.refl SixSphere⟩

/-- Every smooth homotopy six-sphere has the integral homology of the standard six-sphere. -/
public theorem SmoothHomotopySixSphere.toSmoothIntegralHomologySixSphere
    {X : Type} [TopologicalSpace X] [ChartedSpace RealModel X]
    (h : SmoothHomotopySixSphere X) : SmoothIntegralHomologySixSphere X := by
  obtain ⟨e⟩ := h.homotopyEquiv
  exact
    { toCompactConnectedSmoothSixManifold := h.toCompactConnectedSmoothSixManifold
      integralHomology :=
        sixSphere_hasIntegralHomologyOfSixSphere.homotopyEquiv e.symm }

/-- A homotopy six-sphere is simply connected once the corresponding standard-sphere theorem is
available. -/
public theorem SmoothHomotopySixSphere.simplyConnected
    {X : Type} [TopologicalSpace X] [ChartedSpace RealModel X]
    (h : SmoothHomotopySixSphere X) [SimplyConnectedSpace SixSphere] :
    SimplyConnectedSpace X := by
  obtain ⟨e⟩ := h.homotopyEquiv
  exact e.simplyConnectedSpace_iff.mpr inferInstance

end SphereSixComplex
