module

public import SphereSixComplex.Topology.StandardSphere
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.AlgebraicTopology.SingularHomology.Basic

/-!
# Homology-sphere recognition data

This file states the remaining topological recognition input precisely. Integral singular homology
is compared degreewise as an additive group, rather than through ranks or Betti numbers.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set
open scoped ContDiff Manifold

namespace SphereSixComplex

/-- Integral singular homology in degree `k`, regarded as an additive commutative group. -/
public abbrev IntegralSingularHomology (k : ℕ) (X : Type) [TopologicalSpace X] : Type :=
  ((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of X)

/-- Integral singular homology agrees degreewise with that of the standard six-sphere. -/
public def HasIntegralHomologyOfSixSphere (X : Type) [TopologicalSpace X] : Prop :=
  ∀ k : ℕ, Nonempty (IntegralSingularHomology k X ≃+ IntegralSingularHomology k SixSphere)

/-- The complete topological input expected by a six-dimensional sphere-recognition theorem. -/
public def SixSphereRecognitionInput (X : Type) [TopologicalSpace X] : Prop :=
  Nonempty X ∧ PathConnectedSpace X ∧ SimplyConnectedSpace X ∧
    HasIntegralHomologyOfSixSphere X

/-- A homeomorphism induces an additive equivalence on integral singular homology. -/
public noncomputable def integralSingularHomologyEquiv {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (k : ℕ) (h : X ≃ₜ Y) :
    IntegralSingularHomology k X ≃+ IntegralSingularHomology k Y :=
  (((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).mapIso
    (TopCat.isoOfHomeo h)).addCommGroupIsoToAddEquiv

/-- Degreewise integral homology-sphere data transports through a homeomorphism. -/
public theorem HasIntegralHomologyOfSixSphere.homeomorph {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (hX : HasIntegralHomologyOfSixSphere X) (h : X ≃ₜ Y) :
    HasIntegralHomologyOfSixSphere Y := by
  intro k
  obtain ⟨e⟩ := hX k
  exact ⟨(integralSingularHomologyEquiv k h).symm.trans e⟩

/-- Path-connectedness transports through a homeomorphism. -/
public theorem pathConnectedSpace_of_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [PathConnectedSpace X] (h : X ≃ₜ Y) : PathConnectedSpace Y := by
  rw [pathConnectedSpace_iff_univ]
  simpa only [image_univ, h.surjective.range_eq] using isPathConnected_univ.image h.continuous

/-- Simply-connectedness transports through a homeomorphism. -/
public theorem simplyConnectedSpace_of_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [SimplyConnectedSpace X] (h : X ≃ₜ Y) : SimplyConnectedSpace Y :=
  h.toHomotopyEquiv.simplyConnectedSpace_iff.mp inferInstance

/-- All sphere-recognition input transports through a homeomorphism. -/
public theorem SixSphereRecognitionInput.homeomorph {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (hX : SixSphereRecognitionInput X) (h : X ≃ₜ Y) :
    SixSphereRecognitionInput Y := by
  obtain ⟨hne, hpath, hsimple, hhomology⟩ := hX
  let _ : PathConnectedSpace X := hpath
  let _ : SimplyConnectedSpace X := hsimple
  exact ⟨Nonempty.map h hne, pathConnectedSpace_of_homeomorph h,
    simplyConnectedSpace_of_homeomorph h, hhomology.homeomorph h⟩

/-- A diffeomorphism transports all sphere-recognition input. -/
public theorem SixSphereRecognitionInput.diffeomorph
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace H X] [ChartedSpace H' Y] {n : ℕ∞ω}
    (hX : SixSphereRecognitionInput X) (d : Diffeomorph I I' X Y n) :
    SixSphereRecognitionInput Y :=
  hX.homeomorph d.toHomeomorph

/-- The standard six-sphere has its own integral singular homology, degree by degree. -/
public theorem sixSphere_hasIntegralHomologyOfSixSphere :
    HasIntegralHomologyOfSixSphere SixSphere :=
  fun _ ↦ ⟨AddEquiv.refl _⟩

/-- Every recognition component currently available in mathlib for the standard six-sphere. -/
public theorem sixSphere_supportedRecognitionInput :
    Nonempty SixSphere ∧ PathConnectedSpace SixSphere ∧ HasIntegralHomologyOfSixSphere SixSphere :=
  ⟨sixSphere_nonempty, sixSphere_pathConnectedSpace,
    sixSphere_hasIntegralHomologyOfSixSphere⟩

end SphereSixComplex
