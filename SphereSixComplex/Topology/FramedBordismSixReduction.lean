module

public import SphereSixComplex.Topology.GeometricOrientedHCobordismSix
public import SphereSixComplex.Topology.StableFramingHomotopySixSphere

/-!
# A geometric framed-bordism reduction in dimension six

This file isolates the part of the classical Kervaire--Milnor argument which is not presently
available in Mathlib.  Unlike an abstract assumption that `Theta₆` vanishes, the intermediate
objects below are genuine smooth seven-manifolds with their entire boundary specified by a
collar.  A parallelizable filling carries an actual global smooth frame of its tangent bundle,
and a contractible filling carries Mathlib's ordinary `ContractibleSpace` witness.

There are three intentionally separate missing theorems:

* Pontryagin--Thom/Kervaire theory must produce a parallelizable filling;
* middle-dimensional surgery must replace it by a contractible filling;
* puncturing a contractible filling by a smoothly embedded disk must produce the oriented
  h-cobordism to the standard sphere.

The last two statements are expressed as implications between concrete geometric structures.
Consequently none of them is merely a renamed assertion that `Theta₆ = 0`.
-/

@[expose] public section

noncomputable section

open ContinuousMap
open scoped ContDiff Manifold

namespace SphereSixComplex

namespace OrientedMarkedSmoothHomotopySixSphere

/-- The empty closed six-manifold, used as the absent outgoing end of a filling. -/
public abbrev EmptySixManifold := Fin 0

/-- The empty end has the canonical empty smooth atlas over the six-dimensional model. -/
public noncomputable instance emptySixManifoldChartedSpace :
    ChartedSpace RealModel EmptySixManifold :=
  ChartedSpace.empty RealModel EmptySixManifold

/-- A genuine compact smooth seven-manifold whose entire boundary is the marked homotopy sphere.

Using a collared bordism with empty outgoing end keeps the boundary assertion concrete: the
`boundary_eq` field of `SmoothCollaredBordism` says that every boundary point lies in the supplied
incoming collar. -/
public structure SmoothFillingSix
    (S : OrientedMarkedSmoothHomotopySixSphere.{0}) where
  /-- The compact smooth seven-manifold, with `S` as its only boundary component. -/
  bordism : SmoothCollaredBordism.{0, 0, 0, 0, 0}
    𝓘(ℝ, RealModel) S.carrier EmptySixManifold

namespace SmoothFillingSix

variable {S : OrientedMarkedSmoothHomotopySixSphere.{0}}

/-- The underlying filling carrier. -/
public abbrev Carrier (W : SmoothFillingSix S) := W.bordism.W

instance (W : SmoothFillingSix S) : TopologicalSpace W.Carrier := inferInstance
instance (W : SmoothFillingSix S) : T2Space W.Carrier := inferInstance
instance (W : SmoothFillingSix S) : SecondCountableTopology W.Carrier := inferInstance
instance (W : SmoothFillingSix S) :
    ChartedSpace (ModelProd RealModel (EuclideanHalfSpace 1)) W.Carrier := inferInstance
instance (W : SmoothFillingSix S) :
    IsManifold (𝓘(ℝ, RealModel).prod (𝓡∂ 1)) ∞ W.Carrier := inferInstance
instance (W : SmoothFillingSix S) : CompactSpace W.Carrier := inferInstance

/-- A global smooth frame of the tangent bundle of a seven-dimensional filling.

`Fin 0 → ℝ` is the zero-dimensional normed vector space, so this is literally a frame of `TW`,
not a further stabilization of it. -/
public abbrev TangentFraming (W : SmoothFillingSix S) :=
  SmoothStableFraming (M := W.Carrier)
    (𝓘(ℝ, RealModel).prod (𝓡∂ 1)) (Fin 0 → ℝ) (Fin 7)

end SmoothFillingSix

/-- A genuine parallelizable filling of a marked homotopy six-sphere. -/
public structure SmoothParallelizableFillingSix
    (S : OrientedMarkedSmoothHomotopySixSphere.{0}) extends SmoothFillingSix S where
  /-- An actual smooth seven-frame of the filling tangent bundle. -/
  tangentFraming : toSmoothFillingSix.TangentFraming

/-- A genuine contractible filling of a marked homotopy six-sphere. -/
public structure SmoothContractibleFillingSix
    (S : OrientedMarkedSmoothHomotopySixSphere.{0}) extends SmoothFillingSix S where
  /-- The filling carrier is contractible in Mathlib's ordinary topological sense. -/
  contractible : ContractibleSpace toSmoothFillingSix.Carrier

namespace SmoothContractibleFillingSix

variable {S : OrientedMarkedSmoothHomotopySixSphere.{0}}

/-- Install the stored contractibility proof as an instance for downstream topology. -/
public instance (W : SmoothContractibleFillingSix S) :
    ContractibleSpace W.toSmoothFillingSix.Carrier := W.contractible

/-- A contractible filling is explicitly homotopy equivalent to a point. -/
public theorem nonempty_homotopyEquivUnit (W : SmoothContractibleFillingSix S) :
    Nonempty (W.toSmoothFillingSix.Carrier ≃ₕ Unit) :=
  ContractibleSpace.hequiv_unit W.toSmoothFillingSix.Carrier

end SmoothContractibleFillingSix

/-- Representative-level Pontryagin--Thom/Kervaire input.

This asks for an actual parallelizable seven-manifold filling each stably framed homotopy sphere.
The stable frame is an input because different stable framings can represent different framed
bordism classes.  A complete construction must relate that boundary frame to the tangent frame
on the filling; Mathlib currently lacks the boundary differential/orientation API needed to state
that compatibility intrinsically.  Therefore this deliberately strong existence statement is
kept separate from stable parallelizability itself. -/
public def StableFramingsBoundParallelizableSevenManifolds : Prop :=
  ∀ (S : OrientedMarkedSmoothHomotopySixSphere.{0})
    (_f : SmoothStableFramingSix (M := S.carrier)),
    Nonempty (SmoothParallelizableFillingSix S)

/-- The dimension-seven surgery step, stated between genuine geometric witnesses. -/
public def ParallelizableFillingSurgeryToContractible : Prop :=
  ∀ (S : OrientedMarkedSmoothHomotopySixSphere.{0}),
    SmoothParallelizableFillingSix S → Nonempty (SmoothContractibleFillingSix S)

/-- The puncturing/h-cobordism step.

Classically one removes the interior of a smoothly embedded seven-disk from a contractible
filling.  Proving that the remaining collared bordism has both end inclusions as homotopy
equivalences uses smooth disk embeddings, boundary orientation, duality and Whitehead theory;
those ingredients are not available in Mathlib in the required form. -/
public def ContractibleFillingPuncturesToHCobordism
    (D : SixSphereDegreeTheory) : Prop :=
  ∀ (S : OrientedMarkedSmoothHomotopySixSphere.{0}),
    SmoothContractibleFillingSix S →
      SmoothHCobordant D S OrientedMarkedSmoothHomotopySixSphere.standard

/-- Stable parallelizability and representative-level framed null-bordism produce an actual
parallelizable filling. -/
public theorem parallelizableFilling_of_stableFraming
    (hStable : HomotopySixSpheresStablyParallelizable)
    (hPT : StableFramingsBoundParallelizableSevenManifolds) :
    ∀ S : OrientedMarkedSmoothHomotopySixSphere.{0},
      Nonempty (SmoothParallelizableFillingSix S) := by
  intro S
  obtain ⟨f⟩ := hStable S
  exact hPT S f

/-- Adding the surgery theorem upgrades every representative to an actual contractible
seven-dimensional filling. -/
public theorem contractibleFilling_of_framedBordism_and_surgery
    (hStable : HomotopySixSpheresStablyParallelizable)
    (hPT : StableFramingsBoundParallelizableSevenManifolds)
    (hSurgery : ParallelizableFillingSurgeryToContractible) :
    ∀ S : OrientedMarkedSmoothHomotopySixSphere.{0},
      Nonempty (SmoothContractibleFillingSix S) := by
  intro S
  obtain ⟨W⟩ := parallelizableFilling_of_stableFraming hStable hPT S
  exact hSurgery S W

/-- Stable parallelizability, framed null-bordism, surgery, and puncturing together give a
genuine oriented h-cobordism from every representative to the standard sphere. -/
public theorem hCobordant_standard_of_framedBordism_and_surgery
    (D : SixSphereDegreeTheory)
    (hStable : HomotopySixSpheresStablyParallelizable)
    (hPT : StableFramingsBoundParallelizableSevenManifolds)
    (hSurgery : ParallelizableFillingSurgeryToContractible)
    (hPuncture : ContractibleFillingPuncturesToHCobordism D) :
    ∀ S : OrientedMarkedSmoothHomotopySixSphere.{0},
      SmoothHCobordant D S OrientedMarkedSmoothHomotopySixSphere.standard := by
  intro S
  obtain ⟨C⟩ := contractibleFilling_of_framedBordism_and_surgery
    hStable hPT hSurgery S
  exact hPuncture S C

/-- The same concrete chain of geometric inputs kills the generated genuine h-cobordism
quotient.  This endpoint needs no connected-sum construction and no gluing theorem. -/
public theorem generatedGeometricThetaSixVanishes_of_framedBordism_and_surgery
    (D : SixSphereDegreeTheory)
    (hStable : HomotopySixSpheresStablyParallelizable)
    (hPT : StableFramingsBoundParallelizableSevenManifolds)
    (hSurgery : ParallelizableFillingSurgeryToContractible)
    (hPuncture : ContractibleFillingPuncturesToHCobordism D) :
    (generatedGeometricSmoothHCobordismRelation D).ThetaSixVanishes :=
  generatedGeometricThetaSixVanishes_of_hCobordant_standard D
    (hCobordant_standard_of_framedBordism_and_surgery
      D hStable hPT hSurgery hPuncture)

/-- Adapter to the repository's unoriented compatibility endpoint. -/
public theorem generatedGeometricThetaSixVanishesAdapter_of_framedBordism_and_surgery
    (D : SixSphereDegreeTheory)
    (hStable : HomotopySixSpheresStablyParallelizable)
    (hPT : StableFramingsBoundParallelizableSevenManifolds)
    (hSurgery : ParallelizableFillingSurgeryToContractible)
    (hPuncture : ContractibleFillingPuncturesToHCobordism D) :
    (generatedGeometricSmoothHCobordismRelation D).toSmoothHCobordismRelation.ThetaSixVanishes :=
  generatedGeometricThetaSixVanishesAdapter_of_hCobordant_standard D
    (hCobordant_standard_of_framedBordism_and_surgery
      D hStable hPT hSurgery hPuncture)

end OrientedMarkedSmoothHomotopySixSphere

end SphereSixComplex
