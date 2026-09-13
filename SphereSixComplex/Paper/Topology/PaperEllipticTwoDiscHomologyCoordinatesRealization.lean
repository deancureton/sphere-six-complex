module

public import SphereSixComplex.Paper.Topology.EllipticDegreeTwoBasisFromOrbitSweep

public import SphereSixComplex.Paper.Topology.PaperEllipticFiniteCoverHomologyRealization
public import SphereSixComplex.Paper.Topology.PaperEllipticInteriorMayerVietorisBases

/-!
# Realizing the elliptic two-disc homology coordinates

This module turns the actual finite-cover calculations into the coordinate input for the
two-disc Mayer--Vietoris calculation.  The only extra datum is the naturality of the chosen
band trivializations: the order-three and order-four identifications of the same regular fibre
must induce the same period basis in degrees one and two.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Matrix Set
open scoped ContinuousMap

namespace SphereSixComplex

open Geometry Geometry.AnalyticTorusFamily Geometry.ComplexTorus
open Geometry.EllipticFamilySpecialization
open EllipticFilling
open EllipticFilling.RadialEllipticActionData
open AffineCyclicQuotientHomology
open LatticeData MultipleFiberCoinvariants

namespace Geometry.AnalyticData

variable {A : AnalyticData} {D : A.EllipticTwoDiscCoverData}

/-- The two trivializations of the regular band induce one common period basis.  This is the
precise naturality input needed to compare the two finite-cover projections; it contains no
Mayer--Vietoris matrix or homology computation of the union. -/
public structure EllipticBandHomologyAlignment
    (D : A.EllipticTwoDiscCoverData) : Prop where
  degreeOne : ∀ x : IntegralSingularHomology 1 (AdditiveTorus D.bandParameter),
    (orderFourCentralFiberCoverSourceHomologyBasis A.periods).degreeOne
        (integralSingularHomologyMap 1
          ⟨D.bandToOrderFourCoverSource, D.bandToOrderFourCoverSource.continuous⟩ x) =
      (orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeOne
        (integralSingularHomologyMap 1
          ⟨D.bandToOrderThreeCoverSource, D.bandToOrderThreeCoverSource.continuous⟩ x)
  degreeTwo : ∀ x : IntegralSingularHomology 2 (AdditiveTorus D.bandParameter),
    (orderFourCentralFiberCoverSourceHomologyBasis A.periods).degreeTwo
        (integralSingularHomologyMap 2
          ⟨D.bandToOrderFourCoverSource, D.bandToOrderFourCoverSource.continuous⟩ x) =
      (orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeTwo
        (integralSingularHomologyMap 2
          ⟨D.bandToOrderThreeCoverSource, D.bandToOrderThreeCoverSource.continuous⟩ x)

namespace EllipticBandHomologyAlignment

def bandOne :
    IntegralSingularHomology 1
        (D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior) ≃+
      (Fin 4 → ℤ) :=
  (D.bandHomologyEquiv 1).trans <|
    (integralSingularHomologyEquiv 1 D.bandToOrderThreeCoverSource).trans
      (orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeOne

def bandTwo :
    IntegralSingularHomology 2
        (D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior) ≃+
      (Fin 6 → ℤ) :=
  (D.bandHomologyEquiv 2).trans <|
    (integralSingularHomologyEquiv 2 D.bandToOrderThreeCoverSource).trans
      (orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeTwo

theorem integralHomologyMap_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (k : ℕ) (f : C(X, Y)) (g : C(Y, Z)) :
    integralSingularHomologyMap k (g.comp f) =
      (integralSingularHomologyMap k g).comp (integralSingularHomologyMap k f) := by
  ext x
  change ConcreteCategory.hom
      (((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom (g.comp f))) x = _
  rw [(show TopCat.ofHom (g.comp f) = TopCat.ofHom f ≫ TopCat.ofHom g by rfl),
    Functor.map_comp]
  rfl

end EllipticBandHomologyAlignment

end Geometry.AnalyticData

end SphereSixComplex
