module

public import SphereSixComplex.Elliptic.Cover.MarkedRadialFillingExtension

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.CyclicAngularFundamentalDomain

variable (A : AnalyticData)

/-- The canonical chosen order-three filling cover produced by the explicit radial action and
lift. -/
public noncomputable def ellipticThreeCanonicalChosenCover :=
  A.ellipticThreeFillingMarkedDeckData.toExtensionAtBase.toChosenCover

/-- The canonical chosen order-four filling cover produced by the explicit radial action and
lift. -/
public noncomputable def ellipticFourCanonicalChosenCover :=
  A.ellipticFourFillingExtensionAtBase.toChosenCover

public theorem ellipticThreeCanonicalChosenCover_boundaryBase_eq :
    A.ellipticThreeCanonicalChosenCover.boundaryBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩ :=
  A.ellipticThreeFillingMarkedDeckData.toExtensionAtBase
    |>.toChosenCover_boundaryBase_eq

public theorem ellipticFourCanonicalChosenCover_boundaryBase_eq :
    A.ellipticFourCanonicalChosenCover.boundaryBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩ :=
  A.ellipticFourFillingExtensionAtBase
    |>.toChosenCover_boundaryBase_eq














end SphereSixComplex.Geometry.AnalyticData
