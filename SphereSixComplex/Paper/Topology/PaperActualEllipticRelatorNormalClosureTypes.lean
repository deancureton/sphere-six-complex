module

public import SphereSixComplex.Paper.Topology.AffineVanKampenTransport
public import SphereSixComplex.Paper.Topology.EstablishedBasedVanKampen
public import SphereSixComplex.Paper.Topology.PaperActualEllipticCanonicalFiniteMarking

/-!
# Elliptic filling relators and overlap surjectivity

The chosen cyclic covers identify the physical filling relators and show that the filling maps
kill them. Surjectivity of the deck homomorphisms gives surjectivity on fundamental groups.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex.LatticeData SphereSixComplex.Topology
open SphereSixComplex.Topology.PaperVanKampenFourPieceCover

variable (A : AnalyticData)

public theorem ellipticThreeCanonicalChosenCover_fillingBase_eq :
    A.ellipticThreeCanonicalChosenCover.fillingBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem.2⟩ :=
  A.ellipticThreeFillingMarkedDeckData.toExtensionAtBase
    |>.toChosenCover_fillingBase_eq

public theorem ellipticFourCanonicalChosenCover_fillingBase_eq :
    A.ellipticFourCanonicalChosenCover.fillingBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem.2⟩ :=
  A.ellipticFourFillingExtensionAtBase
    |>.toChosenCover_fillingBase_eq

public theorem ellipticThreeCanonicalChosenCover_map_eq :
    fundamentalGroupHomOfBaseEq
        A.ellipticThreeCanonicalChosenCover_boundaryBase_eq
        A.ellipticThreeCanonicalChosenCover_fillingBase_eq
        A.ellipticThreeCanonicalChosenCover.fundamentalGroupMap =
      A.actualVanKampenFourPieceCover.ellipticThreeOverlapFundamentalGroupMap :=
  fundamentalGroupHomOfBaseEq_map_transport
    A.actualVanKampenFourPieceCover.ellipticThreeOverlapToPiece
    A.ellipticThreeCanonicalChosenCover_boundaryBase_eq
    A.ellipticThreeCanonicalChosenCover_fillingBase_eq

public theorem ellipticFourCanonicalChosenCover_map_eq :
    fundamentalGroupHomOfBaseEq
        A.ellipticFourCanonicalChosenCover_boundaryBase_eq
        A.ellipticFourCanonicalChosenCover_fillingBase_eq
        A.ellipticFourCanonicalChosenCover.fundamentalGroupMap =
      A.actualVanKampenFourPieceCover.ellipticFourOverlapFundamentalGroupMap :=
  fundamentalGroupHomOfBaseEq_map_transport
    A.actualVanKampenFourPieceCover.ellipticFourOverlapToPiece
    A.ellipticFourCanonicalChosenCover_boundaryBase_eq
    A.ellipticFourCanonicalChosenCover_fillingBase_eq

/-- The sign-correct order-three filling relator in the actual overlap fundamental group. -/
public noncomputable def ellipticThreeCanonicalRelator :
    FundamentalGroup
        (A.actualVanKampenFourPieceCover.core ∩
          A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace)
        ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
          A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩ :=
  (fundamentalGroupElementOfBaseEq
      A.ellipticThreeCanonicalChosenCover_boundaryBase_eq
      A.ellipticThreeCanonicalChosenCover.meridian) ^ 3 *
    (Additive.toMul
      ((fundamentalGroupAddHomOfBaseEq
        A.ellipticThreeCanonicalChosenCover_boundaryBase_eq
        A.ellipticThreeCanonicalChosenCover.translation) (-epsilon)))⁻¹

/-- The sign-correct order-four filling relator in the actual overlap fundamental group. -/
public noncomputable def ellipticFourCanonicalRelator :
    FundamentalGroup
        (A.actualVanKampenFourPieceCover.core ∩
          A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace)
        ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
          A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩ :=
  (fundamentalGroupElementOfBaseEq
      A.ellipticFourCanonicalChosenCover_boundaryBase_eq
      A.ellipticFourCanonicalChosenCover.meridian) ^ 4 *
    (Additive.toMul
      ((fundamentalGroupAddHomOfBaseEq
        A.ellipticFourCanonicalChosenCover_boundaryBase_eq
        A.ellipticFourCanonicalChosenCover.translation) epsilon'))⁻¹

public theorem ellipticThreeCanonicalRelator_killed :
    A.actualVanKampenFourPieceCover.ellipticThreeOverlapFundamentalGroupMap
        A.ellipticThreeCanonicalRelator = 1 := by
  rw [← A.ellipticThreeCanonicalChosenCover_map_eq]
  exact chosenCyclicRelation_killed
    A.ellipticThreeCanonicalChosenCover
    A.ellipticThreeCanonicalChosenCover_boundaryBase_eq
    A.ellipticThreeCanonicalChosenCover_fillingBase_eq rfl

public theorem ellipticFourCanonicalRelator_killed :
    A.actualVanKampenFourPieceCover.ellipticFourOverlapFundamentalGroupMap
        A.ellipticFourCanonicalRelator = 1 := by
  rw [← A.ellipticFourCanonicalChosenCover_map_eq]
  exact chosenCyclicRelation_killed
    A.ellipticFourCanonicalChosenCover
    A.ellipticFourCanonicalChosenCover_boundaryBase_eq
    A.ellipticFourCanonicalChosenCover_fillingBase_eq rfl

public theorem ellipticThreeOverlapFundamentalGroupMap_surjective :
    Function.Surjective
      A.actualVanKampenFourPieceCover.ellipticThreeOverlapFundamentalGroupMap := by
  rw [← A.ellipticThreeCanonicalChosenCover_map_eq]
  exact fundamentalGroupHomOfBaseEq_surjective
    A.ellipticThreeCanonicalChosenCover_boundaryBase_eq
    A.ellipticThreeCanonicalChosenCover_fillingBase_eq
    A.ellipticThreeCanonicalChosenCover.fundamentalGroupMap
    A.ellipticThreeCanonicalChosenCover.fundamentalGroupMap_surjective

public theorem ellipticFourOverlapFundamentalGroupMap_surjective :
    Function.Surjective
      A.actualVanKampenFourPieceCover.ellipticFourOverlapFundamentalGroupMap := by
  rw [← A.ellipticFourCanonicalChosenCover_map_eq]
  exact fundamentalGroupHomOfBaseEq_surjective
    A.ellipticFourCanonicalChosenCover_boundaryBase_eq
    A.ellipticFourCanonicalChosenCover_fillingBase_eq
    A.ellipticFourCanonicalChosenCover.fundamentalGroupMap
    A.ellipticFourCanonicalChosenCover.fundamentalGroupMap_surjective


end SphereSixComplex.Geometry.AnalyticData

end

end
