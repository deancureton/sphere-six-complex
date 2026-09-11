module

public import SphereSixComplex.Prerequisites.Topology.FiniteOpenCoverLerayComparison
public import SphereSixComplex.Paper.Topology.SectionSevenCoherentRealizationReduction

@[expose] public section
noncomputable section
open AlgebraicTopology CategoryTheory CategoryTheory.Limits Set Simplicial
namespace SphereSixComplex

section SectionSevenReduction

variable {X : Type} [TopologicalSpace X] {C : FourPieceOpenCover X}

/-- A chain homotopy equivalence with the Čech total gives a small-chain comparison. -/
public noncomputable def SectionSevenFourPieceSmallChainComparison.ofCechHomotopyEquiv
    (h : HomotopyEquiv (sectionSevenLerayChainModel (-1))
      (finiteCoverLerayCechTotal C.piece)) :
    SectionSevenFourPieceSmallChainComparison X C := by
  let e := finiteOpenCoverLerayCechComparison
    C.piece C.isOpen_piece C.covers
  refine
    { comparison := h.hom ≫ e.augmentation
      quasiIso := ?_ }
  let _ : QuasiIso h.hom := by
    rw [quasiIso_iff]
    intro k
    rw [quasiIsoAt_iff_isIso_homologyMap]
    change IsIso ((h.toHomologyIso k).hom)
    infer_instance
  let _ : QuasiIso e.augmentation := e.quasiIso
  infer_instance


end SectionSevenReduction

end SphereSixComplex
