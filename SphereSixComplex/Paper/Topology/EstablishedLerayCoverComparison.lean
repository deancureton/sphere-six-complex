module

public import SphereSixComplex.Prerequisites.Topology.FiniteOpenCoverLerayComparison
public import SphereSixComplex.Paper.Topology.SectionSevenCoherentRealizationReduction

@[expose] public section
noncomputable section
open AlgebraicTopology CategoryTheory CategoryTheory.Limits Set Simplicial
namespace SphereSixComplex

section SectionSevenReduction

variable {X : Type} [TopologicalSpace X] {C : FourPieceOpenCover X}

/-- A strong chain-level comparison with the finite algebraic model.  This is sufficient for the
general cover theorem, but it is not asserted by Section 7 of the paper: the paper computes a
Leray spectral sequence rather than a contraction of the four-piece Cech total. -/
public structure SectionSevenLerayCechIdentification
    (X : Type) [TopologicalSpace X] (C : FourPieceOpenCover X) where
  identification : HomotopyEquiv (sectionSevenLerayChainModel (-1))
    (finiteCoverLerayCechTotal C.piece)

namespace SectionSevenLerayCechIdentification

/-- Explicit intersection-chain equivalences and matrix compatibility, packaged as the
identification above, imply the paper-specific small-chain comparison. -/
public noncomputable def toFourPieceSmallChainComparison
    (h : SectionSevenLerayCechIdentification X C) :
    SectionSevenFourPieceSmallChainComparison X C := by
  let e := establishedFiniteOpenCoverLerayCechComparison
    C.piece C.isOpen_piece C.covers
  refine
    { comparison := h.identification.hom ≫ e.augmentation
      quasiIso := ?_ }
  let _ : QuasiIso h.identification.hom := by
    rw [quasiIso_iff]
    intro k
    rw [quasiIsoAt_iff_isIso_homologyMap]
    change IsIso ((h.identification.toHomologyIso k).hom)
    infer_instance
  let _ : QuasiIso e.augmentation := e.quasiIso
  infer_instance

end SectionSevenLerayCechIdentification

end SectionSevenReduction

end SphereSixComplex
