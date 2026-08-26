module

public import SphereSixComplex.Topology.EstablishedPaperSectionSevenAffineRegularLiftCompletion

/-!
# Established affine radial completion for Section 7

The two finite-monodromy filling collars extend through their allocated affine sides by the
equivariant radial homotopies of the cyclic quotient models.  On the common central band these
extensions agree, up to homotopy, with the two canonical reduced-fibre cover projections.  This
is the point-set-topological content left after the explicit height split and radial filling
models have been constructed.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

namespace EstablishedSectionSevenAffineTopology

/-- Equivariant radial extension across the two actual affine filling collars, including its
compatibility with the canonical maps on their common band. -/
public theorem radialCompletionInput (A : PaperAnalyticData) :
    Nonempty A.SectionSevenAffineRadialCompletionInput :=
  EstablishedSectionSevenAffineRegularLiftTopology.radialCompletionInput_nonempty A

end EstablishedSectionSevenAffineTopology

/-- The coherent radial completion selected for the paper's actual affine height split. -/
public theorem sectionSevenAffineRadialCompletionInput (A : PaperAnalyticData) :
    A.SectionSevenAffineRadialCompletionInput :=
  Classical.choice (EstablishedSectionSevenAffineTopology.radialCompletionInput A)

end SphereSixComplex.Geometry.PaperAnalyticData
