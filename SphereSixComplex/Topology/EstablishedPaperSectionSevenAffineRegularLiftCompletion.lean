module

public import SphereSixComplex.Topology.PaperSectionSevenAffineRegularLiftCompletionAssembly

/-!
# Established overlap input for the affine completion

The paper's remaining affine topology is recorded at exactly the level used by the radial
completion: the two overlap inclusions are homotopy equivalences and the induced band maps are
homotopic to the two marked finite-cover projections.  No quotient model or set-level
identification of an overlap with an affine disc is assumed.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

namespace EstablishedSectionSevenAffineRegularLiftTopology

/-- The exact residual affine input from the paper: radial contraction of each actual overlap and
the two marked band homotopies.  The proposition-level assembly theorem shows that this is all the
completion uses. -/
public axiom overlapCompletionInput (A : PaperAnalyticData) :
    A.SectionSevenAffineOverlapCompletionInput

/-- Exact drop-in replacement for the former broad radial-completion existence assumption. -/
public theorem radialCompletionInput_nonempty
    (A : PaperAnalyticData) :
    Nonempty A.SectionSevenAffineRadialCompletionInput :=
  ⟨(overlapCompletionInput A).toRadialCompletion⟩

end EstablishedSectionSevenAffineRegularLiftTopology

/-- The affine radial package selected from the explicit regular-cover construction. -/
public theorem establishedSectionSevenAffineRadialCompletionInput
    (A : PaperAnalyticData) :
    A.SectionSevenAffineRadialCompletionInput :=
  (EstablishedSectionSevenAffineRegularLiftTopology.overlapCompletionInput A).toRadialCompletion

end SphereSixComplex.Geometry.PaperAnalyticData

end
