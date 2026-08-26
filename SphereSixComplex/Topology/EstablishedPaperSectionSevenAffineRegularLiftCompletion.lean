module

public import SphereSixComplex.Topology.PaperSectionSevenAffineMarkedBandSquares

/-!
# Established regular-cover input for the affine completion

The paper's remaining affine topology is recorded through the genuine regular-family deck action,
not as an opaque side-equivalence package.  The two inputs below separate the lifted radial and
quotient geometry from the marked central-band homotopies.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

namespace EstablishedSectionSevenAffineRegularLiftTopology

/-- The two classical full-deck-action affine radial constructions.  The already-derived central
quotient models are not repeated here; these records retain only the lifted radial transport and
the actual overlap quotient identifications that remain to be connected to the star collars. -/
public axiom regularLiftGeometry (A : PaperAnalyticData) :
    A.SectionSevenAffineOrderThreeRegularLiftInput ×
      A.SectionSevenAffineOrderFourRegularLiftInput

/-- The paper's two explicit marked projection squares for the fixed regular-cover contractions.
Each target is the named quotient projection of the selected actual central-band fibre coordinate. -/
public axiom markedProjectionSquares (A : PaperAnalyticData) :
    A.SectionSevenAffineRegularLiftMarkedProjectionSquares
      (regularLiftGeometry A).1 (regularLiftGeometry A).2

/-- The explicit marked projection squares imply the former compatibility interface. -/
public theorem markedBandCompatibility (A : PaperAnalyticData) :
    A.SectionSevenAffineRegularLiftBandCompatibilityInput
      (regularLiftGeometry A).1 (regularLiftGeometry A).2 :=
  (markedProjectionSquares A).toBandCompatibility

/-- Assemble the explicit regular-cover completion package from its separated geometric and
marked-homotopy inputs. -/
public def regularLiftCompletionInput (A : PaperAnalyticData) :
    A.SectionSevenAffineRegularLiftCompletionInput :=
  (markedBandCompatibility A).toCompletionInput

/-- Exact drop-in replacement for the former broad radial-completion existence assumption. -/
public theorem radialCompletionInput_nonempty
    (A : PaperAnalyticData) :
    Nonempty A.SectionSevenAffineRadialCompletionInput :=
  ⟨(regularLiftCompletionInput A).toRadialCompletion⟩

end EstablishedSectionSevenAffineRegularLiftTopology

/-- The affine radial package selected from the explicit regular-cover construction. -/
public theorem establishedSectionSevenAffineRadialCompletionInput
    (A : PaperAnalyticData) :
    A.SectionSevenAffineRadialCompletionInput :=
  (EstablishedSectionSevenAffineRegularLiftTopology.regularLiftCompletionInput A)
    |>.toRadialCompletion

end SphereSixComplex.Geometry.PaperAnalyticData

end
