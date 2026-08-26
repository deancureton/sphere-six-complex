module

public import SphereSixComplex.Topology.PaperSectionSevenAffineMarkedBandSquares
public import SphereSixComplex.Topology.PaperSectionSevenAffineOrderThreeRadialEquivalence
public import SphereSixComplex.Topology.PaperSectionSevenAffineOrderFourRadialEquivalence

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

/-- The remaining affine point-set input: the two actual overlap quotient identifications between
the star collars and the full-deck-action affine disc lifts.  The lifted radial transport is no
longer assumed; it is supplied by `exists_orderThreeAffineRadialEquiv` and
`exists_orderFourAffineRadialEquiv`. -/
public axiom regularLiftOverlapGeometry (A : PaperAnalyticData) :
    A.SectionSevenAffineOrderThreeOverlapQuotientIdentification ×
      A.SectionSevenAffineOrderFourOverlapQuotientIdentification

/-- The two classical full-deck-action affine radial constructions, assembled from the overlap
quotient identifications and the proved lifted radial equivalences. -/
public noncomputable def regularLiftGeometry (A : PaperAnalyticData) :
    A.SectionSevenAffineOrderThreeRegularLiftInput ×
      A.SectionSevenAffineOrderFourRegularLiftInput :=
  let Q3 := (regularLiftOverlapGeometry A).1
  let Q4 := (regularLiftOverlapGeometry A).2
  let h3 := A.exists_orderThreeAffineRadialEquiv
    (Q3.normalizationRadius_pos.trans Q3.normalizationRadius_lt_disc)
    Q3.affineDiscRadius_le_halfPlane
  let h4 := A.exists_orderFourAffineRadialEquiv
    (Q4.normalizationRadius_pos.trans Q4.normalizationRadius_lt_disc)
    Q4.affineDiscRadius_le_halfPlane
  (SectionSevenAffineOrderThreeOverlapQuotientIdentification.toRegularLiftInput A Q3
      h3.choose h3.choose_spec,
    SectionSevenAffineOrderFourOverlapQuotientIdentification.toRegularLiftInput A Q4
      h4.choose h4.choose_spec)

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
