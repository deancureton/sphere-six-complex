module

public import SphereSixComplex.Topology.BoundarySevenCechGlobalComparison

/-!
# Low-degree assembly for the boundary-seven Cech comparison

This file isolates the three genuinely global steps left in the Cech comparison: rowwise
globalization (including the pointwise-limit coherence), a strict chain-level section of the
simplicial-face Cech augmentation, and the low-degree comparison of the two Cech totals.

The definitions below are deliberately expressed using the actual bicomplexes and maps from
`BoundarySevenCechGlobalComparison`, rather than replacing either step by an informal
"spectral sequence" hypothesis.  We also prove that the two quasi-isomorphism fields for the
strict section in `BoundarySevenCechLowAssemblyInput` are redundant: they follow formally
from the section equation and the corresponding assertion for the augmentation.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Simplicial

namespace SphereSixComplex

/-- The horizontal chain complex obtained from a first-quadrant bicomplex by evaluating its
vertical chain-complex entries in degree `q`. -/
public noncomputable def firstQuadrantHorizontalRow
    (K : FirstQuadrantBicomplex) (q : ℕ) : FirstQuadrantChainComplex :=
  ((HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) q).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj K

/-- Evaluation of a bicomplex map on a horizontal row. -/
public noncomputable def firstQuadrantHorizontalRowMap
    {K L : FirstQuadrantBicomplex} (f : K ⟶ L) (q : ℕ) :
    firstQuadrantHorizontalRow K q ⟶ firstQuadrantHorizontalRow L q :=
  ((HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) q).mapHomologicalComplex
    (ComplexShape.down ℕ)).map f

/-- The exact generic homological-algebra statement needed to totalize the existing row
contractions.  It is kept as a proposition, not an axiom or typeclass, so downstream results
must display this missing proof as an explicit argument.

For first-quadrant direct-sum totals this follows from the finite brutal-column filtration:
each total degree sees only finitely many columns. -/
public def FirstQuadrantRowwiseTotalization : Prop :=
  ∀ {K L : FirstQuadrantBicomplex} (f : K ⟶ L),
    (∀ q : ℕ, QuasiIso (firstQuadrantHorizontalRowMap f q)) →
      QuasiIso (HomologicalComplex₂.total.map f (ComplexShape.down ℕ))

/-- A strict right inverse to the simplicial-face total augmentation.  This is the exact
chain-level datum which cannot be recovered merely by choosing inverses on homology. -/
public structure BoundarySevenCechStrictSourceSplit where
  sourceLift :
    (∂Δ[7] : SSet.{0}).chainComplex (AddCommGrpCat.of ℤ) ⟶
      boundarySevenSimplicialFaceCechTotal
  sourceLift_fac :
    sourceLift ≫ boundarySevenSimplicialFaceCechTotalAugmentation = 𝟙 _

/-- The remaining comparison for the map between the two Cech totals.  Its proof is the
finite-coproduct decomposition of the ordered intersections, followed by the local comparison
theorems and rowwise totalization. -/
public structure BoundarySevenFaceCechTotalLowComparison where
  quasiIsoAt_two : QuasiIsoAt boundarySevenFaceCechTotalMap 2
  quasiIsoAt_three : QuasiIsoAt boundarySevenFaceCechTotalMap 3

/-- The coherence isomorphisms identifying evaluation of the two constructed Cech
bicomplexes with the separately constructed evaluated Cech nerves.  These isomorphisms are
canonical pointwise-limit comparisons, but they are not definitional equalities: the Cech
nerve contains wide pullbacks in a functor category. -/
public structure BoundarySevenCechAugmentationRowIdentifications where
  sourceRowArrowIso (q : ℕ) :
    Arrow.mk (firstQuadrantHorizontalRowMap
      boundarySevenSimplicialFaceCechOuterAugmentation q) ≅
      Arrow.mk (AlternatingFaceMapComplex.ε.app
        (boundarySevenSimplicialFaceIntegralEvaluationCech q))
  targetRowArrowIso (q : ℕ) :
    Arrow.mk (firstQuadrantHorizontalRowMap
      boundarySevenFaceNeighborhoodCechOuterAugmentation q) ≅
      Arrow.mk (boundarySevenFaceNeighborhoodCechOuterAugmentationRow q)

/-- The single homological-algebra/coherence package needed to globalize the already-proved
row contractions.  Its first field is the brutal-prefix theorem, and its second field records
the pointwise wide-pullback comparisons needed to apply that theorem to the actual Cech
bicomplexes. -/
public structure BoundarySevenCechRowwiseGlobalization where
  totalization : FirstQuadrantRowwiseTotalization
  rowIdentifications : BoundarySevenCechAugmentationRowIdentifications

/-- A section of a quasi-isomorphism in one degree is automatically a quasi-isomorphism in
that degree. -/
public theorem quasiIsoAt_of_strict_section
    {K L : FirstQuadrantChainComplex} (s : K ⟶ L) (p : L ⟶ K)
    (fac : s ≫ p = 𝟙 K) (n : ℕ) [QuasiIsoAt p n] : QuasiIsoAt s n := by
  haveI : QuasiIsoAt (s ≫ p) n := by
    rw [fac]
    infer_instance
  exact quasiIsoAt_of_comp_right s p n

/-- Rowwise totalization turns the already-proved source row augmentations into a global
quasi-isomorphism of total complexes. -/
public theorem boundarySevenSimplicialFaceCechTotalAugmentation_quasiIso
    (hrow : FirstQuadrantRowwiseTotalization)
    (hident : BoundarySevenCechAugmentationRowIdentifications) :
    QuasiIso boundarySevenSimplicialFaceCechTotalAugmentation := by
  let T := HomologicalComplex₂.total.map
    boundarySevenSimplicialFaceCechOuterAugmentation (ComplexShape.down ℕ)
  have hT : QuasiIso T := by
    apply hrow boundarySevenSimplicialFaceCechOuterAugmentation
    intro q
    letI : QuasiIso (AlternatingFaceMapComplex.ε.app
        (boundarySevenSimplicialFaceIntegralEvaluationCech q)) :=
      boundarySevenSimplicialFaceIntegralCechRowAugmentation_quasiIso q
    exact quasiIso_of_arrow_mk_iso
      (AlternatingFaceMapComplex.ε.app
        (boundarySevenSimplicialFaceIntegralEvaluationCech q))
      (firstQuadrantHorizontalRowMap
        boundarySevenSimplicialFaceCechOuterAugmentation q)
      (hident.sourceRowArrowIso q).symm
  have hP : QuasiIso (firstQuadrantTotalToSingleZero
      ((∂Δ[7] : SSet.{0}).chainComplex (AddCommGrpCat.of ℤ))) := by
    letI : IsIso (firstQuadrantTotalToSingleZero
        ((∂Δ[7] : SSet.{0}).chainComplex (AddCommGrpCat.of ℤ))) :=
      (firstQuadrantSingleZeroTotalIso
        ((∂Δ[7] : SSet.{0}).chainComplex (AddCommGrpCat.of ℤ))).isIso_hom
    infer_instance
  exact quasiIso_comp T _

/-- Rowwise totalization likewise promotes the existing neighbourhood-row contractions to
the actual totalized neighbourhood Cech augmentation. -/
public theorem boundarySevenFaceNeighborhoodCechTotalAugmentation_quasiIso
    (hrow : FirstQuadrantRowwiseTotalization)
    (hident : BoundarySevenCechAugmentationRowIdentifications) :
    QuasiIso boundarySevenFaceNeighborhoodCechTotalAugmentation := by
  let T := HomologicalComplex₂.total.map
    boundarySevenFaceNeighborhoodCechOuterAugmentation (ComplexShape.down ℕ)
  have hT : QuasiIso T := by
    apply hrow boundarySevenFaceNeighborhoodCechOuterAugmentation
    intro q
    letI : QuasiIso (boundarySevenFaceNeighborhoodCechOuterAugmentationRow q) :=
      boundarySevenFaceNeighborhoodCechOuterAugmentationRow_quasiIso q
    exact quasiIso_of_arrow_mk_iso
      (boundarySevenFaceNeighborhoodCechOuterAugmentationRow q)
      (firstQuadrantHorizontalRowMap
        boundarySevenFaceNeighborhoodCechOuterAugmentation q)
      (hident.targetRowArrowIso q).symm
  have hP : QuasiIso (firstQuadrantTotalToSingleZero
      (CoverSmallIntegralSingularChainComplex
        (SSet.toTop.obj (∂Δ[7] : SSet.{0}))
        boundarySevenComparisonFaceNeighborhood)) := by
    letI : IsIso (firstQuadrantTotalToSingleZero
        (CoverSmallIntegralSingularChainComplex
          (SSet.toTop.obj (∂Δ[7] : SSet.{0}))
          boundarySevenComparisonFaceNeighborhood)) :=
      (firstQuadrantSingleZeroTotalIso
        (CoverSmallIntegralSingularChainComplex
          (SSet.toTop.obj (∂Δ[7] : SSet.{0}))
          boundarySevenComparisonFaceNeighborhood)).isIso_hom
    infer_instance
  exact quasiIso_comp T _

/-- Once the generic first-quadrant theorem, the strict source split, and the geometric
comparison of the two Cech totals are supplied, all eight fields of the original low-assembly
package are canonical.  In particular, no separate proof about the source lift on homology is
needed. -/
public noncomputable def boundarySevenCechLowAssemblyInput_of_global_steps
    (hglobal : BoundarySevenCechRowwiseGlobalization)
    (hsplit : BoundarySevenCechStrictSourceSplit)
    (hcech : BoundarySevenFaceCechTotalLowComparison) :
    BoundarySevenCechLowAssemblyInput where
  sourceLift := hsplit.sourceLift
  sourceLift_fac := hsplit.sourceLift_fac
  sourceLift_quasiIsoAt_two := by
    letI : QuasiIso boundarySevenSimplicialFaceCechTotalAugmentation :=
      boundarySevenSimplicialFaceCechTotalAugmentation_quasiIso
        hglobal.totalization hglobal.rowIdentifications
    exact quasiIsoAt_of_strict_section hsplit.sourceLift
      boundarySevenSimplicialFaceCechTotalAugmentation hsplit.sourceLift_fac 2
  sourceLift_quasiIsoAt_three := by
    letI : QuasiIso boundarySevenSimplicialFaceCechTotalAugmentation :=
      boundarySevenSimplicialFaceCechTotalAugmentation_quasiIso
        hglobal.totalization hglobal.rowIdentifications
    exact quasiIsoAt_of_strict_section hsplit.sourceLift
      boundarySevenSimplicialFaceCechTotalAugmentation hsplit.sourceLift_fac 3
  cechMap_quasiIsoAt_two := hcech.quasiIsoAt_two
  cechMap_quasiIsoAt_three := hcech.quasiIsoAt_three
  augmentation_quasiIsoAt_two := by
    letI : QuasiIso boundarySevenFaceNeighborhoodCechTotalAugmentation :=
      boundarySevenFaceNeighborhoodCechTotalAugmentation_quasiIso
        hglobal.totalization hglobal.rowIdentifications
    infer_instance
  augmentation_quasiIsoAt_three := by
    letI : QuasiIso boundarySevenFaceNeighborhoodCechTotalAugmentation :=
      boundarySevenFaceNeighborhoodCechTotalAugmentation_quasiIso
        hglobal.totalization hglobal.rowIdentifications
    infer_instance

/-- Exact final residual for the current Cech route.  It records, without disguising any
obligation, that rowwise globalization, the strict face-resolution split, and
the ordered-intersection comparison together construct the requested assembly input. -/
public theorem boundarySevenCechLowAssemblyInput_of_exact_residual
    (hglobal : BoundarySevenCechRowwiseGlobalization)
    (hsplit : BoundarySevenCechStrictSourceSplit)
    (hcech : BoundarySevenFaceCechTotalLowComparison) :
    Nonempty BoundarySevenCechLowAssemblyInput :=
  ⟨boundarySevenCechLowAssemblyInput_of_global_steps hglobal hsplit hcech⟩

end SphereSixComplex
