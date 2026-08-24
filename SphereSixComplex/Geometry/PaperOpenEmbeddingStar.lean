module

public import SphereSixComplex.Geometry.OpenEmbeddingStarGluing
public import SphereSixComplex.Geometry.PaperCollarSeparation

/-!
# The concrete four-piece open-embedding star

This module packages the cusp and two elliptic collars, at the simultaneously separated radii,
as the common-source open embeddings used by the topological star gluing.
-/

open CategoryTheory TopologicalSpace Topology

namespace SphereSixComplex.Geometry

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open CuspPuncturedCollarBridge EllipticPuncturedCollarGaugeHomeomorph
open EllipticVaryingFamilyQuotient EllipticLogarithmicGaugeDescent
open EllipticLinearCollarGlobalDescent
open EquivariantQuotientHomeomorph

noncomputable section

namespace PaperAnalyticData

variable (A : PaperAnalyticData)

public noncomputable abbrev starCuspWitness := A.actualPuncturedCuspWitness
public noncomputable abbrev starSeparation := A.collarSeparationData

/-- The cusp filling followed by the order-three and order-four varying fillings. -/
@[expose] public noncomputable def starFillingType : Fin 3 → Type :=
  Fin.cases (actualLocalCuspFilling A.starCuspWitness) fun i ↦
    Fin.cases (A.OrderThreeVaryingFilling A.starSeparation.orderThree.radius)
      (fun _ ↦ A.OrderFourVaryingFilling A.starSeparation.orderFour.radius) i

/-- The three common collar-source quotients. -/
@[expose] public noncomputable def starCollarSourceType : Fin 3 → Type :=
  Fin.cases (puncturedLocalCuspQuotient A.starCuspWitness) fun i ↦
    Fin.cases
      (Quotient (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods)
        (orderThreeAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction
          A.starSeparation.orderThree.radius)))
      (fun _ ↦ Quotient (restrictedOrbitRel (orderFourAffineFamilyAction A.periods)
        (orderFourAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction
          A.starSeparation.orderFour.radius))) i

public noncomputable instance starFillingTopology (i : Fin 3) :
    TopologicalSpace (A.starFillingType i) := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change TopologicalSpace (actualLocalCuspFilling A.starCuspWitness)
    infer_instance
  · refine Fin.cases ?_ (fun _ ↦ ?_) j
    · change TopologicalSpace
        (A.OrderThreeVaryingFilling A.starSeparation.orderThree.radius)
      infer_instance
    · change TopologicalSpace
        (A.OrderFourVaryingFilling A.starSeparation.orderFour.radius)
      infer_instance

public noncomputable instance starCollarSourceTopology (i : Fin 3) :
    TopologicalSpace (A.starCollarSourceType i) := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change TopologicalSpace (puncturedLocalCuspQuotient A.starCuspWitness)
    infer_instance
  · refine Fin.cases ?_ (fun _ ↦ ?_) j
    · change TopologicalSpace (Quotient (restrictedOrbitRel
        (orderThreeAffineFamilyAction A.periods)
        (orderThreeAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction
          A.starSeparation.orderThree.radius)))
      infer_instance
    · change TopologicalSpace (Quotient (restrictedOrbitRel
        (orderFourAffineFamilyAction A.periods)
        (orderFourAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction
          A.starSeparation.orderFour.radius)))
      infer_instance

/-- The three collar maps into the punctured global family. -/
@[expose] public noncomputable def starToCentral :
    ∀ i, A.starCollarSourceType i → A.CentralFamily :=
  Fin.cases (puncturedLocalCuspQuotientMap A.starCuspWitness) fun i ↦
    Fin.cases
      (A.orderThreePuncturedCollarToCentralFamily
        A.starSeparation.orderThree.sourceData)
      (fun _ ↦ A.orderFourPuncturedCollarToCentralFamily
        A.starSeparation.orderFour.sourceData) i

/-- The three collar maps into their filling pieces. -/
@[expose] public noncomputable def starToFilling :
    ∀ i, A.starCollarSourceType i → A.starFillingType i :=
  Fin.cases (puncturedLocalCuspToFilling A.starCuspWitness) fun i ↦
    Fin.cases
      (A.orderThreePuncturedCollarToFilling A.starSeparation.orderThree.radius)
      (fun _ ↦ A.orderFourPuncturedCollarToFilling A.starSeparation.orderFour.radius) i

public theorem starToCentral_isOpenEmbedding (i : Fin 3) :
    IsOpenEmbedding (A.starToCentral i) := by
  fin_cases i
  · exact puncturedLocalCuspQuotientMap_isOpenEmbedding A.starCuspWitness
  · exact A.orderThreePuncturedCollarToCentralFamily_isOpenEmbedding
      A.starSeparation.orderThree.sourceData
  · exact A.orderFourPuncturedCollarToCentralFamily_isOpenEmbedding
      A.starSeparation.orderFour.sourceData

public theorem starToFilling_isOpenEmbedding (i : Fin 3) :
    IsOpenEmbedding (A.starToFilling i) := by
  fin_cases i
  · exact puncturedLocalCuspToFilling_isOpenEmbedding A.starCuspWitness
  · exact A.orderThreePuncturedCollarToFilling_isOpenEmbedding
      A.starSeparation.orderThree.radius
  · exact A.orderFourPuncturedCollarToFilling_isOpenEmbedding
      A.starSeparation.orderFour.radius

public theorem starToCentral_ranges_pairwise : Pairwise fun i j ↦
    Disjoint (Set.range (A.starToCentral i)) (Set.range (A.starToCentral j)) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · simp at hij
  · exact A.starSeparation.cusp_orderThree_centralRanges_disjoint
  · exact A.starSeparation.cusp_orderFour_centralRanges_disjoint
  · exact A.starSeparation.cusp_orderThree_centralRanges_disjoint.symm
  · simp at hij
  · exact A.starSeparation.elliptic_centralRanges_disjoint
  · exact A.starSeparation.cusp_orderFour_centralRanges_disjoint.symm
  · exact A.starSeparation.elliptic_centralRanges_disjoint.symm
  · simp at hij

/-- The actual cusp and elliptic collars, as a concrete common-source star. -/
@[expose] public noncomputable def openEmbeddingStarData :
    SphereSixComplex.OpenEmbeddingStarData where
  central := TopCat.of A.CentralFamily
  filling i := TopCat.of (A.starFillingType i)
  collarSource i := TopCat.of (A.starCollarSourceType i)
  toCentral i := TopCat.ofHom ⟨A.starToCentral i,
    (A.starToCentral_isOpenEmbedding i).continuous⟩
  toFilling i := TopCat.ofHom ⟨A.starToFilling i,
    (A.starToFilling_isOpenEmbedding i).continuous⟩
  toCentral_isOpenEmbedding := A.starToCentral_isOpenEmbedding
  toFilling_isOpenEmbedding := A.starToFilling_isOpenEmbedding
  centralRange_disjoint := A.starToCentral_ranges_pairwise

end PaperAnalyticData

end

end SphereSixComplex.Geometry
