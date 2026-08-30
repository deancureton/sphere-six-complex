module

public import SphereSixComplex.Topology.CuspMarkedFiberCellularSpecializationProof

/-!
# Chain-level normalization of the marked cusp specialization

The objectwise cellular-homology model used for the cusp carrier does not include a comparison
map to singular chains.  This file records the minimal chain-level compatibility needed to make
its chosen homology equivalence natural, and the factorization of the geometric specialization
through the labelled toric cellular complex.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory

namespace SphereSixComplex

namespace IntegralCWCellularHomologyModel

variable {Y : Type} [TopologicalSpace Y] [Topology.CWComplex (Set.univ : Set Y)]

/-- Relabel the singular-homology side of an objectwise cellular model by arbitrary degreewise
automorphisms.  The cellular complex, its bases, and hence every incidence formula are unchanged.
This witnesses why incidence data alone cannot determine labelled specialization coordinates. -/
public def relabelHomology (M : IntegralCWCellularHomologyModel Y)
    (e : ∀ n, IntegralSingularHomology n Y ≃+ IntegralSingularHomology n Y) :
    IntegralCWCellularHomologyModel Y where
  chainComplex := M.chainComplex
  cellBasis := M.cellBasis
  homologyEquiv n := (M.homologyEquiv n).trans (e n)

@[simp] public theorem relabelHomology_chainComplex (M : IntegralCWCellularHomologyModel Y)
    (e : ∀ n, IntegralSingularHomology n Y ≃+ IntegralSingularHomology n Y) :
    (M.relabelHomology e).chainComplex = M.chainComplex := rfl

@[simp] public theorem relabelHomology_cellBasis (M : IntegralCWCellularHomologyModel Y)
    (e : ∀ n, IntegralSingularHomology n Y ≃+ IntegralSingularHomology n Y) (n : ℕ) :
    (M.relabelHomology e).cellBasis n = M.cellBasis n := rfl

@[simp] public theorem relabelHomology_homologyEquiv_apply
    (M : IntegralCWCellularHomologyModel Y)
    (e : ∀ n, IntegralSingularHomology n Y ≃+ IntegralSingularHomology n Y) (n : ℕ)
    (x : M.chainComplex.homology n) :
    (M.relabelHomology e).homologyEquiv n x = e n (M.homologyEquiv n x) := rfl

end IntegralCWCellularHomologyModel

/-- A comparison map realizing the chosen objectwise cellular homology equivalence.  No
quasi-isomorphism field is needed: it follows from `homologyMap_eq`. -/
public structure CompatibleIntegralCWCellularChainComparison
    {Y : Type} [TopologicalSpace Y] [Topology.CWComplex (Set.univ : Set Y)]
    (M : IntegralCWCellularHomologyModel Y) where
  comparison : M.chainComplex ⟶ IntegralSingularChainComplex Y
  homologyMap_eq : ∀ n, M.chainComplex.homologyMap comparison n =
    (M.homologyEquiv n).toAddCommGrpIso.hom

namespace CompatibleIntegralCWCellularChainComparison

variable {Y : Type} [TopologicalSpace Y] [Topology.CWComplex (Set.univ : Set Y)]
  {M : IntegralCWCellularHomologyModel Y}

/-- Compatibility with the chosen homology equivalence makes the comparison a quasi-isomorphism. -/
public theorem comparison_homology_isIso
    (C : CompatibleIntegralCWCellularChainComparison M) (n : ℕ) :
    IsIso (M.chainComplex.homologyMap C.comparison n) := by
  rw [C.homologyMap_eq]
  exact Iso.isIso_hom (M.homologyEquiv n).toAddCommGrpIso

/-- The compatible comparison is a quasi-isomorphism. -/
public theorem quasiIso (C : CompatibleIntegralCWCellularChainComparison M) :
    QuasiIso C.comparison := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact C.comparison_homology_isIso n

end CompatibleIntegralCWCellularChainComparison

namespace Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}

/-- A chain-level normalization of the actual cusp specialization.  The first field repairs the
missing naturality of the objectwise cellular model.  The second and third fields give one
labelled cellular lift and assert the geometric specialization triangle before passing to
homology. -/
public structure MarkedFiberCellularChainNormalization
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) where
  cellularComparison :
    let C := establishedStandardA2ToricCentralFiberCWDecomposition W R
    let _ := C.topology
    let _ := C.cwComplex
    CompatibleIntegralCWCellularChainComparison C.establishedIntegralCellularChainModel
  cellularSpecialization :
    IntegralSingularChainComplex (puncturedLocalCuspQuotient W) ⟶
      cuspToricCellularChainComplex
  specialization_triangle :
    let C := establishedStandardA2ToricCentralFiberCWDecomposition W R
    let _ := C.topology
    let _ := C.cwComplex
    let I := establishedStandardA2ToricCentralFiberCellularIncidence W R
    cellularSpecialization ≫ I.chainIso.hom ≫ cellularComparison.comparison =
      actualSpecializationToCWCarrierChainMap W R

namespace MarkedFiberCellularChainNormalization

variable {W : ActualPuncturedCuspCollarWitness N M}
  {R : ActualLocalCuspCentralFiberRetractionData W}

/-- The chain map used by the geometric specialization induces the composite homology map used
in `standardA2CellularSpecializationHomologyMap`. -/
public theorem actualSpecializationToCWCarrier_homologyMap_apply (k : ℕ)
    (x : IntegralSingularHomology k (puncturedLocalCuspQuotient W)) :
    let C := establishedStandardA2ToricCentralFiberCWDecomposition W R
    let _ := C.topology
    ConcreteCategory.hom
        ((IntegralSingularChainComplex (puncturedLocalCuspQuotient W)).homologyMap
          (actualSpecializationToCWCarrierChainMap W R) k) x =
      integralSingularHomologyEquivOfHomotopyEquiv k C.homotopyEquiv
        (R.specializationHomologyMap W k
          (integralSingularHomologyMap k
            ⟨puncturedLocalCuspToFilling W, puncturedLocalCuspToFilling_continuous W⟩ x)) := by
  simp only [actualSpecializationToCWCarrierChainMap,
    HomologicalComplex.homologyMap_comp]
  rfl

/-- A normalized chain factorization removes the arbitrary cellular-homology equivalence: the
existing cellular specialization is the map induced by the labelled chain lift. -/
public theorem cellularSpecialization_homologyMap_apply
    (S : MarkedFiberCellularChainNormalization W R) (k : ℕ)
    (x : IntegralSingularHomology k (puncturedLocalCuspQuotient W)) :
    ConcreteCategory.hom
        ((IntegralSingularChainComplex (puncturedLocalCuspQuotient W)).homologyMap
          S.cellularSpecialization k) x =
      standardA2CellularSpecializationHomologyMap W R k x := by
  let C := establishedStandardA2ToricCentralFiberCWDecomposition W R
  let _ := C.topology
  let _ := C.cwComplex
  let I := establishedStandardA2ToricCentralFiberCellularIncidence W R
  let Q := IntegralSingularChainComplex (puncturedLocalCuspQuotient W)
  have htriangle := congrArg (fun f ↦ Q.homologyMap f k) S.specialization_triangle
  simp only [HomologicalComplex.homologyMap_comp] at htriangle
  let eI := asIso (cuspToricCellularChainComplex.homologyMap I.chainIso.hom k)
  let _ := S.cellularComparison.comparison_homology_isIso k
  let eC := asIso
    (C.establishedIntegralCellularChainModel.chainComplex.homologyMap
      S.cellularComparison.comparison k)
  let eM := (C.establishedIntegralCellularChainModel.homologyEquiv k).toAddCommGrpIso
  have hinv : eC.inv = eM.inv := (Iso.inv_eq_inv eC eM).2
    (S.cellularComparison.homologyMap_eq k)
  have hmap : Q.homologyMap S.cellularSpecialization k =
      Q.homologyMap (actualSpecializationToCWCarrierChainMap W R) k ≫ eC.inv ≫ eI.inv := by
    rw [← htriangle]
    change Q.homologyMap S.cellularSpecialization k =
      Q.homologyMap S.cellularSpecialization k ≫ eI.hom ≫ eC.hom ≫ eC.inv ≫ eI.inv
    simp
  rw [hmap]
  rw [hinv]
  change ConcreteCategory.hom eI.inv
      (ConcreteCategory.hom eM.inv
        (ConcreteCategory.hom
          (Q.homologyMap (actualSpecializationToCWCarrierChainMap W R) k) x)) = _
  rw [standardA2CellularSpecializationHomologyMap,
    actualSpecializationToCWCarrier_homologyMap_apply]
  rfl


end MarkedFiberCellularChainNormalization

namespace EstablishedStandardA2CuspSpecialization

open Geometry.PaperAnalyticData
open SphereSixComplex.LatticeWangAlgebra
open WangHomologyPresentation

/-- The map on degree-one coinvariants induced by a labelled chain lift of specialization. -/
public noncomputable def chainLiftCoinvariantHomologyOneMap (A : PaperAnalyticData)
    (S : MarkedFiberCellularChainNormalization A.starCuspWitness
      A.cuspCentralFiberRetractionData) :
    let G :=
      SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
        A.starCuspWitness
    let _ := G.fiberTopology
    (circleMappingTorusHOnePresentation G.clutching).Coinvariants →+
      cuspToricCellularChainComplex.homology 1 := by
  let G :=
    SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
      A.starCuspWitness
  let _ := G.fiberTopology
  let e := integralSingularHomologyEquivOfHomotopyEquiv 1 G.totalHomotopyEquiv
  exact (ConcreteCategory.hom
    ((IntegralSingularChainComplex (puncturedLocalCuspQuotient A.starCuspWitness)).homologyMap
      S.cellularSpecialization 1)).comp
        (e.symm.toAddMonoidHom.comp
          (circleMappingTorusHOnePresentation G.clutching).coinvariantsToTotal.toAddMonoidHom)

/-- The analogous map on degree-two coinvariants. -/
public noncomputable def chainLiftCoinvariantHomologyTwoMap (A : PaperAnalyticData)
    (S : MarkedFiberCellularChainNormalization A.starCuspWitness
      A.cuspCentralFiberRetractionData) :
    let G :=
      SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
        A.starCuspWitness
    let _ := G.fiberTopology
    (circleMappingTorusHTwoPresentation G.clutching).Coinvariants →+
      cuspToricCellularChainComplex.homology 2 := by
  let G :=
    SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
      A.starCuspWitness
  let _ := G.fiberTopology
  let e := integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv
  exact (ConcreteCategory.hom
    ((IntegralSingularChainComplex (puncturedLocalCuspQuotient A.starCuspWitness)).homologyMap
      S.cellularSpecialization 2)).comp
        (e.symm.toAddMonoidHom.comp
          (circleMappingTorusHTwoPresentation G.clutching).coinvariantsToTotal.toAddMonoidHom)

/-- Chain factorization identifies the chain-lift map with the existing objectwise cellular
specialization in degree one. -/
public theorem chainLiftCoinvariantHomologyOneMap_eq (A : PaperAnalyticData)
    (S : MarkedFiberCellularChainNormalization A.starCuspWitness
      A.cuspCentralFiberRetractionData) :
    chainLiftCoinvariantHomologyOneMap A S = markedFiberCellularCoinvariantHomologyOneMap A := by
  ext x
  exact S.cellularSpecialization_homologyMap_apply 1 _

/-- Chain factorization identifies the degree-two maps as well. -/
public theorem chainLiftCoinvariantHomologyTwoMap_eq (A : PaperAnalyticData)
    (S : MarkedFiberCellularChainNormalization A.starCuspWitness
      A.cuspCentralFiberRetractionData) :
    chainLiftCoinvariantHomologyTwoMap A S = markedFiberCellularCoinvariantHomologyTwoMap A := by
  ext x
  exact S.cellularSpecialization_homologyMap_apply 2 _

/-- The unique degree-one cellular map normalized by the labelled Wang coordinates. -/
public noncomputable def normalizedCoinvariantHomologyOneMap (A : PaperAnalyticData) :
    let G :=
      SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
        A.starCuspWitness
    let _ := G.fiberTopology
    (circleMappingTorusHOnePresentation G.clutching).Coinvariants →+
      cuspToricCellularChainComplex.homology 1 := by
  let G :=
    SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
      A.starCuspWitness
  let _ := G.fiberTopology
  exact cuspToricCellularChainComplex_homologyOneEquiv.symm.toAddMonoidHom.comp
    G.degreeOneCoinvariantsEquiv.toAddMonoidHom

/-- The unique degree-two cellular map normalized by the labelled Wang coordinates. -/
public noncomputable def normalizedCoinvariantHomologyTwoMap (A : PaperAnalyticData) :
    let G :=
      SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
        A.starCuspWitness
    let _ := G.fiberTopology
    (circleMappingTorusHTwoPresentation G.clutching).Coinvariants →+
      cuspToricCellularChainComplex.homology 2 := by
  let G :=
    SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
      A.starCuspWitness
  let _ := G.fiberTopology
  exact cuspToricCellularChainComplex_homologyTwoEquiv.symm.toAddMonoidHom.comp
    G.degreeTwoCoinvariantsEquiv.toAddMonoidHom

/-- The canonical alternative degree-one specialization has the required coordinates. -/
public theorem normalizedCoinvariantHomologyOneMap_naturality (A : PaperAnalyticData) :
    let G :=
      SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
        A.starCuspWitness
    let _ := G.fiberTopology
    cuspToricCellularChainComplex_homologyOneEquiv.toAddMonoidHom.comp
        (normalizedCoinvariantHomologyOneMap A) =
      G.degreeOneCoinvariantsEquiv.toAddMonoidHom := by
  ext x
  simp [normalizedCoinvariantHomologyOneMap]

/-- The canonical alternative degree-two specialization has the required coordinates. -/
public theorem normalizedCoinvariantHomologyTwoMap_naturality (A : PaperAnalyticData) :
    let G :=
      SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
        A.starCuspWitness
    let _ := G.fiberTopology
    cuspToricCellularChainComplex_homologyTwoEquiv.toAddMonoidHom.comp
        (normalizedCoinvariantHomologyTwoMap A) =
      G.degreeTwoCoinvariantsEquiv.toAddMonoidHom := by
  ext x
  simp [normalizedCoinvariantHomologyTwoMap]

/-- The labelled coordinates uniquely determine the normalized degree-one map. -/
public theorem eq_normalizedCoinvariantHomologyOneMap_of_naturality (A : PaperAnalyticData)
    (f :
      let G :=
        SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
          A.starCuspWitness
      let _ := G.fiberTopology
      (circleMappingTorusHOnePresentation G.clutching).Coinvariants →+
        cuspToricCellularChainComplex.homology 1)
    (h :
      let G :=
        SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
          A.starCuspWitness
      let _ := G.fiberTopology
      cuspToricCellularChainComplex_homologyOneEquiv.toAddMonoidHom.comp f =
        G.degreeOneCoinvariantsEquiv.toAddMonoidHom) :
    f = normalizedCoinvariantHomologyOneMap A := by
  ext x
  apply cuspToricCellularChainComplex_homologyOneEquiv.injective
  simpa [normalizedCoinvariantHomologyOneMap] using DFunLike.congr_fun h x

/-- The labelled coordinates uniquely determine the normalized degree-two map. -/
public theorem eq_normalizedCoinvariantHomologyTwoMap_of_naturality (A : PaperAnalyticData)
    (f :
      let G :=
        SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
          A.starCuspWitness
      let _ := G.fiberTopology
      (circleMappingTorusHTwoPresentation G.clutching).Coinvariants →+
        cuspToricCellularChainComplex.homology 2)
    (h :
      let G :=
        SphereSixComplex.Geometry.CuspRadialClutchingConstruction.actualCuspRadialClutchingData
          A.starCuspWitness
      let _ := G.fiberTopology
      cuspToricCellularChainComplex_homologyTwoEquiv.toAddMonoidHom.comp f =
        G.degreeTwoCoinvariantsEquiv.toAddMonoidHom) :
    f = normalizedCoinvariantHomologyTwoMap A := by
  ext x
  apply cuspToricCellularChainComplex_homologyTwoEquiv.injective
  simpa [normalizedCoinvariantHomologyTwoMap] using DFunLike.congr_fun h x

/-- The remaining source-side normalization after constructing the chain comparison and the
specialization triangle.  Its two fields identify the induced maps with canonical normalized
maps, not with a list of generator values.  There is currently no chain model for the Wang
coinvariant presentation on which to combine them into one chain-map equation. -/
public structure MarkedFiberCellularCoinvariantChainNaturality (A : PaperAnalyticData) where
  normalization : MarkedFiberCellularChainNormalization A.starCuspWitness
    A.cuspCentralFiberRetractionData
  degreeOne_eq_normalized :
    chainLiftCoinvariantHomologyOneMap A normalization = normalizedCoinvariantHomologyOneMap A
  degreeTwo_eq_normalized :
    chainLiftCoinvariantHomologyTwoMap A normalization = normalizedCoinvariantHomologyTwoMap A

/-- Once a chain normalization exists, ordinary coinvariant naturality supplies exactly the two
remaining normalization fields.  Thus the chain interface introduces no hidden coefficient
hypotheses. -/
public noncomputable def MarkedFiberCellularCoinvariantNaturality.toChainNaturality
    (A : PaperAnalyticData)
    (S : MarkedFiberCellularChainNormalization A.starCuspWitness
      A.cuspCentralFiberRetractionData)
    (h : MarkedFiberCellularCoinvariantNaturality A) :
    MarkedFiberCellularCoinvariantChainNaturality A where
  normalization := S
  degreeOne_eq_normalized := eq_normalizedCoinvariantHomologyOneMap_of_naturality A _ <| by
    rw [chainLiftCoinvariantHomologyOneMap_eq A S]
    exact h.degreeOne
  degreeTwo_eq_normalized := eq_normalizedCoinvariantHomologyTwoMap_of_naturality A _ <| by
    rw [chainLiftCoinvariantHomologyTwoMap_eq A S]
    exact h.degreeTwo

/-- A compatible cellular comparison, a chain-level specialization triangle, and the two
source-side Wang normalization squares imply the desired coinvariant naturality without using
the established six-coefficient matrix. -/
public theorem markedFiberCellularCoinvariantNaturality_of_chainNaturality
    (A : PaperAnalyticData) (T : MarkedFiberCellularCoinvariantChainNaturality A) :
    MarkedFiberCellularCoinvariantNaturality A := by
  constructor
  · rw [← chainLiftCoinvariantHomologyOneMap_eq A T.normalization]
    rw [T.degreeOne_eq_normalized]
    exact normalizedCoinvariantHomologyOneMap_naturality A
  · rw [← chainLiftCoinvariantHomologyTwoMap_eq A T.normalization]
    rw [T.degreeTwo_eq_normalized]
    exact normalizedCoinvariantHomologyTwoMap_naturality A

end EstablishedStandardA2CuspSpecialization

end Geometry.CuspPuncturedCollarBridge

end SphereSixComplex

end

end
