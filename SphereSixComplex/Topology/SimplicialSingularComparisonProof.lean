module

public import SphereSixComplex.Topology.SimplicialSingularComparison
public import SphereSixComplex.Topology.SingularExcisionOpenCover

/-!
# Reduction of simplicial--singular comparison to cover-small chains

For an open cover of the realization, the affine subdivision theorem proves that cover-small
singular chains include quasi-isomorphically into all singular chains.  Consequently, whenever
the adjunction unit lands in the cover-small singular subcomplex, the canonical comparison is a
quasi-isomorphism exactly when its lift to cover-small chains is one.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Set Simplicial

namespace SphereSixComplex

variable {iota : Type} (K : SSet.{0})
  (U : iota → Set (SSet.toTop.obj K))

/-- The adjunction unit defining the simplicial--singular comparison has image in the simplices
small for `U`. -/
public def SimplicialRealizationUnitLandsInCoverSmall : Prop :=
  SSet.Subcomplex.range (sSetTopAdj.unit.app K) ≤
    coverSmallSingularSubcomplex (SSet.toTop.obj K) U

/-- Elementwise form of cover-smallness: every canonical realized simplex factors through one
member of the cover. -/
public theorem simplicialRealizationUnitLandsInCoverSmall_iff :
    SimplicialRealizationUnitLandsInCoverSmall K U ↔
      ∀ (n : SimplexCategoryᵒᵖ) (x : K.obj n),
        ∃ (j : iota)
          (y : (TopCat.toSSet.obj (TopCat.of (U j))).obj n),
          (TopCat.toSSet.map
            (topologicalSubsetInclusion (SSet.toTop.obj K) (U j))).app n y =
            (sSetTopAdj.unit.app K).app n x := by
  constructor
  · intro h n x
    apply (mem_coverSmallSingularSubcomplex_iff_exists_preimage
      (SSet.toTop.obj K) U _).mp
    exact h n ⟨x, rfl⟩
  · intro h n z hz
    obtain ⟨x, rfl⟩ := hz
    exact (mem_coverSmallSingularSubcomplex_iff_exists_preimage
      (SSet.toTop.obj K) U _).mpr (h n x)

/-- The adjunction unit lifted to the cover-small singular simplicial set. -/
public noncomputable def simplicialToCoverSmallSingularSet
    (hsmall : SimplicialRealizationUnitLandsInCoverSmall K U) :
    K ⟶ coverSmallSingularSubcomplex (SSet.toTop.obj K) U :=
  SSet.Subcomplex.lift (sSetTopAdj.unit.app K) hsmall

@[reassoc (attr := simp)]
public theorem simplicialToCoverSmallSingularSet_comp_inclusion
    (hsmall : SimplicialRealizationUnitLandsInCoverSmall K U) :
    simplicialToCoverSmallSingularSet K U hsmall ≫
        (coverSmallSingularSubcomplex (SSet.toTop.obj K) U).ι =
      sSetTopAdj.unit.app K :=
  SSet.Subcomplex.lift_ι _ _

/-- The integral simplicial comparison, with codomain restricted to cover-small singular
chains. -/
public noncomputable def simplicialToCoverSmallSingularChainMap
    (hsmall : SimplicialRealizationUnitLandsInCoverSmall K U) :
    K.chainComplex (AddCommGrpCat.of ℤ) ⟶
      CoverSmallIntegralSingularChainComplex (SSet.toTop.obj K) U :=
  SSet.chainComplexMap (simplicialToCoverSmallSingularSet K U hsmall)
    (AddCommGrpCat.of ℤ)

/-- The cover-small lift followed by inclusion is the canonical comparison map. -/
@[reassoc]
public theorem simplicialToCoverSmallSingularChainMap_comp_inclusion
    (hsmall : SimplicialRealizationUnitLandsInCoverSmall K U) :
    simplicialToCoverSmallSingularChainMap K U hsmall ≫
        coverSmallIntegralSingularChainInclusion (SSet.toTop.obj K) U =
      simplicialToRealizationSingularChainMap K (AddCommGrpCat.of ℤ) := by
  change
    ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
          (simplicialToCoverSmallSingularSet K U hsmall) ≫
      ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
          (coverSmallSingularSubcomplex (SSet.toTop.obj K) U).ι =
    ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
      (sSetTopAdj.unit.app K)
  rw [← Functor.map_comp,
    simplicialToCoverSmallSingularSet_comp_inclusion]

/-- For an open cover, affine subdivision removes the full-singular-chain part of the comparison
problem: the canonical comparison is a quasi-isomorphism if and only if its cover-small lift is.
-/
public theorem simplicialToSingularComparisonQuasiIsomorphism_iff_coverSmallLift
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ)
    (hsmall : SimplicialRealizationUnitLandsInCoverSmall K U) :
    SimplicialToSingularComparisonQuasiIsomorphism K (AddCommGrpCat.of ℤ) ↔
      QuasiIso (simplicialToCoverSmallSingularChainMap K U hsmall) := by
  have hcover : QuasiIso
      (coverSmallIntegralSingularChainInclusion (SSet.toTop.obj K) U) :=
    coverSmallChainQuasiIsomorphism_of_openCover
      (SSet.toTop.obj K) U hUopen hUcover
  change QuasiIso
      (simplicialToRealizationSingularChainMap K (AddCommGrpCat.of ℤ)) ↔
    QuasiIso (simplicialToCoverSmallSingularChainMap K U hsmall)
  rw [← simplicialToCoverSmallSingularChainMap_comp_inclusion K U hsmall]
  exact quasiIso_iff_comp_right _ _ (hφ' := hcover)

/-- The canonical map from the boundary realization to the ordinary affine standard
seven-simplex, duplicated here so that the comparison proof is independent of any later geometric
identification of the boundary realization. -/
public noncomputable def boundarySevenComparisonToStdSimplex :
    C((SSet.toTop.obj (∂Δ[7] : SSet.{0}) : Type), stdSimplex ℝ (Fin 8)) :=
  ⟨fun x ↦ SimplexCategory.toTopHomeo (SimplexCategory.mk 7)
      (SSet.toTop.map (SSet.boundary 7).ι x),
    (SimplexCategory.toTopHomeo (SimplexCategory.mk 7)).continuous.comp
      (SSet.toTop.map (SSet.boundary 7).ι).hom.continuous⟩

/-- On a codimension-one face, the comparison map is the usual affine face inclusion. -/
public theorem boundarySevenComparisonToStdSimplex_face
    (i : Fin 8) (x : (SSet.toTop.obj (Δ[6] : SSet.{0}) : Type)) :
    boundarySevenComparisonToStdSimplex
        (SSet.toTop.map (SSet.boundary.ι i) x) =
      stdSimplex.map i.succAbove
        (SimplexCategory.toTopHomeo (SimplexCategory.mk 6) x) := by
  unfold boundarySevenComparisonToStdSimplex
  change SimplexCategory.toTopHomeo (SimplexCategory.mk 7)
      (SSet.toTop.map (SSet.boundary 7).ι
        (SSet.toTop.map (SSet.boundary.ι i) x)) = _
  rw [← ConcreteCategory.comp_apply]
  rw [← SSet.toTop.map_comp]
  rw [SSet.boundary.ι_ι]
  exact SimplexCategory.toTopHomeo_naturality_apply (SimplexCategory.δ i) x

/-- An open neighborhood of the `i`-th affine face, pulled back to the realization of
`∂Δ[7]`. -/
public def boundarySevenComparisonFaceNeighborhood (i : Fin 8) :
    Set (SSet.toTop.obj (∂Δ[7] : SSet.{0})) :=
  {x | boundarySevenComparisonToStdSimplex x i < (1 : ℝ) / 8}

/-- The affine face neighborhoods are open. -/
public theorem boundarySevenComparisonFaceNeighborhood_isOpen (i : Fin 8) :
    IsOpen (boundarySevenComparisonFaceNeighborhood i) := by
  apply isOpen_lt
  · exact ((continuous_apply i).comp continuous_subtype_val).comp
      boundarySevenComparisonToStdSimplex.continuous
  · exact continuous_const

/-- The realization of the `i`-th simplicial face lands in its corresponding open affine
neighborhood. -/
public noncomputable def boundarySevenFaceToComparisonFaceNeighborhood (i : Fin 8) :
    SSet.toTop.obj (Δ[6] : SSet.{0}) ⟶
      TopCat.of (boundarySevenComparisonFaceNeighborhood i) := by
  refine TopCat.ofHom
    { toFun := fun x ↦ ⟨SSet.toTop.map (SSet.boundary.ι i) x, ?_⟩
      continuous_toFun := ?_ }
  · change boundarySevenComparisonToStdSimplex
        (SSet.toTop.map (SSet.boundary.ι i) x) i < (1 : ℝ) / 8
    rw [boundarySevenComparisonToStdSimplex_face]
    change stdSimplex.map i.succAbove
      (SimplexCategory.toTopHomeo (SimplexCategory.mk 6) x) i < (1 : ℝ) / 8
    have hz : stdSimplex.map i.succAbove
        (SimplexCategory.toTopHomeo (SimplexCategory.mk 6) x) i = 0 := by
      classical
      simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
      apply Finset.sum_eq_zero
      intro j hj
      exact (Fin.succAbove_ne i j (Finset.mem_filter.mp hj).2).elim
    rw [hz]
    norm_num
  · exact (SSet.toTop.map (SSet.boundary.ι i)).hom.continuous.subtype_mk _

@[reassoc (attr := simp)]
public theorem boundarySevenFaceToComparisonFaceNeighborhood_comp_inclusion
    (i : Fin 8) :
    boundarySevenFaceToComparisonFaceNeighborhood i ≫
        topologicalSubsetInclusion (SSet.toTop.obj (∂Δ[7] : SSet.{0}))
          (boundarySevenComparisonFaceNeighborhood i) =
      SSet.toTop.map (SSet.boundary.ι i) := by
  rfl

/-- The unit on one standard face, mapped into the cover-small singular simplicial set of the
boundary realization. -/
public noncomputable def boundarySevenFaceUnitToSmallSingularSet (i : Fin 8) :
    (Δ[6] : SSet.{0}) ⟶
      coverSmallSingularSubcomplex
        (SSet.toTop.obj (∂Δ[7] : SSet.{0}))
        boundarySevenComparisonFaceNeighborhood :=
  sSetTopAdj.unit.app (Δ[6] : SSet.{0}) ≫
    TopCat.toSSet.map (boundarySevenFaceToComparisonFaceNeighborhood i) ≫
      coverMemberToSmallSingularSet
        (SSet.toTop.obj (∂Δ[7] : SSet.{0}))
        boundarySevenComparisonFaceNeighborhood i

/-- The facewise small unit is the restriction of the boundary comparison unit. -/
@[reassoc (attr := simp)]
public theorem boundarySevenFaceUnitToSmallSingularSet_comp_inclusion (i : Fin 8) :
    boundarySevenFaceUnitToSmallSingularSet i ≫
        (coverSmallSingularSubcomplex
          (SSet.toTop.obj (∂Δ[7] : SSet.{0}))
          boundarySevenComparisonFaceNeighborhood).ι =
      SSet.boundary.ι i ≫ sSetTopAdj.unit.app (∂Δ[7] : SSet.{0}) := by
  unfold boundarySevenFaceUnitToSmallSingularSet
  rw [Category.assoc, Category.assoc,
    coverMemberToSmallSingularSet_comp_inclusion]
  rw [← Functor.map_comp,
    boundarySevenFaceToComparisonFaceNeighborhood_comp_inclusion]
  exact (sSetTopAdj.unit.naturality (SSet.boundary.ι i)).symm

/-- Every canonical simplicial simplex of `∂Δ[7]` lands in one of the eight affine face
neighborhoods. -/
public theorem boundarySevenComparisonUnitLandsInFaceNeighborhoods :
    SimplicialRealizationUnitLandsInCoverSmall
      (∂Δ[7] : SSet.{0}) boundarySevenComparisonFaceNeighborhood := by
  intro n z hz
  obtain ⟨x, rfl⟩ := hz
  have hx := x.2
  simp only [SSet.boundary_eq_iSup, SSet.stdSimplex.face_singleton_compl,
    Subfunctor.iSup_obj, Set.mem_iUnion,
    SSet.Subcomplex.mem_ofSimplex_obj_iff, Opposite.op_unop] at hx
  obtain ⟨i, ⟨y, hy⟩⟩ := hx
  let y' : (Δ[6] : SSet.{0}).obj n := SSet.stdSimplex.objEquiv.symm y
  have hxy : (SSet.boundary.ι i).app n y' = x := by
    apply Subtype.ext
    change (SSet.stdSimplex.map (SimplexCategory.δ i)).app n y' = x.1
    exact hy
  let w := (boundarySevenFaceUnitToSmallSingularSet i).app n y'
  have hw : w.1 = (sSetTopAdj.unit.app (∂Δ[7] : SSet.{0})).app n x := by
    have h := ConcreteCategory.congr_hom
      (congr_app (boundarySevenFaceUnitToSmallSingularSet_comp_inclusion i) n) y'
    change ((boundarySevenFaceUnitToSmallSingularSet i).app n y').1 =
      (sSetTopAdj.unit.app (∂Δ[7] : SSet.{0})).app n
        ((SSet.boundary.ι i).app n y') at h
    simpa only [hxy] using h
  rw [← hw]
  exact w.2

/-- The remaining global geometric assertion needed to know that the eight explicit affine face
neighborhoods cover the whole realization.  It states precisely that the comparison map from the
realized simplicial boundary lands in the affine boundary. -/
public def BoundarySevenComparisonMapLandsInAffineBoundary : Prop :=
  ∀ x : SSet.toTop.obj (∂Δ[7] : SSet.{0}),
    ∃ i : Fin 8, boundarySevenComparisonToStdSimplex x i = 0

/-- If the comparison map lands in the affine boundary, the eight explicit face neighborhoods
cover the realization. -/
public theorem boundarySevenComparisonFaceNeighborhood_iUnion
    (hboundary : BoundarySevenComparisonMapLandsInAffineBoundary) :
    ⋃ i, boundarySevenComparisonFaceNeighborhood i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, hi⟩ := hboundary x
  apply Set.mem_iUnion.2
  refine ⟨i, ?_⟩
  change boundarySevenComparisonToStdSimplex x i < (1 : ℝ) / 8
  rw [hi]
  norm_num

/-- Specialized sharp reduction for the boundary of the seven-simplex.  It remains only to prove
that the explicitly lifted map into cover-small chains is a quasi-isomorphism. -/
public theorem boundarySeven_integralComparison_iff_coverSmallLift
    (U : iota → Set (SSet.toTop.obj (∂Δ[7] : SSet.{0})))
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ)
    (hsmall : SimplicialRealizationUnitLandsInCoverSmall
      (∂Δ[7] : SSet.{0}) U) :
    SimplicialToSingularComparisonQuasiIsomorphism
        (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ) ↔
      QuasiIso (simplicialToCoverSmallSingularChainMap
        (∂Δ[7] : SSet.{0}) U hsmall) :=
  simplicialToSingularComparisonQuasiIsomorphism_iff_coverSmallLift
    (∂Δ[7] : SSet.{0}) U hUopen hUcover hsmall

/-- The second, purely chain-level input for the concrete eight-member face-neighborhood cover:
the explicitly lifted simplicial comparison must be a quasi-isomorphism. -/
public def BoundarySevenFaceNeighborhoodLiftQuasiIsomorphism : Prop :=
  QuasiIso (simplicialToCoverSmallSingularChainMap
    (∂Δ[7] : SSet.{0}) boundarySevenComparisonFaceNeighborhood
      boundarySevenComparisonUnitLandsInFaceNeighborhoods)

/-- Once the realized boundary is known to map to the affine boundary, the original comparison
problem is exactly the quasi-isomorphism problem for the explicit face-neighborhood-small lift. -/
public theorem boundarySeven_integralComparison_iff_faceNeighborhoodLift
    (hboundary : BoundarySevenComparisonMapLandsInAffineBoundary) :
    SimplicialToSingularComparisonQuasiIsomorphism
        (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ) ↔
      BoundarySevenFaceNeighborhoodLiftQuasiIsomorphism := by
  unfold BoundarySevenFaceNeighborhoodLiftQuasiIsomorphism
  exact boundarySeven_integralComparison_iff_coverSmallLift
    boundarySevenComparisonFaceNeighborhood
    boundarySevenComparisonFaceNeighborhood_isOpen
    (boundarySevenComparisonFaceNeighborhood_iUnion hboundary)
    boundarySevenComparisonUnitLandsInFaceNeighborhoods

/-- The two explicit remaining inputs imply the requested canonical integral comparison. -/
public theorem boundarySeven_integralComparison_of_faceNeighborhoodLift
    (hboundary : BoundarySevenComparisonMapLandsInAffineBoundary)
    (hlift : BoundarySevenFaceNeighborhoodLiftQuasiIsomorphism) :
    SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ) :=
  (boundarySeven_integralComparison_iff_faceNeighborhoodLift hboundary).2 hlift

/-- Any open cover for which the cover-small lift is a quasi-isomorphism supplies the requested
canonical integral comparison for `∂Δ[7]`. -/
public theorem boundarySeven_integralComparison_of_coverSmallLift
    (U : iota → Set (SSet.toTop.obj (∂Δ[7] : SSet.{0})))
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ)
    (hsmall : SimplicialRealizationUnitLandsInCoverSmall
      (∂Δ[7] : SSet.{0}) U)
    (hlift : QuasiIso (simplicialToCoverSmallSingularChainMap
      (∂Δ[7] : SSet.{0}) U hsmall)) :
    SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ) :=
  (boundarySeven_integralComparison_iff_coverSmallLift
    U hUopen hUcover hsmall).2 hlift

/-- The exact remaining cover-level input for the integral boundary comparison: an open cover
subordinate to all canonical simplicial simplices, on which the lifted comparison is a
quasi-isomorphism. -/
public def BoundarySevenIntegralCoverSmallComparison : Prop :=
  ∃ (iota : Type)
    (U : iota → Set (SSet.toTop.obj (∂Δ[7] : SSet.{0})))
    (hsmall : SimplicialRealizationUnitLandsInCoverSmall
      (∂Δ[7] : SSet.{0}) U),
    (∀ i, IsOpen (U i)) ∧
      ⋃ i, U i = Set.univ ∧
      QuasiIso (simplicialToCoverSmallSingularChainMap
        (∂Δ[7] : SSet.{0}) U hsmall)

/-- The cover-level comparison input implies the requested canonical quasi-isomorphism. -/
public theorem boundarySeven_integralComparison_of_coverSmallComparison
    (h : BoundarySevenIntegralCoverSmallComparison) :
    SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ) := by
  obtain ⟨iota, U, hsmall, hUopen, hUcover, hlift⟩ := h
  exact boundarySeven_integralComparison_of_coverSmallLift
    U hUopen hUcover hsmall hlift

end SphereSixComplex
