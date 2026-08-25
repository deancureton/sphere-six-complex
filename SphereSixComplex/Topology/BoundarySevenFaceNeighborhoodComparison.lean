module

public import SphereSixComplex.Topology.SimplicialSingularComparisonProof
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-!
# The face-neighborhood Čech reduction for `∂Δ[7]`

This file develops the concrete finite-cover input for the comparison map.  The eight open sets
are the inverse images of the inequalities `x i < 1 / 8`.  Their total intersection is empty,
and the canonical presentation of the cover-small singular set is degreewise surjective.  Thus,
after evaluating in any singular degree, its augmented Čech nerve has an extra degeneracy and
its alternating complex contracts onto the cover-small chain group in that degree.

The final structure below isolates the remaining totalization/local-comparison step: a map from
the boundary chains to the Čech--singular total complex and the standard Čech augmentation,
both quasi-isomorphisms and with the expected composite.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Set Simplicial

namespace SphereSixComplex

/-- The intersection of the affine face neighborhoods indexed by `s`. -/
public def boundarySevenFaceNeighborhoodIntersection (s : Finset (Fin 8)) :
    Set (SSet.toTop.obj (∂Δ[7] : SSet.{0})) :=
  ⋂ i ∈ s, boundarySevenComparisonFaceNeighborhood i

@[simp]
public theorem mem_boundarySevenFaceNeighborhoodIntersection_iff
    (s : Finset (Fin 8)) (x : SSet.toTop.obj (∂Δ[7] : SSet.{0})) :
    x ∈ boundarySevenFaceNeighborhoodIntersection s ↔
      ∀ i ∈ s, boundarySevenComparisonToStdSimplex x i < (1 : ℝ) / 8 := by
  simp [boundarySevenFaceNeighborhoodIntersection,
    boundarySevenComparisonFaceNeighborhood]

/-- Every finite intersection of the eight face neighborhoods is open. -/
public theorem boundarySevenFaceNeighborhoodIntersection_isOpen (s : Finset (Fin 8)) :
    IsOpen (boundarySevenFaceNeighborhoodIntersection s) := by
  apply isOpen_biInter_finset
  intro i _
  exact boundarySevenComparisonFaceNeighborhood_isOpen i

/-- All eight face neighborhoods have empty intersection. -/
public theorem boundarySevenFaceNeighborhoodIntersection_univ_eq_empty :
    boundarySevenFaceNeighborhoodIntersection Finset.univ = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  have hcoord :=
    (mem_boundarySevenFaceNeighborhoodIntersection_iff Finset.univ x).mp hx
  have hsum :
      ∑ i : Fin 8, boundarySevenComparisonToStdSimplex x i <
        ∑ _i : Fin 8, (1 : ℝ) / 8 := by
    apply Finset.sum_lt_sum
    · intro i _
      exact (hcoord i (Finset.mem_univ i)).le
    · exact ⟨0, Finset.mem_univ 0, hcoord 0 (Finset.mem_univ 0)⟩
  rw [stdSimplex.sum_eq_one] at hsum
  norm_num at hsum

/-- Every point of the realized simplicial boundary is represented by a point of one of its
codimension-one faces.  This is the concrete joint-surjectivity consequence of the canonical
colimit presentation of a presheaf by representables. -/
public theorem boundarySevenRealization_exists_face_representation
    (x : SSet.toTop.obj (∂Δ[7] : SSet.{0})) :
    ∃ (i : Fin 8) (y : SSet.toTop.obj (Δ[6] : SSet.{0})),
      SSet.toTop.map (SSet.boundary.ι i) y = x := by
  let c := SSet.toTop.mapCocone
    (Presheaf.coconeOfRepresentable (∂Δ[7] : SSet.{0}))
  let hc : IsColimit c := isColimitOfPreserves SSet.toTop
    (Presheaf.colimitOfRepresentable (∂Δ[7] : SSet.{0}))
  obtain ⟨j, z, hz⟩ := Concrete.isColimit_exists_rep _ hc x
  let a := j.unop.2
  have ha := a.2
  simp only [SSet.boundary_eq_iSup, SSet.stdSimplex.face_singleton_compl,
    Subfunctor.iSup_obj, Set.mem_iUnion,
    SSet.Subcomplex.mem_ofSimplex_obj_iff, Opposite.op_unop] at ha
  obtain ⟨i, ⟨y, hy⟩⟩ := ha
  let y' : (Δ[6] : SSet.{0}).obj j.unop.1 := SSet.stdSimplex.objEquiv.symm y
  have hay : (SSet.boundary.ι i).app j.unop.1 y' = a := by
    apply Subtype.ext
    change (SSet.stdSimplex.map (SimplexCategory.δ i)).app j.unop.1 y' = a.1
    exact hy
  refine ⟨i, SSet.toTop.map (SSet.yonedaEquiv.symm y') z, ?_⟩
  have hcomp :
      SSet.toTop.map (SSet.yonedaEquiv.symm y') ≫
          SSet.toTop.map (SSet.boundary.ι i) =
        SSet.toTop.map (SSet.yonedaEquiv.symm a) := by
    rw [← SSet.toTop.map_comp, SSet.yonedaEquiv_symm_comp, hay]
  have happ := ConcreteCategory.congr_hom hcomp z
  change SSet.toTop.map (SSet.boundary.ι i)
      (SSet.toTop.map (SSet.yonedaEquiv.symm y') z) =
        SSet.toTop.map (SSet.yonedaEquiv.symm a) z at happ
  change SSet.toTop.map (SSet.yonedaEquiv.symm a) z = x at hz
  exact happ.trans hz

/-- The comparison map from the realization really lands in the affine boundary. -/
public theorem boundarySevenComparisonMapLandsInAffineBoundary :
    BoundarySevenComparisonMapLandsInAffineBoundary := by
  intro x
  obtain ⟨i, y, rfl⟩ := boundarySevenRealization_exists_face_representation x
  refine ⟨i, ?_⟩
  rw [boundarySevenComparisonToStdSimplex_face]
  classical
  simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro j hj
  exact (Fin.succAbove_ne i j (Finset.mem_filter.mp hj).2).elim

/-- Consequently, the eight explicit face neighborhoods cover the whole realization. -/
public theorem boundarySevenComparisonFaceNeighborhood_iUnion_unconditional :
    ⋃ i, boundarySevenComparisonFaceNeighborhood i = Set.univ :=
  boundarySevenComparisonFaceNeighborhood_iUnion
    boundarySevenComparisonMapLandsInAffineBoundary

/-- With the global cover assertion discharged, the canonical integral comparison is
unconditionally equivalent to the explicit face-neighborhood lift. -/
public theorem boundarySeven_integralComparison_iff_faceNeighborhoodLift_unconditional :
    SimplicialToSingularComparisonQuasiIsomorphism
        (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ) ↔
      BoundarySevenFaceNeighborhoodLiftQuasiIsomorphism :=
  boundarySeven_integralComparison_iff_faceNeighborhoodLift
    boundarySevenComparisonMapLandsInAffineBoundary

/-- The coproduct of the eight standard simplicial faces. -/
public noncomputable abbrev boundarySevenSimplicialFacePresentationSource : SSet.{0} :=
  sigmaObj (fun _i : Fin 8 ↦ (Δ[6] : SSet.{0}))

/-- The canonical simplicial face presentation of `∂Δ[7]`. -/
public noncomputable def boundarySevenSimplicialFacePresentation :
    boundarySevenSimplicialFacePresentationSource ⟶ (∂Δ[7] : SSet.{0}) :=
  Sigma.desc fun i ↦ SSet.boundary.ι i

/-- The simplicial face presentation is degreewise surjective. -/
public theorem boundarySevenSimplicialFacePresentation_app_surjective
    (n : SimplexCategoryᵒᵖ) :
    Function.Surjective (boundarySevenSimplicialFacePresentation.app n) := by
  intro x
  have hx := x.2
  simp only [SSet.boundary_eq_iSup, SSet.stdSimplex.face_singleton_compl,
    Subfunctor.iSup_obj, Set.mem_iUnion,
    SSet.Subcomplex.mem_ofSimplex_obj_iff, Opposite.op_unop] at hx
  obtain ⟨i, ⟨y, hy⟩⟩ := hx
  let y' : (Δ[6] : SSet.{0}).obj n := SSet.stdSimplex.objEquiv.symm y
  refine ⟨(Sigma.ι (fun _i : Fin 8 ↦ (Δ[6] : SSet.{0})) i).app n y', ?_⟩
  apply Subtype.ext
  change ((Sigma.ι (fun _i : Fin 8 ↦ (Δ[6] : SSet.{0})) i ≫
    boundarySevenSimplicialFacePresentation).app n y').1 = x.1
  rw [boundarySevenSimplicialFacePresentation, Sigma.ι_desc]
  exact hy

/-- The simplicial face presentation is an epimorphism. -/
public instance boundarySevenSimplicialFacePresentation_epi :
    Epi boundarySevenSimplicialFacePresentation := by
  rw [NatTrans.epi_iff_epi_app]
  intro n
  rw [CategoryTheory.epi_iff_surjective]
  exact boundarySevenSimplicialFacePresentation_app_surjective n

/-- The coproduct of the singular simplicial sets of the eight face neighborhoods. -/
public noncomputable abbrev boundarySevenFaceNeighborhoodPresentationSource : SSet.{0} :=
  sigmaObj (fun i : Fin 8 ↦
    TopCat.toSSet.obj (TopCat.of (boundarySevenComparisonFaceNeighborhood i)))

/-- The canonical presentation of the face-neighborhood-small singular simplicial set. -/
public noncomputable def boundarySevenFaceNeighborhoodPresentation :
    boundarySevenFaceNeighborhoodPresentationSource ⟶
      coverSmallSingularSubcomplex
        (SSet.toTop.obj (∂Δ[7] : SSet.{0}))
        boundarySevenComparisonFaceNeighborhood :=
  Sigma.desc fun i ↦
    coverMemberToSmallSingularSet
      (SSet.toTop.obj (∂Δ[7] : SSet.{0}))
      boundarySevenComparisonFaceNeighborhood i

/-- In every simplicial degree, the face-neighborhood presentation is surjective. -/
public theorem boundarySevenFaceNeighborhoodPresentation_app_surjective
    (n : SimplexCategoryᵒᵖ) :
    Function.Surjective (boundarySevenFaceNeighborhoodPresentation.app n) := by
  intro z
  obtain ⟨i, y, hy⟩ :=
    (mem_coverSmallSingularSubcomplex_iff_exists_preimage
      (SSet.toTop.obj (∂Δ[7] : SSet.{0}))
      boundarySevenComparisonFaceNeighborhood z.1).mp z.2
  refine ⟨(Sigma.ι (fun i : Fin 8 ↦
    TopCat.toSSet.obj (TopCat.of (boundarySevenComparisonFaceNeighborhood i))) i).app n y, ?_⟩
  apply Subtype.ext
  have hcat :
      Sigma.ι (fun i : Fin 8 ↦
          TopCat.toSSet.obj
            (TopCat.of (boundarySevenComparisonFaceNeighborhood i))) i ≫
          boundarySevenFaceNeighborhoodPresentation ≫
          (coverSmallSingularSubcomplex
            (SSet.toTop.obj (∂Δ[7] : SSet.{0}))
            boundarySevenComparisonFaceNeighborhood).ι =
        TopCat.toSSet.map
          (topologicalSubsetInclusion (SSet.toTop.obj (∂Δ[7] : SSet.{0}))
            (boundarySevenComparisonFaceNeighborhood i)) := by
    rw [boundarySevenFaceNeighborhoodPresentation, ← Category.assoc, Sigma.ι_desc,
      coverMemberToSmallSingularSet_comp_inclusion]
  have happ := ConcreteCategory.congr_hom (congr_app hcat n) y
  exact happ.trans hy

/-- The cover presentation is an epimorphism of simplicial sets. -/
public instance boundarySevenFaceNeighborhoodPresentation_epi :
    Epi boundarySevenFaceNeighborhoodPresentation := by
  rw [NatTrans.epi_iff_epi_app]
  intro n
  rw [CategoryTheory.epi_iff_surjective]
  exact boundarySevenFaceNeighborhoodPresentation_app_surjective n

/-- Facewise, the realized simplicial unit maps the coproduct of standard faces to the
coproduct of singular sets of the corresponding open neighborhoods. -/
public noncomputable def boundarySevenFacePresentationSourceMap :
    boundarySevenSimplicialFacePresentationSource ⟶
      boundarySevenFaceNeighborhoodPresentationSource :=
  Sigma.desc fun i ↦
    sSetTopAdj.unit.app (Δ[6] : SSet.{0}) ≫
      TopCat.toSSet.map (boundarySevenFaceToComparisonFaceNeighborhood i) ≫
        Sigma.ι (fun i : Fin 8 ↦
          TopCat.toSSet.obj (TopCat.of (boundarySevenComparisonFaceNeighborhood i))) i

@[reassoc (attr := simp)]
public theorem boundarySevenSimplicialFacePresentation_iota (i : Fin 8) :
    Sigma.ι (fun _i : Fin 8 ↦ (Δ[6] : SSet.{0})) i ≫
        boundarySevenSimplicialFacePresentation =
      SSet.boundary.ι i := by
  apply Sigma.ι_desc

@[reassoc (attr := simp)]
public theorem boundarySevenFacePresentationSourceMap_iota (i : Fin 8) :
    Sigma.ι (fun _i : Fin 8 ↦ (Δ[6] : SSet.{0})) i ≫
        boundarySevenFacePresentationSourceMap =
      sSetTopAdj.unit.app (Δ[6] : SSet.{0}) ≫
        TopCat.toSSet.map (boundarySevenFaceToComparisonFaceNeighborhood i) ≫
          Sigma.ι (fun i : Fin 8 ↦
            TopCat.toSSet.obj
              (TopCat.of (boundarySevenComparisonFaceNeighborhood i))) i := by
  apply Sigma.ι_desc

/-- The facewise presentation map commutes with the two augmentations. -/
public theorem boundarySevenFacePresentationSourceMap_comp_presentation :
    boundarySevenFacePresentationSourceMap ≫
        boundarySevenFaceNeighborhoodPresentation =
      boundarySevenSimplicialFacePresentation ≫
        simplicialToCoverSmallSingularSet
          (∂Δ[7] : SSet.{0}) boundarySevenComparisonFaceNeighborhood
          boundarySevenComparisonUnitLandsInFaceNeighborhoods := by
  apply Sigma.hom_ext
  intro i
  simp only [← Category.assoc,
    boundarySevenFacePresentationSourceMap_iota,
    boundarySevenSimplicialFacePresentation_iota]
  rw [Category.assoc, Category.assoc]
  rw [boundarySevenFaceNeighborhoodPresentation, Sigma.ι_desc]
  change boundarySevenFaceUnitToSmallSingularSet i =
    SSet.boundary.ι i ≫
      simplicialToCoverSmallSingularSet
        (∂Δ[7] : SSet.{0}) boundarySevenComparisonFaceNeighborhood
        boundarySevenComparisonUnitLandsInFaceNeighborhoods
  apply (cancel_mono
    (coverSmallSingularSubcomplex
      (SSet.toTop.obj (∂Δ[7] : SSet.{0}))
      boundarySevenComparisonFaceNeighborhood).ι).mp
  rw [boundarySevenFaceUnitToSmallSingularSet_comp_inclusion,
    Category.assoc, simplicialToCoverSmallSingularSet_comp_inclusion]

/-- The preceding commuting square as a morphism of arrows. -/
public noncomputable def boundarySevenFacePresentationArrowMap :
    Arrow.mk boundarySevenSimplicialFacePresentation ⟶
      Arrow.mk boundarySevenFaceNeighborhoodPresentation where
  left := boundarySevenFacePresentationSourceMap
  right := simplicialToCoverSmallSingularSet
    (∂Δ[7] : SSet.{0}) boundarySevenComparisonFaceNeighborhood
    boundarySevenComparisonUnitLandsInFaceNeighborhoods
  w := boundarySevenFacePresentationSourceMap_comp_presentation

/-- The presentation evaluated at one singular degree, as an arrow of types. -/
public noncomputable def boundarySevenFaceNeighborhoodPresentationEvaluationArrow
    (n : SimplexCategoryᵒᵖ) : Arrow (Type 0) :=
  Arrow.mk (boundarySevenFaceNeighborhoodPresentation.app n)

/-- A chosen splitting of the evaluated presentation.  Choice is harmless here: this splitting
is used only horizontally, to contract one Čech row. -/
public noncomputable def boundarySevenFaceNeighborhoodPresentationEvaluationSplitEpi
    (n : SimplexCategoryᵒᵖ) :
    SplitEpi (boundarySevenFaceNeighborhoodPresentationEvaluationArrow n).hom := by
  let h := boundarySevenFaceNeighborhoodPresentation_app_surjective n
  exact
    { section_ := ↾fun z ↦ Function.surjInv h z
      id := by
        ext z
        exact Function.rightInverse_surjInv h z }

/-- The evaluated augmented Čech nerve has an extra degeneracy. -/
public noncomputable def boundarySevenFaceNeighborhoodEvaluationExtraDegeneracy
    (n : SimplexCategoryᵒᵖ) :
    SimplicialObject.Augmented.ExtraDegeneracy
      (boundarySevenFaceNeighborhoodPresentationEvaluationArrow n).augmentedCechNerve :=
  Arrow.AugmentedCechNerve.extraDegeneracy
    (boundarySevenFaceNeighborhoodPresentationEvaluationArrow n)
    (boundarySevenFaceNeighborhoodPresentationEvaluationSplitEpi n)

/-- Apply the free abelian group functor to an evaluated augmented Čech nerve. -/
public noncomputable abbrev boundarySevenFaceNeighborhoodFreeEvaluationCech
    (n : SimplexCategoryᵒᵖ) : SimplicialObject.Augmented AddCommGrpCat :=
  ((SimplicialObject.Augmented.whiskering (Type 0) AddCommGrpCat).obj
    AddCommGrpCat.free).obj
      (boundarySevenFaceNeighborhoodPresentationEvaluationArrow n).augmentedCechNerve

/-- The free-abelian evaluated Čech nerve retains the extra degeneracy. -/
public noncomputable def boundarySevenFaceNeighborhoodFreeEvaluationExtraDegeneracy
    (n : SimplexCategoryᵒᵖ) :
    SimplicialObject.Augmented.ExtraDegeneracy
      (boundarySevenFaceNeighborhoodFreeEvaluationCech n) :=
  (boundarySevenFaceNeighborhoodEvaluationExtraDegeneracy n).map AddCommGrpCat.free

/-- Rowwise Čech exactness: in every singular degree, the alternating Čech complex is
chain-homotopy equivalent to the free group on the cover-small simplices in that degree. -/
public noncomputable def boundarySevenFaceNeighborhoodCechRowHomotopyEquiv
    (n : SimplexCategoryᵒᵖ) :
    HomotopyEquiv
      (AlternatingFaceMapComplex.obj
        (SimplicialObject.Augmented.drop.obj
          (boundarySevenFaceNeighborhoodFreeEvaluationCech n)))
      ((ChainComplex.single₀ AddCommGrpCat).obj
        (SimplicialObject.Augmented.point.obj
          (boundarySevenFaceNeighborhoodFreeEvaluationCech n))) :=
  (boundarySevenFaceNeighborhoodFreeEvaluationExtraDegeneracy n).homotopyEquiv

/-- The same evaluated Čech nerve with the coefficient functor actually used by integral
simplicial chains: a coproduct of copies of `ℤ`. -/
public noncomputable abbrev boundarySevenFaceNeighborhoodIntegralEvaluationCech
    (k : ℕ) : SimplicialObject.Augmented AddCommGrpCat :=
  ((SimplicialObject.Augmented.whiskering (Type 0) AddCommGrpCat).obj
    (sigmaConst.obj (AddCommGrpCat.of ℤ))).obj
      (boundarySevenFaceNeighborhoodPresentationEvaluationArrow
        (Opposite.op (SimplexCategory.mk k))).augmentedCechNerve

/-- The integral evaluated Čech nerve has the same row contraction. -/
public noncomputable def boundarySevenFaceNeighborhoodIntegralEvaluationExtraDegeneracy
    (k : ℕ) :
    SimplicialObject.Augmented.ExtraDegeneracy
      (boundarySevenFaceNeighborhoodIntegralEvaluationCech k) :=
  (boundarySevenFaceNeighborhoodEvaluationExtraDegeneracy
    (Opposite.op (SimplexCategory.mk k))).map
      (sigmaConst.obj (AddCommGrpCat.of ℤ))

/-- Rowwise exactness in the precise coefficient model used by the singular chain complex. -/
public noncomputable def boundarySevenFaceNeighborhoodIntegralCechRowHomotopyEquiv
    (k : ℕ) :
    HomotopyEquiv
      (AlternatingFaceMapComplex.obj
        (SimplicialObject.Augmented.drop.obj
          (boundarySevenFaceNeighborhoodIntegralEvaluationCech k)))
      ((ChainComplex.single₀ AddCommGrpCat).obj
        (SimplicialObject.Augmented.point.obj
          (boundarySevenFaceNeighborhoodIntegralEvaluationCech k))) :=
  (boundarySevenFaceNeighborhoodIntegralEvaluationExtraDegeneracy k).homotopyEquiv

/-- The target of the integral row contraction is definitionally the degree-`k` group of the
cover-small singular chain complex. -/
public noncomputable def boundarySevenFaceNeighborhoodIntegralEvaluationPointIso
    (k : ℕ) :
    SimplicialObject.Augmented.point.obj
        (boundarySevenFaceNeighborhoodIntegralEvaluationCech k) ≅
      (CoverSmallIntegralSingularChainComplex
        (SSet.toTop.obj (∂Δ[7] : SSet.{0}))
        boundarySevenComparisonFaceNeighborhood).X k :=
  Iso.refl _

/-- Equivalently, every horizontal integral Čech-row augmentation is a
quasi-isomorphism. -/
public theorem boundarySevenFaceNeighborhoodIntegralCechRowAugmentation_quasiIso
    (k : ℕ) :
    QuasiIso (AlternatingFaceMapComplex.ε.app
      (boundarySevenFaceNeighborhoodIntegralEvaluationCech k)) :=
  (boundarySevenFaceNeighborhoodIntegralCechRowHomotopyEquiv k).quasiIso_hom

/-- The face-neighborhood presentation, bundled as an arrow of simplicial sets. -/
public noncomputable def boundarySevenFaceNeighborhoodPresentationArrow : Arrow SSet :=
  Arrow.mk boundarySevenFaceNeighborhoodPresentation

/-- The augmented Čech nerve of the face-neighborhood presentation. -/
public noncomputable def boundarySevenFaceNeighborhoodAugmentedCechNerve :
    SimplicialObject.Augmented SSet :=
  boundarySevenFaceNeighborhoodPresentationArrow.augmentedCechNerve

/-- Apply integral simplicial chains in the singular direction to the augmented Čech nerve. -/
public noncomputable def boundarySevenFaceNeighborhoodAugmentedCechChains :
    SimplicialObject.Augmented (ChainComplex AddCommGrpCat ℕ) :=
  ((SimplicialObject.Augmented.whiskering SSet
    (ChainComplex AddCommGrpCat ℕ)).obj
      ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ))).obj
        boundarySevenFaceNeighborhoodAugmentedCechNerve

/-- The Čech--singular bicomplex for the eight explicit face neighborhoods. -/
public noncomputable def boundarySevenFaceNeighborhoodCechBicomplex :
    HomologicalComplex₂ AddCommGrpCat (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  AlternatingFaceMapComplex.obj
    (SimplicialObject.Augmented.drop.obj
      boundarySevenFaceNeighborhoodAugmentedCechChains)

/-- The direct-sum total Čech--singular complex for the eight explicit face neighborhoods. -/
public noncomputable def boundarySevenFaceNeighborhoodCechTotal :
    ChainComplex AddCommGrpCat ℕ :=
  boundarySevenFaceNeighborhoodCechBicomplex.total (ComplexShape.down ℕ)

/-- The canonical outer Čech augmentation before totalization.  Its target is the horizontal
degree-zero complex on the cover-small singular chain complex. -/
public noncomputable def boundarySevenFaceNeighborhoodCechOuterAugmentation :
    boundarySevenFaceNeighborhoodCechBicomplex ⟶
      (ChainComplex.single₀ (ChainComplex AddCommGrpCat ℕ)).obj
        (CoverSmallIntegralSingularChainComplex
          (SSet.toTop.obj (∂Δ[7] : SSet.{0}))
          boundarySevenComparisonFaceNeighborhood) :=
  AlternatingFaceMapComplex.ε.app
    boundarySevenFaceNeighborhoodAugmentedCechChains

/-- Exact data still needed to turn rowwise Čech exactness and the local face contractions
into the comparison theorem.  The first map is the local face/intersection comparison; the
second is the totalized canonical Čech augmentation. -/
public structure BoundarySevenFaceNeighborhoodCechTotalComparison where
  boundaryToCech :
    (∂Δ[7] : SSet.{0}).chainComplex (AddCommGrpCat.of ℤ) ⟶
      boundarySevenFaceNeighborhoodCechTotal
  augmentation :
    boundarySevenFaceNeighborhoodCechTotal ⟶
      CoverSmallIntegralSingularChainComplex
        (SSet.toTop.obj (∂Δ[7] : SSet.{0}))
        boundarySevenComparisonFaceNeighborhood
  fac : boundaryToCech ≫ augmentation =
    simplicialToCoverSmallSingularChainMap
      (∂Δ[7] : SSet.{0}) boundarySevenComparisonFaceNeighborhood
      boundarySevenComparisonUnitLandsInFaceNeighborhoods
  boundaryToCech_quasiIso : QuasiIso boundaryToCech
  augmentation_quasiIso : QuasiIso augmentation

/-- A Čech total comparison supplies the remaining face-neighborhood lift
quasi-isomorphism. -/
public theorem boundarySevenFaceNeighborhoodLiftQuasiIsomorphism_of_cechTotalComparison
    (h : BoundarySevenFaceNeighborhoodCechTotalComparison) :
    BoundarySevenFaceNeighborhoodLiftQuasiIsomorphism := by
  unfold BoundarySevenFaceNeighborhoodLiftQuasiIsomorphism
  rw [← h.fac]
  let _ : QuasiIso h.boundaryToCech := h.boundaryToCech_quasiIso
  let _ : QuasiIso h.augmentation := h.augmentation_quasiIso
  infer_instance

/-- The Čech total comparison also gives the original canonical integral comparison, since the
global affine-boundary cover assertion was proved above. -/
public theorem boundarySeven_integralComparison_of_cechTotalComparison
    (h : BoundarySevenFaceNeighborhoodCechTotalComparison) :
    SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ) :=
  boundarySeven_integralComparison_of_faceNeighborhoodLift
    boundarySevenComparisonMapLandsInAffineBoundary
    (boundarySevenFaceNeighborhoodLiftQuasiIsomorphism_of_cechTotalComparison h)

end SphereSixComplex
