module

public import SphereSixComplex.Topology.BoundarySevenNormalizedGeneratorHomology
public import SphereSixComplex.Topology.BoundarySevenProperFaceAffineGenerator
public import SphereSixComplex.Topology.BoundarySevenProperFaceGeneratorDegreeReduction
public import SphereSixComplex.Topology.SixSphereHomologicalDegreeScalar

/-!
# Degree transport from the proper-face generator

This file closes the generator-transport reduction.  First it strengthens the ambient affine
chain identity to singular chains in the ordinary simplex boundary.  It then transports the
explicit normalized orientation through that identity and proves the proper-face degree formula.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits ContinuousMap Opposite PartialOrder
  Simplicial

namespace SphereSixComplex

/-- The canonical map from the realization of the simplicial boundary to the ordinary affine
boundary, bundled as a morphism of topological spaces. -/
public noncomputable def boundarySevenRealizationToBoundaryTopMap :
    SSet.toTop.obj (∂Δ[7] : SSet.{0}) ⟶
      TopCat.of (StandardSimplexBoundary 7) :=
  TopCat.ofHom boundarySevenRealizationToBoundary

/-- The ambient realization map factors through the ordinary affine boundary. -/
public theorem boundarySevenRealizationToStdSimplexTopMap_factorization_boundary :
    boundarySevenRealizationToBoundaryTopMap ≫
        standardSimplexBoundaryToStdSimplexTopMap =
      boundarySevenRealizationToStdSimplexTopMap := by
  rfl

/-- Forgetting that a singular simplex lands in the affine boundary is injective in every
simplicial degree. -/
public theorem standardSimplexBoundaryToStdSimplex_singularMap_app_injective
    (n : ℕ) :
    Function.Injective
      ((TopCat.toSSet.map standardSimplexBoundaryToStdSimplexTopMap).app
        (Opposite.op (SimplexCategory.mk n))) := by
  intro f g hfg
  apply (TopCat.toSSetObjEquiv _ _).injective
  apply ContinuousMap.ext
  intro w
  apply Subtype.ext
  have h := congrArg
    (fun q ↦ (TopCat.toSSetObjEquiv
      (TopCat.of (stdSimplex ℝ (Fin 8)))
        (Opposite.op (SimplexCategory.mk n)) q) w) hfg
  exact h

/-- The induced map from boundary-valued to ambient singular chains is degreewise monic. -/
public theorem standardSimplexBoundaryToStdSimplex_singularChainMap_f_mono
    (n : ℕ) :
    Mono ((SSet.chainComplexMap
      (TopCat.toSSet.map standardSimplexBoundaryToStdSimplexTopMap)
      (AddCommGrpCat.of ℤ)).f n) :=
  chainComplexMap_f_mono_of_app_injective
    (TopCat.toSSet.map standardSimplexBoundaryToStdSimplexTopMap) n
      (standardSimplexBoundaryToStdSimplex_singularMap_app_injective n)

/-- The proper-face affine generator agrees with the original comparison generator already in
singular chains of the ordinary boundary, after one affine subdivision. -/
public theorem boundarySevenProperFaceGenerator_eq_original_after_affineSubdivision_boundary :
    boundarySevenProperFaceFundamentalChain ≫
        (SSet.chainComplexMap boundarySevenProperFaceAffineSingularMap
          (AddCommGrpCat.of ℤ)).f 6 =
      ((boundarySevenOriginalFundamentalChain ≫
          (simplicialToRealizationSingularChainMap
            (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ)).f 6) ≫
        (SSet.chainComplexMap
          (TopCat.toSSet.map boundarySevenRealizationToBoundaryTopMap)
          (AddCommGrpCat.of ℤ)).f 6) ≫
      (affineSingularSubdivisionChainMap
        (TopCat.of (StandardSimplexBoundary 7))).f 6 := by
  let A := SSet.chainComplexMap boundarySevenProperFaceAffineSingularMap
    (AddCommGrpCat.of ℤ)
  let B := simplicialToRealizationSingularChainMap
    (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ)
  let R := SSet.chainComplexMap
    (TopCat.toSSet.map boundarySevenRealizationToBoundaryTopMap)
      (AddCommGrpCat.of ℤ)
  let V := SSet.chainComplexMap
    (TopCat.toSSet.map standardSimplexBoundaryToStdSimplexTopMap)
      (AddCommGrpCat.of ℤ)
  let Sd := affineSingularSubdivisionChainMap
    (TopCat.of (StandardSimplexBoundary 7))
  let Sa := affineSingularSubdivisionChainMap
    (TopCat.of (stdSimplex ℝ (Fin 8)))
  let _ : Mono (V.f 6) :=
    standardSimplexBoundaryToStdSimplex_singularChainMap_f_mono 6
  apply (cancel_mono (V.f 6)).1
  have htop := congrArg (fun f ↦ TopCat.toSSet.map f)
    boundarySevenRealizationToStdSimplexTopMap_factorization_boundary
  rw [Functor.map_comp] at htop
  have hsset := ((SSet.chainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)).congr_map htop
  have hfactor := congrArg (fun K ↦ K.f 6) hsset
  rw [Functor.map_comp] at hfactor
  change R.f 6 ≫ V.f 6 =
    (SSet.chainComplexMap
      (TopCat.toSSet.map boundarySevenRealizationToStdSimplexTopMap)
      (AddCommGrpCat.of ℤ)).f 6 at hfactor
  have hnat := congrArg (fun K ↦ K.f 6)
    (affineSingularSubdivisionChainMap_naturality
      standardSimplexBoundaryToStdSimplexTopMap)
  change V.f 6 ≫ Sa.f 6 = Sd.f 6 ≫ V.f 6 at hnat
  calc
    (boundarySevenProperFaceFundamentalChain ≫ A.f 6) ≫ V.f 6 =
        ((boundarySevenOriginalFundamentalChain ≫ B.f 6) ≫
          (SSet.chainComplexMap
            (TopCat.toSSet.map boundarySevenRealizationToStdSimplexTopMap)
            (AddCommGrpCat.of ℤ)).f 6) ≫ Sa.f 6 :=
      boundarySevenProperFaceGenerator_eq_original_after_affineSubdivision
    _ = ((boundarySevenOriginalFundamentalChain ≫ B.f 6) ≫
          (R.f 6 ≫ V.f 6)) ≫ Sa.f 6 := by rw [hfactor]
    _ = ((boundarySevenOriginalFundamentalChain ≫ B.f 6) ≫ R.f 6) ≫
          (V.f 6 ≫ Sa.f 6) := by simp only [Category.assoc]
    _ = ((boundarySevenOriginalFundamentalChain ≫ B.f 6) ≫ R.f 6) ≫
          (Sd.f 6 ≫ V.f 6) := by rw [hnat]
    _ = (((boundarySevenOriginalFundamentalChain ≫ B.f 6) ≫ R.f 6) ≫
          Sd.f 6) ≫ V.f 6 := by simp only [Category.assoc]

/-! ## Homology classes represented by explicit cycles -/

/-- Postcomposition of a degree-six cycle by a chain map is again a cycle. -/
public theorem degreeSixCycle_comp_chainMap_isCycle
    {K L : ChainComplex AddCommGrpCat ℕ}
    (F : K ⟶ L) (c : AddCommGrpCat.of ℤ ⟶ K.X 6)
    (hc : c ≫ K.d 6 5 = 0) :
    (c ≫ F.f 6) ≫ L.d 6 5 = 0 := by
  rw [Category.assoc, F.comm 6 5, ← Category.assoc, hc, zero_comp]

/-- The degree-six homology class represented by a chain-level cycle. -/
public noncomputable def degreeSixCycleHomologyClass
    (K : ChainComplex AddCommGrpCat ℕ)
    (c : AddCommGrpCat.of ℤ ⟶ K.X 6)
    (hc : c ≫ K.d 6 5 = 0) :
    AddCommGrpCat.of ℤ ⟶ K.homology 6 :=
  K.liftCycles c 5 (by simp) hc ≫ K.homologyπ 6

/-- Cycle representatives commute with the homology map induced by a chain map. -/
public theorem degreeSixCycleHomologyClass_naturality
    {K L : ChainComplex AddCommGrpCat ℕ}
    (F : K ⟶ L) (c : AddCommGrpCat.of ℤ ⟶ K.X 6)
    (hc : c ≫ K.d 6 5 = 0) :
    degreeSixCycleHomologyClass K c hc ≫
        HomologicalComplex.homologyMap F 6 =
      degreeSixCycleHomologyClass L (c ≫ F.f 6)
        (degreeSixCycle_comp_chainMap_isCycle F c hc) := by
  unfold degreeSixCycleHomologyClass
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
  rw [← Category.assoc]
  rw [HomologicalComplex.liftCycles_comp_cyclesMap]

/-- Taking the homology class of a scalar multiple of a cycle scales its class. -/
public theorem degreeSixCycleHomologyClass_zsmul
    (K : ChainComplex AddCommGrpCat ℕ)
    (c : AddCommGrpCat.of ℤ ⟶ K.X 6)
    (hc : c ≫ K.d 6 5 = 0) (z : ℤ) :
    degreeSixCycleHomologyClass K (z • c)
        (by rw [Preadditive.zsmul_comp, hc, smul_zero]) =
      z • degreeSixCycleHomologyClass K c hc := by
  unfold degreeSixCycleHomologyClass
  have hlift :
      K.liftCycles (z • c) 5 (by simp)
          (by rw [Preadditive.zsmul_comp, hc, smul_zero]) =
        z • K.liftCycles c 5 (by simp) hc := by
    apply (cancel_mono (K.iCycles 6)).1
    rw [HomologicalComplex.liftCycles_i]
    rw [Preadditive.zsmul_comp, HomologicalComplex.liftCycles_i]
  rw [hlift, Preadditive.zsmul_comp]

/-- The homology class depends only on its chain representative, not on the selected proof that
the representative is a cycle. -/
public theorem degreeSixCycleHomologyClass_eq_of_eq
    (K : ChainComplex AddCommGrpCat ℕ)
    (c d : AddCommGrpCat.of ℤ ⟶ K.X 6)
    (hc : c ≫ K.d 6 5 = 0) (hd : d ≫ K.d 6 5 = 0)
    (h : c = d) :
    degreeSixCycleHomologyClass K c hc =
      degreeSixCycleHomologyClass K d hd := by
  subst d
  rfl

/-- The homology class of the proper-face fundamental cycle. -/
public noncomputable def boundarySevenProperFaceFundamentalHomologyClass :
    AddCommGrpCat.of ℤ ⟶
      (BoundarySevenProperFaceNerve.chainComplex
        (AddCommGrpCat.of ℤ)).homology 6 :=
  degreeSixCycleHomologyClass
    (BoundarySevenProperFaceNerve.chainComplex (AddCommGrpCat.of ℤ))
    boundarySevenProperFaceFundamentalChain
    boundarySevenProperFaceFundamentalChain_isCycle

/-- The proper-face class transported by its affine realization to singular homology of the
ordinary simplex boundary. -/
public noncomputable def boundarySevenProperFaceSingularBoundaryHomologyClass :
    AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (StandardSimplexBoundary 7))).chainComplex
          (AddCommGrpCat.of ℤ)).homology 6 :=
  boundarySevenProperFaceFundamentalHomologyClass ≫
    HomologicalComplex.homologyMap
      (SSet.chainComplexMap boundarySevenProperFaceAffineSingularMap
        (AddCommGrpCat.of ℤ)) 6

/-- The original boundary class transported by the canonical realization homeomorphism to
singular homology of the ordinary simplex boundary. -/
public noncomputable def boundarySevenOriginalSingularBoundaryHomologyClass :
    AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (StandardSimplexBoundary 7))).chainComplex
          (AddCommGrpCat.of ℤ)).homology 6 :=
  boundarySevenOriginalFundamentalHomologyClass ≫
    HomologicalComplex.homologyMap
      (simplicialToRealizationSingularChainMap
        (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ)) 6 ≫
    HomologicalComplex.homologyMap
      (SSet.chainComplexMap
        (TopCat.toSSet.map boundarySevenRealizationToBoundaryTopMap)
        (AddCommGrpCat.of ℤ)) 6

/-- The proper-face affine singular class is the original singular boundary class. -/
public theorem boundarySevenProperFaceSingularBoundaryHomologyClass_eq_original :
    boundarySevenProperFaceSingularBoundaryHomologyClass =
      boundarySevenOriginalSingularBoundaryHomologyClass := by
  let K := (BoundarySevenProperFaceNerve.chainComplex (AddCommGrpCat.of ℤ))
  let L := (TopCat.toSSet.obj
    (TopCat.of (StandardSimplexBoundary 7))).chainComplex (AddCommGrpCat.of ℤ)
  let A := SSet.chainComplexMap boundarySevenProperFaceAffineSingularMap
    (AddCommGrpCat.of ℤ)
  let B := simplicialToRealizationSingularChainMap
    (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ)
  let R := SSet.chainComplexMap
    (TopCat.toSSet.map boundarySevenRealizationToBoundaryTopMap)
      (AddCommGrpCat.of ℤ)
  let Sd := affineSingularSubdivisionChainMap
    (TopCat.of (StandardSimplexBoundary 7))
  have hsubdivision : HomologicalComplex.homologyMap Sd 6 = 𝟙 (L.homology 6) := by
    dsimp only [Sd, L]
    rw [(affineSingularSubdivisionHomotopy
      (TopCat.of (StandardSimplexBoundary 7))).homologyMap_eq 6]
    exact HomologicalComplex.homologyMap_id _ _
  have hproper := degreeSixCycleHomologyClass_naturality A
    boundarySevenProperFaceFundamentalChain
      boundarySevenProperFaceFundamentalChain_isCycle
  have horiginalB := degreeSixCycleHomologyClass_naturality B
    boundarySevenOriginalFundamentalChain
      boundarySevenOriginalFundamentalChain_isCycle
  have horiginalR := degreeSixCycleHomologyClass_naturality R
    (boundarySevenOriginalFundamentalChain ≫ B.f 6)
      (degreeSixCycle_comp_chainMap_isCycle B
        boundarySevenOriginalFundamentalChain
          boundarySevenOriginalFundamentalChain_isCycle)
  have horiginalSd := degreeSixCycleHomologyClass_naturality Sd
    ((boundarySevenOriginalFundamentalChain ≫ B.f 6) ≫ R.f 6)
      (degreeSixCycle_comp_chainMap_isCycle R
        (boundarySevenOriginalFundamentalChain ≫ B.f 6)
        (degreeSixCycle_comp_chainMap_isCycle B
          boundarySevenOriginalFundamentalChain
            boundarySevenOriginalFundamentalChain_isCycle))
  have hchain :=
    boundarySevenProperFaceGenerator_eq_original_after_affineSubdivision_boundary
  change boundarySevenProperFaceFundamentalChain ≫ A.f 6 =
    ((boundarySevenOriginalFundamentalChain ≫ B.f 6) ≫ R.f 6) ≫
      Sd.f 6 at hchain
  have hclasses :
      degreeSixCycleHomologyClass L
          (boundarySevenProperFaceFundamentalChain ≫ A.f 6)
          (degreeSixCycle_comp_chainMap_isCycle A
            boundarySevenProperFaceFundamentalChain
              boundarySevenProperFaceFundamentalChain_isCycle) =
        degreeSixCycleHomologyClass L
          (((boundarySevenOriginalFundamentalChain ≫ B.f 6) ≫ R.f 6) ≫
            Sd.f 6)
          (degreeSixCycle_comp_chainMap_isCycle Sd
            ((boundarySevenOriginalFundamentalChain ≫ B.f 6) ≫ R.f 6)
            (degreeSixCycle_comp_chainMap_isCycle R
              (boundarySevenOriginalFundamentalChain ≫ B.f 6)
              (degreeSixCycle_comp_chainMap_isCycle B
                boundarySevenOriginalFundamentalChain
                  boundarySevenOriginalFundamentalChain_isCycle))) := by
    exact degreeSixCycleHomologyClass_eq_of_eq L _ _ _ _ hchain
  have horiginalBase :
      boundarySevenOriginalFundamentalHomologyClass =
        degreeSixCycleHomologyClass
          ((∂Δ[7] : SSet.{0}).chainComplex (AddCommGrpCat.of ℤ))
          boundarySevenOriginalFundamentalChain
          boundarySevenOriginalFundamentalChain_isCycle := by
    rfl
  calc
    boundarySevenProperFaceSingularBoundaryHomologyClass =
        degreeSixCycleHomologyClass L
          (boundarySevenProperFaceFundamentalChain ≫ A.f 6)
          (degreeSixCycle_comp_chainMap_isCycle A
            boundarySevenProperFaceFundamentalChain
              boundarySevenProperFaceFundamentalChain_isCycle) := by
      rw [boundarySevenProperFaceSingularBoundaryHomologyClass,
        boundarySevenProperFaceFundamentalHomologyClass]
      exact hproper
    _ = degreeSixCycleHomologyClass L
          (((boundarySevenOriginalFundamentalChain ≫ B.f 6) ≫ R.f 6) ≫
            Sd.f 6)
          (degreeSixCycle_comp_chainMap_isCycle Sd
            ((boundarySevenOriginalFundamentalChain ≫ B.f 6) ≫ R.f 6)
            (degreeSixCycle_comp_chainMap_isCycle R
              (boundarySevenOriginalFundamentalChain ≫ B.f 6)
              (degreeSixCycle_comp_chainMap_isCycle B
                boundarySevenOriginalFundamentalChain
                  boundarySevenOriginalFundamentalChain_isCycle))) := hclasses
    _ = degreeSixCycleHomologyClass L
          ((boundarySevenOriginalFundamentalChain ≫ B.f 6) ≫ R.f 6)
          (degreeSixCycle_comp_chainMap_isCycle R
            (boundarySevenOriginalFundamentalChain ≫ B.f 6)
            (degreeSixCycle_comp_chainMap_isCycle B
              boundarySevenOriginalFundamentalChain
                boundarySevenOriginalFundamentalChain_isCycle)) ≫
          HomologicalComplex.homologyMap Sd 6 := horiginalSd.symm
    _ = degreeSixCycleHomologyClass L
          ((boundarySevenOriginalFundamentalChain ≫ B.f 6) ≫ R.f 6)
          (degreeSixCycle_comp_chainMap_isCycle R
            (boundarySevenOriginalFundamentalChain ≫ B.f 6)
            (degreeSixCycle_comp_chainMap_isCycle B
              boundarySevenOriginalFundamentalChain
                boundarySevenOriginalFundamentalChain_isCycle)) := by
      rw [hsubdivision, Category.comp_id]
    _ = boundarySevenOriginalSingularBoundaryHomologyClass := by
      rw [← horiginalR, ← horiginalB, ← horiginalBase]
      rfl

/-- A scalar action on the proper-face chain induces the same scalar action on its affine
singular homology class. -/
public theorem boundarySevenProperFaceSingularBoundaryHomologyClass_permutation
    (sigma : Equiv.Perm (Fin 8)) (z : ℤ)
    (h : boundarySevenProperFaceFundamentalChain ≫
          (SSet.chainComplexMap
            (boundarySevenProperFaceNervePermIso sigma).hom
            (AddCommGrpCat.of ℤ)).f 6 =
        z • boundarySevenProperFaceFundamentalChain) :
    boundarySevenProperFaceSingularBoundaryHomologyClass ≫
        HomologicalComplex.homologyMap
          (SSet.chainComplexMap
            (TopCat.toSSet.map (standardSimplexBoundaryPermTopMap sigma))
            (AddCommGrpCat.of ℤ)) 6 =
      z • boundarySevenProperFaceSingularBoundaryHomologyClass := by
  let K := BoundarySevenProperFaceNerve.chainComplex (AddCommGrpCat.of ℤ)
  let L := (TopCat.toSSet.obj
    (TopCat.of (StandardSimplexBoundary 7))).chainComplex (AddCommGrpCat.of ℤ)
  let P := SSet.chainComplexMap
    (boundarySevenProperFaceNervePermIso sigma).hom (AddCommGrpCat.of ℤ)
  let A := SSet.chainComplexMap boundarySevenProperFaceAffineSingularMap
    (AddCommGrpCat.of ℤ)
  let T := SSet.chainComplexMap
    (TopCat.toSSet.map (standardSimplexBoundaryPermTopMap sigma))
      (AddCommGrpCat.of ℤ)
  have hmap := ((SSet.chainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)).congr_map
      (boundarySevenProperFaceAffineSingularMap_equivariant sigma)
  rw [Functor.map_comp, Functor.map_comp] at hmap
  have hmap6 := congrArg (fun F ↦ F.f 6) hmap
  change P.f 6 ≫ A.f 6 = A.f 6 ≫ T.f 6 at hmap6
  have hchain :
      (boundarySevenProperFaceFundamentalChain ≫ A.f 6) ≫ T.f 6 =
        z • (boundarySevenProperFaceFundamentalChain ≫ A.f 6) := by
    calc
      _ = boundarySevenProperFaceFundamentalChain ≫
          (A.f 6 ≫ T.f 6) := Category.assoc _ _ _
      _ = boundarySevenProperFaceFundamentalChain ≫
          (P.f 6 ≫ A.f 6) := by rw [hmap6]
      _ = (boundarySevenProperFaceFundamentalChain ≫ P.f 6) ≫
          A.f 6 := (Category.assoc _ _ _).symm
      _ = (z • boundarySevenProperFaceFundamentalChain) ≫ A.f 6 := by
        rw [h]
      _ = z • (boundarySevenProperFaceFundamentalChain ≫ A.f 6) := by
        rw [Preadditive.zsmul_comp]
  have hA := degreeSixCycleHomologyClass_naturality A
    boundarySevenProperFaceFundamentalChain
      boundarySevenProperFaceFundamentalChain_isCycle
  have hT := degreeSixCycleHomologyClass_naturality T
    (boundarySevenProperFaceFundamentalChain ≫ A.f 6)
      (degreeSixCycle_comp_chainMap_isCycle A
        boundarySevenProperFaceFundamentalChain
          boundarySevenProperFaceFundamentalChain_isCycle)
  calc
    boundarySevenProperFaceSingularBoundaryHomologyClass ≫
          HomologicalComplex.homologyMap T 6 =
        degreeSixCycleHomologyClass L
          (boundarySevenProperFaceFundamentalChain ≫ A.f 6)
          (degreeSixCycle_comp_chainMap_isCycle A
            boundarySevenProperFaceFundamentalChain
              boundarySevenProperFaceFundamentalChain_isCycle) ≫
            HomologicalComplex.homologyMap T 6 := by
      rw [boundarySevenProperFaceSingularBoundaryHomologyClass,
        boundarySevenProperFaceFundamentalHomologyClass, hA]
    _ = degreeSixCycleHomologyClass L
          ((boundarySevenProperFaceFundamentalChain ≫ A.f 6) ≫ T.f 6)
          (degreeSixCycle_comp_chainMap_isCycle T
            (boundarySevenProperFaceFundamentalChain ≫ A.f 6)
            (degreeSixCycle_comp_chainMap_isCycle A
              boundarySevenProperFaceFundamentalChain
                boundarySevenProperFaceFundamentalChain_isCycle)) := hT
    _ = degreeSixCycleHomologyClass L
          (z • (boundarySevenProperFaceFundamentalChain ≫ A.f 6))
          (by
            rw [Preadditive.zsmul_comp]
            rw [degreeSixCycle_comp_chainMap_isCycle A
              boundarySevenProperFaceFundamentalChain
                boundarySevenProperFaceFundamentalChain_isCycle, smul_zero]) := by
      apply degreeSixCycleHomologyClass_eq_of_eq
      exact hchain
    _ = z • degreeSixCycleHomologyClass L
          (boundarySevenProperFaceFundamentalChain ≫ A.f 6)
          (degreeSixCycle_comp_chainMap_isCycle A
            boundarySevenProperFaceFundamentalChain
              boundarySevenProperFaceFundamentalChain_isCycle) :=
      degreeSixCycleHomologyClass_zsmul L _ _ z
    _ = z • boundarySevenProperFaceSingularBoundaryHomologyClass := by
      rw [boundarySevenProperFaceSingularBoundaryHomologyClass,
        boundarySevenProperFaceFundamentalHomologyClass, hA]

/-- The same scalar action holds on the singular class coming from the original simplicial
boundary generator. -/
public theorem boundarySevenOriginalSingularBoundaryHomologyClass_permutation
    (sigma : Equiv.Perm (Fin 8)) (z : ℤ)
    (h : boundarySevenProperFaceFundamentalChain ≫
          (SSet.chainComplexMap
            (boundarySevenProperFaceNervePermIso sigma).hom
            (AddCommGrpCat.of ℤ)).f 6 =
        z • boundarySevenProperFaceFundamentalChain) :
    boundarySevenOriginalSingularBoundaryHomologyClass ≫
        HomologicalComplex.homologyMap
          (SSet.chainComplexMap
            (TopCat.toSSet.map (standardSimplexBoundaryPermTopMap sigma))
            (AddCommGrpCat.of ℤ)) 6 =
      z • boundarySevenOriginalSingularBoundaryHomologyClass := by
  rw [← boundarySevenProperFaceSingularBoundaryHomologyClass_eq_original]
  exact boundarySevenProperFaceSingularBoundaryHomologyClass_permutation sigma z h

/-! ## The explicit sphere orientation and degree -/

/-- The canonical realization homeomorphism followed by a chosen affine-boundary model of the
standard six-sphere. -/
public noncomputable def boundarySevenRealizationHomeomorphSphere
    (e : StandardSimplexBoundary 7 ≃ₜ SixSphere) :
    (SSet.toTop.obj (∂Δ[7] : SSet.{0}) : Type) ≃ₜ SixSphere :=
  (boundarySevenRealizationHomeomorphStandardBoundary_of_injective
    boundarySevenRealizationToBoundary_injective).trans e

/-- The chain-complex isomorphism induced by the canonical realization homeomorphism to the
ordinary affine boundary. -/
public noncomputable def boundarySevenRealizationSingularChainIso :
    (TopCat.toSSet.obj (SSet.toTop.obj (∂Δ[7] : SSet.{0}))).chainComplex
        (AddCommGrpCat.of ℤ) ≅
      (TopCat.toSSet.obj
        (TopCat.of (StandardSimplexBoundary 7))).chainComplex
          (AddCommGrpCat.of ℤ) :=
  ((SSet.chainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)).mapIso
      (TopCat.toSSet.mapIso
        (TopCat.isoOfHomeo
          (boundarySevenRealizationHomeomorphStandardBoundary_of_injective
            boundarySevenRealizationToBoundary_injective)))

/-- The singular chain-complex isomorphism induced by a boundary--sphere homeomorphism. -/
public noncomputable def boundarySevenBoundarySphereSingularChainIso
    (e : StandardSimplexBoundary 7 ≃ₜ SixSphere) :
    (TopCat.toSSet.obj
        (TopCat.of (StandardSimplexBoundary 7))).chainComplex
          (AddCommGrpCat.of ℤ) ≅
      (TopCat.toSSet.obj (TopCat.of SixSphere)).chainComplex
        (AddCommGrpCat.of ℤ) :=
  ((SSet.chainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)).mapIso
      (TopCat.toSSet.mapIso (TopCat.isoOfHomeo e))

/-- The fully explicit top-homology orientation of the standard sphere obtained from the
normalized simplicial generator, the comparison map, and the selected boundary model. -/
public noncomputable def boundarySevenExplicitSphereHomologyIsoInt
    (hcomparison : SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ))
    (e : StandardSimplexBoundary 7 ≃ₜ SixSphere) :
    ((TopCat.toSSet.obj (TopCat.of SixSphere)).chainComplex
      (AddCommGrpCat.of ℤ)).homology 6 ≅ AddCommGrpCat.of ℤ := by
  let _ : QuasiIso (simplicialToRealizationSingularChainMap
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ)) := hcomparison
  let comparisonIso := isoOfQuasiIsoAt
    (simplicialToRealizationSingularChainMap
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ)) 6
  let realizationIso := HomologicalComplex.homologyMapIso
    boundarySevenRealizationSingularChainIso 6
  let sphereIso := HomologicalComplex.homologyMapIso
    (boundarySevenBoundarySphereSingularChainIso e) 6
  exact (comparisonIso.trans realizationIso |>.trans sphereIso).symm ≪≫
    boundarySevenSimplicialHomologySixIsoInt

/-- The additive equivalence underlying the explicit sphere orientation. -/
public noncomputable def boundarySevenExplicitSphereHomologyAddEquivInt
    (hcomparison : SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ))
    (e : StandardSimplexBoundary 7 ≃ₜ SixSphere) :
    IntegralSingularHomology 6 SixSphere ≃+ ℤ :=
  (boundarySevenExplicitSphereHomologyIsoInt hcomparison e).addCommGroupIsoToAddEquiv

/-- The original simplicial generator transported to singular homology of the standard sphere. -/
public noncomputable def boundarySevenOriginalSingularSphereHomologyClass
    (e : StandardSimplexBoundary 7 ≃ₜ SixSphere) :
    AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj (TopCat.of SixSphere)).chainComplex
        (AddCommGrpCat.of ℤ)).homology 6 :=
  boundarySevenOriginalSingularBoundaryHomologyClass ≫
    (HomologicalComplex.homologyMapIso
      (boundarySevenBoundarySphereSingularChainIso e) 6).hom

/-- The transported original class is the positive generator for the explicit sphere
orientation. -/
public theorem boundarySevenOriginalSingularSphereHomologyClass_isoInt
    (hcomparison : SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ))
    (e : StandardSimplexBoundary 7 ≃ₜ SixSphere) :
    boundarySevenOriginalSingularSphereHomologyClass e ≫
        (boundarySevenExplicitSphereHomologyIsoInt hcomparison e).hom =
      𝟙 (AddCommGrpCat.of ℤ) := by
  let _ : QuasiIso (simplicialToRealizationSingularChainMap
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ)) := hcomparison
  let comparisonIso := isoOfQuasiIsoAt
    (simplicialToRealizationSingularChainMap
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ)) 6
  let realizationIso := HomologicalComplex.homologyMapIso
    boundarySevenRealizationSingularChainIso 6
  let sphereIso := HomologicalComplex.homologyMapIso
    (boundarySevenBoundarySphereSingularChainIso e) 6
  let E := comparisonIso.trans realizationIso |>.trans sphereIso
  change (boundarySevenOriginalFundamentalHomologyClass ≫ E.hom) ≫
      (E.symm ≪≫ boundarySevenSimplicialHomologySixIsoInt).hom = 𝟙 _
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  exact boundarySevenOriginalFundamentalHomologyClass_isoInt

/-- Elementwise, the explicit sphere orientation sends the transported original generator to
one. -/
public theorem boundarySevenOriginalSingularSphereHomologyClass_mapsToOne
    (hcomparison : SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ))
    (e : StandardSimplexBoundary 7 ≃ₜ SixSphere) :
    boundarySevenExplicitSphereHomologyAddEquivInt hcomparison e
        (boundarySevenOriginalSingularSphereHomologyClass e (1 : ℤ)) = 1 := by
  have h := ConcreteCategory.congr_hom
    (boundarySevenOriginalSingularSphereHomologyClass_isoInt hcomparison e)
      (1 : ℤ)
  change (boundarySevenExplicitSphereHomologyIsoInt hcomparison e).hom.hom
    (boundarySevenOriginalSingularSphereHomologyClass e |>.hom (1 : ℤ)) = 1
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Transporting first to the ordinary boundary and then along `e` gives the same sphere class
as the composite realization homeomorphism. -/
public theorem boundarySevenOriginalSingularSphereHomologyClass_eq_boundary
    (e : StandardSimplexBoundary 7 ≃ₜ SixSphere) :
    boundarySevenOriginalSingularSphereHomologyClass e =
      boundarySevenOriginalSingularBoundaryHomologyClass ≫
        ((singularHomologyFunctor AddCommGrpCat 6).obj
          (AddCommGrpCat.of ℤ)).map (TopCat.ofHom e) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The scalar action on the original boundary generator transports to the conjugate sphere
self-map. -/
public theorem boundarySevenOriginalSingularSphereHomologyClass_permutation
    (e : StandardSimplexBoundary 7 ≃ₜ SixSphere)
    (sigma : Equiv.Perm (Fin 8)) (z : ℤ)
    (h : boundarySevenProperFaceFundamentalChain ≫
          (SSet.chainComplexMap
            (boundarySevenProperFaceNervePermIso sigma).hom
            (AddCommGrpCat.of ℤ)).f 6 =
        z • boundarySevenProperFaceFundamentalChain) :
    boundarySevenOriginalSingularSphereHomologyClass e ≫
        ((singularHomologyFunctor AddCommGrpCat 6).obj
          (AddCommGrpCat.of ℤ)).map
            (TopCat.ofHom (boundarySevenPermutationSphereMap e sigma)) =
      z • boundarySevenOriginalSingularSphereHomologyClass e := by
  let H := (singularHomologyFunctor AddCommGrpCat 6).obj
    (AddCommGrpCat.of ℤ)
  let eTopIso : TopCat.of (StandardSimplexBoundary 7) ≅ TopCat.of SixSphere :=
    TopCat.isoOfHomeo e
  let eIso := H.mapIso eTopIso
  let P := H.map (standardSimplexBoundaryPermTopMap sigma)
  have hboundary :=
    boundarySevenOriginalSingularBoundaryHomologyClass_permutation sigma z h
  change boundarySevenOriginalSingularBoundaryHomologyClass ≫ P =
    z • boundarySevenOriginalSingularBoundaryHomologyClass at hboundary
  have htop :
      TopCat.ofHom (boundarySevenPermutationSphereMap e sigma) =
        eTopIso.inv ≫
          standardSimplexBoundaryPermTopMap sigma ≫
            eTopIso.hom := by
    rfl
  have hmap := congrArg (fun f ↦ H.map f) htop
  simp only [Functor.map_comp] at hmap
  change H.map (TopCat.ofHom (boundarySevenPermutationSphereMap e sigma)) =
    eIso.inv ≫ P ≫ eIso.hom at hmap
  rw [boundarySevenOriginalSingularSphereHomologyClass_eq_boundary]
  calc
    (boundarySevenOriginalSingularBoundaryHomologyClass ≫ eIso.hom) ≫
          H.map (TopCat.ofHom (boundarySevenPermutationSphereMap e sigma)) =
        (boundarySevenOriginalSingularBoundaryHomologyClass ≫ eIso.hom) ≫
          (eIso.inv ≫ P ≫ eIso.hom) := by rw [hmap]
    _ = (boundarySevenOriginalSingularBoundaryHomologyClass ≫ P) ≫
          eIso.hom := by simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = (z • boundarySevenOriginalSingularBoundaryHomologyClass) ≫
          eIso.hom := congrArg (fun q ↦ q ≫ eIso.hom) hboundary
    _ = z •
          (boundarySevenOriginalSingularBoundaryHomologyClass ≫ eIso.hom) :=
      Preadditive.zsmul_comp _ _ z

set_option backward.isDefEq.respectTransparency false in
/-- The proper-face fundamental cycle computes the homological degree for every vertex
permutation.  No generator-transport assumption remains: the explicit normalized orientation
computes the degree first, and orientation-independence transfers the result to the orientation
used by the public comparison API. -/
public theorem boundarySevenProperFaceGeneratorDegreeTransport_proof
    (hcomparison : SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ))
    (e : StandardSimplexBoundary 7 ≃ₜ SixSphere) :
    BoundarySevenProperFaceGeneratorDegreeTransport hcomparison e := by
  intro sigma z h
  let orientation₀ :=
    boundarySevenExplicitSphereHomologyAddEquivInt hcomparison e
  let c := boundarySevenOriginalSingularSphereHomologyClass e
  have hdegree₀ :
      sixSphereHomologicalDegree orientation₀
        (boundarySevenPermutationSphereMap e sigma) = z := by
    rw [sixSphereHomologicalDegree]
    have hc_one : orientation₀ (c (1 : ℤ)) = 1 :=
      boundarySevenOriginalSingularSphereHomologyClass_mapsToOne hcomparison e
    have horientation_symm : orientation₀.symm 1 = c (1 : ℤ) := by
      apply orientation₀.injective
      rw [orientation₀.apply_symm_apply, hc_one]
    rw [horientation_symm]
    let H := (singularHomologyFunctor AddCommGrpCat 6).obj
      (AddCommGrpCat.of ℤ)
    change orientation₀
      ((H.map (TopCat.ofHom
        (boundarySevenPermutationSphereMap e sigma))).hom (c.hom (1 : ℤ))) = z
    have hperm := ConcreteCategory.congr_hom
      (boundarySevenOriginalSingularSphereHomologyClass_permutation e sigma z h)
        (1 : ℤ)
    change (H.map (TopCat.ofHom
        (boundarySevenPermutationSphereMap e sigma))).hom (c.hom (1 : ℤ)) =
      z • c.hom (1 : ℤ) at hperm
    rw [hperm]
    calc
      orientation₀ (z • c (1 : ℤ)) =
          z • orientation₀ (c (1 : ℤ)) :=
        orientation₀.toAddMonoidHom.map_zsmul _ _
      _ = z := by rw [hc_one]; simp
  exact sixSphereHomologicalDegree_allOrientations_of_one orientation₀
    (boundarySevenPermutationSphereMap e sigma) z hdegree₀
      (sixSphereTopHomologyAddEquivOfStandardBoundaryComparison hcomparison e)

end SphereSixComplex
