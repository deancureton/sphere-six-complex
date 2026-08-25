module

public import SphereSixComplex.Topology.BoundarySevenProperFaceRealizationInjective
public import SphereSixComplex.Topology.BoundarySevenSubdivisionGeneratorTransportPrelude
public import SphereSixComplex.Topology.SingularAffineSubdivisionPrism

/-!
# The proper-face fundamental chain under affine realization

This file evaluates the intrinsic proper-face generator under the explicit affine singular map.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory ContinuousMap Opposite PartialOrder Simplicial

namespace SphereSixComplex

/-- The standard homeomorphism from the realization of a representable simplex to its ordinary
topological simplex, regarded as a morphism of topological spaces. -/
public noncomputable def standardSimplexRealizationToStdSimplexTopMap (n : ℕ) :
    SSet.toTop.obj (Δ[n] : SSet.{0}) ⟶
      TopCat.of (stdSimplex ℝ (Fin (n + 1))) :=
  TopCat.ofHom ⟨SimplexCategory.toTopHomeo (SimplexCategory.mk n),
    (SimplexCategory.toTopHomeo (SimplexCategory.mk n)).continuous⟩

set_option backward.isDefEq.respectTransparency false in
/-- The top simplex sent through the realization/singular adjunction unit and the standard
realization homeomorphism is the universal identity singular simplex. -/
theorem standardSimplexTopSimplex_comparison_realization
    (n : ℕ) :
    (TopCat.toSSet.map (standardSimplexRealizationToStdSimplexTopMap n)).app
        (Opposite.op (SimplexCategory.mk n))
        ((sSetTopAdj.unit.app (Δ[n] : SSet.{0})).app
          (Opposite.op (SimplexCategory.mk n))
          (standardSimplexTopSimplex n)) =
      standardTopologicalSimplexIdentitySimplex n := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  apply ContinuousMap.ext
  intro w
  have hunit := sSetTopAdj_unit_app_app_down (Δ[n] : SSet.{0})
    (Opposite.op (SimplexCategory.mk n)) (standardSimplexTopSimplex n)
  have hid : SSet.yonedaEquiv.symm (standardSimplexTopSimplex n) =
      𝟙 (Δ[n] : SSet.{0}) := by
    apply SSet.yonedaEquiv.injective
    rfl
  have hmapid : SSet.toTop.map (𝟙 (Δ[n] : SSet.{0})) =
      𝟙 (SSet.toTop.obj (Δ[n] : SSet.{0})) :=
    SSet.toTop.map_id _
  have hunit' :
      ((sSetTopAdj.unit.app (Δ[n] : SSet.{0})).app
        (Opposite.op (SimplexCategory.mk n))
        (standardSimplexTopSimplex n)).down =
          SSet.toTopSimplex.inv.app (SimplexCategory.mk n) := by
    calc
      _ = SSet.toTopSimplex.inv.app (SimplexCategory.mk n) ≫
          SSet.toTop.map
            (SSet.yonedaEquiv.symm (standardSimplexTopSimplex n)) := hunit
      _ = SSet.toTopSimplex.inv.app (SimplexCategory.mk n) ≫
          𝟙 (SSet.toTop.obj (Δ[n] : SSet.{0})) := by rw [hid, hmapid]
      _ = SSet.toTopSimplex.inv.app (SimplexCategory.mk n) :=
        Category.comp_id _
  have hpoint := ConcreteCategory.congr_hom hunit' (ULift.up w)
  have hinv :
      ConcreteCategory.hom
          (SSet.toTopSimplex.inv.app (SimplexCategory.mk n)) (ULift.up w) =
        (SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm w := by
    rfl
  change SimplexCategory.toTopHomeo (SimplexCategory.mk n)
      (((sSetTopAdj.unit.app (Δ[n] : SSet.{0})).app
        (Opposite.op (SimplexCategory.mk n))
        (standardSimplexTopSimplex n)).down.hom (ULift.up w)) = w
  rw [hpoint]
  calc
    _ = SimplexCategory.toTopHomeo (SimplexCategory.mk n)
        ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm w) :=
      congrArg (SimplexCategory.toTopHomeo (SimplexCategory.mk n)) hinv
    _ = w := Homeomorph.apply_symm_apply _ _

/-- Chain-level form of `standardSimplexTopSimplex_comparison_realization`. -/
public theorem standardSimplexTopSimplexChain_comparison_realization
    (n : ℕ) :
    (((Δ[n] : SSet.{0}).ιChainComplex (standardSimplexTopSimplex n) ≫
        (simplicialToRealizationSingularChainMap
          (Δ[n] : SSet.{0}) (AddCommGrpCat.of ℤ)).f n) ≫
      (SSet.chainComplexMap
        (TopCat.toSSet.map (standardSimplexRealizationToStdSimplexTopMap n))
        (AddCommGrpCat.of ℤ)).f n) =
    (TopCat.toSSet.obj
      (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).ιChainComplex
        (standardTopologicalSimplexIdentitySimplex n) := by
  unfold simplicialToRealizationSingularChainMap
  rw [SSet.ι_chainComplexMap_f, SSet.ι_chainComplexMap_f]
  exact congrArg
    (TopCat.toSSet.obj
      (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).ιChainComplex
      (standardSimplexTopSimplex_comparison_realization n)

/-- The canonical realization map from the simplicial boundary to the ambient ordinary
seven-simplex, as a morphism of topological spaces. -/
public noncomputable def boundarySevenRealizationToStdSimplexTopMap :
    SSet.toTop.obj (∂Δ[7] : SSet.{0}) ⟶
      TopCat.of (stdSimplex ℝ (Fin 8)) :=
  TopCat.ofHom boundarySevenRealizationToStdSimplex

/-- Realizing the simplicial boundary inclusion and then using the standard representable
homeomorphism is the canonical affine map from the realized boundary. -/
public theorem boundarySevenRealizationToStdSimplexTopMap_factorization :
    SSet.toTop.map
        ((SSet.boundary 7 : SSet.Subcomplex (Δ[7] : SSet.{0})).ι) ≫
      standardSimplexRealizationToStdSimplexTopMap 7 =
    boundarySevenRealizationToStdSimplexTopMap := by
  rfl

/-- Naturality of the canonical comparison, followed by the affine realization map, identifies
the boundary route with inclusion into the full representable simplex. -/
public theorem boundarySevenComparisonRealizationToStdSimplex_factorization :
    SSet.chainComplexMap
          ((SSet.boundary 7 : SSet.Subcomplex (Δ[7] : SSet.{0})).ι)
          (AddCommGrpCat.of ℤ) ≫
        simplicialToRealizationSingularChainMap
          (Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ) ≫
      SSet.chainComplexMap
        (TopCat.toSSet.map (standardSimplexRealizationToStdSimplexTopMap 7))
        (AddCommGrpCat.of ℤ) =
    simplicialToRealizationSingularChainMap
          (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ) ≫
      SSet.chainComplexMap
        (TopCat.toSSet.map boundarySevenRealizationToStdSimplexTopMap)
        (AddCommGrpCat.of ℤ) := by
  let j := (SSet.boundary 7 : SSet.Subcomplex (Δ[7] : SSet.{0})).ι
  rw [← Category.assoc, simplicialToRealizationSingularChainMap_naturality j,
    Category.assoc]
  congr 1
  rw [← Functor.map_comp, ← Functor.map_comp,
    boundarySevenRealizationToStdSimplexTopMap_factorization]

/-- The intrinsic alternating boundary, sent through the canonical comparison and the affine
boundary realization, is the ordinary singular boundary of the universal seven-simplex. -/
public theorem boundarySevenOriginalFundamentalChain_comparison_realization_stdSimplex :
    (boundarySevenOriginalFundamentalChain ≫
        (simplicialToRealizationSingularChainMap
          (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ)).f 6) ≫
      (SSet.chainComplexMap
        (TopCat.toSSet.map boundarySevenRealizationToStdSimplexTopMap)
        (AddCommGrpCat.of ℤ)).f 6 =
    (TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin 8)))).ιChainComplex
          (standardTopologicalSimplexIdentitySimplex 7) ≫
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin 8)))).chainComplex
          (AddCommGrpCat.of ℤ)).d 7 6 := by
  let j := (SSet.boundary 7 : SSet.Subcomplex (Δ[7] : SSet.{0})).ι
  let Cbdry := simplicialToRealizationSingularChainMap
    (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ)
  let Tbdry := SSet.chainComplexMap
    (TopCat.toSSet.map boundarySevenRealizationToStdSimplexTopMap)
      (AddCommGrpCat.of ℤ)
  let Cstd := simplicialToRealizationSingularChainMap
    (Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ)
  let Tstd := SSet.chainComplexMap
    (TopCat.toSSet.map (standardSimplexRealizationToStdSimplexTopMap 7))
      (AddCommGrpCat.of ℤ)
  let J := SSet.chainComplexMap j (AddCommGrpCat.of ℤ)
  have hfactor := congrArg (fun K ↦ K.f 6)
    boundarySevenComparisonRealizationToStdSimplex_factorization
  change (J ≫ Cstd ≫ Tstd).f 6 = (Cbdry ≫ Tbdry).f 6 at hfactor
  have hfactor' : J.f 6 ≫ Cstd.f 6 ≫ Tstd.f 6 =
      Cbdry.f 6 ≫ Tbdry.f 6 := by
    exact hfactor
  calc
    (boundarySevenOriginalFundamentalChain ≫ Cbdry.f 6) ≫ Tbdry.f 6 =
        boundarySevenOriginalFundamentalChain ≫ (Cbdry.f 6 ≫ Tbdry.f 6) :=
      Category.assoc _ _ _
    _ = boundarySevenOriginalFundamentalChain ≫
          (J.f 6 ≫ Cstd.f 6 ≫ Tstd.f 6) := by rw [hfactor']
    _ = ((boundarySevenOriginalFundamentalChain ≫ J.f 6) ≫
          Cstd.f 6) ≫ Tstd.f 6 := by simp only [Category.assoc]
    _ = (standardSevenOriginalBoundaryChain ≫ Cstd.f 6) ≫ Tstd.f 6 := by
      rw [boundarySevenOriginalFundamentalChain_comp_boundaryInclusion]
    _ = (((standardSevenTopSimplexChain ≫ Cstd.f 7) ≫ Tstd.f 7) ≫
          ((TopCat.toSSet.obj
            (TopCat.of (stdSimplex ℝ (Fin 8)))).chainComplex
              (AddCommGrpCat.of ℤ)).d 7 6) := by
      rw [standardSevenOriginalBoundaryChain]
      calc
        ((standardSevenTopSimplexChain ≫
            ((Δ[7] : SSet.{0}).chainComplex
              (AddCommGrpCat.of ℤ)).d 7 6) ≫ Cstd.f 6) ≫ Tstd.f 6 =
            (standardSevenTopSimplexChain ≫
              (((Δ[7] : SSet.{0}).chainComplex
                (AddCommGrpCat.of ℤ)).d 7 6 ≫ Cstd.f 6)) ≫ Tstd.f 6 :=
          congrArg (fun q ↦ q ≫ Tstd.f 6)
            (Category.assoc _ _ _)
        _ = (standardSevenTopSimplexChain ≫
              (Cstd.f 7 ≫
                ((TopCat.toSSet.obj
                  (SSet.toTop.obj (Δ[7] : SSet.{0}))).chainComplex
                    (AddCommGrpCat.of ℤ)).d 7 6)) ≫ Tstd.f 6 := by
          rw [Cstd.comm 7 6]
        _ = ((standardSevenTopSimplexChain ≫ Cstd.f 7) ≫
              ((TopCat.toSSet.obj
                (SSet.toTop.obj (Δ[7] : SSet.{0}))).chainComplex
                  (AddCommGrpCat.of ℤ)).d 7 6) ≫ Tstd.f 6 := by
          rw [← Category.assoc]
        _ = (standardSevenTopSimplexChain ≫ Cstd.f 7) ≫
              (((TopCat.toSSet.obj
                (SSet.toTop.obj (Δ[7] : SSet.{0}))).chainComplex
                  (AddCommGrpCat.of ℤ)).d 7 6 ≫ Tstd.f 6) :=
          Category.assoc _ _ _
        _ = (standardSevenTopSimplexChain ≫ Cstd.f 7) ≫
              (Tstd.f 7 ≫
                ((TopCat.toSSet.obj
                  (TopCat.of (stdSimplex ℝ (Fin 8)))).chainComplex
                    (AddCommGrpCat.of ℤ)).d 7 6) := by
          rw [Tstd.comm 7 6]
        _ = ((standardSevenTopSimplexChain ≫ Cstd.f 7) ≫ Tstd.f 7) ≫
              ((TopCat.toSSet.obj
                (TopCat.of (stdSimplex ℝ (Fin 8)))).chainComplex
                  (AddCommGrpCat.of ℤ)).d 7 6 :=
          (Category.assoc _ _ _).symm
    _ = (TopCat.toSSet.obj
          (TopCat.of (stdSimplex ℝ (Fin 8)))).ιChainComplex
            (standardTopologicalSimplexIdentitySimplex 7) ≫
          ((TopCat.toSSet.obj
            (TopCat.of (stdSimplex ℝ (Fin 8)))).chainComplex
              (AddCommGrpCat.of ℤ)).d 7 6 := by
      rw [standardSevenTopSimplexChain]
      rw [standardSimplexTopSimplexChain_comparison_realization]

/-- For the universal identity singular simplex, the alternating affine subdivisions of its
faces are the explicit alternating affine boundary chain. -/
public theorem standardTopologicalSimplexIdentity_affineSubdivisionAlternatingFaceChain
    (n : ℕ) :
    affineSubdivisionSingularSimplexAlternatingFaceChain
        (TopCat.of (stdSimplex ℝ (Fin (n + 2)))) n
        (standardTopologicalSimplexIdentitySimplex (n + 1)) =
      affineSubdividedSimplexAlternatingFaceChain n := by
  rw [affineSubdividedSimplexAlternatingFaceChain_eq_expected]
  rw [affineSubdivisionSingularSimplexAlternatingFaceChain,
    affineSubdividedSimplexExpectedBoundaryChain]
  apply Finset.sum_congr rfl
  intro p _
  apply congrArg (fun q ↦ ((-1 : ℤ) ^ p.val) • q)
  rw [affineSubdivisionSingularSimplexChain,
    singularSimplexTopCatMap_identity_delta]

/-- Affine singular subdivision sends the ordinary singular boundary of the universal
seven-simplex to the explicit alternating affine subdivided boundary. -/
public theorem standardSevenTopologicalBoundary_affineSubdivision :
    ((TopCat.toSSet.obj
          (TopCat.of (stdSimplex ℝ (Fin 8)))).ιChainComplex
        (standardTopologicalSimplexIdentitySimplex 7) ≫
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin 8)))).chainComplex
          (AddCommGrpCat.of ℤ)).d 7 6) ≫
      (affineSingularSubdivisionChainMap
        (TopCat.of (stdSimplex ℝ (Fin 8)))).f 6 =
    affineSubdividedSimplexAlternatingFaceChain 6 := by
  let S := affineSingularSubdivisionChainMap
    (TopCat.of (stdSimplex ℝ (Fin 8)))
  change (_ ≫ _) ≫ S.f 6 = _
  rw [Category.assoc, ← S.comm 7 6, ← Category.assoc]
  rw [affineSingularSubdivisionChainMap_f,
    iota_affineSingularSubdivisionComponent,
    affineSubdivisionSingularSimplexChain_boundary,
    standardTopologicalSimplexIdentity_affineSubdivisionAlternatingFaceChain]

/-- After one affine singular subdivision, the original boundary generator transported through
the canonical comparison is the explicit alternating affine subdivided boundary. -/
public theorem boundarySevenOriginalFundamentalChain_comparison_affineSubdivision :
    (((boundarySevenOriginalFundamentalChain ≫
          (simplicialToRealizationSingularChainMap
            (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ)).f 6) ≫
        (SSet.chainComplexMap
          (TopCat.toSSet.map boundarySevenRealizationToStdSimplexTopMap)
          (AddCommGrpCat.of ℤ)).f 6) ≫
      (affineSingularSubdivisionChainMap
        (TopCat.of (stdSimplex ℝ (Fin 8)))).f 6) =
    affineSubdividedSimplexAlternatingFaceChain 6 := by
  rw [boundarySevenOriginalFundamentalChain_comparison_realization_stdSimplex]
  exact standardSevenTopologicalBoundary_affineSubdivision

/-- Forget the proof that a point lies in the ordinary simplex boundary. -/
public noncomputable def standardSimplexBoundaryToStdSimplexTopMap :
    TopCat.of (StandardSimplexBoundary 7) ⟶
      TopCat.of (stdSimplex ℝ (Fin 8)) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Forgetting the boundary witness, the proper-face affine simplex is the ordinary affine flag
simplex associated to its image in the full nonempty-face nerve. -/
public theorem boundarySevenProperFaceAffineFlagMap_val_eq_affineFlagContinuousMap
    (k : ℕ) (F : ComposableArrows BoundarySevenProperFace k)
    (w : stdSimplex ℝ (Fin (k + 1))) :
    (boundarySevenProperFaceAffineFlagMap k F w : stdSimplex ℝ (Fin 8)) =
      affineFlagContinuousMap 7 k
        (boundarySevenProperFaceNerveInclusion.app
          (Opposite.op (SimplexCategory.mk k)) F) w := by
  rfl

/-- After forgetting the boundary witness, the proper-face singular simplex is literally the
ambient affine flag singular simplex. -/
public theorem boundarySevenProperFaceAffineSingularSimplex_map_val
    (k : ℕ) (F : ComposableArrows BoundarySevenProperFace k) :
    (TopCat.toSSet.map standardSimplexBoundaryToStdSimplexTopMap).app
        (Opposite.op (SimplexCategory.mk k))
        (boundarySevenProperFaceAffineSingularSimplex k F) =
      affineFlagSingularSimplex 7 k
        (boundarySevenProperFaceNerveInclusion.app
          (Opposite.op (SimplexCategory.mk k)) F) := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  apply ContinuousMap.ext
  intro w
  exact boundarySevenProperFaceAffineFlagMap_val_eq_affineFlagContinuousMap k F w

/-- The proper-face affine chain map, followed by the boundary inclusion, is the restriction of
the ambient affine flag chain map along the proper-face nerve inclusion. -/
public theorem boundarySevenProperFaceAffineChainMap_comp_val :
    SSet.chainComplexMap boundarySevenProperFaceAffineSingularMap
        (AddCommGrpCat.of ℤ) ≫
      SSet.chainComplexMap
          (TopCat.toSSet.map standardSimplexBoundaryToStdSimplexTopMap)
          (AddCommGrpCat.of ℤ) =
    SSet.chainComplexMap boundarySevenProperFaceNerveInclusion
        (AddCommGrpCat.of ℤ) ≫
      affineFlagChainMap 7 := by
  let A := SSet.chainComplexMap boundarySevenProperFaceAffineSingularMap
    (AddCommGrpCat.of ℤ)
  let V := SSet.chainComplexMap
    (TopCat.toSSet.map standardSimplexBoundaryToStdSimplexTopMap)
      (AddCommGrpCat.of ℤ)
  let I := SSet.chainComplexMap boundarySevenProperFaceNerveInclusion
    (AddCommGrpCat.of ℤ)
  let G := affineFlagChainMap 7
  apply HomologicalComplex.Hom.ext
  funext k
  apply BoundarySevenProperFaceNerve.chainComplex_hom_ext
  intro F
  change ((BoundarySevenProperFaceNerve.ιChainComplex F ≫ A.f k) ≫ V.f k) =
    ((BoundarySevenProperFaceNerve.ιChainComplex F ≫ I.f k) ≫ G.f k)
  rw [SSet.ι_chainComplexMap_f, SSet.ι_chainComplexMap_f,
    SSet.ι_chainComplexMap_f]
  dsimp only [G]
  rw [affineFlagChainMap_f]
  rw [iota_affineFlagChainComponent]
  exact congrArg
    (TopCat.toSSet.obj (TopCat.of (stdSimplex ℝ (Fin 8)))).ιChainComplex
      (boundarySevenProperFaceAffineSingularSimplex_map_val k F)

/-- The ambient affine realization of the explicit subdivided boundary is the alternating affine
boundary of the subdivided seven-simplex. -/
public theorem subdividedSevenBoundaryFundamentalChain_affineFlag :
    subdividedSevenBoundaryFundamentalChain ≫
        (affineFlagChainMap 7).f 6 =
      affineSubdividedSimplexAlternatingFaceChain 6 := by
  let G := affineFlagChainMap 7
  change (subdividedSimplexFundamentalChain 7 ≫ _) ≫ G.f 6 = _
  rw [Category.assoc, ← G.comm 7 6, ← Category.assoc]
  exact affineSubdividedSimplexFundamentalChain_boundary 6

/-- Under the canonical proper-face comparison and affine homeomorphism, the intrinsic
proper-face generator is exactly the alternating affine boundary chain, after forgetting the
boundary witness. -/
public theorem boundarySevenProperFaceFundamentalChain_affine_realization_val :
    (boundarySevenProperFaceFundamentalChain ≫
        (SSet.chainComplexMap boundarySevenProperFaceAffineSingularMap
          (AddCommGrpCat.of ℤ)).f 6) ≫
      (SSet.chainComplexMap
        (TopCat.toSSet.map standardSimplexBoundaryToStdSimplexTopMap)
        (AddCommGrpCat.of ℤ)).f 6 =
    affineSubdividedSimplexAlternatingFaceChain 6 := by
  let A := SSet.chainComplexMap boundarySevenProperFaceAffineSingularMap
    (AddCommGrpCat.of ℤ)
  let V := SSet.chainComplexMap
    (TopCat.toSSet.map standardSimplexBoundaryToStdSimplexTopMap)
      (AddCommGrpCat.of ℤ)
  let I := SSet.chainComplexMap boundarySevenProperFaceNerveInclusion
    (AddCommGrpCat.of ℤ)
  let G := affineFlagChainMap 7
  have hmap := congrArg (fun K ↦ K.f 6)
    boundarySevenProperFaceAffineChainMap_comp_val
  change A.f 6 ≫ V.f 6 = I.f 6 ≫ G.f 6 at hmap
  calc
    (boundarySevenProperFaceFundamentalChain ≫ A.f 6) ≫ V.f 6 =
        boundarySevenProperFaceFundamentalChain ≫ (A.f 6 ≫ V.f 6) :=
      Category.assoc _ _ _
    _ = boundarySevenProperFaceFundamentalChain ≫ (I.f 6 ≫ G.f 6) := by
      rw [hmap]
    _ = (boundarySevenProperFaceFundamentalChain ≫ I.f 6) ≫ G.f 6 :=
      (Category.assoc _ _ _).symm
    _ = subdividedSevenBoundaryFundamentalChain ≫ G.f 6 := by
      rw [boundarySevenProperFaceFundamentalChain_comp_inclusion]
    _ = affineSubdividedSimplexAlternatingFaceChain 6 :=
      subdividedSevenBoundaryFundamentalChain_affineFlag

/-- The proper-face affine generator and the original boundary generator agree exactly after
transporting both to ambient singular chains and applying one affine subdivision to the latter. -/
public theorem boundarySevenProperFaceGenerator_eq_original_after_affineSubdivision :
    (boundarySevenProperFaceFundamentalChain ≫
        (SSet.chainComplexMap boundarySevenProperFaceAffineSingularMap
          (AddCommGrpCat.of ℤ)).f 6) ≫
      (SSet.chainComplexMap
        (TopCat.toSSet.map standardSimplexBoundaryToStdSimplexTopMap)
        (AddCommGrpCat.of ℤ)).f 6 =
    ((boundarySevenOriginalFundamentalChain ≫
          (simplicialToRealizationSingularChainMap
            (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ)).f 6) ≫
        (SSet.chainComplexMap
          (TopCat.toSSet.map boundarySevenRealizationToStdSimplexTopMap)
          (AddCommGrpCat.of ℤ)).f 6) ≫
      (affineSingularSubdivisionChainMap
        (TopCat.of (stdSimplex ℝ (Fin 8)))).f 6 := by
  rw [boundarySevenProperFaceFundamentalChain_affine_realization_val,
    boundarySevenOriginalFundamentalChain_comparison_affineSubdivision]

end SphereSixComplex
