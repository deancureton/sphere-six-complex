module

public import SphereSixComplex.Topology.BinaryOpenCoverAssembly
public import SphereSixComplex.Topology.FirstHurewiczProof
public import SphereSixComplex.Topology.MappingTorusBaseCircleWangBoundaryNaturality
public import Mathlib.Algebra.Homology.ConcreteCategory

/-!
# The positive degree-zero boundary of the identity mapping torus of a point

The standard vertex--edge cover cuts the positive cylinder loop into an edge segment and two
vertex segments. Their chain boundaries are respectively `high - low` and `low - high`, so the
connecting morphism returns the low overlap point with coefficient `+1`.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Set Topology TopologicalSpace
open scoped ContinuousMap

namespace SphereSixComplex.Topology.IdentityUnitMappingTorusPositiveBoundary

open SphereSixComplex.BinaryOpenCover
open CanonicalProductWangBoundaryNaturality
open FirstHurewiczProof
open SphereSixComplex.StandardCircleHomologyLiftDegree

public abbrev PointFiber := Unit

public abbrev PointMappingTorus := CircleMappingTorus (Homeomorph.refl PointFiber)

public abbrev pointVertexOpen : Opens (TopCat.of PointMappingTorus) :=
  mappingTorusVertexOpen (Homeomorph.refl PointFiber)

public abbrev pointEdgeOpen : Opens (TopCat.of PointMappingTorus) :=
  mappingTorusEdgeOpen (Homeomorph.refl PointFiber)

/-- The positively oriented cylinder coordinate in the identity mapping torus of a point. -/
public def pointCylinder : C(unitInterval, PointMappingTorus) where
  toFun t := circleMappingTorusCylinderProjection (Homeomorph.refl PointFiber) (t, ())
  continuous_toFun := by fun_prop

public theorem pointCylinder_zero_eq_one : pointCylinder 0 = pointCylinder 1 := by
  symm
  apply Quotient.sound
  apply Relation.EqvGen.rel
  exact Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)

/-- The full positive cylinder loop, based at the glued endpoint. -/
public def positiveCylinderLoop : Path (pointCylinder 0) (pointCylinder 0) where
  toFun := pointCylinder
  continuous_toFun := pointCylinder.continuous
  source' := rfl
  target' := pointCylinder_zero_eq_one.symm

/-- The first-homology class of the positive cylinder loop. -/
public def positiveCylinderClass : IntegralSingularHomology 1 PointMappingTorus :=
  loopHomologyClass positiveCylinderLoop

private theorem positiveCylinderLoop_baseCircle :
    ((positiveCylinderLoop.map
      (circleMappingTorusBaseCircleProjection
        (Homeomorph.refl PointFiber)).continuous).cast (by simp [pointCylinder])
      (by simp [pointCylinder])) = unitCircleIntegerLoop 1 := by
  apply Path.ext
  funext t
  change (circleMappingTorusBaseCircleProjection (Homeomorph.refl PointFiber))
      (positiveCylinderLoop t) = (unitCircleIntegerLoop 1) t
  change (circleMappingTorusBaseCircleProjection (Homeomorph.refl PointFiber))
      (pointCylinder t) = _
  rw [show pointCylinder t = circleMappingTorusCylinderProjection
    (Homeomorph.refl PointFiber) (t, ()) by rfl]
  simp [unitCircleIntegerLoop]

/-- The positive cylinder class has base-circle winding `+1`. -/
public theorem positiveCylinderClass_baseCircle_winding :
    unitCircleHomologyWinding
        (integralSingularHomologyMap 1
          (circleMappingTorusBaseCircleProjection (Homeomorph.refl PointFiber))
          positiveCylinderClass) = 1 := by
  rw [positiveCylinderClass, integralSingularHomologyMap_loopHomologyClass]
  have h0 : (0 : UnitAddCircle) =
      circleMappingTorusBaseCircleProjection (Homeomorph.refl PointFiber)
        (pointCylinder 0) := by simp [pointCylinder]
  rw [← loopHomologyClass_cast _ h0]
  rw [positiveCylinderLoop_baseCircle, unitCircleHomologyWinding_integerLoop]

private theorem pointCylinder_mem_vertex (t : unitInterval) (ht : t ∈ vertexBand) :
    pointCylinder t ∈ pointVertexOpen := by
  change bouquetMk (fun _ : Unit ↦ Homeomorph.refl PointFiber) ((), t, ()) ∈
    vertexPiece (fun _ : Unit ↦ Homeomorph.refl PointFiber)
  rw [vertexPiece, mem_bouquetPiece_mk_iff _ vertexBand_ends]
  exact ht

private theorem pointCylinder_mem_edge (t : unitInterval) (ht : t ∈ edgeBand) :
    pointCylinder t ∈ pointEdgeOpen := by
  change bouquetMk (fun _ : Unit ↦ Homeomorph.refl PointFiber) ((), t, ()) ∈
    edgePiece (fun _ : Unit ↦ Homeomorph.refl PointFiber)
  rw [edgePiece, mem_bouquetPiece_mk_iff _ edgeBand_ends]
  exact ht

private theorem convexComb_zero_quarter_mem_vertex (s : unitInterval) :
    Icc.convexComb 0 uQuarter s ∈ vertexBand := by
  left
  change (1 - (s : ℝ)) * 0 + (s : ℝ) * (1 / 4) < 1 / 3
  linarith [unitInterval.nonneg s, unitInterval.le_one s]

private theorem convexComb_quarter_threeQuarters_mem_edge (s : unitInterval) :
    Icc.convexComb uQuarter uThreeQuarters s ∈ edgeBand := by
  constructor
  · change 1 / 6 < (1 - (s : ℝ)) * (1 / 4) + (s : ℝ) * (3 / 4)
    linarith [unitInterval.nonneg s, unitInterval.le_one s]
  · change (1 - (s : ℝ)) * (1 / 4) + (s : ℝ) * (3 / 4) < 5 / 6
    linarith [unitInterval.nonneg s, unitInterval.le_one s]

private theorem convexComb_threeQuarters_one_mem_vertex (s : unitInterval) :
    Icc.convexComb uThreeQuarters 1 s ∈ vertexBand := by
  right
  change 2 / 3 < (1 - (s : ℝ)) * (3 / 4) + (s : ℝ) * 1
  linarith [unitInterval.nonneg s, unitInterval.le_one s]

private def lowVertexPath :
    Path
      (⟨pointCylinder 0, pointCylinder_mem_vertex 0 (Or.inl (by norm_num))⟩ :
        (Opens.toTopCat (TopCat.of PointMappingTorus)).obj pointVertexOpen)
      ⟨pointCylinder uQuarter,
        pointCylinder_mem_vertex uQuarter uQuarter_mem_overlapBand.1⟩ where
  toFun s := ⟨pointCylinder (Icc.convexComb 0 uQuarter s),
    pointCylinder_mem_vertex _ (convexComb_zero_quarter_mem_vertex s)⟩
  continuous_toFun := Continuous.subtype_mk
    (pointCylinder.continuous.comp (Icc.continuous_convexComb 0 uQuarter)) _
  source' := by ext; simp
  target' := by ext; simp

private def edgePath :
    Path
      (⟨pointCylinder uQuarter, pointCylinder_mem_edge uQuarter uQuarter_mem_edgeBand⟩ :
        (Opens.toTopCat (TopCat.of PointMappingTorus)).obj pointEdgeOpen)
      ⟨pointCylinder uThreeQuarters,
        pointCylinder_mem_edge uThreeQuarters uThreeQuarters_mem_edgeBand⟩ where
  toFun s := ⟨pointCylinder (Icc.convexComb uQuarter uThreeQuarters s),
    pointCylinder_mem_edge _ (convexComb_quarter_threeQuarters_mem_edge s)⟩
  continuous_toFun := Continuous.subtype_mk
    (pointCylinder.continuous.comp
      (Icc.continuous_convexComb uQuarter uThreeQuarters)) _
  source' := by ext; simp
  target' := by ext; simp

private def highVertexPath :
    Path
      (⟨pointCylinder uThreeQuarters,
        pointCylinder_mem_vertex uThreeQuarters uThreeQuarters_mem_overlapBand.1⟩ :
        (Opens.toTopCat (TopCat.of PointMappingTorus)).obj pointVertexOpen)
      ⟨pointCylinder 1, pointCylinder_mem_vertex 1 (Or.inr (by norm_num))⟩ where
  toFun s := ⟨pointCylinder (Icc.convexComb uThreeQuarters 1 s),
    pointCylinder_mem_vertex _ (convexComb_threeQuarters_one_mem_vertex s)⟩
  continuous_toFun := Continuous.subtype_mk
    (pointCylinder.continuous.comp (Icc.continuous_convexComb uThreeQuarters 1)) _
  source' := by ext; simp
  target' := by ext; simp

private theorem vertexOne_eq_zero :
    (⟨pointCylinder 1, pointCylinder_mem_vertex 1 (Or.inr (by norm_num))⟩ :
        (Opens.toTopCat (TopCat.of PointMappingTorus)).obj pointVertexOpen) =
      ⟨pointCylinder 0, pointCylinder_mem_vertex 0 (Or.inl (by norm_num))⟩ := by
  apply Subtype.ext
  exact pointCylinder_zero_eq_one.symm

private def vertexPath :
    Path
      (⟨pointCylinder uThreeQuarters,
        pointCylinder_mem_vertex uThreeQuarters uThreeQuarters_mem_overlapBand.1⟩ :
        (Opens.toTopCat (TopCat.of PointMappingTorus)).obj pointVertexOpen)
      ⟨pointCylinder uQuarter,
        pointCylinder_mem_vertex uQuarter uQuarter_mem_overlapBand.1⟩ :=
  highVertexPath.trans (lowVertexPath.cast vertexOne_eq_zero rfl)

private def lowOverlapPoint :
    (Opens.toTopCat (TopCat.of PointMappingTorus)).obj
      (pointVertexOpen ⊓ pointEdgeOpen) :=
  ⟨pointCylinder uQuarter,
    pointCylinder_mem_vertex uQuarter uQuarter_mem_overlapBand.1,
    pointCylinder_mem_edge uQuarter uQuarter_mem_edgeBand⟩

private def highOverlapPoint :
    (Opens.toTopCat (TopCat.of PointMappingTorus)).obj
      (pointVertexOpen ⊓ pointEdgeOpen) :=
  ⟨pointCylinder uThreeQuarters,
    pointCylinder_mem_vertex uThreeQuarters uThreeQuarters_mem_overlapBand.1,
    pointCylinder_mem_edge uThreeQuarters uThreeQuarters_mem_edgeBand⟩

private def vertexChain : (openSingularChains pointVertexOpen).X 1 :=
  pathChain vertexPath

private def edgeChain : (openSingularChains pointEdgeOpen).X 1 :=
  pathChain edgePath

private def overlapChain : (openSingularChains (pointVertexOpen ⊓ pointEdgeOpen)).X 0 :=
  pointChain lowOverlapPoint - pointChain highOverlapPoint

private noncomputable def piecesEquiv (n : ℕ) :
    (openSingularChains pointVertexOpen ⊞ openSingularChains pointEdgeOpen).X n ≃+
      (openSingularChains pointVertexOpen).X n × (openSingularChains pointEdgeOpen).X n :=
  ((HomologicalComplex.biprodXIso
    (openSingularChains pointVertexOpen) (openSingularChains pointEdgeOpen) n).trans
      (AddCommGrpCat.biprodIsoProd _ _)).addCommGroupIsoToAddEquiv

private lemma biprodIsoProd_hom_comp_fst_local (G H : AddCommGrpCat) :
    (AddCommGrpCat.biprodIsoProd G H).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.fst G H) =
      (biprod.fst : G ⊞ H ⟶ G) := by
  rw [← cancel_epi (AddCommGrpCat.biprodIsoProd G H).inv]
  simp

private lemma biprodIsoProd_hom_comp_snd_local (G H : AddCommGrpCat) :
    (AddCommGrpCat.biprodIsoProd G H).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.snd G H) =
      (biprod.snd : G ⊞ H ⟶ H) := by
  rw [← cancel_epi (AddCommGrpCat.biprodIsoProd G H).inv]
  simp

private theorem piecesEquiv_apply (n : ℕ)
    (z : (openSingularChains pointVertexOpen ⊞ openSingularChains pointEdgeOpen).X n) :
    piecesEquiv n z =
      (((biprod.fst : openSingularChains pointVertexOpen ⊞
          openSingularChains pointEdgeOpen ⟶ openSingularChains pointVertexOpen).f n) z,
       ((biprod.snd : openSingularChains pointVertexOpen ⊞
          openSingularChains pointEdgeOpen ⟶ openSingularChains pointEdgeOpen).f n) z) := by
  apply Prod.ext
  · change (ConcreteCategory.hom
        (((HomologicalComplex.biprodXIso (openSingularChains pointVertexOpen)
          (openSingularChains pointEdgeOpen) n).hom ≫
        (AddCommGrpCat.biprodIsoProd _ _).hom) ≫
          AddCommGrpCat.ofHom (AddMonoidHom.fst _ _))) z = _
    rw [Category.assoc,
      biprodIsoProd_hom_comp_fst_local, HomologicalComplex.biprodXIso_hom_fst]
  · change (ConcreteCategory.hom
        (((HomologicalComplex.biprodXIso (openSingularChains pointVertexOpen)
          (openSingularChains pointEdgeOpen) n).hom ≫
        (AddCommGrpCat.biprodIsoProd _ _).hom) ≫
          AddCommGrpCat.ofHom (AddMonoidHom.snd _ _))) z = _
    rw [Category.assoc,
      biprodIsoProd_hom_comp_snd_local, HomologicalComplex.biprodXIso_hom_snd]

private def pieceChain :
    (openSingularChains pointVertexOpen ⊞ openSingularChains pointEdgeOpen).X 1 :=
  (piecesEquiv 1).symm (vertexChain, edgeChain)

private theorem piecesEquiv_boundary (z :
    (openSingularChains pointVertexOpen ⊞ openSingularChains pointEdgeOpen).X 1) :
    piecesEquiv 0
        ((openSingularChains pointVertexOpen ⊞ openSingularChains pointEdgeOpen).d 1 0 z) =
      ((openSingularChains pointVertexOpen).d 1 0 (piecesEquiv 1 z).1,
       (openSingularChains pointEdgeOpen).d 1 0 (piecesEquiv 1 z).2) := by
  rw [piecesEquiv_apply]
  apply Prod.ext
  · rw [piecesEquiv_apply]
    change (ConcreteCategory.hom
      ((openSingularChains pointVertexOpen ⊞ openSingularChains pointEdgeOpen).d 1 0 ≫
        (biprod.fst : openSingularChains pointVertexOpen ⊞
          openSingularChains pointEdgeOpen ⟶ openSingularChains pointVertexOpen).f 0)) z =
      (ConcreteCategory.hom
        ((biprod.fst : openSingularChains pointVertexOpen ⊞
          openSingularChains pointEdgeOpen ⟶ openSingularChains pointVertexOpen).f 1 ≫
            (openSingularChains pointVertexOpen).d 1 0)) z
    rw [HomologicalComplex.Hom.comm]
  · rw [piecesEquiv_apply]
    change (ConcreteCategory.hom
      ((openSingularChains pointVertexOpen ⊞ openSingularChains pointEdgeOpen).d 1 0 ≫
        (biprod.snd : openSingularChains pointVertexOpen ⊞
          openSingularChains pointEdgeOpen ⟶ openSingularChains pointEdgeOpen).f 0)) z =
      (ConcreteCategory.hom
        ((biprod.snd : openSingularChains pointVertexOpen ⊞
          openSingularChains pointEdgeOpen ⟶ openSingularChains pointEdgeOpen).f 1 ≫
            (openSingularChains pointEdgeOpen).d 1 0)) z
    rw [HomologicalComplex.Hom.comm]

private theorem boundary_vertexChain :
    (openSingularChains pointVertexOpen).d 1 0 vertexChain =
      pointChain
          (⟨pointCylinder uQuarter,
            pointCylinder_mem_vertex uQuarter uQuarter_mem_overlapBand.1⟩ :
            (Opens.toTopCat (TopCat.of PointMappingTorus)).obj pointVertexOpen) -
        pointChain
          (⟨pointCylinder uThreeQuarters,
            pointCylinder_mem_vertex uThreeQuarters uThreeQuarters_mem_overlapBand.1⟩ :
            (Opens.toTopCat (TopCat.of PointMappingTorus)).obj pointVertexOpen) := by
  exact boundaryOne_pathChain vertexPath

private theorem boundary_edgeChain :
    (openSingularChains pointEdgeOpen).d 1 0 edgeChain =
      pointChain
          (⟨pointCylinder uThreeQuarters,
            pointCylinder_mem_edge uThreeQuarters uThreeQuarters_mem_edgeBand⟩ :
            (Opens.toTopCat (TopCat.of PointMappingTorus)).obj pointEdgeOpen) -
        pointChain
          (⟨pointCylinder uQuarter,
            pointCylinder_mem_edge uQuarter uQuarter_mem_edgeBand⟩ :
            (Opens.toTopCat (TopCat.of PointMappingTorus)).obj pointEdgeOpen) := by
  exact boundaryOne_pathChain edgePath

private theorem openMVToBiprodChain_fst :
    openMVToBiprodChain pointVertexOpen pointEdgeOpen ≫
        (biprod.fst : openSingularChains pointVertexOpen ⊞
          openSingularChains pointEdgeOpen ⟶ openSingularChains pointVertexOpen) =
      integralSimplicialChains.map
        (TopCat.toSSet.map ((Opens.toTopCat (TopCat.of PointMappingTorus)).map
          (Opens.infLELeft pointVertexOpen pointEdgeOpen))) := by
  simp [openMVToBiprodChain]

private theorem openMVToBiprodChain_snd :
    openMVToBiprodChain pointVertexOpen pointEdgeOpen ≫
        (biprod.snd : openSingularChains pointVertexOpen ⊞
          openSingularChains pointEdgeOpen ⟶ openSingularChains pointEdgeOpen) =
      -integralSimplicialChains.map
        (TopCat.toSSet.map ((Opens.toTopCat (TopCat.of PointMappingTorus)).map
          (Opens.infLERight pointVertexOpen pointEdgeOpen))) := by
  simp [openMVToBiprodChain]

private theorem boundary_pieceChain :
    (openSingularChains pointVertexOpen ⊞ openSingularChains pointEdgeOpen).d 1 0
        pieceChain =
      (openMVToBiprodChain pointVertexOpen pointEdgeOpen).f 0 overlapChain := by
  apply (piecesEquiv 0).injective
  rw [piecesEquiv_boundary]
  rw [show piecesEquiv 1 pieceChain = (vertexChain, edgeChain) by simp [pieceChain]]
  change ((openSingularChains pointVertexOpen).d 1 0 vertexChain,
      (openSingularChains pointEdgeOpen).d 1 0 edgeChain) = _
  rw [boundary_vertexChain, boundary_edgeChain]
  rw [piecesEquiv_apply]
  apply Prod.ext
  · change _ = ((biprod.fst : openSingularChains pointVertexOpen ⊞
        openSingularChains pointEdgeOpen ⟶ openSingularChains pointVertexOpen).f 0)
          ((openMVToBiprodChain pointVertexOpen pointEdgeOpen).f 0 overlapChain)
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f,
      openMVToBiprodChain_fst]
    change _ = (singularChainMap
      (((Opens.toTopCat (TopCat.of PointMappingTorus)).map
        (Opens.infLELeft pointVertexOpen pointEdgeOpen)).hom)).f 0 overlapChain
    rw [overlapChain, map_sub]
    simp only [pointChain, singularChainMap_simplex]
    rfl
  · change _ = ((biprod.snd : openSingularChains pointVertexOpen ⊞
        openSingularChains pointEdgeOpen ⟶ openSingularChains pointEdgeOpen).f 0)
          ((openMVToBiprodChain pointVertexOpen pointEdgeOpen).f 0 overlapChain)
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f,
      openMVToBiprodChain_snd]
    change _ = -((singularChainMap
      (((Opens.toTopCat (TopCat.of PointMappingTorus)).map
        (Opens.infLERight pointVertexOpen pointEdgeOpen)).hom)).f 0 overlapChain)
    rw [overlapChain, map_sub]
    simp only [pointChain, singularChainMap_simplex]
    change _ = -(pointChain
        (⟨pointCylinder uQuarter,
          pointCylinder_mem_edge uQuarter uQuarter_mem_edgeBand⟩ :
          (Opens.toTopCat (TopCat.of PointMappingTorus)).obj pointEdgeOpen) -
      pointChain
        (⟨pointCylinder uThreeQuarters,
          pointCylinder_mem_edge uThreeQuarters uThreeQuarters_mem_edgeBand⟩ :
          (Opens.toTopCat (TopCat.of PointMappingTorus)).obj pointEdgeOpen))
    simp only [pointChain]
    abel

private abbrev coverShort := coverChainShortComplex pointVertexOpen pointEdgeOpen

private def generatedOverlapChain : coverShort.X₁.X 0 :=
  (intersectionForwardChain pointVertexOpen pointEdgeOpen).f 0 overlapChain

private def generatedPieceChain : coverShort.X₂.X 1 :=
  (biprodForwardChain pointVertexOpen pointEdgeOpen).f 1 pieceChain

private def generatedUnionChain : coverShort.X₃.X 1 :=
  coverShort.g.f 1 generatedPieceChain

private theorem boundary_generatedPieceChain :
    coverShort.X₂.d 1 0 generatedPieceChain =
      coverShort.f.f 0 generatedOverlapChain := by
  change coverShort.X₂.d 1 0
      ((biprodForwardChain pointVertexOpen pointEdgeOpen).f 1 pieceChain) =
    coverShort.f.f 0
      ((intersectionForwardChain pointVertexOpen pointEdgeOpen).f 0 overlapChain)
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.Hom.comm,
    ConcreteCategory.comp_apply, boundary_pieceChain]
  have h := HomologicalComplex.congr_hom
    (openMVToBiprodChain_naturality pointVertexOpen pointEdgeOpen) 0
  simp only [HomologicalComplex.comp_f] at h
  exact ConcreteCategory.congr_hom h overlapChain

private theorem generatedUnionChain_isCycle :
    coverShort.X₃.d 1 0 generatedUnionChain = 0 := by
  change coverShort.X₃.d 1 0 (coverShort.g.f 1 generatedPieceChain) = 0
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.Hom.comm,
    ConcreteCategory.comp_apply, boundary_generatedPieceChain]
  rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, coverShort.zero]
  simp

private theorem generatedUnionCycle_morphism :
    AddCommGrpCat.asHom generatedUnionChain ≫ coverShort.X₃.d 1 0 = 0 := by
  apply AddCommGrpCat.int_hom_ext
  simpa using generatedUnionChain_isCycle

private def generatedPositiveClass : coverShort.X₃.homology 1 :=
  ((coverShort.X₃.liftCycles (AddCommGrpCat.asHom generatedUnionChain) 0 (by simp)
      generatedUnionCycle_morphism) ≫ coverShort.X₃.homologyπ 1) 1

private def generatedOverlapClass : coverShort.X₁.homology 0 :=
  ((coverShort.X₁.liftCycles (AddCommGrpCat.asHom generatedOverlapChain) 0 (by simp)
      (by simp)) ≫ coverShort.X₁.homologyπ 0) 1

private theorem generatedBoundary_positive :
    ConcreteCategory.hom (generatedBoundary pointVertexOpen pointEdgeOpen 0)
        generatedPositiveClass = generatedOverlapClass := by
  let hS := coverChainShortComplex_shortExact pointVertexOpen pointEdgeOpen
  have hx₂ : AddCommGrpCat.asHom generatedPieceChain ≫ coverShort.g.f 1 =
      AddCommGrpCat.asHom generatedUnionChain := by
    apply AddCommGrpCat.int_hom_ext
    simp [generatedUnionChain]
  have hx₁ : AddCommGrpCat.asHom generatedOverlapChain ≫ coverShort.f.f 0 =
      AddCommGrpCat.asHom generatedPieceChain ≫ coverShort.X₂.d 1 0 := by
    apply AddCommGrpCat.int_hom_ext
    simpa using boundary_generatedPieceChain.symm
  have hδ := hS.δ_eq 1 0 rfl
    (AddCommGrpCat.asHom generatedUnionChain) generatedUnionCycle_morphism
    (AddCommGrpCat.asHom generatedPieceChain) hx₂
    (AddCommGrpCat.asHom generatedOverlapChain) hx₁ 0 (by simp)
  have hδ1 := ConcreteCategory.congr_hom hδ (1 : ℤ)
  simpa only [generatedPositiveClass, generatedOverlapClass, generatedBoundary,
    Category.assoc, ConcreteCategory.comp_apply] using hδ1

private def ordinaryOverlapClass :
    IntegralSingularHomology 0
      ((Opens.toTopCat (TopCat.of PointMappingTorus)).obj
        (pointVertexOpen ⊓ pointEdgeOpen)) :=
  (((openSingularChains (pointVertexOpen ⊓ pointEdgeOpen)).liftCycles
      (AddCommGrpCat.asHom overlapChain) 0 (by simp) (by simp)) ≫
    (openSingularChains (pointVertexOpen ⊓ pointEdgeOpen)).homologyπ 0) 1

private theorem ordinaryOverlapClass_forward :
    ConcreteCategory.hom
        (HomologicalComplex.homologyMap
          (intersectionForwardChain pointVertexOpen pointEdgeOpen) 0)
        ordinaryOverlapClass = generatedOverlapClass := by
  rw [ordinaryOverlapClass, generatedOverlapClass]
  rw [← ConcreteCategory.comp_apply, Category.assoc,
    HomologicalComplex.homologyπ_naturality]
  rw [← Category.assoc, HomologicalComplex.liftCycles_comp_cyclesMap]
  have hchain : AddCommGrpCat.asHom overlapChain ≫
      (intersectionForwardChain pointVertexOpen pointEdgeOpen).f 0 =
        AddCommGrpCat.asHom generatedOverlapChain := by
    apply AddCommGrpCat.int_hom_ext
    simp [generatedOverlapChain]
  rw [hchain]

private theorem generatedOverlapClass_intersectionIso :
    ConcreteCategory.hom
        ((mappingTorusOpenCoverHomologyComparison
          (Homeomorph.refl PointFiber)).intersectionIso 0).hom
        generatedOverlapClass = ordinaryOverlapClass := by
  change ConcreteCategory.hom
      (intersectionHomologyIso pointVertexOpen pointEdgeOpen 0).hom
        generatedOverlapClass = ordinaryOverlapClass
  let I := intersectionHomologyIso pointVertexOpen pointEdgeOpen 0
  have hfwd : ConcreteCategory.hom I.inv ordinaryOverlapClass =
      generatedOverlapClass := by
    change ConcreteCategory.hom
        (HomologicalComplex.homologyMap
          (intersectionForwardChain pointVertexOpen pointEdgeOpen) 0)
        ordinaryOverlapClass = generatedOverlapClass
    exact ordinaryOverlapClass_forward
  rw [← hfwd]
  change ConcreteCategory.hom I.hom
      (ConcreteCategory.hom I.inv ordinaryOverlapClass) = ordinaryOverlapClass
  rw [← ConcreteCategory.comp_apply, I.inv_hom_id]
  rfl

/-- The homology class represented by a degree-zero chain. -/
public noncomputable def zeroChainHomologyClass
    (K : ChainComplex AddCommGrpCat ℕ) (c : K.X 0) : K.homology 0 :=
  ((K.liftCycles (AddCommGrpCat.asHom c) 0 (by simp) (by simp)) ≫ K.homologyπ 0) 1

/-- Auditable chain-level data fixing the positive sign of the identity-point mapping-torus
Mayer--Vietoris boundary. -/
public structure PositiveBoundaryCalibration where
  low :
    (Opens.toTopCat (TopCat.of PointMappingTorus)).obj
      (pointVertexOpen ⊓ pointEdgeOpen)
  high :
    (Opens.toTopCat (TopCat.of PointMappingTorus)).obj
      (pointVertexOpen ⊓ pointEdgeOpen)
  source : (coverChainShortComplex pointVertexOpen pointEdgeOpen).X₃.homology 1
  low_coe : low.1 = pointCylinder uQuarter
  high_coe : high.1 = pointCylinder uThreeQuarters
  generated_boundary :
    ConcreteCategory.hom (generatedBoundary pointVertexOpen pointEdgeOpen 0) source =
      zeroChainHomologyClass
        (coverChainShortComplex pointVertexOpen pointEdgeOpen).X₁
        ((intersectionForwardChain pointVertexOpen pointEdgeOpen).f 0
          (pointChain low - pointChain high))
  ordinary_boundary :
    ConcreteCategory.hom
        ((mappingTorusOpenCoverHomologyComparison
          (Homeomorph.refl PointFiber)).intersectionIso 0).hom
        (ConcreteCategory.hom
          (generatedBoundary pointVertexOpen pointEdgeOpen 0) source) =
      zeroChainHomologyClass
        (openSingularChains (pointVertexOpen ⊓ pointEdgeOpen))
        (pointChain low - pointChain high)

/-- The canonical positive-boundary calibration for the cylinder loop cut at the two overlap
points. -/
public opaque positiveBoundaryCalibration : PositiveBoundaryCalibration := by
  refine
    { low := lowOverlapPoint
      high := highOverlapPoint
      source := generatedPositiveClass
      low_coe := rfl
      high_coe := rfl
      generated_boundary := ?_
      ordinary_boundary := ?_ }
  · simpa only [zeroChainHomologyClass, generatedOverlapClass,
      generatedOverlapChain, overlapChain] using generatedBoundary_positive
  · rw [generatedBoundary_positive, generatedOverlapClass_intersectionIso]
    rfl

/-- The generated connecting morphism sends the calibrated positive class to `low - high`. -/
public theorem positiveBoundaryCalibration_generated :
    ConcreteCategory.hom (generatedBoundary pointVertexOpen pointEdgeOpen 0)
        positiveBoundaryCalibration.source =
      zeroChainHomologyClass
        (coverChainShortComplex pointVertexOpen pointEdgeOpen).X₁
        ((intersectionForwardChain pointVertexOpen pointEdgeOpen).f 0
          (pointChain positiveBoundaryCalibration.low -
            pointChain positiveBoundaryCalibration.high)) :=
  positiveBoundaryCalibration.generated_boundary

/-- After the canonical comparison, the calibrated boundary is literally the ordinary
degree-zero chain class `low - high`. -/
public theorem positiveBoundaryCalibration_ordinary :
    ConcreteCategory.hom
        ((mappingTorusOpenCoverHomologyComparison
          (Homeomorph.refl PointFiber)).intersectionIso 0).hom
        (ConcreteCategory.hom
          (generatedBoundary pointVertexOpen pointEdgeOpen 0)
          positiveBoundaryCalibration.source) =
      zeroChainHomologyClass
        (openSingularChains (pointVertexOpen ⊓ pointEdgeOpen))
        (pointChain positiveBoundaryCalibration.low -
          pointChain positiveBoundaryCalibration.high) :=
  positiveBoundaryCalibration.ordinary_boundary

end SphereSixComplex.Topology.IdentityUnitMappingTorusPositiveBoundary

end

end
