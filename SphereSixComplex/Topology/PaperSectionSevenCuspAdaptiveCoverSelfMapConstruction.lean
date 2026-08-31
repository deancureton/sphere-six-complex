module

public import SphereSixComplex.Topology.PaperSectionSevenCuspAdaptiveCoverDegreeOneSelfMap

/-!
# Endpoint-fixed reparameterizations of a circle mapping torus

An endpoint-fixed continuous scalar phase on the mapping-torus cylinder descends to a self-map
of the quotient.  Straight-line interpolation with the original cylinder coordinate supplies a
homotopy to the identity, and pullbacks of the standard cover can be checked on representatives.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace
open scoped ContinuousMap

namespace SphereSixComplex

variable {F : Type} [TopologicalSpace F]

/-- Straight-line interpolation from a reparameterized cylinder coordinate to the original
coordinate. -/
public def circleMappingTorusPhaseInterpolation (r : C(unitInterval × F, unitInterval))
    (p : unitInterval × F) (s : unitInterval) : unitInterval :=
  ⟨(1 - (s : ℝ)) * (r p : ℝ) + (s : ℝ) * (p.1 : ℝ), by
    have hs0 := s.2.1
    have hs1 := s.2.2
    have hr0 := (r p).2.1
    have hr1 := (r p).2.2
    have hp0 := p.1.2.1
    have hp1 := p.1.2.2
    constructor <;> nlinarith⟩

@[simp]
public theorem circleMappingTorusPhaseInterpolation_zero
    (r : C(unitInterval × F, unitInterval)) (p : unitInterval × F) :
    circleMappingTorusPhaseInterpolation r p 0 = r p := by
  apply Subtype.ext
  norm_num [circleMappingTorusPhaseInterpolation]

@[simp]
public theorem circleMappingTorusPhaseInterpolation_one
    (r : C(unitInterval × F, unitInterval)) (p : unitInterval × F) :
    circleMappingTorusPhaseInterpolation r p 1 = p.1 := by
  apply Subtype.ext
  norm_num [circleMappingTorusPhaseInterpolation]

private theorem circleMappingTorusPhaseInterpolation_eq_zero
    (r : C(unitInterval × F, unitInterval)) (hzero : ∀ y, r (0, y) = 0)
    (y : F) (s : unitInterval) : circleMappingTorusPhaseInterpolation r (0, y) s = 0 := by
  apply Subtype.ext
  simp [circleMappingTorusPhaseInterpolation, hzero]

private theorem circleMappingTorusPhaseInterpolation_eq_one
    (r : C(unitInterval × F, unitInterval)) (hone : ∀ y, r (1, y) = 1)
    (y : F) (s : unitInterval) : circleMappingTorusPhaseInterpolation r (1, y) s = 1 := by
  apply Subtype.ext
  simp [circleMappingTorusPhaseInterpolation, hone]

private theorem circleMappingTorusPhaseInterpolation_triple_eq_of_end
    (r : C(unitInterval × F, unitInterval)) (hzero : ∀ y, r (0, y) = 0)
    (hone : ∀ y, r (1, y) = 1) (p : Unit × unitInterval × F) (s : unitInterval)
    (hp : p.2.1 = 0 ∨ p.2.1 = 1) :
    (p.1, circleMappingTorusPhaseInterpolation r p.2 s, p.2.2) = p := by
  rcases p with ⟨i, t, y⟩
  rcases hp with hp | hp
  · dsimp only [Prod.fst, Prod.snd] at hp ⊢
    subst t
    rw [circleMappingTorusPhaseInterpolation_eq_zero r hzero]
  · dsimp only [Prod.fst, Prod.snd] at hp ⊢
    subst t
    rw [circleMappingTorusPhaseInterpolation_eq_one r hone]

private theorem circleMappingTorusPhaseInterpolation_respects
    (φ : F ≃ₜ F) (r : C(unitInterval × F, unitInterval))
    (hzero : ∀ y, r (0, y) = 0) (hone : ∀ y, r (1, y) = 1)
    {p q : Unit × unitInterval × F}
    (h : finiteBouquetMappingTorusSetoid (fun _ : Unit ↦ φ) p q) (s : unitInterval) :
    bouquetMk (fun _ : Unit ↦ φ)
        (p.1, circleMappingTorusPhaseInterpolation r p.2 s, p.2.2) =
      bouquetMk (fun _ : Unit ↦ φ)
        (q.1, circleMappingTorusPhaseInterpolation r q.2 s, q.2.2) := by
  rw [bouquetMk_eq_iff]
  have hkey : bouquetKey (fun _ : Unit ↦ φ) p = bouquetKey (fun _ : Unit ↦ φ) q :=
    (eqvGen_iff_bouquetKey (fun _ : Unit ↦ φ) p q).mp h
  rcases eq_or_mem_ends_of_bouquetKey hkey with rfl | ⟨hp, hq⟩
  · rfl
  · have hpfix := circleMappingTorusPhaseInterpolation_triple_eq_of_end
      r hzero hone p s hp
    have hqfix := circleMappingTorusPhaseInterpolation_triple_eq_of_end
      r hzero hone q s hq
    simpa only [hpfix, hqfix] using hkey

/-- The interpolated paths before passing to the mapping-torus quotient. -/
public noncomputable def circleMappingTorusCylinderReparametrizationPaths
    (φ : F ≃ₜ F) (r : C(unitInterval × F, unitInterval)) :
    C(Unit × unitInterval × F, C(unitInterval, CircleMappingTorus φ)) :=
  ContinuousMap.curry
    ⟨fun q ↦ bouquetMk (fun _ : Unit ↦ φ)
        (q.1.1, circleMappingTorusPhaseInterpolation r q.1.2 q.2, q.1.2.2),
      continuous_quot_mk.comp <| continuous_fst.comp continuous_fst |>.prodMk
        ((Continuous.subtype_mk
            (((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul
                (continuous_subtype_val.comp (r.continuous.comp
                  (continuous_snd.comp continuous_fst)))).add
              ((continuous_subtype_val.comp continuous_snd).mul
                (continuous_subtype_val.comp
                  (continuous_fst.comp (continuous_snd.comp continuous_fst))))) _).prodMk
          (continuous_snd.comp (continuous_snd.comp continuous_fst)))⟩

/-- Endpoint-fixed interpolation preserves the mapping-torus quotient relation. -/
public theorem circleMappingTorusCylinderReparametrizationPaths_respects
    (φ : F ≃ₜ F) (r : C(unitInterval × F, unitInterval))
    (hzero : ∀ y, r (0, y) = 0) (hone : ∀ y, r (1, y) = 1)
    (p q : Unit × unitInterval × F)
    (hpq : finiteBouquetMappingTorusSetoid (fun _ : Unit ↦ φ) p q) :
    circleMappingTorusCylinderReparametrizationPaths φ r p =
      circleMappingTorusCylinderReparametrizationPaths φ r q := by
  apply ContinuousMap.ext
  intro s
  exact circleMappingTorusPhaseInterpolation_respects φ r hzero hone hpq s

/-- The family of quotient maps induced by straight-line interpolation of an endpoint-fixed
phase. -/
public noncomputable def circleMappingTorusReparametrizationPaths
    (φ : F ≃ₜ F) (r : C(unitInterval × F, unitInterval))
    (hzero : ∀ y, r (0, y) = 0) (hone : ∀ y, r (1, y) = 1) :
    C(CircleMappingTorus φ, C(unitInterval, CircleMappingTorus φ)) :=
  ⟨Quotient.lift (circleMappingTorusCylinderReparametrizationPaths φ r)
      (circleMappingTorusCylinderReparametrizationPaths_respects φ r hzero hone),
    continuous_quot_lift
      (circleMappingTorusCylinderReparametrizationPaths_respects φ r hzero hone)
      (circleMappingTorusCylinderReparametrizationPaths φ r).continuous⟩

@[simp]
public theorem circleMappingTorusReparametrizationPaths_cylinderProjection
    (φ : F ≃ₜ F) (r : C(unitInterval × F, unitInterval))
    (hzero : ∀ y, r (0, y) = 0) (hone : ∀ y, r (1, y) = 1)
    (p : unitInterval × F) (s : unitInterval) :
    circleMappingTorusReparametrizationPaths φ r hzero hone
        (circleMappingTorusCylinderProjection φ p) s =
      circleMappingTorusCylinderProjection φ
        (circleMappingTorusPhaseInterpolation r p s, p.2) := by
  change Quotient.lift (circleMappingTorusCylinderReparametrizationPaths φ r)
      (circleMappingTorusCylinderReparametrizationPaths_respects φ r hzero hone)
      (Quotient.mk _ ((), p)) s = _
  rw [Quotient.lift_mk]
  rfl

/-- The self-map induced by an endpoint-fixed cylinder phase. -/
public noncomputable def circleMappingTorusReparametrization
    (φ : F ≃ₜ F) (r : C(unitInterval × F, unitInterval))
    (hzero : ∀ y, r (0, y) = 0) (hone : ∀ y, r (1, y) = 1) :
    C(CircleMappingTorus φ, CircleMappingTorus φ) :=
  ⟨fun z ↦ circleMappingTorusReparametrizationPaths φ r hzero hone z 0,
    ((ContinuousMap.uncurry
      (circleMappingTorusReparametrizationPaths φ r hzero hone)).continuous.comp
        (continuous_id.prodMk continuous_const))⟩

@[simp]
public theorem circleMappingTorusReparametrization_cylinderProjection
    (φ : F ≃ₜ F) (r : C(unitInterval × F, unitInterval))
    (hzero : ∀ y, r (0, y) = 0) (hone : ∀ y, r (1, y) = 1)
    (p : unitInterval × F) :
    circleMappingTorusReparametrization φ r hzero hone
        (circleMappingTorusCylinderProjection φ p) =
      circleMappingTorusCylinderProjection φ (r p, p.2) := by
  change circleMappingTorusReparametrizationPaths φ r hzero hone
      (circleMappingTorusCylinderProjection φ p) 0 = _
  rw [circleMappingTorusReparametrizationPaths_cylinderProjection]
  simp

/-- The quotient-descended reparameterization is homotopic to the identity. -/
public noncomputable def circleMappingTorusReparametrizationHomotopy
    (φ : F ≃ₜ F) (r : C(unitInterval × F, unitInterval))
    (hzero : ∀ y, r (0, y) = 0) (hone : ∀ y, r (1, y) = 1) :
    ContinuousMap.Homotopy (circleMappingTorusReparametrization φ r hzero hone)
      (ContinuousMap.id (CircleMappingTorus φ)) where
  toFun q := circleMappingTorusReparametrizationPaths φ r hzero hone q.2 q.1
  continuous_toFun :=
    (ContinuousMap.uncurry
      (circleMappingTorusReparametrizationPaths φ r hzero hone)).continuous.comp continuous_swap
  map_zero_left z := rfl
  map_one_left z := by
    induction z using Quotient.inductionOn with
    | _ p =>
      rcases p.1 with ⟨⟩
      change circleMappingTorusReparametrizationPaths φ r hzero hone
          (circleMappingTorusCylinderProjection φ p.2) 1 =
        circleMappingTorusCylinderProjection φ p.2
      rw [circleMappingTorusReparametrizationPaths_cylinderProjection]
      simp

/-- The induced self-map is homotopic to the identity, hence has degree one in the sense used by
the pullback-cover comparison. -/
public theorem circleMappingTorusReparametrization_homotopic_id
    (φ : F ≃ₜ F) (r : C(unitInterval × F, unitInterval))
    (hzero : ∀ y, r (0, y) = 0) (hone : ∀ y, r (1, y) = 1) :
    (circleMappingTorusReparametrization φ r hzero hone).Homotopic
      (ContinuousMap.id (CircleMappingTorus φ)) :=
  ⟨circleMappingTorusReparametrizationHomotopy φ r hzero hone⟩

/-- Pullback of the standard vertex open is determined pointwise by the scalar phase. -/
public theorem circleMappingTorusReparametrization_vertex_pullback
    (φ : F ≃ₜ F) (r : C(unitInterval × F, unitInterval))
    (hzero : ∀ y, r (0, y) = 0) (hone : ∀ y, r (1, y) = 1)
    (U : Opens (TopCat.of (CircleMappingTorus φ)))
    (hU : ∀ p : unitInterval × F,
      r p ∈ vertexBand ↔ circleMappingTorusCylinderProjection φ p ∈ U) :
    (Opens.map (TopCat.ofHom
      (circleMappingTorusReparametrization φ r hzero hone))).obj
        (Topology.CanonicalProductWangBoundaryNaturality.mappingTorusVertexOpen φ) = U := by
  ext z
  induction z using Quotient.inductionOn with
  | _ p =>
    rcases p.1 with ⟨⟩
    change circleMappingTorusReparametrization φ r hzero hone
        (circleMappingTorusCylinderProjection φ p.2) ∈
          vertexPiece (fun _ : Unit ↦ φ) ↔
      circleMappingTorusCylinderProjection φ p.2 ∈ U
    rw [circleMappingTorusReparametrization_cylinderProjection, vertexPiece]
    change bouquetMk (fun _ : Unit ↦ φ) ((), r p.2, p.2.2) ∈
        bouquetPiece (fun _ : Unit ↦ φ) vertexBand ↔ _
    rw [mem_bouquetPiece_mk_iff (fun _ : Unit ↦ φ) vertexBand_ends]
    exact hU p.2

/-- Pullback of the standard edge open is determined pointwise by the scalar phase. -/
public theorem circleMappingTorusReparametrization_edge_pullback
    (φ : F ≃ₜ F) (r : C(unitInterval × F, unitInterval))
    (hzero : ∀ y, r (0, y) = 0) (hone : ∀ y, r (1, y) = 1)
    (U : Opens (TopCat.of (CircleMappingTorus φ)))
    (hU : ∀ p : unitInterval × F,
      r p ∈ edgeBand ↔ circleMappingTorusCylinderProjection φ p ∈ U) :
    (Opens.map (TopCat.ofHom
      (circleMappingTorusReparametrization φ r hzero hone))).obj
        (Topology.CanonicalProductWangBoundaryNaturality.mappingTorusEdgeOpen φ) = U := by
  ext z
  induction z using Quotient.inductionOn with
  | _ p =>
    rcases p.1 with ⟨⟩
    change circleMappingTorusReparametrization φ r hzero hone
        (circleMappingTorusCylinderProjection φ p.2) ∈
          edgePiece (fun _ : Unit ↦ φ) ↔
      circleMappingTorusCylinderProjection φ p.2 ∈ U
    rw [circleMappingTorusReparametrization_cylinderProjection, edgePiece]
    change bouquetMk (fun _ : Unit ↦ φ) ((), r p.2, p.2.2) ∈
        bouquetPiece (fun _ : Unit ↦ φ) edgeBand ↔ _
    rw [mem_bouquetPiece_mk_iff (fun _ : Unit ↦ φ) edgeBand_ends]
    exact hU p.2

end SphereSixComplex

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.MappingTorusDegreeOneCoverComparison

variable {A : PaperAnalyticData}

namespace SectionSevenEllipticTwoDiscCoverData

/-- An endpoint-fixed phase with the two exact band criteria supplies all four fields of the
adaptive degree-one self-map package. -/
public noncomputable def actualCuspAdaptiveCoverDegreeOneSelfMapOfPhase
    (R : A.SectionSevenAffineRadialCompletionInput)
    (r : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      C(unitInterval × G.Fiber, unitInterval))
    (hzero : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      ∀ y, r (0, y) = 0)
    (hone : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      ∀ y, r (1, y) = 1)
    (hvertex : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      ∀ p : unitInterval × G.Fiber,
        r p ∈ vertexBand ↔ circleMappingTorusCylinderProjection G.clutching p ∈
          actualCuspMappingTorusOrderFourOpen R)
    (hedge : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      ∀ p : unitInterval × G.Fiber,
        r p ∈ edgeBand ↔ circleMappingTorusCylinderProjection G.clutching p ∈
          actualCuspMappingTorusOrderThreeOpen R) :
    ActualCuspAdaptiveCoverDegreeOneSelfMap R := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact
    { selfMap := circleMappingTorusReparametrization G.clutching r hzero hone
      homotopic_id := circleMappingTorusReparametrization_homotopic_id
        G.clutching r hzero hone
      vertex_pullback := circleMappingTorusReparametrization_vertex_pullback
        G.clutching r hzero hone (actualCuspMappingTorusOrderFourOpen R) hvertex
      edge_pullback := circleMappingTorusReparametrization_edge_pullback
        G.clutching r hzero hone (actualCuspMappingTorusOrderThreeOpen R) hedge }

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
