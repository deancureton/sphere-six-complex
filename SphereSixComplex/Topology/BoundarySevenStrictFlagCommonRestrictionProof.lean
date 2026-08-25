module

public import SphereSixComplex.Topology.BoundarySevenStrictFlagOverlap
public import SphereSixComplex.Topology.StandardSimplexPositiveSupport

/-!
# Common restrictions for equal strict-flag affine presentations

Positive faces are recovered intrinsically from the represented boundary point.  This file
packages that recovery into an order isomorphism of positive levels and then into a common
simplicial restriction of the two flag representatives.
-/

@[expose] public section

noncomputable section

open CategoryTheory PartialOrder Simplicial

namespace SphereSixComplex

/-- The positive level of `G` whose face equals a specified positive level of `F`. -/
public noncomputable def boundarySevenStrictFlagPositiveFaceMatch
    (k m : ℕ)
    (F : ComposableArrows BoundarySevenProperFace k)
    (G : ComposableArrows BoundarySevenProperFace m)
    (w : stdSimplex ℝ (Fin (k + 1)))
    (v : stdSimplex ℝ (Fin (m + 1)))
    (hF : StrictMono F.obj) (hG : StrictMono G.obj)
    (h : boundarySevenProperFaceAffineFlagMap k F w =
      boundarySevenProperFaceAffineFlagMap m G v)
    (j : {j : Fin (k + 1) // 0 < w j}) :
    {l : Fin (m + 1) // 0 < v l} :=
  ⟨(boundarySevenStrictFlag_overlap_exists_positive_face_eq
      k m F G w v hF hG h j.1 j.2).choose,
    (boundarySevenStrictFlag_overlap_exists_positive_face_eq
      k m F G w v hF hG h j.1 j.2).choose_spec.1⟩

@[simp]
public theorem boundarySevenStrictFlagPositiveFaceMatch_face
    (k m : ℕ)
    (F : ComposableArrows BoundarySevenProperFace k)
    (G : ComposableArrows BoundarySevenProperFace m)
    (w : stdSimplex ℝ (Fin (k + 1)))
    (v : stdSimplex ℝ (Fin (m + 1)))
    (hF : StrictMono F.obj) (hG : StrictMono G.obj)
    (h : boundarySevenProperFaceAffineFlagMap k F w =
      boundarySevenProperFaceAffineFlagMap m G v)
    (j : {j : Fin (k + 1) // 0 < w j}) :
    F.obj j.1 = G.obj
      (boundarySevenStrictFlagPositiveFaceMatch k m F G w v hF hG h j).1 :=
  (boundarySevenStrictFlag_overlap_exists_positive_face_eq
    k m F G w v hF hG h j.1 j.2).choose_spec.2

/-- Equal strict-flag affine presentations have canonically matched ordered positive levels. -/
public noncomputable def boundarySevenStrictFlagPositiveFaceOrderIso
    (k m : ℕ)
    (F : ComposableArrows BoundarySevenProperFace k)
    (G : ComposableArrows BoundarySevenProperFace m)
    (w : stdSimplex ℝ (Fin (k + 1)))
    (v : stdSimplex ℝ (Fin (m + 1)))
    (hF : StrictMono F.obj) (hG : StrictMono G.obj)
    (h : boundarySevenProperFaceAffineFlagMap k F w =
      boundarySevenProperFaceAffineFlagMap m G v) :
    {j : Fin (k + 1) // 0 < w j} ≃o
      {l : Fin (m + 1) // 0 < v l} where
  toFun := boundarySevenStrictFlagPositiveFaceMatch k m F G w v hF hG h
  invFun := boundarySevenStrictFlagPositiveFaceMatch m k G F v w hG hF h.symm
  left_inv j := by
    apply Subtype.ext
    apply hF.injective
    have hforward := boundarySevenStrictFlagPositiveFaceMatch_face
      k m F G w v hF hG h j
    have hbackward := boundarySevenStrictFlagPositiveFaceMatch_face
      m k G F v w hG hF h.symm
        (boundarySevenStrictFlagPositiveFaceMatch k m F G w v hF hG h j)
    exact (hforward.trans hbackward).symm
  right_inv l := by
    apply Subtype.ext
    apply hG.injective
    have hbackward := boundarySevenStrictFlagPositiveFaceMatch_face
      m k G F v w hG hF h.symm l
    have hforward := boundarySevenStrictFlagPositiveFaceMatch_face
      k m F G w v hF hG h
        (boundarySevenStrictFlagPositiveFaceMatch m k G F v w hG hF h.symm l)
    exact (hbackward.trans hforward).symm
  map_rel_iff' {i j} := by
    let e := boundarySevenStrictFlagPositiveFaceMatch k m F G w v hF hG h
    change (e i).1 ≤ (e j).1 ↔ i.1 ≤ j.1
    calc
      (e i).1 ≤ (e j).1 ↔ G.obj (e i).1 ≤ G.obj (e j).1 :=
        hG.le_iff_le.symm
      _ ↔ F.obj i.1 ≤ F.obj j.1 := by
        rw [boundarySevenStrictFlagPositiveFaceMatch_face
          k m F G w v hF hG h i,
          boundarySevenStrictFlagPositiveFaceMatch_face
            k m F G w v hF hG h j]
      _ ↔ i.1 ≤ j.1 := hF.le_iff_le

/-- The proposition-level positive-face matching interface is unconditional. -/
public theorem boundarySevenStrictFlagPositiveFaceOrderMatching_proof :
    BoundarySevenStrictFlagPositiveFaceOrderMatching := by
  intro k m F G w v hF hG h
  let e := boundarySevenStrictFlagPositiveFaceOrderIso
    k m F G w v hF hG h
  refine ⟨e, ?_⟩
  intro j
  exact boundarySevenStrictFlagPositiveFaceMatch_face k m F G w v hF hG h j

/-- Equal strict-flag affine presentations are induced from one common positive-face simplex. -/
public theorem boundarySevenStrictFlagCommonRestriction :
    BoundarySevenStrictFlagCommonRestriction := by
  intro k m F G w v hF hG h
  let r := standardSimplexPositiveSupportDimension w
  let fw : Fin (r + 1) ↪o Fin (k + 1) :=
    standardSimplexPositiveSupportIndex w
  let e := boundarySevenStrictFlagPositiveFaceOrderIso
    k m F G w v hF hG h
  let gwFun : Fin (r + 1) → Fin (m + 1) := fun j ↦
    (e ⟨fw j, standardSimplexPositiveSupportIndex_mem w j⟩).1
  have hgwFun : StrictMono gwFun := by
    intro i j hij
    change (e ⟨fw i, standardSimplexPositiveSupportIndex_mem w i⟩).1 <
      (e ⟨fw j, standardSimplexPositiveSupportIndex_mem w j⟩).1
    exact e.strictMono (fw.strictMono hij)
  let gw : Fin (r + 1) ↪o Fin (m + 1) :=
    OrderEmbedding.ofStrictMono gwFun hgwFun
  let f : SimplexCategory.mk r ⟶ SimplexCategory.mk k :=
    SimplexCategory.mkHom fw.toOrderHom
  let g : SimplexCategory.mk r ⟶ SimplexCategory.mk m :=
    SimplexCategory.mkHom gw.toOrderHom
  let u : stdSimplex ℝ (Fin (r + 1)) :=
    standardSimplexPositiveSupportCompressed w
  have hfg : BoundarySevenProperFaceNerve.map f.op F =
      BoundarySevenProperFaceNerve.map g.op G := by
    refine ComposableArrows.ext (fun i ↦ ?_) (fun i hi ↦ ?_)
    · change F.obj (fw i) = G.obj (gw i)
      exact boundarySevenStrictFlagPositiveFaceMatch_face
        k m F G w v hF hG h
          ⟨fw i, standardSimplexPositiveSupportIndex_mem w i⟩
    · apply Subsingleton.elim
  have hmapf : stdSimplex.map f u = w := by
    exact standardSimplex_map_positiveSupportCompressed w
  have hnatF := congrArg
    (fun q : C(stdSimplex ℝ (Fin (r + 1)), StandardSimplexBoundary 7) ↦ q u)
    (boundarySevenProperFaceAffineFlagMap_naturality f F)
  have hnatG := congrArg
    (fun q : C(stdSimplex ℝ (Fin (r + 1)), StandardSimplexBoundary 7) ↦ q u)
    (boundarySevenProperFaceAffineFlagMap_naturality g G)
  have hmapg : stdSimplex.map g u = v := by
    apply boundarySevenProperFaceAffineFlagMap_injective_of_strictMono m G hG
    calc
      boundarySevenProperFaceAffineFlagMap m G (stdSimplex.map g u) =
          boundarySevenProperFaceAffineFlagMap r
            (BoundarySevenProperFaceNerve.map g.op G) u := hnatG.symm
      _ = boundarySevenProperFaceAffineFlagMap r
            (BoundarySevenProperFaceNerve.map f.op F) u := by rw [hfg]
      _ = boundarySevenProperFaceAffineFlagMap k F (stdSimplex.map f u) := hnatF
      _ = boundarySevenProperFaceAffineFlagMap k F w := by rw [hmapf]
      _ = boundarySevenProperFaceAffineFlagMap m G v := h
  exact ⟨r, f, g, u, hmapf, hmapg, hfg⟩

end SphereSixComplex
