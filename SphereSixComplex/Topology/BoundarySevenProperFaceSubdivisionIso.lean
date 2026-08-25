module

public import SphereSixComplex.Topology.BoundarySevenProperFaceSubdivisionBridge

/-!
# The proper-face subdivision comparison is an isomorphism

This file studies the remaining categorical step in the proper-face subdivision bridge: the
explicit chart cocone should itself be colimiting.  The basic combinatorial fact is that every
flag of proper faces lies in the chart indexed by its largest face.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits PartialOrder Simplicial

namespace SphereSixComplex

/-- The dimension of the unique increasing simplex whose vertex set is a nonempty proper
face. -/
public def boundarySevenProperFaceDimension (t : BoundarySevenProperFace) : ℕ :=
  t.1.card - 1

public theorem boundarySevenProperFace_card_eq_dimension_add_one
    (t : BoundarySevenProperFace) :
    t.1.card = boundarySevenProperFaceDimension t + 1 := by
  rw [boundarySevenProperFaceDimension]
  have hpos : 0 < t.1.card := Finset.card_pos.mpr t.2.1
  omega

/-- Increasing enumeration of the vertices in a proper face. -/
public def boundarySevenProperFaceOrderEmb (t : BoundarySevenProperFace) :
    Fin (boundarySevenProperFaceDimension t + 1) ↪o Fin 8 :=
  t.1.orderEmbOfFin (boundarySevenProperFace_card_eq_dimension_add_one t)

public theorem boundarySevenProperFaceOrderEmb_mem
    (t : BoundarySevenProperFace)
    (i : Fin (boundarySevenProperFaceDimension t + 1)) :
    boundarySevenProperFaceOrderEmb t i ∈ t.1 :=
  Finset.orderEmbOfFin_mem _ _ _

/-- The nondegenerate boundary simplex obtained by increasingly enumerating a proper face. -/
public noncomputable def boundarySevenProperFaceBoundarySimplex
    (t : BoundarySevenProperFace) :
    boundarySevenSimplicialBoundary.obj
      (Opposite.op (SimplexCategory.mk (boundarySevenProperFaceDimension t))) := by
  let e := boundarySevenProperFaceOrderEmb t
  let z : (Δ[7] : SSet.{0}).obj
      (Opposite.op (SimplexCategory.mk (boundarySevenProperFaceDimension t))) :=
    SSet.stdSimplex.objMk e.toOrderHom
  refine ⟨z, ?_⟩
  intro hsurj
  change Function.Surjective e at hsurj
  apply t.2.2
  apply Finset.eq_univ_iff_forall.mpr
  intro a
  obtain ⟨i, hi⟩ := hsurj a
  have himem := boundarySevenProperFaceOrderEmb_mem t i
  rw [← hi]
  exact himem

public theorem boundarySevenProperFaceBoundarySimplex_nonDegenerate
    (t : BoundarySevenProperFace) :
    boundarySevenProperFaceBoundarySimplex t ∈
      boundarySevenSimplicialBoundary.nonDegenerate
        (boundarySevenProperFaceDimension t) := by
  apply (SSet.Subcomplex.mem_nonDegenerate_iff
    (A := SSet.boundary 7) (boundarySevenProperFaceBoundarySimplex t)).2
  rw [SSet.stdSimplex.mem_nonDegenerate_iff_strictMono]
  change StrictMono (boundarySevenProperFaceOrderEmb t)
  exact (boundarySevenProperFaceOrderEmb t).strictMono

/-- The canonical nondegenerate boundary simplex indexed by a proper face. -/
public noncomputable def boundarySevenProperFaceBoundaryN
    (t : BoundarySevenProperFace) : boundarySevenSimplicialBoundary.N :=
  SSet.N.mk (boundarySevenProperFaceBoundarySimplex t)
    (boundarySevenProperFaceBoundarySimplex_nonDegenerate t)

@[simp]
public theorem boundarySevenProperFaceBoundaryN_dim
    (t : BoundarySevenProperFace) :
    (boundarySevenProperFaceBoundaryN t).dim = boundarySevenProperFaceDimension t :=
  rfl

/-- The largest face in a flag. -/
public def boundarySevenProperFaceFlagTop {k : ℕ}
    (F : ComposableArrows BoundarySevenProperFace k) : BoundarySevenProperFace :=
  F.obj (Fin.last k)

public theorem boundarySevenProperFaceFlag_obj_le_top {k : ℕ}
    (F : ComposableArrows BoundarySevenProperFace k) (j : Fin (k + 1)) :
    F.obj j ≤ boundarySevenProperFaceFlagTop F :=
  leOfHom (F.map (homOfLE (Fin.le_last j)))

/-- The vertices of one face of a flag, written in the local increasing coordinates of the
largest face. -/
public noncomputable def boundarySevenProperFaceFlagLocalFinset {k : ℕ}
    (F : ComposableArrows BoundarySevenProperFace k) (j : Fin (k + 1)) :
    Finset (ULift.{0}
      (Fin (boundarySevenProperFaceDimension (boundarySevenProperFaceFlagTop F) + 1))) :=
  (Finset.univ.filter (fun i ↦
    boundarySevenProperFaceOrderEmb (boundarySevenProperFaceFlagTop F) i ∈
      (F.obj j).1)).image ULift.up

public theorem boundarySevenProperFaceFlagLocalFinset_nonempty {k : ℕ}
    (F : ComposableArrows BoundarySevenProperFace k) (j : Fin (k + 1)) :
    (boundarySevenProperFaceFlagLocalFinset F j).Nonempty := by
  obtain ⟨a, ha⟩ := (F.obj j).2.1
  have hatop : a ∈ (boundarySevenProperFaceFlagTop F).1 :=
    boundarySevenProperFaceFlag_obj_le_top F j ha
  let e := (boundarySevenProperFaceFlagTop F).1.orderIsoOfFin
    (boundarySevenProperFace_card_eq_dimension_add_one
      (boundarySevenProperFaceFlagTop F))
  obtain ⟨i, hi⟩ := e.surjective ⟨a, hatop⟩
  refine ⟨ULift.up i, ?_⟩
  rw [boundarySevenProperFaceFlagLocalFinset, Finset.mem_image]
  refine ⟨i, ?_, rfl⟩
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  change (e i).1 ∈ (F.obj j).1
  rw [hi]
  exact ha

/-- A face in the local subdivision chart of the largest face. -/
public noncomputable def boundarySevenProperFaceFlagLocalFace {k : ℕ}
    (F : ComposableArrows BoundarySevenProperFace k) (j : Fin (k + 1)) :
    NonemptyFiniteChains
      (ULift.{0}
        (Fin (boundarySevenProperFaceDimension (boundarySevenProperFaceFlagTop F) + 1))) where
  finset := boundarySevenProperFaceFlagLocalFinset F j
  nonempty := boundarySevenProperFaceFlagLocalFinset_nonempty F j
  comparable := fun _ _ ↦ le_total _ _

public theorem boundarySevenProperFaceFlagLocalFace_mono {k : ℕ}
    (F : ComposableArrows BoundarySevenProperFace k) {i j : Fin (k + 1)}
    (hij : i ≤ j) :
    boundarySevenProperFaceFlagLocalFace F i ≤
      boundarySevenProperFaceFlagLocalFace F j := by
  intro a ha
  change a ∈ boundarySevenProperFaceFlagLocalFinset F i at ha
  change a ∈ boundarySevenProperFaceFlagLocalFinset F j
  rw [boundarySevenProperFaceFlagLocalFinset, Finset.mem_image] at ha ⊢
  obtain ⟨b, hb, rfl⟩ := ha
  refine ⟨b, ?_, rfl⟩
  rw [Finset.mem_filter] at hb ⊢
  refine ⟨hb.1, ?_⟩
  exact leOfHom (F.map (homOfLE hij)) hb.2

/-- A flag, expressed in the subdivision chart indexed by its largest face. -/
public noncomputable def boundarySevenProperFaceFlagLocalFlag {k : ℕ}
    (F : ComposableArrows BoundarySevenProperFace k) :
    ComposableArrows
      (NonemptyFiniteChains
        (ULift.{0}
          (Fin (boundarySevenProperFaceDimension (boundarySevenProperFaceFlagTop F) + 1)))) k where
  obj := boundarySevenProperFaceFlagLocalFace F
  map f := homOfLE (boundarySevenProperFaceFlagLocalFace_mono F (leOfHom f))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

@[simp]
public theorem boundarySevenProperFaceBoundaryN_ambientOrderHom
    (t : BoundarySevenProperFace) :
    boundarySevenNondegenerateAmbientOrderHom
        (boundarySevenProperFaceBoundaryN t) =
      (boundarySevenProperFaceOrderEmb t).toOrderHom := by
  rfl

/-- Mapping a local face back to ambient vertices recovers the original face of the flag. -/
public theorem boundarySevenProperFaceFlagLocalFace_map {k : ℕ}
    (F : ComposableArrows BoundarySevenProperFace k) (j : Fin (k + 1)) :
    boundarySevenNondegenerateFaceMap
        (boundarySevenProperFaceBoundaryN (boundarySevenProperFaceFlagTop F))
        (boundarySevenProperFaceFlagLocalFace F j) =
      F.obj j := by
  apply Subtype.ext
  have hval := boundarySevenNondegenerateFaceMap_val
    (boundarySevenProperFaceBoundaryN (boundarySevenProperFaceFlagTop F))
    (boundarySevenProperFaceFlagLocalFace F j)
  rw [hval]
  change
    (boundarySevenProperFaceFlagLocalFinset F j).image
        (fun i ↦ boundarySevenProperFaceOrderEmb
          (boundarySevenProperFaceFlagTop F) i.down) =
      (F.obj j).1
  rw [boundarySevenProperFaceFlagLocalFinset, Finset.image_image]
  apply Finset.ext
  intro a
  constructor
  · intro ha
    obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp ha
    rw [Finset.mem_filter] at hi
    rw [← hia]
    exact hi.2
  · intro ha
    have hatop : a ∈ (boundarySevenProperFaceFlagTop F).1 :=
      boundarySevenProperFaceFlag_obj_le_top F j ha
    let e := (boundarySevenProperFaceFlagTop F).1.orderIsoOfFin
      (boundarySevenProperFace_card_eq_dimension_add_one
        (boundarySevenProperFaceFlagTop F))
    obtain ⟨i, hi⟩ := e.surjective ⟨a, hatop⟩
    refine Finset.mem_image.mpr ⟨i, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      change (e i).1 ∈ (F.obj j).1
      rw [hi]
      exact ha
    · change (e i).1 = a
      exact congrArg Subtype.val hi

/-- The nerve map of a largest-face chart sends the local flag to the original flag. -/
public theorem boundarySevenProperFaceFlagLocalFlag_map {k : ℕ}
    (F : ComposableArrows BoundarySevenProperFace k) :
    (PartOrd.nerveFunctor.map
      (boundarySevenNondegenerateFaceHom
        (boundarySevenProperFaceBoundaryN
          (boundarySevenProperFaceFlagTop F)))).app
        (Opposite.op (SimplexCategory.mk k))
        (boundarySevenProperFaceFlagLocalFlag F) = F := by
  refine ComposableArrows.ext (fun j ↦ ?_) (fun j hj ↦ ?_)
  · exact boundarySevenProperFaceFlagLocalFace_map F j
  · apply Subsingleton.elim

/-- A chosen preimage of a flag in the subdivision chart of its largest face. -/
public noncomputable def boundarySevenProperFaceFlagChartPoint {k : ℕ}
    (F : ComposableArrows BoundarySevenProperFace k) :
    (SSet.sd.obj
      (SSet.stdSimplex.obj
        (SimplexCategory.mk
          (boundarySevenProperFaceDimension
            (boundarySevenProperFaceFlagTop F))))).obj
      (Opposite.op (SimplexCategory.mk k)) :=
  (SSet.stdSimplex.sdIso.inv.app
    (SimplexCategory.mk
      (boundarySevenProperFaceDimension
        (boundarySevenProperFaceFlagTop F)))).app
    (Opposite.op (SimplexCategory.mk k))
    (boundarySevenProperFaceFlagLocalFlag F)

/-- Every simplex of the proper-face nerve is covered by the chart of its largest face. -/
public theorem boundarySevenProperFaceFlag_chart_covered {k : ℕ}
    (F : ComposableArrows BoundarySevenProperFace k) :
    (boundarySevenNondegenerateSubdivisionChart
      (boundarySevenProperFaceBoundaryN
        (boundarySevenProperFaceFlagTop F))).app
        (Opposite.op (SimplexCategory.mk k))
        (boundarySevenProperFaceFlagChartPoint F) = F := by
  change
    (PartOrd.nerveFunctor.map
      (boundarySevenNondegenerateFaceHom
        (boundarySevenProperFaceBoundaryN
          (boundarySevenProperFaceFlagTop F)))).app
      (Opposite.op (SimplexCategory.mk k))
      ((SSet.stdSimplex.sdIso.hom.app
        (SimplexCategory.mk
          (boundarySevenProperFaceDimension
            (boundarySevenProperFaceFlagTop F)))).app
        (Opposite.op (SimplexCategory.mk k))
        ((SSet.stdSimplex.sdIso.inv.app
          (SimplexCategory.mk
            (boundarySevenProperFaceDimension
              (boundarySevenProperFaceFlagTop F)))).app
          (Opposite.op (SimplexCategory.mk k))
          (boundarySevenProperFaceFlagLocalFlag F))) = F
  have hcancel :
      (SSet.stdSimplex.sdIso.hom.app
        (SimplexCategory.mk
          (boundarySevenProperFaceDimension
            (boundarySevenProperFaceFlagTop F)))).app
          (Opposite.op (SimplexCategory.mk k))
          ((SSet.stdSimplex.sdIso.inv.app
            (SimplexCategory.mk
              (boundarySevenProperFaceDimension
                (boundarySevenProperFaceFlagTop F)))).app
            (Opposite.op (SimplexCategory.mk k))
            (boundarySevenProperFaceFlagLocalFlag F)) =
        boundarySevenProperFaceFlagLocalFlag F := by
    have h := congrArg
      (fun q : SimplexCategory.sd.obj
            (SimplexCategory.mk
              (boundarySevenProperFaceDimension
                (boundarySevenProperFaceFlagTop F))) ⟶
          SimplexCategory.sd.obj
            (SimplexCategory.mk
              (boundarySevenProperFaceDimension
                (boundarySevenProperFaceFlagTop F))) ↦
        q.app (Opposite.op (SimplexCategory.mk k))
          (boundarySevenProperFaceFlagLocalFlag F))
      (Iso.inv_hom_id (SSet.stdSimplex.sdIso.app
        (SimplexCategory.mk
          (boundarySevenProperFaceDimension
            (boundarySevenProperFaceFlagTop F)))))
    exact h
  rw [hcancel]
  exact boundarySevenProperFaceFlagLocalFlag_map F

/-- The ambient vertex enumeration of a nondegenerate boundary simplex is strictly
increasing. -/
public theorem boundarySevenNondegenerateAmbientOrderHom_strictMono
    (x : boundarySevenSimplicialBoundary.N) :
    StrictMono (boundarySevenNondegenerateAmbientOrderHom x) := by
  have hx := (SSet.Subcomplex.mem_nonDegenerate_iff
    (A := SSet.boundary 7) x.simplex).1 x.nonDegenerate
  rw [SSet.stdSimplex.mem_nonDegenerate_iff_strictMono] at hx
  exact hx

/-- Removing the universe lift from the ambient vertex map does not introduce any
identifications. -/
public theorem boundarySevenNondegenerateAmbientVertexHom_injective
    (x : boundarySevenSimplicialBoundary.N) :
    Function.Injective (boundarySevenNondegenerateAmbientVertexHom x).hom := by
  intro i j hij
  apply ULift.ext
  exact (boundarySevenNondegenerateAmbientOrderHom_strictMono x).injective hij

/-- The ambient vertex set of a nondegenerate simplex of the boundary. -/
public def boundarySevenNondegenerateVertexFace
    (x : boundarySevenSimplicialBoundary.N) : BoundarySevenProperFace := by
  let t : Finset (Fin 8) := Finset.univ.image
    (boundarySevenNondegenerateAmbientOrderHom x)
  refine ⟨t, Finset.image_nonempty.mpr Finset.univ_nonempty, ?_⟩
  intro ht
  apply x.simplex.2
  intro a
  have ha : a ∈ t := by rw [ht]; simp
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp ha
  exact ⟨i, hi⟩

public theorem boundarySevenNondegenerateVertexFace_card
    (x : boundarySevenSimplicialBoundary.N) :
    (boundarySevenNondegenerateVertexFace x).1.card = x.dim + 1 := by
  rw [boundarySevenNondegenerateVertexFace,
    Finset.card_image_of_injective _
      (boundarySevenNondegenerateAmbientOrderHom_strictMono x).injective,
    Finset.card_univ, Fintype.card_fin]

/-- A nondegenerate boundary simplex is the increasing enumeration of its ambient vertex
face. -/
public theorem boundarySevenNondegenerateAmbientOrderHom_eq_vertexFaceOrderEmb
    (x : boundarySevenSimplicialBoundary.N) :
    boundarySevenNondegenerateAmbientOrderHom x =
      (boundarySevenNondegenerateVertexFace x).1.orderEmbOfFin
        (boundarySevenNondegenerateVertexFace_card x) := by
  apply OrderHom.ext
  funext i
  exact congrFun (Finset.orderEmbOfFin_unique
    (boundarySevenNondegenerateVertexFace_card x)
    (fun i ↦ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    (boundarySevenNondegenerateAmbientOrderHom_strictMono x)) i

public theorem boundarySevenNondegenerateVertexFace_dimension
    (x : boundarySevenSimplicialBoundary.N) :
    boundarySevenProperFaceDimension
      (boundarySevenNondegenerateVertexFace x) = x.dim := by
  rw [boundarySevenProperFaceDimension,
    boundarySevenNondegenerateVertexFace_card]
  omega

/-- The ambient vertex set of the canonical simplex indexed by a proper face is that face. -/
@[simp]
public theorem boundarySevenNondegenerateVertexFace_boundaryN
    (t : BoundarySevenProperFace) :
    boundarySevenNondegenerateVertexFace
      (boundarySevenProperFaceBoundaryN t) = t := by
  apply Subtype.ext
  change Finset.univ.image (boundarySevenProperFaceOrderEmb t) = t.1
  exact Finset.image_orderEmbOfFin_univ _ _

/-- Passing from a nondegenerate boundary simplex to its ambient vertex face is monotone. -/
public theorem boundarySevenNondegenerateVertexFace_mono
    {x y : boundarySevenSimplicialBoundary.N} (hxy : x ≤ y) :
    boundarySevenNondegenerateVertexFace x ≤
      boundarySevenNondegenerateVertexFace y := by
  intro a ha
  change a ∈ Finset.univ.image
      (boundarySevenNondegenerateAmbientOrderHom x) at ha
  change a ∈ Finset.univ.image
      (boundarySevenNondegenerateAmbientOrderHom y)
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
  refine Finset.mem_image.mpr ⟨(SSet.N.monoOfLE hxy).toOrderHom i,
    Finset.mem_univ _, ?_⟩
  exact (boundarySevenNondegenerateAmbientOrderHom_monoOfLE hxy i).symm

/-- Local vertex coordinates for the inclusion of one ambient vertex face in another. -/
public def boundarySevenNondegenerateVertexFaceIndexOrderEmb
    {x y : boundarySevenSimplicialBoundary.N}
    (hxy : boundarySevenNondegenerateVertexFace x ≤
      boundarySevenNondegenerateVertexFace y) :
    Fin (x.dim + 1) ↪o Fin (y.dim + 1) :=
  OrderEmbedding.ofStrictMono
    (fun i ↦
      ((boundarySevenNondegenerateVertexFace y).1.orderIsoOfFin
        (boundarySevenNondegenerateVertexFace_card y)).symm
        ⟨boundarySevenNondegenerateAmbientOrderHom x i,
          hxy (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩)
    (fun _ _ hij ↦
      ((boundarySevenNondegenerateVertexFace y).1.orderIsoOfFin
        (boundarySevenNondegenerateVertexFace_card y)).symm.strictMono
        ((boundarySevenNondegenerateAmbientOrderHom_strictMono x) hij))

public theorem boundarySevenNondegenerateVertexFaceIndexOrderEmb_map
    {x y : boundarySevenSimplicialBoundary.N}
    (hxy : boundarySevenNondegenerateVertexFace x ≤
      boundarySevenNondegenerateVertexFace y)
    (i : Fin (x.dim + 1)) :
    boundarySevenNondegenerateAmbientOrderHom y
        (boundarySevenNondegenerateVertexFaceIndexOrderEmb hxy i) =
      boundarySevenNondegenerateAmbientOrderHom x i := by
  rw [boundarySevenNondegenerateAmbientOrderHom_eq_vertexFaceOrderEmb]
  exact congrArg Subtype.val
    (((boundarySevenNondegenerateVertexFace y).1.orderIsoOfFin
      (boundarySevenNondegenerateVertexFace_card y)).apply_symm_apply
        ⟨boundarySevenNondegenerateAmbientOrderHom x i,
          hxy (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩)

/-- Inclusion of ambient vertex faces exactly characterizes the order on nondegenerate
boundary simplices. -/
public theorem boundarySevenNondegenerateVertexFace_le_iff
    {x y : boundarySevenSimplicialBoundary.N} :
    boundarySevenNondegenerateVertexFace x ≤
        boundarySevenNondegenerateVertexFace y ↔
      x ≤ y := by
  constructor
  · intro hxy
    rw [SSet.N.le_iff_exists_mono]
    let f : SimplexCategory.mk x.dim ⟶ SimplexCategory.mk y.dim :=
      SimplexCategory.Hom.mk
        (boundarySevenNondegenerateVertexFaceIndexOrderEmb hxy).toOrderHom
    refine ⟨f, (SimplexCategory.mono_iff_injective (f := f)).2
      (boundarySevenNondegenerateVertexFaceIndexOrderEmb hxy).injective, ?_⟩
    apply Subtype.ext
    apply ULift.ext
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    exact boundarySevenNondegenerateVertexFaceIndexOrderEmb_map hxy i
  · exact boundarySevenNondegenerateVertexFace_mono

/-- Increasingly enumerating the ambient vertex set of a nondegenerate boundary simplex
recovers that simplex. -/
@[simp]
public theorem boundarySevenProperFaceBoundaryN_vertexFace
    (x : boundarySevenSimplicialBoundary.N) :
    boundarySevenProperFaceBoundaryN
      (boundarySevenNondegenerateVertexFace x) = x := by
  apply le_antisymm
  · rw [← boundarySevenNondegenerateVertexFace_le_iff]
    simp
  · rw [← boundarySevenNondegenerateVertexFace_le_iff]
    simp

/-- Nondegenerate boundary simplices, ordered by face inclusion, are exactly nonempty proper
ambient vertex faces. -/
public noncomputable def boundarySevenNondegenerateVertexFaceOrderIso :
    boundarySevenSimplicialBoundary.N ≃o BoundarySevenProperFace where
  toFun := boundarySevenNondegenerateVertexFace
  invFun := boundarySevenProperFaceBoundaryN
  left_inv := boundarySevenProperFaceBoundaryN_vertexFace
  right_inv := boundarySevenNondegenerateVertexFace_boundaryN
  map_rel_iff' := boundarySevenNondegenerateVertexFace_le_iff

/-- Every face in a local chart is contained in the ambient vertex face of the chart. -/
public theorem boundarySevenNondegenerateFaceMap_le_vertexFace
    (x : boundarySevenSimplicialBoundary.N)
    (s : NonemptyFiniteChains (ULift.{0} (Fin (x.dim + 1)))) :
    boundarySevenNondegenerateFaceMap x s ≤
      boundarySevenNondegenerateVertexFace x := by
  intro a ha
  rw [boundarySevenNondegenerateFaceMap_val] at ha
  change a ∈ Finset.univ.image
    (boundarySevenNondegenerateAmbientOrderHom x)
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  exact Finset.mem_image.mpr ⟨i.down, Finset.mem_univ _, rfl⟩

/-- The largest ambient face of a flag produced by a chart is contained in the ambient
vertex face indexing that chart. -/
public theorem boundarySevenNondegenerateSubdivisionChart_top_le_vertexFace
    (x : boundarySevenSimplicialBoundary.N) {k : ℕ}
    (p : (SSet.sd.obj
      (SSet.stdSimplex.obj (SimplexCategory.mk x.dim))).obj
        (Opposite.op (SimplexCategory.mk k))) :
    boundarySevenProperFaceFlagTop
        ((boundarySevenNondegenerateSubdivisionChart x).app
          (Opposite.op (SimplexCategory.mk k)) p) ≤
      boundarySevenNondegenerateVertexFace x := by
  change boundarySevenNondegenerateFaceMap x
      (((SSet.stdSimplex.sdIso.hom.app
        (SimplexCategory.mk x.dim)).app
          (Opposite.op (SimplexCategory.mk k)) p).obj (Fin.last k)) ≤
    boundarySevenNondegenerateVertexFace x
  exact boundarySevenNondegenerateFaceMap_le_vertexFace _ _

/-- If a flag is represented in a chart, its canonical largest-face chart maps into that
chart in the nondegenerate-simplex indexing category. -/
public theorem boundarySevenProperFaceBoundaryN_flagTop_le_of_chart
    (x : boundarySevenSimplicialBoundary.N) {k : ℕ}
    (p : (SSet.sd.obj
      (SSet.stdSimplex.obj (SimplexCategory.mk x.dim))).obj
        (Opposite.op (SimplexCategory.mk k)))
    (F : ComposableArrows BoundarySevenProperFace k)
    (hF : (boundarySevenNondegenerateSubdivisionChart x).app
      (Opposite.op (SimplexCategory.mk k)) p = F) :
    boundarySevenProperFaceBoundaryN
        (boundarySevenProperFaceFlagTop F) ≤ x := by
  rw [← boundarySevenNondegenerateVertexFace_le_iff]
  rw [boundarySevenNondegenerateVertexFace_boundaryN]
  rw [← hF]
  exact boundarySevenNondegenerateSubdivisionChart_top_le_vertexFace x p

/-- A face in one nondegenerate-simplex chart is determined by its ambient proper face. -/
public theorem boundarySevenNondegenerateFaceMap_injective
    (x : boundarySevenSimplicialBoundary.N) :
    Function.Injective (boundarySevenNondegenerateFaceMap x) := by
  intro s t hst
  apply NonemptyFiniteChains.ext
  apply Finset.image_injective
    (boundarySevenNondegenerateAmbientVertexHom_injective x)
  exact congrArg Subtype.val hst

/-- In every degree, the nerve map underlying one explicit chart is injective. -/
public theorem boundarySevenNondegenerateFaceHom_nerve_app_injective
    (x : boundarySevenSimplicialBoundary.N) (n : SimplexCategoryᵒᵖ) :
    Function.Injective
      ((PartOrd.nerveFunctor.map
        (boundarySevenNondegenerateFaceHom x)).app n) := by
  rcases n with ⟨⟨k⟩⟩
  intro F G hFG
  apply ComposableArrows.ext (fun j ↦ ?_) (fun j hj ↦ ?_)
  · apply boundarySevenNondegenerateFaceMap_injective x
    exact congrArg (fun H ↦ H.obj j) hFG
  · apply Subsingleton.elim

/-- Each standard-simplex chart embeds into the proper-face nerve. Thus any failure of the
global comparison to be injective can only come from overlap relations between distinct
charts. -/
public theorem boundarySevenNondegenerateSubdivisionChart_app_injective
    (x : boundarySevenSimplicialBoundary.N) (n : SimplexCategoryᵒᵖ) :
    Function.Injective
      ((boundarySevenNondegenerateSubdivisionChart x).app n) := by
  intro p q hpq
  apply (injective_of_mono
    ((SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk x.dim)).app n))
  apply boundarySevenNondegenerateFaceHom_nerve_app_injective x n
  exact hpq

/-- The canonical largest-face representative of a flag becomes any chosen representative
of that flag after transition to the chosen chart. -/
public theorem boundarySevenProperFaceFlagChartPoint_transition
    (x : boundarySevenSimplicialBoundary.N) {k : ℕ}
    (p : (SSet.sd.obj
      (SSet.stdSimplex.obj (SimplexCategory.mk x.dim))).obj
        (Opposite.op (SimplexCategory.mk k)))
    (F : ComposableArrows BoundarySevenProperFace k)
    (hF : (boundarySevenNondegenerateSubdivisionChart x).app
      (Opposite.op (SimplexCategory.mk k)) p = F) :
    ((boundarySevenSimplicialBoundary.functorN' ⋙ SSet.sd).map
      (homOfLE
        (boundarySevenProperFaceBoundaryN_flagTop_le_of_chart x p F hF))).app
        (Opposite.op (SimplexCategory.mk k))
        (boundarySevenProperFaceFlagChartPoint F) = p := by
  apply boundarySevenNondegenerateSubdivisionChart_app_injective x
    (Opposite.op (SimplexCategory.mk k))
  have hnat := congrArg
    (fun q ↦ q.app (Opposite.op (SimplexCategory.mk k))
      (boundarySevenProperFaceFlagChartPoint F))
    (boundarySevenNondegenerateSubdivisionChart_naturality
      (homOfLE
        (boundarySevenProperFaceBoundaryN_flagTop_le_of_chart x p F hF)))
  exact hnat.trans
    ((boundarySevenProperFaceFlag_chart_covered F).trans hF.symm)

/-- The degreewise cocone obtained by evaluating the explicit subdivision-chart cocone. -/
public noncomputable def boundarySevenProperFaceSubdivisionComponentCocone
    (n : SimplexCategoryᵒᵖ) :
    Cocone
      ((boundarySevenSimplicialBoundary.functorN' ⋙ SSet.sd).flip.obj n) :=
  ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj n).mapCocone
    boundarySevenProperFaceSubdivisionCocone

/-- In each simplicial degree, the proper-face flag set is the quotient of all local chart
flags by the chart-transition relations. -/
public theorem boundarySevenProperFaceSubdivisionComponentCocone_isColimit
    (n : SimplexCategoryᵒᵖ) :
    ((Functor.coconeTypesEquiv
      ((boundarySevenSimplicialBoundary.functorN' ⋙ SSet.sd).flip.obj n)).symm
        (boundarySevenProperFaceSubdivisionComponentCocone n)).IsColimit := by
  let D := (boundarySevenSimplicialBoundary.functorN' ⋙ SSet.sd).flip.obj n
  let c := D.coconeTypesEquiv.symm
    (boundarySevenProperFaceSubdivisionComponentCocone n)
  change c.IsColimit
  refine ⟨⟨?_, ?_⟩⟩
  · intro u v huv
    obtain ⟨x, p, rfl⟩ := D.ιColimitType_jointly_surjective u
    obtain ⟨y, q, rfl⟩ := D.ιColimitType_jointly_surjective v
    change (boundarySevenNondegenerateSubdivisionChart x).app n p =
      (boundarySevenNondegenerateSubdivisionChart y).app n q at huv
    rcases n with ⟨⟨k⟩⟩
    let F : ComposableArrows BoundarySevenProperFace k :=
      (boundarySevenNondegenerateSubdivisionChart x).app
        (Opposite.op (SimplexCategory.mk k)) p
    have hFx : (boundarySevenNondegenerateSubdivisionChart x).app
        (Opposite.op (SimplexCategory.mk k)) p = F := rfl
    have hFy : (boundarySevenNondegenerateSubdivisionChart y).app
        (Opposite.op (SimplexCategory.mk k)) q = F := huv.symm
    let z := boundarySevenProperFaceBoundaryN
      (boundarySevenProperFaceFlagTop F)
    let r := boundarySevenProperFaceFlagChartPoint F
    have hzx : z ≤ x :=
      boundarySevenProperFaceBoundaryN_flagTop_le_of_chart x p F hFx
    have hzy : z ≤ y :=
      boundarySevenProperFaceBoundaryN_flagTop_le_of_chart y q F hFy
    have hrx : D.map (homOfLE hzx) r = p :=
      boundarySevenProperFaceFlagChartPoint_transition x p F hFx
    have hry : D.map (homOfLE hzy) r = q :=
      boundarySevenProperFaceFlagChartPoint_transition y q F hFy
    calc
      D.ιColimitType x p = D.ιColimitType x (D.map (homOfLE hzx) r) :=
        congrArg (D.ιColimitType x) hrx.symm
      _ = D.ιColimitType z r := D.ιColimitType_map (homOfLE hzx) r
      _ = D.ιColimitType y (D.map (homOfLE hzy) r) :=
        (D.ιColimitType_map (homOfLE hzy) r).symm
      _ = D.ιColimitType y q := congrArg (D.ιColimitType y) hry
  · rw [Functor.CoconeTypes.descColimitType_surjective_iff]
    rcases n with ⟨⟨k⟩⟩
    intro F
    change ComposableArrows BoundarySevenProperFace k at F
    refine ⟨boundarySevenProperFaceBoundaryN
      (boundarySevenProperFaceFlagTop F),
      boundarySevenProperFaceFlagChartPoint F, ?_⟩
    exact boundarySevenProperFaceFlag_chart_covered F

/-- The explicit proper-face chart cocone is colimiting. -/
public noncomputable def boundarySevenProperFaceSubdivisionCoconeIsColimit :
    IsColimit boundarySevenProperFaceSubdivisionCocone := by
  apply evaluationJointlyReflectsColimits _
  intro n
  exact Nonempty.some
    ((Types.isColimit_iff_coconeTypesIsColimit
      (boundarySevenProperFaceSubdivisionComponentCocone n)).2
        (boundarySevenProperFaceSubdivisionComponentCocone_isColimit n))

/-- The canonical comparison from the subdivision of `∂Δ[7]` to the nerve of its nonempty
proper faces is an isomorphism. -/
public instance boundarySevenSubdivisionToProperFaceNerve_isIso :
    IsIso boundarySevenSubdivisionToProperFaceNerve := by
  apply (IsColimit.nonempty_isColimit_iff_isIso_desc
    boundarySevenSubdivisionIsColimit).mp
  exact ⟨boundarySevenProperFaceSubdivisionCoconeIsColimit⟩

/-- The canonical simplicial isomorphism from the subdivided boundary to the proper-face
nerve. -/
public noncomputable def boundarySevenSubdivisionProperFaceNerveIso :
    SSet.sd.obj (∂Δ[7] : SSet.{0}) ≅ BoundarySevenProperFaceNerve :=
  asIso boundarySevenSubdivisionToProperFaceNerve

/-- Every degree of the canonical subdivision comparison is surjective. -/
public theorem boundarySevenSubdivisionToProperFaceNerve_app_surjective
    (n : SimplexCategoryᵒᵖ) :
    Function.Surjective (boundarySevenSubdivisionToProperFaceNerve.app n) := by
  rcases n with ⟨⟨k⟩⟩
  intro F
  change ComposableArrows BoundarySevenProperFace k at F
  let x := boundarySevenProperFaceBoundaryN (boundarySevenProperFaceFlagTop F)
  let p := boundarySevenProperFaceFlagChartPoint F
  refine ⟨(SSet.sd.map (SSet.yonedaEquiv.symm x.simplex)).app
    (Opposite.op (SimplexCategory.mk k)) p, ?_⟩
  have hchart := congrArg
    (fun q ↦ q.app (Opposite.op (SimplexCategory.mk k)) p)
    (boundarySevenSubdivisionToProperFaceNerve_chart x)
  exact hchart.trans (boundarySevenProperFaceFlag_chart_covered F)

/-- The canonical comparison onto the proper-face nerve is an epimorphism. -/
public instance boundarySevenSubdivisionToProperFaceNerve_epi :
    Epi boundarySevenSubdivisionToProperFaceNerve := by
  rw [NatTrans.epi_iff_epi_app]
  intro n
  rw [CategoryTheory.epi_iff_surjective]
  exact boundarySevenSubdivisionToProperFaceNerve_app_surjective n

end SphereSixComplex
