module

public import SphereSixComplex.Topology.BoundarySevenSubdivisionGeneratorComparison
public import Mathlib.AlgebraicTopology.SimplicialSet.NonsingularColimit

/-!
# The proper-face nerve and subdivision of the seven-simplex boundary

This file constructs the comparison map from Mathlib's left-Kan-extension subdivision of
`∂Δ[7]` to the explicit nerve of nonempty proper faces.  Its defining identity says that,
after the literal inclusion of proper faces, it is exactly subdivision of the boundary
inclusion (transported through the representable subdivision isomorphism).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits PartialOrder Simplicial

namespace SphereSixComplex

public abbrev boundarySevenSimplicialBoundary : SSet.{0} :=
  (SSet.boundary 7 : SSet.{0})

/-- The ambient order map represented by a nondegenerate simplex of `∂Δ[7]`. -/
public def boundarySevenNondegenerateAmbientOrderHom
    (x : boundarySevenSimplicialBoundary.N) :
    Fin (x.dim + 1) →o Fin 8 :=
  SSet.stdSimplex.asOrderHom x.simplex.1

/-- The ambient vertex map of a nondegenerate boundary simplex, with the universe lift used by
`SimplexCategory.sd` removed. -/
public def boundarySevenNondegenerateAmbientVertexHom
    (x : boundarySevenSimplicialBoundary.N) :
    PartOrd.of (ULift.{0} (Fin (x.dim + 1))) ⟶
      PartOrd.of (Fin 8) :=
  PartOrd.ofHom
    { toFun := fun i ↦ boundarySevenNondegenerateAmbientOrderHom x i.down
      monotone' := fun _ _ h ↦
        (boundarySevenNondegenerateAmbientOrderHom x).monotone h }

/-- Map a nonempty collection of vertices of a nondegenerate boundary simplex to the
corresponding proper face of the ambient seven-simplex. -/
public noncomputable def boundarySevenNondegenerateFaceMap
    (x : boundarySevenSimplicialBoundary.N)
    (s : NonemptyFiniteChains (ULift.{0} (Fin (x.dim + 1)))) :
    BoundarySevenProperFace := by
  let t : Finset (Fin 8) := s.finset.image
    (boundarySevenNondegenerateAmbientVertexHom x).hom
  refine ⟨t, Finset.image_nonempty.mpr s.nonempty, ?_⟩
  intro ht
  apply x.simplex.2
  intro i
  have hi : i ∈ t := by rw [ht]; simp
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hi
  exact ⟨j.down, hj⟩

@[simp]
public theorem boundarySevenNondegenerateFaceMap_val
    (x : boundarySevenSimplicialBoundary.N)
    (s : NonemptyFiniteChains (ULift.{0} (Fin (x.dim + 1)))) :
    (boundarySevenNondegenerateFaceMap x s).1 =
      s.finset.image (boundarySevenNondegenerateAmbientVertexHom x).hom :=
  rfl

public theorem boundarySevenNondegenerateFaceMap_val_eq_chainMap
    (x : boundarySevenSimplicialBoundary.N)
    (s : NonemptyFiniteChains (ULift.{0} (Fin (x.dim + 1)))) :
    (boundarySevenNondegenerateFaceMap x s).1 =
      (NonemptyFiniteChains.map s
        (boundarySevenNondegenerateAmbientVertexHom x).hom).finset := by
  rw [boundarySevenNondegenerateFaceMap_val]
  apply Finset.ext
  intro a
  constructor
  · intro ha
    obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp ha
    rw [NonemptyFiniteChains.mem_map_iff]
    exact ⟨i, hi, hia⟩
  · intro ha
    rw [NonemptyFiniteChains.mem_map_iff] at ha
    obtain ⟨i, hi, hia⟩ := ha
    exact Finset.mem_image.mpr ⟨i, hi, hia⟩

/-- The monotone map from the face poset of a nondegenerate boundary simplex to the ambient
proper-face poset. -/
public noncomputable def boundarySevenNondegenerateFaceHom
    (x : boundarySevenSimplicialBoundary.N) :
    PartOrd.nonemptyFiniteChainsFunctor.obj
        (SimplexCategory.toPartOrd.obj (SimplexCategory.mk x.dim)) ⟶
      PartOrd.of BoundarySevenProperFace :=
  PartOrd.ofHom
    { toFun := boundarySevenNondegenerateFaceMap x
      monotone' := by
        intro s t hst
        change NonemptyFiniteChains (ULift.{0} (Fin (x.dim + 1))) at s t
        change s.finset.image (boundarySevenNondegenerateAmbientVertexHom x).hom ⊆
          t.finset.image (boundarySevenNondegenerateAmbientVertexHom x).hom
        exact Finset.image_mono _ hst }

/-- The explicit subdivision chart of a nondegenerate simplex of the boundary, with values in
the global proper-face nerve. -/
public noncomputable def boundarySevenNondegenerateSubdivisionChart
    (x : boundarySevenSimplicialBoundary.N) :
    SSet.sd.obj (SSet.stdSimplex.obj (SimplexCategory.mk x.dim)) ⟶
      BoundarySevenProperFaceNerve :=
  SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk x.dim) ≫
    PartOrd.nerveFunctor.map (boundarySevenNondegenerateFaceHom x)

public theorem boundarySevenNondegenerateAmbientOrderHom_monoOfLE
    {x y : boundarySevenSimplicialBoundary.N} (h : x ≤ y)
    (i : Fin (x.dim + 1)) :
    boundarySevenNondegenerateAmbientOrderHom x i =
      boundarySevenNondegenerateAmbientOrderHom y
        ((SSet.N.monoOfLE h).toOrderHom i) := by
  have hmap := SSet.N.map_monoOfLE h
  change x.simplex.1 i =
    y.simplex.1 ((SSet.N.monoOfLE h).toOrderHom i)
  have hi := congrArg (fun z ↦ z.1 i) hmap
  exact hi.symm

public theorem boundarySevenNondegenerateAmbientVertexHom_comp_monoOfLE
    {x y : boundarySevenSimplicialBoundary.N} (h : x ≤ y) :
    SimplexCategory.toPartOrd.map (SSet.N.monoOfLE h) ≫
        boundarySevenNondegenerateAmbientVertexHom y =
      boundarySevenNondegenerateAmbientVertexHom x := by
  apply PartOrd.ext
  intro i
  change boundarySevenNondegenerateAmbientOrderHom y
      ((SSet.N.monoOfLE h).toOrderHom i.down) =
    boundarySevenNondegenerateAmbientOrderHom x i.down
  exact (boundarySevenNondegenerateAmbientOrderHom_monoOfLE h i.down).symm

public theorem boundarySevenNondegenerateFaceHom_comp_monoOfLE
    {x y : boundarySevenSimplicialBoundary.N} (h : x ≤ y) :
    (PartOrd.nonemptyFiniteChainsFunctor.map
          (SimplexCategory.toPartOrd.map
          (SSet.N.monoOfLE h))) ≫
      boundarySevenNondegenerateFaceHom y =
      boundarySevenNondegenerateFaceHom x := by
  apply PartOrd.ext
  intro s
  change NonemptyFiniteChains (ULift.{0} (Fin (x.dim + 1))) at s
  apply Subtype.ext
  have hvert :
      PartOrd.nonemptyFiniteChainsFunctor.map
          (SimplexCategory.toPartOrd.map (SSet.N.monoOfLE h)) ≫
        PartOrd.nonemptyFiniteChainsFunctor.map
          (boundarySevenNondegenerateAmbientVertexHom y) =
      PartOrd.nonemptyFiniteChainsFunctor.map
        (boundarySevenNondegenerateAmbientVertexHom x) := by
    calc
      _ = PartOrd.nonemptyFiniteChainsFunctor.map
          (SimplexCategory.toPartOrd.map (SSet.N.monoOfLE h) ≫
            boundarySevenNondegenerateAmbientVertexHom y) :=
        (PartOrd.nonemptyFiniteChainsFunctor.map_comp _ _).symm
      _ = _ := congrArg PartOrd.nonemptyFiniteChainsFunctor.map
        (boundarySevenNondegenerateAmbientVertexHom_comp_monoOfLE h)
  have happ := congrArg (fun q ↦ q.hom s) hvert
  let t : NonemptyFiniteChains (ULift.{0} (Fin (y.dim + 1))) :=
    (PartOrd.nonemptyFiniteChainsFunctor.map
      (SimplexCategory.toPartOrd.map (SSet.N.monoOfLE h))).hom s
  have happ' :
      NonemptyFiniteChains.map t
          (boundarySevenNondegenerateAmbientVertexHom y).hom =
        NonemptyFiniteChains.map s
          (boundarySevenNondegenerateAmbientVertexHom x).hom := by
    exact happ
  change (boundarySevenNondegenerateFaceMap y t).1 =
    (boundarySevenNondegenerateFaceMap x s).1
  calc
    _ = (NonemptyFiniteChains.map t
        (boundarySevenNondegenerateAmbientVertexHom y).hom).finset :=
      boundarySevenNondegenerateFaceMap_val_eq_chainMap y t
    _ = (NonemptyFiniteChains.map s
        (boundarySevenNondegenerateAmbientVertexHom x).hom).finset :=
      congrArg NonemptyFiniteChains.finset happ'
    _ = _ := (boundarySevenNondegenerateFaceMap_val_eq_chainMap x s).symm

public theorem boundarySevenNondegenerateSubdivisionChart_naturality
    {x y : boundarySevenSimplicialBoundary.N} (f : x ⟶ y) :
    (boundarySevenSimplicialBoundary.functorN' ⋙ SSet.sd).map f ≫
        boundarySevenNondegenerateSubdivisionChart y =
      boundarySevenNondegenerateSubdivisionChart x := by
  let g := SSet.N.monoOfLE (leOfHom f)
  have hsd := SSet.stdSimplex.sdIso.hom.naturality g
  have hsd' :
      SSet.sd.map (SSet.stdSimplex.map g) ≫
          SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk y.dim) =
        SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk x.dim) ≫
          SimplexCategory.sd.map g := by
    exact hsd
  change SSet.sd.map (SSet.stdSimplex.map g) ≫
      (SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk y.dim) ≫
        PartOrd.nerveFunctor.map (boundarySevenNondegenerateFaceHom y)) = _
  calc
    _ = (SSet.sd.map (SSet.stdSimplex.map g) ≫
          SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk y.dim)) ≫
        PartOrd.nerveFunctor.map (boundarySevenNondegenerateFaceHom y) :=
      (Category.assoc _ _ _).symm
    _ = (SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk x.dim) ≫
          SimplexCategory.sd.map g) ≫
        PartOrd.nerveFunctor.map (boundarySevenNondegenerateFaceHom y) :=
      congrArg (fun z ↦ z ≫
        PartOrd.nerveFunctor.map (boundarySevenNondegenerateFaceHom y)) hsd'
    _ = SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk x.dim) ≫
        (SimplexCategory.sd.map g ≫
          PartOrd.nerveFunctor.map (boundarySevenNondegenerateFaceHom y)) :=
      Category.assoc _ _ _
    _ = boundarySevenNondegenerateSubdivisionChart x := by
      have hface :
          PartOrd.nerveFunctor.map
              (PartOrd.nonemptyFiniteChainsFunctor.map
                (SimplexCategory.toPartOrd.map g)) ≫
            PartOrd.nerveFunctor.map (boundarySevenNondegenerateFaceHom y) =
          PartOrd.nerveFunctor.map (boundarySevenNondegenerateFaceHom x) := by
        rw [← Functor.map_comp,
          boundarySevenNondegenerateFaceHom_comp_monoOfLE (leOfHom f)]
      change SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk x.dim) ≫
          (PartOrd.nerveFunctor.map
              (PartOrd.nonemptyFiniteChainsFunctor.map
                (SimplexCategory.toPartOrd.map g)) ≫
            PartOrd.nerveFunctor.map (boundarySevenNondegenerateFaceHom y)) =
        SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk x.dim) ≫
          PartOrd.nerveFunctor.map (boundarySevenNondegenerateFaceHom x)
      exact congrArg
        (fun z ↦ SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk x.dim) ≫ z)
        hface

/-- The chart cocone from the subdivided nondegenerate simplices of `∂Δ[7]` to the explicit
proper-face nerve. -/
public noncomputable def boundarySevenProperFaceSubdivisionCocone :
    Cocone (boundarySevenSimplicialBoundary.functorN' ⋙ SSet.sd) where
  pt := BoundarySevenProperFaceNerve
  ι :=
    { app := boundarySevenNondegenerateSubdivisionChart
      naturality := fun _ _ f ↦ boundarySevenNondegenerateSubdivisionChart_naturality f }

/-- Subdivision preserves the standard-simplex colimit presentation of the nonsingular
boundary. -/
public noncomputable def boundarySevenSubdivisionIsColimit :
    IsColimit (SSet.sd.mapCocone boundarySevenSimplicialBoundary.coconeN') :=
  isColimitOfPreserves SSet.sd boundarySevenSimplicialBoundary.isColimitCoconeN'

/-- The canonical comparison from Mathlib's left-Kan-extension subdivision of `∂Δ[7]` to the
explicit nerve of nonempty proper faces. -/
public noncomputable def boundarySevenSubdivisionToProperFaceNerve :
    SSet.sd.obj (∂Δ[7] : SSet.{0}) ⟶ BoundarySevenProperFaceNerve :=
  boundarySevenSubdivisionIsColimit.desc boundarySevenProperFaceSubdivisionCocone

/-- On every nondegenerate boundary simplex, the global comparison is the explicit map that
sends a nonempty set of local vertices to its ambient proper face. -/
public theorem boundarySevenSubdivisionToProperFaceNerve_chart
    (x : boundarySevenSimplicialBoundary.N) :
    SSet.sd.map (SSet.yonedaEquiv.symm x.simplex) ≫
        boundarySevenSubdivisionToProperFaceNerve =
      boundarySevenNondegenerateSubdivisionChart x := by
  exact boundarySevenSubdivisionIsColimit.fac
    boundarySevenProperFaceSubdivisionCocone x

/-- The simplex-category morphism represented by a nondegenerate simplex of the boundary after
forgetting that its image is proper. -/
public def boundarySevenNondegenerateAmbientSimplexHom
    (x : boundarySevenSimplicialBoundary.N) :
    SimplexCategory.mk x.dim ⟶ SimplexCategory.mk 7 :=
  SimplexCategory.Hom.mk (boundarySevenNondegenerateAmbientOrderHom x)

/-- The underlying standard-simplex map of a boundary simplex is its ambient monotone vertex
map. -/
public theorem boundarySevenNondegenerateSimplex_comp_boundaryInclusion
    (x : boundarySevenSimplicialBoundary.N) :
    SSet.yonedaEquiv.symm x.simplex ≫ (SSet.boundary 7).ι =
      SSet.stdSimplex.map (boundarySevenNondegenerateAmbientSimplexHom x) := by
  apply SSet.yonedaEquiv.injective
  rfl

/-- Universe-lift the ambient vertices, matching the vertex convention in
`SimplexCategory.sd`. -/
public def boundarySevenAmbientVertexULiftHom :
    PartOrd.of (Fin 8) ⟶ PartOrd.of (ULift.{0} (Fin 8)) :=
  PartOrd.ofHom
    { toFun := ULift.up
      monotone' := fun _ _ h ↦ h }

public theorem boundarySevenAmbientVertexHom_comp_uLift
    (x : boundarySevenSimplicialBoundary.N) :
    boundarySevenNondegenerateAmbientVertexHom x ≫
        boundarySevenAmbientVertexULiftHom =
      SimplexCategory.toPartOrd.map
        (boundarySevenNondegenerateAmbientSimplexHom x) := by
  apply PartOrd.ext
  intro i
  rfl

public theorem boundarySevenFinsetImage_uLift_eq_chainMap
    (s : NonemptyFiniteChains (Fin 8)) :
    s.finset.image ULift.up =
      (NonemptyFiniteChains.map s boundarySevenAmbientVertexULiftHom.hom).finset := by
  apply Finset.ext
  intro a
  constructor
  · intro ha
    obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp ha
    rw [NonemptyFiniteChains.mem_map_iff]
    exact ⟨i, hi, hia⟩
  · intro ha
    rw [NonemptyFiniteChains.mem_map_iff] at ha
    obtain ⟨i, hi, hia⟩ := ha
    exact Finset.mem_image.mpr ⟨i, hi, hia⟩

/-- Including the proper faces produced by one boundary simplex is the usual map of full
nonempty-face posets induced by its ambient vertex map. -/
public theorem boundarySevenNondegenerateFaceHom_comp_inclusion
    (x : boundarySevenSimplicialBoundary.N) :
    boundarySevenNondegenerateFaceHom x ≫
        boundarySevenProperFaceInclusionHom =
      PartOrd.nonemptyFiniteChainsFunctor.map
        (SimplexCategory.toPartOrd.map
          (boundarySevenNondegenerateAmbientSimplexHom x)) := by
  apply PartOrd.ext
  intro s
  change NonemptyFiniteChains (ULift.{0} (Fin (x.dim + 1))) at s
  let t : NonemptyFiniteChains (Fin 8) :=
    NonemptyFiniteChains.map s
      (boundarySevenNondegenerateAmbientVertexHom x).hom
  let u : NonemptyFiniteChains (ULift.{0} (Fin 8)) :=
    NonemptyFiniteChains.map t boundarySevenAmbientVertexULiftHom.hom
  let v : NonemptyFiniteChains (ULift.{0} (Fin 8)) :=
    NonemptyFiniteChains.map s
      (SimplexCategory.toPartOrd.map
        (boundarySevenNondegenerateAmbientSimplexHom x)).hom
  have hchain :
      PartOrd.nonemptyFiniteChainsFunctor.map
          (boundarySevenNondegenerateAmbientVertexHom x) ≫
        PartOrd.nonemptyFiniteChainsFunctor.map
          boundarySevenAmbientVertexULiftHom =
      PartOrd.nonemptyFiniteChainsFunctor.map
        (SimplexCategory.toPartOrd.map
          (boundarySevenNondegenerateAmbientSimplexHom x)) := by
    calc
      _ = PartOrd.nonemptyFiniteChainsFunctor.map
          (boundarySevenNondegenerateAmbientVertexHom x ≫
            boundarySevenAmbientVertexULiftHom) :=
        (PartOrd.nonemptyFiniteChainsFunctor.map_comp _ _).symm
      _ = _ := congrArg PartOrd.nonemptyFiniteChainsFunctor.map
        (boundarySevenAmbientVertexHom_comp_uLift x)
  have huv : u = v := by
    exact congrArg (fun q ↦ q.hom s) hchain
  apply NonemptyFiniteChains.ext
  change (boundarySevenNondegenerateFaceMap x s).1.image ULift.up = v.finset
  calc
    _ = t.finset.image ULift.up := by
      rw [boundarySevenNondegenerateFaceMap_val_eq_chainMap]
    _ = u.finset := boundarySevenFinsetImage_uLift_eq_chainMap t
    _ = v.finset := congrArg NonemptyFiniteChains.finset huv

/-- Each chart comparison followed by the literal proper-face inclusion is exactly the
representable subdivision of its ambient simplex map. -/
public theorem boundarySevenNondegenerateSubdivisionChart_comp_inclusion
    (x : boundarySevenSimplicialBoundary.N) :
    boundarySevenNondegenerateSubdivisionChart x ≫
        boundarySevenProperFaceNerveInclusion =
      SSet.sd.map
          (SSet.stdSimplex.map
            (boundarySevenNondegenerateAmbientSimplexHom x)) ≫
        SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk 7) := by
  have hface := congrArg PartOrd.nerveFunctor.map
    (boundarySevenNondegenerateFaceHom_comp_inclusion x)
  have hface' :
      PartOrd.nerveFunctor.map (boundarySevenNondegenerateFaceHom x) ≫
          PartOrd.nerveFunctor.map boundarySevenProperFaceInclusionHom =
        SimplexCategory.sd.map
          (boundarySevenNondegenerateAmbientSimplexHom x) := by
    calc
      _ = PartOrd.nerveFunctor.map
          (boundarySevenNondegenerateFaceHom x ≫
            boundarySevenProperFaceInclusionHom) :=
        (PartOrd.nerveFunctor.map_comp _ _).symm
      _ = _ := hface
  have hsd := SSet.stdSimplex.sdIso.hom.naturality
    (boundarySevenNondegenerateAmbientSimplexHom x)
  have hsd' :
      SSet.sd.map
          (SSet.stdSimplex.map
            (boundarySevenNondegenerateAmbientSimplexHom x)) ≫
        SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk 7) =
      SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk x.dim) ≫
        SimplexCategory.sd.map
          (boundarySevenNondegenerateAmbientSimplexHom x) := by
    exact hsd
  change (SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk x.dim) ≫
      PartOrd.nerveFunctor.map (boundarySevenNondegenerateFaceHom x)) ≫
        PartOrd.nerveFunctor.map boundarySevenProperFaceInclusionHom = _
  have hwhisker :
      SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk x.dim) ≫
          (PartOrd.nerveFunctor.map (boundarySevenNondegenerateFaceHom x) ≫
            PartOrd.nerveFunctor.map boundarySevenProperFaceInclusionHom) =
        SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk x.dim) ≫
          SimplexCategory.sd.map
            (boundarySevenNondegenerateAmbientSimplexHom x) :=
    congrArg
      (fun z : SimplexCategory.sd.obj (SimplexCategory.mk x.dim) ⟶
          SimplexCategory.sd.obj (SimplexCategory.mk 7) ↦
        SSet.stdSimplex.sdIso.hom.app
          (SimplexCategory.mk x.dim) ≫ z) hface'
  exact (Category.assoc _ _ _).trans (hwhisker.trans hsd'.symm)

/-- The canonical comparison is a literal factorization of subdivided boundary inclusion
through the proper-face nerve.  This is the precise natural identity missing from the older
proper-face API. -/
public theorem boundarySevenSubdivisionToProperFaceNerve_comp_inclusion :
    boundarySevenSubdivisionToProperFaceNerve ≫
        boundarySevenProperFaceNerveInclusion =
      SSet.sd.map (SSet.boundary.{0} 7).ι ≫
        SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk 7) := by
  apply boundarySevenSubdivisionIsColimit.hom_ext
  intro x
  calc
    SSet.sd.map (SSet.yonedaEquiv.symm x.simplex) ≫
          (boundarySevenSubdivisionToProperFaceNerve ≫
            boundarySevenProperFaceNerveInclusion) =
        (SSet.sd.map (SSet.yonedaEquiv.symm x.simplex) ≫
          boundarySevenSubdivisionToProperFaceNerve) ≫
            boundarySevenProperFaceNerveInclusion :=
      (Category.assoc _ _ _).symm
    _ = boundarySevenNondegenerateSubdivisionChart x ≫
        boundarySevenProperFaceNerveInclusion := by
      rw [boundarySevenSubdivisionToProperFaceNerve_chart]
    _ = SSet.sd.map
          (SSet.stdSimplex.map
            (boundarySevenNondegenerateAmbientSimplexHom x)) ≫
        SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk 7) :=
      boundarySevenNondegenerateSubdivisionChart_comp_inclusion x
    _ = SSet.sd.map
          (SSet.yonedaEquiv.symm x.simplex ≫ (SSet.boundary 7).ι) ≫
        SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk 7) := by
      rw [boundarySevenNondegenerateSimplex_comp_boundaryInclusion]
    _ = (SSet.sd.map (SSet.yonedaEquiv.symm x.simplex) ≫
          SSet.sd.map (SSet.boundary 7).ι) ≫
        SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk 7) := by
      rw [Functor.map_comp]
    _ = SSet.sd.map (SSet.yonedaEquiv.symm x.simplex) ≫
        (SSet.sd.map (SSet.boundary 7).ι ≫
          SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk 7)) :=
      Category.assoc _ _ _

/-- Chain-level form of the subdivision factorization, for arbitrary coefficients. -/
public theorem boundarySevenSubdivisionToProperFaceNerve_chainMap_comp_inclusion
    (R : AddCommGrpCat) :
    SSet.chainComplexMap boundarySevenSubdivisionToProperFaceNerve R ≫
        SSet.chainComplexMap boundarySevenProperFaceNerveInclusion R =
      SSet.chainComplexMap (SSet.sd.map (SSet.boundary.{0} 7).ι) R ≫
        SSet.chainComplexMap
          (SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk 7)) R := by
  let F := (SSet.chainComplexFunctor AddCommGrpCat).obj R
  calc
    F.map boundarySevenSubdivisionToProperFaceNerve ≫
          F.map boundarySevenProperFaceNerveInclusion =
        F.map (boundarySevenSubdivisionToProperFaceNerve ≫
          boundarySevenProperFaceNerveInclusion) :=
      (F.map_comp _ _).symm
    _ = F.map (SSet.sd.map (SSet.boundary 7).ι ≫
        SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk 7)) :=
      congrArg F.map boundarySevenSubdivisionToProperFaceNerve_comp_inclusion
    _ = F.map (SSet.sd.map (SSet.boundary 7).ι) ≫
        F.map (SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk 7)) :=
      F.map_comp _ _

/-- The intrinsic fundamental chain of `∂Δ[7]`, after canonical barycentric subdivision and the
new comparison, becomes the explicit subdivided boundary chain after the literal proper-face
inclusion. -/
public theorem boundarySevenOriginalFundamentalChain_subdivisionToProperFace_comp_inclusion :
    ((boundarySevenOriginalFundamentalChain ≫
          (barycentricSubdivisionChainMapCanonical (∂Δ[7] : SSet.{0})).f 6) ≫
        (SSet.chainComplexMap boundarySevenSubdivisionToProperFaceNerve
          (AddCommGrpCat.of ℤ)).f 6) ≫
      (SSet.chainComplexMap boundarySevenProperFaceNerveInclusion
        (AddCommGrpCat.of ℤ)).f 6 =
      subdividedSevenBoundaryFundamentalChain := by
  have hfactor := congrArg (fun k ↦ k.f 6)
    (boundarySevenSubdivisionToProperFaceNerve_chainMap_comp_inclusion
      (AddCommGrpCat.of ℤ))
  let c := boundarySevenOriginalFundamentalChain ≫
    (barycentricSubdivisionChainMapCanonical (∂Δ[7] : SSet.{0})).f 6
  calc
    (c ≫ (SSet.chainComplexMap boundarySevenSubdivisionToProperFaceNerve
          (AddCommGrpCat.of ℤ)).f 6) ≫
        (SSet.chainComplexMap boundarySevenProperFaceNerveInclusion
          (AddCommGrpCat.of ℤ)).f 6 =
      c ≫ ((SSet.chainComplexMap boundarySevenSubdivisionToProperFaceNerve
          (AddCommGrpCat.of ℤ)).f 6 ≫
        (SSet.chainComplexMap boundarySevenProperFaceNerveInclusion
          (AddCommGrpCat.of ℤ)).f 6) := Category.assoc _ _ _
    _ = c ≫ ((SSet.chainComplexMap
          (SSet.sd.map (SSet.boundary 7).ι) (AddCommGrpCat.of ℤ)).f 6 ≫
        (SSet.chainComplexMap
          (SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk 7))
          (AddCommGrpCat.of ℤ)).f 6) :=
      congrArg (fun z ↦ c ≫ z) hfactor
    _ = (c ≫ (SSet.chainComplexMap
          (SSet.sd.map (SSet.boundary 7).ι) (AddCommGrpCat.of ℤ)).f 6) ≫
        (SSet.chainComplexMap
          (SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk 7))
          (AddCommGrpCat.of ℤ)).f 6 := (Category.assoc _ _ _).symm
    _ = (subdividedSevenBoundaryFundamentalChain ≫
          (SSet.chainComplexMap
            (SSet.stdSimplex.sdIso.inv.app (SimplexCategory.mk 7))
            (AddCommGrpCat.of ℤ)).f 6) ≫
        (SSet.chainComplexMap
          (SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk 7))
          (AddCommGrpCat.of ℤ)).f 6 := by
      rw [boundarySevenOriginalFundamentalChain_barycentricSubdivision_comp_inclusion]
    _ = subdividedSevenBoundaryFundamentalChain := by
      rw [Category.assoc]
      let F := (SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
      have hcancel :
          F.map (SSet.stdSimplex.sdIso.inv.app (SimplexCategory.mk 7)) ≫
              F.map (SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk 7)) =
            𝟙 _ := by
        rw [← F.map_comp]
        simp
      have hcancel' := congrArg (fun k ↦ k.f 6) hcancel
      change
        (F.map (SSet.stdSimplex.sdIso.inv.app (SimplexCategory.mk 7))).f 6 ≫
            (F.map (SSet.stdSimplex.sdIso.hom.app (SimplexCategory.mk 7))).f 6 =
          𝟙 _ at hcancel'
      rw [hcancel', Category.comp_id]

end SphereSixComplex
