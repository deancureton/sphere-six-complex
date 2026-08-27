module

public import SphereSixComplex.Topology.OrderedCechNormalization
public import SphereSixComplex.Topology.SectionSevenPaperCoverIdentification

/-!
# The normalized ordered Čech total of the Section 7 star cover

The local intersection chain models of the four-piece star cover are a contravariant diagram on
nonempty subsets of `Fin 4`, so the generic ordered Čech normalization applies.  This file
identifies the existing ordered Čech bicomplex `localLerayCechBicomplex` with the generic
bicomplex over all tuples and records the resulting homotopy equivalence between
`localLerayCechTotal` and the normalized total, whose summands are indexed by strictly increasing
tuples of cover indices, i.e. by nonempty supports.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Simplicial SphereSixComplex.OrderedCechTuple

namespace SphereSixComplex

namespace SectionSevenStarIntersectionChainModels

variable {A : FourPieceStarGluingData} (L : SectionSevenStarIntersectionChainModels A)

/-- The local models of the star cover as a generic diagram on nonempty subsets of `Fin 4`. -/
public def toSupportChainModels : SupportChainModels (Fin 4) where
  model := L.model
  face := L.face
  face_id := L.face_id
  face_comp := L.face_comp

/-- In each simplicial degree, the ordered Čech coproduct of the local models is the generic
coproduct over all tuples. -/
public def localCechObjectIso (n : ℕ) :
    L.localLerayCechBicomplex.X n ≅ (L.toSupportChainModels.cechComplex TupleClass.all).X n where
  hom := Sigma.desc fun a : CechTuple (Opposite.op ⦋n⦌) ↦
    Sigma.ι (fun b : {b : Fin (n + 1) → Fin 4 // TupleClass.all.mem n b} ↦
      L.toSupportChainModels.model (tupleSupport b.1)) ⟨a, trivial⟩
  inv := Sigma.desc fun b : {b : Fin (n + 1) → Fin 4 // TupleClass.all.mem n b} ↦
    Sigma.ι (fun a : CechTuple (Opposite.op ⦋n⦌) ↦ L.model a.intersectionIndex) b.1
  hom_inv_id := by
    dsimp only [localLerayCechBicomplex, alternatingFaceMapComplex_obj_X,
      localCechChainSimplicialObject, SupportChainModels.cechComplex_X]
    apply Sigma.hom_ext
    intro a
    exact (Sigma.ι_desc_assoc _ _ _).trans ((Sigma.ι_desc _ _).trans (Category.comp_id _).symm)
  inv_hom_id := by
    dsimp only [localLerayCechBicomplex, alternatingFaceMapComplex_obj_X,
      localCechChainSimplicialObject, SupportChainModels.cechComplex_X]
    apply Sigma.hom_ext
    rintro ⟨b, hb⟩
    exact (Sigma.ι_desc_assoc _ _ _).trans ((Sigma.ι_desc _ _).trans (Category.comp_id _).symm)

/-- The ordered Čech bicomplex of the local models is the generic bicomplex over all tuples: the
alternating face maps of the Čech nerve are the realizations of the formal face maps. -/
public def localLerayCechBicomplexIso :
    L.localLerayCechBicomplex ≅ L.toSupportChainModels.cechComplex TupleClass.all :=
  HomologicalComplex.Hom.isoOfComponents L.localCechObjectIso fun i j hij ↦ by
    obtain rfl : i = j + 1 := hij.symm
    rw [SupportChainModels.cechComplex_d]
    unfold localLerayCechBicomplex
    rw [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD]
    dsimp only [SimplicialObject.δ, localCechChainSimplicialObject, localCechObjectIso,
      localLerayCechBicomplex, alternatingFaceMapComplex_obj_X, SupportChainModels.cechComplex_X]
    apply Sigma.hom_ext
    intro a
    erw [Sigma.ι_desc_assoc, SupportChainModels.ι_realize, boundary_single, map_sum,
      Preadditive.sum_comp, Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    erw [mul_one, ← Finsupp.smul_single_one (Fin.removeNth i a) ((-1 : ℤ) ^ (i : ℕ)), map_smul,
      SupportChainModels.realizeAux_single, SupportChainModels.ιOrZero_of_mem _ trivial,
      Preadditive.zsmul_comp, Preadditive.comp_zsmul, Sigma.ι_desc_assoc, Category.assoc,
      Sigma.ι_desc]
    unfold SupportChainModels.faceOrZero
    erw [dite_eq_left ((tupleSupport_subset_iff a (Fin.removeNth i a)).2 (Set.range_comp_subset_range _ _))]
    rfl

/-- The ordered Čech total of the local models is the generic total over all tuples. -/
public def localLerayCechTotalIso :
    L.localLerayCechTotal ≅ L.toSupportChainModels.cechTotal TupleClass.all :=
  HomologicalComplex₂.total.mapIso L.localLerayCechBicomplexIso (ComplexShape.down ℕ)

/-- The normalized ordered Čech total complex of the local models: one summand per strictly
increasing tuple of cover indices. -/
public abbrev normalizedOrderedCechTotal : ChainComplex AddCommGrpCat ℕ :=
  L.toSupportChainModels.cechTotal TupleClass.strictMono

/-- The ordered Čech total of the local models is homotopy equivalent to its normalization. -/
public def normalizedOrderedCechHomotopyEquiv :
    HomotopyEquiv L.localLerayCechTotal L.normalizedOrderedCechTotal :=
  (HomotopyEquiv.ofIso L.localLerayCechTotalIso).trans
    L.toSupportChainModels.totalNormalizationHomotopyEquiv

/-- The normalized bicomplex vanishes in simplicial degrees at least four. -/
public theorem isZero_normalized_cechObject {n : ℕ} (hn : 4 ≤ n) :
    IsZero ((L.toSupportChainModels.cechComplex TupleClass.strictMono).X n) :=
  L.toSupportChainModels.isZero_cechObject_strictMono (by simpa using hn)

end SectionSevenStarIntersectionChainModels

end SphereSixComplex
