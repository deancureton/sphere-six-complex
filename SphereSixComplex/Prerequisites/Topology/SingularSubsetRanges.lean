module

public import SphereSixComplex.Prerequisites.Topology.SingularExcisionRefinement
public import SphereSixComplex.Prerequisites.Topology.SimplicialSubcomplexRelativeExcision
public import SphereSixComplex.Prerequisites.Topology.BinaryOpenCoverCorestriction

@[expose] public section
noncomputable section
open Set CategoryTheory CategoryTheory.Limits AlgebraicTopology
namespace SphereSixComplex

public def singularSubsetRange (X : TopCat) (U : Set X) : (TopCat.toSSet.obj X).Subcomplex :=
  SSet.Subcomplex.range (TopCat.toSSet.map (topologicalSubsetInclusion X U))

public def singularSubsetCorestriction (X : TopCat) (U : Set X) :=
  SSet.Subcomplex.toRange (TopCat.toSSet.map (topologicalSubsetInclusion X U))

public instance singularSubsetCorestriction_isIso (X : TopCat) (U : Set X) :
    IsIso (singularSubsetCorestriction X U) := by
  let : Mono (topologicalSubsetInclusion X U) :=
    (TopCat.mono_iff_injective _).mpr Subtype.val_injective
  change IsIso (SSet.Subcomplex.toRange _)
  infer_instance

public theorem singularSubsetRange_mono (X : TopCat) {U V : Set X} (h : U ⊆ V) :
    singularSubsetRange X U ≤ singularSubsetRange X V := by
  let i : TopCat.of U ⟶ TopCat.of V := TopCat.ofHom ⟨Set.inclusion h, continuous_inclusion h⟩
  have hi : i ≫ topologicalSubsetInclusion X V = topologicalSubsetInclusion X U := rfl
  unfold singularSubsetRange
  rw [← hi, Functor.map_comp]
  exact Subfunctor.range_comp_le _ _

public theorem singularSubsetRange_inter (X : TopCat) (U V : Set X) :
    singularSubsetRange X (U ∩ V) = singularSubsetRange X U ⊓ singularSubsetRange X V := by
  apply le_antisymm (le_inf (singularSubsetRange_mono X inter_subset_left)
    (singularSubsetRange_mono X inter_subset_right))
  intro n x hx
  change (∃ a, (TopCat.toSSet.map (topologicalSubsetInclusion X U)).app n a = x) ∧
    (∃ b, (TopCat.toSSet.map (topologicalSubsetInclusion X V)).app n b = x) at hx
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hx
  change ∃ c, (TopCat.toSSet.map (topologicalSubsetInclusion X (U ∩ V))).app n c = x
  let aMap := (TopCat.of U).toSSetObjEquiv n a
  let bMap := (TopCat.of V).toSSetObjEquiv n b
  let xMap := X.toSSetObjEquiv n x
  have ha' z : xMap z = (aMap z).1 :=
    (congrArg (fun s ↦ X.toSSetObjEquiv n s z) ha).symm
  have hb' z : xMap z = (bMap z).1 :=
    (congrArg (fun s ↦ X.toSSetObjEquiv n s z) hb).symm
  let c : ContinuousMap (stdSimplex ℝ (Fin (n.unop.len + 1))) ↥(U ∩ V) :=
    ⟨fun z ↦ ⟨xMap z, ha' z ▸ (aMap z).2, hb' z ▸ (bMap z).2⟩,
      xMap.continuous.subtype_mk _⟩
  refine ⟨(TopCat.of ↥(U ∩ V)).toSSetObjEquiv n |>.symm c, ?_⟩
  apply (X.toSSetObjEquiv n).injective
  ext z
  rfl

public def singularSubsetCorestrictionChains (X : TopCat) (U : Set X) :=
  BinaryOpenCover.integralSimplicialChains.map (singularSubsetCorestriction X U)

public instance singularSubsetCorestrictionChains_isIso (X : TopCat) (U : Set X) :
    IsIso (singularSubsetCorestrictionChains X U) := by
  dsimp [singularSubsetCorestrictionChains]
  infer_instance

public theorem singularSubsetCorestriction_natural (X : TopCat) {U V : Set X} (h : U ⊆ V) :
    TopCat.toSSet.map (TopCat.ofHom ⟨Set.inclusion h, continuous_inclusion h⟩) ≫
      singularSubsetCorestriction X V =
    singularSubsetCorestriction X U ≫
      SSet.Subcomplex.homOfLE (singularSubsetRange_mono X h) := by
  apply (cancel_mono (singularSubsetRange X V).ι).mp
  simp only [Category.assoc, singularSubsetCorestriction]
  rfl

end SphereSixComplex
