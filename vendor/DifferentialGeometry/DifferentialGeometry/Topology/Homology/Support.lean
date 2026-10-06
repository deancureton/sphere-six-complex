module

public import DifferentialGeometry.Topology.Homology.SingularSubcomplex
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex

@[expose] public section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex Simplicial

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

lemma exists_finset_sum_ι {ι : Type u} (Z : ι → ModuleCat.{u} ℤ)
    (x : (∐ Z : ModuleCat.{u} ℤ)) :
    ∃ (S : Finset ι) (y : ∀ i, Z i), x = ∑ i ∈ S, Sigma.ι Z i (y i) := by
  classical
  set d := (ModuleCat.coprodIsoDirectSum Z).hom x with hd
  refine ⟨d.support, fun i => d i, ?_⟩
  have h1 : x = (ModuleCat.coprodIsoDirectSum Z).inv d := by
    rw [hd, ← ModuleCat.comp_apply]
    simp
  have h2 := DirectSum.sum_support_of d
  rw [h1]
  conv_lhs => rw [← h2]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← DirectSum.lof_eq_of ℤ, ModuleCat.lof_coprodIsoDirectSum_inv_apply]

variable (R : ModuleCat.{u} ℤ) (X : TopCat.{u})

def simplexSupport (k : ℕ) (S : Finset ((TopCat.toSSet.obj X) _⦋k⦌)) : Set X :=
  ⋃ σ ∈ S, Set.range (X.toSSetObjEquiv _ σ)

lemma isCompact_simplexSupport (k : ℕ) (S : Finset ((TopCat.toSSet.obj X) _⦋k⦌)) :
    IsCompact (simplexSupport X k S) :=
  S.isCompact_biUnion fun σ _ => isCompact_range (X.toSSetObjEquiv _ σ).continuous

lemma mem_singSub_simplexSupport {k : ℕ} {S : Finset ((TopCat.toSSet.obj X) _⦋k⦌)}
    {σ : (TopCat.toSSet.obj X) _⦋k⦌} (hσ : σ ∈ S) :
    σ ∈ (singSub X (simplexSupport X k S)).obj _ :=
  (mem_singSub_iff X _ σ).2 (Set.subset_biUnion_of_mem (u := fun σ => Set.range
    (X.toSSetObjEquiv _ σ)) hσ)

abbrev singSubChainMap (K : Set X) :
    ((singSub X K : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).chainComplex R ⟶ singularChains R X :=
  SSet.chainComplexMap (singSub X K).ι R

instance (K : Set X) (k : ℕ) : Mono ((singSubChainMap R X K).f k) :=
  inferInstanceAs (Mono ((SSet.chainComplexMap (singSub X K).pair.hom R).f k))

instance (K : Set X) : Mono (singSubChainMap R X K) :=
  inferInstanceAs (Mono (SSet.chainComplexMap (singSub X K).pair.hom R))

theorem exists_isCompact_singSubChainMap_f_eq (k : ℕ) (x : (singularChains R X).X k) :
    ∃ K : Set X, IsCompact K ∧ ∃ w, (singSubChainMap R X K).f k w = x := by
  obtain ⟨S, y, hS⟩ :=
    exists_finset_sum_ι (fun _ : (TopCat.toSSet.obj X) _⦋k⦌ => R) x
  refine ⟨simplexSupport X k S, isCompact_simplexSupport X k S, ?_⟩
  have hmem :
      x ∈ LinearMap.range ((singSubChainMap R X (simplexSupport X k S)).f k).hom := by
    rw [hS]
    refine Submodule.sum_mem _ fun σ hσ => ?_
    refine ⟨SSet.ιChainComplex (R := R) (X := ((singSub X (simplexSupport X k S) :
      (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}))
      ⟨σ, mem_singSub_simplexSupport X hσ⟩ (y σ), ?_⟩
    exact ConcreteCategory.congr_hom
      (SSet.ι_chainComplexMap_f _ _ (singSub X (simplexSupport X k S)).ι R
        ⟨σ, mem_singSub_simplexSupport X hσ⟩) (y σ)
  obtain ⟨w, hw⟩ := hmem
  exact ⟨w, hw⟩

lemma homologyπ_mem_range_homologyMap {L M : ChainComplex (ModuleCat.{u} ℤ) ℕ} (φ : L ⟶ M)
    [∀ j, Mono (φ.f j)] (k : ℕ) (z : M.cycles k) (w : L.X k)
    (hw : φ.f k w = M.iCycles k z) :
    M.homologyπ k z ∈ Set.range (homologyMap φ k) := by
  have hdw : L.d k ((ComplexShape.down ℕ).next k) w = 0 := by
    apply (ModuleCat.mono_iff_injective (φ.f _)).1 inferInstance
    rw [← ModuleCat.comp_apply, ← φ.comm, ModuleCat.comp_apply, hw, ← ModuleCat.comp_apply,
      iCycles_d, map_zero]
    simp
  have hw' : L.iCycles k (L.cyclesMk w _ rfl hdw) = w := L.i_cyclesMk w _ rfl hdw
  have hcyc : cyclesMap φ k (L.cyclesMk w _ rfl hdw) = z := by
    apply (ModuleCat.mono_iff_injective (M.iCycles k)).1 inferInstance
    rw [← ModuleCat.comp_apply, cyclesMap_i, ModuleCat.comp_apply, hw', hw]
  refine ⟨L.homologyπ k (L.cyclesMk w _ rfl hdw), ?_⟩
  rw [← ModuleCat.comp_apply, homologyπ_naturality, ModuleCat.comp_apply, hcyc]

theorem exists_isCompact_mem_range_inclMap (k : ℕ) (c : singularHomology R X k) :
    ∃ K : Set X, IsCompact K ∧ c ∈ Set.range (inclMap R X K k) := by
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective ((singularChains R X).homologyπ k)).1 inferInstance c
  obtain ⟨K, hK, w, hw⟩ :=
    exists_isCompact_singSubChainMap_f_eq R X k ((singularChains R X).iCycles k z)
  obtain ⟨a, ha⟩ := homologyπ_mem_range_homologyMap (singSubChainMap R X K) k z w hw
  refine ⟨K, hK, (singularSubcomplexHomologyIso X R K k).hom a, ?_⟩
  rw [← ModuleCat.comp_apply, singularSubcomplexHomologyIso_hom_inclMap]
  exact ha.trans hz

lemma inclMap_inclOfLE {A B : Set X} (h : A ⊆ B) (n : ℕ) :
    homologyMap ((singularChainFunctor R).map (inclOfLE h)) n ≫ inclMap R X B n = inclMap R X A n := by
  change homologyMap ((singularChainFunctor R).map (inclOfLE h)) n ≫ homologyMap ((singularChainFunctor R).map (incl X B)) n =
    homologyMap ((singularChainFunctor R).map (incl X A)) n
  rw [← homologyMap_comp, ← Functor.map_comp, inclOfLE_incl]

lemma range_inclMap_mono {A B : Set X} (h : A ⊆ B) (n : ℕ) :
    Set.range (inclMap R X A n) ⊆ Set.range (inclMap R X B n) := by
  rintro _ ⟨a, rfl⟩
  refine ⟨homologyMap ((singularChainFunctor R).map (inclOfLE h)) n a, ?_⟩
  rw [← inclMap_inclOfLE R X h n]
  rfl

theorem exists_isCompact_superset_mem_range_inclMap (k : ℕ) (c : singularHomology R X k) {K₀ : Set X}
    (hK₀ : IsCompact K₀) :
    ∃ K : Set X, IsCompact K ∧ K₀ ⊆ K ∧ c ∈ Set.range (inclMap R X K k) := by
  obtain ⟨K, hK, hc⟩ := exists_isCompact_mem_range_inclMap R X k c
  exact ⟨K₀ ∪ K, hK₀.union hK, Set.subset_union_left,
    range_inclMap_mono R X Set.subset_union_right k hc⟩

instance hasDimensionLT_zero_pair_empty_left : (pair X ∅).left.HasDimensionLT 0 := by
  rw [← SSet.notNonempty_iff_hasDimensionLT_zero]
  rintro ⟨σ⟩
  exact ((TopCat.of (∅ : Set X)).toSSetObjEquiv _ σ (Classical.arbitrary _)).2

instance isIso_relπ_empty (k : ℕ) : IsIso (relπ R X ∅ k) :=
  inferInstanceAs (IsIso ((pair X ∅).homologyπ R k))

def relativeHomologyEmptyIso (k : ℕ) : relativeHomology R X ∅ k ≅ singularHomology R X k := (asIso (relπ R X ∅ k)).symm

@[simp]
lemma relativeHomologyEmptyIso_inv (k : ℕ) : (relativeHomologyEmptyIso R X k).inv = relπ R X ∅ k := rfl

@[reassoc (attr := simp)]
lemma relπ_relativeHomologyEmptyIso_hom (k : ℕ) : relπ R X ∅ k ≫ (relativeHomologyEmptyIso R X k).hom = 𝟙 _ := by
  rw [← relativeHomologyEmptyIso_inv, Iso.inv_hom_id]

@[reassoc (attr := simp)]
lemma relativeHomologyEmptyIso_hom_relπ (k : ℕ) : (relativeHomologyEmptyIso R X k).hom ≫ relπ R X ∅ k = 𝟙 _ := by
  rw [← relativeHomologyEmptyIso_inv, Iso.hom_inv_id]

lemma incl_univ_eq : incl X Set.univ = (TopCat.isoOfHomeo (Homeomorph.Set.univ X)).hom := rfl

instance isIso_incl_univ : IsIso (incl X Set.univ) := by
  rw [incl_univ_eq]
  infer_instance

instance isIso_pair_univ_hom : IsIso (pair X Set.univ).hom :=
  inferInstanceAs (IsIso (TopCat.toSSet.map (incl X Set.univ)))

theorem isZero_relativeHomology_univ (k : ℕ) : IsZero (relativeHomology R X Set.univ k) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) k).map_isZero
    (SSetPair.isZero_chainComplex (pair X Set.univ) R)

end DifferentialGeometry.Topology.SingularPair
