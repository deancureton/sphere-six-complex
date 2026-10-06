module

public import DifferentialGeometry.Topology.Homology.SingularPair

@[expose] public section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex Simplicial

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

variable (X : TopCat.{u})

lemma singSub_le_iff {A : Set X} {S : (TopCat.toSSet.obj X).Subcomplex} :
    singSub X A ≤ S ↔ ∀ (n : SimplexCategoryᵒᵖ) (σ : (TopCat.toSSet.obj X).obj n),
      Set.range (X.toSSetObjEquiv n σ) ⊆ A → σ ∈ S.obj n := by
  constructor
  · intro h n σ hσ
    exact h n ((mem_singSub_iff X A σ).2 hσ)
  · intro h n σ hσ
    exact h n σ ((mem_singSub_iff X A σ).1 hσ)

lemma le_singSub_iff {A : Set X} {S : (TopCat.toSSet.obj X).Subcomplex} :
    S ≤ singSub X A ↔ ∀ (n : SimplexCategoryᵒᵖ) (σ : (TopCat.toSSet.obj X).obj n),
      σ ∈ S.obj n → Set.range (X.toSSetObjEquiv n σ) ⊆ A := by
  constructor
  · intro h n σ hσ
    exact (mem_singSub_iff X A σ).1 (h n hσ)
  · intro h n σ hσ
    exact (mem_singSub_iff X A σ).2 (h n σ hσ)

lemma singSub_mono {A B : Set X} (h : A ⊆ B) : singSub X A ≤ singSub X B := by
  intro n σ hσ
  rw [mem_singSub_iff] at hσ ⊢
  exact hσ.trans h

lemma singSub_inf (A B : Set X) : singSub X (A ∩ B) = singSub X A ⊓ singSub X B := by
  ext n σ
  rw [Subfunctor.min_obj, Set.mem_inter_iff, mem_singSub_iff, mem_singSub_iff, mem_singSub_iff,
    Set.subset_inter_iff]

lemma singSub_univ : singSub X Set.univ = ⊤ := by
  ext n σ
  rw [mem_singSub_iff]
  simp

lemma singSub_eq_top_iff (A : Set X) : singSub X A = ⊤ ↔ A = Set.univ := by
  constructor
  · intro h
    apply Set.eq_univ_of_forall
    intro x
    have hx : (X.toSSetObjEquiv (Opposite.op ⦋0⦌)).symm (ContinuousMap.const _ x) ∈
        (singSub X A).obj (Opposite.op ⦋0⦌) := by
      rw [h]; trivial
    rw [mem_singSub_iff] at hx
    exact hx ⟨Convexity.StdSimplex.single 0, by simp⟩
  · rintro rfl
    exact singSub_univ X

lemma singSub_iInf {ι : Sort*} (A : ι → Set X) :
    singSub X (⋂ i, A i) = ⨅ i, singSub X (A i) := by
  ext n σ
  rw [mem_singSub_iff, Subfunctor.iInf_obj, Set.mem_iInter, Set.subset_iInter_iff]
  simp only [mem_singSub_iff]

lemma singSub_empty : singSub X ∅ = ⊥ := by
  ext n σ
  rw [mem_singSub_iff]
  simp only [Set.subset_empty_iff, Set.range_eq_empty_iff, Subfunctor.bot_obj,
    Set.mem_empty_iff_false, iff_false]
  intro h
  exact h.false (Convexity.StdSimplex.single 0)

lemma singSub_sup_le (A B : Set X) : singSub X A ⊔ singSub X B ≤ singSub X (A ∪ B) :=
  sup_le (singSub_mono X Set.subset_union_left) (singSub_mono X Set.subset_union_right)

def small {ι : Type*} (U : ι → Set X) : (TopCat.toSSet.obj X).Subcomplex :=
  ⨆ i, singSub X (U i)

variable {X}

lemma small_obj {ι : Type*} (U : ι → Set X) (n : SimplexCategoryᵒᵖ) :
    (small X U).obj n = ⋃ i, (singSub X (U i)).obj n := by
  simp [small]

lemma mem_small_iff {ι : Type*} (U : ι → Set X) {n : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj X).obj n) :
    σ ∈ (small X U).obj n ↔ ∃ i, Set.range (X.toSSetObjEquiv n σ) ⊆ U i := by
  rw [small_obj, Set.mem_iUnion]
  simp only [mem_singSub_iff]

lemma singSub_le_small {ι : Type*} (U : ι → Set X) (i : ι) : singSub X (U i) ≤ small X U :=
  le_iSup (fun i ↦ singSub X (U i)) i

lemma small_le_iff {ι : Type*} (U : ι → Set X) (S : (TopCat.toSSet.obj X).Subcomplex) :
    small X U ≤ S ↔ ∀ i, singSub X (U i) ≤ S :=
  iSup_le_iff

lemma small_le_top {ι : Type*} (U : ι → Set X) : small X U ≤ ⊤ := le_top

lemma small_le_singSub_iUnion {ι : Type*} (U : ι → Set X) :
    small X U ≤ singSub X (⋃ i, U i) :=
  (small_le_iff U _).2 fun i ↦ singSub_mono X (Set.subset_iUnion U i)

lemma small_mono {ι : Type*} {U V : ι → Set X} (h : ∀ i, U i ⊆ V i) :
    small X U ≤ small X V :=
  iSup_mono fun i ↦ singSub_mono X (h i)

lemma small_mono_of_forall_exists {ι κ : Type*} {U : ι → Set X} {V : κ → Set X}
    (h : ∀ i, ∃ j, U i ⊆ V j) : small X U ≤ small X V := by
  rw [small_le_iff]
  intro i
  obtain ⟨j, hj⟩ := h i
  exact (singSub_mono X hj).trans (singSub_le_small V j)

lemma small_eq_top_of_mem {ι : Type*} (U : ι → Set X) {i : ι} (hi : U i = Set.univ) :
    small X U = ⊤ :=
  top_le_iff.1 ((singSub_univ X).symm.le.trans (hi ▸ singSub_le_small U i))

lemma small_bool (U : Bool → Set X) :
    small X U = singSub X (U true) ⊔ singSub X (U false) := by
  simp [small, iSup_bool_eq]

lemma small_fin_two (U V : Set X) :
    small X ![U, V] = singSub X U ⊔ singSub X V := by
  refine le_antisymm (iSup_le (Fin.forall_fin_two.2 ⟨le_sup_left, le_sup_right⟩)) ?_
  exact sup_le (le_iSup (fun i ↦ singSub X (![U, V] i)) 0)
    (le_iSup (fun i ↦ singSub X (![U, V] i)) 1)

lemma small_pair (U V : Set X) :
    small X (fun b : Bool ↦ bif b then U else V) = singSub X U ⊔ singSub X V := by
  simp [small_bool]

variable (X) in
abbrev smallι {ι : Type*} (U : ι → Set X) : ((small X U : (TopCat.toSSet.obj X).Subcomplex) :
    SSet.{u}) ⟶ TopCat.toSSet.obj X :=
  (small X U).ι

lemma smallι_app_apply {ι : Type*} (U : ι → Set X) (n : SimplexCategoryᵒᵖ)
    (σ : ((small X U : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).obj n) :
    (smallι X U).app n σ = σ.1 := rfl

lemma mem_of_small {ι : Type*} (U : ι → Set X) (n : SimplexCategoryᵒᵖ)
    (σ : ((small X U : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).obj n) :
    ∃ i, Set.range (X.toSSetObjEquiv n σ.1) ⊆ U i :=
  (mem_small_iff U σ.1).1 σ.2

variable (R : ModuleCat.{u} ℤ)

variable (X) in
abbrev smallChainMap {ι : Type*} (U : ι → Set X) :
    ((small X U : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).chainComplex R ⟶ singularChains R X :=
  SSet.chainComplexMap (small X U).ι R

lemma ι_smallChainMap_f {ι : Type*} (U : ι → Set X) {n : ℕ}
    (σ : ((small X U : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}) _⦋n⦌) :
    ((small X U : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).ιChainComplex σ ≫
      (smallChainMap X R U).f n = (TopCat.toSSet.obj X).ιChainComplex σ.1 :=
  SSet.ι_chainComplexMap_f _ _ (small X U).ι R σ

instance {ι : Type*} (U : ι → Set X) (n : ℕ) : Mono ((smallChainMap X R U).f n) :=
  inferInstanceAs (Mono ((SSet.chainComplexMap (small X U).pair.hom R).f n))

instance {ι : Type*} (U : ι → Set X) : Mono (smallChainMap X R U) :=
  inferInstanceAs (Mono (SSet.chainComplexMap (small X U).pair.hom R))

abbrev subChainMap {S₁ S₂ : (TopCat.toSSet.obj X).Subcomplex} (h : S₁ ≤ S₂) :
    (S₁ : SSet.{u}).chainComplex R ⟶ (S₂ : SSet.{u}).chainComplex R :=
  SSet.chainComplexMap (SSet.Subcomplex.homOfLE h) R

lemma ι_subChainMap_f {S₁ S₂ : (TopCat.toSSet.obj X).Subcomplex} (h : S₁ ≤ S₂) {n : ℕ}
    (σ : (S₁ : SSet.{u}) _⦋n⦌) :
    (S₁ : SSet.{u}).ιChainComplex σ ≫ (subChainMap R h).f n =
      (S₂ : SSet.{u}).ιChainComplex ⟨σ.1, h _ σ.2⟩ := by
  simp [SSet.ι_chainComplexMap_f]

lemma subChainMap_comp_chainComplexMap_ι {S₁ S₂ : (TopCat.toSSet.obj X).Subcomplex}
    (h : S₁ ≤ S₂) :
    subChainMap R h ≫ SSet.chainComplexMap S₂.ι R = SSet.chainComplexMap S₁.ι R := by
  rw [← Functor.map_comp, SSet.Subcomplex.homOfLE_ι]

theorem coverSq (U V : Set X) :
    SSet.Subcomplex.BicartSq (singSub X (U ∩ V)) (singSub X U) (singSub X V)
      (singSub X U ⊔ singSub X V) :=
  ⟨rfl, (singSub_inf X U V).symm⟩

theorem coverSq_isPushout (U V : Set X) :
    IsPushout (SSet.Subcomplex.homOfLE (coverSq U V).le₁₂)
      (SSet.Subcomplex.homOfLE (coverSq U V).le₁₃)
      (SSet.Subcomplex.homOfLE (coverSq U V).le₂₄)
      (SSet.Subcomplex.homOfLE (coverSq U V).le₃₄) :=
  (coverSq U V).isPushout

variable (X) in
def singSubIso (A : Set X) :
    ((singSub X A : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}) ≅
      TopCat.toSSet.obj (TopCat.of A) :=
  (asIso (SSet.Subcomplex.toRange (TopCat.toSSet.map (incl X A)))).symm

@[reassoc (attr := simp)]
lemma singSubIso_inv_ι (A : Set X) :
    (singSubIso X A).inv ≫ (singSub X A).ι = TopCat.toSSet.map (incl X A) := by
  simp [singSubIso]

@[reassoc (attr := simp)]
lemma singSubIso_hom_map_incl (A : Set X) :
    (singSubIso X A).hom ≫ TopCat.toSSet.map (incl X A) = (singSub X A).ι := by
  rw [← singSubIso_inv_ι, Iso.hom_inv_id_assoc]

lemma singSubIso_inv_app_val (A : Set X) (n : SimplexCategoryᵒᵖ)
    (τ : (TopCat.toSSet.obj (TopCat.of A)).obj n) :
    ((singSubIso X A).inv.app n τ).1 = (TopCat.toSSet.map (incl X A)).app n τ := by
  simp [singSubIso]

lemma singSubIso_hom_app (A : Set X) (n : SimplexCategoryᵒᵖ)
    (σ : ((singSub X A : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).obj n) :
    (TopCat.toSSet.map (incl X A)).app n ((singSubIso X A).hom.app n σ) = σ.1 := by
  exact congr_arg (fun f ↦ f.app n σ) (singSubIso_hom_map_incl (X := X) A)

variable (X) in
def singSubPairIso (A : Set X) : (singSub X A).pair ≅ pair X A :=
  MorphismProperty.Arrow.isoMk (singSubIso X A) (Iso.refl _) (by
    change (singSubIso X A).hom ≫ TopCat.toSSet.map (incl X A) = (singSub X A).ι ≫ 𝟙 _
    rw [Category.comp_id]
    exact singSubIso_hom_map_incl A)

@[simp]
lemma singSubPairIso_hom_left (A : Set X) :
    (singSubPairIso X A).hom.left = (singSubIso X A).hom := rfl

@[simp]
lemma singSubPairIso_hom_right (A : Set X) :
    (singSubPairIso X A).hom.right = 𝟙 _ := rfl

@[simp]
lemma singSubPairIso_inv_left (A : Set X) :
    (singSubPairIso X A).inv.left = (singSubIso X A).inv := rfl

@[simp]
lemma singSubPairIso_inv_right (A : Set X) :
    (singSubPairIso X A).inv.right = 𝟙 _ := rfl

variable (X) in
def singSubChainComplexIso (A : Set X) :
    (singSub X A).pair.chainComplex R ≅ (pair X A).chainComplex R :=
  ((SSetPair.chainComplexFunctor.{u} (ModuleCat.{u} ℤ)).obj R).mapIso (singSubPairIso X A)

variable (X) in
def singularSubcomplexRelativeHomologyIso (A : Set X) (n : ℕ) : (singSub X A).pair.homology R n ≅ relativeHomology R X A n :=
  (SSetPair.homologyFunctor.{u} R n).mapIso (singSubPairIso X A)

lemma singularSubcomplexRelativeHomologyIso_hom (A : Set X) (n : ℕ) :
    (singularSubcomplexRelativeHomologyIso X R A n).hom = SSetPair.homologyMap (singSubPairIso X A).hom R n := rfl

lemma chainComplexMap_chainComplexπ {P P' : SSetPair.{u}} (f : P ⟶ P') :
    SSet.chainComplexMap f.right R ≫ P'.chainComplexπ R =
      P.chainComplexπ R ≫ SSetPair.chainComplexMap f R :=
  ((SSetPair.chainComplexFunctorπ.{u} (ModuleCat.{u} ℤ)).app R).naturality f

lemma homologyMap_homologyπ {P P' : SSetPair.{u}} (f : P ⟶ P') (n : ℕ) :
    SSet.homologyMap f.right R n ≫ P'.homologyπ R n =
      P.homologyπ R n ≫ SSetPair.homologyMap f R n := by
  simp only [SSet.homologyMap, SSetPair.homologyπ, SSetPair.homologyMap, ← homologyMap_comp,
    chainComplexMap_chainComplexπ]

lemma homologyπ_singularSubcomplexRelativeHomologyIso_hom (A : Set X) (n : ℕ) :
    (singSub X A).pair.homologyπ R n ≫ (singularSubcomplexRelativeHomologyIso X R A n).hom = relπ R X A n := by
  rw [singularSubcomplexRelativeHomologyIso_hom, ← homologyMap_homologyπ, singSubPairIso_hom_right]
  exact (SSet.homologyMap_id _ R n).symm ▸ Category.id_comp _

section embedding

variable {Y : TopCat.{u}} (f : Y ⟶ X)

lemma mem_range_toSSet_map_iff (hf : _root_.Topology.IsEmbedding f) {n : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj X).obj n) :
    σ ∈ (SSet.Subcomplex.range (TopCat.toSSet.map f)).obj n ↔
      Set.range (X.toSSetObjEquiv n σ) ⊆ Set.range f := by
  constructor
  · rintro ⟨τ, rfl⟩ _ ⟨x, rfl⟩
    exact ⟨Y.toSSetObjEquiv n τ x, rfl⟩
  · intro h
    have : ∀ z, ∃ y, f y = X.toSSetObjEquiv n σ z := fun z ↦ h ⟨z, rfl⟩
    choose g hg using this
    have hg' : ⇑f ∘ g = X.toSSetObjEquiv n σ := funext hg
    have hc : Continuous g := hf.continuous_iff.2 (hg' ▸ (X.toSSetObjEquiv n σ).continuous)
    refine ⟨(Y.toSSetObjEquiv n).symm ⟨g, hc⟩, ?_⟩
    apply (X.toSSetObjEquiv n).injective
    ext z
    exact hg z

lemma range_toSSet_map_eq_singSub (hf : _root_.Topology.IsEmbedding f) :
    SSet.Subcomplex.range (TopCat.toSSet.map f) = singSub X (Set.range f) := by
  ext n σ
  rw [mem_range_toSSet_map_iff f hf, mem_singSub_iff]

end embedding

section restrict

def inclOfLE {A B : Set X} (h : A ⊆ B) : TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom ⟨Set.inclusion h, continuous_inclusion h⟩

@[reassoc (attr := simp)]
lemma inclOfLE_incl {A B : Set X} (h : A ⊆ B) : inclOfLE h ≫ incl X B = incl X A := rfl

lemma inclOfLE_inclOfLE {A B D : Set X} (h : A ⊆ B) (h' : B ⊆ D) :
    inclOfLE h ≫ inclOfLE h' = inclOfLE (h.trans h') := rfl

lemma inclOfLE_refl (A : Set X) : inclOfLE (le_refl A) = 𝟙 _ := rfl

instance {A B : Set X} (h : A ⊆ B) : Mono (inclOfLE h) := mono_of_mono_fac (inclOfLE_incl h)

lemma isEmbedding_incl (A : Set X) : _root_.Topology.IsEmbedding (incl X A) :=
  _root_.Topology.IsEmbedding.subtypeVal

lemma range_incl (A : Set X) : Set.range (incl X A) = A := Subtype.range_val

abbrev inclRestrict (A B : Set X) : TopCat.of (Subtype.val ⁻¹' B : Set (TopCat.of A)) ⟶ X :=
  incl (TopCat.of A) (Subtype.val ⁻¹' B) ≫ incl X A

lemma isEmbedding_inclRestrict (A B : Set X) : _root_.Topology.IsEmbedding (inclRestrict A B) :=
  (isEmbedding_incl A).comp (isEmbedding_incl (X := TopCat.of A) _)

lemma range_inclRestrict (A B : Set X) : Set.range (inclRestrict A B) = A ∩ B := by
  change Set.range (Subtype.val ∘ Subtype.val) = A ∩ B
  rw [Set.range_comp, Subtype.range_val, Subtype.image_preimage_coe]

lemma singSub_inter_le_left (A B : Set X) : singSub X (A ∩ B) ≤ singSub X A :=
  singSub_mono X Set.inter_subset_left

lemma singSub_inter_le_right (A B : Set X) : singSub X (A ∩ B) ≤ singSub X B :=
  singSub_mono X Set.inter_subset_right

lemma singSub_inter_eq_range (A B : Set X) :
    singSub X (A ∩ B) = SSet.Subcomplex.range (TopCat.toSSet.map (inclRestrict A B)) := by
  rw [range_toSSet_map_eq_singSub _ (isEmbedding_inclRestrict A B), range_inclRestrict]

def restrictIso (A B : Set X) :
    TopCat.toSSet.obj (TopCat.of (Subtype.val ⁻¹' B : Set (TopCat.of A))) ≅
      ((singSub X (A ∩ B) : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}) :=
  asIso (SSet.Subcomplex.toRange (TopCat.toSSet.map (inclRestrict A B))) ≪≫
    SSet.Subcomplex.eqToIso (singSub_inter_eq_range A B).symm

@[reassoc (attr := simp)]
lemma restrictIso_hom_ι (A B : Set X) :
    (restrictIso A B).hom ≫ (singSub X (A ∩ B)).ι = TopCat.toSSet.map (inclRestrict A B) := by
  simp only [restrictIso, Iso.trans_hom, asIso_hom, SSet.Subcomplex.eqToIso_hom, Category.assoc,
    SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.toRange_ι]

def restrictPairIso (A B : Set X) :
    pair (TopCat.of A) (Subtype.val ⁻¹' B) ≅
      SSetPair.of (SSet.Subcomplex.homOfLE (singSub_inter_le_left A B)) :=
  MorphismProperty.Arrow.isoMk (restrictIso A B) (singSubIso X A).symm (by
    change (restrictIso A B).hom ≫ SSet.Subcomplex.homOfLE (singSub_inter_le_left A B) =
      TopCat.toSSet.map (incl (TopCat.of A) (Subtype.val ⁻¹' B)) ≫ (singSubIso X A).inv
    rw [← cancel_mono (singSub X A).ι, Category.assoc, Category.assoc,
      SSet.Subcomplex.homOfLE_ι, restrictIso_hom_ι, singSubIso_inv_ι, ← Functor.map_comp])

def relativeHomologyRestrictIso (A B : Set X) (n : ℕ) :
    relativeHomology R (TopCat.of A) (Subtype.val ⁻¹' B) n ≅
      (SSetPair.of (SSet.Subcomplex.homOfLE (singSub_inter_le_left A B))).homology R n :=
  (SSetPair.homologyFunctor.{u} R n).mapIso (restrictPairIso A B)

end restrict

@[reassoc]
lemma singSubIso_hom_map_inclOfLE {A B : Set X} (h : A ⊆ B) :
    (singSubIso X A).hom ≫ TopCat.toSSet.map (inclOfLE h) =
      SSet.Subcomplex.homOfLE (singSub_mono X h) ≫ (singSubIso X B).hom := by
  rw [← cancel_mono (TopCat.toSSet.map (incl X B)), Category.assoc, ← Functor.map_comp,
    inclOfLE_incl, singSubIso_hom_map_incl, Category.assoc, singSubIso_hom_map_incl,
    SSet.Subcomplex.homOfLE_ι]

variable (X) in
def singularSubcomplexHomologyIso (A : Set X) (n : ℕ) :
    ((singSub X A : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).homology R n ≅
      singularHomology R (TopCat.of A) n :=
  (SSet.homologyFunctor.{u} R n).mapIso (singSubIso X A)

lemma singularSubcomplexHomologyIso_hom (A : Set X) (n : ℕ) :
    (singularSubcomplexHomologyIso X R A n).hom = SSet.homologyMap (singSubIso X A).hom R n := rfl

lemma singularSubcomplexHomologyIso_hom_inclMap (A : Set X) (n : ℕ) :
    (singularSubcomplexHomologyIso X R A n).hom ≫ inclMap R X A n = SSet.homologyMap (singSub X A).ι R n :=
  (SSet.homologyMap_comp _ _ _ (singSubIso X A).hom (TopCat.toSSet.map (incl X A)) R n).symm.trans
    (congr_arg (fun f ↦ SSet.homologyMap f R n) (singSubIso_hom_map_incl A))

lemma singularSubcomplexHomologyIso_hom_map_inclOfLE {A B : Set X} (h : A ⊆ B) (n : ℕ) :
    (singularSubcomplexHomologyIso X R A n).hom ≫ homologyMap ((singularChainFunctor R).map (inclOfLE h)) n =
      SSet.homologyMap (SSet.Subcomplex.homOfLE (singSub_mono X h)) R n ≫ (singularSubcomplexHomologyIso X R B n).hom :=
  (SSet.homologyMap_comp _ _ _ (singSubIso X A).hom (TopCat.toSSet.map (inclOfLE h)) R n).symm.trans
    ((congr_arg (fun f ↦ SSet.homologyMap f R n) (singSubIso_hom_map_inclOfLE h)).trans
      (SSet.homologyMap_comp _ _ _ _ _ R n))

lemma map_mem_small {ι : Type*} (U : ι → Set X) {m n : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    {σ : (TopCat.toSSet.obj X).obj n} (hσ : σ ∈ (small X U).obj n) :
    (TopCat.toSSet.obj X).map f σ ∈ (small X U).obj m :=
  (small X U).map f hσ

lemma map_mem_singSub (A : Set X) {m n : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    {σ : (TopCat.toSSet.obj X).obj n} (hσ : σ ∈ (singSub X A).obj n) :
    (TopCat.toSSet.obj X).map f σ ∈ (singSub X A).obj m :=
  (singSub X A).map f hσ

end DifferentialGeometry.Topology.SingularPair
