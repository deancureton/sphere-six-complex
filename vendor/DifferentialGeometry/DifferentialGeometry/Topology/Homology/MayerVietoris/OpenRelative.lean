module

public import DifferentialGeometry.Topology.Homology.MayerVietoris.Relative
public import DifferentialGeometry.Topology.Homology.Relative.SingularExcision
public import DifferentialGeometry.Topology.Homology.Naturality

@[expose] public section

open CategoryTheory Limits HomologicalComplex

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

variable (R : ModuleCat.{u} ℤ) {X : TopCat.{u}}

lemma image_sup {K L : SSet.{u}} (A B : K.Subcomplex) (f : K ⟶ L) :
    (A ⊔ B).image f = A.image f ⊔ B.image f :=
  le_antisymm ((SSet.Subcomplex.image_le_iff _ _ _).2 (sup_le
      ((SSet.Subcomplex.image_le_iff _ _ _).1 le_sup_left)
      ((SSet.Subcomplex.image_le_iff _ _ _).1 le_sup_right)))
    (sup_le (SSet.Subcomplex.image_monotone f le_sup_left)
      (SSet.Subcomplex.image_monotone f le_sup_right))

lemma image_singSub_incl {A W : Set X} (h : A ⊆ W) :
    (singSub (TopCat.of W) (Subtype.val ⁻¹' A)).image (TopCat.toSSet.map (incl X W)) =
      singSub X A := by
  rw [singSub, ← SSet.Subcomplex.range_comp, ← Functor.map_comp]
  change SSet.Subcomplex.range (TopCat.toSSet.map (inclRestrict W A)) = _
  rw [← singSub_inter_eq_range, Set.inter_eq_right.2 h]

variable (P Q : Set X)

abbrev supSub : (TopCat.toSSet.obj (TopCat.of (P ∪ Q : Set X))).Subcomplex :=
  singSub (TopCat.of (P ∪ Q : Set X)) (Subtype.val ⁻¹' P) ⊔
    singSub (TopCat.of (P ∪ Q : Set X)) (Subtype.val ⁻¹' Q)

lemma range_supSub_ι_comp :
    SSet.Subcomplex.range ((supSub P Q).ι ≫ TopCat.toSSet.map (incl X (P ∪ Q))) =
      singSub X P ⊔ singSub X Q := by
  rw [← SSet.Subcomplex.image_eq_range, image_sup,
    image_singSub_incl Set.subset_union_left, image_singSub_incl Set.subset_union_right]

instance mono_supSub_ι_comp : Mono ((supSub P Q).ι ≫ TopCat.toSSet.map (incl X (P ∪ Q))) :=
  mono_comp _ _

def supTransportIso :
    ((supSub P Q : (TopCat.toSSet.obj (TopCat.of (P ∪ Q : Set X))).Subcomplex) : SSet.{u}) ≅
      ((singSub X P ⊔ singSub X Q : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}) :=
  asIso (SSet.Subcomplex.toRange ((supSub P Q).ι ≫ TopCat.toSSet.map (incl X (P ∪ Q)))) ≪≫
    SSet.Subcomplex.eqToIso (range_supSub_ι_comp P Q)

@[reassoc (attr := simp)]
lemma supTransportIso_hom_ι :
    (supTransportIso P Q).hom ≫ (singSub X P ⊔ singSub X Q).ι =
      (supSub P Q).ι ≫ TopCat.toSSet.map (incl X (P ∪ Q)) := by
  simp only [supTransportIso, Iso.trans_hom, asIso_hom, SSet.Subcomplex.eqToIso_hom,
    Category.assoc, SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.toRange_ι]

lemma supTransportIso_hom_homOfLE_singSubIso_hom :
    (supTransportIso P Q).hom ≫ SSet.Subcomplex.homOfLE (singSub_sup_le X P Q) ≫
      (singSubIso X (P ∪ Q)).hom = (supSub P Q).ι := by
  rw [← cancel_mono (TopCat.toSSet.map (incl X (P ∪ Q))), Category.assoc, Category.assoc,
    singSubIso_hom_map_incl, SSet.Subcomplex.homOfLE_ι, supTransportIso_hom_ι]

variable {P Q}

lemma interior_preimage_union_eq_univ (hP : IsOpen P) (hQ : IsOpen Q) :
    interior (Subtype.val ⁻¹' P : Set (TopCat.of (P ∪ Q : Set X))) ∪
      interior (Subtype.val ⁻¹' Q : Set (TopCat.of (P ∪ Q : Set X))) = Set.univ := by
  rw [(hP.preimage continuous_subtype_val).interior_eq,
    (hQ.preimage continuous_subtype_val).interior_eq]
  exact Set.eq_univ_of_forall fun y ↦ y.2

theorem quasiIso_subChainMap_sup_of_isOpen (hP : IsOpen P) (hQ : IsOpen Q) :
    QuasiIso (subChainMap R (singSub_sup_le X P Q)) := by
  have h1 : QuasiIso (SSet.chainComplexMap (supSub P Q).ι R) :=
    quasiIso_sup_ι R (X := TopCat.of (P ∪ Q : Set X)) (interior_preimage_union_eq_univ hP hQ)
  have h2 : SSet.chainComplexMap (supTransportIso P Q).hom R ≫
      (subChainMap R (singSub_sup_le X P Q) ≫
        SSet.chainComplexMap (singSubIso X (P ∪ Q)).hom R) =
      SSet.chainComplexMap (supSub P Q).ι R := by
    rw [subChainMap, ← Functor.map_comp, ← Functor.map_comp,
      supTransportIso_hom_homOfLE_singSubIso_hom]
  rw [← h2] at h1
  have h3 : QuasiIso (SSet.chainComplexMap (supTransportIso P Q).hom R) :=
    quasiIso_of_isIso
      (((SSet.chainComplexFunctor.{u} (ModuleCat.{u} ℤ)).obj R).map (supTransportIso P Q).hom)
  have h4 : QuasiIso (SSet.chainComplexMap (singSubIso X (P ∪ Q)).hom R) :=
    quasiIso_of_isIso
      (((SSet.chainComplexFunctor.{u} (ModuleCat.{u} ℤ)).obj R).map (singSubIso X (P ∪ Q)).hom)
  rw [quasiIso_iff_comp_left, quasiIso_iff_comp_right] at h1
  exact h1

variable (P Q)

theorem isIso_quotHomologyMap_sup (hP : IsOpen P) (hQ : IsOpen Q) (k : ℕ) :
    IsIso (quotHomologyMap R (singSub_sup_le X P Q) k) :=
  isIso_homologyMap_of_quasiIso R (pairOfLE (singSub_sup_le X P Q))
    (by
      rw [pairOfLE_left]
      exact quasiIso_subChainMap_sup_of_isOpen R hP hQ)
    (by
      rw [chainComplexMap_pairOfLE_right]
      exact quasiIso_of_isIso (𝟙 _)) k

variable {P Q} in
def relativeHomologySupIso (hP : IsOpen P) (hQ : IsOpen Q) (k : ℕ) :
    (singSub X P ⊔ singSub X Q).pair.homology R k ≅ relativeHomology R X (P ∪ Q) k :=
  @asIso _ _ _ _ _ (isIso_quotHomologyMap_sup R P Q hP hQ k) ≪≫ singularSubcomplexRelativeHomologyIso X R (P ∪ Q) k

variable {P Q} in
lemma relativeHomologySupIso_hom (hP : IsOpen P) (hQ : IsOpen Q) (k : ℕ) :
    (relativeHomologySupIso R hP hQ k).hom =
      quotHomologyMap R (singSub_sup_le X P Q) k ≫ (singularSubcomplexRelativeHomologyIso X R (P ∪ Q) k).hom := rfl

def relativeHomologyInfIso (k : ℕ) :
    (singSub X P ⊓ singSub X Q).pair.homology R k ≅ relativeHomology R X (P ∩ Q) k where
  hom := quotHomologyMap R (singSub_inf X P Q).symm.le k ≫ (singularSubcomplexRelativeHomologyIso X R (P ∩ Q) k).hom
  inv := (singularSubcomplexRelativeHomologyIso X R (P ∩ Q) k).inv ≫ quotHomologyMap R (singSub_inf X P Q).le k
  hom_inv_id := by
    rw [Category.assoc, Iso.hom_inv_id_assoc, quotHomologyMap_comp, quotHomologyMap_refl]
  inv_hom_id := by
    rw [Category.assoc, ← Category.assoc (quotHomologyMap R _ k), quotHomologyMap_comp,
      quotHomologyMap_refl, Category.id_comp, Iso.inv_hom_id]

lemma relativeHomologyInfIso_hom (k : ℕ) :
    (relativeHomologyInfIso R P Q k).hom =
      quotHomologyMap R (singSub_inf X P Q).symm.le k ≫ (singularSubcomplexRelativeHomologyIso X R (P ∩ Q) k).hom := rfl

variable {P Q}

lemma id_mapsTo {A B : Set X} (h : A ⊆ B) : Set.MapsTo (𝟙 X) A B := h

lemma id_comp_mapsTo {A B : Set X} (h : A ⊆ B) : Set.MapsTo (𝟙 X ≫ 𝟙 X) A B := h

lemma restr_id_eq_inclOfLE {A B : Set X} (h : A ⊆ B) :
    restr (𝟙 X) (id_mapsTo h) = inclOfLE h := rfl

lemma singSubPairIso_hom_pairMap_id {A B : Set X} (h : A ⊆ B) :
    (singSubPairIso X A).hom ≫ pairMap (𝟙 X) (id_mapsTo h) =
      pairOfLE (singSub_mono X h) ≫ (singSubPairIso X B).hom := by
  refine MorphismProperty.Comma.Hom.ext' (CommaMorphism.ext ?_ ?_)
  · change (singSubIso X A).hom ≫ TopCat.toSSet.map (restr (𝟙 X) h) =
      SSet.Subcomplex.homOfLE (singSub_mono X h) ≫ (singSubIso X B).hom
    rw [restr_id_eq_inclOfLE]
    exact singSubIso_hom_map_inclOfLE h
  · change 𝟙 _ ≫ TopCat.toSSet.map (𝟙 X) = 𝟙 _ ≫ 𝟙 _
    rw [CategoryTheory.Functor.map_id]

lemma singularSubcomplexRelativeHomologyIso_hom_relativeHomologyMap_id {A B : Set X} (h : A ⊆ B) (k : ℕ) :
    (singularSubcomplexRelativeHomologyIso X R A k).hom ≫ relativeHomologyMap R (𝟙 X) (id_mapsTo h) k =
      quotHomologyMap R (singSub_mono X h) k ≫ (singularSubcomplexRelativeHomologyIso X R B k).hom := by
  rw [singularSubcomplexRelativeHomologyIso_hom, singularSubcomplexRelativeHomologyIso_hom]
  change SSetPair.homologyMap _ R k ≫ SSetPair.homologyMap _ R k =
    SSetPair.homologyMap _ R k ≫ SSetPair.homologyMap _ R k
  rw [← SSetPair.homologyMap_comp, ← SSetPair.homologyMap_comp,
    singSubPairIso_hom_pairMap_id h]

variable (P Q)

abbrev relMVLift (k : ℕ) : relativeHomology R X (P ∩ Q) k ⟶ relativeHomology R X P k ⊞ relativeHomology R X Q k :=
  biprod.lift (relativeHomologyMap R (𝟙 X) (id_mapsTo (Set.inter_subset_left : P ∩ Q ⊆ P)) k)
    (-(relativeHomologyMap R (𝟙 X) (id_mapsTo (Set.inter_subset_right : P ∩ Q ⊆ Q)) k))

abbrev relMVDesc (k : ℕ) : relativeHomology R X P k ⊞ relativeHomology R X Q k ⟶ relativeHomology R X (P ∪ Q) k :=
  biprod.desc (relativeHomologyMap R (𝟙 X) (id_mapsTo (Set.subset_union_left : P ⊆ P ∪ Q)) k)
    (relativeHomologyMap R (𝟙 X) (id_mapsTo (Set.subset_union_right : Q ⊆ P ∪ Q)) k)

abbrev biprodRelativeHomologyIso (k : ℕ) :
    ((singSub X P).pair.homology R k ⊞ (singSub X Q).pair.homology R k) ≅
      (relativeHomology R X P k ⊞ relativeHomology R X Q k) :=
  biprod.mapIso (singularSubcomplexRelativeHomologyIso X R P k) (singularSubcomplexRelativeHomologyIso X R Q k)

variable {P Q}

def relMVδ (hP : IsOpen P) (hQ : IsOpen Q) (k : ℕ) :
    relativeHomology R X (P ∪ Q) (k + 1) ⟶ relativeHomology R X (P ∩ Q) k :=
  (relativeHomologySupIso R hP hQ (k + 1)).inv ≫ quotMVδ (singSub X P) (singSub X Q) R k ≫
    (relativeHomologyInfIso R P Q k).hom

lemma relativeHomologySupIso_hom_relMVδ (hP : IsOpen P) (hQ : IsOpen Q) (k : ℕ) :
    (relativeHomologySupIso R hP hQ (k + 1)).hom ≫ relMVδ R hP hQ k =
      quotMVδ (singSub X P) (singSub X Q) R k ≫ (relativeHomologyInfIso R P Q k).hom := by
  rw [relMVδ, Iso.hom_inv_id_assoc]

variable (P Q) in
lemma relativeHomologyInfIso_hom_relMVLift (k : ℕ) :
    (relativeHomologyInfIso R P Q k).hom ≫ relMVLift R P Q k =
      quotMVLift (singSub X P) (singSub X Q) R k ≫ (biprodRelativeHomologyIso R P Q k).hom := by
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.lift_fst, Category.assoc, biprod.mapIso_hom, biprod.map_fst,
      ← Category.assoc, quotMVLift_fst, relativeHomologyInfIso_hom, Category.assoc,
      singularSubcomplexRelativeHomologyIso_hom_relativeHomologyMap_id R Set.inter_subset_left, ← Category.assoc, quotHomologyMap_comp]
  · rw [Category.assoc, biprod.lift_snd, Category.assoc, biprod.mapIso_hom, biprod.map_snd,
      ← Category.assoc, quotMVLift_snd, relativeHomologyInfIso_hom, Category.assoc, Preadditive.comp_neg,
      singularSubcomplexRelativeHomologyIso_hom_relativeHomologyMap_id R Set.inter_subset_right, Preadditive.comp_neg,
      Preadditive.neg_comp, ← Category.assoc, quotHomologyMap_comp]

lemma biprodRelativeHomologyIso_hom_relMVDesc (hP : IsOpen P) (hQ : IsOpen Q) (k : ℕ) :
    (biprodRelativeHomologyIso R P Q k).hom ≫ relMVDesc R P Q k =
      quotMVDesc (singSub X P) (singSub X Q) R k ≫ (relativeHomologySupIso R hP hQ k).hom := by
  apply biprod.hom_ext'
  · rw [biprod.mapIso_hom, biprod.inl_map_assoc, biprod.inl_desc, ← Category.assoc,
      inl_quotMVDesc, relativeHomologySupIso_hom, singularSubcomplexRelativeHomologyIso_hom_relativeHomologyMap_id R Set.subset_union_left,
      ← Category.assoc, quotHomologyMap_comp]
  · rw [biprod.mapIso_hom, biprod.inr_map_assoc, biprod.inr_desc, ← Category.assoc,
      inr_quotMVDesc, relativeHomologySupIso_hom, singularSubcomplexRelativeHomologyIso_hom_relativeHomologyMap_id R Set.subset_union_right,
      ← Category.assoc, quotHomologyMap_comp]

@[reassoc (attr := simp)]
lemma relMVδ_relMVLift (hP : IsOpen P) (hQ : IsOpen Q) (k : ℕ) :
    relMVδ R hP hQ k ≫ relMVLift R P Q k = 0 := by
  rw [← cancel_epi (relativeHomologySupIso R hP hQ (k + 1)).hom, ← Category.assoc, relativeHomologySupIso_hom_relMVδ,
    Category.assoc, relativeHomologyInfIso_hom_relMVLift, quotMVδ_quotMVLift_assoc, zero_comp, comp_zero]

variable (P Q) in
@[reassoc]
lemma relMVLift_relMVDesc (k : ℕ) : relMVLift R P Q k ≫ relMVDesc R P Q k = 0 := by
  simp

@[reassoc (attr := simp)]
lemma relMVDesc_relMVδ (hP : IsOpen P) (hQ : IsOpen Q) (k : ℕ) :
    relMVDesc R P Q (k + 1) ≫ relMVδ R hP hQ k = 0 := by
  rw [← cancel_epi (biprodRelativeHomologyIso R P Q (k + 1)).hom, ← Category.assoc,
    biprodRelativeHomologyIso_hom_relMVDesc R hP hQ (k + 1), Category.assoc, relativeHomologySupIso_hom_relMVδ,
    quotMVDesc_quotMVδ_assoc, zero_comp, comp_zero]

theorem relMV_exact₁ (hP : IsOpen P) (hQ : IsOpen Q) (k : ℕ) :
    (ShortComplex.mk (relMVδ R hP hQ k) (relMVLift R P Q k)
      (relMVδ_relMVLift R hP hQ k)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (quotMV_exact₁' (singSub X P) (singSub X Q) R k)
  exact ShortComplex.isoMk (relativeHomologySupIso R hP hQ (k + 1)) (relativeHomologyInfIso R P Q k)
    (biprodRelativeHomologyIso R P Q k) (relativeHomologySupIso_hom_relMVδ R hP hQ k) (relativeHomologyInfIso_hom_relMVLift R P Q k)

theorem relMV_exact₂ (hP : IsOpen P) (hQ : IsOpen Q) (k : ℕ) :
    (ShortComplex.mk (relMVLift R P Q k) (relMVDesc R P Q k)
      (relMVLift_relMVDesc R P Q k)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (quotMV_exact₂' (singSub X P) (singSub X Q) R k)
  exact ShortComplex.isoMk (relativeHomologyInfIso R P Q k) (biprodRelativeHomologyIso R P Q k)
    (relativeHomologySupIso R hP hQ k) (relativeHomologyInfIso_hom_relMVLift R P Q k)
    (biprodRelativeHomologyIso_hom_relMVDesc R hP hQ k)

theorem relMV_exact₃ (hP : IsOpen P) (hQ : IsOpen Q) (k : ℕ) :
    (ShortComplex.mk (relMVDesc R P Q (k + 1)) (relMVδ R hP hQ k)
      (relMVDesc_relMVδ R hP hQ k)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (quotMV_exact₃' (singSub X P) (singSub X Q) R k)
  exact ShortComplex.isoMk (biprodRelativeHomologyIso R P Q (k + 1)) (relativeHomologySupIso R hP hQ (k + 1))
    (relativeHomologyInfIso R P Q k) (biprodRelativeHomologyIso_hom_relMVDesc R hP hQ (k + 1))
    (relativeHomologySupIso_hom_relMVδ R hP hQ k)

theorem mono_relMVLift (hP : IsOpen P) (hQ : IsOpen Q) (k : ℕ)
    (h : IsZero (relativeHomology R X (P ∪ Q) (k + 1))) : Mono (relMVLift R P Q k) :=
  (relMV_exact₁ R hP hQ k).mono_g (h.eq_zero_of_src _)

lemma biprod_eq_zero_of_fst_snd {M N : ModuleCat.{u} ℤ} (z : ↑(M ⊞ N))
    (h₁ : (biprod.fst : M ⊞ N ⟶ M) z = 0) (h₂ : (biprod.snd : M ⊞ N ⟶ N) z = 0) : z = 0 := by
  have h := congrArg (fun f : M ⊞ N ⟶ M ⊞ N ↦ f z) (biprod.total (X := M) (Y := N))
  simp only [ModuleCat.id_apply] at h
  rw [← h]
  change (biprod.fst ≫ biprod.inl : M ⊞ N ⟶ M ⊞ N) z +
    (biprod.snd ≫ biprod.inr : M ⊞ N ⟶ M ⊞ N) z = 0
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, h₁, h₂, map_zero, map_zero, add_zero]

theorem relMV_injective (hP : IsOpen P) (hQ : IsOpen Q) (k : ℕ)
    (h : IsZero (relativeHomology R X (P ∪ Q) (k + 1))) (a : relativeHomology R X (P ∩ Q) k)
    (ha : relativeHomologyMap R (𝟙 X) (id_mapsTo (Set.inter_subset_left : P ∩ Q ⊆ P)) k a = 0)
    (hb : relativeHomologyMap R (𝟙 X) (id_mapsTo (Set.inter_subset_right : P ∩ Q ⊆ Q)) k a = 0) :
    a = 0 := by
  have hmono := mono_relMVLift R hP hQ k h
  apply (ModuleCat.mono_iff_injective (relMVLift R P Q k)).1 hmono
  rw [map_zero]
  apply biprod_eq_zero_of_fst_snd
  · rw [← ModuleCat.comp_apply, biprod.lift_fst, ha]
  · rw [← ModuleCat.comp_apply, biprod.lift_snd]
    change -(relativeHomologyMap R (𝟙 X) (id_mapsTo (Set.inter_subset_right : P ∩ Q ⊆ Q)) k a) = 0
    rw [hb, neg_zero]

theorem isZero_relativeHomology_inter_of_isZero (hP : IsOpen P) (hQ : IsOpen Q) (k : ℕ)
    (h₁ : IsZero (relativeHomology R X (P ∪ Q) (k + 1))) (h₂ : IsZero (relativeHomology R X P k))
    (h₃ : IsZero (relativeHomology R X Q k)) : IsZero (relativeHomology R X (P ∩ Q) k) := by
  have hP' : relativeHomologyMap R (𝟙 X) (id_mapsTo (Set.inter_subset_left : P ∩ Q ⊆ P)) k = 0 :=
    h₂.eq_zero_of_tgt _
  have hQ' : relativeHomologyMap R (𝟙 X) (id_mapsTo (Set.inter_subset_right : P ∩ Q ⊆ Q)) k = 0 :=
    h₃.eq_zero_of_tgt _
  have : Subsingleton (relativeHomology R X (P ∩ Q) k) := by
    refine ⟨fun a b ↦ ?_⟩
    rw [relMV_injective R hP hQ k h₁ a (by rw [hP']; rfl) (by rw [hQ']; rfl),
      relMV_injective R hP hQ k h₁ b (by rw [hP']; rfl) (by rw [hQ']; rfl)]
  exact ModuleCat.isZero_of_subsingleton _

end DifferentialGeometry.Topology.SingularPair
