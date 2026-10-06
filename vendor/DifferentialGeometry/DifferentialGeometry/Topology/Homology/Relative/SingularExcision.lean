module

public import DifferentialGeometry.Topology.Homology.SingularSubcomplex
public import DifferentialGeometry.Topology.Homology.MayerVietoris.ShortExact
public import DifferentialGeometry.Topology.Homology.Subdivision.SmallSimplices
public import DifferentialGeometry.Topology.Homology.MayerVietoris.MayerVietoris
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

@[expose] public section

open CategoryTheory Limits HomologicalComplex

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

variable (R : ModuleCat.{u} ℤ)

section PairQuasiIso

variable {P P' : SSetPair.{u}} (φ : P ⟶ P')

def pairShortComplexMap : P.chainComplexShortComplex R ⟶ P'.chainComplexShortComplex R :=
  ShortComplex.homMk (SSet.chainComplexMap φ.left R) (SSet.chainComplexMap φ.right R)
    (SSetPair.chainComplexMap φ R)
    (by
      dsimp only [SSetPair.chainComplexShortComplex]
      rw [← Functor.map_comp, ← Functor.map_comp, MorphismProperty.Arrow.w])
    (chainComplexMap_right_chainComplexπ R φ)

@[simp] lemma pairShortComplexMap_τ₁ :
    (pairShortComplexMap R φ).τ₁ = SSet.chainComplexMap φ.left R := rfl

@[simp] lemma pairShortComplexMap_τ₂ :
    (pairShortComplexMap R φ).τ₂ = SSet.chainComplexMap φ.right R := rfl

@[simp] lemma pairShortComplexMap_τ₃ :
    (pairShortComplexMap R φ).τ₃ = SSetPair.chainComplexMap φ R := rfl

theorem quasiIso_chainComplexMap_of_quasiIso
    (h₁ : QuasiIso (SSet.chainComplexMap φ.left R))
    (h₂ : QuasiIso (SSet.chainComplexMap φ.right R)) :
    QuasiIso (SSetPair.chainComplexMap φ R) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃ (pairShortComplexMap R φ)
    (P.shortExact_chainComplexShortComplex R) (P'.shortExact_chainComplexShortComplex R) h₁ h₂

theorem isIso_homologyMap_of_quasiIso
    (h₁ : QuasiIso (SSet.chainComplexMap φ.left R))
    (h₂ : QuasiIso (SSet.chainComplexMap φ.right R)) (n : ℕ) :
    IsIso (SSetPair.homologyMap φ R n) :=
  haveI := quasiIso_chainComplexMap_of_quasiIso R φ h₁ h₂
  (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance

instance isIso_homologyMap_of_isIso [IsIso φ] (n : ℕ) : IsIso (SSetPair.homologyMap φ R n) :=
  inferInstanceAs (IsIso ((SSetPair.homologyFunctor.{u} R n).map φ))

end PairQuasiIso

variable {X : TopCat.{u}} (U V : Set X)

lemma mapsTo_incl : Set.MapsTo (incl X U) (Subtype.val ⁻¹' V) V := fun _ hx ↦ hx

lemma singSub_inter_eq_inf_swap : singSub X (U ∩ V) = singSub X V ⊓ singSub X U := by
  rw [singSub_inf, inf_comm]

def infPairIso :
    SSetPair.of (SSet.Subcomplex.homOfLE (singSub_inter_le_left U V)) ≅
      pairInf (singSub X V) (singSub X U) :=
  MorphismProperty.Arrow.isoMk (SSet.Subcomplex.eqToIso (singSub_inter_eq_inf_swap U V))
    (Iso.refl _) (by
      rw [Iso.refl_hom]
      rfl)

@[simp] lemma infPairIso_hom_left :
    (infPairIso U V).hom.left =
      SSet.Subcomplex.homOfLE (singSub_inter_eq_inf_swap U V).le := rfl

@[simp] lemma infPairIso_hom_right : (infPairIso U V).hom.right = 𝟙 _ := rfl

def supPairMap : pairSup (singSub X V) (singSub X U) ⟶ pair X V :=
  SSetPair.homMk (singSubIso X V).hom (singSub X V ⊔ singSub X U).ι (by
    change (singSubIso X V).hom ≫ TopCat.toSSet.map (incl X V) =
      SSet.Subcomplex.homOfLE (le_sup_left : singSub X V ≤ singSub X V ⊔ singSub X U) ≫
        (singSub X V ⊔ singSub X U).ι
    rw [singSubIso_hom_map_incl, SSet.Subcomplex.homOfLE_ι])

@[simp] lemma supPairMap_left : (supPairMap U V).left = (singSubIso X V).hom := rfl

@[simp] lemma supPairMap_right : (supPairMap U V).right = (singSub X V ⊔ singSub X U).ι := rfl

abbrev inclRestr : TopCat.of (Subtype.val ⁻¹' V : Set (TopCat.of U)) ⟶ TopCat.of V :=
  TopCat.ofHom ⟨(mapsTo_incl U V).restrict, by fun_prop⟩

lemma pairMap_incl_left :
    (pairMap (incl X U) (mapsTo_incl U V)).left = TopCat.toSSet.map (inclRestr U V) := rfl

lemma pairMap_incl_right :
    (pairMap (incl X U) (mapsTo_incl U V)).right = TopCat.toSSet.map (incl X U) := rfl

lemma restrictPairIso_hom_left :
    (restrictPairIso U V).hom.left = (restrictIso U V).hom := rfl

lemma restrictPairIso_hom_right :
    (restrictPairIso U V).hom.right = (singSubIso X U).inv := rfl

lemma inclRestr_incl : inclRestr U V ≫ incl X V = inclRestrict U V := rfl

lemma factorisation_left :
    TopCat.toSSet.map (inclRestr U V) =
      (restrictIso U V).hom ≫
        SSet.Subcomplex.homOfLE (singSub_inter_eq_inf_swap U V).le ≫
        SSet.Subcomplex.homOfLE (inf_le_left : singSub X V ⊓ singSub X U ≤ singSub X V) ≫
        (singSubIso X V).hom := by
  rw [← cancel_mono (TopCat.toSSet.map (incl X V)), ← Functor.map_comp, inclRestr_incl,
    Category.assoc, Category.assoc, Category.assoc, singSubIso_hom_map_incl,
    SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.homOfLE_ι, restrictIso_hom_ι]

lemma factorisation_right :
    TopCat.toSSet.map (incl X U) =
      (singSubIso X U).inv ≫ 𝟙 _ ≫
        SSet.Subcomplex.homOfLE (le_sup_right : singSub X U ≤ singSub X V ⊔ singSub X U) ≫
        (singSub X V ⊔ singSub X U).ι := by
  rw [Category.id_comp, SSet.Subcomplex.homOfLE_ι, singSubIso_inv_ι]

theorem pairMap_incl_factorisation :
    pairMap (incl X U) (mapsTo_incl U V) =
      (restrictPairIso U V).hom ≫ (infPairIso U V).hom ≫
        excisionPairMap (singSub X V) (singSub X U) ≫ supPairMap U V := by
  apply MorphismProperty.Arrow.Hom.ext
  · simp only [MorphismProperty.Comma.comp_hom, Comma.comp_left]
    exact factorisation_left U V
  · simp only [MorphismProperty.Comma.comp_hom, Comma.comp_right]
    exact factorisation_right U V

section excision

variable {U V}

lemma iUnion_interior_coverFam_of_union (h : interior U ∪ interior V = Set.univ) :
    ⋃ b, interior (coverFam X U V b) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ interior U ∪ interior V := h ▸ Set.mem_univ x
  rw [Set.mem_iUnion]
  rcases hx with hx | hx
  · exact ⟨true, hx⟩
  · exact ⟨false, hx⟩

theorem quasiIso_sup_ι (h : interior U ∪ interior V = Set.univ) :
    QuasiIso (SSet.chainComplexMap (singSub X U ⊔ singSub X V).ι R) := by
  rw [← small_coverFam]
  exact quasiIso_smallChainMap R _ (iUnion_interior_coverFam_of_union h)

theorem quasiIso_supPairMap_left :
    QuasiIso (SSet.chainComplexMap (supPairMap U V).left R) :=
  quasiIso_of_isIso
    (((SSet.chainComplexFunctor.{u} (ModuleCat.{u} ℤ)).obj R).map (singSubIso X V).hom)

theorem quasiIso_supPairMap_right (h : interior U ∪ interior V = Set.univ) :
    QuasiIso (SSet.chainComplexMap (supPairMap U V).right R) := by
  rw [supPairMap_right]
  exact quasiIso_sup_ι R (by rwa [Set.union_comm])

theorem isIso_homologyMap_supPairMap (h : interior U ∪ interior V = Set.univ) (n : ℕ) :
    IsIso (SSetPair.homologyMap (supPairMap U V) R n) :=
  isIso_homologyMap_of_quasiIso R _ (quasiIso_supPairMap_left R)
    (quasiIso_supPairMap_right R h) n

theorem excision (h : interior U ∪ interior V = Set.univ) (n : ℕ) :
    IsIso (relativeHomologyMap R (incl X U) (mapsTo_incl U V) n) := by
  have := isIso_homologyMap_supPairMap R h n
  rw [relativeHomologyMap, pairMap_incl_factorisation, SSetPair.homologyMap_comp,
    SSetPair.homologyMap_comp, SSetPair.homologyMap_comp]
  infer_instance

def excisionIso (h : interior U ∪ interior V = Set.univ) (n : ℕ) :
    relativeHomology R (TopCat.of U) (Subtype.val ⁻¹' V) n ≅ relativeHomology R X V n :=
  @asIso _ _ _ _ _ (excision R h n)

lemma excisionIso_hom (h : interior U ∪ interior V = Set.univ) (n : ℕ) :
    (excisionIso R h n).hom = relativeHomologyMap R (incl X U) (mapsTo_incl U V) n := rfl

theorem excision_open (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    IsIso (relativeHomologyMap R (incl X U) (mapsTo_incl U V) n) :=
  excision R (by rwa [hU.interior_eq, hV.interior_eq]) n

def excisionOpenIso (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    relativeHomology R (TopCat.of U) (Subtype.val ⁻¹' V) n ≅ relativeHomology R X V n :=
  @asIso _ _ _ _ _ (excision_open R hU hV hUV n)

variable (Z A : Set X)

lemma interior_compl_union_interior_of_closure_subset (hZ : closure Z ⊆ interior A) :
    interior Zᶜ ∪ interior A = Set.univ := by
  rw [interior_compl]
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ closure Z
  · exact Or.inr (hZ hx)
  · exact Or.inl hx

theorem excision_closed (hZ : closure Z ⊆ interior A) (n : ℕ) :
    IsIso (relativeHomologyMap R (incl X Zᶜ) (mapsTo_incl Zᶜ A) n) :=
  excision R (interior_compl_union_interior_of_closure_subset Z A hZ) n

def excisionClosedIso (hZ : closure Z ⊆ interior A) (n : ℕ) :
    relativeHomology R (TopCat.of (Zᶜ : Set X)) (Subtype.val ⁻¹' A) n ≅ relativeHomology R X A n :=
  @asIso _ _ _ _ _ (excision_closed R Z A hZ n)

end excision

end DifferentialGeometry.Topology.SingularPair
