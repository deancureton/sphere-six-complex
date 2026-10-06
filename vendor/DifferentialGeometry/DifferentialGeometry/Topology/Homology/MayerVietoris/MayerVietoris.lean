module

public import DifferentialGeometry.Topology.Homology.SingularSubcomplex
public import DifferentialGeometry.Topology.Homology.MayerVietoris.ShortExact
public import DifferentialGeometry.Topology.Homology.Subdivision.SmallSimplices

@[expose] public section

open CategoryTheory Limits HomologicalComplex

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

variable (R : ModuleCat.{u} ℤ) (X : TopCat.{u}) (U V : Set X)

abbrev coverFam : Bool → Set X := fun b ↦ bif b then U else V

lemma small_coverFam : small X (coverFam X U V) = singSub X U ⊔ singSub X V :=
  small_pair U V

variable {X U V} in
lemma iUnion_interior_coverFam (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) :
    ⋃ b, interior (coverFam X U V b) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ U ∪ V := hUV ▸ Set.mem_univ x
  rw [Set.mem_iUnion]
  rcases hx with hx | hx
  · exact ⟨true, by simpa [coverFam, hU.interior_eq] using hx⟩
  · exact ⟨false, by simpa [coverFam, hV.interior_eq] using hx⟩

variable {X U V} in
theorem isIso_homologyMap_sup_ι (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ) : IsIso (SSet.homologyMap (singSub X U ⊔ singSub X V).ι R n) := by
  rw [← small_coverFam]
  exact isIso_homologyMap_small R _ (iUnion_interior_coverFam hU hV hUV) n

variable {X U V} in
def supIso (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    ((singSub X U ⊔ singSub X V : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).homology R n ≅
      singularHomology R X n :=
  @asIso _ _ _ _ _ (isIso_homologyMap_sup_ι R hU hV hUV n)

variable {X U V} in
lemma supIso_hom (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    (supIso R hU hV hUV n).hom = SSet.homologyMap (singSub X U ⊔ singSub X V).ι R n := rfl

def infIso (n : ℕ) :
    ((singSub X U ⊓ singSub X V : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).homology R n ≅
      singularHomology R (TopCat.of (U ∩ V : Set X)) n :=
  (SSet.homologyFunctor.{u} R n).mapIso (SSet.Subcomplex.eqToIso (singSub_inf X U V).symm) ≪≫
    singularSubcomplexHomologyIso X R (U ∩ V) n

lemma infIso_hom (n : ℕ) :
    (infIso R X U V n).hom =
      SSet.homologyMap (SSet.Subcomplex.homOfLE (singSub_inf X U V).symm.le) R n ≫
        (singularSubcomplexHomologyIso X R (U ∩ V) n).hom := rfl

def mvOpenLift (n : ℕ) :
    singularHomology R (TopCat.of (U ∩ V : Set X)) n ⟶ singularHomology R (TopCat.of U) n ⊞ singularHomology R (TopCat.of V) n :=
  biprod.lift (homologyMap ((singularChainFunctor R).map (inclOfLE (Set.inter_subset_left : U ∩ V ⊆ U))) n)
    (-(homologyMap ((singularChainFunctor R).map (inclOfLE (Set.inter_subset_right : U ∩ V ⊆ V))) n))

def mvOpenDesc (n : ℕ) : singularHomology R (TopCat.of U) n ⊞ singularHomology R (TopCat.of V) n ⟶ singularHomology R X n :=
  biprod.desc (inclMap R X U n) (inclMap R X V n)

@[simp]
lemma mvOpenLift_fst (n : ℕ) :
    mvOpenLift R X U V n ≫ biprod.fst =
      homologyMap ((singularChainFunctor R).map (inclOfLE (Set.inter_subset_left : U ∩ V ⊆ U))) n :=
  biprod.lift_fst _ _

@[simp]
lemma mvOpenLift_snd (n : ℕ) :
    mvOpenLift R X U V n ≫ biprod.snd =
      -homologyMap ((singularChainFunctor R).map (inclOfLE (Set.inter_subset_right : U ∩ V ⊆ V))) n :=
  biprod.lift_snd _ _

@[simp]
lemma inl_mvOpenDesc (n : ℕ) : biprod.inl ≫ mvOpenDesc R X U V n = inclMap R X U n :=
  biprod.inl_desc _ _

@[simp]
lemma inr_mvOpenDesc (n : ℕ) : biprod.inr ≫ mvOpenDesc R X U V n = inclMap R X V n :=
  biprod.inr_desc _ _

variable {X U V} in
def mvOpenδ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    singularHomology R X (n + 1) ⟶ singularHomology R (TopCat.of (U ∩ V : Set X)) n :=
  (supIso R hU hV hUV (n + 1)).inv ≫ mvδ (singSub X U) (singSub X V) R n ≫
    (infIso R X U V n).hom

abbrev biprodHIso (n : ℕ) :
    (((singSub X U : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).homology R n ⊞
      ((singSub X V : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).homology R n) ≅
      (singularHomology R (TopCat.of U) n ⊞ singularHomology R (TopCat.of V) n) :=
  biprod.mapIso (singularSubcomplexHomologyIso X R U n) (singularSubcomplexHomologyIso X R V n)

lemma infIso_hom_mvOpenLift (n : ℕ) :
    (infIso R X U V n).hom ≫ mvOpenLift R X U V n =
      mvLift (singSub X U) (singSub X V) R n ≫ (biprodHIso R X U V n).hom := by
  have h1 : (singularSubcomplexHomologyIso X R (U ∩ V) n).hom ≫ (mvOpenLift R X U V n ≫ biprod.fst) =
      SSet.homologyMap (SSet.Subcomplex.homOfLE
        (singSub_mono X (Set.inter_subset_left : U ∩ V ⊆ U))) R n ≫ (singularSubcomplexHomologyIso X R U n).hom := by
    rw [mvOpenLift_fst]
    exact singularSubcomplexHomologyIso_hom_map_inclOfLE R _ n
  have h2 : (singularSubcomplexHomologyIso X R (U ∩ V) n).hom ≫ (mvOpenLift R X U V n ≫ biprod.snd) =
      -(SSet.homologyMap (SSet.Subcomplex.homOfLE
        (singSub_mono X (Set.inter_subset_right : U ∩ V ⊆ V))) R n ≫ (singularSubcomplexHomologyIso X R V n).hom) := by
    rw [mvOpenLift_snd]
    exact (Preadditive.comp_neg _ _).trans (congrArg Neg.neg (singularSubcomplexHomologyIso_hom_map_inclOfLE R _ n))
  apply biprod.hom_ext
  · rw [Category.assoc, infIso_hom, Category.assoc, h1, biprod.mapIso_hom, Category.assoc,
      biprod.map_fst, reassoc_of% (mvLift_fst (singSub X U) (singSub X V) R n),
      ← Category.assoc, ← SSet.homologyMap_comp]
    rfl
  · rw [Category.assoc, infIso_hom, Category.assoc, h2, biprod.mapIso_hom, Category.assoc,
      biprod.map_snd, reassoc_of% (mvLift_snd (singSub X U) (singSub X V) R n),
      Preadditive.neg_comp, Preadditive.comp_neg, ← Category.assoc, ← SSet.homologyMap_comp]
    rfl

lemma biprodHIso_hom_mvOpenDesc (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ) :
    (biprodHIso R X U V n).hom ≫ mvOpenDesc R X U V n =
      mvDesc (singSub X U) (singSub X V) R n ≫ (supIso R hU hV hUV n).hom := by
  apply biprod.hom_ext'
  · rw [biprod.mapIso_hom, biprod.inl_map_assoc, inl_mvOpenDesc, singularSubcomplexHomologyIso_hom_inclMap,
      ← Category.assoc, inl_mvDesc, supIso_hom]
    erw [← SSet.homologyMap_comp]
    rw [SSet.Subcomplex.homOfLE_ι]
  · rw [biprod.mapIso_hom, biprod.inr_map_assoc, inr_mvOpenDesc, singularSubcomplexHomologyIso_hom_inclMap,
      ← Category.assoc, inr_mvDesc, supIso_hom]
    erw [← SSet.homologyMap_comp]
    rw [SSet.Subcomplex.homOfLE_ι]

variable {X U V} in
lemma supIso_hom_mvOpenδ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    (supIso R hU hV hUV (n + 1)).hom ≫ mvOpenδ R hU hV hUV n =
      mvδ (singSub X U) (singSub X V) R n ≫ (infIso R X U V n).hom := by
  rw [mvOpenδ, Iso.hom_inv_id_assoc]

variable {X U V}

@[reassoc (attr := simp)]
lemma mvOpenδ_mvOpenLift (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    mvOpenδ R hU hV hUV n ≫ mvOpenLift R X U V n = 0 := by
  rw [mvOpenδ, Category.assoc, Category.assoc, infIso_hom_mvOpenLift, mvδ_mvLift_assoc,
    zero_comp, comp_zero]

@[reassoc (attr := simp)]
lemma mvOpenLift_mvOpenDesc (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ) :
    mvOpenLift R X U V n ≫ mvOpenDesc R X U V n = 0 := by
  rw [← cancel_epi (infIso R X U V n).hom, ← Category.assoc, infIso_hom_mvOpenLift,
    Category.assoc, biprodHIso_hom_mvOpenDesc R X U V hU hV hUV, mvLift_mvDesc_assoc,
    zero_comp, comp_zero]

@[reassoc (attr := simp)]
lemma mvOpenDesc_mvOpenδ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    mvOpenDesc R X U V (n + 1) ≫ mvOpenδ R hU hV hUV n = 0 := by
  rw [← cancel_epi (biprodHIso R X U V (n + 1)).hom, ← Category.assoc,
    biprodHIso_hom_mvOpenDesc R X U V hU hV hUV, Category.assoc, supIso_hom_mvOpenδ,
    mvDesc_mvδ_assoc, zero_comp, comp_zero]

theorem mayerVietoris_exact₁ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ) :
    (ShortComplex.mk (mvOpenδ R hU hV hUV n) (mvOpenLift R X U V n)
      (mvOpenδ_mvOpenLift R hU hV hUV n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (mv_exact₁' (singSub X U) (singSub X V) R n)
  exact ShortComplex.isoMk (supIso R hU hV hUV (n + 1)) (infIso R X U V n)
    (biprodHIso R X U V n) (supIso_hom_mvOpenδ R hU hV hUV n) (infIso_hom_mvOpenLift R X U V n)

theorem mayerVietoris_exact₂ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ) :
    (ShortComplex.mk (mvOpenLift R X U V n) (mvOpenDesc R X U V n)
      (mvOpenLift_mvOpenDesc R hU hV hUV n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (mv_exact₂' (singSub X U) (singSub X V) R n)
  exact ShortComplex.isoMk (infIso R X U V n) (biprodHIso R X U V n) (supIso R hU hV hUV n)
    (infIso_hom_mvOpenLift R X U V n) (biprodHIso_hom_mvOpenDesc R X U V hU hV hUV n)

theorem mayerVietoris_exact₃ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ) :
    (ShortComplex.mk (mvOpenDesc R X U V (n + 1)) (mvOpenδ R hU hV hUV n)
      (mvOpenDesc_mvOpenδ R hU hV hUV n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (mv_exact₃' (singSub X U) (singSub X V) R n)
  exact ShortComplex.isoMk (biprodHIso R X U V (n + 1)) (supIso R hU hV hUV (n + 1))
    (infIso R X U V n) (biprodHIso_hom_mvOpenDesc R X U V hU hV hUV (n + 1))
    (supIso_hom_mvOpenδ R hU hV hUV n)

lemma mvOpenDesc_eq_zero_of_isZero (n : ℕ) (hU' : IsZero (singularHomology R (TopCat.of U) n))
    (hV' : IsZero (singularHomology R (TopCat.of V) n)) : mvOpenDesc R X U V n = 0 :=
  IsZero.eq_zero_of_src ((biprod_isZero_iff _ _).2 ⟨hU', hV'⟩) _

lemma mvOpenLift_eq_zero_of_isZero (n : ℕ) (hU' : IsZero (singularHomology R (TopCat.of U) n))
    (hV' : IsZero (singularHomology R (TopCat.of V) n)) : mvOpenLift R X U V n = 0 :=
  IsZero.eq_zero_of_tgt ((biprod_isZero_iff _ _).2 ⟨hU', hV'⟩) _

theorem mono_mvOpenδ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ)
    (hU' : IsZero (singularHomology R (TopCat.of U) (n + 1))) (hV' : IsZero (singularHomology R (TopCat.of V) (n + 1))) :
    Mono (mvOpenδ R hU hV hUV n) :=
  (mayerVietoris_exact₃ R hU hV hUV n).mono_g (mvOpenDesc_eq_zero_of_isZero R (n + 1) hU' hV')

theorem epi_mvOpenδ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ)
    (hU' : IsZero (singularHomology R (TopCat.of U) n)) (hV' : IsZero (singularHomology R (TopCat.of V) n)) :
    Epi (mvOpenδ R hU hV hUV n) :=
  (mayerVietoris_exact₁ R hU hV hUV n).epi_f (mvOpenLift_eq_zero_of_isZero R n hU' hV')

def mvOpenδIsKernel (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ)
    (hU' : IsZero (singularHomology R (TopCat.of U) (n + 1))) (hV' : IsZero (singularHomology R (TopCat.of V) (n + 1))) :
    IsLimit (KernelFork.ofι (mvOpenδ R hU hV hUV n) (mvOpenδ_mvOpenLift R hU hV hUV n)) :=
  haveI := mono_mvOpenδ R hU hV hUV n hU' hV'
  (mayerVietoris_exact₁ R hU hV hUV n).fIsKernel

theorem isIso_mvOpenδ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ)
    (hU₁ : IsZero (singularHomology R (TopCat.of U) (n + 1))) (hV₁ : IsZero (singularHomology R (TopCat.of V) (n + 1)))
    (hU₀ : IsZero (singularHomology R (TopCat.of U) n)) (hV₀ : IsZero (singularHomology R (TopCat.of V) n)) :
    IsIso (mvOpenδ R hU hV hUV n) :=
  haveI := mono_mvOpenδ R hU hV hUV n hU₁ hV₁
  haveI := epi_mvOpenδ R hU hV hUV n hU₀ hV₀
  isIso_of_mono_of_epi _

def mvOpenδIso (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ)
    (hU₁ : IsZero (singularHomology R (TopCat.of U) (n + 1))) (hV₁ : IsZero (singularHomology R (TopCat.of V) (n + 1)))
    (hU₀ : IsZero (singularHomology R (TopCat.of U) n)) (hV₀ : IsZero (singularHomology R (TopCat.of V) n)) :
    singularHomology R X (n + 1) ≅ singularHomology R (TopCat.of (U ∩ V : Set X)) n :=
  @asIso _ _ _ _ _ (isIso_mvOpenδ R hU hV hUV n hU₁ hV₁ hU₀ hV₀)

def mayerVietorisIsoOfIsZero (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ)
    (h : ∀ k, k = n ∨ k = n + 1 →
      IsZero (singularHomology R (TopCat.of U) k) ∧ IsZero (singularHomology R (TopCat.of V) k)) :
    singularHomology R X (n + 1) ≅ singularHomology R (TopCat.of (U ∩ V : Set X)) n :=
  mvOpenδIso R hU hV hUV n (h (n + 1) (Or.inr rfl)).1 (h (n + 1) (Or.inr rfl)).2
    (h n (Or.inl rfl)).1 (h n (Or.inl rfl)).2

def mvOpenBoundaryIsoOfContractible (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    [ContractibleSpace U] [ContractibleSpace V] (n : ℕ) (hn : n ≠ 0) :
    singularHomology R X (n + 1) ≅ singularHomology R (TopCat.of (U ∩ V : Set X)) n :=
  mvOpenδIso R hU hV hUV n (isZero_of_contractible R U (n + 1) n.succ_ne_zero)
    (isZero_of_contractible R V (n + 1) n.succ_ne_zero)
    (isZero_of_contractible R U n hn) (isZero_of_contractible R V n hn)

end DifferentialGeometry.Topology.SingularPair
