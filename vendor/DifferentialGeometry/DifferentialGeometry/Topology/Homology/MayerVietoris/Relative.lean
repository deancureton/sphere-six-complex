module

public import DifferentialGeometry.Topology.Homology.MayerVietoris.ShortExact

@[expose] public section

open CategoryTheory Limits Simplicial Opposite HomologicalComplex

open scoped ZeroObject

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

section BiprodCofork

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]
  {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} {f₁ : X₁ ⟶ Y₁} {π₁ : Y₁ ⟶ Z₁} {f₂ : X₂ ⟶ Y₂} {π₂ : Y₂ ⟶ Z₂}

lemma biprod_map_map_condition (w₁ : f₁ ≫ π₁ = 0) (w₂ : f₂ ≫ π₂ = 0) :
    biprod.map f₁ f₂ ≫ biprod.map π₁ π₂ = 0 := by
  apply biprod.hom_ext' <;> simp [biprod.inl_map_assoc, biprod.inr_map_assoc,
    reassoc_of% w₁, reassoc_of% w₂]

def isColimitBiprodCokernelCofork (w₁ : f₁ ≫ π₁ = 0) (w₂ : f₂ ≫ π₂ = 0)
    (h₁ : IsColimit (CokernelCofork.ofπ π₁ w₁)) (h₂ : IsColimit (CokernelCofork.ofπ π₂ w₂)) :
    IsColimit (CokernelCofork.ofπ (biprod.map π₁ π₂) (biprod_map_map_condition w₁ w₂)) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun {W} h hh ↦ biprod.desc
      (Cofork.IsColimit.desc h₁ (biprod.inl ≫ h) (by
        rw [zero_comp, ← biprod.inl_map_assoc, hh, comp_zero]))
      (Cofork.IsColimit.desc h₂ (biprod.inr ≫ h) (by
        rw [zero_comp, ← biprod.inr_map_assoc, hh, comp_zero])))
    (fun {W} h hh ↦ by
      apply biprod.hom_ext'
      · rw [biprod.inl_map_assoc, biprod.inl_desc]
        exact Cofork.IsColimit.π_desc' h₁ _ _
      · rw [biprod.inr_map_assoc, biprod.inr_desc]
        exact Cofork.IsColimit.π_desc' h₂ _ _)
    (fun {W} h hh m hm ↦ by
      apply biprod.hom_ext'
      · apply Cofork.IsColimit.hom_ext h₁
        rw [biprod.inl_desc, Cofork.IsColimit.π_desc', ← hm, Cofork.π_ofπ, biprod.inl_map_assoc]
      · apply Cofork.IsColimit.hom_ext h₂
        rw [biprod.inr_desc, Cofork.IsColimit.π_desc', ← hm, Cofork.π_ofπ, biprod.inr_map_assoc])

end BiprodCofork

section Split

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C] (X : C)

@[reassoc]
lemma split_lift_desc :
    biprod.lift (𝟙 X) (-𝟙 X) ≫ biprod.desc (𝟙 X) (𝟙 X) = 0 := by
  simp

def splitShortComplex : ShortComplex C :=
  ShortComplex.mk (biprod.lift (𝟙 X) (-𝟙 X)) (biprod.desc (𝟙 X) (𝟙 X)) (split_lift_desc X)

@[simp] lemma splitShortComplex_X₁ : (splitShortComplex X).X₁ = X := rfl
@[simp] lemma splitShortComplex_X₂ : (splitShortComplex X).X₂ = (X ⊞ X) := rfl
@[simp] lemma splitShortComplex_X₃ : (splitShortComplex X).X₃ = X := rfl
@[simp] lemma splitShortComplex_f : (splitShortComplex X).f = biprod.lift (𝟙 X) (-𝟙 X) := rfl
@[simp] lemma splitShortComplex_g : (splitShortComplex X).g = biprod.desc (𝟙 X) (𝟙 X) := rfl

lemma split_id :
    biprod.fst ≫ biprod.lift (𝟙 X) (-𝟙 X) + biprod.desc (𝟙 X) (𝟙 X) ≫ biprod.inr =
      𝟙 (X ⊞ X) := by
  apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp

def splitShortComplexSplitting : (splitShortComplex X).Splitting where
  r := biprod.fst
  s := biprod.inr
  f_r := biprod.lift_fst _ _
  s_g := biprod.inr_desc _ _
  id := split_id X

lemma splitShortComplex_shortExact [HasZeroObject C] : (splitShortComplex X).ShortExact :=
  (splitShortComplexSplitting X).shortExact

end Split

variable {K : SSet.{u}} (A B : K.Subcomplex)

def pairOfLE {A B : K.Subcomplex} (h : A ≤ B) : A.pair ⟶ B.pair :=
  (SSet.Subcomplex.toPairFunctor K).map (homOfLE h)

@[simp]
lemma pairOfLE_left {A B : K.Subcomplex} (h : A ≤ B) :
    (pairOfLE h).left = SSet.Subcomplex.homOfLE h := rfl

@[simp]
lemma pairOfLE_right {A B : K.Subcomplex} (h : A ≤ B) : (pairOfLE h).right = 𝟙 K := rfl

lemma pairOfLE_comp {A B C : K.Subcomplex} (h : A ≤ B) (h' : B ≤ C) :
    pairOfLE h ≫ pairOfLE h' = pairOfLE (h.trans h') := by
  rw [pairOfLE, pairOfLE, ← Functor.map_comp]
  rfl

lemma pairOfLE_refl (A : K.Subcomplex) : pairOfLE (le_refl A) = 𝟙 A.pair :=
  (SSet.Subcomplex.toPairFunctor K).map_id A

variable (R : ModuleCat.{u} ℤ)

abbrev quotMap {A B : K.Subcomplex} (h : A ≤ B) :
    A.pair.chainComplex R ⟶ B.pair.chainComplex R :=
  SSetPair.chainComplexMap (pairOfLE h) R

lemma quotMap_comp {A B C : K.Subcomplex} (h : A ≤ B) (h' : B ≤ C) :
    quotMap R h ≫ quotMap R h' = quotMap R (h.trans h') := by
  rw [quotMap, quotMap, quotMap, ← Functor.map_comp, pairOfLE_comp]

lemma quotMap_refl (A : K.Subcomplex) : quotMap R (le_refl A) = 𝟙 _ := by
  rw [quotMap, pairOfLE_refl]
  exact CategoryTheory.Functor.map_id _ _

lemma chainComplexMap_pairOfLE_right {A B : K.Subcomplex} (h : A ≤ B) :
    SSet.chainComplexMap (pairOfLE h).right R = 𝟙 (K.chainComplex R) :=
  CategoryTheory.Functor.map_id _ _

abbrev quotπ (A : K.Subcomplex) : K.chainComplex R ⟶ A.pair.chainComplex R :=
  A.pair.chainComplexπ R

abbrev subι (A : K.Subcomplex) : (A : SSet.{u}).chainComplex R ⟶ K.chainComplex R :=
  SSet.chainComplexMap A.ι R

instance mono_subι (A : K.Subcomplex) : Mono (subι R A) :=
  inferInstanceAs (Mono (SSet.chainComplexMap A.pair.hom R))

@[reassoc (attr := simp)]
lemma subι_quotπ (A : K.Subcomplex) : subι R A ≫ quotπ R A = 0 :=
  A.pair.chainComplex_condition R

@[reassoc (attr := simp)]
lemma quotπ_quotMap {A B : K.Subcomplex} (h : A ≤ B) :
    quotπ R A ≫ quotMap R h = quotπ R B := by
  have := (chainComplexMap_right_chainComplexπ R (pairOfLE h)).symm
  rw [chainComplexMap_pairOfLE_right] at this
  exact this.trans (Category.id_comp _)

abbrev q₁ : (A ⊓ B).pair.chainComplex R ⟶ A.pair.chainComplex R :=
  quotMap R (inf_le_left : A ⊓ B ≤ A)

abbrev q₂ : (A ⊓ B).pair.chainComplex R ⟶ B.pair.chainComplex R :=
  quotMap R (inf_le_right : A ⊓ B ≤ B)

abbrev r₁ : A.pair.chainComplex R ⟶ (A ⊔ B).pair.chainComplex R :=
  quotMap R (le_sup_left : A ≤ A ⊔ B)

abbrev r₂ : B.pair.chainComplex R ⟶ (A ⊔ B).pair.chainComplex R :=
  quotMap R (le_sup_right : B ≤ A ⊔ B)

@[reassoc (attr := simp)]
lemma q₁_r₁ : q₁ A B R ≫ r₁ A B R = q₂ A B R ≫ r₂ A B R := by
  simp only [q₁, r₁, q₂, r₂, quotMap_comp]

@[reassoc]
lemma quot_lift_desc :
    biprod.lift (q₁ A B R) (-(q₂ A B R)) ≫ biprod.desc (r₁ A B R) (r₂ A B R) = 0 := by
  simp

def quotMV : ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
  ShortComplex.mk (biprod.lift (q₁ A B R) (-(q₂ A B R))) (biprod.desc (r₁ A B R) (r₂ A B R))
    (quot_lift_desc A B R)

@[simp] lemma quotMV_X₁ : (quotMV A B R).X₁ = (A ⊓ B).pair.chainComplex R := rfl
@[simp] lemma quotMV_X₂ :
    (quotMV A B R).X₂ = (A.pair.chainComplex R ⊞ B.pair.chainComplex R) := rfl
@[simp] lemma quotMV_X₃ : (quotMV A B R).X₃ = (A ⊔ B).pair.chainComplex R := rfl
@[simp] lemma quotMV_f : (quotMV A B R).f = biprod.lift (q₁ A B R) (-(q₂ A B R)) := rfl
@[simp] lemma quotMV_g : (quotMV A B R).g = biprod.desc (r₁ A B R) (r₂ A B R) := rfl

def mvToSplit : mvShortComplex A B R ⟶ splitShortComplex (K.chainComplex R) where
  τ₁ := subι R (A ⊓ B)
  τ₂ := biprod.map (subι R A) (subι R B)
  τ₃ := subι R (A ⊔ B)
  comm₁₂ := by
    dsimp only [mvShortComplex, splitShortComplex]
    apply biprod.hom_ext <;> simp [← Functor.map_comp]
  comm₂₃ := by
    dsimp only [mvShortComplex, splitShortComplex]
    apply biprod.hom_ext' <;> simp [← Functor.map_comp]

def splitToQuotMV : splitShortComplex (K.chainComplex R) ⟶ quotMV A B R where
  τ₁ := quotπ R (A ⊓ B)
  τ₂ := biprod.map (quotπ R A) (quotπ R B)
  τ₃ := quotπ R (A ⊔ B)
  comm₁₂ := by
    dsimp only [splitShortComplex, quotMV]
    apply biprod.hom_ext <;> simp
  comm₂₃ := by
    dsimp only [splitShortComplex, quotMV]
    apply biprod.hom_ext' <;> simp

lemma mvToSplit_splitToQuotMV : mvToSplit A B R ≫ splitToQuotMV A B R = 0 := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  · exact subι_quotπ R (A ⊓ B)
  · exact biprod_map_map_condition (subι_quotπ R A) (subι_quotπ R B)
  · exact subι_quotπ R (A ⊔ B)

def quotMVSnakeInput : ShortComplex.SnakeInput (ChainComplex (ModuleCat.{u} ℤ) ℕ) where
  L₀ := ShortComplex.mk (0 : (0 : ChainComplex (ModuleCat.{u} ℤ) ℕ) ⟶ 0)
    (0 : 0 ⟶ (0 : ChainComplex (ModuleCat.{u} ℤ) ℕ)) zero_comp
  L₁ := mvShortComplex A B R
  L₂ := splitShortComplex (K.chainComplex R)
  L₃ := quotMV A B R
  v₀₁ := 0
  v₁₂ := mvToSplit A B R
  v₂₃ := splitToQuotMV A B R
  w₀₂ := zero_comp
  w₁₃ := mvToSplit_splitToQuotMV A B R
  h₀ := by
    apply ShortComplex.isLimitOfIsLimitπ
    · refine (KernelFork.isLimitMapConeEquiv _ _).symm
        (KernelFork.IsLimit.ofMonoOfIsZero _ ?_ (isZero_zero _))
      exact mono_subι R (A ⊓ B)
    · refine (KernelFork.isLimitMapConeEquiv _ _).symm
        (KernelFork.IsLimit.ofMonoOfIsZero _ ?_ (isZero_zero _))
      exact biprod.map_mono _ _
    · refine (KernelFork.isLimitMapConeEquiv _ _).symm
        (KernelFork.IsLimit.ofMonoOfIsZero _ ?_ (isZero_zero _))
      exact mono_subι R (A ⊔ B)
  h₃ := by
    apply ShortComplex.isColimitOfIsColimitπ
    · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm
        ((A ⊓ B).pair.isColimitCokernelCoforkChainComplex R)
    · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm
        (isColimitBiprodCokernelCofork (subι_quotπ R A) (subι_quotπ R B)
          (A.pair.isColimitCokernelCoforkChainComplex R)
          (B.pair.isColimitCokernelCoforkChainComplex R))
    · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm
        ((A ⊔ B).pair.isColimitCokernelCoforkChainComplex R)
  L₁_exact := (mvShortComplex_shortExact A B R).exact
  epi_L₁_g := (mvShortComplex_shortExact A B R).epi_g
  L₂_exact := (splitShortComplex_shortExact _).exact
  mono_L₂_f := (splitShortComplex_shortExact _).mono_f

lemma quotMVSnakeInput_L₃ : (quotMVSnakeInput A B R).L₃ = quotMV A B R := rfl

lemma quotMVSnakeInput_δ : (quotMVSnakeInput A B R).δ = 0 :=
  (isZero_zero _).eq_of_src _ _

theorem quotMV_shortExact : (quotMV A B R).ShortExact where
  exact := (quotMVSnakeInput A B R).L₃_exact
  mono_f := (quotMVSnakeInput A B R).L₂'_exact.mono_g (quotMVSnakeInput_δ A B R)
  epi_g := by
    have : Epi (quotMVSnakeInput A B R).L₂.g := (splitShortComplex_shortExact _).epi_g
    exact (quotMVSnakeInput A B R).epi_L₃_g

def quotMVδ (n : ℕ) :
    (A ⊔ B).pair.homology R (n + 1) ⟶ (A ⊓ B).pair.homology R n :=
  (quotMV_shortExact A B R).δ (n + 1) n rfl

@[reassoc (attr := simp)]
lemma quotMVδ_comp (n : ℕ) :
    quotMVδ A B R n ≫ homologyMap (biprod.lift (q₁ A B R) (-(q₂ A B R))) n = 0 :=
  (quotMV_shortExact A B R).δ_comp (n + 1) n rfl

@[reassoc (attr := simp)]
lemma comp_quotMVδ (n : ℕ) :
    homologyMap (biprod.desc (r₁ A B R) (r₂ A B R)) (n + 1) ≫ quotMVδ A B R n = 0 :=
  (quotMV_shortExact A B R).comp_δ (n + 1) n rfl

lemma homologyMap_quot_lift_desc (n : ℕ) :
    homologyMap (biprod.lift (q₁ A B R) (-(q₂ A B R))) n ≫
      homologyMap (biprod.desc (r₁ A B R) (r₂ A B R)) n = 0 := by
  rw [← homologyMap_comp, quot_lift_desc, homologyMap_zero]

theorem quotMV_exact₁ (n : ℕ) :
    (ShortComplex.mk (quotMVδ A B R n) (homologyMap (biprod.lift (q₁ A B R) (-(q₂ A B R))) n)
      (quotMVδ_comp A B R n)).Exact :=
  (quotMV_shortExact A B R).homology_exact₁ (n + 1) n rfl

theorem quotMV_exact₂ (n : ℕ) :
    (ShortComplex.mk (homologyMap (biprod.lift (q₁ A B R) (-(q₂ A B R))) n)
      (homologyMap (biprod.desc (r₁ A B R) (r₂ A B R)) n)
      (homologyMap_quot_lift_desc A B R n)).Exact :=
  (quotMV_shortExact A B R).homology_exact₂ n

theorem quotMV_exact₃ (n : ℕ) :
    (ShortComplex.mk (homologyMap (biprod.desc (r₁ A B R) (r₂ A B R)) (n + 1)) (quotMVδ A B R n)
      (comp_quotMVδ A B R n)).Exact :=
  (quotMV_shortExact A B R).homology_exact₃ (n + 1) n rfl

def homologyBiprodIsoOf (X Y : ChainComplex (ModuleCat.{u} ℤ) ℕ) (n : ℕ) :
    (X ⊞ Y).homology n ≅ (X.homology n ⊞ Y.homology n) where
  hom := biprod.lift (homologyMap biprod.fst n) (homologyMap biprod.snd n)
  inv := biprod.desc (homologyMap biprod.inl n) (homologyMap biprod.inr n)
  hom_inv_id := by
    rw [biprod.lift_desc, ← homologyMap_comp, ← homologyMap_comp, ← homologyMap_add,
      biprod.total, homologyMap_id]
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp [← homologyMap_comp]

abbrev quotHomologyMap {A B : K.Subcomplex} (h : A ≤ B) (n : ℕ) :
    A.pair.homology R n ⟶ B.pair.homology R n :=
  SSetPair.homologyMap (pairOfLE h) R n

lemma quotHomologyMap_comp {A B C : K.Subcomplex} (h : A ≤ B) (h' : B ≤ C) (n : ℕ) :
    quotHomologyMap R h n ≫ quotHomologyMap R h' n = quotHomologyMap R (h.trans h') n := by
  rw [quotHomologyMap, quotHomologyMap, quotHomologyMap, ← SSetPair.homologyMap_comp,
    pairOfLE_comp]

lemma quotHomologyMap_refl (A : K.Subcomplex) (n : ℕ) :
    quotHomologyMap R (le_refl A) n = 𝟙 _ := by
  rw [quotHomologyMap, pairOfLE_refl, SSetPair.homologyMap_id]

@[reassoc (attr := simp)]
lemma homologyπ_quotHomologyMap {A B : K.Subcomplex} (h : A ≤ B) (n : ℕ) :
    A.pair.homologyπ R n ≫ quotHomologyMap R h n = B.pair.homologyπ R n := by
  rw [quotHomologyMap, SSetPair.homologyMap, SSetPair.homologyπ, ← homologyMap_comp]
  exact congrArg (fun φ ↦ homologyMap φ n) (quotπ_quotMap R h)

def quotMVLift (n : ℕ) :
    (A ⊓ B).pair.homology R n ⟶ (A.pair.homology R n ⊞ B.pair.homology R n) :=
  biprod.lift (quotHomologyMap R (inf_le_left : A ⊓ B ≤ A) n)
    (-(quotHomologyMap R (inf_le_right : A ⊓ B ≤ B) n))

def quotMVDesc (n : ℕ) :
    (A.pair.homology R n ⊞ B.pair.homology R n) ⟶ (A ⊔ B).pair.homology R n :=
  biprod.desc (quotHomologyMap R (le_sup_left : A ≤ A ⊔ B) n)
    (quotHomologyMap R (le_sup_right : B ≤ A ⊔ B) n)

@[simp]
lemma quotMVLift_fst (n : ℕ) :
    quotMVLift A B R n ≫ biprod.fst = quotHomologyMap R (inf_le_left : A ⊓ B ≤ A) n :=
  biprod.lift_fst _ _

@[simp]
lemma quotMVLift_snd (n : ℕ) :
    quotMVLift A B R n ≫ biprod.snd = -quotHomologyMap R (inf_le_right : A ⊓ B ≤ B) n :=
  biprod.lift_snd _ _

@[simp]
lemma inl_quotMVDesc (n : ℕ) :
    biprod.inl ≫ quotMVDesc A B R n = quotHomologyMap R (le_sup_left : A ≤ A ⊔ B) n :=
  biprod.inl_desc _ _

@[simp]
lemma inr_quotMVDesc (n : ℕ) :
    biprod.inr ≫ quotMVDesc A B R n = quotHomologyMap R (le_sup_right : B ≤ A ⊔ B) n :=
  biprod.inr_desc _ _

lemma homologyMap_quot_lift_homologyBiprodIsoOf_hom (n : ℕ) :
    homologyMap (biprod.lift (q₁ A B R) (-(q₂ A B R))) n ≫
      (homologyBiprodIsoOf _ _ n).hom = quotMVLift A B R n := by
  dsimp only [homologyBiprodIsoOf, quotMVLift]
  apply biprod.hom_ext
  · simp [← homologyMap_comp]
  · simp [← homologyMap_comp, homologyMap_neg]

lemma homologyBiprodIsoOf_inv_homologyMap_quot_desc (n : ℕ) :
    (homologyBiprodIsoOf _ _ n).inv ≫ homologyMap (biprod.desc (r₁ A B R) (r₂ A B R)) n =
      quotMVDesc A B R n := by
  dsimp only [homologyBiprodIsoOf, quotMVDesc]
  apply biprod.hom_ext'
  · simp [← homologyMap_comp]
  · simp [← homologyMap_comp]

@[reassoc (attr := simp)]
lemma quotMVδ_quotMVLift (n : ℕ) : quotMVδ A B R n ≫ quotMVLift A B R n = 0 := by
  rw [← homologyMap_quot_lift_homologyBiprodIsoOf_hom, quotMVδ_comp_assoc, zero_comp]

@[reassoc (attr := simp)]
lemma quotMVLift_quotMVDesc (n : ℕ) : quotMVLift A B R n ≫ quotMVDesc A B R n = 0 := by
  rw [← homologyMap_quot_lift_homologyBiprodIsoOf_hom,
    ← homologyBiprodIsoOf_inv_homologyMap_quot_desc, Category.assoc, Iso.hom_inv_id_assoc,
    homologyMap_quot_lift_desc]

@[reassoc (attr := simp)]
lemma quotMVDesc_quotMVδ (n : ℕ) : quotMVDesc A B R (n + 1) ≫ quotMVδ A B R n = 0 := by
  rw [← homologyBiprodIsoOf_inv_homologyMap_quot_desc, Category.assoc, comp_quotMVδ, comp_zero]

theorem quotMV_exact₁' (n : ℕ) :
    (ShortComplex.mk (quotMVδ A B R n) (quotMVLift A B R n)
      (quotMVδ_quotMVLift A B R n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (quotMV_exact₁ A B R n)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (homologyBiprodIsoOf _ _ n)
    (by simp) (by simp [homologyMap_quot_lift_homologyBiprodIsoOf_hom])

theorem quotMV_exact₂' (n : ℕ) :
    (ShortComplex.mk (quotMVLift A B R n) (quotMVDesc A B R n)
      (quotMVLift_quotMVDesc A B R n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (quotMV_exact₂ A B R n)
  exact ShortComplex.isoMk (Iso.refl _) (homologyBiprodIsoOf _ _ n) (Iso.refl _)
    (by simp [homologyMap_quot_lift_homologyBiprodIsoOf_hom])
    (by simp [← homologyBiprodIsoOf_inv_homologyMap_quot_desc])

theorem quotMV_exact₃' (n : ℕ) :
    (ShortComplex.mk (quotMVDesc A B R (n + 1)) (quotMVδ A B R n)
      (quotMVDesc_quotMVδ A B R n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (quotMV_exact₃ A B R n)
  exact ShortComplex.isoMk (homologyBiprodIsoOf _ _ (n + 1)) (Iso.refl _) (Iso.refl _)
    (by simp [← homologyBiprodIsoOf_inv_homologyMap_quot_desc]) (by simp)

end DifferentialGeometry.Topology.SingularPair
