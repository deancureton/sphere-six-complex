module

public import DifferentialGeometry.Topology.Homology.SingularPair
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst

@[expose] public section

open CategoryTheory Limits Simplicial Opposite HomologicalComplex

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

section CokerIso

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  {X₁ X₂ X₃ X₄ : C} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
  {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

def pushoutCokernelIso (h : IsPushout t l r b)
    {cl : CokernelCofork l} (hl : IsColimit cl)
    {cr : CokernelCofork r} (hr : IsColimit cr) :
    cl.pt ≅ cr.pt where
  hom := Cofork.IsColimit.desc hl (b ≫ cr.π) (by
    rw [← Category.assoc, ← h.w, Category.assoc, cr.condition, comp_zero, zero_comp])
  inv := Cofork.IsColimit.desc hr (h.desc 0 cl.π (by simp [cl.condition]))
    (by simp [zero_comp])
  hom_inv_id := by
    apply Cofork.IsColimit.hom_ext hl
    simp
  inv_hom_id := by
    apply Cofork.IsColimit.hom_ext hr
    apply h.hom_ext
    · simp
    · simp

@[reassoc (attr := simp)]
lemma π_pushoutCokernelIso_hom (h : IsPushout t l r b)
    {cl : CokernelCofork l} (hl : IsColimit cl)
    {cr : CokernelCofork r} (hr : IsColimit cr) :
    cl.π ≫ (pushoutCokernelIso h hl hr).hom = b ≫ cr.π := by
  simp [pushoutCokernelIso]

@[reassoc (attr := simp)]
lemma π_pushoutCokernelIso_inv (h : IsPushout t l r b)
    {cl : CokernelCofork l} (hl : IsColimit cl)
    {cr : CokernelCofork r} (hr : IsColimit cr) :
    b ≫ cr.π ≫ (pushoutCokernelIso h hl hr).inv = cl.π := by
  simp [pushoutCokernelIso]

end CokerIso

variable {K : SSet.{u}} (A B : K.Subcomplex) (R : ModuleCat.{u} ℤ)

lemma bicartSq : SSet.Subcomplex.BicartSq (A ⊓ B) A B (A ⊔ B) where
  sup_eq := rfl
  inf_eq := rfl

lemma isPushout_sset :
    IsPushout (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A))
      (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B))
      (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B))
      (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B)) :=
  (bicartSq A B).isPushout

abbrev ι₁ :
    ((A ⊓ B : K.Subcomplex) : SSet.{u}).chainComplex R ⟶ (A : SSet.{u}).chainComplex R :=
  SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)) R

abbrev ι₂ :
    ((A ⊓ B : K.Subcomplex) : SSet.{u}).chainComplex R ⟶ (B : SSet.{u}).chainComplex R :=
  SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) R

abbrev j₁ :
    (A : SSet.{u}).chainComplex R ⟶ ((A ⊔ B : K.Subcomplex) : SSet.{u}).chainComplex R :=
  SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B)) R

abbrev j₂ :
    (B : SSet.{u}).chainComplex R ⟶ ((A ⊔ B : K.Subcomplex) : SSet.{u}).chainComplex R :=
  SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B)) R

lemma isPushout_X (n : ℕ) :
    IsPushout ((ι₁ A B R).f n) ((ι₂ A B R).f n) ((j₁ A B R).f n) ((j₂ A B R).f n) :=
  ((isPushout_sset A B).map ((evaluation _ _).obj (op ⦋n⦌))).map (sigmaConst.obj R)

@[reassoc (attr := simp)]
lemma ι₁_j₁ : ι₁ A B R ≫ j₁ A B R = ι₂ A B R ≫ j₂ A B R := by
  simp only [ι₁, j₁, ι₂, j₂, ← Functor.map_comp]
  rfl

lemma isPushout : IsPushout (ι₁ A B R) (ι₂ A B R) (j₁ A B R) (j₂ A B R) where
  w := ι₁_j₁ A B R
  isColimit' := ⟨isColimitOfEval _ _ (fun n ↦
    (PushoutCocone.isColimitMapCoconeEquiv _ _).2 (isPushout_X A B R n).isColimit)⟩

instance : Mono (ι₁ A B R) :=
  inferInstanceAs (Mono (SSet.chainComplexMap
    (SSetPair.of (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A))).hom R))

instance : Mono (ι₂ A B R) :=
  inferInstanceAs (Mono (SSet.chainComplexMap
    (SSetPair.of (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B))).hom R))

instance : Mono (j₁ A B R) :=
  inferInstanceAs (Mono (SSet.chainComplexMap
    (SSetPair.of (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B))).hom R))

instance : Mono (j₂ A B R) :=
  inferInstanceAs (Mono (SSet.chainComplexMap
    (SSetPair.of (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B))).hom R))

@[reassoc]
lemma lift_desc :
    biprod.lift (ι₁ A B R) (-(ι₂ A B R)) ≫ biprod.desc (j₁ A B R) (j₂ A B R) = 0 := by
  simp

def mvShortComplex : ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
  ShortComplex.mk (biprod.lift (ι₁ A B R) (-(ι₂ A B R)))
    (biprod.desc (j₁ A B R) (j₂ A B R)) (lift_desc A B R)

lemma mvShortComplex_eq : mvShortComplex A B R = (isPushout A B R).shortComplex := rfl

@[simp] lemma mvShortComplex_X₁ :
    (mvShortComplex A B R).X₁ = ((A ⊓ B : K.Subcomplex) : SSet.{u}).chainComplex R := rfl

@[simp] lemma mvShortComplex_X₂ :
    (mvShortComplex A B R).X₂ =
      ((A : SSet.{u}).chainComplex R ⊞ (B : SSet.{u}).chainComplex R) := rfl

@[simp] lemma mvShortComplex_X₃ :
    (mvShortComplex A B R).X₃ = ((A ⊔ B : K.Subcomplex) : SSet.{u}).chainComplex R := rfl

@[simp] lemma mvShortComplex_f :
    (mvShortComplex A B R).f = biprod.lift (ι₁ A B R) (-(ι₂ A B R)) := rfl

@[simp] lemma mvShortComplex_g :
    (mvShortComplex A B R).g = biprod.desc (j₁ A B R) (j₂ A B R) := rfl

theorem mvShortComplex_shortExact : (mvShortComplex A B R).ShortExact where
  exact := (isPushout A B R).exact_shortComplex
  mono_f := by
    dsimp [mvShortComplex]
    exact mono_of_mono_fac (biprod.lift_fst _ _)
  epi_g := (isPushout A B R).epi_shortComplex_g

def mvδ (n : ℕ) :
    ((A ⊔ B : K.Subcomplex) : SSet.{u}).homology R (n + 1) ⟶
      ((A ⊓ B : K.Subcomplex) : SSet.{u}).homology R n :=
  (mvShortComplex_shortExact A B R).δ (n + 1) n rfl

@[reassoc (attr := simp)]
lemma mvδ_comp (n : ℕ) :
    mvδ A B R n ≫ homologyMap (biprod.lift (ι₁ A B R) (-(ι₂ A B R))) n = 0 :=
  (mvShortComplex_shortExact A B R).δ_comp (n + 1) n rfl

@[reassoc (attr := simp)]
lemma comp_mvδ (n : ℕ) :
    homologyMap (biprod.desc (j₁ A B R) (j₂ A B R)) (n + 1) ≫ mvδ A B R n = 0 :=
  (mvShortComplex_shortExact A B R).comp_δ (n + 1) n rfl

lemma homologyMap_lift_desc (n : ℕ) :
    homologyMap (biprod.lift (ι₁ A B R) (-(ι₂ A B R))) n ≫
      homologyMap (biprod.desc (j₁ A B R) (j₂ A B R)) n = 0 := by
  rw [← homologyMap_comp, lift_desc, homologyMap_zero]

theorem mv_exact₁ (n : ℕ) :
    (ShortComplex.mk (mvδ A B R n) (homologyMap (biprod.lift (ι₁ A B R) (-(ι₂ A B R))) n)
      (mvδ_comp A B R n)).Exact :=
  (mvShortComplex_shortExact A B R).homology_exact₁ (n + 1) n rfl

theorem mv_exact₂ (n : ℕ) :
    (ShortComplex.mk (homologyMap (biprod.lift (ι₁ A B R) (-(ι₂ A B R))) n)
      (homologyMap (biprod.desc (j₁ A B R) (j₂ A B R)) n)
      (homologyMap_lift_desc A B R n)).Exact :=
  (mvShortComplex_shortExact A B R).homology_exact₂ n

theorem mv_exact₃ (n : ℕ) :
    (ShortComplex.mk (homologyMap (biprod.desc (j₁ A B R) (j₂ A B R)) (n + 1)) (mvδ A B R n)
      (comp_mvδ A B R n)).Exact :=
  (mvShortComplex_shortExact A B R).homology_exact₃ (n + 1) n rfl

def homologyBiprodIso (n : ℕ) :
    ((A : SSet.{u}).chainComplex R ⊞ (B : SSet.{u}).chainComplex R).homology n ≅
      ((A : SSet.{u}).homology R n ⊞ (B : SSet.{u}).homology R n) where
  hom := biprod.lift (homologyMap biprod.fst n) (homologyMap biprod.snd n)
  inv := biprod.desc (homologyMap biprod.inl n) (homologyMap biprod.inr n)
  hom_inv_id := by
    rw [biprod.lift_desc, ← homologyMap_comp, ← homologyMap_comp, ← homologyMap_add,
      biprod.total, homologyMap_id]
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp [← homologyMap_comp]

def mvLift (n : ℕ) :
    ((A ⊓ B : K.Subcomplex) : SSet.{u}).homology R n ⟶
      ((A : SSet.{u}).homology R n ⊞ (B : SSet.{u}).homology R n) :=
  biprod.lift (SSet.homologyMap (SSet.Subcomplex.homOfLE inf_le_left) R n)
    (-(SSet.homologyMap (SSet.Subcomplex.homOfLE inf_le_right) R n))

def mvDesc (n : ℕ) :
    ((A : SSet.{u}).homology R n ⊞ (B : SSet.{u}).homology R n) ⟶
      ((A ⊔ B : K.Subcomplex) : SSet.{u}).homology R n :=
  biprod.desc (SSet.homologyMap (SSet.Subcomplex.homOfLE le_sup_left) R n)
    (SSet.homologyMap (SSet.Subcomplex.homOfLE le_sup_right) R n)

@[simp]
lemma mvLift_fst (n : ℕ) :
    mvLift A B R n ≫ biprod.fst =
      SSet.homologyMap (SSet.Subcomplex.homOfLE inf_le_left) R n :=
  biprod.lift_fst _ _

@[simp]
lemma mvLift_snd (n : ℕ) :
    mvLift A B R n ≫ biprod.snd =
      -SSet.homologyMap (SSet.Subcomplex.homOfLE inf_le_right) R n :=
  biprod.lift_snd _ _

@[simp]
lemma inl_mvDesc (n : ℕ) :
    biprod.inl ≫ mvDesc A B R n =
      SSet.homologyMap (SSet.Subcomplex.homOfLE le_sup_left) R n :=
  biprod.inl_desc _ _

@[simp]
lemma inr_mvDesc (n : ℕ) :
    biprod.inr ≫ mvDesc A B R n =
      SSet.homologyMap (SSet.Subcomplex.homOfLE le_sup_right) R n :=
  biprod.inr_desc _ _

lemma homologyMap_lift_homologyBiprodIso_hom (n : ℕ) :
    homologyMap (biprod.lift (ι₁ A B R) (-(ι₂ A B R))) n ≫ (homologyBiprodIso A B R n).hom =
      mvLift A B R n := by
  dsimp only [homologyBiprodIso, mvLift]
  apply biprod.hom_ext
  · simp [← homologyMap_comp]
  · simp [← homologyMap_comp, homologyMap_neg]

lemma homologyBiprodIso_inv_homologyMap_desc (n : ℕ) :
    (homologyBiprodIso A B R n).inv ≫ homologyMap (biprod.desc (j₁ A B R) (j₂ A B R)) n =
      mvDesc A B R n := by
  dsimp only [homologyBiprodIso, mvDesc]
  apply biprod.hom_ext'
  · simp [← homologyMap_comp]
  · simp [← homologyMap_comp]

@[reassoc (attr := simp)]
lemma mvδ_mvLift (n : ℕ) : mvδ A B R n ≫ mvLift A B R n = 0 := by
  rw [← homologyMap_lift_homologyBiprodIso_hom, mvδ_comp_assoc, zero_comp]

@[reassoc (attr := simp)]
lemma mvLift_mvDesc (n : ℕ) : mvLift A B R n ≫ mvDesc A B R n = 0 := by
  rw [← homologyMap_lift_homologyBiprodIso_hom, ← homologyBiprodIso_inv_homologyMap_desc,
    Category.assoc, Iso.hom_inv_id_assoc, homologyMap_lift_desc]

@[reassoc (attr := simp)]
lemma mvDesc_mvδ (n : ℕ) : mvDesc A B R (n + 1) ≫ mvδ A B R n = 0 := by
  rw [← homologyBiprodIso_inv_homologyMap_desc, Category.assoc, comp_mvδ, comp_zero]

theorem mv_exact₁' (n : ℕ) :
    (ShortComplex.mk (mvδ A B R n) (mvLift A B R n) (mvδ_mvLift A B R n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (mv_exact₁ A B R n)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (homologyBiprodIso A B R n)
    (by simp) (by simp [homologyMap_lift_homologyBiprodIso_hom])

theorem mv_exact₂' (n : ℕ) :
    (ShortComplex.mk (mvLift A B R n) (mvDesc A B R n) (mvLift_mvDesc A B R n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (mv_exact₂ A B R n)
  exact ShortComplex.isoMk (Iso.refl _) (homologyBiprodIso A B R n) (Iso.refl _)
    (by simp [homologyMap_lift_homologyBiprodIso_hom])
    (by simp [← homologyBiprodIso_inv_homologyMap_desc])

theorem mv_exact₃' (n : ℕ) :
    (ShortComplex.mk (mvDesc A B R (n + 1)) (mvδ A B R n) (mvDesc_mvδ A B R n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (mv_exact₃ A B R n)
  exact ShortComplex.isoMk (homologyBiprodIso A B R (n + 1)) (Iso.refl _) (Iso.refl _)
    (by simp [← homologyBiprodIso_inv_homologyMap_desc]) (by simp)

abbrev pairSup : SSetPair.{u} :=
  SSetPair.of (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B))

abbrev pairInf : SSetPair.{u} :=
  SSetPair.of (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B))

def cokerIso : (pairInf A B).chainComplex R ≅ (pairSup A B).chainComplex R :=
  pushoutCokernelIso (isPushout A B R) ((pairInf A B).isColimitCokernelCoforkChainComplex R)
    ((pairSup A B).isColimitCokernelCoforkChainComplex R)

@[reassoc (attr := simp)]
lemma chainComplexπ_cokerIso_hom :
    (pairInf A B).chainComplexπ R ≫ (cokerIso A B R).hom =
      j₂ A B R ≫ (pairSup A B).chainComplexπ R :=
  π_pushoutCokernelIso_hom (isPushout A B R) _ _

def homologyCokerIso (n : ℕ) : (pairInf A B).homology R n ≅ (pairSup A B).homology R n :=
  homologyMapIso (cokerIso A B R) n

@[reassoc]
lemma chainComplexMap_right_chainComplexπ {P P' : SSetPair.{u}} (φ : P ⟶ P') :
    SSet.chainComplexMap φ.right R ≫ P'.chainComplexπ R =
      P.chainComplexπ R ≫ SSetPair.chainComplexMap φ R :=
  ((SSetPair.chainComplexFunctorπ (ModuleCat.{u} ℤ)).app R).naturality φ

@[reassoc]
lemma homologyMap_right_homologyπ {P P' : SSetPair.{u}} (φ : P ⟶ P') (n : ℕ) :
    SSet.homologyMap φ.right R n ≫ P'.homologyπ R n =
      P.homologyπ R n ≫ SSetPair.homologyMap φ R n := by
  simp only [SSetPair.homologyπ, SSetPair.homologyMap, SSet.homologyMap, ← homologyMap_comp,
    chainComplexMap_right_chainComplexπ]

def excisionPairMap : pairInf A B ⟶ pairSup A B :=
  SSetPair.homMk (SSet.Subcomplex.homOfLE inf_le_left) (SSet.Subcomplex.homOfLE le_sup_right)
    rfl

lemma excisionPairMap_right :
    (excisionPairMap A B).right = SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B) := rfl

lemma excisionPairMap_left :
    (excisionPairMap A B).left = SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A) := rfl

lemma chainComplexMap_excisionPairMap :
    SSetPair.chainComplexMap (excisionPairMap A B) R = (cokerIso A B R).hom := by
  apply Cofork.IsColimit.hom_ext ((pairInf A B).isColimitCokernelCoforkChainComplex R)
  dsimp only [SSetPair.cokernelCoforkChainComplex]
  rw [Cofork.π_ofπ, ← chainComplexMap_right_chainComplexπ, chainComplexπ_cokerIso_hom]
  rfl

instance isIso_chainComplexMap_excisionPairMap :
    IsIso (SSetPair.chainComplexMap (excisionPairMap A B) R) := by
  rw [chainComplexMap_excisionPairMap]
  infer_instance

lemma homologyMap_excisionPairMap (n : ℕ) :
    SSetPair.homologyMap (excisionPairMap A B) R n = (homologyCokerIso A B R n).hom := by
  simp only [SSetPair.homologyMap, chainComplexMap_excisionPairMap, homologyCokerIso,
    homologyMapIso_hom]

instance isIso_homologyMap_excisionPairMap (n : ℕ) :
    IsIso (SSetPair.homologyMap (excisionPairMap A B) R n) := by
  rw [homologyMap_excisionPairMap]
  infer_instance

@[reassoc]
lemma homologyπ_homologyCokerIso_hom (n : ℕ) :
    (pairInf A B).homologyπ R n ≫ (homologyCokerIso A B R n).hom =
      SSet.homologyMap (excisionPairMap A B).right R n ≫ (pairSup A B).homologyπ R n := by
  rw [← homologyMap_excisionPairMap, homologyMap_right_homologyπ]

end DifferentialGeometry.Topology.SingularPair
