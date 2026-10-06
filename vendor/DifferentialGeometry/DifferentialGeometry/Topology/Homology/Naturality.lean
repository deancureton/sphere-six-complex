module

public import DifferentialGeometry.Topology.Homology.SingularPair
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

@[expose] public section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex Simplicial

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

variable (R : ModuleCat.{u} ℤ)

abbrev singularHomologyMap {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) : singularHomology R X n ⟶ singularHomology R Y n :=
  ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj R).map f

lemma singularHomologyMap_eq_homologyMap {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) :
    singularHomologyMap R f n = homologyMap ((singularChainFunctor R).map f) n := rfl

lemma singularHomologyMap_id (X : TopCat.{u}) (n : ℕ) : singularHomologyMap R (𝟙 X) n = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

@[reassoc]
lemma singularHomologyMap_comp {X Y W : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ W) (n : ℕ) :
    singularHomologyMap R (f ≫ g) n = singularHomologyMap R f n ≫ singularHomologyMap R g n :=
  CategoryTheory.Functor.map_comp _ _ _

lemma inclMap_eq_singularHomologyMap (X : TopCat.{u}) (A : Set X) (n : ℕ) :
    inclMap R X A n = singularHomologyMap R (incl X A) n := rfl

lemma homologyIso_hom {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    (homologyIso R e n).hom = singularHomologyMap R (TopCat.ofHom e.toFun) n := rfl

instance isIso_singularHomologyMap_of_homotopyEquiv {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    IsIso (singularHomologyMap R (TopCat.ofHom e.toFun) n) :=
  ⟨(homologyIso R e n).inv, (homologyIso R e n).hom_inv_id, (homologyIso R e n).inv_hom_id⟩

def restr {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y) (hf : Set.MapsTo f A B) :
    TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom ⟨hf.restrict, by fun_prop⟩

@[simp]
lemma restr_apply {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y) (hf : Set.MapsTo f A B)
    (a : A) : restr f hf a = ⟨f a, hf a.2⟩ := rfl

lemma restr_comp_incl {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) : restr f hf ≫ incl Y B = incl X A ≫ f := rfl

lemma pairMap_left {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) : (pairMap f hf).left = TopCat.toSSet.map (restr f hf) := rfl

lemma pairMap_right {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) : (pairMap f hf).right = TopCat.toSSet.map f := rfl

lemma restr_id (X : TopCat.{u}) (A : Set X) (hf : Set.MapsTo (𝟙 X) A A) :
    restr (𝟙 X) hf = 𝟙 (TopCat.of A) := by
  ext x
  rfl

lemma restr_comp {X Y W : TopCat.{u}} {A : Set X} {B : Set Y} {D : Set W}
    (f : X ⟶ Y) (g : Y ⟶ W) (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B D)
    (hfg : Set.MapsTo (f ≫ g) A D) :
    restr (f ≫ g) hfg = restr f hf ≫ restr g hg := by
  ext x
  rfl

lemma pairMap_id (X : TopCat.{u}) (A : Set X) (hf : Set.MapsTo (𝟙 X) A A) :
    pairMap (𝟙 X) hf = 𝟙 (pair X A) := by
  refine MorphismProperty.Comma.Hom.ext' (CommaMorphism.ext ?_ ?_)
  · change TopCat.toSSet.map (restr (𝟙 X) hf) = 𝟙 _
    rw [restr_id, CategoryTheory.Functor.map_id]
  · rfl

lemma pairMap_comp {X Y W : TopCat.{u}} {A : Set X} {B : Set Y} {D : Set W}
    (f : X ⟶ Y) (g : Y ⟶ W) (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B D)
    (hfg : Set.MapsTo (f ≫ g) A D) :
    pairMap (f ≫ g) hfg = pairMap f hf ≫ pairMap g hg := by
  refine MorphismProperty.Comma.Hom.ext' (CommaMorphism.ext ?_ ?_)
  · change TopCat.toSSet.map (restr (f ≫ g) hfg) =
      TopCat.toSSet.map (restr f hf) ≫ TopCat.toSSet.map (restr g hg)
    rw [restr_comp f g hf hg hfg, CategoryTheory.Functor.map_comp]
  · change TopCat.toSSet.map (f ≫ g) = TopCat.toSSet.map f ≫ TopCat.toSSet.map g
    rw [CategoryTheory.Functor.map_comp]

theorem relativeHomologyMap_id (X : TopCat.{u}) (A : Set X) (hf : Set.MapsTo (𝟙 X) A A) (n : ℕ) :
    relativeHomologyMap R (𝟙 X) hf n = 𝟙 _ := by
  rw [relativeHomologyMap, pairMap_id, SSetPair.homologyMap_id]

theorem relativeHomologyMap_comp {X Y W : TopCat.{u}} {A : Set X} {B : Set Y} {D : Set W}
    (f : X ⟶ Y) (g : Y ⟶ W) (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B D)
    (hfg : Set.MapsTo (f ≫ g) A D) (n : ℕ) :
    relativeHomologyMap R (f ≫ g) hfg n = relativeHomologyMap R f hf n ≫ relativeHomologyMap R g hg n := by
  rw [relativeHomologyMap, pairMap_comp f g hf hg hfg, SSetPair.homologyMap_comp]

@[reassoc (attr := simp)]
lemma relativeHomologyMap_id_comp {X : TopCat.{u}} {A B D : Set X}
    (hAB : Set.MapsTo (𝟙 X) A B) (hBD : Set.MapsTo (𝟙 X) B D) (n : ℕ) :
    relativeHomologyMap R (𝟙 X) hAB n ≫ relativeHomologyMap R (𝟙 X) hBD n =
      relativeHomologyMap R (𝟙 X) (fun _ hx => hBD (hAB hx)) n := by
  simpa only [Category.id_comp] using
    (relativeHomologyMap_comp R (𝟙 X) (𝟙 X) hAB hBD (fun _ hx => hBD (hAB hx)) n).symm

def scMap {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y) (hf : Set.MapsTo f A B) :
    (pair X A).chainComplexShortComplex R ⟶ (pair Y B).chainComplexShortComplex R where
  τ₁ := (singularChainFunctor R).map (restr f hf)
  τ₂ := (singularChainFunctor R).map f
  τ₃ := SSetPair.chainComplexMap (pairMap f hf) R
  comm₁₂ := ((SSetPair.chainComplexFunctorLeftToRight _).app R).naturality (pairMap f hf)
  comm₂₃ := ((SSetPair.chainComplexFunctorπ _).app R).naturality (pairMap f hf)

theorem δ_natural {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) (n : ℕ) :
    δ R X A n ≫ singularHomologyMap R (restr f hf) n = relativeHomologyMap R f hf (n + 1) ≫ δ R Y B n :=
  HomologySequence.δ_naturality (scMap R f hf) _ _ (n + 1) n rfl

theorem δ_natural' {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) (n : ℕ) :
    δ R X A n ≫ homologyMap ((singularChainFunctor R).map (restr f hf)) n = relativeHomologyMap R f hf (n + 1) ≫ δ R Y B n :=
  δ_natural R f hf n

lemma chainComplexπ_natural {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) :
    ((SSetPair.chainComplexFunctorRight _).obj R).map (pairMap f hf) ≫
      ((SSetPair.chainComplexFunctorπ _).app R).app (pair Y B) =
    ((SSetPair.chainComplexFunctorπ _).app R).app (pair X A) ≫
      ((SSetPair.chainComplexFunctor _).obj R).map (pairMap f hf) :=
  ((SSetPair.chainComplexFunctorπ _).app R).naturality (pairMap f hf)

theorem relπ_natural {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) (n : ℕ) :
    relπ R X A n ≫ relativeHomologyMap R f hf n = singularHomologyMap R f n ≫ relπ R Y B n := by
  have h := congrArg (fun φ => HomologicalComplex.homologyMap φ n) (chainComplexπ_natural R f hf)
  simp only [homologyMap_comp] at h
  exact h.symm

theorem relπ_natural' {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) (n : ℕ) :
    relπ R X A n ≫ relativeHomologyMap R f hf n = homologyMap ((singularChainFunctor R).map f) n ≫ relπ R Y B n :=
  relπ_natural R f hf n

theorem inclMap_natural {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) (n : ℕ) :
    inclMap R X A n ≫ singularHomologyMap R f n = singularHomologyMap R (restr f hf) n ≫ inclMap R Y B n := by
  have h := congrArg (fun φ => HomologicalComplex.homologyMap φ n)
    (((SSetPair.chainComplexFunctorLeftToRight _).app R).naturality (pairMap f hf))
  simp only [homologyMap_comp] at h
  exact h.symm

theorem inclMap_natural' {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) (n : ℕ) :
    inclMap R X A n ≫ homologyMap ((singularChainFunctor R).map f) n =
      homologyMap ((singularChainFunctor R).map (restr f hf)) n ≫ inclMap R Y B n :=
  inclMap_natural R f hf n

abbrev ε (X : TopCat.{u}) : singularHomology R X 0 ⟶ R := X.singularHomology₀ε R

@[reassoc]
lemma ι_inv_iCycles (X : SSet.{u}) (x : X _⦋0⦌) :
    X.ιChainComplex x ≫ inv ((X.chainComplex R).iCycles 0) =
      (X.chainComplex R).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) := by
  rw [← cancel_mono ((X.chainComplex R).iCycles 0)]
  simp

lemma homology₀ε_natural {X Y : SSet.{u}} (f : X ⟶ Y) :
    SSet.homologyMap f R 0 ≫ Y.homology₀ε R = X.homology₀ε R := by
  rw [SSet.homologyMap, ← cancel_epi ((X.chainComplex R).homologyπ 0), homologyπ_naturality_assoc,
    ← cancel_epi (inv ((X.chainComplex R).iCycles 0))]
  apply SSet.chainComplex_hom_ext
  intro x
  rw [ι_inv_iCycles_assoc, ι_inv_iCycles_assoc, liftCycles_comp_cyclesMap_assoc]
  simp

@[reassoc (attr := simp)]
theorem ε_natural {X Y : TopCat.{u}} (f : X ⟶ Y) : singularHomologyMap R f 0 ≫ ε R Y = ε R X :=
  homology₀ε_natural R (TopCat.toSSet.map f)

theorem ε_natural' {X Y : TopCat.{u}} (f : X ⟶ Y) :
    homologyMap ((singularChainFunctor R).map f) 0 ≫ Y.singularHomology₀ε R = X.singularHomology₀ε R :=
  ε_natural R f

@[reassoc (attr := simp)]
theorem inclMap_ε (X : TopCat.{u}) (A : Set X) : inclMap R X A 0 ≫ ε R X = ε R (TopCat.of A) :=
  ε_natural R (incl X A)

theorem isIso_ε_of_pathConnected (X : TopCat.{u}) [PathConnectedSpace X] : IsIso (ε R X) :=
  inferInstance

theorem isIso_ε_of_contractible (X : Type u) [TopologicalSpace X] [ContractibleSpace X] :
    IsIso (ε R (TopCat.of X)) :=
  inferInstance

abbrev reducedHomologyZero (X : TopCat.{u}) : ModuleCat.{u} ℤ := kernel (ε R X)

abbrev reducedHomologyZeroInclusion (X : TopCat.{u}) : reducedHomologyZero R X ⟶ singularHomology R X 0 := kernel.ι (ε R X)

instance (X : TopCat.{u}) : Mono (reducedHomologyZeroInclusion R X) := inferInstance

@[reassoc]
lemma reducedHomologyZeroInclusion_ε (X : TopCat.{u}) : reducedHomologyZeroInclusion R X ≫ ε R X = 0 := kernel.condition _

def reducedHomologyZeroMap {X Y : TopCat.{u}} (f : X ⟶ Y) : reducedHomologyZero R X ⟶ reducedHomologyZero R Y :=
  kernel.lift _ (reducedHomologyZeroInclusion R X ≫ singularHomologyMap R f 0) (by rw [Category.assoc, ε_natural, kernel.condition])

@[reassoc (attr := simp)]
lemma reducedHomologyZeroMap_ι {X Y : TopCat.{u}} (f : X ⟶ Y) :
    reducedHomologyZeroMap R f ≫ reducedHomologyZeroInclusion R Y = reducedHomologyZeroInclusion R X ≫ singularHomologyMap R f 0 :=
  kernel.lift_ι _ _ _

@[simp]
lemma reducedHomologyZeroMap_id (X : TopCat.{u}) : reducedHomologyZeroMap R (𝟙 X) = 𝟙 _ := by
  rw [← cancel_mono (reducedHomologyZeroInclusion R X), reducedHomologyZeroMap_ι, singularHomologyMap_id, Category.comp_id, Category.id_comp]

@[reassoc]
lemma reducedHomologyZeroMap_comp {X Y W : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ W) :
    reducedHomologyZeroMap R (f ≫ g) = reducedHomologyZeroMap R f ≫ reducedHomologyZeroMap R g := by
  rw [← cancel_mono (reducedHomologyZeroInclusion R W), reducedHomologyZeroMap_ι, singularHomologyMap_comp, Category.assoc, reducedHomologyZeroMap_ι,
    reducedHomologyZeroMap_ι_assoc]

lemma mono_reducedHomologyZeroMap_of_mono {X Y : TopCat.{u}} (f : X ⟶ Y) [Mono (singularHomologyMap R f 0)] :
    Mono (reducedHomologyZeroMap R f) :=
  mono_of_mono_fac (reducedHomologyZeroMap_ι R f)

def reducedHomologyZeroMapIso {X Y : TopCat.{u}} (f : X ⟶ Y) [IsIso (singularHomologyMap R f 0)] : reducedHomologyZero R X ≅ reducedHomologyZero R Y :=
  kernel.mapIso (ε R X) (ε R Y) (asIso (singularHomologyMap R f 0)) (Iso.refl R)
    (by rw [Iso.refl_hom, Category.comp_id, asIso_hom, ε_natural])

lemma reducedHomologyZeroMapIso_hom {X Y : TopCat.{u}} (f : X ⟶ Y) [IsIso (singularHomologyMap R f 0)] :
    (reducedHomologyZeroMapIso R f).hom = reducedHomologyZeroMap R f := rfl

instance isIso_reducedHomologyZeroMap {X Y : TopCat.{u}} (f : X ⟶ Y) [IsIso (singularHomologyMap R f 0)] :
    IsIso (reducedHomologyZeroMap R f) :=
  ⟨(reducedHomologyZeroMapIso R f).inv, (reducedHomologyZeroMapIso R f).hom_inv_id, (reducedHomologyZeroMapIso R f).inv_hom_id⟩

def reducedHomologyZeroIso {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) : reducedHomologyZero R (TopCat.of X) ≅ reducedHomologyZero R (TopCat.of Y) :=
  reducedHomologyZeroMapIso R (TopCat.ofHom e.toFun)

lemma reducedHomologyZeroIso_hom {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) :
    (reducedHomologyZeroIso R e).hom = reducedHomologyZeroMap R (TopCat.ofHom e.toFun) := rfl

def reducedHomologyZeroIsoOfHomeomorph {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    reducedHomologyZero R (TopCat.of X) ≅ reducedHomologyZero R (TopCat.of Y) :=
  reducedHomologyZeroIso R e.toHomotopyEquiv

theorem isZero_reducedHomologyZero_of_pathConnected (X : TopCat.{u}) [PathConnectedSpace X] :
    IsZero (reducedHomologyZero R X) :=
  (isZero_zero _).of_iso (kernel.ofMono (ε R X))

theorem isZero_reducedHomologyZero_of_contractible (X : Type u) [TopologicalSpace X] [ContractibleSpace X] :
    IsZero (reducedHomologyZero R (TopCat.of X)) :=
  isZero_reducedHomologyZero_of_pathConnected R (TopCat.of X)

section two

variable {ι : Type u} (a b : ι)

def prj (c : ι) : ∐ (fun _ : ι ↦ R) ⟶ R := by
  classical
  exact Sigma.desc (fun i ↦ if i = c then 𝟙 R else 0)

@[reassoc (attr := simp)]
lemma ι_prj_self (c : ι) : Sigma.ι (fun _ : ι ↦ R) c ≫ prj R c = 𝟙 R := by
  simp [prj]

@[reassoc]
lemma ι_prj_ne {i c : ι} (h : i ≠ c) : Sigma.ι (fun _ : ι ↦ R) i ≫ prj R c = 0 := by
  simp [prj, h]

lemma sub_comp_sigmaDesc_id :
    (Sigma.ι (fun _ : ι ↦ R) a - Sigma.ι (fun _ : ι ↦ R) b) ≫ Sigma.desc (fun _ : ι ↦ 𝟙 R) = 0 := by
  simp [Preadditive.sub_comp]

variable (hab : a ≠ b) (hcov : ∀ i, i = a ∨ i = b)
include hab hcov

lemma prj_total : prj R a ≫ Sigma.ι (fun _ : ι ↦ R) a + prj R b ≫ Sigma.ι (fun _ : ι ↦ R) b =
    𝟙 _ := by
  ext i
  rcases hcov i with rfl | rfl
  · simp [Preadditive.comp_add, ι_prj_ne_assoc R hab]
  · simp [Preadditive.comp_add, ι_prj_ne_assoc R hab.symm]

lemma sigmaDesc_id_eq : Sigma.desc (fun _ : ι ↦ 𝟙 R) = prj R a + prj R b := by
  ext i
  rcases hcov i with rfl | rfl
  · simp [Preadditive.comp_add, ι_prj_ne R hab]
  · simp [Preadditive.comp_add, ι_prj_ne R hab.symm]

def isLimitKernelForkTwo :
    IsLimit (KernelFork.ofι _ (sub_comp_sigmaDesc_id R a b)) :=
  KernelFork.IsLimit.ofι _ _ (fun g _ ↦ g ≫ prj R a)
    (fun g hg ↦ by
      have h1 : g ≫ prj R a + g ≫ prj R b = 0 := by
        rw [← Preadditive.comp_add, ← sigmaDesc_id_eq R a b hab hcov, hg]
      have h2 : g ≫ prj R b = -(g ≫ prj R a) := by
        rw [eq_neg_iff_add_eq_zero, add_comm, h1]
      calc (g ≫ prj R a) ≫ (Sigma.ι (fun _ : ι ↦ R) a - Sigma.ι (fun _ : ι ↦ R) b)
          = g ≫ prj R a ≫ Sigma.ι (fun _ : ι ↦ R) a + g ≫ prj R b ≫ Sigma.ι (fun _ : ι ↦ R) b := by
            rw [Preadditive.comp_sub, ← Category.assoc, ← Category.assoc, h2,
              Preadditive.neg_comp, sub_eq_add_neg]
        _ = g := by
            rw [← Preadditive.comp_add, prj_total R a b hab hcov, Category.comp_id])
    (fun g hg m hm ↦ by
      rw [← hm, Category.assoc, Preadditive.sub_comp, ι_prj_self, ι_prj_ne R hab.symm, sub_zero,
        Category.comp_id])

def kernelSigmaDescTwoIso : kernel (Sigma.desc (fun _ : ι ↦ 𝟙 R)) ≅ R :=
  (kernelIsKernel _).conePointUniqueUpToIso (isLimitKernelForkTwo R a b hab hcov)

end two

def reducedHomologyZeroIsoKernelSigmaDesc (X : TopCat.{u}) :
    reducedHomologyZero R X ≅ kernel (Sigma.desc (fun _ : ZerothHomotopy X ↦ 𝟙 R)) :=
  kernel.mapIso (ε R X) _ (X.singularHomology₀Iso R) (Iso.refl R)
    (by rw [Iso.refl_hom, Category.comp_id, TopCat.singularHomology₀Iso_sigma_desc_id])

def reducedHomologyZeroIsoOfTwoPathComponents (X : TopCat.{u}) (a b : ZerothHomotopy X) (hab : a ≠ b)
    (hcov : ∀ i, i = a ∨ i = b) : reducedHomologyZero R X ≅ R :=
  reducedHomologyZeroIsoKernelSigmaDesc R X ≪≫ kernelSigmaDescTwoIso R a b hab hcov

lemma _root_.ZerothHomotopy.dg_mk_injective_of_totallyDisconnectedSpace {X : Type u}
    [TopologicalSpace X] [TotallyDisconnectedSpace X] :
    Function.Injective (ZerothHomotopy.mk (X := X)) := by
  intro x y h
  obtain ⟨p⟩ : Joined x y := Quotient.exact h
  exact (isPreconnected_range p.continuous).subsingleton ⟨0, p.source⟩ ⟨1, p.target⟩

def _root_.ZerothHomotopy.equivOfTotallyDisconnectedSpace (X : Type u) [TopologicalSpace X]
    [TotallyDisconnectedSpace X] : X ≃ ZerothHomotopy X :=
  Equiv.ofBijective ZerothHomotopy.mk
    ⟨ZerothHomotopy.dg_mk_injective_of_totallyDisconnectedSpace, ZerothHomotopy.mk_surjective⟩

def reducedHomologyZeroIsoOfTwoPoints (X : TopCat.{u}) [TotallyDisconnectedSpace X] (x y : X) (hxy : x ≠ y)
    (hcov : ∀ z, z = x ∨ z = y) : reducedHomologyZero R X ≅ R :=
  reducedHomologyZeroIsoOfTwoPathComponents R X (.mk x) (.mk y)
    (fun h ↦ hxy (ZerothHomotopy.dg_mk_injective_of_totallyDisconnectedSpace h))
    (fun i ↦ by
      obtain ⟨z, rfl⟩ := ZerothHomotopy.mk_surjective i
      rcases hcov z with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl)

def reducedHomologyZeroUliftFinTwoIso : reducedHomologyZero R (TopCat.of (ULift.{u} (Fin 2))) ≅ R :=
  reducedHomologyZeroIsoOfTwoPoints R (TopCat.of (ULift.{u} (Fin 2))) ⟨0⟩ ⟨1⟩ (by simp)
    (fun z ↦ by
      rcases z with ⟨z⟩
      fin_cases z
      · exact Or.inl rfl
      · exact Or.inr rfl)

section kernelExact

variable {S : ShortComplex (ModuleCat.{u} ℤ)} (hS : S.Exact)

lemma kernelLift_comp_zero₃ {T : ModuleCat.{u} ℤ} (ε₃ : S.X₃ ⟶ T) (h : S.g ≫ ε₃ = 0) :
    S.f ≫ kernel.lift ε₃ S.g h = 0 := by
  rw [← cancel_mono (kernel.ι ε₃), Category.assoc, kernel.lift_ι, S.zero, zero_comp]

include hS in
lemma exact_kernelLift₃ {T : ModuleCat.{u} ℤ} (ε₃ : S.X₃ ⟶ T) (h : S.g ≫ ε₃ = 0) :
    (ShortComplex.mk S.f (kernel.lift ε₃ S.g h) (kernelLift_comp_zero₃ ε₃ h)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff] at hS ⊢
  intro x₂ hx₂
  change kernel.lift ε₃ S.g h x₂ = 0 at hx₂
  apply hS
  have := congrArg (kernel.ι ε₃) hx₂
  rwa [← ModuleCat.comp_apply, kernel.lift_ι, map_zero] at this

section
variable {T₂ T₃ : ModuleCat.{u} ℤ} (ε₂ : S.X₂ ⟶ T₂) (ε₃ : S.X₃ ⟶ T₃) (t : T₂ ⟶ T₃) [Mono t]
  (h : S.g ≫ ε₃ = ε₂ ≫ t)
include h

lemma f_comp_eq_zero_of_mono : S.f ≫ ε₂ = 0 := by
  rw [← cancel_mono t, Category.assoc, ← h, ← Category.assoc, S.zero, zero_comp, zero_comp]

omit [Mono t] in
lemma ι_comp_g_comp_eq_zero : (kernel.ι ε₂ ≫ S.g) ≫ ε₃ = 0 := by
  rw [Category.assoc, h, kernel.condition_assoc, zero_comp]

lemma kernelLift_comp_zero₂₃ :
    kernel.lift ε₂ S.f (f_comp_eq_zero_of_mono ε₂ ε₃ t h) ≫
      kernel.lift ε₃ (kernel.ι ε₂ ≫ S.g) (ι_comp_g_comp_eq_zero ε₂ ε₃ t h) = 0 := by
  rw [← cancel_mono (kernel.ι ε₃), Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc, S.zero,
    zero_comp]

include hS in
lemma exact_kernelLift₂₃ :
    (ShortComplex.mk _ _ (kernelLift_comp_zero₂₃ ε₂ ε₃ t h)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff] at hS ⊢
  intro x₂ hx₂
  change kernel.lift ε₃ (kernel.ι ε₂ ≫ S.g) _ x₂ = 0 at hx₂
  have h1 : S.g (kernel.ι ε₂ x₂) = 0 := by
    have := congrArg (kernel.ι ε₃) hx₂
    rwa [← ModuleCat.comp_apply, kernel.lift_ι, map_zero, ModuleCat.comp_apply] at this
  obtain ⟨x₁, hx₁⟩ := hS _ h1
  refine ⟨x₁, ?_⟩
  apply (ModuleCat.mono_iff_injective (kernel.ι ε₂)).1 inferInstance
  change (kernel.lift ε₂ S.f _ ≫ kernel.ι ε₂) x₁ = kernel.ι ε₂ x₂
  rw [kernel.lift_ι]
  exact hx₁

end

section
variable {T₁ T₂ : ModuleCat.{u} ℤ} (ε₁ : S.X₁ ⟶ T₁) (ε₂ : S.X₂ ⟶ T₂) (t : T₁ ⟶ T₂) [Mono t]
  (h : S.f ≫ ε₂ = ε₁ ≫ t)
include h

omit [Mono t] in
lemma ι_comp_f_comp_eq_zero : (kernel.ι ε₁ ≫ S.f) ≫ ε₂ = 0 := by
  rw [Category.assoc, h, kernel.condition_assoc, zero_comp]

omit [Mono t] in
lemma kernelLift_comp_zero₁₂ :
    kernel.lift ε₂ (kernel.ι ε₁ ≫ S.f) (ι_comp_f_comp_eq_zero ε₁ ε₂ t h) ≫
      (kernel.ι ε₂ ≫ S.g) = 0 := by
  rw [kernel.lift_ι_assoc, Category.assoc, S.zero, comp_zero]

include hS in
lemma exact_kernelLift₁₂ :
    (ShortComplex.mk _ _ (kernelLift_comp_zero₁₂ ε₁ ε₂ t h)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff] at hS ⊢
  intro x₂ hx₂
  change (kernel.ι ε₂ ≫ S.g) x₂ = 0 at hx₂
  rw [ModuleCat.comp_apply] at hx₂
  obtain ⟨x₁, hx₁⟩ := hS _ hx₂
  have hx₁' : ε₁ x₁ = 0 := by
    apply (ModuleCat.mono_iff_injective t).1 inferInstance
    rw [map_zero]
    calc t (ε₁ x₁) = (S.f ≫ ε₂) x₁ := by rw [h, ModuleCat.comp_apply]
      _ = ε₂ (kernel.ι ε₂ x₂) := by rw [ModuleCat.comp_apply, hx₁]
      _ = (kernel.ι ε₂ ≫ ε₂) x₂ := by rw [ModuleCat.comp_apply]
      _ = 0 := by rw [kernel.condition]; simp
  let y := (ModuleCat.kernelIsoKer ε₁).inv ⟨x₁, LinearMap.mem_ker.2 hx₁'⟩
  have hy : kernel.ι ε₁ y = x₁ := by
    change ((ModuleCat.kernelIsoKer ε₁).inv ≫ kernel.ι ε₁) ⟨x₁, _⟩ = x₁
    rw [ModuleCat.kernelIsoKer_inv_kernel_ι]
    rfl
  refine ⟨y, ?_⟩
  apply (ModuleCat.mono_iff_injective (kernel.ι ε₂)).1 inferInstance
  change (kernel.lift ε₂ (kernel.ι ε₁ ≫ S.f) _ ≫ kernel.ι ε₂) y = kernel.ι ε₂ x₂
  rw [kernel.lift_ι, ModuleCat.comp_apply, hy, hx₁]

end

end kernelExact

variable (X : TopCat.{u}) (A : Set X)

@[reassoc (attr := simp)]
theorem δ_comp_ε : δ R X A 0 ≫ ε R (TopCat.of A) = 0 := by
  have h : δ R X A 0 ≫ inclMap R X A 0 = 0 := (pair X A).homologyδ_comp R 1 0 rfl
  rw [← inclMap_ε, ← Category.assoc, h, zero_comp]

def δred : relativeHomology R X A 1 ⟶ reducedHomologyZero R (TopCat.of A) :=
  kernel.lift _ (δ R X A 0) (δ_comp_ε R X A)

@[reassoc (attr := simp)]
lemma δred_ι : δred R X A ≫ reducedHomologyZeroInclusion R (TopCat.of A) = δ R X A 0 :=
  kernel.lift_ι _ _ _

@[reassoc (attr := simp)]
lemma δred_comp_reducedHomologyZeroMap : δred R X A ≫ reducedHomologyZeroMap R (incl X A) = 0 := by
  rw [← cancel_mono (reducedHomologyZeroInclusion R X), Category.assoc, reducedHomologyZeroMap_ι, δred_ι_assoc, zero_comp]
  exact (pair X A).homologyδ_comp R 1 0 rfl

@[reassoc (attr := simp)]
lemma singularHomologyMap_incl_relπ (n : ℕ) :
    singularHomologyMap R (incl X A) n ≫ relπ R X A n = 0 :=
  (pair X A).homologyMap_hom_homologyπ R n

@[reassoc]
lemma reducedHomologyZeroMap_comp_relπ : reducedHomologyZeroMap R (incl X A) ≫ (reducedHomologyZeroInclusion R X ≫ relπ R X A 0) = 0 := by
  simp

@[reassoc (attr := simp)]
lemma relπ_comp_δred : relπ R X A 1 ≫ δred R X A = 0 := by
  rw [← cancel_mono (reducedHomologyZeroInclusion R (TopCat.of A)), Category.assoc, δred_ι, zero_comp]
  exact (pair X A).comp_homologyδ R 1 0 rfl

theorem les_red_exact₁ :
    (ShortComplex.mk (δred R X A) (reducedHomologyZeroMap R (incl X A)) (δred_comp_reducedHomologyZeroMap R X A)).Exact :=
  exact_kernelLift₂₃ (les_exact₁ R X A 0) (ε R (TopCat.of A)) (ε R X) (𝟙 R)
    (by rw [Category.comp_id]; exact inclMap_ε R X A)

theorem les_red_exact₂ :
    (ShortComplex.mk (reducedHomologyZeroMap R (incl X A)) (reducedHomologyZeroInclusion R X ≫ relπ R X A 0)
      (reducedHomologyZeroMap_comp_relπ R X A)).Exact :=
  exact_kernelLift₁₂ (les_exact₂ R X A 0) (ε R (TopCat.of A)) (ε R X) (𝟙 R)
    (by rw [Category.comp_id]; exact inclMap_ε R X A)

theorem les_red_exact₃ :
    (ShortComplex.mk (relπ R X A 1) (δred R X A) (relπ_comp_δred R X A)).Exact :=
  exact_kernelLift₃ (les_exact₃ R X A 0) (ε R (TopCat.of A)) (δ_comp_ε R X A)

end DifferentialGeometry.Topology.SingularPair
