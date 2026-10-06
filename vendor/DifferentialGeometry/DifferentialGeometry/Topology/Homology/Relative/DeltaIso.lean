module

public import DifferentialGeometry.Topology.Homology.Spheres.SphereHomology
public import DifferentialGeometry.Topology.Homology.Relative.PairVanishing

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

variable (R : ModuleCat.{u} ℤ)

theorem isIso_δ_of_isZero (X : TopCat.{u}) (A : Set X) (i : ℕ)
    (h₁ : IsZero (singularHomology R X (i + 2))) (h₂ : IsZero (singularHomology R X (i + 1))) :
    IsIso (δ R X A (i + 1)) := by
  have hmono : Mono (δ R X A (i + 1)) :=
    (les_exact₃ R X A (i + 1)).mono_g_iff.2 (h₁.eq_zero_of_src _)
  have hepi : Epi (δ R X A (i + 1)) :=
    (les_exact₁ R X A (i + 1)).epi_f_iff.2 (h₂.eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

theorem isIso_δred_of_isZero (X : TopCat.{u}) (A : Set X)
    (h₁ : IsZero (singularHomology R X 1)) (h₂ : IsZero (reducedHomologyZero R X)) : IsIso (δred R X A) := by
  have hmono : Mono (δred R X A) :=
    (les_red_exact₃ R X A).mono_g_iff.2 (h₁.eq_zero_of_src _)
  have hepi : Epi (δred R X A) :=
    (les_red_exact₁ R X A).epi_f_iff.2 (h₂.eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

def δIsoOfIsZero (X : TopCat.{u}) (A : Set X) (i : ℕ)
    (h₁ : IsZero (singularHomology R X (i + 2))) (h₂ : IsZero (singularHomology R X (i + 1))) :
    relativeHomology R X A (i + 2) ≅ singularHomology R (TopCat.of A) (i + 1) :=
  have := isIso_δ_of_isZero R X A i h₁ h₂
  asIso (δ R X A (i + 1))

lemma δIsoOfIsZero_hom (X : TopCat.{u}) (A : Set X) (i : ℕ)
    (h₁ : IsZero (singularHomology R X (i + 2))) (h₂ : IsZero (singularHomology R X (i + 1))) :
    (δIsoOfIsZero R X A i h₁ h₂).hom = δ R X A (i + 1) := rfl

def δredIsoOfIsZero (X : TopCat.{u}) (A : Set X)
    (h₁ : IsZero (singularHomology R X 1)) (h₂ : IsZero (reducedHomologyZero R X)) :
    relativeHomology R X A 1 ≅ reducedHomologyZero R (TopCat.of A) :=
  have := isIso_δred_of_isZero R X A h₁ h₂
  asIso (δred R X A)

lemma δredIsoOfIsZero_hom (X : TopCat.{u}) (A : Set X)
    (h₁ : IsZero (singularHomology R X 1)) (h₂ : IsZero (reducedHomologyZero R X)) :
    (δredIsoOfIsZero R X A h₁ h₂).hom = δred R X A := rfl

theorem δred_natural {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) :
    δred R X A ≫ reducedHomologyZeroMap R (restr f hf) = relativeHomologyMap R f hf 1 ≫ δred R Y B := by
  rw [← cancel_mono (reducedHomologyZeroInclusion R (TopCat.of B)), Category.assoc, Category.assoc, reducedHomologyZeroMap_ι,
    δred_ι, δred_ι_assoc]
  exact δ_natural R f hf 0

theorem isZero_relativeHomology_zero_of_epi (X : TopCat.{u}) (A : Set X) (h : Epi (inclMap R X A 0)) :
    IsZero (relativeHomology R X A 0) := by
  have hπ : relπ R X A 0 = 0 := (les_exact₂ R X A 0).epi_f_iff.1 h
  have : Epi (relπ R X A 0) := inferInstanceAs (Epi ((pair X A).homologyπ R 0))
  exact IsZero.of_epi_eq_zero _ hπ

theorem epi_inclMap_zero_of_pathConnected (X : TopCat.{u}) (A : Set X) [PathConnectedSpace X]
    [Nonempty A] : Epi (inclMap R X A 0) := by
  have hε : IsIso (ε R X) := isIso_ε_of_pathConnected R X
  have hA : Nonempty (TopCat.of A) := inferInstanceAs (Nonempty A)
  have h : inclMap R X A 0 = ε R (TopCat.of A) ≫ inv (ε R X) := by
    rw [← inclMap_ε, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [h]
  have : Epi (ε R (TopCat.of A)) :=
    IsSplitEpi.epi _ (hf := ⟨⟨⟨εSection R (TopCat.of A), εSection_ε R (TopCat.of A)⟩⟩⟩)
  infer_instance

theorem isZero_relativeHomology_zero_of_pathConnected (X : TopCat.{u}) (A : Set X) [PathConnectedSpace X]
    [Nonempty A] : IsZero (relativeHomology R X A 0) :=
  isZero_relativeHomology_zero_of_epi R X A (epi_inclMap_zero_of_pathConnected R X A)

lemma relativeHomologyMap_congr {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf hf' : Set.MapsTo f A B) (n : ℕ) : relativeHomologyMap R f hf n = relativeHomologyMap R f hf' n := rfl

lemma relativeHomologyMap_eq_of_eq {X Y : TopCat.{u}} {A : Set X} {B : Set Y} {f g : X ⟶ Y} (h : f = g)
    (hf : Set.MapsTo f A B) (n : ℕ) : relativeHomologyMap R f hf n = relativeHomologyMap R g (h ▸ hf) n := by
  subst h; rfl

lemma mapsTo_id_of_subset {X : TopCat.{u}} {A A' : Set X} (h : A ⊆ A') :
    Set.MapsTo (𝟙 X) A A' := fun x hx => by simpa using h hx

lemma mapsTo_comp {X Y W : TopCat.{u}} {A : Set X} {B : Set Y} {D : Set W} {f : X ⟶ Y}
    {g : Y ⟶ W} (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B D) : Set.MapsTo (f ≫ g) A D :=
  fun x hx => by simpa using hg (hf hx)

lemma relativeHomologyMap_comp_id {X Y : TopCat.{u}} {A A' : Set X} {B B' : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) (hf' : Set.MapsTo f A' B') (hA : Set.MapsTo (𝟙 X) A A')
    (hB : Set.MapsTo (𝟙 Y) B B') (n : ℕ) :
    relativeHomologyMap R f hf n ≫ relativeHomologyMap R (𝟙 Y) hB n = relativeHomologyMap R (𝟙 X) hA n ≫ relativeHomologyMap R f hf' n := by
  rw [← relativeHomologyMap_comp R f (𝟙 Y) hf hB (mapsTo_comp hf hB) n,
    ← relativeHomologyMap_comp R (𝟙 X) f hA hf' (mapsTo_comp hA hf') n]
  exact relativeHomologyMap_eq_of_eq R (by simp) _ n

def relativeHomologyIsoOfEq (X : TopCat.{u}) {A A' : Set X} (h : A = A') (n : ℕ) :
    relativeHomology R X A n ≅ relativeHomology R X A' n where
  hom := relativeHomologyMap R (𝟙 X) (mapsTo_id_of_subset h.le) n
  inv := relativeHomologyMap R (𝟙 X) (mapsTo_id_of_subset h.ge) n
  hom_inv_id := by
    subst h
    rw [relativeHomologyMap_id, Category.id_comp]
  inv_hom_id := by
    subst h
    rw [relativeHomologyMap_id, Category.id_comp]

section homeomorph

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y)

abbrev homeoHom : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom (f : C(X, Y))

lemma homeoHom_eq_toHomotopyEquiv : homeoHom f = TopCat.ofHom f.toHomotopyEquiv.toFun := rfl

@[simp]
lemma homeoHom_apply (x : X) : homeoHom f x = f x := rfl

lemma homeoHom_comp_symm : homeoHom f ≫ homeoHom f.symm = 𝟙 _ := by
  ext x
  simp

lemma symm_comp_homeoHom : homeoHom f.symm ≫ homeoHom f = 𝟙 _ := by
  ext x
  simp

lemma mapsTo_homeoHom {A : Set X} {B : Set Y} (h : f '' A = B) :
    Set.MapsTo (homeoHom f) A B := by
  subst h
  exact Set.mapsTo_image f A

lemma mapsTo_homeoHom_symm {A : Set X} {B : Set Y} (h : f '' A = B) :
    Set.MapsTo (homeoHom f.symm) B A := by
  subst h
  rintro _ ⟨a, ha, rfl⟩
  simpa using ha

def relativeHomologyIsoOfHomeomorphImage {A : Set X} {B : Set Y} (h : f '' A = B) (k : ℕ) :
    relativeHomology R (TopCat.of X) A k ≅ relativeHomology R (TopCat.of Y) B k where
  hom := relativeHomologyMap R (homeoHom f) (mapsTo_homeoHom f h) k
  inv := relativeHomologyMap R (homeoHom f.symm) (mapsTo_homeoHom_symm f h) k
  hom_inv_id := by
    rw [← relativeHomologyMap_comp R _ _ _ _
      (mapsTo_comp (mapsTo_homeoHom f h) (mapsTo_homeoHom_symm f h)) k]
    exact (relativeHomologyMap_eq_of_eq R (homeoHom_comp_symm f) _ k).trans (relativeHomologyMap_id R _ _ _ k)
  inv_hom_id := by
    rw [← relativeHomologyMap_comp R _ _ _ _
      (mapsTo_comp (mapsTo_homeoHom_symm f h) (mapsTo_homeoHom f h)) k]
    exact (relativeHomologyMap_eq_of_eq R (symm_comp_homeoHom f) _ k).trans (relativeHomologyMap_id R _ _ _ k)

lemma relativeHomologyIsoOfHomeomorphImage_hom {A : Set X} {B : Set Y} (h : f '' A = B) (k : ℕ) :
    (relativeHomologyIsoOfHomeomorphImage R f h k).hom = relativeHomologyMap R (homeoHom f) (mapsTo_homeoHom f h) k :=
  rfl

lemma relativeHomologyIsoOfHomeomorphImage_inv {A : Set X} {B : Set Y} (h : f '' A = B) (k : ℕ) :
    (relativeHomologyIsoOfHomeomorphImage R f h k).inv =
      relativeHomologyMap R (homeoHom f.symm) (mapsTo_homeoHom_symm f h) k :=
  rfl

theorem isIso_relativeHomologyMap_homeoHom {A : Set X} {B : Set Y} (h : f '' A = B)
    (hf : Set.MapsTo (homeoHom f) A B) (k : ℕ) : IsIso (relativeHomologyMap R (homeoHom f) hf k) :=
  ⟨(relativeHomologyIsoOfHomeomorphImage R f h k).inv, (relativeHomologyIsoOfHomeomorphImage R f h k).hom_inv_id,
    (relativeHomologyIsoOfHomeomorphImage R f h k).inv_hom_id⟩

def relativeHomologyIsoOfHomeomorph (A : Set X) (k : ℕ) :
    relativeHomology R (TopCat.of X) A k ≅ relativeHomology R (TopCat.of Y) (f '' A) k :=
  relativeHomologyIsoOfHomeomorphImage R f rfl k

lemma relativeHomologyIsoOfHomeomorph_hom (A : Set X) (k : ℕ) :
    (relativeHomologyIsoOfHomeomorph R f A k).hom = relativeHomologyMap R (homeoHom f) (Set.mapsTo_image f A) k :=
  rfl

lemma homeomorph_image_eq_of_mem_iff {A : Set X} {B : Set Y} (h : ∀ x, x ∈ A ↔ f x ∈ B) :
    f '' A = B := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x).1 hx
  · intro hy
    exact ⟨f.symm y, (h _).2 (by simpa using hy), by simp⟩

def relativeHomologyIsoOfHomeomorphMemIff {A : Set X} {B : Set Y} (h : ∀ x, x ∈ A ↔ f x ∈ B) (k : ℕ) :
    relativeHomology R (TopCat.of X) A k ≅ relativeHomology R (TopCat.of Y) B k :=
  relativeHomologyIsoOfHomeomorphImage R f (homeomorph_image_eq_of_mem_iff f h) k

lemma relativeHomologyIsoOfHomeomorphMemIff_hom {A : Set X} {B : Set Y} (h : ∀ x, x ∈ A ↔ f x ∈ B) (k : ℕ) :
    (relativeHomologyIsoOfHomeomorphMemIff R f h k).hom =
      relativeHomologyMap R (homeoHom f) (fun x hx => (h x).1 hx) k :=
  rfl

lemma relativeHomologyIsoOfHomeomorphImage_natural {A A' : Set X} {B B' : Set Y} (h : f '' A = B)
    (h' : f '' A' = B') (hA : Set.MapsTo (𝟙 (TopCat.of X)) A A')
    (hB : Set.MapsTo (𝟙 (TopCat.of Y)) B B') (k : ℕ) :
    (relativeHomologyIsoOfHomeomorphImage R f h k).hom ≫ relativeHomologyMap R (𝟙 _) hB k =
      relativeHomologyMap R (𝟙 _) hA k ≫ (relativeHomologyIsoOfHomeomorphImage R f h' k).hom :=
  relativeHomologyMap_comp_id R _ _ _ hA hB k

end homeomorph

section nested

variable {X : Type u} [TopologicalSpace X]

lemma homeomorphPreimageVal_image {B B' : Set X} (h : B ⊆ B') (A : Set X) :
    homeomorphPreimageVal h '' (Subtype.val ⁻¹' (Subtype.val ⁻¹' A)) =
      (Subtype.val ⁻¹' A : Set B) := by
  ext ⟨x, hx⟩
  constructor
  · rintro ⟨⟨⟨y, hy⟩, hy'⟩, hyA, hxy⟩
    cases hxy
    exact hyA
  · intro hxA
    exact ⟨⟨⟨x, h hx⟩, hx⟩, hxA, rfl⟩

def relativeHomologyIsoOfSubtypeSubtype {B B' : Set X} (h : B ⊆ B') (A : Set X) (k : ℕ) :
    relativeHomology R (TopCat.of (Subtype.val ⁻¹' B : Set B')) (Subtype.val ⁻¹' (Subtype.val ⁻¹' A)) k ≅
      relativeHomology R (TopCat.of B) (Subtype.val ⁻¹' A) k :=
  relativeHomologyIsoOfHomeomorphImage R (homeomorphPreimageVal h) (homeomorphPreimageVal_image h A) k

end nested

end DifferentialGeometry.Topology.SingularPair

end
