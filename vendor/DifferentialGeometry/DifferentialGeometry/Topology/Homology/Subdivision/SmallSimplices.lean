module

public import DifferentialGeometry.Topology.Homology.SingularSubcomplex
public import DifferentialGeometry.Topology.Homology.Subdivision.DiameterBound

@[expose] public section

open CategoryTheory Limits AlgebraicTopology Convexity
open scoped Simplicial

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

open AffChain

variable (R : ModuleCat.{u} ℤ) (X : TopCat.{u})

lemma subdivisionHomotopyComponent_d_zero : subdivisionHomotopyComponent R X 0 ≫ (simplicialChains R X).d 1 0 + (barycentricSubdivisionMap R X).f 0 = 𝟙 _ := by
  have h := (homotopyIdBarycentricSubdivision R X).comm 0
  rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex] at h
  simp only [homotopyIdBarycentricSubdivision, dite_eq_left rfl, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
    Category.comp_id, zero_add, HomologicalComplex.id_f] at h
  exact h.symm

lemma d_subdivisionHomotopyComponent_add_subdivisionHomotopyComponent_d (j : ℕ) :
    (simplicialChains R X).d (j + 1) j ≫ subdivisionHomotopyComponent R X j + subdivisionHomotopyComponent R X (j + 1) ≫ (simplicialChains R X).d (j + 2) (j + 1) +
      (barycentricSubdivisionMap R X).f (j + 1) = 𝟙 _ := by
  have h := (homotopyIdBarycentricSubdivision R X).comm (j + 1)
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at h
  simp only [homotopyIdBarycentricSubdivision, dite_eq_left rfl, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
    Category.comp_id, HomologicalComplex.id_f] at h
  exact h.symm

def iteratedSubdivisionHomotopyComponent (k j : ℕ) : (simplicialChains R X).X j ⟶ (simplicialChains R X).X (j + 1) :=
  ∑ i ∈ Finset.range k, (iteratedBarycentricSubdivisionMap R X i).f j ≫ subdivisionHomotopyComponent R X j

@[simp] lemma iteratedSubdivisionHomotopyComponent_zero (j : ℕ) : iteratedSubdivisionHomotopyComponent R X 0 j = 0 := by simp [iteratedSubdivisionHomotopyComponent]

lemma iteratedSubdivisionHomotopyComponent_succ (k j : ℕ) : iteratedSubdivisionHomotopyComponent R X (k + 1) j = iteratedSubdivisionHomotopyComponent R X k j + (iteratedBarycentricSubdivisionMap R X k).f j ≫ subdivisionHomotopyComponent R X j := by
  simp [iteratedSubdivisionHomotopyComponent, Finset.sum_range_succ]

lemma iteratedSubdivisionHomotopyComponent_sub_iteratedSubdivisionHomotopyComponent {k k' : ℕ} (h : k' ≤ k) (j : ℕ) :
    iteratedSubdivisionHomotopyComponent R X k j - iteratedSubdivisionHomotopyComponent R X k' j = ∑ i ∈ Finset.Ico k' k, (iteratedBarycentricSubdivisionMap R X i).f j ≫ subdivisionHomotopyComponent R X j := by
  rw [sub_eq_iff_eq_add', iteratedSubdivisionHomotopyComponent, iteratedSubdivisionHomotopyComponent, Finset.sum_range_add_sum_Ico _ h]

lemma iteratedSubdivisionHomotopyComponent_d_zero (k : ℕ) : iteratedSubdivisionHomotopyComponent R X k 0 ≫ (simplicialChains R X).d 1 0 + (iteratedBarycentricSubdivisionMap R X k).f 0 = 𝟙 _ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedSubdivisionHomotopyComponent_succ, Preadditive.add_comp, iteratedBarycentricSubdivisionMap_succ, HomologicalComplex.comp_f, Category.assoc,
      add_assoc, ← Preadditive.comp_add, subdivisionHomotopyComponent_d_zero, Category.comp_id, ih]

lemma d_iteratedSubdivisionHomotopyComponent_add_iteratedSubdivisionHomotopyComponent_d (k j : ℕ) :
    (simplicialChains R X).d (j + 1) j ≫ iteratedSubdivisionHomotopyComponent R X k j + iteratedSubdivisionHomotopyComponent R X k (j + 1) ≫ (simplicialChains R X).d (j + 2) (j + 1) +
      (iteratedBarycentricSubdivisionMap R X k).f (j + 1) = 𝟙 _ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedSubdivisionHomotopyComponent_succ, iteratedSubdivisionHomotopyComponent_succ, Preadditive.add_comp, Preadditive.comp_add, iteratedBarycentricSubdivisionMap_succ,
      HomologicalComplex.comp_f, Category.assoc,
      ← (iteratedBarycentricSubdivisionMap R X k).comm_assoc (j + 1) j]
    have key : (iteratedBarycentricSubdivisionMap R X k).f (j + 1) ≫ ((simplicialChains R X).d (j + 1) j ≫ subdivisionHomotopyComponent R X j +
        subdivisionHomotopyComponent R X (j + 1) ≫ (simplicialChains R X).d (j + 2) (j + 1) + (barycentricSubdivisionMap R X).f (j + 1)) =
        (iteratedBarycentricSubdivisionMap R X k).f (j + 1) := by
      rw [d_subdivisionHomotopyComponent_add_subdivisionHomotopyComponent_d, Category.comp_id]
    simp only [Preadditive.comp_add] at key
    calc _ = ((simplicialChains R X).d (j + 1) j ≫ iteratedSubdivisionHomotopyComponent R X k j +
          iteratedSubdivisionHomotopyComponent R X k (j + 1) ≫ (simplicialChains R X).d (j + 2) (j + 1) +
          (iteratedBarycentricSubdivisionMap R X k).f (j + 1)) - (iteratedBarycentricSubdivisionMap R X k).f (j + 1) +
          ((iteratedBarycentricSubdivisionMap R X k).f (j + 1) ≫ (simplicialChains R X).d (j + 1) j ≫ subdivisionHomotopyComponent R X j +
            (iteratedBarycentricSubdivisionMap R X k).f (j + 1) ≫ subdivisionHomotopyComponent R X (j + 1) ≫ (simplicialChains R X).d (j + 2) (j + 1) +
            (iteratedBarycentricSubdivisionMap R X k).f (j + 1) ≫ (barycentricSubdivisionMap R X).f (j + 1)) := by abel
      _ = 𝟙 _ := by rw [ih, key, sub_add_cancel]

section cover

variable {X} {ι : Type*} (U : ι → Set X)

abbrev smallInc :
    ((small X U : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).chainComplex R ⟶ simplicialChains R X :=
  SSet.chainComplexMap (small X U).ι R

instance (n : ℕ) : Mono ((smallInc R U).f n) :=
  inferInstanceAs (Mono ((SSet.chainComplexMap (small X U).pair.hom R).f n))

@[reassoc]
lemma ι_smallInc_f {n : ℕ}
    (σ : ((small X U : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}) _⦋n⦌) :
    ((small X U : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).ιChainComplex σ ≫
      (smallInc R U).f n = (TopCat.toSSet.obj X).ιChainComplex σ.1 :=
  SSet.ι_chainComplexMap_f _ _ (small X U).ι R σ

variable (hU : ⋃ i, interior (U i) = Set.univ)

open Classical in
def mIdx {m : ℕ} (τ : Sing X m) : ℕ :=
  Nat.find (exists_isSmall hU (X.toSSetObjEquiv _ τ))

lemma isSmall_mIdx {m : ℕ} (τ : Sing X m) :
    isSmall U (X.toSSetObjEquiv _ τ) (mIdx U hU τ) := by
  classical exact Nat.find_spec (exists_isSmall hU (X.toSSetObjEquiv _ τ))

lemma mIdx_le {m : ℕ} (τ : Sing X m) {k : ℕ} (h : isSmall U (X.toSSetObjEquiv _ τ) k) :
    mIdx U hU τ ≤ k := by
  classical exact Nat.find_min' (exists_isSmall hU (X.toSSetObjEquiv _ τ)) h

lemma mIdx_δ_le {m : ℕ} (τ : Sing X (m + 1)) (i : Fin (m + 2)) :
    mIdx U hU ((TopCat.toSSet.obj X).δ i τ) ≤ mIdx U hU τ :=
  mIdx_le U hU _ ((isSmall_mIdx U hU τ).δ i)

lemma isSmall_zero_of_mem_small {m : ℕ} {τ : Sing X m} (hτ : τ ∈ (small X U).obj _) :
    isSmall U (X.toSSetObjEquiv _ τ) 0 := by
  obtain ⟨i, hi⟩ := (mem_small_iff U τ).1 hτ
  intro s _
  exact ⟨i, (Set.image_subset_range _ _).trans hi⟩

lemma mIdx_eq_zero_of_mem_small {m : ℕ} {τ : Sing X m} (hτ : τ ∈ (small X U).obj _) :
    mIdx U hU τ = 0 :=
  Nat.le_zero.1 (mIdx_le U hU τ (isSmall_zero_of_mem_small U hτ))

lemma δ_mem_small {m : ℕ} {τ : Sing X (m + 1)} (hτ : τ ∈ (small X U).obj _)
    (i : Fin (m + 2)) :
    (TopCat.toSSet.obj X).δ i τ ∈ (small X U).obj _ :=
  (small X U).map _ hτ

def smallSubdivisionHomotopyComponent (j : ℕ) : (simplicialChains R X).X j ⟶ (simplicialChains R X).X (j + 1) :=
  Sigma.desc fun τ => (TopCat.toSSet.obj X).ιChainComplex τ ≫ iteratedSubdivisionHomotopyComponent R X (mIdx U hU τ) j

@[reassoc]
lemma ι_smallSubdivisionHomotopyComponent {j : ℕ} (τ : Sing X j) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ smallSubdivisionHomotopyComponent R U hU j =
      (TopCat.toSSet.obj X).ιChainComplex τ ≫ iteratedSubdivisionHomotopyComponent R X (mIdx U hU τ) j :=
  Sigma.ι_comp_desc _ _

lemma ι_d_smallSubdivisionHomotopyComponent {j : ℕ} (τ : Sing X (j + 1)) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ (simplicialChains R X).d (j + 1) j ≫ smallSubdivisionHomotopyComponent R U hU j =
      ∑ i : Fin (j + 2), (-1) ^ (i : ℕ) • ((TopCat.toSSet.obj X).ιChainComplex
        ((TopCat.toSSet.obj X).δ i τ) ≫
          iteratedSubdivisionHomotopyComponent R X (mIdx U hU ((TopCat.toSSet.obj X).δ i τ)) j) := by
  rw [SSet.ιChainComplex_d_assoc, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, ι_smallSubdivisionHomotopyComponent]

def smallSubdivisionHomotopyHom (i j : ℕ) : (simplicialChains R X).X i ⟶ (simplicialChains R X).X j :=
  if h : i + 1 = j then smallSubdivisionHomotopyComponent R U hU i ≫ ((simplicialChains R X).XIsoOfEq h).hom else 0

lemma smallSubdivisionHomotopyHom_succ (i : ℕ) : smallSubdivisionHomotopyHom R U hU i (i + 1) = smallSubdivisionHomotopyComponent R U hU i := by
  simp [smallSubdivisionHomotopyHom]

abbrev smallSubdivisionNullHomotopicMap : simplicialChains R X ⟶ simplicialChains R X := Homotopy.nullHomotopicMap (smallSubdivisionHomotopyHom R U hU)

lemma smallSubdivisionNullHomotopicMap_f_zero : (smallSubdivisionNullHomotopicMap R U hU).f 0 = smallSubdivisionHomotopyComponent R U hU 0 ≫ (simplicialChains R X).d 1 0 := by
  change dNext 0 (smallSubdivisionHomotopyHom R U hU) + prevD 0 (smallSubdivisionHomotopyHom R U hU) = _
  rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, smallSubdivisionHomotopyHom_succ, zero_add]

lemma smallSubdivisionNullHomotopicMap_f_succ (j : ℕ) : (smallSubdivisionNullHomotopicMap R U hU).f (j + 1) =
    (simplicialChains R X).d (j + 1) j ≫ smallSubdivisionHomotopyComponent R U hU j +
      smallSubdivisionHomotopyComponent R U hU (j + 1) ≫ (simplicialChains R X).d (j + 2) (j + 1) := by
  change dNext (j + 1) (smallSubdivisionHomotopyHom R U hU) + prevD (j + 1) (smallSubdivisionHomotopyHom R U hU) = _
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex, smallSubdivisionHomotopyHom_succ, smallSubdivisionHomotopyHom_succ]

abbrev ρbig : simplicialChains R X ⟶ simplicialChains R X := 𝟙 _ - smallSubdivisionNullHomotopicMap R U hU

lemma ι_ρbig_zero (τ : Sing X 0) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ (ρbig R U hU).f 0 =
      (TopCat.toSSet.obj X).ιChainComplex τ ≫ (iteratedBarycentricSubdivisionMap R X (mIdx U hU τ)).f 0 := by
  have hD : iteratedSubdivisionHomotopyComponent R X (mIdx U hU τ) 0 ≫ (simplicialChains R X).d 1 0 =
      𝟙 _ - (iteratedBarycentricSubdivisionMap R X (mIdx U hU τ)).f 0 := by
    rw [← iteratedSubdivisionHomotopyComponent_d_zero R X (mIdx U hU τ)]; abel
  rw [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, smallSubdivisionNullHomotopicMap_f_zero, Preadditive.comp_sub,
    Category.comp_id, ι_smallSubdivisionHomotopyComponent_assoc, hD, Preadditive.comp_sub, Category.comp_id, sub_sub_cancel]

lemma ι_ρbig_succ {j : ℕ} (τ : Sing X (j + 1)) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ (ρbig R U hU).f (j + 1) =
      (TopCat.toSSet.obj X).ιChainComplex τ ≫ (iteratedBarycentricSubdivisionMap R X (mIdx U hU τ)).f (j + 1) +
      ∑ i : Fin (j + 2), (-1) ^ (i : ℕ) • ((TopCat.toSSet.obj X).ιChainComplex
        ((TopCat.toSSet.obj X).δ i τ) ≫
          (iteratedSubdivisionHomotopyComponent R X (mIdx U hU τ) j - iteratedSubdivisionHomotopyComponent R X (mIdx U hU ((TopCat.toSSet.obj X).δ i τ)) j)) := by
  have hD : iteratedSubdivisionHomotopyComponent R X (mIdx U hU τ) (j + 1) ≫ (simplicialChains R X).d (j + 2) (j + 1) =
      𝟙 _ - (simplicialChains R X).d (j + 1) j ≫ iteratedSubdivisionHomotopyComponent R X (mIdx U hU τ) j -
        (iteratedBarycentricSubdivisionMap R X (mIdx U hU τ)).f (j + 1) := by
    rw [← d_iteratedSubdivisionHomotopyComponent_add_iteratedSubdivisionHomotopyComponent_d R X (mIdx U hU τ) j]; abel
  have h2 : (TopCat.toSSet.obj X).ιChainComplex τ ≫ smallSubdivisionHomotopyComponent R U hU (j + 1) ≫
      (simplicialChains R X).d (j + 2) (j + 1) =
      (TopCat.toSSet.obj X).ιChainComplex τ -
        ∑ i : Fin (j + 2), (-1) ^ (i : ℕ) • ((TopCat.toSSet.obj X).ιChainComplex
          ((TopCat.toSSet.obj X).δ i τ) ≫ iteratedSubdivisionHomotopyComponent R X (mIdx U hU τ) j) -
        (TopCat.toSSet.obj X).ιChainComplex τ ≫ (iteratedBarycentricSubdivisionMap R X (mIdx U hU τ)).f (j + 1) := by
    rw [ι_smallSubdivisionHomotopyComponent_assoc, hD, Preadditive.comp_sub, Preadditive.comp_sub, Category.comp_id,
      ← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
    simp only [Preadditive.zsmul_comp]
  rw [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, smallSubdivisionNullHomotopicMap_f_succ, Preadditive.comp_sub,
    Category.comp_id, Preadditive.comp_add, ι_d_smallSubdivisionHomotopyComponent, h2]
  simp only [Preadditive.comp_sub, smul_sub, Finset.sum_sub_distrib]
  abel

lemma ι_ρbig_of_mem_small {j : ℕ} {τ : Sing X j} (hτ : τ ∈ (small X U).obj _) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ (ρbig R U hU).f j =
      (TopCat.toSSet.obj X).ιChainComplex τ := by
  cases j with
  | zero =>
    rw [ι_ρbig_zero, mIdx_eq_zero_of_mem_small U hU hτ, iteratedBarycentricSubdivisionMap_zero, HomologicalComplex.id_f,
      Category.comp_id]
  | succ j =>
    rw [ι_ρbig_succ, mIdx_eq_zero_of_mem_small U hU hτ, iteratedBarycentricSubdivisionMap_zero, HomologicalComplex.id_f,
      Category.comp_id]
    simp only [mIdx_eq_zero_of_mem_small U hU (δ_mem_small U hτ _), sub_self, Limits.comp_zero,
      smul_zero, Finset.sum_const_zero, add_zero]

def smallRange (j : ℕ) : AddSubgroup (R ⟶ (simplicialChains R X).X j) :=
  (Preadditive.rightComp R ((smallInc R U).f j)).range

lemma mem_smallRange_iff {j : ℕ} (f : R ⟶ (simplicialChains R X).X j) :
    f ∈ smallRange R U j ↔
      ∃ c : R ⟶
        (((small X U : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).chainComplex R).X j,
        c ≫ (smallInc R U).f j = f :=
  AddMonoidHom.mem_range

lemma ι_iteratedBarycentricSubdivisionMap_mem_smallRange {m : ℕ} (τ : Sing X m) {k : ℕ}
    (h : isSmall U (X.toSSetObjEquiv _ τ) k) {j : ℕ} (hj : k ≤ j) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ (iteratedBarycentricSubdivisionMap R X j).f m ∈ smallRange R U m := by
  rw [mem_smallRange_iff, ← sing_toSSetObjEquiv τ,
    h.ι_iteratedBarycentricSubdivisionMap_f_eq R hj (small X U) (singSub_le_small U)]
  exact ⟨_, rfl⟩

lemma ι_iteratedBarycentricSubdivisionMap_subdivisionHomotopyComponent_mem_smallRange {m : ℕ} (τ : Sing X m) {k : ℕ}
    (h : isSmall U (X.toSSetObjEquiv _ τ) k) {j : ℕ} (hj : k ≤ j) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ (iteratedBarycentricSubdivisionMap R X j).f m ≫ subdivisionHomotopyComponent R X m ∈
      smallRange R U (m + 1) := by
  rw [mem_smallRange_iff, ← sing_toSSetObjEquiv τ,
    h.ι_iteratedBarycentricSubdivisionMap_f_subdivisionHomotopyComponent_eq R hj (small X U) (singSub_le_small U)]
  exact ⟨_, rfl⟩

lemma ι_ρbig_mem_smallRange {j : ℕ} (τ : Sing X j) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ (ρbig R U hU).f j ∈ smallRange R U j := by
  cases j with
  | zero =>
    rw [ι_ρbig_zero]
    exact ι_iteratedBarycentricSubdivisionMap_mem_smallRange R U τ (isSmall_mIdx U hU τ) le_rfl
  | succ j =>
    rw [ι_ρbig_succ]
    refine add_mem (ι_iteratedBarycentricSubdivisionMap_mem_smallRange R U τ (isSmall_mIdx U hU τ) le_rfl)
      (sum_mem fun i _ => zsmul_mem ?_ _)
    rw [iteratedSubdivisionHomotopyComponent_sub_iteratedSubdivisionHomotopyComponent R X (mIdx_δ_le U hU τ i), Preadditive.comp_sum]
    refine sum_mem fun i' hi' => ?_
    exact ι_iteratedBarycentricSubdivisionMap_subdivisionHomotopyComponent_mem_smallRange R U _ (isSmall_mIdx U hU _) (Finset.mem_Ico.1 hi').1

def ρf (j : ℕ) :
    (simplicialChains R X).X j ⟶
      (((small X U : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).chainComplex R).X j :=
  Sigma.desc fun τ => ((mem_smallRange_iff R U _).1 (ι_ρbig_mem_smallRange R U hU τ)).choose

lemma ι_ρf_comp {j : ℕ} (τ : Sing X j) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ ρf R U hU j ≫ (smallInc R U).f j =
      (TopCat.toSSet.obj X).ιChainComplex τ ≫ (ρbig R U hU).f j := by
  rw [← Category.assoc]
  erw [Sigma.ι_comp_desc]
  exact ((mem_smallRange_iff R U _).1 (ι_ρbig_mem_smallRange R U hU τ)).choose_spec

lemma ρf_comp_smallChainMap_f (j : ℕ) :
    ρf R U hU j ≫ (smallInc R U).f j = (ρbig R U hU).f j :=
  SSet.chainComplex_hom_ext fun τ => ι_ρf_comp R U hU τ

def ρ : simplicialChains R X ⟶ ((small X U : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).chainComplex R where
  f j := ρf R U hU j
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    rw [← cancel_mono ((smallInc R U).f j), Category.assoc, Category.assoc,
      ← (smallInc R U).comm (j + 1) j, ← Category.assoc, ρf_comp_smallChainMap_f,
      ρf_comp_smallChainMap_f, (ρbig R U hU).comm]

@[simp] lemma ρ_f (j : ℕ) : (ρ R U hU).f j = ρf R U hU j := rfl

theorem ρ_comp_smallChainMap : ρ R U hU ≫ smallInc R U = ρbig R U hU :=
  HomologicalComplex.hom_ext _ _ fun j => ρf_comp_smallChainMap_f R U hU j

theorem smallChainMap_comp_ρ : smallInc R U ≫ ρ R U hU = 𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ fun j => ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  refine SSet.chainComplex_hom_ext fun σ => ?_
  rw [← cancel_mono ((smallInc R U).f j), Category.assoc, Category.assoc, ρ_f,
    ρf_comp_smallChainMap_f, Category.comp_id, ι_smallInc_f_assoc,
    ι_ρbig_of_mem_small R U hU σ.2, ι_smallInc_f]

def homotopyρ : Homotopy (ρ R U hU ≫ smallInc R U) (𝟙 (simplicialChains R X)) where
  hom := -smallSubdivisionHomotopyHom R U hU
  zero i j hij := by
    have : ¬ i + 1 = j := hij
    simp [smallSubdivisionHomotopyHom, this]
  comm i := by
    rw [ρ_comp_smallChainMap, map_neg, map_neg, HomologicalComplex.sub_f_apply,
      HomologicalComplex.id_f]
    change 𝟙 _ - (dNext i (smallSubdivisionHomotopyHom R U hU) + prevD i (smallSubdivisionHomotopyHom R U hU)) = _
    abel

def smallHomotopyEquiv :
    HomotopyEquiv (((small X U : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).chainComplex R)
      (simplicialChains R X) where
  hom := smallInc R U
  inv := ρ R U hU
  homotopyHomInvId := Homotopy.ofEq (smallChainMap_comp_ρ R U hU)
  homotopyInvHomId := homotopyρ R U hU

@[simp] lemma smallHomotopyEquiv_hom : (smallHomotopyEquiv R U hU).hom = smallInc R U := rfl

include hU in
theorem quasiIso_smallChainMap : QuasiIso (SSet.chainComplexMap (small X U).ι R) :=
  (smallHomotopyEquiv R U hU).quasiIso_hom

include hU in
theorem quasiIso_smallChainMap' : QuasiIso (smallChainMap X R U) :=
  quasiIso_smallChainMap R U hU

include hU in
theorem quasiIsoAt_smallChainMap (n : ℕ) :
    QuasiIsoAt (SSet.chainComplexMap (small X U).ι R) n :=
  (smallHomotopyEquiv R U hU).quasiIsoAt_hom n

include hU in
theorem isIso_homologyMap_smallChainMap (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (SSet.chainComplexMap (small X U).ι R) n) :=
  (quasiIsoAt_iff_isIso_homologyMap _ n).1 (quasiIsoAt_smallChainMap R U hU n)

include hU in
theorem isIso_homologyMap_small (n : ℕ) :
    IsIso (SSet.homologyMap (small X U).ι R n) :=
  isIso_homologyMap_smallChainMap R U hU n

end cover

end DifferentialGeometry.Topology.SingularPair
