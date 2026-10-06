module

public import DifferentialGeometry.Topology.Homology.Local.LocalGood
public import DifferentialGeometry.Topology.Homology.MayerVietoris.OpenRelative

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

variable {R : ModuleCat.{u} ℤ} {X : TopCat.{u}}

lemma relativeHomologyMap_id_apply_relativeHomologyMap_id_apply {A B C : Set X} (h₁ : Set.MapsTo (𝟙 X) A B)
    (h₂ : Set.MapsTo (𝟙 X) B C) (h₃ : Set.MapsTo (𝟙 X) A C) (k : ℕ) (α : relativeHomology R X A k) :
    relativeHomologyMap R (𝟙 X) h₂ k (relativeHomologyMap R (𝟙 X) h₁ k α) = relativeHomologyMap R (𝟙 X) h₃ k α := by
  rw [← ModuleCat.comp_apply, ← relativeHomologyMap_comp R (𝟙 X) (𝟙 X) h₁ h₂ (mapsTo_comp h₁ h₂) k]
  exact congrArg (fun f : relativeHomology R X A k ⟶ relativeHomology R X C k => f α)
    (relativeHomologyMap_eq_of_eq R (Category.id_comp (𝟙 X)) _ k)

lemma relativeHomologyMap_id_injective_of_eq {A B : Set X} (e : A = B) (h : Set.MapsTo (𝟙 X) A B)
    (k : ℕ) : Function.Injective (relativeHomologyMap R (𝟙 X) h k) := by
  have : relativeHomologyMap R (𝟙 X) h k = (relativeHomologyIsoOfEq R X e k).hom := rfl
  rw [this]
  exact (ModuleCat.mono_iff_injective _).1 inferInstance

namespace localGood

variable {n : ℕ}

theorem union {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (gA : localGood R X n A)
    (gB : localGood R X n B) (gAB : localGood R X n (A ∩ B)) : localGood R X n (A ∪ B) := by
  have hP : IsOpen Aᶜ := hA.isOpen_compl
  have hQ : IsOpen Bᶜ := hB.isOpen_compl
  have hvan : ∀ i, n < i → IsZero (relativeHomology R X (Aᶜ ∩ Bᶜ) i) := fun i hi =>
    isZero_relativeHomology_inter_of_isZero R hP hQ i
      ((gAB.isZero (by omega)).of_iso (relativeHomologyIsoOfEq R X (Set.compl_inter A B) (i + 1)).symm)
      (gA.isZero hi) (gB.isZero hi)
  refine ⟨fun i hi => (hvan i hi).of_iso (relativeHomologyIsoOfEq R X (Set.compl_union A B) i),
    fun α hα => ?_⟩
  have hmt : Set.MapsTo (𝟙 X) (A ∪ B)ᶜ (Aᶜ ∩ Bᶜ) := mapsTo_id_of_subset (Set.compl_union A B).le
  apply relativeHomologyMap_id_injective_of_eq (Set.compl_union A B) hmt n
  rw [map_zero]
  refine relMV_injective R hP hQ n
    ((gAB.isZero (Nat.lt_succ_self n)).of_iso
      (relativeHomologyIsoOfEq R X (Set.compl_inter A B) (n + 1)).symm)
    _ ?_ ?_
  · rw [relativeHomologyMap_id_apply_relativeHomologyMap_id_apply hmt _ (mapsTo_id_of_subset (Set.compl_subset_compl.2
      Set.subset_union_left))]
    refine gA.eq_zero fun x hx => ?_
    rw [relativeHomologyMap_id_apply_relativeHomologyMap_id_apply _ _ (compl_mapsTo (Or.inl hx : x ∈ A ∪ B))]
    exact hα x (Or.inl hx)
  · rw [relativeHomologyMap_id_apply_relativeHomologyMap_id_apply hmt _ (mapsTo_id_of_subset (Set.compl_subset_compl.2
      Set.subset_union_right))]
    refine gB.eq_zero fun x hx => ?_
    rw [relativeHomologyMap_id_apply_relativeHomologyMap_id_apply _ _ (compl_mapsTo (Or.inr hx : x ∈ A ∪ B))]
    exact hα x (Or.inr hx)

theorem of_finite_convex (hn : 1 ≤ n) (m : ℕ) (C : Fin m → Set (EU.{u} n))
    (hC : ∀ j, Convex ℝ (C j) ∧ IsCompact (C j)) :
    localGood R (TopCat.of (EU n)) n (⋃ j, C j) := by
  induction m with
  | zero => exact (empty _ _).of_eq (Set.iUnion_of_empty C).symm
  | succ m ih =>
    refine (union (isClosed_iUnion_of_finite fun j => (hC (Fin.castSucc j)).2.isClosed)
      (hC (Fin.last m)).2.isClosed (ih (C ∘ Fin.castSucc) fun j => hC _)
      (of_convex hn (hC (Fin.last m)).1 (hC (Fin.last m)).2) ?_).of_eq
      (Set.iUnion_fin_add_one_eq_iUnion_castSucc C).symm
    refine (ih (fun j => C (Fin.castSucc j) ∩ C (Fin.last m)) fun j =>
      ⟨(hC _).1.inter (hC _).1, (hC _).2.inter_right (hC _).2.isClosed⟩).of_eq ?_
    exact (Set.iUnion_inter (C (Fin.last m)) (C ∘ Fin.castSucc)).symm

end localGood

end DifferentialGeometry.Topology.SingularPair

end
