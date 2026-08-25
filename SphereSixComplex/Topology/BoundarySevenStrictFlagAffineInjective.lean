module

public import SphereSixComplex.Topology.BoundarySevenProperFaceRealization

/-!
# Injectivity of affine barycentric coordinates on a strict flag

The barycenters of a strictly nested flag of nonempty faces are affinely independent.  Here we
prove the precise point-set consequence needed for the proper-face realization: the affine map
on each nondegenerate flag simplex is injective.
-/

@[expose] public section

noncomputable section

open CategoryTheory ContinuousMap PartialOrder Set Simplicial

namespace SphereSixComplex

/-- Every level of a strict flag has a vertex which first appears at exactly that level. -/
private theorem boundarySevenStrictFlag_exists_levelVertex
    (k : ℕ) (F : ComposableArrows BoundarySevenProperFace k)
    (hF : StrictMono F.obj) (j : Fin (k + 1)) :
    ∃ a : Fin 8, ∀ l : Fin (k + 1),
      (a ∈ (F.obj l).1 ↔ j ≤ l) := by
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · obtain ⟨a, ha⟩ := (F.obj (0 : Fin (k + 1))).2.1
    refine ⟨a, fun l ↦ ⟨fun _ ↦ Fin.zero_le l, fun _ ↦ ?_⟩⟩
    have hle : F.obj (0 : Fin (k + 1)) ≤ F.obj l :=
      leOfHom (F.map (homOfLE (Fin.zero_le l)))
    exact hle ha
  · have hlt : F.obj i.castSucc < F.obj i.succ :=
      hF i.castSucc_lt_succ
    have hsub : (F.obj i.castSucc).1 ⊆ (F.obj i.succ).1 := hlt.le
    have hex : ∃ a, a ∈ (F.obj i.succ).1 ∧ a ∉ (F.obj i.castSucc).1 := by
      by_contra h
      push Not at h
      apply hlt.ne
      apply Subtype.ext
      apply Finset.Subset.antisymm hsub
      intro a ha
      exact h a ha
    obtain ⟨a, haNow, haBefore⟩ := hex
    refine ⟨a, fun l ↦ ⟨?_, ?_⟩⟩
    · intro hal
      by_contra hle
      have hli : l ≤ i.castSucc := by
        change ¬ (i.val + 1 ≤ l.val) at hle
        change l.val ≤ i.val
        omega
      have hfaces : F.obj l ≤ F.obj i.castSucc :=
        leOfHom (F.map (homOfLE hli))
      exact haBefore (hfaces hal)
    · intro hil
      have hfaces : F.obj i.succ ≤ F.obj l :=
        leOfHom (F.map (homOfLE hil))
      exact hfaces haNow

/-- A strict flag has unique barycentric coefficients. -/
public theorem boundarySevenProperFaceAffineFlagMap_injective_of_strictMono
    (k : ℕ) (F : ComposableArrows BoundarySevenProperFace k)
    (hF : StrictMono F.obj) :
    Function.Injective (boundarySevenProperFaceAffineFlagMap k F) := by
  intro w v hwv
  apply Subtype.ext
  funext j
  let P : Fin (k + 1) → Prop := fun i ↦
    ∀ l, i ≤ l → w l = v l
  have hP : ∀ i, P i := by
    intro i
    induction i using Fin.reverseInduction with
    | last =>
        intro l hil
        have hli : l = Fin.last k := Fin.le_antisymm (Fin.le_last l) hil
        subst l
        obtain ⟨a, ha⟩ :=
          boundarySevenStrictFlag_exists_levelVertex k F hF (Fin.last k)
        have hcoord := congrArg
          (fun z : StandardSimplexBoundary 7 ↦ (z.1 : stdSimplex ℝ (Fin 8)) a) hwv
        change (∑ l, w l * boundarySevenProperFaceBarycenter (F.obj l) a) =
          ∑ l, v l * boundarySevenProperFaceBarycenter (F.obj l) a at hcoord
        simp only [boundarySevenProperFaceBarycenter_apply, ha,
          Fin.last_le_iff, mul_ite, mul_zero] at hcoord
        rw [← Finset.sum_filter, ← Finset.sum_filter] at hcoord
        simp only [Finset.filter_eq', Finset.mem_univ, ↓reduceIte,
          Finset.sum_singleton] at hcoord
        have hcard : (((F.obj (Fin.last k)).1.card : ℝ)⁻¹) ≠ 0 := by
          apply inv_ne_zero
          exact_mod_cast (F.obj (Fin.last k)).2.1.card_ne_zero
        exact mul_right_cancel₀ hcard hcoord
    | cast i ih =>
        intro l hil
        by_cases hli : l = i.castSucc
        · subst l
          obtain ⟨a, ha⟩ :=
            boundarySevenStrictFlag_exists_levelVertex k F hF i.castSucc
          have hcoord := congrArg
            (fun z : StandardSimplexBoundary 7 ↦ (z.1 : stdSimplex ℝ (Fin 8)) a) hwv
          change (∑ l, w l * boundarySevenProperFaceBarycenter (F.obj l) a) =
            ∑ l, v l * boundarySevenProperFaceBarycenter (F.obj l) a at hcoord
          simp only [boundarySevenProperFaceBarycenter_apply, ha,
            mul_ite, mul_zero] at hcoord
          rw [← Finset.sum_filter, ← Finset.sum_filter] at hcoord
          let s := Finset.univ.filter (fun l : Fin (k + 1) ↦ i.castSucc ≤ l)
          change Finset.sum s
              (fun l ↦ w l * ((F.obj l).1.card : ℝ)⁻¹) =
            Finset.sum s
              (fun l ↦ v l * ((F.obj l).1.card : ℝ)⁻¹) at hcoord
          have hi : i.castSucc ∈ s := by simp [s]
          rw [← Finset.sum_erase_add s _ hi,
            ← Finset.sum_erase_add s _ hi] at hcoord
          have htail :
              Finset.sum (s.erase i.castSucc)
                  (fun l ↦ w l * ((F.obj l).1.card : ℝ)⁻¹) =
                Finset.sum (s.erase i.castSucc)
                  (fun l ↦ v l * ((F.obj l).1.card : ℝ)⁻¹) := by
            apply Finset.sum_congr rfl
            intro m hm
            have hms : m ∈ s := Finset.mem_of_mem_erase hm
            have hmle : i.castSucc ≤ m := (Finset.mem_filter.mp hms).2
            have hmne : m ≠ i.castSucc := Finset.ne_of_mem_erase hm
            have hsucc : i.succ ≤ m := by
              change i.val ≤ m.val at hmle
              have hmne' : m.val ≠ i.val := by
                intro hval
                apply hmne
                apply Fin.ext
                exact hval
              change i.val + 1 ≤ m.val
              omega
            rw [ih m hsucc]
          rw [htail] at hcoord
          have hterm :
              w i.castSucc * ((F.obj i.castSucc).1.card : ℝ)⁻¹ =
                v i.castSucc * ((F.obj i.castSucc).1.card : ℝ)⁻¹ :=
            add_left_cancel hcoord
          have hcard : (((F.obj i.castSucc).1.card : ℝ)⁻¹) ≠ 0 := by
            apply inv_ne_zero
            exact_mod_cast (F.obj i.castSucc).2.1.card_ne_zero
          exact mul_right_cancel₀ hcard hterm
        · have hsucc : i.succ ≤ l := by
            change i.val ≤ l.val at hil
            have hli' : l.val ≠ i.val := by
              intro hval
              apply hli
              apply Fin.ext
              exact hval
            change i.val + 1 ≤ l.val
            omega
          exact ih l hsucc
  change w j = v j
  exact (show P j from hP j) j j.le_refl

end SphereSixComplex
