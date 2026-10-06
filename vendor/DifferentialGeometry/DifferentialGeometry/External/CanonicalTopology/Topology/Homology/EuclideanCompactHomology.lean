module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.LocalStarConvex
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Sets.Compacts

@[expose] public section
noncomputable section

open Set

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem bounded_star_convex_local_class_restrict
    (n : ℕ) {p : E} {K L : Set E}
    (hpK : p ∈ K) (hsK : StarConvex ℝ p K) (hbK : Bornology.IsBounded K)
    (hpL : p ∈ L) (hsL : StarConvex ℝ p L) (hbL : Bornology.IsBounded L)
    (hKL : K ⊆ L) (a : integralLocalHomology n p) :
    integralRelativeHomologyMap n (ContinuousMap.id E)
        (show MapsTo (ContinuousMap.id E) Lᶜ Kᶜ from compl_subset_compl.mpr hKL)
        ((integralBoundedStarConvexLocalHomologyIso n hpL hsL hbL).toLinearEquiv.symm a) =
      (integralBoundedStarConvexLocalHomologyIso n hpK hsK hbK).toLinearEquiv.symm a := by
  let eK := (integralBoundedStarConvexLocalHomologyIso n hpK hsK hbK).toLinearEquiv
  let eL := (integralBoundedStarConvexLocalHomologyIso n hpL hsL hbL).toLinearEquiv
  apply eK.injective
  have hcomp := LinearMap.congr_fun (integralRelativeHomologyMap_comp n
    (ContinuousMap.id E) (ContinuousMap.id E)
    (show MapsTo (ContinuousMap.id E) Lᶜ Kᶜ from compl_subset_compl.mpr hKL)
    (show MapsTo (ContinuousMap.id E) Kᶜ ({p}ᶜ : Set E) from
      compl_subset_compl.mpr (singleton_subset_iff.mpr hpK))) (eL.symm a)
  exact hcomp.symm.trans ((eL.apply_symm_apply a).trans (eK.apply_symm_apply a).symm)

private theorem bounded_star_convex_local_class_independent
    (n : ℕ) {p : E} {S K L : Set E}
    (hpK : p ∈ K) (hsK : StarConvex ℝ p K) (hbK : Bornology.IsBounded K)
    (hpL : p ∈ L) (hsL : StarConvex ℝ p L) (hbL : Bornology.IsBounded L)
    (hSK : S ⊆ K) (hSL : S ⊆ L) (a : integralLocalHomology n p) :
    integralRelativeHomologyMap n (ContinuousMap.id E)
        (show MapsTo (ContinuousMap.id E) Kᶜ Sᶜ from compl_subset_compl.mpr hSK)
        ((integralBoundedStarConvexLocalHomologyIso n hpK hsK hbK).toLinearEquiv.symm a) =
      integralRelativeHomologyMap n (ContinuousMap.id E)
        (show MapsTo (ContinuousMap.id E) Lᶜ Sᶜ from compl_subset_compl.mpr hSL)
        ((integralBoundedStarConvexLocalHomologyIso n hpL hsL hbL).toLinearEquiv.symm a) := by
  let b := (integralBoundedStarConvexLocalHomologyIso n (K := K ∪ L) (c := p)
    (Or.inl hpK : p ∈ K ∪ L)
    (hsK.union hsL) (hbK.union hbL)).toLinearEquiv.symm a
  have hK := bounded_star_convex_local_class_restrict n hpK hsK hbK
    (Or.inl hpK : p ∈ K ∪ L) (hsK.union hsL) (hbK.union hbL) subset_union_left a
  have hL := bounded_star_convex_local_class_restrict n hpL hsL hbL
    (Or.inl hpK : p ∈ K ∪ L) (hsK.union hsL) (hbK.union hbL) subset_union_right a
  have hcompK := LinearMap.congr_fun (integralRelativeHomologyMap_comp n
    (ContinuousMap.id E) (ContinuousMap.id E)
    (show MapsTo (ContinuousMap.id E) (K ∪ L)ᶜ Kᶜ from
      compl_subset_compl.mpr subset_union_left)
    (show MapsTo (ContinuousMap.id E) Kᶜ Sᶜ from compl_subset_compl.mpr hSK)) b
  have hcompL := LinearMap.congr_fun (integralRelativeHomologyMap_comp n
    (ContinuousMap.id E) (ContinuousMap.id E)
    (show MapsTo (ContinuousMap.id E) (K ∪ L)ᶜ Lᶜ from
      compl_subset_compl.mpr subset_union_right)
    (show MapsTo (ContinuousMap.id E) Lᶜ Sᶜ from compl_subset_compl.mpr hSL)) b
  simp only [LinearMap.comp_apply] at hcompK hcompL
  rw [hK] at hcompK
  rw [hL] at hcompL
  exact hcompK.symm.trans hcompL

end DifferentialGeometry.Topology

end

noncomputable section

open TopologicalSpace Set Metric

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem exists_compact_star_convex_superset (p : E) (K : Compacts E) :
    ∃ L : Compacts E, K ≤ L ∧ p ∈ (L : Set E) ∧ StarConvex ℝ p (L : Set E) := by
  obtain ⟨r, hr, hKr⟩ := K.isCompact.isBounded.subset_closedBall_lt 0 p
  have hp : p ∈ closedBall p r := mem_closedBall_self hr.le
  exact ⟨⟨closedBall p r, isCompact_closedBall p r⟩, hKr, hp,
    (convex_closedBall p r).starConvex hp⟩

theorem exists_unique_compact_homology_family_of_local_class
    (n : ℕ) (p : E) (a : integralLocalHomology n p) :
    ∃! c : ∀ K : Compacts E, integralRelativeHomology n (K : Set E)ᶜ,
      (∀ (K L : Compacts E) (h : K ≤ L),
        integralRelativeHomologyMap n (ContinuousMap.id E)
          (show MapsTo (ContinuousMap.id E) (L : Set E)ᶜ (K : Set E)ᶜ from
            compl_subset_compl.mpr h) (c L) = c K) ∧ c {p} = a := by
  choose L hKL hpL hsL using exists_compact_star_convex_superset p
  let e (K : Compacts E) := (integralBoundedStarConvexLocalHomologyIso n
    (hpL K) (hsL K) (L K).isCompact.isBounded).toLinearEquiv
  let c (K : Compacts E) : integralRelativeHomology n (K : Set E)ᶜ :=
    integralRelativeHomologyMap n (ContinuousMap.id E)
      (show MapsTo (ContinuousMap.id E) (L K : Set E)ᶜ (K : Set E)ᶜ from
        compl_subset_compl.mpr (hKL K)) ((e K).symm a)
  refine ⟨c, ⟨?_, ?_⟩, ?_⟩
  · intro K J hKJ
    have hcomp := LinearMap.congr_fun (integralRelativeHomologyMap_comp n
      (ContinuousMap.id E) (ContinuousMap.id E)
      (show MapsTo (ContinuousMap.id E) (L J : Set E)ᶜ (J : Set E)ᶜ from
        compl_subset_compl.mpr (hKL J))
      (show MapsTo (ContinuousMap.id E) (J : Set E)ᶜ (K : Set E)ᶜ from
        compl_subset_compl.mpr hKJ)) ((e J).symm a)
    have hind := bounded_star_convex_local_class_independent n
      (hpL J) (hsL J) (L J).isCompact.isBounded
      (hpL K) (hsL K) (L K).isCompact.isBounded
      (hKJ.trans (hKL J)) (hKL K) a
    exact hcomp.symm.trans hind
  · exact (e {p}).apply_symm_apply a
  · intro d hd
    funext K
    have hdp : (e K) (d (L K)) = a :=
      (hd.1 {p} (L K) (singleton_subset_iff.mpr (hpL K))).trans hd.2
    have hdL : d (L K) = (e K).symm a :=
      (e K).injective (hdp.trans ((e K).apply_symm_apply a).symm)
    exact (hd.1 K (L K) (hKL K)).symm.trans
      (congrArg (integralRelativeHomologyMap n (ContinuousMap.id E)
        (show MapsTo (ContinuousMap.id E) (L K : Set E)ᶜ (K : Set E)ᶜ from
          compl_subset_compl.mpr (hKL K))) hdL)

end DifferentialGeometry.Topology

end
