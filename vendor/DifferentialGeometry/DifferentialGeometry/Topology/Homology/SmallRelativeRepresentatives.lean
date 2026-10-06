module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SmallCycles
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ChainCokernelElements
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeFunctoriality
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.TwoSetSmallChains

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u v w

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] {ι : Type v} {κ : Type w}

theorem exists_small_relative_homology_representative (n : ℕ) (A : Set X)
    (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcoverU : ∀ x, ∃ i, x ∈ U i)
    (a : integralRelativeHomology n A) :
    ∃ (c : (integralSingularChains X).X n)
      (z : LinearMap.ker ((integralRelativeChains A).sc n).g.hom),
      c ∈ integralSingularSmallChains n U ∧
      (integralSingularChains X).d n ((ComplexShape.down ℕ).next n) c ∈
        integralSingularChainsIn ((ComplexShape.down ℕ).next n) A ∧
      (integralRelativeChainSequence A).g.f n c = z.val ∧
      moduleHomologyClass ((integralRelativeChains A).sc n) z = a := by
  obtain ⟨z, hz⟩ := moduleHomologyClass_surjective ((integralRelativeChains A).sc n) a
  obtain ⟨c, hc⟩ := chainCokernelπ_surjective
    (integralSingularChainMap (singularSubspaceInclusion A)) n z.val
  let π : integralSingularChains X ⟶ integralRelativeChains A :=
    (integralRelativeChainSequence A).g
  have hcarrier (m : ℕ) (b : (integralSingularChains X).X m) :
      π.f m b = 0 ↔ b ∈ integralSingularChainsIn m A := by
    rw [integralSingularChainsIn_eq_range]
    exact chainCokernelπ_eq_zero_iff _ m b
  have hdc : (integralSingularChains X).d n ((ComplexShape.down ℕ).next n) c ∈
      integralSingularChainsIn ((ComplexShape.down ℕ).next n) A := by
    apply (hcarrier _ _).mp
    have h := congrArg (fun f : (integralSingularChains X).X n ⟶
      (integralRelativeChains A).X ((ComplexShape.down ℕ).next n) => f c)
      (π.comm n ((ComplexShape.down ℕ).next n))
    change (integralRelativeChains A).d n ((ComplexShape.down ℕ).next n)
      (π.f n c) = π.f _ ((integralSingularChains X).d n _ c) at h
    rw [← h]
    change ((integralRelativeChains A).sc n).g
      ((cokernel.π (integralSingularChainMap (singularSubspaceInclusion A))).f n c) = 0
    rw [hc]
    exact z.property
  cases n with
  | zero =>
    exact ⟨c, z, integralSingularSmallChains_zero_all U hU hcoverU c, hdc, hc, hz⟩
  | succ n =>
    have hnext : (ComplexShape.down ℕ).next (n + 1) = n :=
      (ComplexShape.down ℕ).next_eq' rfl
    rw [hnext] at hdc
    obtain ⟨k, hk⟩ := exists_integralSingularSubdivisionIterate_small (n + 1) U hU hcoverU c
    let s := integralSingularSubdivisionIterate (n + 1) k c
    have hds : (integralSingularChains X).d (n + 1) n s ∈ integralSingularChainsIn n A := by
      rw [integralSingularSubdivisionIterate_boundary]
      exact integralSingularSubdivisionIterate_mem n k A hdc
    have hws : ((integralRelativeChains A).sc (n + 1)).g (π.f (n + 1) s) = 0 := by
      change (integralRelativeChains A).d (n + 1) ((ComplexShape.down ℕ).next (n + 1))
        (π.f (n + 1) s) = 0
      rw [hnext]
      have h := congrArg (fun f : (integralSingularChains X).X (n + 1) ⟶
        (integralRelativeChains A).X n => f s) (π.comm (n + 1) n)
      exact h.trans ((hcarrier n _).mpr hds)
    let w : LinearMap.ker ((integralRelativeChains A).sc (n + 1)).g.hom :=
      ⟨π.f (n + 1) s, hws⟩
    refine ⟨s, w, hk k le_rfl, ?_, rfl, ?_⟩
    · rw [hnext]
      exact hds
    · have hclass : moduleHomologyClass ((integralRelativeChains A).sc (n + 1)) z =
          moduleHomologyClass ((integralRelativeChains A).sc (n + 1)) w := by
        have hboundary : (integralRelativeChains A).d (n + 2) (n + 1)
            (π.f (n + 2) (integralSingularSubdivisionIterateHomotopy (n + 1) k c)) =
              π.f (n + 1) c - π.f (n + 1) s := by
          have h := congrArg (fun f : (integralSingularChains X).X (n + 2) ⟶
            (integralRelativeChains A).X (n + 1) =>
            f (integralSingularSubdivisionIterateHomotopy (n + 1) k c))
            (π.comm (n + 2) (n + 1))
          change (integralRelativeChains A).d (n + 2) (n + 1)
            (π.f (n + 2) (integralSingularSubdivisionIterateHomotopy (n + 1) k c)) =
              π.f (n + 1) ((integralSingularChains X).d (n + 2) (n + 1)
                (integralSingularSubdivisionIterateHomotopy (n + 1) k c)) at h
          rw [h, integralSingularSubdivisionIterateHomotopy_boundary, map_sub, map_sub]
          have hH : π.f (n + 1)
              (integralSingularSubdivisionIterateHomotopy n k
                ((integralSingularChains X).d (n + 1) n c)) = 0 :=
            (hcarrier _ _).mpr (integralSingularSubdivisionIterateHomotopy_mem n k A hdc)
          rw [hH, sub_zero]
        apply (moduleHomologyClass_eq_iff _ z w).mpr
        change ∃ b : (integralRelativeChains A).X ((ComplexShape.down ℕ).prev (n + 1)),
          (integralRelativeChains A).d ((ComplexShape.down ℕ).prev (n + 1)) (n + 1) b =
            z.val - w.val
        rw [ChainComplex.prev]
        refine ⟨π.f (n + 2) (integralSingularSubdivisionIterateHomotopy (n + 1) k c), ?_⟩
        exact hboundary.trans (congrArg₂ (fun b d : (integralRelativeChains A).X (n + 1) => b - d)
          hc (rfl : π.f (n + 1) s = w.val))
      exact hclass.symm.trans hz

theorem exists_small_relative_homology_representative_two_covers (n : ℕ) (A : Set X)
    (U : ι → Set X) (V : κ → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcoverU : ∀ x, ∃ i, x ∈ U i)
    (hV : ∀ i, IsOpen (V i)) (hcoverV : ∀ x, ∃ i, x ∈ V i)
    (a : integralRelativeHomology n A) :
    ∃ (c : (integralSingularChains X).X n)
      (z : LinearMap.ker ((integralRelativeChains A).sc n).g.hom),
      c ∈ integralSingularSmallChains n U ∧
      c ∈ integralSingularSmallChains n V ∧
      (integralSingularChains X).d n ((ComplexShape.down ℕ).next n) c ∈
        integralSingularChainsIn ((ComplexShape.down ℕ).next n) A ∧
      (integralRelativeChainSequence A).g.f n c = z.val ∧
      moduleHomologyClass ((integralRelativeChains A).sc n) z = a := by
  let W : ι × κ → Set X := fun i => U i.1 ∩ V i.2
  have hW : ∀ i, IsOpen (W i) := fun i => (hU i.1).inter (hV i.2)
  have hcoverW : ∀ x, ∃ i, x ∈ W i := by
    intro x
    obtain ⟨i, hi⟩ := hcoverU x
    obtain ⟨j, hj⟩ := hcoverV x
    exact ⟨(i, j), hi, hj⟩
  obtain ⟨c, z, hc, hdc, hπ, hz⟩ :=
    exists_small_relative_homology_representative n A W hW hcoverW a
  exact ⟨c, z, integralSingularSmallChains_refinement n W U
    (fun i => ⟨i.1, inter_subset_left⟩) hc,
    integralSingularSmallChains_refinement n W V (fun i => ⟨i.2, inter_subset_right⟩) hc,
    hdc, hπ, hz⟩

end DifferentialGeometry.Topology

end

noncomputable section

open CategoryTheory Set

universe u v w

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] {J : Type v} {ι : J → Type w}

theorem exists_small_relative_homology_representative_finite_covers [Finite J]
    (n : ℕ) (A : Set X) (U : (j : J) → ι j → Set X)
    (hU : ∀ j i, IsOpen (U j i)) (hcoverU : ∀ j x, ∃ i, x ∈ U j i)
    (a : integralRelativeHomology n A) :
    ∃ (c : (integralSingularChains X).X n)
      (z : LinearMap.ker ((integralRelativeChains A).sc n).g.hom),
      (∀ j, c ∈ integralSingularSmallChains n (U j)) ∧
      (integralSingularChains X).d n ((ComplexShape.down ℕ).next n) c ∈
        integralSingularChainsIn ((ComplexShape.down ℕ).next n) A ∧
      (integralRelativeChainSequence A).g.f n c = z.val ∧
      moduleHomologyClass ((integralRelativeChains A).sc n) z = a := by
  classical
  let V : ((j : J) → ι j) → Set X := fun i => ⋂ j, U j (i j)
  have hV : ∀ i, IsOpen (V i) := fun i => isOpen_iInter_of_finite (fun j => hU j (i j))
  have hcoverV : ∀ x, ∃ i, x ∈ V i := by
    intro x
    choose i hi using fun j => hcoverU j x
    exact ⟨i, mem_iInter.mpr hi⟩
  obtain ⟨c, z, hc, hdc, hπ, hz⟩ :=
    exists_small_relative_homology_representative n A V hV hcoverV a
  exact ⟨c, z, fun j => integralSingularSmallChains_refinement n V (U j)
    (fun i => ⟨i j, iInter_subset (fun j => U j (i j)) j⟩) hc, hdc, hπ, hz⟩

end DifferentialGeometry.Topology

end

noncomputable section

open CategoryTheory Set

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem exists_relative_subspace_cycle_of_small
    (n : ℕ) (W A : Set X)
    (c : (integralSingularChains X).X n)
    (hsmall : c ∈ integralSingularSmallChains n (twoSetCover W A))
    (z : LinearMap.ker ((integralRelativeChains A).sc n).g.hom)
    (hc : (integralRelativeChainSequence A).g.f n c = z.val) :
    ∃ a : (integralSingularChains W).X n,
      ∃ w : LinearMap.ker ((integralRelativeChains (subspaceIntersection A W)).sc n).g.hom,
        (integralRelativeChainSequence (subspaceIntersection A W)).g.f n a = w.val ∧
        (integralRelativeChainMap (singularSubspaceInclusion W)
          (show MapsTo (singularSubspaceInclusion W) (subspaceIntersection A W) A from
            fun _ hx => hx)).f n w.val = z.val ∧
        c - (integralSingularChainMap (singularSubspaceInclusion W)).f n a ∈
          integralSingularChainsIn n A := by
  obtain ⟨a, b, hab⟩ := integralSingularTwoSetSmallChains_decompose n W A ⟨c, hsmall⟩
  change (integralSingularChainMap (singularSubspaceInclusion W)).f n a +
    (integralSingularChainMap (singularSubspaceInclusion A)).f n b = c at hab
  have hrem : c - (integralSingularChainMap (singularSubspaceInclusion W)).f n a ∈
      integralSingularChainsIn n A := by
    have he : c - (integralSingularChainMap (singularSubspaceInclusion W)).f n a =
        (integralSingularChainMap (singularSubspaceInclusion A)).f n b := by
      rw [← hab]
      abel
    rw [he, integralSingularChainsIn_eq_range]
    exact ⟨b, rfl⟩
  let πA : integralSingularChains X ⟶ integralRelativeChains A := (integralRelativeChainSequence A).g
  let πW : integralSingularChains W ⟶ integralRelativeChains (subspaceIntersection A W) := (integralRelativeChainSequence (subspaceIntersection A W)).g
  change πA.f n c = z.val at hc
  let f := integralRelativeChainMap (singularSubspaceInclusion W)
    (show MapsTo (singularSubspaceInclusion W) (subspaceIntersection A W) A from
      fun _ hx => hx)
  have hrem0 : πA.f n (c - (integralSingularChainMap (singularSubspaceInclusion W)).f n a) = 0 := by
    apply (chainCokernelπ_eq_zero_iff _ n _).2
    exact (integralSingularChainsIn_eq_range n A).le hrem
  have ha : πA.f n ((integralSingularChainMap (singularSubspaceInclusion W)).f n a) = z.val := by
    rw [map_sub] at hrem0
    exact (sub_eq_zero.mp hrem0).symm.trans hc
  have hf : f.f n (πW.f n a) = z.val := by
    have h := congrArg (fun g : integralSingularChains W ⟶ integralRelativeChains A => g.f n a)
      (integralRelativeChainMap_π (singularSubspaceInclusion W)
        (show MapsTo (singularSubspaceInclusion W) (subspaceIntersection A W) A from
          fun _ hx => hx))
    exact h.trans ha
  let j := (ComplexShape.down ℕ).next n
  have hdz : πA.f j ((integralSingularChains X).d n j c) = 0 := by
    have h := congrArg (fun g : (integralSingularChains X).X n ⟶
      (integralRelativeChains A).X j => g c) (πA.comm n j)
    change (integralRelativeChains A).d n j (πA.f n c) =
      πA.f j ((integralSingularChains X).d n j c) at h
    rw [hc] at h
    exact h.symm.trans z.property
  have hdcA : (integralSingularChains X).d n j c ∈ integralSingularChainsIn j A := by
    rw [integralSingularChainsIn_eq_range]
    exact (chainCokernelπ_eq_zero_iff _ j _).1 hdz
  have hda : (integralSingularChains W).d n j a ∈
      integralSingularChainsIn j (subspaceIntersection A W) := by
    rw [integralSingularChainsIn_subspace_iff]
    have h := congrArg (fun g : (integralSingularChains W).X n ⟶
      (integralSingularChains X).X j => g a)
      ((integralSingularChainMap (singularSubspaceInclusion W)).comm n j)
    change (integralSingularChains X).d n j
      ((integralSingularChainMap (singularSubspaceInclusion W)).f n a) =
      (integralSingularChainMap (singularSubspaceInclusion W)).f j
        ((integralSingularChains W).d n j a) at h
    rw [← h]
    have hremD := integralSingularSmallChains_d n j (fun _ : Unit => A)
      (show c - (integralSingularChainMap (singularSubspaceInclusion W)).f n a ∈
        integralSingularSmallChains n (fun _ : Unit => A) from by
          simpa only [integralSingularSmallChains, iSup_const] using hrem)
    simp only [integralSingularSmallChains, iSup_const] at hremD
    rw [map_sub] at hremD
    have hs := (integralSingularChainsIn j A).sub_mem hdcA hremD
    have he : (integralSingularChains X).d n j c -
        ((integralSingularChains X).d n j c -
          (integralSingularChains X).d n j
            ((integralSingularChainMap (singularSubspaceInclusion W)).f n a)) =
        (integralSingularChains X).d n j
          ((integralSingularChainMap (singularSubspaceInclusion W)).f n a) := by abel
    exact he ▸ hs
  have hw : πW.f n a ∈ LinearMap.ker ((integralRelativeChains (subspaceIntersection A W)).sc n).g.hom := by
    change (integralRelativeChains (subspaceIntersection A W)).d n j (πW.f n a) = 0
    have h := congrArg (fun g : (integralSingularChains W).X n ⟶
      (integralRelativeChains (subspaceIntersection A W)).X j => g a) (πW.comm n j)
    change (integralRelativeChains (subspaceIntersection A W)).d n j (πW.f n a) =
      πW.f j ((integralSingularChains W).d n j a) at h
    refine h.trans ?_
    apply (chainCokernelπ_eq_zero_iff _ j _).2
    exact (integralSingularChainsIn_eq_range j (subspaceIntersection A W)).le hda
  exact ⟨a, ⟨πW.f n a, hw⟩, rfl, hf, hrem⟩

end DifferentialGeometry.Topology

end
