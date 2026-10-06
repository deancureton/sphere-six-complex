module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.EuclideanLocalVanishing
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.LocalStarConvex
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeVanishing
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeMayerVietoris
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CompactSupport

@[expose] public section


section

noncomputable section

open CategoryTheory Module Set

universe u

namespace DifferentialGeometry.Topology

private theorem integralRelativeHomology_empty_complement_subsingleton
    {X : Type u} [TopologicalSpace X] (n : ℕ) :
    Subsingleton (integralRelativeHomology n (∅ : Set X)ᶜ) := by
  simpa only [compl_empty] using integralRelativeHomology_univ_subsingleton (X := X) n

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem integralRelativeHomology_subsingleton_of_bounded_starConvex
    (n : ℕ) (hn : finrank ℝ E < n) {K : Set E} {c : E}
    (hs : StarConvex ℝ c K) (hb : Bornology.IsBounded K) :
    Subsingleton (integralRelativeHomology n Kᶜ) := by
  rcases K.eq_empty_or_nonempty with rfl | hK
  · exact integralRelativeHomology_empty_complement_subsingleton n
  · let := integralLocalHomology_subsingleton_of_finrank_lt n hn c
    let e := (integralBoundedStarConvexLocalHomologyIso n (hs.mem hK) hs hb).toLinearEquiv
    exact ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩

theorem integralRelativeHomology_subsingleton_of_bounded_convex
    (n : ℕ) (hn : finrank ℝ E < n) {K : Set E}
    (hK : Convex ℝ K) (hb : Bornology.IsBounded K) :
    Subsingleton (integralRelativeHomology n Kᶜ) := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨c, hc⟩
  · exact integralRelativeHomology_empty_complement_subsingleton n
  · exact integralRelativeHomology_subsingleton_of_bounded_starConvex n hn (hK.starConvex hc) hb

theorem integralRelativeHomology_subsingleton_of_compact_convex
    (n : ℕ) (hn : finrank ℝ E < n) {K : Set E}
    (hK : Convex ℝ K) (hc : IsCompact K) :
    Subsingleton (integralRelativeHomology n Kᶜ) :=
  integralRelativeHomology_subsingleton_of_bounded_convex n hn hK hc.isBounded

end DifferentialGeometry.Topology

end

end


section

open Set

namespace DifferentialGeometry.Topology

private theorem exists_finite_closed_ball_neighborhood
    {E : Type*} [PseudoMetricSpace E] (K U : Set E)
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ r : K → ℝ, (∀ x, 0 < r x) ∧ ∃ t : Finset K,
      K ⊆ interior (⋃ x ∈ t, Metric.closedBall x.val (r x)) ∧
      (⋃ x ∈ t, Metric.closedBall x.val (r x)) ⊆ U := by
  classical
  have hlocal (x : K) : ∃ r : ℝ, 0 < r ∧ Metric.closedBall x.val r ⊆ U :=
    Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds (hKU x.property))
  choose r hr hsub using hlocal
  have hcover : K ⊆ ⋃ x : K, Metric.ball x.val (r x) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hr _)⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => Metric.ball x.val (r x))
    (fun _ => Metric.isOpen_ball) hcover
  refine ⟨r, hr, t, ht.trans ?_, ?_⟩
  · apply (isOpen_biUnion fun (x : K) (_ : x ∈ t) =>
      Metric.isOpen_ball (x := x.val) (ε := r x)).subset_interior_iff.mpr
    exact iUnion₂_mono fun _ _ => Metric.ball_subset_closedBall
  · exact iUnion₂_subset fun x _ => hsub x

end DifferentialGeometry.Topology

end


section

noncomputable section

open Set Module

universe u v

namespace DifferentialGeometry.Topology

private theorem relative_union_subsingleton_of_inter
    {X : Type u} [TopologicalSpace X] (n : ℕ) (K L : Set X)
    (hK : IsClosed K) (hL : IsClosed L)
    [Subsingleton (integralRelativeHomology n Kᶜ)]
    [Subsingleton (integralRelativeHomology n Lᶜ)]
    [Subsingleton (integralRelativeHomology (n + 1) (K ∩ L)ᶜ)] :
    Subsingleton (integralRelativeHomology n (K ∪ L)ᶜ) := by
  let : Subsingleton (integralRelativeHomology (n + 1) (Kᶜ ∪ Lᶜ)) := by
    rw [← compl_inter]
    infer_instance
  rw [compl_union]
  exact ⟨fun a b => relative_homology_inter_eq_of_restrictions_eq n Kᶜ Lᶜ
    hK.isOpen_compl hL.isOpen_compl a b (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

private theorem relative_finite_convex_union_vanishing
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type v} (s : Finset ι) (K : ι → Set E)
    (hconv : ∀ i ∈ s, Convex ℝ (K i)) (hcompact : ∀ i ∈ s, IsCompact (K i))
    (n : ℕ) (hn : finrank ℝ E < n) :
    Subsingleton (integralRelativeHomology n (⋃ i ∈ s, K i)ᶜ) := by
  classical
  induction s using Finset.induction_on generalizing K n with
  | empty =>
    simpa only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, compl_empty] using
      integralRelativeHomology_univ_subsingleton (X := E) n
  | @insert i s hi ih =>
    have hci : Convex ℝ (K i) := hconv i (Finset.mem_insert_self i s)
    have hki : IsCompact (K i) := hcompact i (Finset.mem_insert_self i s)
    have hcs : ∀ j ∈ s, Convex ℝ (K j) :=
      fun j hj => hconv j (Finset.mem_insert_of_mem hj)
    have hks : ∀ j ∈ s, IsCompact (K j) :=
      fun j hj => hcompact j (Finset.mem_insert_of_mem hj)
    let U := ⋃ j ∈ s, K j
    have hU : IsCompact U := s.isCompact_biUnion hks
    let := integralRelativeHomology_subsingleton_of_compact_convex n hn hci hki
    let : Subsingleton (integralRelativeHomology n Uᶜ) := ih K hcs hks n hn
    let : Subsingleton (integralRelativeHomology (n + 1) (K i ∩ U)ᶜ) := by
      have h := ih (fun j => K i ∩ K j)
        (fun j hj => hci.inter (hcs j hj))
        (fun j hj => hki.inter (hks j hj)) (n + 1) (by omega)
      simpa only [U, inter_iUnion] using h
    have h := relative_union_subsingleton_of_inter n (K i) U hki.isClosed hU.isClosed
    simpa only [Finset.mem_insert, iUnion_iUnion_eq_or_left, U] using h

end DifferentialGeometry.Topology

end

end


section

noncomputable section

open Set Module

universe u

namespace DifferentialGeometry.Topology

theorem integralRelativeHomology_subsingleton_of_compact
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (n : ℕ) (hn : finrank ℝ E < n) (K : Set E) (hK : IsCompact K) :
    Subsingleton (integralRelativeHomology n Kᶜ) := by
  have hz (a : integralRelativeHomology n Kᶜ) : a = 0 := by
    obtain ⟨L, hKL, _, _, b, hb⟩ := exists_relative_homology_class_on_compact_neighborhood
      n K univ hK isOpen_univ (subset_univ _) a
    obtain ⟨r, _, t, hKC, hCL⟩ := exists_finite_closed_ball_neighborhood
      K (interior L) hK isOpen_interior hKL
    let C := ⋃ x ∈ t, Metric.closedBall x.val (r x)
    let : Subsingleton (integralRelativeHomology n Cᶜ) :=
      relative_finite_convex_union_vanishing t (fun x => Metric.closedBall x.val (r x))
        (fun x _ => convex_closedBall x.val (r x))
        (fun x _ => isCompact_closedBall x.val (r x)) n hn
    have hLC : MapsTo (ContinuousMap.id E) Lᶜ Cᶜ :=
      fun _ hx hxC => hx (interior_subset (hCL hxC))
    have hCK : MapsTo (ContinuousMap.id E) Cᶜ Kᶜ :=
      fun _ hx hxK => hx (interior_subset (hKC hxK))
    have hcomp := integralRelativeHomologyMap_comp n (ContinuousMap.id E)
      (ContinuousMap.id E) hLC hCK
    calc
      a = integralRelativeHomologyMap n (ContinuousMap.id E)
          (show MapsTo (ContinuousMap.id E) Lᶜ Kᶜ from
            fun _ hx hxK => hx (interior_subset (hKL hxK))) b := hb.symm
      _ = integralRelativeHomologyMap n (ContinuousMap.id E) hCK
          (integralRelativeHomologyMap n (ContinuousMap.id E) hLC b) := by
        exact congrArg (fun f : integralRelativeHomology n Lᶜ →ₗ[ℤ]
          integralRelativeHomology n Kᶜ => f b) hcomp
      _ = integralRelativeHomologyMap n (ContinuousMap.id E) hCK 0 :=
        congrArg _ (Subsingleton.elim _ _)
      _ = 0 := map_zero _
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

end DifferentialGeometry.Topology

end

end
