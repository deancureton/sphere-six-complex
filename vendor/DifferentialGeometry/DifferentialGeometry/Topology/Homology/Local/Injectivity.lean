module

public import DifferentialGeometry.Topology.Homology.Local.PointRestriction

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

variable (R : ModuleCat.{u} ℤ)

section charted

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem relπ_compl_eq_zero_of_forall_ptRes (hn : 1 ≤ n) {A : Set M} (hA : IsCompact A)
    (c : singularHomology R (TopCat.of M) n) (h : ∀ x ∈ A, ptRes R (TopCat.of M) n c x = 0) :
    relπ R (TopCat.of M) Aᶜ n c = 0 :=
  (localGood.of_isCompact R hn hA).2 _ fun x hx => by
    rw [ptRes_res R hx n c]
    exact h x hx

theorem eq_zero_of_forall_ptRes [CompactSpace M] (hn : 1 ≤ n) (c : singularHomology R (TopCat.of M) n)
    (h : ∀ x, ptRes R (TopCat.of M) n c x = 0) : c = 0 := by
  have h0 := relπ_compl_eq_zero_of_forall_ptRes R hn isCompact_univ c fun x _ => h x
  rw [Set.compl_univ] at h0
  have hmono : Mono (relπ R (TopCat.of M) ∅ n) := by
    have := isIso_relπ_empty R (TopCat.of M) n
    infer_instance
  exact ((ModuleCat.mono_iff_injective (relπ R (TopCat.of M) ∅ n)).1 hmono)
    (h0.trans (map_zero _).symm)

theorem mono_relπ_compl_singleton (hn : 1 ≤ n) [CompactSpace M] [ConnectedSpace M] (x : M) :
    Mono (relπ R (TopCat.of M) {x}ᶜ n) := by
  rw [ModuleCat.mono_iff_injective, injective_iff_map_eq_zero]
  intro c hc
  exact eq_zero_of_forall_ptRes R hn c (ptRes_eq_zero_of_exists R hn c ⟨x, hc⟩)

theorem ptRes_injective (hn : 1 ≤ n) [CompactSpace M] [ConnectedSpace M] (x : M) :
    Function.Injective fun c : singularHomology R (TopCat.of M) n => ptRes R (TopCat.of M) n c x :=
  (ModuleCat.mono_iff_injective _).1 (mono_relπ_compl_singleton R hn x)

end charted

end DifferentialGeometry.Topology.SingularPair

end
