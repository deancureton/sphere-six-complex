module

public import SphereSixComplex.Geometry.CuspStraighteningHomeomorph

/-!
# Joint continuity of the standard toric action

The action of an algebraic torus on a toric variety is jointly algebraic, hence continuous.
The current toric-model interface exposes continuity of every fixed multiplier and holomorphicity
for smooth parameter families, but not this joint-continuity theorem.  This file isolates that
standard toric fact; it contains no cusp straightening, quotient, or retraction conclusion.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Geometry.CuspStraighteningExtension
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel

/-- Every integral character of the dense algebraic torus is continuous. -/
public theorem continuous_evaluateCharacter (m : FanLattice) :
    Continuous fun x : DenseTorus ↦ ((evaluateCharacter m x : ℂˣ) : ℂ) := by
  refine Units.continuous_val.comp ?_
  exact continuous_finsetProd _ fun j _ ↦ (continuous_apply j).zpow (m j)

/-- Characters of the dense algebraic torus are multiplicative. -/
public theorem evaluateCharacter_mul (m : FanLattice) (g x : DenseTorus) :
    evaluateCharacter m (g * x) = evaluateCharacter m g * evaluateCharacter m x := by
  simp [evaluateCharacter, mul_zpow, Finset.prod_mul_distrib]

/-- Joint continuity of the algebraic torus action on the standard infinite `A₂` toric model.
In a unimodular affine chart the action is coordinatewise multiplication by the characters dual
to the cone rays; that formula is jointly continuous, and it agrees with the action on the dense
torus, hence on the whole chart source by density and separation. -/
public theorem establishedContinuousTorusAction (M : Model) : ContinuousTorusAction M := by
  constructor
  rw [continuous_iff_continuousAt]
  rintro ⟨g₀, p₀⟩
  obtain ⟨upper, v, hp₀⟩ := M.toricChart_cover p₀
  set e := M.toricChart upper v with he
  set G : DenseTorus × M.Carrier → M.Carrier := fun z ↦
    e.invFun (WithLp.toLp 2 fun i ↦
      ((evaluateCharacter (a2DualCharacter upper v i) z.1 : ℂˣ) : ℂ) * e z.2 i) with hG
  have htarget : e.target = Set.univ := M.toricChart_target upper v
  have hinv : Continuous e.invFun := by
    have := e.contMDiffOn_invFun.continuousOn
    rw [htarget, continuousOn_univ] at this
    exact this
  have hchart : ContinuousOn (fun p : M.Carrier ↦ e p) e.source :=
    e.contMDiffOn_toFun.continuousOn
  have hGon : ContinuousOn G (Set.univ ×ˢ e.source) := by
    refine hinv.comp_continuousOn ?_
    refine (PiLp.continuous_toLp 2 _).comp_continuousOn ?_
    refine continuousOn_pi.2 fun i ↦ ?_
    refine ContinuousOn.mul ?_ ?_
    · exact ((continuous_evaluateCharacter (a2DualCharacter upper v i)).comp
        continuous_fst).continuousOn
    · exact ((PiLp.continuous_apply 2 _ i).comp_continuousOn
        (hchart.comp continuous_snd.continuousOn fun z hz ↦ hz.2))
  have key : ∀ g : DenseTorus,
      Set.EqOn (fun p ↦ M.torusAction g p) (fun p ↦ G (g, p)) e.source := by
    intro g
    refine Set.EqOn.of_subset_closure (s := Set.range M.torusEmbedding) ?_ ?_ ?_ ?_ ?_
    · rintro _ ⟨x, rfl⟩
      have hcoord : (WithLp.toLp 2 fun i ↦
          ((evaluateCharacter (a2DualCharacter upper v i) g : ℂˣ) : ℂ) *
            e (M.torusEmbedding x) i) = e (M.torusEmbedding (g * x)) := by
        rw [← WithLp.toLp_ofLp 2 (e (M.torusEmbedding (g * x)))]
        congr 1
        funext i
        show _ = e (M.torusEmbedding (g * x)) i
        rw [M.toricChart_torus_character upper v (g * x) i,
          M.toricChart_torus_character upper v x i, evaluateCharacter_mul]
        push_cast
        ring
      show M.torusAction g (M.torusEmbedding x) = G (g, M.torusEmbedding x)
      rw [M.torusAction_torus, hG]
      simp only [hcoord]
      exact (e.left_inv (M.torus_mem_toricChart upper v (g * x))).symm
    · exact ((M.torusAction_holomorphic g).continuous).continuousOn
    · exact (hGon.comp (Continuous.continuousOn (by fun_prop))
        (fun p hp ↦ ⟨Set.mem_univ _, hp⟩))
    · exact fun _ ⟨x, hx⟩ ↦ hx ▸ M.torus_mem_toricChart upper v x
    · rw [M.torus_dense.closure_range]
      exact Set.subset_univ _
  have hnhds : Set.univ ×ˢ e.source ∈ nhds (g₀, p₀) :=
    (isOpen_univ.prod e.open_source).mem_nhds ⟨Set.mem_univ _, hp₀⟩
  refine (hGon.continuousAt hnhds).congr ?_
  filter_upwards [hnhds] with z hz using (key z.1 hz.2).symm

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
