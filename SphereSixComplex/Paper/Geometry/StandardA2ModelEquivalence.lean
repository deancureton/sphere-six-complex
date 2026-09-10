module

public import SphereSixComplex.Paper.Geometry.StandardInfiniteA2ToricModel
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section
noncomputable section
open Set SphereSixComplex.Geometry.CuspCombinatorics SphereSixComplex.Geometry.CuspFilling

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Model

public def chartTransport (M N : Model) (upper : Bool) (v : ToricLattice)
    (p : M.Carrier) : N.Carrier :=
  (N.toricChart upper v).invFun (M.toricChart upper v p)

public theorem chartTransport_torus (M N : Model) (upper : Bool) (v : ToricLattice)
    (x : DenseTorus) : chartTransport M N upper v (M.torusEmbedding x) = N.torusEmbedding x := by
  have he : M.toricChart upper v (M.torusEmbedding x) =
      N.toricChart upper v (N.torusEmbedding x) := by
    ext i
    exact (M.toricChart_torus_character upper v x i).trans
      (N.toricChart_torus_character upper v x i).symm
  unfold chartTransport
  rw [he]
  exact (N.toricChart upper v).left_inv (N.torus_mem_toricChart upper v x)

public theorem chartTransport_continuousOn (M N : Model) (upper : Bool) (v : ToricLattice) :
    ContinuousOn (chartTransport M N upper v) (M.toricChart upper v).source := by
  have hn : Continuous (N.toricChart upper v).invFun := by
    rw [← continuousOn_univ, ← N.toricChart_target upper v]
    exact (N.toricChart upper v).contMDiffOn_invFun.continuousOn
  exact hn.comp_continuousOn (M.toricChart upper v).contMDiffOn_toFun.continuousOn

public theorem chartTransport_agree (M N : Model) (upper upper' : Bool) (v v' : ToricLattice) :
    EqOn (chartTransport M N upper v) (chartTransport M N upper' v')
      ((M.toricChart upper v).source ∩ (M.toricChart upper' v').source) := by
  let U := (M.toricChart upper v).source ∩ (M.toricChart upper' v').source
  have hU : IsOpen U := (M.toricChart upper v).open_source.inter
    (M.toricChart upper' v').open_source
  have he : EqOn (chartTransport M N upper v) (chartTransport M N upper' v')
      (U ∩ Set.range M.torusEmbedding) := by
    rintro p ⟨_, x, rfl⟩
    rw [chartTransport_torus, chartTransport_torus]
  exact he.of_subset_closure
    ((chartTransport_continuousOn M N upper v).mono inter_subset_left)
    ((chartTransport_continuousOn M N upper' v').mono inter_subset_right)
    inter_subset_left (M.torus_dense.open_subset_closure_inter hU)

public def transport (M N : Model) (p : M.Carrier) : N.Carrier :=
  chartTransport M N (M.toricChart_cover p).choose (M.toricChart_cover p).choose_spec.choose p

public theorem transport_eq_chartTransport (M N : Model) (upper : Bool) (v : ToricLattice)
    {p : M.Carrier} (hp : p ∈ (M.toricChart upper v).source) :
    transport M N p = chartTransport M N upper v p :=
  chartTransport_agree M N _ _ _ _ ⟨(M.toricChart_cover p).choose_spec.choose_spec, hp⟩

public theorem transport_torus (M N : Model) (x : DenseTorus) :
    transport M N (M.torusEmbedding x) = N.torusEmbedding x := by
  rw [transport_eq_chartTransport M N false 0 (M.torus_mem_toricChart false 0 x),
    chartTransport_torus]

public theorem transport_continuous (M N : Model) : Continuous (transport M N) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨upper, v, hp⟩ := M.toricChart_cover p
  have hnhds := (M.toricChart upper v).open_source.mem_nhds hp
  apply ((chartTransport_continuousOn M N upper v).continuousAt hnhds).congr_of_eventuallyEq
  filter_upwards [hnhds] with q hq
  exact transport_eq_chartTransport M N upper v hq

public theorem transport_left_inverse (M N : Model) :
    Function.LeftInverse (transport N M) (transport M N) := by
  intro p
  obtain ⟨upper, v, hp⟩ := M.toricChart_cover p
  rw [transport_eq_chartTransport M N upper v hp]
  have ht : M.toricChart upper v p ∈ (N.toricChart upper v).target := by
    rw [N.toricChart_target]
    trivial
  have hn : chartTransport M N upper v p ∈ (N.toricChart upper v).source :=
    (N.toricChart upper v).map_target ht
  rw [transport_eq_chartTransport N M upper v hn]
  dsimp only [chartTransport]
  have hr : N.toricChart upper v ((N.toricChart upper v).invFun
      (M.toricChart upper v p)) = M.toricChart upper v p :=
    (N.toricChart upper v).right_inv ht
  rw [hr]
  exact (M.toricChart upper v).left_inv hp

public def canonicalHomeomorph (M N : Model) : M.Carrier ≃ₜ N.Carrier where
  toFun := transport M N
  invFun := transport N M
  left_inv := transport_left_inverse M N
  right_inv := transport_left_inverse N M
  continuous_toFun := transport_continuous M N
  continuous_invFun := transport_continuous N M

public theorem transport_mem_chart (M N : Model) (upper : Bool) (v : ToricLattice)
    {p : M.Carrier} (hp : p ∈ (M.toricChart upper v).source) :
    transport M N p ∈ (N.toricChart upper v).source := by
  rw [transport_eq_chartTransport M N upper v hp]
  apply (N.toricChart upper v).map_target
  rw [N.toricChart_target]
  trivial

public theorem toricChart_transport (M N : Model) (upper : Bool) (v : ToricLattice)
    {p : M.Carrier} (hp : p ∈ (M.toricChart upper v).source) :
    N.toricChart upper v (transport M N p) = M.toricChart upper v p := by
  rw [transport_eq_chartTransport M N upper v hp]
  apply (N.toricChart upper v).right_inv
  rw [N.toricChart_target]
  trivial

public theorem transport_t (M N : Model) (p : M.Carrier) : N.t (transport M N p) = M.t p := by
  obtain ⟨upper, v, hp⟩ := M.toricChart_cover p
  rw [N.toricChart_t upper v _ (transport_mem_chart M N upper v hp),
    toricChart_transport M N upper v hp, M.toricChart_t upper v p hp]

public theorem transport_torusAction (M N : Model) (g : DenseTorus) (p : M.Carrier) :
    transport M N (M.torusAction g p) = N.torusAction g (transport M N p) := by
  apply congrFun (Continuous.ext_on M.torus_dense
    ((transport_continuous M N).comp (M.torusAction_holomorphic g).continuous)
    ((N.torusAction_holomorphic g).continuous.comp (transport_continuous M N)) ?_) p
  rintro q ⟨x, rfl⟩
  simp only [Function.comp_apply, M.torusAction_torus, transport_torus, N.torusAction_torus]

public theorem transport_fanShear (M N : Model) (g : CuspFilling.ParameterLattice)
    (p : M.Carrier) : transport M N (Additive.toMul (M.fanShear g) p) =
    Additive.toMul (N.fanShear g) (transport M N p) := by
  apply congrFun (Continuous.ext_on M.torus_dense
    ((transport_continuous M N).comp (M.fanShear_holomorphic g).continuous)
    ((N.fanShear_holomorphic g).continuous.comp (transport_continuous M N)) ?_) p
  rintro q ⟨x, rfl⟩
  simp only [Function.comp_apply, M.fanShear_torus, transport_torus, N.fanShear_torus]

public theorem transport_centralComponent_iff (M N : Model) (w : ToricLattice)
    (p : M.Carrier) : transport M N p ∈ N.centralComponent w ↔ p ∈ M.centralComponent w := by
  obtain ⟨upper, v, hp⟩ := M.toricChart_cover p
  have hn := transport_mem_chart M N upper v hp
  by_cases hw : w ∈ Set.range (a2Triangle upper v)
  · obtain ⟨i, rfl⟩ := hw
    rw [N.centralComponent_in_chart upper v i _ hn,
      M.centralComponent_in_chart upper v i p hp, toricChart_transport M N upper v hp]
  · constructor
    · intro h
      exact False.elim (Set.disjoint_left.mp
        (N.otherCentralComponent_disjoint_chart upper v w hw) h hn)
    · intro h
      exact False.elim (Set.disjoint_left.mp
        (M.otherCentralComponent_disjoint_chart upper v w hw) h hp)

public def centralFiberHomeomorph (M N : Model) :
    {p : M.Carrier // M.t p = 0} ≃ₜ {p : N.Carrier // N.t p = 0} where
  toFun := fun p ↦ ⟨transport M N p.1, (transport_t M N p.1).trans p.2⟩
  invFun := fun p ↦ ⟨transport N M p.1, (transport_t N M p.1).trans p.2⟩
  left_inv := fun p ↦ Subtype.ext (transport_left_inverse M N p.1)
  right_inv := fun p ↦ Subtype.ext (transport_left_inverse N M p.1)
  continuous_toFun := ((transport_continuous M N).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((transport_continuous N M).comp continuous_subtype_val).subtype_mk _

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Model
