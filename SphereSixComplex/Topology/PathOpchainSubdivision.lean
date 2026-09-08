module

public import SphereSixComplex.Topology.ConvexRadialPathHomotopy

@[expose] public section
noncomputable section
open Set Topology
namespace SphereSixComplex
open Topology.FirstHurewiczProof

public theorem pathOpchainClass_map_trans {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : ContinuousMap X Y) {x y z : X} (p : Path x y) (q : Path y z) :
    pathOpchainClass ((p.trans q).map f.continuous) =
      pathOpchainClass (p.map f.continuous) + pathOpchainClass (q.map f.continuous) := by
  rw [Path.map_trans, pathOpchainClass_trans]

public theorem pathOpchainClass_map_segment_subdivision
    {X : Type} [TopologicalSpace X] (f : ContinuousMap ℝ X) (a b c : ℝ) :
    pathOpchainClass ((Path.segment a c).map f.continuous) =
      pathOpchainClass ((Path.segment a b).map f.continuous) +
        pathOpchainClass ((Path.segment b c).map f.continuous) := by
  have h := (SimplyConnectedSpace.paths_homotopic (Path.segment a c)
    ((Path.segment a b).trans (Path.segment b c))).map f
  exact (pathOpchainClass_homotopic h).trans (pathOpchainClass_map_trans f _ _)

public theorem pathOpchainClass_map_segment_four
    {X : Type} [TopologicalSpace X] (f : ContinuousMap ℝ X) (a b c d e : ℝ) :
    pathOpchainClass ((Path.segment a e).map f.continuous) =
      ((pathOpchainClass ((Path.segment a b).map f.continuous) +
        pathOpchainClass ((Path.segment b c).map f.continuous)) +
        pathOpchainClass ((Path.segment c d).map f.continuous)) +
        pathOpchainClass ((Path.segment d e).map f.continuous) := by
  rw [pathOpchainClass_map_segment_subdivision f a d e,
    pathOpchainClass_map_segment_subdivision f a c d,
    pathOpchainClass_map_segment_subdivision f a b c]

public theorem pathOpchainClass_map_six
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : ContinuousMap X Y)
    {a b c d e g h : X} (p₀ : Path a b) (p₁ : Path b c) (p₂ : Path c d)
    (p₃ : Path d e) (p₄ : Path e g) (p₅ : Path g h) :
    pathOpchainClass (((((p₀.trans p₁).trans p₂).trans p₃).trans p₄).trans p₅ |>.map f.continuous) =
      ((((pathOpchainClass (p₀.map f.continuous) + pathOpchainClass (p₁.map f.continuous)) +
        pathOpchainClass (p₂.map f.continuous)) + pathOpchainClass (p₃.map f.continuous)) +
        pathOpchainClass (p₄.map f.continuous)) + pathOpchainClass (p₅.map f.continuous) := by
  simp only [pathOpchainClass_map_trans]

public theorem path_trans_pointwise {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Z) (g : Y → Z) {a b c : X} {a' b' c' : Y}
    (p : Path a b) (q : Path b c) (p' : Path a' b') (q' : Path b' c')
    (hp : ∀ t, f (p t) = g (p' t)) (hq : ∀ t, f (q t) = g (q' t)) (t : unitInterval) :
    f ((p.trans q) t) = g ((p'.trans q') t) := by
  simp only [Path.trans_apply]
  split_ifs
  · exact hp _
  · exact hq _

end SphereSixComplex
