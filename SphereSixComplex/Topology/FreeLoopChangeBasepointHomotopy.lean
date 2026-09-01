module

public import SphereSixComplex.Topology.PaperActualEllipticOrderThreeProductLoopSplittingProof
public import Mathlib.Topology.Subpath

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Topology

/-- Vertical composition preserves equality of the two loop-endpoint traces. -/
public theorem freeLoopHomotopyTrans_trace
    {X : Type*} [TopologicalSpace X]
    {f g h : C(unitInterval, X)}
    (H : ContinuousMap.Homotopy f g)
    (K : ContinuousMap.Homotopy g h)
    (hH : ∀ s : unitInterval, H (s, 0) = H (s, 1))
    (hK : ∀ s : unitInterval, K (s, 0) = K (s, 1))
    (s : unitInterval) :
    H.trans K (s, 0) = H.trans K (s, 1) := by
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hH _
  · exact hK _

/-- The initial segment of a path, with its source displayed at the declared source point. -/
public def pathInitialSegment
    {X : Type*} [TopologicalSpace X] {a b : X}
    (w : Path a b) (s : unitInterval) : Path a (w s) :=
  (w.subpath 0 s).cast w.source.symm rfl

public theorem pathInitialSegment_zero_apply
    {X : Type*} [TopologicalSpace X] {a b : X}
    (w : Path a b) (t : unitInterval) : pathInitialSegment w 0 t = a := by
  simp [pathInitialSegment, Path.subpath]

public theorem pathInitialSegment_one_apply
    {X : Type*} [TopologicalSpace X] {a b : X}
    (w : Path a b) (t : unitInterval) : pathInitialSegment w 1 t = w t := by
  simp [pathInitialSegment, Path.subpath]

public theorem pathInitialSegment_continuous_family
    {X : Type*} [TopologicalSpace X] {a b : X} (w : Path a b) :
    Continuous ↿(fun s : unitInterval ↦ pathInitialSegment w s) := by
  change Continuous
    ((fun x : unitInterval × unitInterval × unitInterval ↦
      w.subpath x.1 x.2.1 x.2.2) ∘
        (fun st : unitInterval × unitInterval ↦ (0, st.1, st.2)))
  exact w.subpath_continuous_family.comp
    (continuous_const.prodMk (continuous_fst.prodMk continuous_snd))

public theorem continuous_freeLoopWhiskerPrefix
    {X : Type*} [TopologicalSpace X] {a b : X}
    (p : Path a a) (w : Path a b) :
    Continuous (fun st : unitInterval × unitInterval ↦
      ((pathInitialSegment w st.1).symm.trans
        (p.trans (pathInitialSegment w st.1))) st.2) := by
  have hq : Continuous ↿(fun s : unitInterval ↦ pathInitialSegment w s) :=
    pathInitialSegment_continuous_family w
  have hqs : Continuous ↿(fun s : unitInterval ↦
      (pathInitialSegment w s).symm) :=
    Path.symm_continuous_family _ hq
  have hp : Continuous ↿(fun _ : unitInterval ↦ p) := by
    change Continuous (fun st : unitInterval × unitInterval ↦ p st.2)
    exact p.continuous.comp continuous_snd
  have hr : Continuous ↿(fun s : unitInterval ↦
      p.trans (pathInitialSegment w s)) :=
    Path.trans_continuous_family
      (a := fun _ : unitInterval ↦ a) (b := fun _ ↦ a) (c := fun s ↦ w s)
      (fun _ ↦ p) hp (fun s ↦ pathInitialSegment w s) hq
  exact Path.trans_continuous_family
    (a := fun s ↦ w s) (b := fun _ ↦ a) (c := fun s ↦ w s)
    (fun s ↦ (pathInitialSegment w s).symm) hqs
    (fun s ↦ p.trans (pathInitialSegment w s)) hr

/-- Slide a loop along the initial segments of a path, starting from the version with
constant paths explicitly inserted on both sides. -/
public def freeLoopWhiskerPrefixHomotopy
    {X : Type*} [TopologicalSpace X] {a b : X}
    (p : Path a a) (w : Path a b) :
    ContinuousMap.Homotopy
      ((Path.refl a).trans (p.trans (Path.refl a))).toContinuousMap
      (w.symm.trans (p.trans w)).toContinuousMap where
  toFun st :=
    ((pathInitialSegment w st.1).symm.trans
      (p.trans (pathInitialSegment w st.1))) st.2
  continuous_toFun := continuous_freeLoopWhiskerPrefix p w
  map_zero_left t := by
    change ((pathInitialSegment w 0).symm.trans
      (p.trans (pathInitialSegment w 0))) t =
      ((Path.refl a).trans (p.trans (Path.refl a))) t
    simp only [Path.trans_apply]
    split_ifs <;> simp [pathInitialSegment_zero_apply]
  map_one_left t := by
    change ((pathInitialSegment w 1).symm.trans
      (p.trans (pathInitialSegment w 1))) t =
      (w.symm.trans (p.trans w)) t
    simp only [Path.trans_apply]
    split_ifs <;> simp [pathInitialSegment_one_apply]

/-- The prefix-sliding homotopy has the same moving-basepoint trace at both loop endpoints. -/
public theorem freeLoopWhiskerPrefixHomotopy_trace
    {X : Type*} [TopologicalSpace X] {a b : X}
    (p : Path a a) (w : Path a b) (s : unitInterval) :
    freeLoopWhiskerPrefixHomotopy p w (s, 0) =
      freeLoopWhiskerPrefixHomotopy p w (s, 1) := by
  change ((pathInitialSegment w s).symm.trans
      (p.trans (pathInitialSegment w s))) 0 =
    ((pathInitialSegment w s).symm.trans
      (p.trans (pathInitialSegment w s))) 1
  exact ((pathInitialSegment w s).symm.trans
      (p.trans (pathInitialSegment w s))).source.trans
    ((pathInitialSegment w s).symm.trans
      (p.trans (pathInitialSegment w s))).target.symm

/-- Changing the basepoint of a loop by a path is realized by a genuine free homotopy, with
equal point-set traces at the two loop endpoints. -/
public theorem exists_freeLoopChangeBasepointHomotopy
    {X : Type*} [TopologicalSpace X] {a b : X}
    (p : Path a a) (w : Path a b) :
    ∃ H : ContinuousMap.Homotopy p.toContinuousMap
        (w.symm.trans (p.trans w)).toContinuousMap,
      ∀ s : unitInterval, H (s, 0) = H (s, 1) := by
  have hreparam : Nonempty (Path.Homotopy p
      ((Path.refl a).trans (p.trans (Path.refl a)))) := by
    apply Path.Homotopic.Quotient.exact
    simp
  rcases hreparam with ⟨R⟩
  let H₀ := pathHomotopyToFreeHomotopy R
  let H₁ := freeLoopWhiskerPrefixHomotopy p w
  let H := H₀.trans H₁
  refine ⟨H, ?_⟩
  intro s
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs with hs
  · exact (R.source _).trans (R.target _).symm
  · exact freeLoopWhiskerPrefixHomotopy_trace p w _

end SphereSixComplex.Topology

end

end
