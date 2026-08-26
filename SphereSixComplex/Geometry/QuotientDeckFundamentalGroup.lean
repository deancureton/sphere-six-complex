module

public import SphereSixComplex.Geometry.Quotient
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Fundamental-group classes from deck paths

For a path-connected space with a group action, a path from a point to one of its deck translates
projects to a based loop in the orbit quotient.  This elementary construction is shared by the
outer triangle-group quotient and the two finite affine elliptic filling quotients.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry

variable {M G : Type*} [TopologicalSpace M] [Group G] [MulAction G M]

/-- Concatenate a continuously chosen path from each point to its image under `f`.  The result
records the lifted path through `n` successive iterates of `f`. -/
public def iteratedForwardPath {X : Type*} [TopologicalSpace X]
    (f : X → X) (step : ∀ x, Path x (f x)) :
    ∀ (n : ℕ) (x : X), Path x (f^[n] x)
  | 0, x => Path.refl x
  | n + 1, x =>
      ((step x).trans (iteratedForwardPath f step n (f x))).cast rfl
        (Function.iterate_succ_apply f n x)

/-- Concatenate one path with its successive images under a continuous self-map.  Unlike
`iteratedForwardPath`, every later segment is the corresponding iterate of the first segment;
this is the lift that represents a power of the projected one-step loop. -/
public def iteratedMappedPath {X : Type*} [TopologicalSpace X]
    (f : X → X) (hf : Continuous f) {x : X}
    (P : Path x (f x)) : ∀ n : ℕ, Path x (f^[n] x)
  | 0 => Path.refl x
  | n + 1 =>
      (iteratedMappedPath f hf P n).trans
        ((P.map (hf.iterate n)).cast rfl (Function.iterate_succ_apply f n x))

/-- A map invariant under one application of `f` is invariant under every iterate of `f`. -/
public theorem map_iterate_eq_of_map_comp_eq {X Y : Type*}
    (f : X → X) (q : X → Y) (hq : ∀ z, q (f z) = q z) (n : ℕ) (z : X) :
    q (f^[n] z) = q z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact (ih (f z)).trans (hq z)

/-- Project a path from `x` to `f x` along an `f`-invariant map, obtaining a loop. -/
public def projectedForwardLoop {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → X) (q : X → Y) (hq : ∀ z, q (f z) = q z)
    {x : X} (P : Path x (f x)) (hqcont : Continuous q) : Path (q x) (q x) :=
  (P.map hqcont).cast rfl (hq x).symm

/-- Project the successive images of a path to the invariant target and cast its final endpoint
back to the initial basepoint. -/
public def projectedIteratedMappedLoop {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → X) (hf : Continuous f)
    (q : X → Y) (hq : ∀ z, q (f z) = q z) {x : X}
    (P : Path x (f x)) (hqcont : Continuous q) (n : ℕ) : Path (q x) (q x) :=
  ((iteratedMappedPath f hf P n).map hqcont).cast rfl
    (map_iterate_eq_of_map_comp_eq f q hq n x).symm

/-- A literal `n`-fold concatenation of one based loop. -/
public def repeatedLoop {Y : Type*} [TopologicalSpace Y] {y : Y}
    (L : Path y y) : ℕ → Path y y
  | 0 => Path.refl y
  | n + 1 => (repeatedLoop L n).trans L

/-- Regard a based path as its fundamental-group class. -/
public def pathLoopClass {Y : Type*} [TopologicalSpace Y] {y : Y}
    (L : Path y y) : FundamentalGroup Y y :=
  Path.Homotopic.Quotient.mk L

/-- Casting both endpoints of a loop along a point equality is the same as applying the
fundamental-group homomorphism induced by the identity map with that target basepoint. -/
public theorem pathLoopClass_cast_eq_mapOfEq_id
    {X : Type*} [TopologicalSpace X] {x y : X}
    (L : Path x x) (h : x = y) :
    pathLoopClass (L.cast h.symm h.symm) =
      FundamentalGroup.mapOfEq (ContinuousMap.id X) h (pathLoopClass L) := by
  have hm := FundamentalGroup.mapOfEq_apply (ContinuousMap.id X)
    (show (ContinuousMap.id X) x = y from h) (pathLoopClass L)
  rw [hm]
  rfl

/-- Transporting a local loop back along a path is represented by whiskering the loop with that
path and its reverse. -/
public def whiskeredLoopClass {X : Type*} [TopologicalSpace X] {x y : X}
    (W : Path x y) (L : Path y y) : FundamentalGroup X x :=
  pathLoopClass (W.trans (L.trans W.symm))

/-- If the far endpoint of a whisker is identified with its starting point, Mathlib's reversed
path-composition convention writes geometric whiskering as inverse conjugation.  This is the
conversion needed when a paper presentation uses the usual left-to-right loop convention. -/
public theorem whiskeredLoopClass_eq_conjugate_cast
    {X : Type*} [TopologicalSpace X] {x y : X}
    (W : Path x y) (L : Path y y) (h : y = x) :
    whiskeredLoopClass W L =
      (pathLoopClass (W.cast rfl h.symm))⁻¹ *
        pathLoopClass (L.cast h.symm h.symm) *
        pathLoopClass (W.cast rfl h.symm) := by
  subst h
  simp only [whiskeredLoopClass, pathLoopClass,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  rfl

public theorem fundamentalGroupMulEquivOfPath_symm_apply_eq_whiskeredLoopClass
    {X : Type*} [TopologicalSpace X] {x y : X}
    (W : Path x y) (L : Path y y) :
    (FundamentalGroup.fundamentalGroupMulEquivOfPath W).symm (pathLoopClass L) =
      whiskeredLoopClass W L := by
  rfl

/-- Basepoint transport preserves a conjugation identity. -/
public theorem whiskeredLoopClass_conjugation
    {X : Type*} [TopologicalSpace X] {x y : X}
    (W : Path x y) (D T T' : Path y y)
    (h : (pathLoopClass D)⁻¹ * pathLoopClass T * pathLoopClass D =
      pathLoopClass T') :
    (whiskeredLoopClass W D)⁻¹ * whiskeredLoopClass W T *
        whiskeredLoopClass W D = whiskeredLoopClass W T' := by
  let e := FundamentalGroup.fundamentalGroupMulEquivOfPath W
  have hm := congrArg e.symm h
  rw [← fundamentalGroupMulEquivOfPath_symm_apply_eq_whiskeredLoopClass W D,
    ← fundamentalGroupMulEquivOfPath_symm_apply_eq_whiskeredLoopClass W T,
    ← fundamentalGroupMulEquivOfPath_symm_apply_eq_whiskeredLoopClass W T']
  simpa only [map_mul, map_inv] using hm

/-- Literal repeated concatenation represents the corresponding group power.  The proof records
the reversal built into Mathlib's categorical convention for fundamental-group multiplication. -/
public theorem pathLoopClass_repeatedLoop {Y : Type*} [TopologicalSpace Y]
    {y : Y} (L : Path y y) (n : ℕ) :
    pathLoopClass (repeatedLoop L n) = pathLoopClass L ^ n := by
  induction n with
  | zero =>
      rw [repeatedLoop.eq_def, pow_zero]
      exact Path.Homotopic.Quotient.mk_refl y
  | succ n ih =>
      rw [repeatedLoop.eq_def, pathLoopClass, Path.Homotopic.Quotient.mk_trans,
        ← pathLoopClass, ih, pow_succ']
      rfl

/-- After projection along an invariant map, the concatenation of the successive images of a
path is literally the repeated projected loop. -/
public theorem projectedIteratedMappedLoop_eq_repeatedLoop
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → X) (hf : Continuous f)
    (q : X → Y) (hq : ∀ z, q (f z) = q z) {x : X}
    (P : Path x (f x)) (hqcont : Continuous q) (n : ℕ) :
    projectedIteratedMappedLoop f hf q hq P hqcont n =
      repeatedLoop (projectedForwardLoop f q hq P hqcont) n := by
  induction n with
  | zero =>
      apply Path.ext
      funext t
      rfl
  | succ n ih =>
      apply Path.ext
      funext t
      change q (((iteratedMappedPath f hf P n).trans
          ((P.map (hf.iterate n)).cast rfl
            (Function.iterate_succ_apply f n x))) t) =
        ((repeatedLoop (projectedForwardLoop f q hq P hqcont) n).trans
          (projectedForwardLoop f q hq P hqcont)) t
      rw [Path.trans_apply]
      rw [Path.trans_apply]
      split_ifs with ht
      · exact congrArg
          (fun Q : Path (q x) (q x) =>
            Q ⟨2 * (t : ℝ), by constructor <;> linarith [t.2.1, t.2.2]⟩) ih
      · change q ((f^[n])
            (P ⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.2.1, t.2.2]⟩)) =
          q (P ⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.2.1, t.2.2]⟩)
        rw [map_iterate_eq_of_map_comp_eq f q hq]

/-- The projected successive-image path represents the `n`th power of its projected one-step
loop in the fundamental group. -/
public theorem pathLoopClass_projectedIteratedMappedLoop_eq_pow
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → X) (hf : Continuous f)
    (q : X → Y) (hq : ∀ z, q (f z) = q z) {x : X}
    (P : Path x (f x)) (hqcont : Continuous q) (n : ℕ) :
    pathLoopClass (projectedIteratedMappedLoop f hf q hq P hqcont n) =
      pathLoopClass (projectedForwardLoop f q hq P hqcont) ^ n := by
  rw [projectedIteratedMappedLoop_eq_repeatedLoop]
  exact pathLoopClass_repeatedLoop _ _

/-- A chosen path from a point to one of its translates in a path-connected action space. -/
public def orbitDeckPath [PathConnectedSpace M] (x : M) (g : G) : Path x (g • x) :=
  PathConnectedSpace.somePath _ _

/-- The canonical continuous projection to an orbit quotient. -/
public def orbitQuotientMap : C(M, OrbitQuotient (M := M) (G := G)) :=
  ⟨quotientProjection, continuous_quot_mk⟩

/-- A point and any of its translates have the same orbit-quotient image. -/
public theorem orbitQuotientMap_smul (x : M) (g : G) :
    orbitQuotientMap (G := G) (g • x) = orbitQuotientMap (G := G) x := by
  apply Quotient.sound
  change MulAction.orbitRel G M (g • x) x
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨g, rfl⟩

/-- Compose paths carrying `x` to its `g`- and `h`-translates.  The second path is first
translated by `g`, so the endpoint records the product `g * h` rather than merely forgetting the
deck labels after quotienting. -/
public def composedOrbitDeckPath (x : M) (g h : G)
    (Pg : Path x (g • x)) (Ph : Path x (h • x))
    (hg : Continuous (fun y : M ↦ g • y)) :
    Path x ((g * h) • x) :=
  (Pg.trans (Ph.map hg)).cast rfl (mul_smul g h x)

/-- Project a specified path to a deck translate, rather than using the arbitrary path selected
by `orbitDeckPath`. -/
public def projectedOrbitDeckPath (x : M) (g : G) (Pg : Path x (g • x)) :
    Path (orbitQuotientMap (G := G) x) (orbitQuotientMap (G := G) x) :=
  (Pg.map (orbitQuotientMap (G := G)).continuous).cast rfl
    (orbitQuotientMap_smul x g).symm

/-- Projecting a composed deck path gives the literal concatenation of the two projected loops.
The second upstairs segment was translated by `g`, but orbit projection removes that translate. -/
public theorem projectedOrbitDeckPath_mul_eq
    (x : M) (g h : G)
    (Pg : Path x (g • x)) (Ph : Path x (h • x))
    (hg : Continuous (fun y : M ↦ g • y)) :
    projectedOrbitDeckPath x (g * h)
        (composedOrbitDeckPath x g h Pg Ph hg) =
      (projectedOrbitDeckPath x g Pg).trans
        (projectedOrbitDeckPath x h Ph) := by
  apply Path.ext
  funext t
  unfold composedOrbitDeckPath projectedOrbitDeckPath
  change orbitQuotientMap (G := G) ((Pg.trans (Ph.map hg)) t) =
    ((projectedOrbitDeckPath x g Pg).trans
      (projectedOrbitDeckPath x h Ph)) t
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs with ht
  · rfl
  · exact orbitQuotientMap_smul _ _

/-- Deck-path composition is contravariant in the fundamental group.  This theorem records the
precise order reversal: a path labelled `g * h` projects to the class labelled `h` times the class
labelled `g` in Mathlib's fundamental-group multiplication. -/
public theorem projectedOrbitDeckPath_mul
    (x : M) (g h : G)
    (Pg : Path x (g • x)) (Ph : Path x (h • x))
    (hg : Continuous (fun y : M ↦ g • y)) :
    pathLoopClass (projectedOrbitDeckPath x (g * h)
      (composedOrbitDeckPath x g h Pg Ph hg)) =
      pathLoopClass (projectedOrbitDeckPath x h Ph) *
        pathLoopClass (projectedOrbitDeckPath x g Pg) := by
  rw [projectedOrbitDeckPath_mul_eq]
  rfl

/-- Rebase a deck path at `y` along `Q : x → y`.  The return path must be translated by `g`
upstairs; after orbit projection it becomes the ordinary reverse whisker. -/
public def rebasedOrbitDeckPath {x y : M} (g : G)
    (Q : Path x y) (D : Path y (g • y))
    (hg : Continuous (fun z : M ↦ g • z)) : Path x (g • x) :=
  Q.trans (D.trans (Q.symm.map hg))

/-- Projecting the genuinely rebased deck path is literally the usual whiskered loop: the
translated return path has the same orbit projection as the original reverse whisker. -/
public theorem projectedRebasedOrbitDeckPath_eq
    {x y : M} (g : G) (Q : Path x y) (D : Path y (g • y))
    (hg : Continuous (fun z : M ↦ g • z)) :
    projectedOrbitDeckPath x g (rebasedOrbitDeckPath g Q D hg) =
      (Q.map (orbitQuotientMap (G := G)).continuous).trans
        ((projectedOrbitDeckPath y g D).trans
          (Q.map (orbitQuotientMap (G := G)).continuous).symm) := by
  apply Path.ext
  funext t
  unfold projectedOrbitDeckPath rebasedOrbitDeckPath
  change orbitQuotientMap (G := G)
      ((Q.trans (D.trans (Q.symm.map hg))) t) =
    ((Q.map (orbitQuotientMap (G := G)).continuous).trans
      ((projectedOrbitDeckPath y g D).trans
        (Q.map (orbitQuotientMap (G := G)).continuous).symm)) t
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs with ht
  · rfl
  · rw [Path.trans_apply, Path.trans_apply]
    split_ifs with hu
    · rfl
    · change orbitQuotientMap (G := G)
          (g • Q.symm ⟨2 * (2 * (t : ℝ) - 1) - 1,
            by constructor <;> linarith [t.2.1, t.2.2]⟩) =
        orbitQuotientMap (G := G)
          (Q.symm ⟨2 * (2 * (t : ℝ) - 1) - 1,
            by constructor <;> linarith [t.2.1, t.2.2]⟩)
      exact orbitQuotientMap_smul _ _

/-- The path equality above, expressed as the corresponding fundamental-group class. -/
public theorem projectedRebasedOrbitDeckPath_class
    {x y : M} (g : G) (Q : Path x y) (D : Path y (g • y))
    (hg : Continuous (fun z : M ↦ g • z)) :
    pathLoopClass (projectedOrbitDeckPath x g
      (rebasedOrbitDeckPath g Q D hg)) =
      whiskeredLoopClass
        (Q.map (orbitQuotientMap (G := G)).continuous)
        (projectedOrbitDeckPath y g D) :=
  congrArg pathLoopClass (projectedRebasedOrbitDeckPath_eq g Q D hg)

/-- Projecting a path to a deck translate gives a based loop in the orbit quotient. -/
public def orbitDeckLoop [PathConnectedSpace M] (x : M) (g : G) :
    Path (orbitQuotientMap (G := G) x) (orbitQuotientMap (G := G) x) :=
  ((orbitDeckPath x g).map (orbitQuotientMap (G := G)).continuous).cast rfl
    (orbitQuotientMap_smul x g).symm

/-- The fundamental-group class represented by a projected deck path. -/
public def orbitDeckClass [PathConnectedSpace M] (x : M) (g : G) :
    FundamentalGroup (OrbitQuotient (M := M) (G := G))
      (orbitQuotientMap (G := G) x) :=
  Path.Homotopic.Quotient.mk (orbitDeckLoop x g)

end SphereSixComplex.Geometry
