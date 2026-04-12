/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.Topology.VectorBundle.Equiv
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# Smooth Vector Bundle Homomorphisms and Equivalences

This file defines bundled `C^n` fiberwise-linear maps between smooth vector bundles
over possibly different base manifolds. These are the smooth analogs of
`VectorBundleHom` and `VectorBundleEquiv` from `Mathlib.Topology.VectorBundle.Equiv`.

A `ContMDiffVectorBundleHom` bundles a `C^n` map of total spaces with a family of
linear maps between fibers. A `ContMDiffVectorBundleEquiv` strengthens this to a
`Diffeomorph` of total spaces with fiberwise linear equivalences.

## Main Definitions

* `ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂` : a `C^n` fiberwise-linear map
  between vector bundles, covering a base map `baseMap : B₁ → B₂`.
* `ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂` : a `Diffeomorph` of total spaces
  with fiberwise linear equivalences, covering a bijection of base manifolds.
* `ContMDiffVectorBundleEquiv.ofFiberwiseLinearEquiv` : construct an equivalence from
  a family of fiberwise linear equivalences, given smoothness of the induced
  total-space maps.
* `ContMDiffVectorBundleHom.toContMDiffVectorBundleEquiv` : promote a bijective `C^n`
  homomorphism to an equivalence, given that the base map is a diffeomorphism.

## References

* [J. M. Lee, *Introduction to Smooth Manifolds*][lee2012] p. 261

## Tags

vector bundle, homomorphism, equivalence, isomorphism, diffeomorphism
-/

@[expose] public section

open Bundle

/-! ## `C^n` vector bundle equivalences -/

open scoped Manifold

/-- A `C^n` vector bundle equivalence between bundles `E₁` over `B₁` and `E₂` over `B₂`. -/
structure ContMDiffVectorBundleEquiv
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
    {HB : Type*} [TopologicalSpace HB]
    (IB : ModelWithCorners 𝕜 EB HB)
    (n : WithTop ℕ∞)
    {B₁ : Type*} [TopologicalSpace B₁] [ChartedSpace HB B₁]
    (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    (E₁ : B₁ → Type*) [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
    [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    {B₂ : Type*} [TopologicalSpace B₂] [ChartedSpace HB B₂]
    (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (E₂ : B₂ → Type*) [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
    [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂] where
  baseMap : B₁ → B₂
  toDiffeomorph : Diffeomorph (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂))
    (TotalSpace F₁ E₁) (TotalSpace F₂ E₂) n
  fiberLinearEquiv : ∀ x : B₁, E₁ x ≃ₗ[𝕜] E₂ (baseMap x)
  fiber_compat : ∀ (x : B₁) (v : E₁ x),
    toDiffeomorph ⟨x, v⟩ = ⟨baseMap x, fiberLinearEquiv x v⟩

namespace ContMDiffVectorBundleEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {n : WithTop ℕ∞}
  {B₁ : Type*} [TopologicalSpace B₁] [ChartedSpace HB B₁]
  {B₂ : Type*} [TopologicalSpace B₂] [ChartedSpace HB B₂]
  {B₃ : Type*} [TopologicalSpace B₃] [ChartedSpace HB B₃]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {E₃ : B₃ → Type*} [∀ x, AddCommMonoid (E₃ x)] [∀ x, Module 𝕜 (E₃ x)]
  [TopologicalSpace (TotalSpace F₃ E₃)] [∀ x, TopologicalSpace (E₃ x)]
  [FiberBundle F₃ E₃] [VectorBundle 𝕜 F₃ E₃]

/-- Construct a `ContMDiffVectorBundleEquiv` without specifying the base map, deriving it as
`fun x => (Φ ⟨x, 0⟩).proj`. -/
def mk'
    (Φ : Diffeomorph (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂))
      (TotalSpace F₁ E₁) (TotalSpace F₂ E₂) n)
    (φ : ∀ x : B₁, E₁ x ≃ₗ[𝕜] E₂ ((Φ ⟨x, 0⟩).proj))
    (hcompat : ∀ (x : B₁) (v : E₁ x),
      Φ ⟨x, v⟩ = ⟨(Φ ⟨x, 0⟩).proj, φ x v⟩) :
    ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂ where
  baseMap x := (Φ ⟨x, 0⟩).proj
  toDiffeomorph := Φ
  fiberLinearEquiv := φ
  fiber_compat := hcompat

@[ext]
theorem ext (A B : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂)
    (h : A.toDiffeomorph = B.toDiffeomorph) : A = B := by
  obtain ⟨f_A, Φ_A, φ_A, hA⟩ := A
  obtain ⟨f_B, Φ_B, φ_B, hB⟩ := B
  simp only at h; subst h
  have hf : f_A = f_B := by
    ext x
    have h₁ := hA x 0; have h₂ := hB x 0
    simp only [map_zero] at h₁ h₂
    rw [h₁] at h₂; exact congrArg TotalSpace.proj h₂
  subst hf; congr 1
  ext x v
  have h₁ := hA x v; rw [hB] at h₁
  exact TotalSpace.mk_inj.mp h₁.symm

instance : FunLike
    (ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂)
    (TotalSpace F₁ E₁) (TotalSpace F₂ E₂) where
  coe e := e.toDiffeomorph
  coe_injective' f g h :=
    ext f g (Diffeomorph.ext (congrFun h))

instance : ContinuousMapClass
    (ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂)
    (TotalSpace F₁ E₁) (TotalSpace F₂ E₂) where
  map_continuous e := e.toDiffeomorph.continuous

/-- The underlying `ContinuousMap`. -/
@[simps]
def toContinuousMap
    (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂) :
    C(TotalSpace F₁ E₁, TotalSpace F₂ E₂) :=
  ⟨e, e.toDiffeomorph.continuous⟩

/-- The base map equals the projection of the diffeomorphism on the zero section. -/
theorem baseMap_eq
    (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂)
    (x : B₁) :
    e.baseMap x = (e.toDiffeomorph ⟨x, 0⟩).proj := by
  simp [e.fiber_compat, map_zero]

/-- The base map of a `C^n` vector bundle equivalence is bijective. -/
theorem baseMap_bijective (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂) :
    Function.Bijective e.baseMap := by
  constructor
  · intro x₁ x₂ h
    have h₁ := e.fiber_compat x₁ 0
    have h₂ := e.fiber_compat x₂ 0
    simp only [map_zero] at h₁ h₂
    have hinj := e.toDiffeomorph.injective (h₁.trans (by rw [h]) |>.trans h₂.symm)
    exact congrArg TotalSpace.proj hinj
  · intro y
    obtain ⟨⟨x, v⟩, hxv⟩ := e.toDiffeomorph.surjective ⟨y, 0⟩
    have h := e.fiber_compat x v
    have : (e.toDiffeomorph.toEquiv ⟨x, v⟩) = e.toDiffeomorph ⟨x, v⟩ := rfl
    rw [this, h] at hxv
    exact ⟨x, congrArg TotalSpace.proj hxv⟩

/-- The underlying `VectorBundleEquiv` of a `ContMDiffVectorBundleEquiv`. -/
@[simps baseMap fiberLinearEquiv]
def toVectorBundleEquiv (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂) :
    VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂ where
  baseMap := e.baseMap
  toHomeomorph := e.toDiffeomorph.toHomeomorph
  fiberLinearEquiv := e.fiberLinearEquiv
  fiber_compat x v := e.fiber_compat x v

@[simp]
theorem proj_eq (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂)
    (p : TotalSpace F₁ E₁) : (e.toDiffeomorph p).proj = e.baseMap p.proj := by
  obtain ⟨x, v⟩ := p; simp [e.fiber_compat]

@[simp]
theorem toDiffeomorph_apply (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂)
    (x : B₁) (v : E₁ x) :
    e.toDiffeomorph ⟨x, v⟩ = ⟨e.baseMap x, e.fiberLinearEquiv x v⟩ :=
  e.fiber_compat x v

/-- The identity `C^n` vector bundle equivalence. -/
@[simps baseMap toDiffeomorph fiberLinearEquiv]
def refl : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₁ E₁ where
  baseMap := _root_.id
  toDiffeomorph := Diffeomorph.refl (IB.prod 𝓘(𝕜, F₁)) (TotalSpace F₁ E₁) n
  fiberLinearEquiv x := LinearEquiv.refl 𝕜 (E₁ x)
  fiber_compat _ _ := rfl

/-- The inverse of a `C^n` vector bundle equivalence. -/
def symm (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂) :
    ContMDiffVectorBundleEquiv 𝕜 IB n F₂ E₂ F₁ E₁ where
  baseMap y := (e.toDiffeomorph.symm ⟨y, 0⟩).proj
  toDiffeomorph := e.toDiffeomorph.symm
  fiberLinearEquiv y :=
    let x := (e.toDiffeomorph.symm ⟨y, 0⟩).proj
    have hx : e.baseMap x = y := by
      have := e.proj_eq (e.toDiffeomorph.symm ⟨y, 0⟩)
      simp [e.toDiffeomorph.apply_symm_apply] at this; exact this.symm
    (hx ▸ e.fiberLinearEquiv x).symm
  fiber_compat y v := by exact e.toVectorBundleEquiv.symm.fiber_compat y v

/-- Composition of `C^n` vector bundle equivalences. -/
def trans (e₁₂ : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂)
    (e₂₃ : ContMDiffVectorBundleEquiv 𝕜 IB n F₂ E₂ F₃ E₃) :
    ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₃ E₃ where
  baseMap := e₂₃.baseMap ∘ e₁₂.baseMap
  toDiffeomorph := e₁₂.toDiffeomorph.trans e₂₃.toDiffeomorph
  fiberLinearEquiv x :=
    (e₁₂.fiberLinearEquiv x).trans (e₂₃.fiberLinearEquiv (e₁₂.baseMap x))
  fiber_compat x v := by
    simp only [Diffeomorph.coe_trans, Function.comp_apply,
      e₁₂.fiber_compat, e₂₃.fiber_compat]
    congr 1

@[simp]
theorem refl_apply (p : TotalSpace F₁ E₁) :
    (refl : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₁ E₁)
      p = p := rfl

@[simp]
theorem symm_apply_apply
    (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂)
    (p : TotalSpace F₁ E₁) :
    e.symm (e p) = p :=
  e.toDiffeomorph.symm_apply_apply p

@[simp]
theorem apply_symm_apply
    (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂)
    (p : TotalSpace F₂ E₂) :
    e (e.symm p) = p :=
  e.toDiffeomorph.apply_symm_apply p

@[simp]
theorem symm_symm
    (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂) :
    e.symm.symm = e :=
  ext _ _ (Diffeomorph.ext fun p =>
    congrFun (congrArg DFunLike.coe
      (Equiv.symm_symm e.toDiffeomorph.toEquiv)) p)

@[simp]
theorem symm_trans_self
    (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂) :
    e.symm.trans e = refl :=
  ext _ _ (Diffeomorph.ext fun p =>
    e.toDiffeomorph.apply_symm_apply p)

@[simp]
theorem self_trans_symm
    (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂) :
    e.trans e.symm = refl :=
  ext _ _ (Diffeomorph.ext fun p =>
    e.toDiffeomorph.symm_apply_apply p)

@[simp]
theorem trans_apply
    (e₁₂ : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂)
    (e₂₃ : ContMDiffVectorBundleEquiv 𝕜 IB n F₂ E₂ F₃ E₃)
    (p : TotalSpace F₁ E₁) :
    (e₁₂.trans e₂₃) p = e₂₃ (e₁₂ p) := rfl

@[simp]
theorem symm_apply
    (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂)
    (p : TotalSpace F₂ E₂) :
    e.symm p = e.toDiffeomorph.symm p := rfl

@[simp]
theorem trans_refl
    (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂) :
    e.trans refl = e :=
  ext _ _ (Diffeomorph.ext fun _ => rfl)

@[simp]
theorem refl_trans
    (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂) :
    refl.trans e = e :=
  ext _ _ (Diffeomorph.ext fun _ => rfl)

theorem injective
    (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂) :
    Function.Injective e :=
  e.toDiffeomorph.injective

theorem surjective
    (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂) :
    Function.Surjective e :=
  e.toDiffeomorph.surjective

theorem bijective
    (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂) :
    Function.Bijective e :=
  e.toDiffeomorph.bijective

end ContMDiffVectorBundleEquiv

/-! ## `C^n` vector bundle homomorphisms -/

/-- A `C^n` vector bundle homomorphism from `E₁` over `B₁` to `E₂` over `B₂`. -/
structure ContMDiffVectorBundleHom
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
    {HB : Type*} [TopologicalSpace HB]
    (IB : ModelWithCorners 𝕜 EB HB)
    (n : WithTop ℕ∞)
    {B₁ : Type*} [TopologicalSpace B₁] [ChartedSpace HB B₁]
    (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    (E₁ : B₁ → Type*) [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
    [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    {B₂ : Type*} [TopologicalSpace B₂] [ChartedSpace HB B₂]
    (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (E₂ : B₂ → Type*) [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
    [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂] where
  baseMap : B₁ → B₂
  toFun : TotalSpace F₁ E₁ → TotalSpace F₂ E₂
  contMDiff_toFun : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n toFun
  fiberLinearMap : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)
  fiber_compat : ∀ (x : B₁) (v : E₁ x),
    toFun ⟨x, v⟩ = ⟨baseMap x, fiberLinearMap x v⟩

namespace ContMDiffVectorBundleHom

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {n : WithTop ℕ∞}
  {B₁ : Type*} [TopologicalSpace B₁] [ChartedSpace HB B₁]
  {B₂ : Type*} [TopologicalSpace B₂] [ChartedSpace HB B₂]
  {B₃ : Type*} [TopologicalSpace B₃] [ChartedSpace HB B₃]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {E₃ : B₃ → Type*} [∀ x, AddCommMonoid (E₃ x)] [∀ x, Module 𝕜 (E₃ x)]
  [TopologicalSpace (TotalSpace F₃ E₃)] [∀ x, TopologicalSpace (E₃ x)]
  [FiberBundle F₃ E₃] [VectorBundle 𝕜 F₃ E₃]

/-- Construct a `ContMDiffVectorBundleHom` without specifying the base map, deriving it as
`fun x => (Φ ⟨x, 0⟩).proj`. -/
def mk'
    (Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂)
    (hΦ : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n Φ)
    (φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ ((Φ ⟨x, 0⟩).proj))
    (hcompat : ∀ (x : B₁) (v : E₁ x),
      Φ ⟨x, v⟩ = ⟨(Φ ⟨x, 0⟩).proj, φ x v⟩) :
    ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂ where
  baseMap x := (Φ ⟨x, 0⟩).proj
  toFun := Φ
  contMDiff_toFun := hΦ
  fiberLinearMap := φ
  fiber_compat := hcompat

@[ext]
theorem ext (A B : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂)
    (h : A.toFun = B.toFun) : A = B := by
  obtain ⟨f_A, Φ_A, _, φ_A, hA⟩ := A
  obtain ⟨f_B, Φ_B, _, φ_B, hB⟩ := B
  simp only at h; subst h
  have hf : f_A = f_B := by
    ext x
    have h₁ := hA x 0; have h₂ := hB x 0
    simp only [map_zero] at h₁ h₂
    rw [h₁] at h₂; exact congrArg TotalSpace.proj h₂
  subst hf; congr 1
  ext x v
  have h₁ := hA x v; rw [hB] at h₁
  exact TotalSpace.mk_inj.mp h₁.symm

instance : FunLike
    (ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂)
    (TotalSpace F₁ E₁) (TotalSpace F₂ E₂) where
  coe := toFun
  coe_injective' f g h := ext f g h

instance : ContinuousMapClass
    (ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂)
    (TotalSpace F₁ E₁) (TotalSpace F₂ E₂) where
  map_continuous f := f.contMDiff_toFun.continuous

/-- The underlying `ContinuousMap`. -/
@[simps]
def toContinuousMap
    (f : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂) :
    C(TotalSpace F₁ E₁, TotalSpace F₂ E₂) :=
  ⟨f, f.contMDiff_toFun.continuous⟩

/-- The base map equals the projection of the total space map on the zero section. -/
theorem baseMap_eq
    (f : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂)
    (x : B₁) :
    f.baseMap x = (f.toFun ⟨x, 0⟩).proj := by
  simp [f.fiber_compat, map_zero]

/-- The base map of a `C^n` vector bundle homomorphism is `C^n`, since it factors as
`π₂ ∘ Φ ∘ zeroSection`. -/
theorem contMDiff_baseMap [ContMDiffVectorBundle n F₁ E₁ IB]
    (f : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂) :
    ContMDiff IB IB n f.baseMap := by
  have h : f.baseMap = TotalSpace.proj ∘ f.toFun ∘ zeroSection F₁ E₁ := by
    ext x; simp [baseMap_eq, zeroSection]
  rw [h]
  have h₁ : ContMDiff IB (IB.prod 𝓘(𝕜, F₁)) n (zeroSection F₁ E₁) :=
    contMDiff_zeroSection 𝕜 E₁
  have h₂ : ContMDiff (IB.prod 𝓘(𝕜, F₂)) IB n (TotalSpace.proj (F := F₂) (E := E₂)) :=
    (contMDiff_proj E₂).of_le le_top
  exact h₂.comp (f.contMDiff_toFun.comp h₁)

/-- The underlying `VectorBundleHom` of a `ContMDiffVectorBundleHom`. -/
@[simps baseMap fiberLinearMap]
def toVectorBundleHom (f : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂) :
    VectorBundleHom 𝕜 F₁ E₁ F₂ E₂ where
  baseMap := f.baseMap
  toFun := f.toFun
  continuous_toFun := f.contMDiff_toFun.continuous
  fiberLinearMap := f.fiberLinearMap
  fiber_compat x v := f.fiber_compat x v

@[simp]
theorem proj_eq (f : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂)
    (p : TotalSpace F₁ E₁) :
    (f.toFun p).proj = f.baseMap p.proj := by
  obtain ⟨x, v⟩ := p; simp [f.fiber_compat]

@[simp]
theorem toFun_apply (f : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂)
    (x : B₁) (v : E₁ x) :
    f.toFun ⟨x, v⟩ = ⟨f.baseMap x, f.fiberLinearMap x v⟩ :=
  f.fiber_compat x v

/-- The identity `C^n` vector bundle homomorphism. -/
@[simps baseMap fiberLinearMap]
def id : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₁ E₁ where
  baseMap := _root_.id
  toFun := _root_.id
  contMDiff_toFun := contMDiff_id
  fiberLinearMap _ := LinearMap.id
  fiber_compat _ _ := rfl

/-- Composition of `C^n` vector bundle homomorphisms. -/
@[simps baseMap fiberLinearMap]
def comp (g : ContMDiffVectorBundleHom 𝕜 IB n F₂ E₂ F₃ E₃)
    (f : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂) :
    ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₃ E₃ where
  baseMap := g.baseMap ∘ f.baseMap
  toFun := g.toFun ∘ f.toFun
  contMDiff_toFun := g.contMDiff_toFun.comp f.contMDiff_toFun
  fiberLinearMap x := (g.fiberLinearMap (f.baseMap x)).comp (f.fiberLinearMap x)
  fiber_compat x v := by
    simp only [Function.comp_apply, f.fiber_compat, g.fiber_compat]
    congr 1

@[simp]
theorem comp_id (f : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂) :
    f.comp id = f := ext _ _ rfl

@[simp]
theorem id_comp (f : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂) :
    id.comp f = f := ext _ _ rfl

theorem comp_assoc
    (h : ContMDiffVectorBundleHom 𝕜 IB n F₃ E₃ F₁ E₁)
    (g : ContMDiffVectorBundleHom 𝕜 IB n F₂ E₂ F₃ E₃)
    (f : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂) :
    (h.comp g).comp f = h.comp (g.comp f) := ext _ _ rfl

@[simp]
theorem coe_id :
    ⇑(id : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₁ E₁) =
      _root_.id := rfl

@[simp]
theorem coe_comp
    (g : ContMDiffVectorBundleHom 𝕜 IB n F₂ E₂ F₃ E₃)
    (f : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂) :
    ⇑(g.comp f) = ⇑g ∘ ⇑f := rfl

end ContMDiffVectorBundleHom

namespace ContMDiffVectorBundleEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {n : WithTop ℕ∞}
  {B₁ : Type*} [TopologicalSpace B₁] [ChartedSpace HB B₁]
  {B₂ : Type*} [TopologicalSpace B₂] [ChartedSpace HB B₂]
  {B₃ : Type*} [TopologicalSpace B₃] [ChartedSpace HB B₃]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommMonoid (E₁ x)]
    [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)]
    [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommMonoid (E₂ x)]
    [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)]
    [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {E₃ : B₃ → Type*} [∀ x, AddCommMonoid (E₃ x)]
    [∀ x, Module 𝕜 (E₃ x)]
  [TopologicalSpace (TotalSpace F₃ E₃)]
    [∀ x, TopologicalSpace (E₃ x)]
  [FiberBundle F₃ E₃] [VectorBundle 𝕜 F₃ E₃]

/-- A `ContMDiffVectorBundleEquiv` as a `ContMDiffVectorBundleHom`. -/
@[simps baseMap fiberLinearMap]
def toContMDiffVectorBundleHom
    (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂) :
    ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂ where
  baseMap := e.baseMap
  toFun := e.toDiffeomorph
  contMDiff_toFun := e.toDiffeomorph.contMDiff
  fiberLinearMap x := (e.fiberLinearEquiv x).toLinearMap
  fiber_compat x v := e.fiber_compat x v

@[simp]
theorem toContMDiffVectorBundleHom_refl :
    toContMDiffVectorBundleHom
      (refl : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₁ E₁)
      = ContMDiffVectorBundleHom.id :=
  ContMDiffVectorBundleHom.ext _ _ rfl

theorem toContMDiffVectorBundleHom_comp
    (e₁₂ : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂)
    (e₂₃ : ContMDiffVectorBundleEquiv 𝕜 IB n F₂ E₂ F₃ E₃) :
    (e₁₂.trans e₂₃).toContMDiffVectorBundleHom =
      e₂₃.toContMDiffVectorBundleHom.comp
        e₁₂.toContMDiffVectorBundleHom :=
  ContMDiffVectorBundleHom.ext _ _ rfl

end ContMDiffVectorBundleEquiv

/-! ## Building `ContMDiffVectorBundleEquiv` from fiberwise data -/

section FiberwiseEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {n : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B → Type*} [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B → Type*} [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

/-- Package a fiberwise linear map family into a `ContMDiffVectorBundleHom` covering an
arbitrary base map `f : B → B₂`, given a smoothness proof for the induced total-space map.
Intended entry point for callers who can discharge smoothness directly via operations on
structured bundles (e.g. `Bundle.continuousMultilinearMap`), bypassing the
section-characterization lemma. -/
def ContMDiffVectorBundleHom.ofFiberwiseLinearMap
    {B₂ : Type*} [TopologicalSpace B₂] [ChartedSpace HB B₂]
    {E₂ : B₂ → Type*} [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
    [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
    (f : B → B₂)
    (φ : ∀ x : B, E₁ x →ₗ[𝕜] E₂ (f x))
    (h_smooth : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n
      (fun p : TotalSpace F₁ E₁ => (⟨f p.1, φ p.1 p.2⟩ : TotalSpace F₂ E₂))) :
    ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂ where
  baseMap := f
  toFun p := ⟨f p.1, φ p.1 p.2⟩
  contMDiff_toFun := h_smooth
  fiberLinearMap := φ
  fiber_compat _ _ := rfl

/-- Assemble a `ContMDiffVectorBundleEquiv` covering the identity from two mutually-inverse
`ContMDiffVectorBundleHom`s. Unlike `ContMDiffVectorBundleHom.toContMDiffVectorBundleEquivId`,
both directions of smoothness are supplied as input, so no finite-dimensional or
complete-space assumptions are needed on the fibers or base field. The base map of `Ψ` is
forced to be the identity by the mutual-inverse hypotheses, so it need not be supplied. -/
noncomputable def ContMDiffVectorBundleEquiv.ofMutualInverseHoms
    (Φ : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂)
    (Ψ : ContMDiffVectorBundleHom 𝕜 IB n F₂ E₂ F₁ E₁)
    (hΦ : Φ.baseMap = _root_.id)
    (hΨΦ : ∀ p, Ψ.toFun (Φ.toFun p) = p)
    (hΦΨ : ∀ p, Φ.toFun (Ψ.toFun p) = p) :
    ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂ :=
  have hΨ : Ψ.baseMap = _root_.id := by
    funext y
    have h := congrArg TotalSpace.proj (hΦΨ ⟨y, 0⟩)
    rwa [Φ.proj_eq, Ψ.proj_eq, hΦ] at h
  match Φ, Ψ, hΦ, hΨ, hΨΦ, hΦΨ with
  | ⟨_, toFunΦ, hcΦ, φ, compatΦ⟩, ⟨_, toFunΨ, hcΨ, ψ, compatΨ⟩,
    rfl, rfl, hΨΦ, hΦΨ =>
    { baseMap := _root_.id
      toDiffeomorph :=
        { toEquiv := ⟨toFunΦ, toFunΨ, hΨΦ, hΦΨ⟩
          contMDiff_toFun := hcΦ
          contMDiff_invFun := hcΨ }
      fiberLinearEquiv := fun x =>
        LinearEquiv.ofLinear (φ x) (ψ x)
          (LinearMap.ext fun v => by
            have h := hΦΨ ⟨x, v⟩
            simp only [compatΦ, compatΨ] at h
            exact eq_of_heq (TotalSpace.mk.inj h).2)
          (LinearMap.ext fun v => by
            have h := hΨΦ ⟨x, v⟩
            simp only [compatΦ, compatΨ] at h
            exact eq_of_heq (TotalSpace.mk.inj h).2)
      fiber_compat := compatΦ }

/-- Construct a `ContMDiffVectorBundleEquiv` covering the identity from a fiberwise linear
equivalence `φ : ∀ x, E₁ x ≃ₗ[𝕜] E₂ x`, together with smoothness proofs for the
total-space maps induced by `φ` and `φ.symm`. This is the main user-facing constructor for
equivalences built from pointwise linear-algebraic data. -/
noncomputable def ContMDiffVectorBundleEquiv.ofFiberwiseLinearEquiv
    (φ : ∀ x : B, E₁ x ≃ₗ[𝕜] E₂ x)
    (h_smooth : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n
      (fun p : TotalSpace F₁ E₁ => (⟨p.1, φ p.1 p.2⟩ : TotalSpace F₂ E₂)))
    (h_smooth_inv : ContMDiff (IB.prod 𝓘(𝕜, F₂)) (IB.prod 𝓘(𝕜, F₁)) n
      (fun p : TotalSpace F₂ E₂ => (⟨p.1, (φ p.1).symm p.2⟩ : TotalSpace F₁ E₁))) :
    ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂ where
  baseMap := _root_.id
  toDiffeomorph :=
    { toEquiv :=
        { toFun := fun p => ⟨p.1, φ p.1 p.2⟩
          invFun := fun p => ⟨p.1, (φ p.1).symm p.2⟩
          left_inv := fun ⟨_, v⟩ => by simp
          right_inv := fun ⟨_, v⟩ => by simp }
      contMDiff_toFun := h_smooth
      contMDiff_invFun := h_smooth_inv }
  fiberLinearEquiv := φ
  fiber_compat _ _ := rfl

end FiberwiseEquiv

/-! ## Bijective `C^n` bundle homomorphisms are equivalences -/

section ToContMDiffVectorBundleEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {n : WithTop ℕ∞}
  {B₁ : Type*} [TopologicalSpace B₁] [ChartedSpace HB B₁]
  {B₂ : Type*} [TopologicalSpace B₂] [ChartedSpace HB B₂]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [ContMDiffVectorBundle n F₁ E₁ IB]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [ContMDiffVectorBundle n F₂ E₂ IB]

/-- `ContMDiffAt` analog of `continuousAt_clm_of_pointwise`: pointwise smoothness of a
continuous-linear-map-valued map lifts to operator-valued smoothness when the source
is finite-dimensional, by embedding `F₁ →L[𝕜] F₂` into `Fin (rank F₁) → F₂` via
evaluation on a basis and using a continuous linear left inverse.
TODO: move to `Mathlib.Geometry.Manifold.ContMDiff.NormedSpace`. -/
lemma contMDiffAt_clm_of_pointwise
    {X : Type*} [TopologicalSpace X] [ChartedSpace HB X]
    {A : X → (F₁ →L[𝕜] F₂)} {x : X}
    (h : ∀ v, ContMDiffAt IB 𝓘(𝕜, F₂) n (fun q => A q v) x) :
    ContMDiffAt IB 𝓘(𝕜, F₁ →L[𝕜] F₂) n A x := by
  haveI : FiniteDimensional 𝕜 (F₁ →L[𝕜] F₂) := ContinuousLinearMap.finiteDimensional
  let bF₁ := Module.finBasis 𝕜 F₁
  let evalBasis : (F₁ →L[𝕜] F₂) →L[𝕜] (Fin (Module.finrank 𝕜 F₁) → F₂) :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.apply 𝕜 F₂ (bF₁ i))
  have evalBasis_inj : Function.Injective evalBasis := fun L₁ L₂ heq => by
    ext v; rw [← bF₁.sum_equivFun v]; simp only [map_sum, map_smul]
    congr 1; ext i; exact congrArg _ (congrFun heq i)
  haveI : FiniteDimensional 𝕜 (Fin (Module.finrank 𝕜 F₁) → F₂) := inferInstance
  obtain ⟨gLM, hgLM⟩ := evalBasis.toLinearMap.exists_leftInverse_of_injective
    (evalBasis.ker_eq_bot_of_injective evalBasis_inj)
  let g : (Fin (Module.finrank 𝕜 F₁) → F₂) →L[𝕜] (F₁ →L[𝕜] F₂) :=
    ⟨gLM, LinearMap.continuous_of_finiteDimensional _⟩
  have hg : ∀ x, g (evalBasis x) = x := fun x => congr($(hgLM) x)
  have hEA : ContMDiffAt IB 𝓘(𝕜, Fin _ → F₂) n (evalBasis ∘ A) x :=
    contMDiffAt_pi_space.mpr fun i => h (bF₁ i)
  have : A = g ∘ evalBasis ∘ A := by funext q; exact (hg (A q)).symm
  rw [this]
  exact g.contDiff.contMDiff.contMDiffAt.comp _ hEA

/-- `ContMDiff` analog of `continuous_symm_of_fiberBijective'`: the inverse of a
fiberwise-linear, fiberwise-bijective `C^n` bijection between `C^n` vector bundles is `C^n`
when the base map is a `Diffeomorph`. -/
lemma contMDiff_symm_of_fiberBijective'
    {Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂}
    (hΦ_smooth : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n Φ)
    (baseMap : Diffeomorph IB IB B₁ B₂ n)
    {φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)}
    (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨baseMap x, φ x v⟩)
    (hbij : Function.Bijective Φ) (hφ_bij : ∀ x, Function.Bijective (φ x)) :
    ContMDiff (IB.prod 𝓘(𝕜, F₂)) (IB.prod 𝓘(𝕜, F₁)) n
      (Equiv.ofBijective Φ hbij).symm := by
  set Φ_equiv := Equiv.ofBijective Φ hbij
  have hproj : ∀ p, (Φ_equiv.symm p).proj = baseMap.symm p.proj := fun p => by
    have h1 : Φ (Φ_equiv.symm p) = p := Φ_equiv.apply_symm_apply p
    rw [hcompat (Φ_equiv.symm p).proj (Φ_equiv.symm p).snd] at h1
    have h := congrArg TotalSpace.proj h1
    simp only at h
    rw [← h, baseMap.symm_apply_apply]
  intro ⟨y, w⟩
  obtain ⟨x, rfl⟩ : ∃ x, baseMap x = y :=
    ⟨baseMap.symm y, baseMap.apply_symm_apply y⟩
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨?_, ?_⟩
  · simp only [hproj]
    have hbm_symm : ContMDiff (IB.prod 𝓘(𝕜, F₂)) IB n
        (fun p : TotalSpace F₂ E₂ => baseMap.symm p.proj) :=
      baseMap.symm.contMDiff.comp ((contMDiff_proj E₂).of_le le_top)
    exact hbm_symm.contMDiffAt
  · simp only [hproj, Diffeomorph.symm_apply_apply]
    set e₁ := trivializationAt F₁ E₁ x
    set e₂ := trivializationAt F₂ E₂ (baseMap x)
    have hx₁ := mem_baseSet_trivializationAt F₁ E₁ x
    have hx₂ := mem_baseSet_trivializationAt F₂ E₂ (baseMap x)
    have he₂_source : (⟨baseMap x, w⟩ : TotalSpace F₂ E₂) ∈ e₂.source :=
      e₂.mem_source.mpr hx₂
    set A : B₁ → (F₁ →L[𝕜] F₂) := trivializationCoord baseMap φ x with hA_def
    have hΦ_proj : ∀ p, (Φ p).proj = baseMap p.proj := fun p => by
      obtain ⟨a, b⟩ := p; simp [hcompat]
    have hA_contMDiff : ContMDiffAt IB 𝓘(𝕜, F₁ →L[𝕜] F₂) n A x := by
      apply contMDiffAt_clm_of_pointwise
      intro v
      suffices h : ContMDiffAt IB 𝓘(𝕜, F₂) n
          (fun q => (e₂ (Φ (e₁.toOpenPartialHomeomorph.symm (q, v)))).2) x by
        refine h.congr_of_eventuallyEq (Filter.eventually_of_mem
          (IsOpen.mem_nhds (e₁.open_baseSet.inter
            (baseMap.continuous.isOpen_preimage _ e₂.open_baseSet)) ⟨hx₁, ?_⟩) ?_)
        · exact hx₂
        · intro q ⟨hq₁, hq₂⟩
          exact trivializationCoord_apply hcompat x q hq₁ hq₂ v
      have he₁_tgt : (x, v) ∈ e₁.target := by
        rw [e₁.target_eq]; exact ⟨hx₁, Set.mem_univ _⟩
      have he₁_symm : ContMDiffAt IB (IB.prod 𝓘(𝕜, F₁)) n
          (fun q => e₁.toOpenPartialHomeomorph.symm (q, v)) x := by
        have h1 := e₁.contMDiffOn_symm (n := n) (IB := IB) |>.contMDiffAt
          (e₁.toOpenPartialHomeomorph.open_target.mem_nhds he₁_tgt)
        have h2 : ContMDiffAt IB (IB.prod 𝓘(𝕜, F₁)) n (fun q => (q, v)) x :=
          contMDiffAt_id.prodMk contMDiffAt_const
        exact h1.comp x h2
      have hpΦ : Φ (e₁.toOpenPartialHomeomorph.symm (x, v)) ∈ e₂.source := by
        rw [e₂.mem_source, hΦ_proj, e₁.proj_symm_apply he₁_tgt]; exact hx₂
      have hΦ_at : ContMDiffAt (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n Φ
          (e₁.toOpenPartialHomeomorph.symm (x, v)) := hΦ_smooth.contMDiffAt
      have he₂_at : ContMDiffAt (IB.prod 𝓘(𝕜, F₂)) (IB.prod 𝓘(𝕜, F₂)) n e₂
          (Φ (e₁.toOpenPartialHomeomorph.symm (x, v))) :=
        e₂.contMDiffOn (n := n) (IB := IB) |>.contMDiffAt
          (e₂.open_source.mem_nhds hpΦ)
      have hcomp1 : ContMDiffAt IB (IB.prod 𝓘(𝕜, F₂)) n
          (fun q => Φ (e₁.toOpenPartialHomeomorph.symm (q, v))) x := by
        refine hΦ_at.comp x he₁_symm
      have hcomp2 : ContMDiffAt IB (IB.prod 𝓘(𝕜, F₂)) n
          (fun q => e₂ (Φ (e₁.toOpenPartialHomeomorph.symm (q, v)))) x := by
        refine he₂_at.comp x hcomp1
      exact hcomp2.snd
    haveI : CompleteSpace F₁ := FiniteDimensional.complete 𝕜 F₁
    have hA_inv_at_x : (A x : F₁ →L[𝕜] F₂).IsInvertible :=
      trivializationCoord_isInvertible (baseMap := baseMap) hφ_bij x x ⟨hx₁, hx₂⟩
    have hA_inv_contMDiff : ContMDiffAt IB 𝓘(𝕜, F₂ →L[𝕜] F₁) n
        (ContinuousLinearMap.inverse ∘ A) x :=
      (hA_inv_at_x.contDiffAt_map_inverse (n := n)).contMDiffAt.comp x hA_contMDiff
    have hNice_smooth : ContMDiffAt (IB.prod 𝓘(𝕜, F₂)) 𝓘(𝕜, F₁) n
        (fun p : B₂ × F₂ =>
          ContinuousLinearMap.inverse (A (baseMap.symm p.1)) p.2) (e₂ ⟨baseMap x, w⟩) := by
      have h1 : ContMDiffAt (IB.prod 𝓘(𝕜, F₂)) 𝓘(𝕜, F₂ →L[𝕜] F₁) n
          (fun p : B₂ × F₂ =>
            ContinuousLinearMap.inverse (A (baseMap.symm p.1))) (e₂ ⟨baseMap x, w⟩) := by
        have hfst_at : ContMDiffAt (IB.prod 𝓘(𝕜, F₂)) IB n
            (fun p : B₂ × F₂ => p.1) (e₂ ⟨baseMap x, w⟩) := contMDiffAt_fst
        have hbm_at : ContMDiffAt IB IB n baseMap.symm
            ((fun p : B₂ × F₂ => p.1) (e₂ ⟨baseMap x, w⟩)) :=
          baseMap.symm.contMDiff.contMDiffAt
        have hcomp_bm : ContMDiffAt (IB.prod 𝓘(𝕜, F₂)) IB n
            (baseMap.symm ∘ (fun p : B₂ × F₂ => p.1)) (e₂ ⟨baseMap x, w⟩) :=
          hbm_at.comp _ hfst_at
        have hbm_eq :
            (baseMap.symm ∘ (fun p : B₂ × F₂ => p.1)) (e₂ ⟨baseMap x, w⟩) = x := by
          simp [e₂.coe_fst he₂_source, baseMap.symm_apply_apply]
        have hAinv_at : ContMDiffAt IB 𝓘(𝕜, F₂ →L[𝕜] F₁) n
            (ContinuousLinearMap.inverse ∘ A)
            ((baseMap.symm ∘ (fun p : B₂ × F₂ => p.1)) (e₂ ⟨baseMap x, w⟩)) := by
          rw [hbm_eq]; exact hA_inv_contMDiff
        exact hAinv_at.comp _ hcomp_bm
      exact h1.clm_apply contMDiffAt_snd
    have hG_snd_smooth : ContMDiffAt (IB.prod 𝓘(𝕜, F₂)) 𝓘(𝕜, F₁) n
        (fun p : B₂ × F₂ =>
          (e₁ (Φ_equiv.symm (e₂.toOpenPartialHomeomorph.symm p))).2)
        (e₂ ⟨baseMap x, w⟩) :=
      hNice_smooth.congr_of_eventuallyEq
        (trivializationCoord_inverse_eventuallyEq baseMap.toHomeomorph
          hcompat hbij hφ_bij x w).symm
    have he₂_smooth := (e₂.contMDiffOn (n := n) (IB := IB)).contMDiffAt
      (e₂.open_source.mem_nhds he₂_source)
    exact (hG_snd_smooth.comp _ he₂_smooth).congr_of_eventuallyEq
      (by filter_upwards [e₂.open_source.mem_nhds he₂_source] with p hp
          exact congrArg (fun q => (e₁ (Φ_equiv.symm q)).2)
            (e₂.toOpenPartialHomeomorph.left_inv hp).symm)

/-- A bijective `C^n` vector bundle homomorphism whose base map is a `Diffeomorph` is a `C^n`
vector bundle equivalence. The base map being a diffeomorphism cannot be derived from
bijectivity of the total-space map alone. See `toContMDiffVectorBundleEquivId` for the
special case where the base map is the identity. -/
noncomputable def ContMDiffVectorBundleHom.toContMDiffVectorBundleEquiv
    (f : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂)
    (baseMap : Diffeomorph IB IB B₁ B₂ n)
    (hbase : f.baseMap = baseMap)
    (hbij : Function.Bijective f.toFun) :
    ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂ :=
  match f, hbase, hbij with
  | ⟨_, Φ, hΦ_smooth, φ, hcompat⟩, rfl, hbij =>
    let hφ_bij := fiberBijective_of_bijective'
      hcompat hbij baseMap.injective
    { baseMap := baseMap
      toDiffeomorph :=
        { toEquiv := Equiv.ofBijective Φ hbij
          contMDiff_toFun := hΦ_smooth
          contMDiff_invFun :=
            contMDiff_symm_of_fiberBijective'
              hΦ_smooth baseMap hcompat hbij hφ_bij }
      fiberLinearEquiv := fun x =>
        LinearEquiv.ofBijective (φ x) (hφ_bij x)
      fiber_compat := hcompat }

end ToContMDiffVectorBundleEquiv

section ToContMDiffVectorBundleEquivId

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {n : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B → Type*} [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [ContMDiffVectorBundle n F₁ E₁ IB]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₂ : B → Type*} [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [ContMDiffVectorBundle n F₂ E₂ IB]

/-- `ContMDiff` analog of `continuous_symm_of_fiberBijective`: the inverse of a
fiberwise-linear, fiberwise-bijective `C^n` bijection between `C^n` vector bundles over the
same base (with identity base map) is itself `C^n`. This is the special case of
`contMDiff_symm_of_fiberBijective'` with `Diffeomorph.refl`. -/
lemma contMDiff_symm_of_fiberBijective
    {Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂}
    (hΦ_smooth : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n Φ)
    {φ : ∀ x, E₁ x →ₗ[𝕜] E₂ x}
    (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨x, φ x v⟩)
    (hbij : Function.Bijective Φ) (hφ_bij : ∀ x, Function.Bijective (φ x)) :
    ContMDiff (IB.prod 𝓘(𝕜, F₂)) (IB.prod 𝓘(𝕜, F₁)) n
      (Equiv.ofBijective Φ hbij).symm :=
  contMDiff_symm_of_fiberBijective' hΦ_smooth (Diffeomorph.refl IB B n) hcompat hbij hφ_bij

/-- Special case of `ContMDiffVectorBundleHom.toContMDiffVectorBundleEquiv` for the identity
base map. -/
noncomputable def ContMDiffVectorBundleHom.toContMDiffVectorBundleEquivId
    (f : ContMDiffVectorBundleHom 𝕜 IB n F₁ E₁ F₂ E₂)
    (hid : f.baseMap = _root_.id)
    (hbij : Function.Bijective f.toFun) :
    ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₂ E₂ :=
  f.toContMDiffVectorBundleEquiv (Diffeomorph.refl IB B n) hid hbij

end ToContMDiffVectorBundleEquivId

end
