/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap

/-! # The vector bundle of continuous alternating maps is `C^n`

We show that the bundle of continuous alternating maps between two `C^n` vector bundles with
finite-dimensional typical fibers over a common base is again a `C^n` vector bundle, parallel
to what `Mathlib/Geometry/Manifold/VectorBundle/Hom.lean` does for the bundle of continuous
linear maps.

The topological vector bundle structure on `fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x` is provided by
`Mathlib/Topology/VectorBundle/ContinuousAlternatingMap.lean`.

The proof factors through the linear isometric embedding of alternating maps into multilinear
maps and pulls back smoothness via the finite-dimensional postcomposition iff
`ContinuousLinearMap.contDiff_comp_iff`, valid for all `n : WithTop ℕ∞` (including `n = ω`)
when the codomain is finite-dimensional.
-/

public section

noncomputable section

open Bundle Set Bundle.Pretrivialization ContinuousAlternatingMap

open scoped Manifold Bundle Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {ι : Type*} [Fintype ι]

variable {B F₁ F₂ : Type*} {n : WithTop ℕ∞}
  {E₁ : B → Type*} {E₂ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [ContMDiffVectorBundle n F₁ E₁ IB]
  [ContMDiffVectorBundle n F₂ E₂ IB]

theorem Bundle.contMDiffOn_continuousAlternatingMapCoordChange
    {e₁ e₁' : Trivialization F₁ (π F₁ E₁)} {e₂ e₂' : Trivialization F₂ (π F₂ E₂)}
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    ContMDiffOn IB 𝓘(𝕜, (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)) n
      (continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  have h₁ := contMDiffOn_coordChangeL (IB := IB) e₁' e₁ (n := n)
  have h₂ := contMDiffOn_coordChangeL (IB := IB) e₂ e₂' (n := n)
  refine (h₁.mono ?_).cle_continuousAlternatingMapCongr (h₂.mono ?_) <;> mfld_set_tac

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

/-- The prebundle of continuous alternating maps is `C^n`-smooth. -/
instance Bundle.ContinuousAlternatingMap.vectorPrebundle.isContMDiff :
    (Bundle.ContinuousAlternatingMap.vectorPrebundle (𝕜 := 𝕜) (ι := ι)
      (F₁ := F₁) (E₁ := E₁) (F₂ := F₂) (E₂ := E₂)).IsContMDiff IB n where
  exists_contMDiffCoordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨Bundle.Pretrivialization.continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂',
      Bundle.contMDiffOn_continuousAlternatingMapCoordChange,
      Bundle.Pretrivialization.continuousAlternatingMapCoordChange_apply⟩

/-- If `E₁` and `E₂` are `C^n` vector bundles with finite-dimensional typical fibers, then the
bundle of continuous `ι`-slot alternating maps from `E₁` to `E₂` is also a `C^n` vector bundle. -/
instance ContMDiffVectorBundle.continuousAlternatingMap :
    ContMDiffVectorBundle n (F₁ [⋀^ι]→L[𝕜] F₂)
      (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x) IB :=
  (Bundle.ContinuousAlternatingMap.vectorPrebundle (𝕜 := 𝕜) (ι := ι)
    (F₁ := F₁) (E₁ := E₁) (F₂ := F₂) (E₂ := E₂)).contMDiffVectorBundle IB

end
