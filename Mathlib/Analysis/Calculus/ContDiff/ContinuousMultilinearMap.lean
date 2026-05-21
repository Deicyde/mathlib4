/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smoothness of operations on continuous multilinear maps

We prove `C^n`-smoothness of `p ↦ ContinuousMultilinearMap.compContinuousLinearMapL (f p)`
when `f` is `C^n`, plus the diagonal specialization for the constant family `fun _ : ι ↦ p`.
-/

public section

variable {𝕜 ι E : Type*} {F G : ι → Type*} {H : Type*}
  [NontriviallyNormedField 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
  [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace 𝕜 (G i)]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  {s : Set E} {x : E}

open ContinuousMultilinearMap
open scoped ContDiff

theorem ContinuousMultilinearMap.contDiffWithinAt_compContinuousLinearMapL
    {n : WithTop ℕ∞} {f : E → ∀ i, F i →L[𝕜] G i} (hf : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n (fun p ↦ compContinuousLinearMapL (F := H) (f p)) s x :=
  (compContinuousLinearMapContinuousMultilinear 𝕜 F G H).contDiff.comp_contDiffWithinAt hf

theorem ContinuousMultilinearMap.contDiffAt_compContinuousLinearMapL
    {n : WithTop ℕ∞} {f : E → ∀ i, F i →L[𝕜] G i} (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun p ↦ compContinuousLinearMapL (F := H) (f p)) x :=
  (compContinuousLinearMapContinuousMultilinear 𝕜 F G H).contDiff.comp_contDiffAt x hf

theorem ContinuousMultilinearMap.contDiffOn_compContinuousLinearMapL
    {n : WithTop ℕ∞} {f : E → ∀ i, F i →L[𝕜] G i} (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun p ↦ compContinuousLinearMapL (F := H) (f p)) s :=
  (compContinuousLinearMapContinuousMultilinear 𝕜 F G H).contDiff.comp_contDiffOn hf

theorem ContinuousMultilinearMap.contDiff_compContinuousLinearMapL
    {n : WithTop ℕ∞} {f : E → ∀ i, F i →L[𝕜] G i} (hf : ContDiff 𝕜 n f) :
    ContDiff 𝕜 n (fun p ↦ compContinuousLinearMapL (F := H) (f p)) :=
  (compContinuousLinearMapContinuousMultilinear 𝕜 F G H).contDiff.comp hf

theorem ContinuousMultilinearMap.compContinuousLinearMapL_diag_contDiff
    {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
    {M' : Type*} [NormedAddCommGroup M'] [NormedSpace 𝕜 M']
    {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N] {n : WithTop ℕ∞} :
    ContDiff 𝕜 n (fun p : M →L[𝕜] M' ↦ compContinuousLinearMapL (F := N) (fun _ : ι ↦ p)) :=
  contDiff_compContinuousLinearMapL (contDiff_pi.2 fun _ ↦ contDiff_id)
