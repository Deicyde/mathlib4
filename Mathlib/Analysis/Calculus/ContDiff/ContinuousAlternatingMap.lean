/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.ContinuousMultilinearMap
public import Mathlib.Analysis.Normed.Module.Alternating.Basic

/-!
# Smoothness of operations on continuous alternating maps

The pullback operator `compContinuousLinearMapCLM` is `C^n` in its defining continuous linear map.
For `n : ℕ∞` this holds in any characteristic with `[CompleteSpace F]`; the analytic case `n = ω`
requires `[CharZero 𝕜]` so that the polarization formula can lift the order-`n` Taylor coefficient
into the alternating-target operator space.

## Implementation notes

In characteristic 0, the explicit `1/n!`-weighted symmetrized sum produces a continuous
multilinear map whose diagonal recovers the polynomial `p ↦ compContinuousLinearMapCLM p`,
showing that this polynomial of degree `Fintype.card ι` is analytic. In positive characteristic
`p ≤ Fintype.card ι` the polarization formula is unavailable, and no continuous symmetric
multilinear lift into the alternating-target space is known (see the discussion in
`Mathlib/Analysis/Calculus/ContDiff/LinearIsometry.lean` on the Banach branch).
-/

public section

open ContinuousAlternatingMap ContinuousMultilinearMap
open scoped ContDiff

variable {𝕜 ι E F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞}

theorem ContinuousAlternatingMap.contDiff (f : E [⋀^ι]→L[𝕜] F) : ContDiff 𝕜 n f :=
  f.toContinuousMultilinearMap.contDiff

variable [CompleteSpace F] [CharZero 𝕜]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

/-- In characteristic 0, the symmetric continuous multilinear lift of `compContinuousLinearMapCLM`
whose diagonal recovers the function. Constructed via the polarization formula
`(1 / n!) Σ_σ Φ ∘ (p_{σ(1)}, …, p_{σ(n)})` with `n = Fintype.card ι`.

The output lands in the alternating-target operator space because the `1/n!`-weighted sum
over symmetric-group permutations of the `p_i`'s preserves alternation of `Φ` in its `v_i`
arguments. -/
private noncomputable def compContinuousLinearMapPolarized :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin (Fintype.card ι) ↦ E →L[𝕜] E')
      ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) :=
  -- The explicit polarization formula. Char-0 hypothesis is used to divide by `n!`.
  sorry

private theorem compContinuousLinearMapPolarized_diag (p : E →L[𝕜] E') :
    compContinuousLinearMapPolarized (E := E) (E' := E') (F := F) (ι := ι) (fun _ ↦ p) =
      compContinuousLinearMapCLM p :=
  sorry

theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff :
    ContDiff 𝕜 n (compContinuousLinearMapCLM :
      (E →L[𝕜] E') → (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) := by
  -- Write `compContinuousLinearMapCLM` as the diagonal of the polarized multilinear lift,
  -- then conclude via `ContinuousMultilinearMap.contDiff` ∘ diagonal.
  have hμ : ContDiff 𝕜 n (compContinuousLinearMapPolarized (𝕜 := 𝕜) (ι := ι)
      (E := E) (E' := E') (F := F)) := ContinuousMultilinearMap.contDiff _
  have hΔ : ContDiff 𝕜 n (fun p : E →L[𝕜] E' ↦ (fun _ : Fin (Fintype.card ι) ↦ p)) :=
    contDiff_pi.mpr (fun _ ↦ contDiff_id)
  have heq : compContinuousLinearMapCLM (𝕜 := 𝕜) (ι := ι) (E := E) (E' := E') (F := F) =
      (fun (p : Fin (Fintype.card ι) → (E →L[𝕜] E')) ↦
        compContinuousLinearMapPolarized p) ∘
      (fun p : E →L[𝕜] E' ↦ (fun _ ↦ p)) := by
    funext p
    exact (compContinuousLinearMapPolarized_diag p).symm
  rw [heq]
  exact hμ.comp hΔ
