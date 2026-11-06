import Mathlib

/-!
# Hurwitz stability independent of polynomial degree

Every complex root must lie in the open left half-plane. This module contains
no synthesis assertion and places no restriction on polynomial degree.
-/
namespace SPR
open Polynomial

/-- Every complex root of a real polynomial has strictly negative real part. -/
def IsHurwitz (a : ℝ[X]) : Prop :=
  ∀ z : ℂ, (a.map (algebraMap ℝ ℂ)).IsRoot z → z.re < 0

namespace Hurwitz

/-- A real root of a Hurwitz polynomial is negative. -/
theorem real_root_neg {p : ℝ[X]} (hp : IsHurwitz p) {x : ℝ}
    (hx : p.IsRoot x) : x < 0 :=
  hp (x : ℂ) (hx.map (f := algebraMap ℝ ℂ))

/-- With nonnegative leading coefficient, Hurwitz polynomials are positive on [0,∞). -/
theorem eval_pos {p : ℝ[X]} (hp : IsHurwitz p)
    (hlc : 0 ≤ p.leadingCoeff) {x : ℝ} (hx : 0 ≤ x) : 0 < p.eval x :=
  zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
    (fun _ hy => (real_root_neg hp hy).trans_le hx) hlc

theorem hurwitz_derivative {p : ℝ[X]} (hp : IsHurwitz p) (hdeg : 0 < p.natDegree) :
    IsHurwitz p.derivative := by
  let P := p.map (algebraMap ℝ ℂ)
  have hPdeg : 0 < P.natDegree := by simpa [P] using hdeg
  have hPdne : P.derivative ≠ 0 := by
    have hd := degree_derivative_eq P hPdeg
    intro he
    simp [he] at hd
  have hconv : Convex ℝ {z : ℂ | z.re < 0} :=
    (convex_Iio (0 : ℝ)).linear_preimage Complex.reLm
  have hroots : P.rootSet ℂ ⊆ {z : ℂ | z.re < 0} := by
    intro z hz
    exact hp z (by simpa [P, coe_aeval_eq_eval] using (mem_rootSet.mp hz).2)
  intro z hz
  have hm : z ∈ P.derivative.rootSet ℂ := by
    apply mem_rootSet.mpr
    refine ⟨hPdne, ?_⟩
    simpa [P, derivative_map, coe_aeval_eq_eval] using hz
  exact (convexHull_min hroots hconv)
    (P.rootSet_derivative_subset_convexHull_rootSet
      (natDegree_pos_iff_degree_pos.mp hPdeg) hm)

theorem derivative_natDegree_exact {p : ℝ[X]} (hdeg : 0 < p.natDegree) :
    p.derivative.natDegree = p.natDegree - 1 :=
  natDegree_eq_of_degree_eq_some (degree_derivative_eq p hdeg)

theorem derivative_leadingCoeff_pos {p : ℝ[X]} (hlc : 0 < p.leadingCoeff)
    (hdeg : 0 < p.natDegree) : 0 < p.derivative.leadingCoeff := by
  rw [← coeff_natDegree, derivative_natDegree_exact hdeg, coeff_derivative,
    Nat.sub_add_cancel (by omega : 1 ≤ p.natDegree), coeff_natDegree]
  exact mul_pos hlc (by positivity)

theorem hurwitz_coeff_pos {p : ℝ[X]} (hp : IsHurwitz p) (hlc : 0 < p.leadingCoeff)
    (n : ℕ) (hn : n ≤ p.natDegree) : 0 < p.coeff n := by
  induction n generalizing p with
  | zero =>
    rw [coeff_zero_eq_eval_zero]
    exact eval_pos hp hlc.le le_rfl
  | succ n ih =>
    have hdeg : 0 < p.natDegree := by omega
    have hn' : n ≤ p.derivative.natDegree := by
      rw [derivative_natDegree_exact hdeg]
      omega
    have h := ih (hurwitz_derivative hp hdeg) (derivative_leadingCoeff_pos hlc hdeg) hn'
    rw [coeff_derivative] at h
    exact (mul_pos_iff_of_pos_right (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mp h

end Hurwitz
end SPR
