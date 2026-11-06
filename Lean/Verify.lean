import Main
import Lean.Util.CollectAxioms

/-!
# 原命题展开核验

以下类型赋值展开稳定性、同一个首一恰四次分子、全箱与全实频率量词。
若公开主定理不具有这一精确类型，本文件无法编译。
-/

open Polynomial

-- This type expands the complete original quantifier contract.
example : ∀ K : SPR.N4.Box4,
    (∀ a : SPR.N4.Poly4, K.Contains a →
      ∀ z : ℂ, (a.poly.map (algebraMap ℝ ℂ)).IsRoot z → z.re < 0) →
    ∃ b : ℝ[X], b.Monic ∧ b.natDegree = 4 ∧
      ∀ a : SPR.N4.Poly4, K.Contains a → ∀ w : ℝ,
        0 < (b.eval₂ (algebraMap ℝ ℂ) ((w : ℂ) * Complex.I) /
          a.poly.eval₂ (algebraMap ℝ ℂ) ((w : ℂ) * Complex.I)).re :=
  SPR.N4.Direct.robustSPR

#check SPR.N4.Direct.robustSPR
#print SPR.N4.Direct.robustSPR
#print SPR.N4.RobustSPRStatement
#print SPR.N4.Box4
#print SPR.N4.Box4.Contains
#print SPR.N4.Box4.RobustlyHurwitz
#print SPR.N4.Poly4.poly
#print SPR.N4.FrequencySPR
#print SPR.IsHurwitz
#print axioms SPR.N4.Direct.robustSPR

run_cmd do
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in (← Lean.collectAxioms `SPR.N4.Direct.robustSPR) do
    unless allowed.contains name do
      throwError "Unexpected root axiom {name}"
  Lean.logInfo "N4 expanded original contract and root axiom policy passed"
