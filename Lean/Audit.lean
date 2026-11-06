import SPR
import Lean.Util.CollectAxioms
import Lean.PrivateName

/-!
# 四阶分享工程的传递公理审计

默认构建检查全部导入的 SPR 定理，包括还原用户名称后的私有定理。
仅允许 propext、Classical.choice、Quot.sound；发现其他公理时构建失败。
这段代码执行审计，不为数学证明提供新公理。
-/

#check SPR.N4.Direct.robustSPR
#print axioms SPR.N4.Direct.robustSPR

set_option maxHeartbeats 0 in
-- Traverse all imported SPR theorem dependencies without truncating the audit.
run_cmd do
  let env ← Lean.getEnv
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked := 0
  let mut fourthOrderChecked := 0
  let mut privateChecked := 0
  for (name, info) in env.constants.toList do
    let userName := Lean.privateToUserName name
    if (`SPR).isPrefixOf userName && info.isTheorem then
      for axiomName in (← Lean.collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Unexpected axiom {axiomName} in {name}"
      checked := checked + 1
      if (`SPR.N4).isPrefixOf userName then
        fourthOrderChecked := fourthOrderChecked + 1
      if userName != name then
        privateChecked := privateChecked + 1
  if fourthOrderChecked < 20 then
    throwError "Incomplete fourth-order import: audited only {fourthOrderChecked} theorems"
  Lean.logInfo m!"SPR axiom audit passed: {checked} theorems; only \
    propext, Classical.choice, Quot.sound"
  Lean.logInfo m!"Fourth-order checked declarations: {fourthOrderChecked}"
  Lean.logInfo m!"Private SPR theorems included: {privateChecked}"
