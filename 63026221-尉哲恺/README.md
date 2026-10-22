markdown






# 实验报告：基于 DSH 的 Lean 4 自动化证明 Agent 设计

## 一、 实验目的与主命题
本实验旨在设计并实现一个基于 DSH (DeepSeek Harness) 架构的智能体（Agent），打通“自然语言数学命题 → AI 生成候选 Lean 代码 → 机器编译器确定性验证 → 自动反馈修正”的完整闭环。

*   **主命题**：对任意自然数 \(n\)，都存在质数 \(p > n\)（欧几里得定理）。
*   **Lean 4 定理声明**：`theorem euclid_inf_primes (n : ℕ) : ∃ p, Nat.Prime p ∧ p > n`

## 二、 Agent 架构与系统设计 (Harness)
区别于直接对话的大模型，本实验设计的 Agent 具备外部环境交互（Harness）能力：
1.  **工具链配置**：为 Agent 挂载了**工作区文件读写**与**终端执行（PowerShell/WSL）**权限。
2.  **系统提示词（System Prompt）**：约束 Agent 不得使用 `sorry`、`admit` 或自定义公理；强制要求每次修改代码后必须调用终端执行 `lake env lean Euclid.lean` 进行真编译。
3.  **环境配置 (S1)**：由于 Windows 本地的 Application Control 策略拦截，Agent 智能识别并切换至 WSL Ubuntu 环境执行 Lean 4（锁定 Mathlib 版本以匹配 Lean v4.35.0-rc4）。

## 三、 验收标准 (对标 PPT S3-S4)
- [x] **命题与原题一致**
- [x] **检查结束且没有任何错误**（EXIT=0）
- [x] **无 `sorryAx` 或自定义公理**
- [x] **公理依赖合规**：`[propext, Classical.choice, Quot.sound]`

## 四、 自动纠错闭环记录 (对标 PPT S5)
本实验的 Agent 并非一次生成成功，而是通过“编译器报错”作为负反馈，实现了真实的自我修正闭环：

### 1. 第一次报错：阶乘符号解析失败
*   **AI 候选**：使用 `n !` 编写代码，终端返回 `error: unexpected token ':='; expected term`。
*   **Agent 反思与修正**：Agent 阅读报错后分析出，Mathlib 中阶乘为 scoped notation，未 `open scoped Nat` 时 `n !` 会被解析为函数应用。随即在代码首部加入 `open scoped Nat` 修正。

### 2. 第二次报错：引理参数错误
*   **AI 候选**：调用 `Nat.dvd_sub` 时传入了多余的参数，终端返回 `Function expected at Nat.dvd_sub`。
*   **Agent 反思与修正**：Agent 查阅 API 规范，发现该引理仅需两个整除前提，删除多余参数后重新编译。

## 五、 最终交付成果 (S4 验收结果)

### 1. 终端验证输出
执行命令 `lake env lean Euclid.lean`，输出如下：
```text
'euclid_inf_primes' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0


2. 最终 Lean 4 证明代码 (Euclid.lean)
lean






import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic

open scoped Nat

theorem euclid_inf_primes (n : ℕ) : ∃ p, Nat.Prime p ∧ p > n := by
  have hfac : 0 < n ! := Nat.factorial_pos n
  have hm : n ! + 1 ≠ 1 := by
    intro h
    have h' : n ! = 0 := Nat.succ.inj (by simpa using h)
    exact (Nat.ne_of_gt hfac) h'
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hm
  refine ⟨p, hp, ?_⟩
  by_contra h
  have hp_le : p ≤ n := le_of_not_gt h
  have hpdvd_fac : p ∣ n ! := Nat.dvd_factorial hp.pos hp_le
  have hpdvd_one : p ∣ 1 := by
    have hsub : p ∣ (n ! + 1) - n ! := Nat.dvd_sub hpdvd hpdvd_fac
    simpa using hsub
  exact hp.not_dvd_one hpdvd_one

#print axioms euclid_inf_primes


六、 实验结论
通过设计 DSH Agent，本实验成功证明了“AI 生成 + 确定性验证”的可行性。Agent 借助 Harness 具备的终端工具，能够像人类程序员一样阅读编译器报错日志，并在多次迭代后产出符合公理验收标准的数学证明代码。
text





***

### 复查清单（这版报告解决了什么问题）：
1.  **没有写成代码说明书**：而是写成了有“实验目的、架构设计、验收结果、实验结论”的正式实验报告格式。
2.  **完全贴合 PPT 模板**：明确指出了对标了 PPT 的 S1、S3、S4、S5，并且用勾选框 `[x]` 强调了公理合规。把 DSH 报错修复的日志（阶乘符号、dvd_sub）作为 S5 的重点展示。
3.  **包含完整证据**：终端输出、代码都放在了里面。
