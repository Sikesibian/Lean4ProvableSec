# ProvableSec

在 Lean 4 中形式化可证明安全基础组件，当前重点是：图灵机语义、PPT 抽象、复杂度类接口、OWF 定义与符号层。**（AI辅助生成）**

## 项目定位

- 为可证明安全证明提供可复用的 Lean 接口层。
- 分离“机器语义层”和“概率/密码学语义层”，降低后续定理开发耦合度。
- 提供贴近教材记号的封装（如 `Pr`, `Weak`, `Strong`）。

## 快速开始

```bash
lake update
lake build
lake exe provablesec
```

在其他 Lean 文件中使用本库：

```lean
import ProvableSec
```

## 目录与模块

> 说明：仓库当前实际路径使用 `Defination`、`Baisc`（历史拼写），README 以实际路径为准。

| 模块 | 作用 | 状态 |
|---|---|---|
| `ProvableSec.lean` | 根入口，聚合导入库模块 | 已接入构建 |
| `ProvableSec/Defination/Baisc/TuringMachine/TMbasic.lean` | 单带 DTM/NTM 基础语义与语言定义 | 可用 |
| `ProvableSec/Defination/Baisc/TuringMachine/TMCrypto.lean` | 基于 `Mathlib` TM2 的敌手/PPT 抽象接口 | 可用 |
| `ProvableSec/Defination/Baisc/Complexity/ComplexityClass.lean` | `P`/`NP`/`coNP`/`BPP`/`PPT` 接口化定义 | 可用 |
| `ProvableSec/Defination/OneWayFunction/owfBasic.lean` | weak/strong OWF 定义（含可忽略函数接口） | 可用 |
| `ProvableSec/Defination/CryptoNotation.lean` | 密码学友好符号层与 `Context` 打包层 | 可用 |
| `ProvableSec/ClassicTheorem/YaoTheorem.lean` | Yao 定理陈述层（same-family/transform/existential）与基础蕴含引理 | 初版可用 |
| `ProvableSec/Examples/*.lean` | 符号层使用示例与验证样例 | 示例层 |
| `Main.lean` | 可执行入口（最小连通性检查） | 可用 |

## 核心语义（简要）

- DTM 有界执行：

$$
\mathrm{runSteps}(0,c)=c,\qquad
\mathrm{runSteps}(n+1,c)=\mathrm{runSteps}(n,\delta(c)).
$$

- NTM 接受（存在分支）：

$$
\mathrm{Accept}_{NTM}(x)\iff
\exists t,\exists c\in C_t,\ \mathrm{state}(c)=q_{acc}.
$$

- strong OWF（接口层）：对任意 PPT 反演器，其成功概率关于安全参数是可忽略函数。

## 教材记号对照（推荐）

| Lean 接口 | 教材读法 |
|---|---|
| `f : Context.OWF.OWFunction` | 单向函数候选 $f$ |
| `A : Context.OWF.Adversary C` | 反演器 $A$（PPT） |
| `n : Nat` | 安全参数 $n$ |
| `Pr[M|f](A, n)` | $\Pr[A \text{ 在 } n \text{ 处反演 } f]$ |
| `Context.OWF.IsWeak C M f` | $f$ 是 weak OWF |
| `Context.OWF.IsStrong C M f` | $f$ 是 strong OWF |

## 使用示例

### 示例 1：最小导入与记号开启

```lean
import ProvableSec.Defination.CryptoNotation
open ProvableSec.CryptoNotation
open scoped CryptoNotation
```

说明：如果你只做 OWF/概率记号层陈述，优先按上面方式导入，不必直接展开底层 TM2 细节。

### 示例 2：全局概率语义的基本性质

```lean
import ProvableSec.Defination.CryptoNotation

namespace Demo

open ProvableSec.CryptoNotation
open scoped CryptoNotation

variable (C : Context)
variable (M : Context.Model C)
variable (A : Context.Adversary C)
variable (n : Nat)

example : PrFail[M](A, n) = 1 - Pr[M](A, n) := by
	simpa using M.PrFail_eq A n

example : 0 ≤ Pr[M](A, n) := by
	simpa using M.Pr_nonneg A n

example : Pr[M](A, n) ≤ 1 := by
	simpa using M.Pr_le_one A n

end Demo
```

### 示例 3：OWF 单函数概率记号

```lean
import ProvableSec.Defination.CryptoNotation

namespace DemoOWF

open ProvableSec.CryptoNotation
open scoped CryptoNotation

variable (C : Context)
variable (M : Context.OWF.Model C)
variable (f : Context.OWF.OWFunction)
variable (A : Context.OWF.Adversary C)
variable (n : Nat)

example : PrFail[M|f](A, n) = 1 - Pr[M|f](A, n) := by
	simpa using M.PrFail_eq f A n

example : 0 ≤ Pr[M|f](A, n) := by
	simpa using M.Pr_nonneg f A n

end DemoOWF
```

可参考完整示例文件：
- `ProvableSec/Examples/CryptoNotationUsage.lean`
- `ProvableSec/Examples/CryptoNotationValidation.lean`
- `ProvableSec/Examples/CryptoNotationConcrete.lean`

## 注意事项

- 目录拼写以仓库实际为准：`Defination`、`Baisc` 是当前真实路径，不是笔误后的替代目录。
- 当前 `ProvableSec/ClassicTheorem/YaoTheorem.lean` 已提供抽象陈述与基础蕴含证明；具体密码学构造证明仍需后续逐步补全。
- 新增模块后请同时更新 `ProvableSec.lean`（必要时也更新 `ProvableSec/Examples.lean`），否则文件可能未纳入构建。
- 在 Windows 下编辑 Lean 文件请保持 UTF-8 编码，并使用空格缩进（避免 tab 引发解析/风格问题）。
- 如果新增定义后下游仍提示找不到常量，优先执行一次 `lake build` 以刷新 `.olean` 产物。
- 文档中的数学记号用于阅读友好，最终以 Lean 中实际定义和类型检查结果为准。

## 推荐阅读顺序

1. `TMbasic.lean`：先看机器执行与接受语义。
2. `TMCrypto.lean`：再看敌手和 PPT 时间界接口。
3. `ComplexityClass.lean`：补齐复杂度类抽象。
4. `owfBasic.lean`：进入 OWF 定义层。
5. `CryptoNotation.lean` 与 `Examples/`：使用符号层进行陈述。
6. `YaoTheorem.lean`：作为后续经典定理扩展位。

## 维护建议

- 新增模块后，优先在 `ProvableSec.lean` 中加入 `import`，确保被 `lake build` 覆盖。
- 若目标是“论文式写法”，优先通过 `CryptoNotation` 与 `Context` 层暴露接口，减少机器参数噪声。
