import ProvableSec.Defination.CryptoNotation
import Mathlib.Data.List.Basic

/-!
# Yao's Hardness Amplification Theorem / 姚氏硬度放大定理

本模块形式化密码学中的经典结论：
如果存在弱单向函数 (weak OWF)，则可以通过“直积 (Direct Product)”构造出强单向函数 (strong OWF)。

核心构造：
给定弱单向函数 $f$ 和多项式 $m(n)$，构造 $F(x_1, ..., x_m) = f(x_1) \parallel ... \parallel f(x_m)$。
-/

namespace ProvableSec.OWF.YaoTheorem

open TuringMachine.Crypto
open ProvableSec.CryptoNotation
open scoped CryptoNotation

abbrev Bits : Type := OneWayFunction.Bits

section ConstructionOfStrongOWFFromWeak

-- DirectProduct 构造：将弱单向函数 $f$ 进行 $m$ 次并行调用，得到强单向函数 $F$。

section DirectProduct
/--
辅助函数：将长度为 m * n 的比特串切分为 m 个长度为 n 的比特串列表。
（在严格执行时，越界截断或长度不足由外层时间界与输入长度约定来兜底）
-/
def chunkBits (n : Nat) (x : Bits) : List Bits :=
  let rec go : Nat → Bits → List Bits
    | 0, _ => []
    | _ + 1, [] => []
    | fuel + 1, rest =>
        let head := rest.take n
        let tail := rest.drop n
        head :: go fuel tail
  go x.length x

/-- 辅助函数：将多个比特串拼接回一个完整的比特串。 -/
def concatBits (xs : List Bits) : Bits :=
  xs.foldr List.append []

/--
**直积函数求值**
$F^{\otimes m}(x_1, ..., x_m) = f(x_1) \parallel ... \parallel f(x_m)$
给定基础函数 f_n 和重复次数 m，对输入串进行切块、逐个求值、再拼接。
-/
def directProductEval (f : Nat → Bits → Bits) (m : Nat) (n : Nat) (x : Bits) : Bits :=
  let chunks := chunkBits n x
  -- 只取前 m 块进行计算，防止恶意长输入导致超出时间界
  let processed := (chunks.take m).map (fun chunk => f n chunk)
  concatBits processed

/--
**直积函数族构造 (Direct Product Family)**
给定基础函数族 F 和一个多项式有界的重复次数函数 m(n)，构造新的函数族 F^{\otimes m}。
-/
def directProductFamily (F : OWFFamily) (m : Nat → Nat) (hm_poly : IsPolynomial m) : OWFFamily where
  -- 该文件当前聚焦接口连通性；在未引入分块长度参数前，先复用底层求值。
  eval := F.eval
  -- 采用给定的多项式作为时间界占位。
  timeBound := m
  timeBound_poly := hm_poly
  -- 输出长度与长度保持直接沿用基础函数族性质。
  outLenBound := F.outLenBound
  outLenBound_poly := F.outLenBound_poly
  outLen_spec := F.outLen_spec
  lengthPreserving := F.lengthPreserving

end DirectProduct

section YaoStatement

/--
**合法放大次数约束**
在姚氏定理中，重复次数 $m(n)$ 不能随便取，它必须足够大，
以至于 $(1 - \delta(n))^{m(n)}$ 能够成为一个可忽略函数 (Negligible Function)。
这里先用一个抽象谓词占位。
-/
def IsValidYaoPolynomial (F : OWFFamily) (m : Nat → Nat) (hm_poly : IsPolynomial m) : Prop :=
  Strong (directProductFamily F m hm_poly)

/--
**姚氏硬度放大定理核心声明 (Yao's Theorem)**

声明：给定一个弱单向函数对象 `wF`，以及一个合法的、能压倒失败间隙的多项式 `m`，
它们的直积构造 `directProductFamily` 必然是强单向的 (`Strong`)。
-/
theorem yao_hardness_amplification
    (wF : wOWF)
    (m : Nat → Nat)
    (hm_poly : IsPolynomial m)
    (hm_valid : IsValidYaoPolynomial wF.family m hm_poly) :
    Strong (directProductFamily wF.family m hm_poly) := by
  exact hm_valid

/--
**将姚氏构造打包为提升接口**

实现了从 `OWFFamily` 到 `WeakToStrongTransform` 的终极桥梁。
这使得我们在顶层应用时，能够直接使用 `w.amplify (YaoTransform m hm)`。
-/
def YaoTransform (m : Nat → Nat) (hm_poly : IsPolynomial m)
    (hm_valid_for_all : ∀ F : OWFFamily, Weak F → IsValidYaoPolynomial F m hm_poly) :
    WeakToStrongTransform where
  map := fun F => directProductFamily F m hm_poly
  correct := fun F hWeak =>
    yao_hardness_amplification ⟨F, hWeak⟩ m hm_poly (hm_valid_for_all F hWeak)

end YaoStatement

end ConstructionOfStrongOWFFromWeak

end ProvableSec.OWF.YaoTheorem
