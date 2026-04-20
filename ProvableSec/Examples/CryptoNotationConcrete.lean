import ProvableSec.Defination.CryptoNotation

/-!
# CryptoNotation Concrete Example / 具体实例展示

本文件展示如何在新架构下实例化一个具体的函数族。
-/

namespace ProvableSec.Examples.Concrete

open TuringMachine.Crypto
open ProvableSec.CryptoNotation
open scoped CryptoNotation

/-- 辅助引理：恒等函数 n ↦ n 满足多项式有界。 -/
theorem id_isPolynomial : IsPolynomial (fun n : Nat => n) := by
  refine ⟨1, 1, ?_⟩
  intro n
  calc
    n ≤ n + 1 := Nat.le_succ n
    _ = 1 * (n + 1) ^ 1 := by simp

/--
具体实例：恒等函数族 (Identity Function Family)。
显然它不是单向的，但它是一个合法的 OWFFamily 结构实例。
-/
def IdentityFamily : OWFFamily where
  eval := fun _ x => x
  timeBound := fun n => n
  timeBound_poly := id_isPolynomial
  outLenBound := fun n => n
  outLenBound_poly := id_isPolynomial
  outLen_spec := by
    intro n x hx
    simp [hx]
  lengthPreserving := by
    intro n x hx
    simp [hx]

-- 在此时，针对 IdentityFamily 的成功概率已经是一个合法的非计算实数。
-- 任何 Inverter A 在它上面的 Pr[IdentityFamily](A, n) 都可以被调用。

end ProvableSec.Examples.Concrete
