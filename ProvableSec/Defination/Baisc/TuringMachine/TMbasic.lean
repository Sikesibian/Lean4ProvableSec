import Mathlib.Data.List.Basic

/-!
# 图灵机基础框架 / Turing Machine Basic Framework

## 目标 / Goal
- 提供“先可编译、可运行、可扩展”的图灵机核心定义。
- provide a compile-first, runnable, and extensible TM core.

## 内容 / Contents
- 单带 tape 结构与移动语义 / one-tape data model and movement semantics
- 确定性图灵机 DTM 的一步与有界步语义 / one-step and bounded-step semantics for DTM
- 非确定性图灵机 NTM 的分支语义 / branching semantics for NTM
- DTM 到 NTM 的标准嵌入 / canonical embedding from DTM to NTM

## 语法与关键字 / Syntax and Keywords
- `namespace ... end`：命名空间封装。
- `inductive`：定义归纳类型（如 `Move`）。
- `structure`：定义记录类型（如 `Tape`, `DTM`）。
- `def`：定义函数。
- `match ... with`：模式匹配。
- `if ... then ... else`：条件分支。
- `let ... := ...`：局部绑定。
- `Prop` 与 `Set`：分别表示命题与集合。

## 公式化语义 / Formal Semantics

设配置为 $c_t$，DTM 单步转移记为 $\delta$：

$$
c_{t+1} = \delta(c_t).
$$

有界执行满足：

$$
\mathrm{runSteps}(0,c)=c,\qquad
\mathrm{runSteps}(n+1,c)=\mathrm{runSteps}(n,\delta(c)).
$$

DTM 接受定义：

$$
\mathrm{Accept}_{DTM}(w) \iff \exists t,\ \mathrm{state}(\mathrm{eval}(w,t))=q_{acc}.
$$

NTM 配置集语义：

$$
C_{t+1}=\bigcup_{c\in C_t}\mathrm{Next}(c),
\qquad
\mathrm{Accept}_{NTM}(w)\iff\exists t,\exists c\in C_t,\ \mathrm{state}(c)=q_{acc}.
$$
-/
namespace TuringMachine

universe u v

/--
读写头移动方向。
head movement direction.
-/
inductive Move where
  | left
  | stay
  | right
  deriving DecidableEq

/--
单带 tape 三段表示。
three-part one-tape representation.

- `left`: 头左侧内容（最近单元在前）；symbols left of head, nearest first.
- `head`: 头下当前符号；current symbol under head.
- `right`: 头右侧内容（最近单元在前）；symbols right of head, nearest first.
-/
structure Tape (Γ : Type u) where
  left : List Γ
  head : Γ
  right : List Γ
  deriving DecidableEq

namespace Tape

variable {Γ : Type u}

/-- 读取头下符号。read the head symbol. -/
def read (t : Tape Γ) : Γ :=
  t.head

/-- 在头下写入符号。write at the head cell. -/
def write (t : Tape Γ) (a : Γ) : Tape Γ :=
  { t with head := a }

/-- 左移，越界处补空白符。move left, using blank beyond known boundary. -/
def moveLeft (blank : Γ) (t : Tape Γ) : Tape Γ :=
  match t.left with
  | [] =>
      { left := []
        head := blank
        right := t.head :: t.right }
  | x :: xs =>
      { left := xs
        head := x
        right := t.head :: t.right }

/-- 右移，越界处补空白符。move right, using blank beyond known boundary. -/
def moveRight (blank : Γ) (t : Tape Γ) : Tape Γ :=
  match t.right with
  | [] =>
      { left := t.head :: t.left
        head := blank
        right := [] }
  | x :: xs =>
      { left := t.head :: t.left
        head := x
        right := xs }

/-- 按给定方向移动。move according to direction. -/
def move (blank : Γ) (dir : Move) (t : Tape Γ) : Tape Γ :=
  match dir with
  | .left => moveLeft blank t
  | .stay => t
  | .right => moveRight blank t

/-- 由输入构造初始 tape。build initial tape from input. -/
def ofInput (blank : Γ) : List Γ -> Tape Γ
  | [] =>
      { left := []
        head := blank
        right := [] }
  | x :: xs =>
      { left := []
        head := x
        right := xs }

end Tape

/-- 一步转移指令。one transition instruction. -/
structure Instruction (Q : Type u) (Γ : Type v) where
  nextState : Q
  writeSym : Γ
  moveDir : Move

/-- 配置 = 状态 + tape。configuration = state + tape. -/
structure Config (Q : Type u) (Γ : Type v) where
  state : Q
  tape : Tape Γ
  deriving DecidableEq

/--
确定性单带图灵机。
deterministic one-tape Turing machine.
-/
structure DTM (Q : Type u) (Γ : Type v) where
  start : Q
  accept : Q
  reject : Q
  blank : Γ
  step : Q -> Γ -> Instruction Q Γ

namespace DTM

variable {Q : Type u} {Γ : Type v}

/-- 是否停机态（接受或拒绝）。halting-state test (accept or reject). -/
def isHaltingState (M : DTM Q Γ) [DecidableEq Q] (q : Q) : Bool :=
  decide (q = M.accept ∨ q = M.reject)

/-- 确定性一步执行。one deterministic step. -/
def next (M : DTM Q Γ) [DecidableEq Q] (c : Config Q Γ) : Config Q Γ :=
  if M.isHaltingState c.state then
    c
  else
    let ins := M.step c.state (Tape.read c.tape)
    { state := ins.nextState
      tape := Tape.move M.blank ins.moveDir (Tape.write c.tape ins.writeSym) }

/-- 输入对应的初始配置。initial configuration from input. -/
def initConfig (M : DTM Q Γ) (input : List Γ) : Config Q Γ :=
  { state := M.start
    tape := Tape.ofInput M.blank input }

/-- 执行固定步数。run for a fixed number of steps. -/
def runSteps (M : DTM Q Γ) [DecidableEq Q] : Nat -> Config Q Γ -> Config Q Γ
  | 0, c => c
  | n + 1, c => M.runSteps n (M.next c)

/-- 对输入执行给定步数。evaluate input for `steps` steps. -/
def eval (M : DTM Q Γ) [DecidableEq Q] (input : List Γ) (steps : Nat) : Config Q Γ :=
  M.runSteps steps (M.initConfig input)

/-- 是否在给定步数后处于接受态。accept at the given step bound. -/
def acceptsIn (M : DTM Q Γ) [DecidableEq Q] (input : List Γ) (steps : Nat) : Prop :=
  (M.eval input steps).state = M.accept

/-- 是否在给定步数后处于拒绝态。reject at the given step bound. -/
def rejectsIn (M : DTM Q Γ) [DecidableEq Q] (input : List Γ) (steps : Nat) : Prop :=
  (M.eval input steps).state = M.reject

/-- 是否在某个有限步内接受。accepts in some finite number of steps. -/
def accepts (M : DTM Q Γ) [DecidableEq Q] (input : List Γ) : Prop :=
  ∃ steps, M.acceptsIn input steps

/-- 机器识别语言。recognized language. -/
def language (M : DTM Q Γ) [DecidableEq Q] : Set (List Γ) :=
  { w | M.accepts w }

end DTM

/--
非确定性单带图灵机。
nondeterministic one-tape Turing machine.
-/
structure NTM (Q : Type u) (Γ : Type v) where
  start : Q
  accept : Q
  reject : Q
  blank : Γ
  step : Q -> Γ -> List (Instruction Q Γ)

namespace NTM

variable {Q : Type u} {Γ : Type v}

/-- 是否停机态（接受或拒绝）。halting-state test (accept or reject). -/
def isHaltingState (M : NTM Q Γ) [DecidableEq Q] (q : Q) : Bool :=
  decide (q = M.accept ∨ q = M.reject)

/-- 对单个配置应用一条转移指令。apply one instruction to one configuration. -/
def applyInstruction (M : NTM Q Γ) (c : Config Q Γ)
    (ins : Instruction Q Γ) : Config Q Γ :=
  { state := ins.nextState
    tape := Tape.move M.blank ins.moveDir (Tape.write c.tape ins.writeSym) }

/-- 一步展开全部非确定性后继。one-step expansion of all nondeterministic successors. -/
def nextConfigs (M : NTM Q Γ) [DecidableEq Q] (c : Config Q Γ) : List (Config Q Γ) :=
  if M.isHaltingState c.state then
    [c]
  else
    (M.step c.state (Tape.read c.tape)).map (fun ins => M.applyInstruction c ins)

/-- 输入对应的初始配置。initial configuration from input. -/
def initConfig (M : NTM Q Γ) (input : List Γ) : Config Q Γ :=
  { state := M.start
    tape := Tape.ofInput M.blank input }

/-- 展平配置列表的列表。flatten a list of configuration lists. -/
def flattenConfigs (xss : List (List (Config Q Γ))) : List (Config Q Γ) :=
  xss.foldr List.append []

/--
对配置前沿执行固定步数（层式展开）。
run a fixed number of steps over a configuration frontier (layered expansion).
-/
def runSteps (M : NTM Q Γ) [DecidableEq Q] : Nat -> List (Config Q Γ) -> List (Config Q Γ)
  | 0, cs => cs
  | n + 1, cs => M.runSteps n (flattenConfigs (cs.map (fun c => M.nextConfigs c)))

/-- 对输入执行给定步数。evaluate input for `steps` steps. -/
def eval (M : NTM Q Γ) [DecidableEq Q] (input : List Γ) (steps : Nat) : List (Config Q Γ) :=
  M.runSteps steps [M.initConfig input]

/-- 是否存在分支在给定步数后接受。some branch accepts at the given step bound. -/
def acceptsIn (M : NTM Q Γ) [DecidableEq Q] (input : List Γ) (steps : Nat) : Prop :=
  ∃ c ∈ M.eval input steps, c.state = M.accept

/-- 是否存在某个有限步数使某分支接受。some branch accepts in finite steps. -/
def accepts (M : NTM Q Γ) [DecidableEq Q] (input : List Γ) : Prop :=
  ∃ steps, M.acceptsIn input steps

/-- 机器识别语言。recognized language. -/
def language (M : NTM Q Γ) [DecidableEq Q] : Set (List Γ) :=
  { w | M.accepts w }

end NTM

namespace DTM

variable {Q : Type u} {Γ : Type v}

/--
把 DTM 视为每步只有一个分支的 NTM。
view a DTM as an NTM with singleton branching.
-/
def toNTM (M : DTM Q Γ) : NTM Q Γ where
  start := M.start
  accept := M.accept
  reject := M.reject
  blank := M.blank
  step q a := [M.step q a]

end DTM

namespace NTM

variable {Q : Type u} {Γ : Type v}

/--
将 NTM 转换为 DTM 的标准构造。
canonical construction of DTM from NTM.
-/
def frontierStep (M : NTM Q Γ) [DecidableEq Q]
    (cs : List (Config Q Γ)) : List (Config Q Γ) :=
  flattenConfigs (cs.map (fun c => M.nextConfigs c))

/--
固定输入下的前沿确定化构造。
determinize an NTM by storing the whole frontier in DTM state for a fixed input.

该 DTM 使用 `Unit` 作为哑 tape 字母表；空前沿 `[]` 作为停机汇点。
the DTM uses `Unit` as a dummy tape alphabet; empty frontier `[]` is the halting sink.
-/
def toDTM (M : NTM Q Γ) [DecidableEq Q] (input : List Γ) :
    DTM (List (Config Q Γ)) Unit where
  start := [M.initConfig input]
  accept := []
  reject := []
  blank := ()
  step cs _ :=
    { nextState := M.frontierStep cs
      writeSym := ()
      moveDir := .stay }

/-- 前沿接受判定：存在某配置处于接受态。frontier accepts iff some configuration is accepting. -/
def frontierAccepts (M : NTM Q Γ) (cs : List (Config Q Γ)) : Prop :=
  ∃ c ∈ cs, c.state = M.accept

@[simp] theorem frontierStep_nil (M : NTM Q Γ) [DecidableEq Q] :
    M.frontierStep [] = [] := by
  simp [frontierStep, flattenConfigs]

@[simp] theorem runSteps_one_eq_frontierStep (M : NTM Q Γ) [DecidableEq Q]
    (cs : List (Config Q Γ)) :
    M.runSteps 1 cs = M.frontierStep cs := by
  simp [runSteps, frontierStep]

@[simp] theorem toDTM_next_state (M : NTM Q Γ) [DecidableEq Q] [DecidableEq Γ]
    (input : List Γ) (c : Config (List (Config Q Γ)) Unit) :
    ((M.toDTM input).next c).state = M.frontierStep c.state := by
  by_cases h : c.state = []
  · simp [DTM.next, DTM.isHaltingState, toDTM, frontierStep, flattenConfigs, h]
  · simp [DTM.next, DTM.isHaltingState, toDTM, frontierStep, h]

theorem toDTM_runSteps_state (M : NTM Q Γ) [DecidableEq Q] [DecidableEq Γ]
    (input : List Γ) (steps : Nat) (c : Config (List (Config Q Γ)) Unit) :
    ((M.toDTM input).runSteps steps c).state = M.runSteps steps c.state := by
  induction steps generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      simpa [DTM.runSteps, runSteps, frontierStep, toDTM_next_state] using
        ih ((M.toDTM input).next c)

theorem toDTM_eval_state (M : NTM Q Γ) [DecidableEq Q] [DecidableEq Γ]
    (input : List Γ) (dummyInput : List Unit) (steps : Nat) :
    ((M.toDTM input).eval dummyInput steps).state = M.eval input steps := by
  simpa [DTM.eval, NTM.eval, DTM.initConfig, NTM.initConfig] using
    (toDTM_runSteps_state (M := M) (input := input) (steps := steps)
      (c := (M.toDTM input).initConfig dummyInput))

theorem acceptsIn_iff_toDTM_frontierAccepts (M : NTM Q Γ)
    [DecidableEq Q] [DecidableEq Γ] (input : List Γ) (steps : Nat) :
    M.acceptsIn input steps ↔ M.frontierAccepts ((M.toDTM input).eval [] steps).state := by
  unfold acceptsIn frontierAccepts
  simp [toDTM_eval_state (M := M) (input := input) (dummyInput := []) (steps := steps)]

theorem accepts_iff_exists_toDTM_frontierAccepts (M : NTM Q Γ)
    [DecidableEq Q] [DecidableEq Γ] (input : List Γ) :
    M.accepts input ↔ ∃ steps, M.frontierAccepts ((M.toDTM input).eval [] steps).state := by
  constructor
  · intro h
    rcases h with ⟨steps, hsteps⟩
    exact ⟨steps, (acceptsIn_iff_toDTM_frontierAccepts
      (M := M) (input := input) (steps := steps)).1 hsteps⟩
  · intro h
    rcases h with ⟨steps, hsteps⟩
    exact ⟨steps, (acceptsIn_iff_toDTM_frontierAccepts
      (M := M) (input := input) (steps := steps)).2 hsteps⟩

end NTM

end TuringMachine
