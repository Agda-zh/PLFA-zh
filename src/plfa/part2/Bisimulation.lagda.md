---
title      : "Bisimulation: 联系不同的规约系统"
permalink  : /Bisimulation/
translators: ["Fangyi Zhou"]
progress   : 60
---

```agda
module plfa.part2.Bisimulation where
```

<!--
Some constructs can be defined in terms of other constructs.  In the
previous chapter, we saw how _let_ terms can be rewritten as an
application of an abstraction, and how two alternative formulations of
products — one with projections and one with case — can be formulated
in terms of each other.  In this chapter, we look at how to formalise
such claims.
-->

有一些构造可以用其他的构造来定义。
在上一章中，我们展示了 _let_ 项可以被重写为抽象的应用，以及积的两种不同表示方法 ——
一种使用投影，一种使用匹配表达式。
本章中，我们来看看如何形式化这些断言。

<!--
Given two different systems, with different terms and reduction rules,
we define what it means to claim that one _simulates_ the other.
Let's call our two systems _source_ and _target_.  Let `M`, `N` range
over terms of the source, and `M†`, `N†` range over terms of the
target.  We define a relation
-->

给定两个不同的系统，它们有不同的项和不同的规约规则，我们定义诸如
『一个系统**模拟（Simulate）**了另一个系统』此类断言的意义。
假设两个系统分别叫做**源**（Source）和**目标**（Target），我们用
`M` 和 `N` 表示源系统的项，`M†` 和 `N†` 表示目标系统的项。
我们定义一个关系

    M ~ M†

<!--
between corresponding terms of the two systems. We have a
_simulation_ of the source by the target if every reduction
in the source has a corresponding reduction sequence
in the target:
-->

于两个系统对应的项之上。
如果每个源系统的每一个规约都有一个对应的规约序列，那我们就有了一个**模拟**。

<!--
_Simulation_: For every `M`, `M†`, and `N`:
If `M ~ M†` and `M —→ N`
then `M† —↠ N†` and `N ~ N†`
for some `N†`.
-->

**模拟**：对于任意的 `M`、`M†` 和 `N`，
如果 `M ~ M†` 和 `M —→ N` 成立，那么 `M† —↠ N†` 和 `N ~ N†` 对于一些 `N†` 成立。

<!--
Or, in a diagram:
-->

或者，用图表来表示：

    M  --- —→ --- N
    |             |
    |             |
    ~             ~
    |             |
    |             |
    M† --- —↠ --- N†

<!--
Sometimes we will have a stronger condition, where each reduction in the source
corresponds to a reduction (rather than a reduction sequence)
in the target:
-->

有时我们会使用一个更强的条件，使得每个源系统的规约对应目标系统的规约（而不是规约序列）：

    M  --- —→ --- N
    |             |
    |             |
    ~             ~
    |             |
    |             |
    M† --- —→ --- N†

<!--
This stronger condition is known as _lock-step_ or _on the nose_ simulation.
-->

这个更强的条件被称为**锁步**（Lock-step）或者**准确无误**（On the nose）的模拟。

『译注：[On the nose][on-the-nose] 本义为在鼻子之上，用于表述准确无误。』

<!--
We are particularly interested in the situation where there is also
a simulation from the target to the source: every reduction in the
target has a corresponding reduction sequence in the source.  This
situation is called a _bisimulation_.
-->

如果从目标系统到源系统也有一个模拟：即每个目标系统的规约在源目标系统中有对应的规约序列，
我们对这样的情况尤其感兴趣。
这样的情况被称为**双模拟**（Bisimulation）。

<!--
Simulation is established by case analysis over all possible
reductions and all possible terms to which they are related.  For each
reduction step in the source we must show a corresponding reduction
sequence in the target.
-->

要建立模拟，我们需要分情况讨论所有的可能规约，以及所有它们可能联系的项。
对于每个源系统中规约的步骤，我们必须给出目标系统中对应的规约系列。

<!--
For instance, the source might be lambda calculus with _let_
added, and the target the same system with `let` translated out.
The key rule defining our relation will be:
-->

譬如说，源系统可以是带 _let_ 项的 λ 演算，而目标系统中的 `let` 被翻译了。
定义这个关系的关键规则是：

    M ~ M†
    N ~ N†
    --------------------------------
    let x = M in N ~ (ƛ x ⇒ N†) · M†

<!--
All the other rules are congruences: variables relate to
themselves, and abstractions and applications relate if their
components relate:
-->

其他的规则都是合同性的规则：变量于它们自身相关，抽象与应用在它们的组成部分分别相关时相关：

    -----
    x ~ x

    N ~ N†
    ------------------
    ƛ x ⇒ N ~ ƛ x ⇒ N†

    L ~ L†
    M ~ M†
    ---------------
    L · M ~ L† · M†

<!--
Covering the other constructs of our language — naturals,
fixpoints, products, and so on — would add little save length.
-->

讨论语言中的其他构造——自然数、不动点和积等——对我们本章的重点意义不大，
我们节约长度而不讨论。

<!--
In this case, our relation can be specified by a function
from source to target:
-->

在此情况下，关系的定义可以用一个从源至目标的函数来制定：

    (x) †               =  x
    (ƛ x ⇒ N) †         =  ƛ x ⇒ (N †)
    (L · M) †           =  (L †) · (M †)
    (let x = M in N) †  =  (ƛ x ⇒ (N †)) · (M †)

<!--
And we have
-->

我们有：

    M † ≡ N
    -------
    M ~ N

<!--
and conversely. But in general we may have a relation without any
corresponding function.
-->

以及其逆命题。
但一般情况下，我们可能有一个关系而不一定有对应的函数。

<!--
This chapter formalises establishing that `~` as defined
above is a simulation from source to target.  We leave
establishing it in the reverse direction as an exercise.
Another exercise is to show the alternative formulations
of products in
Chapter [More](/More/)
are in bisimulation.
-->

本章形式化上文中定义的 `~` 关系是一个从源系统至目标系统的模拟。
我们将反向的证明留作习题。
另一个习题是证明 [More](/More/) 章节中积的替代表示方法形成了一个双模拟。

<!--
## Imports
-->

## 导入

<!--
We import our source language from
Chapter [More](/More/):
-->

我们从 [More](/More/) 章节中导入源语言：

```agda
open import plfa.part2.More
```


<!--
## Simulation
-->

## 模拟

<!--
The simulation is a straightforward formalisation of the rules
in the introduction:
-->

我们直接地形式化导言中的模拟：

```agda
infix  4 _~_
infix  5 ~ƛ_
infix  7 _~·_

data _~_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ~` : ∀ {Γ A} {x : Γ ∋ A}
     ---------
   → ` x ~ ` x

  ~ƛ_ : ∀ {Γ A B} {N N† : Γ , A ⊢ B}
    → N ~ N†
      ----------
    → ƛ N ~ ƛ N†

  _~·_ : ∀ {Γ A B} {L L† : Γ ⊢ A ⇒ B} {M M† : Γ ⊢ A}
    → L ~ L†
    → M ~ M†
      ---------------
    → L · M ~ L† · M†

  ~let : ∀ {Γ A B} {M M† : Γ ⊢ A} {N N† : Γ , A ⊢ B}
    → M ~ M†
    → N ~ N†
      ----------------------
    → `let M N ~ (ƛ N†) · M†
```
<!--
The language in Chapter [More](/More/) has more constructs, which we could easily add.
However, leaving the simulation small lets us focus on the essence.
It's a handy technical trick that we can have a large source language,
but only bother to include in the simulation the terms of interest.
-->

[More](/More/) 章节中的语言有更多的构造，我们可以简单地扩充上述定义。
但是，使上述的定义小而精简让我们注重本章的重点。
虽然我们有一个较大的源语言，但我们只在模拟中考虑我们感兴趣的项，这是一个方便的小窍门。


<!--
#### Exercise `_†` (practice)
-->

#### Exercise `_†` （实践）

<!--
Formalise the translation from source to target given in the introduction.
Show that `M † ≡ N` implies `M ~ N`, and conversely.
-->

形式化导言中给定的源语言至目标语言的翻译。
证明 `M † ≡ N` 蕴含了 `M ~ N`，以及其逆命题。

<!--
**Hint:** For simplicity, we focus on only a few constructs of the language,
so `_†` should be defined only on relevant terms. One way to do this is
to use a decidable predicate to pick out terms in the domain of `_†`, using
[proof by reflection](/Decidable/#proof-by-reflection).
-->
**提示：**为了简洁，我们只注重语言中的一小部分构造，所以 `_†` 的定义只需要注重相关的部分。
达成此目的的一种方法是用[互映证明](/Decidable/#proof-by-reflection)定义一个谓词来选出
 `_†` 定义域中的项。

```agda
-- 在这里写出你的代码。
```


<!--
## Simulation commutes with values
-->

## 模拟与值可交换

<!--
We need a number of technical results. The first is that simulation
commutes with values.  That is, if `M ~ M†` and `M` is a value then
`M†` is also a value:
-->

我们需要一系列技术结果。首先是模拟与值可交换（Commute）。
即：若 `M ~ M†` 且 `M` 是一个值，那么 `M†` 也是一个值。

```agda
~val : ∀ {Γ A} {M M† : Γ ⊢ A}
  → M ~ M†
  → Value M
    --------
  → Value M†
~val ~`           ()
~val (~ƛ ~N)      V-ƛ  =  V-ƛ
~val (~L ~· ~M)   ()
~val (~let ~M ~N) ()
```
<!--
It is a straightforward case analysis, where here the only value
of interest is a lambda abstraction.
-->

这是一个直接的分情况讨论，唯一有意思的情况是 λ 抽象。

<!--
#### Exercise `~val⁻¹` (practice)
-->

#### Exercise `~val⁻¹` （实践）

<!--
Show that this also holds in the reverse direction: if `M ~ M†`
and `Value M†` then `Value M`.
-->

证明此命题在反方向亦成立：
若 `M ~ M†` 且 `Value M†`，那么 `Value M` 成立。

```agda
-- 在这里写出你的代码。
```

<!--
## Simulation commutes with renaming
-->

## 模拟与重命名可交换

<!--
The next technical result is that simulation commutes with renaming.
That is, if `ρ` maps any judgment `Γ ∋ A` to a judgment `Δ ∋ A`,
and if `M ~ M†` then `rename ρ M ~ rename ρ M†`:
-->

下一个技术结果是模拟和重命名可交换。
即：若 `ρ` 将任意的判断 `Γ ∋ A` 映射至另一个判断 `Δ ∋ A`，且
`M ~ M†`，那么 `rename ρ M ~ rename ρ M†`：

```agda
~rename : ∀ {Γ Δ}
  → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
    ----------------------------------------------------------
  → (∀ {A} {M M† : Γ ⊢ A} → M ~ M† → rename ρ M ~ rename ρ M†)
~rename ρ (~`)          =  ~`
~rename ρ (~ƛ ~N)       =  ~ƛ (~rename (ext ρ) ~N)
~rename ρ (~L ~· ~M)    =  (~rename ρ ~L) ~· (~rename ρ ~M)
~rename ρ (~let ~M ~N)  =  ~let (~rename ρ ~M) (~rename (ext ρ) ~N)
```
<!--
The structure of the proof is similar to the structure of renaming itself:
reconstruct each term with recursive invocation, extending the environment
where appropriate (in this case, only for the body of an abstraction).
-->

此证明的结构与重命名的结构相似：
使用递归来重新构造每一个项，并在需要时扩充上下文（在这里，我们只需要在 λ 抽象的抽象体中使用）。


<!--
## Simulation commutes with substitution
-->

## 模拟与替换可交换

<!--
The third technical result is that simulation commutes with substitution.
It is more complex than renaming, because where we had one renaming map
`ρ` here we need two substitution maps, `σ` and `σ†`.
-->

第三个技术结果是模拟与替换可交换。
这个结果比重命名更复杂，因为我们之前只有一个重命名映射 `ρ`，
而现在我们需要两个替换映射 `σ` 和 `σ†`。

<!--
The proof first requires we establish an analogue of extension.
If `σ` and `σ†` both map any judgment `Γ ∋ A` to a judgment `Δ ⊢ A`,
such that for every `x` in `Γ ∋ A` we have `σ x ~ σ† x`,
then for any `x` in `Γ , B ∋ A` we have `exts σ x ~ exts σ† x`:
-->

这个证明首先需要我们构造一个类似于扩充的概念。
如果 `σ` 和 `σ†` 都将任何判断 `Γ ∋ A` 映射至一个判断 `Δ ⊢ A`，
且对于 `Γ ∋ A` 中的任意 `x`，我们有 `σ x ~ σ† x`，
那么对于任何 `Γ , B ∋ A` 中的 `x`，我们有 `exts σ x ~ exts σ† x`：

```agda
~exts : ∀ {Γ Δ}
  → {σ  : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → {σ† : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → (∀ {A} → (x : Γ ∋ A) → σ x ~ σ† x)
    --------------------------------------------------
  → (∀ {A B} → (x : Γ , B ∋ A) → exts σ x ~ exts σ† x)
~exts ~σ Z      =  ~`
~exts ~σ (S x)  =  ~rename S_ (~σ x)
```
<!--
The structure of the proof is similar to the structure of extension itself.
The newly introduced variable trivially relates to itself, and otherwise
we apply renaming to the hypothesis.
-->

这个证明的结构于扩充的结构相似。
新加入的变量平凡地与它自身相关，否则我们可以对假设使用重命名。

<!--
With extension under our belts, it is straightforward to show
substitution commutes.  If `σ` and `σ†` both map any judgment `Γ ∋ A`
to a judgment `Δ ⊢ A`, such that for every `x` in `Γ ∋ A` we have `σ
x ~ σ† x`, and if `M ~ M†`, then `subst σ M ~ subst σ† M†`:
-->

如上定义完扩充之后，证明替换与模拟交换就很直接了。
如果 `σ` 和 `σ†` 都将任何判断 `Γ ∋ A` 映射至一个判断 `Δ ⊢ A`，
且对于 `Γ ∋ A` 中的任意 `x`，我们有 `σ x ~ σ† x`，
如果 `M ~ M†`，那么 `subst σ M ~ subst σ† M†`：

```agda
~subst : ∀ {Γ Δ}
  → {σ  : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → {σ† : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → (∀ {A} → (x : Γ ∋ A) → σ x ~ σ† x)
    ---------------------------------------------------------
  → (∀ {A} {M M† : Γ ⊢ A} → M ~ M† → subst σ M ~ subst σ† M†)
~subst ~σ (~` {x = x})  =  ~σ x
~subst ~σ (~ƛ ~N)       =  ~ƛ (~subst (~exts ~σ) ~N)
~subst ~σ (~L ~· ~M)    =  (~subst ~σ ~L) ~· (~subst ~σ ~M)
~subst ~σ (~let ~M ~N)  =  ~let (~subst ~σ ~M) (~subst (~exts ~σ) ~N)
```
<!--
Again, the structure of the proof is similar to the structure of
substitution itself: reconstruct each term with recursive invocation,
extending the environment where appropriate (in this case, only for
the body of an abstraction).
-->

与之前一样，这个证明的结构于替换的结构类似：使用递归重新构造每一个项，
并在需要时扩充上下文（在这里，我们只需要在 λ 抽象的抽象体中使用）。

<!--
From the general case of substitution, it is also easy to derive
the required special case.  If `N ~ N†` and `M ~ M†`, then
`N [ M ] ~ N† [ M† ]`:
-->

从上面的替换的广义定义，我们可以简单地推导出我们所需的特殊形式：
如果 `N ~ N†` 和 `M ∼ M†`，那么 `N [ M ] ~ N† [ M† ]`：

```agda
~sub : ∀ {Γ A B} {N N† : Γ , B ⊢ A} {M M† : Γ ⊢ B}
  → N ~ N†
  → M ~ M†
    -----------------------
  → (N [ M ]) ~ (N† [ M† ])
~sub {Γ} {A} {B} ~N ~M = ~subst {Γ , B} {Γ} ~σ {A} ~N
  where
  ~σ : ∀ {A} → (x : Γ , B ∋ A) → _ ~ _
  ~σ Z      =  ~M
  ~σ (S x)  =  ~`
```

<!--
Once more, the structure of the proof resembles the original.
-->

再一次，这个证明与原定义的结构类似。


## The relation is a simulation

Finally, we can show that the relation actually is a simulation.
In fact, we will show the stronger condition of a lock-step simulation.
What we wish to show is:

_Lock-step simulation_: For every `M`, `M†`, and `N`:
If `M ~ M†` and `M —→ N`
then `M† —→ N†` and `N ~ N†`
for some `N†`.

Or, in a diagram:

    M  --- —→ --- N
    |             |
    |             |
    ~             ~
    |             |
    |             |
    M† --- —→ --- N†

We first formulate a concept corresponding to the lower leg
of the diagram, that is, its right and bottom edges:
```agda
data Leg {Γ A} (M† N : Γ ⊢ A) : Set where

  leg : ∀ {N† : Γ ⊢ A}
    → N ~ N†
    → M† —→ N†
      --------
    → Leg M† N
```
For our formalisation, in this case, we can use a stronger
relation than `—↠`, replacing it by `—→`.

We can now state and prove that the relation is a simulation.
Again, in this case, we can use a stronger relation than
`—↠`, replacing it by `—→`:
```agda
sim : ∀ {Γ A} {M M† N : Γ ⊢ A}
  → M ~ M†
  → M —→ N
    ---------
  → Leg  M† N
sim ~`              ()
sim (~ƛ ~N)         ()
sim (~L ~· ~M)      (ξ-·₁ L—→)
  with sim ~L L—→
...  | leg ~L′ L†—→                 =  leg (~L′ ~· ~M)   (ξ-·₁ L†—→)
sim (~V ~· ~M)      (ξ-·₂ VV M—→)
  with sim ~M M—→
...  | leg ~M′ M†—→                 =  leg (~V ~· ~M′)   (ξ-·₂ (~val ~V VV) M†—→)
sim ((~ƛ ~N) ~· ~V) (β-ƛ VV)        =  leg (~sub ~N ~V)  (β-ƛ (~val ~V VV))
sim (~let ~M ~N)    (ξ-let M—→)
  with sim ~M M—→
...  | leg ~M′ M†—→                 =  leg (~let ~M′ ~N) (ξ-·₂ V-ƛ M†—→)
sim (~let ~V ~N)    (β-let VV)      =  leg (~sub ~N ~V)  (β-ƛ (~val ~V VV))
```
The proof is by case analysis, examining each possible instance of `M ~ M†`
and each possible instance of `M —→ M†`, using recursive invocation whenever
the reduction is by a `ξ` rule, and hence contains another reduction.
In its structure, it looks a little bit like a proof of progress:

* If the related terms are variables, no reduction applies.
* If the related terms are abstractions, no reduction applies.
* If the related terms are applications, there are three subcases:
  - The source term reduces via `ξ-·₁`, in which case the target term does as well.
    Recursive invocation gives us

        L  --- —→ ---  L′
        |              |
        |              |
        ~              ~
        |              |
        |              |
        L† --- —→ --- L′†

    from which follows:

         L · M  --- —→ ---  L′ · M
           |                   |
           |                   |
           ~                   ~
           |                   |
           |                   |
        L† · M† --- —→ --- L′† · M†

  - The source term reduces via `ξ-·₂`, in which case the target term does as well.
    Recursive invocation gives us

        M  --- —→ ---  M′
        |              |
        |              |
        ~              ~
        |              |
        |              |
        M† --- —→ --- M′†

    from which follows:

         V · M  --- —→ ---  V · M′
           |                  |
           |                  |
           ~                  ~
           |                  |
           |                  |
        V† · M† --- —→ --- V† · M′†

    Since simulation commutes with values and `V` is a value, `V†` is also a value.

  - The source term reduces via `β-ƛ`, in which case the target term does as well:

         (ƛ x ⇒ N) · V  --- —→ ---  N [ x := V ]
              |                           |
              |                           |
              ~                           ~
              |                           |
              |                           |
        (ƛ x ⇒ N†) · V† --- —→ --- N† [ x :=  V† ]

    Since simulation commutes with values and `V` is a value, `V†` is also a value.
    Since simulation commutes with substitution and `N ~ N†` and `V ~ V†`,
    we have `N [ x := V ] ~ N† [ x := V† ]`.

* If the related terms are a let and an application of an abstraction,
  there are two subcases:

  - The source term reduces via `ξ-let`, in which case the target term
    reduces via `ξ-·₂`.  Recursive invocation gives us

        M  --- —→ ---  M′
        |              |
        |              |
        ~              ~
        |              |
        |              |
        M† --- —→ --- M′†

    from which follows:

        let x = M in N --- —→ --- let x = M′ in N
              |                         |
              |                         |
              ~                         ~
              |                         |
              |                         |
        (ƛ x ⇒ N) · M  --- —→ --- (ƛ x ⇒ N) · M′

  - The source term reduces via `β-let`, in which case the target
    term reduces via `β-ƛ`:

        let x = V in N  --- —→ ---  N [ x := V ]
              |                         |
              |                         |
              ~                         ~
              |                         |
              |                         |
        (ƛ x ⇒ N†) · V† --- —→ --- N† [ x := V† ]

    Since simulation commutes with values and `V` is a value, `V†` is also a value.
    Since simulation commutes with substitution and `N ~ N†` and `V ~ V†`,
    we have `N [ x := V ] ~ N† [ x := V† ]`.


#### Exercise `sim⁻¹` (practice)

Show that we also have a simulation in the other direction, and hence that we have
a bisimulation.

```agda
-- Your code goes here
```

#### Exercise `products` (practice)

Show that the two formulations of products in
Chapter [More](/More/)
are in bisimulation.  The only constructs you need to include are
variables, and those connected to functions and products.
In this case, the simulation is _not_ lock-step.

```agda
-- Your code goes here
```

## Unicode

This chapter uses the following unicode:

    †  U+2020  DAGGER (\dag)
    ⁻  U+207B  SUPERSCRIPT MINUS (\^-)
    ¹  U+00B9  SUPERSCRIPT ONE (\^1)

[on-the-nose]: https://dictionary.cambridge.org/dictionary/english-chinese-simplified/on-the-nose