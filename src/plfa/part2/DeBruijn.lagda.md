---
title      : "DeBruijn: 内在类型的 de Bruijn 表示法"
permalink  : /DeBruijn/
translators: ["Fangyi Zhou"]
---

```agda
module plfa.part2.DeBruijn where
```

<!--
The previous two chapters introduced lambda calculus, with a
formalisation based on named variables, and terms defined
separately from types.  We began with that approach because it
is traditional, but it is not the one we recommend.  This
chapter presents an alternative approach, where named
variables are replaced by de Bruijn indices and terms are
indexed by their types.  Our new presentation is more compact, using
substantially fewer lines of code to cover the same ground.
-->

前面两个章节介绍了 λ-演算，用以带名字的变量进行形式化，而且将项与类型分开定义。
我们之所以使用这样的方法，是因为这是传统的定义方法，但不是我们推荐的方法。
在本节中，我们使用另一种方法，用 de Bruijn 因子来代替带名字的变量，并且用项的类型来索引项。
这种新的表示法更加紧凑，可以使用更少的代码来证明相同的内容。

<!--
There are two fundamental approaches to typed lambda calculi.
One approach, followed in the last two chapters,
is to first define terms and then define types.
Terms exist independent of types, and may have types assigned to them
by separate typing rules.
Another approach, followed in this chapter,
is to first define types and then define terms.
Terms and type rules are intertwined, and it makes no sense to talk
of a term without a type.
The two approaches are sometimes called _Curry style_ and _Church style_.
Following Reynolds, we will refer to them as _extrinsic_ and _intrinsic_.
-->

表示带类型的 λ-演算有两种基本的方法。
其一是我们在前两章中使用的方法，先定义项，再定义类型。
项独立于类型存在，其类型由另外的赋型规则指派。
其二是我们在本章中使用的方法，先定义类型，再定义项。
项和类型的规则相互环绕，并且讨论不带类型的项将没有意义。
这两种方法有的时候被称为**柯里法（Curry Style）**和**邱奇法（Church Style）**。
沿用 Reynolds 的叫法，我们把两种方法称为**外在法（Extrinsic）**和**内在法（Intrinsic）**。

<!--
The particular representation described here
was first proposed by
Thorsten Altenkirch and Bernhard Reus.
The formalisation of renaming and substitution
we use is due to Conor McBride.
Related work has been carried out by
James Chapman, James McKinna, and many others.
-->

我们在这里使用的这种表示法最先由 Thorsten Altenkirch 和 Bernhard Reus 提出。
使用的将重命名和替换形式化的方法由 Conor McBride 提出。
James Chapman、James McKinna 和许多其他人也进行了相关的研究。

<!--
## Imports
-->

## 导入

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)
```

<!--
## Introduction
-->

## 简介

<!--
There is a close correspondence between the structure of a
term and the structure of the derivation showing that it is
well typed.  For example, here is the term for the Church
numeral two:
-->

项的结构和其良类型的推导的结构联系很紧密。例如，这里是 Church 法表示的二：

    twoᶜ : Term
    twoᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

<!--
And here is its corresponding type derivation:
-->

这里是它对应的赋型推导：

    ⊢twoᶜ : ∀ {A} → ∅ ⊢ twoᶜ ⦂ Ch A
    ⊢twoᶜ = ⊢ƛ (⊢ƛ (⊢` ∋s · (⊢` ∋s · ⊢` ∋z)))
      where
      ∋s = S′ Z
      ∋z = Z

<!--
(These are both taken from Chapter
[Lambda](/Lambda/)
and you can see the corresponding derivation tree written out
in full
[here](/Lambda/#derivation).)
The two definitions are in close correspondence, where:
-->

（两者都摘自 [Lambda](/Lambda/) 章节，你可以在[这里](/Lambda/#derivation)查看完整的推导树。）
两者的定义对应的很紧密，其中：

<!--
  * `` `_ `` corresponds to `` ⊢` ``
  * `ƛ_⇒_`   corresponds to `⊢ƛ`
  * `_·_`    corresponds to `_·_`
-->

  * `` `_ `` 对应了 `` ⊢` ``
  * `ƛ_⇒_`   对应了 `⊢ƛ`
  * `_·_`    对应了 `_·_`

<!--
Further, if we think of `Z` as zero and `S` as successor, then
the lookup derivation for each variable corresponds to a
number which tells us how many enclosing binding terms to
count to find the binding of that variable.  Here `"z"`
corresponds to `Z` or zero and `"s"` corresponds to `S Z` or
one.  And, indeed, `"z"` is bound by the inner abstraction
(count outward past zero abstractions) and `"s"` is bound by the
outer abstraction (count outward past one abstraction).
-->

此外，如果我们将 `Z` 看作零，将 `S` 看做后继，那么每个变量的查询推导对应了
一个自然数：它告诉我们到达此变量的约束之前，经过了多少约束项。
这里的 `"z"` 对应了 `Z` 或者零，`"s"` 对应了 `S Z` 或者一。
的确，`"z"` 被里面的抽象约束（向外跨过 0 个抽象），
`"s"` 被外面的抽象约束（向外跨过 1 个抽象）。

<!--
In this chapter, we are going to exploit this correspondence,
and introduce a new notation for terms that simultaneously
represents the term and its type derivation.  Now we will
write the following:
-->

本章中，我们利用这个对应特性，引入一种新的项的记法，其同时表示了项以及它的类型推导。
现在，我们写出如下：


    twoᶜ  :  ∅ ⊢ Ch `ℕ
    twoᶜ  =  ƛ ƛ (# 1 · (# 1 · # 0))

<!--
A variable is represented by a natural number (written with
`Z` and `S`, and abbreviated in the usual way), and tells us
how many enclosing binding terms to count to find the binding
of that variable. Thus, `# 0` is bound at the inner `ƛ`, and
`# 1` at the outer `ƛ`.
-->

变量由一个自然数表示（用 `Z` 和 `S` 表示，简写为常见形式），它告诉我们
这个变量的约束在多少个约束之外。因此，`# 0` 由里面的 `ƛ` 约束，`# 1`
由外面的 `ƛ` 约束。

<!--
Replacing variables by numbers in this way is called _de
Bruijn representation_, and the numbers themselves are called
_de Bruijn indices_, after the Dutch mathematician Nicolaas
Govert (Dick) de Bruijn (1918—2012), a pioneer in the creation
of proof assistants.  One advantage of replacing named
variables with de Bruijn indices is that each term now has a
unique representation, rather than being represented by the
equivalence class of terms under alpha renaming.
-->

用数字代替变量的这种表示方法叫做 **de Bruijn 表示法**，这些数字本身被称为
**de Bruijn 因子（de Bruijn Indices）**，得名于荷兰数学家
Nicolaas Govert (Dick) de Bruijn （1918 - 2012），一位创造证明助理的先锋。
使用 de Bruijn 因子表示变量的一个好处是：每个项有一个唯一的表示方法，而不是
在 α-重命名下的一个相等类。

<!--
The other important feature of our chosen representation is
that it is _intrinsically typed_.  In the previous two chapters,
the definition of terms and the definition of types are
completely separate.  All terms have type `Term`, and nothing
in Agda prevents one from writing a nonsense term such as
`` `zero · `suc `zero `` which has no type.  Such terms that
exist independent of types are sometimes called _preterms_ or
_raw terms_.  Here we are going to replace the type `Term` of
raw terms by the type `Γ ⊢ A` of intrinsically-typed terms
which in context `Γ` have type `A`.
-->

我们选择的表示方式的另一个重要特性是：他是**内在类型（Intrinsically Typed）**的。
在前两章中，项和类型的定义是完全分离的。所有的项拥有 `Term` 类型，Agda 并不会
阻止我们写出例如 `` `zero · `suc `zero `` 的没有类型的无意义的项。
这样独立于类型存在的项有时被称为**原项（Preterms）**或者**源项（Raw Terms）**。
我们将用 `Γ ⊢ A` 类型的内在类型的项，表示它在 `Γ` 语境中拥有类型 `A`，
来取代 `Term` 类型的源项。

<!--
While these two choices fit well, they are independent.  One
can use de Bruijn indices in raw terms, or
have intrinsically-typed terms with names.  In
Chapter [Untyped](/Untyped/),
we will introduce terms with de Bruijn indices that
are intrinsically scoped but not typed.
-->

尽管这两个选择很适合我们，这两个选择仍然是独立的。
可以用 de Bruijn 因子配合源项，也可以用内在类型的项配合变量名。
在 [Untyped](/Untyped/) 章节中，我们将使用 de Bruijn 表示内在作用域的项，
但不包含类型。

<!--
## A second example
-->

## 第二个例子

<!--
De Bruijn indices can be tricky to get the hang of, so before
proceeding further let's consider a second example.  Here is
the term that adds two naturals:
-->

De Bruijn 因子可能掌握起来有点棘手。在我们继续之前，我们先来考虑第二个例子。
下面是一个将两个自然数相加的一个项：

    plus : Term
    plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
             case ` "m"
               [zero⇒ ` "n"
               |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]

<!--
Note variable `"m"` is bound twice, once in a lambda abstraction
and once in the successor branch of the case.  Any appearance
of `"m"` in the successor branch must refer to the latter
binding, due to shadowing.
-->

注意变量 `"m"` 被约束了两次，一次在 λ 抽象中，另一次在匹配表达式的后继分支中。
由于屏蔽效应，在匹配表达式后继分支出现的 `"m"` 必须指代后面的约束。

<!--
Here is its corresponding type derivation:
-->

下面是它对应的类型推导：

    ⊢plus : ∅ ⊢ plus ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
    ⊢plus = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` ∋m) (⊢` ∋n)
             (⊢suc (⊢` ∋+ · ⊢` ∋m′ · ⊢` ∋n′)))))
      where
      ∋+  = (S′ (S′ (S′ Z)))
      ∋m  = (S′ Z)
      ∋n  = Z
      ∋m′ = Z
      ∋n′ = (S′ Z)

<!--
The two definitions are in close correspondence, where in
addition to the previous correspondences we have:
-->

两者的定义对应的很紧密，除去之前的对应，我们注意到：

<!--
  * `` `zero `` corresponds to `⊢zero`
  * `` `suc_ `` corresponds to `⊢suc`
  * `` case_[zero⇒_|suc_⇒_] `` corresponds to `⊢case`
  * `μ_⇒_` corresponds to `⊢μ`
-->

  * `` `zero `` 对应了 `⊢zero`
  * `` `suc_ `` 对应了 `⊢suc`
  * `` case_[zero⇒_|suc_⇒_] `` 对应了 `⊢case`
  * `μ_⇒_` 对应了 `⊢μ`

<!--
Note the two lookup judgments `∋m` and `∋m′` refer to two
different bindings of variables named `"m"`.  In contrast, the
two judgments `∋n` and `∋n′` both refer to the same binding
of `"n"` but accessed in different contexts, the first where
`"n"` is the last binding in the context, and the second after
`"m"` is bound in the successor branch of the case.
-->

注意到，查询判断 `∋m` 和 `∋m′` 表示了两个名称同为 `"m"` 变量的不同约束。
作为对比， 判断 `∋n` 和 `∋n′` 都表示变量 `"n"` 的约束，但是其语境不同，
前者中 `"n"` 是语境中最后一个约束，后者中则是在匹配表达式后继分支中 `"m"` 约束之后。

<!--
Here is the term and its type derivation in the notation of this chapter:
-->

下面是用本章中的记法表示的这个项极其类型推导：

    plus : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
    plus = μ ƛ ƛ case (# 1) (# 0) (`suc (# 3 · # 0 · # 1))

<!--
Reading from left to right, each de Bruijn index corresponds
to a lookup derivation:
-->

从左往右，每个 de Bruijn 因子对应了一个查询判断：

<!--
  * `# 1` corresponds to `∋m`
  * `# 0` corresponds to `∋n`
  * `# 3` corresponds to `∋+`
  * `# 0` corresponds to `∋m′`
  * `# 1` corresponds to `∋n′`
-->

  * `# 1` 对应了 `∋m`
  * `# 0` 对应了 `∋n`
  * `# 3` 对应了 `∋+`
  * `# 0` 对应了 `∋m′`
  * `# 1` 对应了 `∋n′`

<!--
The de Bruijn index counts the number of `S` constructs in the
corresponding lookup derivation.  Variable `"n"` bound in the
inner abstraction is referred to as `# 0` in the zero branch
of the case but as `# 1` in the successor branch of the case,
because of the intervening binding.  Variable `"m"` bound in the
lambda abstraction is referred to by the first `# 1` in the
code, while variable `"m"` bound in the successor branch of the
case is referred to by the second `# 0`.  There is no
shadowing: with variable names, there is no way to refer to
the former binding in the scope of the latter, but with de
Bruijn indices it could be referred to as `# 2`.
-->

De Bruijn 因子计算了对应查询推断中 `S` 构造子的数量。
里面抽象约束的变量 `"n"` 在匹配表达式零分支中由 `# 0` 表示， 但在后继分支中由
`# 1` 表示，因为中间产生了约束。
抽象约束的变量 `"m"` 第一次出现是由 `# 1` 表示，然而第二次出现在匹配表达式
的后继分支时则由 `# 0` 表示。这里没有屏蔽效应————使用变量名时，我们无法
在后者的作用域内指代外部的约束，但是我们可以用 de Bruijn 因子 `# 2` 来指代。

<!--
## Order of presentation
-->

## 展示的顺序

<!--
In the current chapter, the use of intrinsically-typed terms
necessitates that we cannot introduce operations such as
substitution or reduction without also showing that they
preserve types.  Hence, the order of presentation must change.
-->

在本章中，使用内在类型的项要求我们在引入诸如重命名或者替换等操作的同时，证明它们保留了类型。
因此，我们必须改变展示的顺序。

<!--
The syntax of terms now incorporates their typing rules.  The
definition of substitution is somewhat more involved, but incorporates
the trickiest part of the previous proof, the lemma establishing that
substitution preserves types.  The definition of reduction
incorporates preservation, which no longer requires a separate proof.
-->

项的语法现在包含了它们的赋型规则。
替换的定义现在更加深入，但包括了之前证明中最棘手的部分，即替换保留了类型。
归约的定义现在包括了保型性，不需要额外的证明。

<!--
## Syntax
-->

## 语法

<!--
We now begin our formal development.
-->

现在，我们开始正式的定义。

<!--
First, we get all our infix declarations out of the way.
We list separately operators for judgments, types, and terms:
-->

我们首先定义中缀声明。我们分别列出判断、类型和项的运算符：

```agda
infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix  5 ƛ_
infix  5 μ_
infixl 7 _·_
infix  8 `suc_
infix  9 `_
infix  9 S_
infix  9 #_
```

<!--
Since terms are intrinsically typed, we must define types and
contexts before terms.
-->

由于项是内在类型的，我们必须在定义项之前先定义类型和语境。

<!--
### Types
-->

### 类型

<!--
As before, we have just two types, functions and naturals.
The formal definition is unchanged:
-->

与以前一样，我们只有两种类型：函数和自然数。它的形式化定义没有变化：

```agda
data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ  : Type
```

<!--
### Contexts
-->

<!--
Contexts are as before, but we drop the names.
Contexts are formalised as follows:
-->

语境如同之前一样，但是我们舍去了名字。
语境如下形式化：

```agda
data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context
```

<!--
A context is just a list of types, with the type of the most
recently bound variable on the right.  As before, we let `Γ`
and `Δ` range over contexts.  We write `∅` for the empty
context, and `Γ , A` for the context `Γ` extended by type `A`.
For example
-->

语境就是一个类型的列表，其最近约束的变量出现在右边。
如之前一样，我们使用 `Γ` 和 `Δ` 来表示语境。
我们用 `∅` 表示空语境，用 `Γ , A` 表示以 `A` 扩充的语境 `Γ`。
例如：

```agda
_ : Context
_ = ∅ , `ℕ ⇒ `ℕ , `ℕ
```

<!--
is a context with two variables in scope, where the outer
bound one has type `` `ℕ ⇒ `ℕ ``, and the inner bound one has
type `` `ℕ ``.
-->

在作用域中有两个变量，外部约束的变量的类型是 `` `ℕ ⇒ `ℕ ``，内部约束的类型是 `` `ℕ ``。

<!--
### Variables and the lookup judgment
-->

### 变量及查询判断

<!--
Intrinsically-typed variables correspond to the lookup judgment.
They are represented by de Bruijn indices, and hence also
correspond to natural numbers.  We write
-->

内在类型的变量对应着查询判断。它们由 de Bruijn 因子表示，因此也对应着自然数。
我们用

    Γ ∋ A

<!--
for variables which in context `Γ` have type `A`.
The lookup judgement is formalised by a datatype indexed
by a context and a type.
It looks exactly like the old lookup judgment, but
with all variable names dropped:
-->

表示语境 `Γ` 中带有类型 `A` 的变量。
查询判断由一个以语境和类型索引的数据类型来形式化。
它和之前的查询判断看上去一样，但是变量名被舍去了：

```agda
data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
      ---------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ , B ∋ A
```

<!--
Constructor `S` no longer requires an additional parameter,
since without names shadowing is no longer an issue.  Now
constructors `Z` and `S` correspond even more closely to the
constructors `here` and `there` for the element-of relation
`_∈_` on lists, as well as to constructors `zero` and `suc`
for natural numbers.
-->

`S` 构造子不再需要额外的参数，由于没有名字以后就不需要处理屏蔽效应。
现在的构造子 `Z` 和 `S` 更紧密地对应了列表中成员关系的构造子 `here` 和 `there`，
以及自然数的构造子 `zero` 和 `suc`。

<!--
For example, consider the following old-style lookup
judgments:
-->

例如，我们考虑下面的旧式查询判断：

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "z" ⦂ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "s" ⦂ `ℕ ⇒ `ℕ ``

<!--
They correspond to the following intrinsically-typed variables:
-->

它们对应了下列内在类型的变量：

```agda
_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ∋ `ℕ
_ = Z

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ∋ `ℕ ⇒ `ℕ
_ = S Z
```

<!--
In the given context, `"z"` is represented by `Z`
(as the most recently bound variable),
and `"s"` by `S Z`
(as the next most recently bound variable).
-->

在给出的语境中，`"z"` 由 `Z` 表示（最近约束的变量），
`"s"` 由 `S Z` 表示（下一个最近约束的变量）。

<!--
### Terms and the typing judgment
-->

### 项以及赋型判断

<!--
Intrinsically-typed terms correspond to the typing judgment.
We write
-->

内在类型的项对应了其赋型判断。我们用

    Γ ⊢ A

<!--
for terms which in context `Γ` have type `A`.
The judgement is formalised by a datatype indexed
by a context and a type.
It looks exactly like the old typing judgment, but
with all terms and variable names dropped:
-->

表示在语境 `Γ` 中类型为 `A` 的项。
这个判断用由语境和类型索引的数据类型进行形式化。
它和之前的查询判断看上去一样，但是变量名被舍去了：

```agda
data _⊢_ : Context → Type → Set where

  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  ƛ_  : ∀ {Γ A B}
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B

  `zero : ∀ {Γ}
      ---------
    → Γ ⊢ `ℕ

  `suc_ : ∀ {Γ}
    → Γ ⊢ `ℕ
      ------
    → Γ ⊢ `ℕ

  case : ∀ {Γ A}
    → Γ ⊢ `ℕ
    → Γ ⊢ A
    → Γ , `ℕ ⊢ A
      ----------
    → Γ ⊢ A

  μ_ : ∀ {Γ A}
    → Γ , A ⊢ A
      ---------
    → Γ ⊢ A
```

<!--
The definition exploits the close correspondence between the
structure of terms and the structure of a derivation showing
that it is well typed: now we use the derivation _as_ the
term.
-->

这个定义利用了项的结构和其良类型推导的结构之间紧密的对应关系：我们现在
使用推导**当作**项。

<!--
For example, consider the following old-style typing judgments:
-->

例如，考虑下列旧式的赋型判断：

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "z" ⦂ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" ⦂ `ℕ ⇒ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" · ` "z" ⦂  `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" · (` "s" · ` "z") ⦂  `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ ⊢ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) ⦂  `ℕ ⇒ `ℕ ``
* `` ∅ ⊢ ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) ⦂  (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ ``

<!--
They correspond to the following intrinsically-typed terms:
-->

它们对应了下列内在类型的项：

```agda
_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ
_ = ` Z

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ ⇒ `ℕ
_ = ` S Z

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ
_ = ` S Z · ` Z

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ
_ = ` S Z · (` S Z · ` Z)

_ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ ⇒ `ℕ
_ = ƛ (` S Z · (` S Z · ` Z))

_ : ∅ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ
_ = ƛ ƛ (` S Z · (` S Z · ` Z))
```

<!--
The final term represents the Church numeral two.
-->

最后的项表示了 Church 法表示的二。

<!--
### Abbreviating de Bruijn indices
-->
### 简化 de Bruijn 因子

<!--
We define a helper function that computes the length of a context,
which will be useful in making sure an index is within context bounds:
-->

我们定义一个辅助函数来计算语境的长度，它会在之后确保一个因子在语境约束中有帮助：

```agda
length : Context → ℕ
length ∅        =  zero
length (Γ , _)  =  suc (length Γ)
```

<!--
We can use a natural number to select a type from a context:
-->

我们可以用一个自然数来从语境中选择一个类型：

```agda
lookup : {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Type
lookup {(_ , A)} {zero}    (s≤s z≤n)  =  A
lookup {(Γ , _)} {(suc n)} (s≤s p)    =  lookup p
```

<!--
We intend to apply the function only when the natural is shorter than
the length of the context, which is witnessed by `p`.
-->

我们希望只在自然数小于语境长度的时候应用这个函数，由 `p` 来印证。

<!--
Given the above, we can convert a natural to a corresponding
de Bruijn index, looking up its type in the context:
-->

结合上述，我们可以将一个自然数转换成其对应的 de Bruijn 因子，从语境中查询它的类型：

```agda
count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ lookup p
count {_ , _} {zero}    (s≤s z≤n)  =  Z
count {Γ , _} {(suc n)} (s≤s p)    =  S (count p)
```

<!--
We can then introduce a convenient abbreviation for variables:
-->

然后，我们可以引入一个变量的简略表示方法：

```agda
#_ : ∀ {Γ}
  → (n : ℕ)
  → {n∈Γ : True (suc n ≤? length Γ)}
    --------------------------------
  → Γ ⊢ lookup (toWitness n∈Γ)
#_ n {n∈Γ}  =  ` count (toWitness n∈Γ)
```

<!--
Function `#_` takes an implicit argument `n∈Γ` that provides evidence for `n` to
be within the context's bounds. Recall that
[`True`](/Decidable/#proof-by-reflection),
[`_≤?_`](/Decidable/#the-best-of-both-worlds) and
[`toWitness`](/Decidable/#decidables-from-booleans-and-booleans-from-decidables)
are defined in Chapter [Decidable](/Decidable/). The type of `n∈Γ` guards
against invoking `#_` on an `n` that is out of context bounds. Finally, in the
return type `n∈Γ` is converted to a witness that `n` is within the bounds.
-->

函数 `#_` 取一个隐式参数 `n∈Γ` 来证明 `n` 在语境的约束内。
回忆 [`True`](/Decidable/#proof-by-reflection)、
[`_≤?_`](/Decidable/#the-best-of-both-worlds) 和
[`toWitness`](/Decidable/#decidables-from-booleans-and-booleans-from-decidables)
在 [Decidable](/Decidable/) 章节中定义。
`n∈Γ` 的类型保证了 `#_` 不会在 `n` 超出语境约束时被应用。
最后，在返回类型中，`n∈Γ` 被转换为 `n` 在语境约束内的证明。

<!--
With this abbreviation, we can rewrite the Church numeral two more compactly:
-->

使用这种缩略方法，我们可以用更简洁的方法写出 Church 法表示的二：

```agda
_ : ∅ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ
_ = ƛ ƛ (# 1 · (# 1 · # 0))
```

<!--
### Test examples
-->

### 测试例子

<!--
We repeat the test examples from Chapter [Lambda](/Lambda/). You can find them
[here](/Lambda/#derivation) for comparison.
-->

我们重复 [Lambda](/Lambda/) 中的测试例子。
你可以在[这里](/Lambda/#derivation)找到它们，并加以对比。

<!--
First, computing two plus two on naturals:
-->

首先计算自然数二加二：

```agda
two : ∀ {Γ} → Γ ⊢ `ℕ
two = `suc `suc `zero

plus : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
plus = μ ƛ ƛ (case (# 1) (# 0) (`suc (# 3 · # 0 · # 1)))

2+2 : ∀ {Γ} → Γ ⊢ `ℕ
2+2 = plus · two · two
```

<!--
We generalise to arbitrary contexts because later we will give examples
where `two` appears nested inside binders.
-->

我们推广到任意语境，因为我们在稍后给出 `two` 在内部约束时出现的例子。

<!--
Next, computing two plus two on Church numerals:
-->

接下来，计算 Church 法表示的二加二：

```agda
Ch : Type → Type
Ch A  =  (A ⇒ A) ⇒ A ⇒ A

twoᶜ : ∀ {Γ A} → Γ ⊢ Ch A
twoᶜ = ƛ ƛ (# 1 · (# 1 · # 0))

plusᶜ : ∀ {Γ A} → Γ ⊢ Ch A ⇒ Ch A ⇒ Ch A
plusᶜ = ƛ ƛ ƛ ƛ (# 3 · # 1 · (# 2 · # 1 · # 0))

sucᶜ : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ
sucᶜ = ƛ `suc (# 0)

2+2ᶜ : ∀ {Γ} → Γ ⊢ `ℕ
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero
```

<!--
As before we generalise everything to arbitrary
contexts.  While we are at it, we also generalise `twoᶜ` and
`plusᶜ` to Church numerals over arbitrary types.
-->

如同之前那样，我们推广到任意语境。
同时，我们将 `twoᶜ` 和 `plusᶜ` 推广至任意类型的 Church 法表示的自然数。


<!--
#### Exercise `mul` (recommended)
-->

#### 练习 `mul` （推荐）

<!--
Write out the definition of a lambda term that multiplies
two natural numbers, now adapted to the intrinsically-typed
de Bruijn representation.
-->

用内在类型和 de Bruijn 法写出一个将两个自然数相乘的项。


```agda
-- 请将代码写在此处
```

<!--
## Renaming
-->

## 重命名

<!--
Renaming is a necessary prelude to substitution, enabling us
to "rebase" a term from one context to another.  It
corresponds directly to the renaming result from the previous
chapter, but here the theorem that ensures renaming preserves
typing also acts as code that performs renaming.
-->

重命名是替换之前重要的一步，让我们可以将一个项从一个语境中 「转移」 至另一个语境。
它直接对应了上一章中的关于重命名的结论，但此处重命名保留类型的定理同时是进行重命名的代码。

<!--
As before, we first need an extension lemma that allows us to
extend the context when we encounter a binder. Given a map
from variables in one context to variables in another,
extension yields a map from the first context extended to the
second context similarly extended.  It looks exactly like the
old extension lemma, but with all names and terms dropped:
-->

和之前一样，我们首先需要一条扩充引理，使我们可以到遇到约束时扩充我们的语境。
给定一个将一个语境中的变量映射至另一个语境中变量的映射，扩充会生成一个
从扩充后的第一个语境至以相同方法扩充的第二个语境的映射。
它看上去和之前的扩充引理完全一样，只是舍去了名字和项：

```agda
ext : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ∋ A)
    ---------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)
```

<!--
Let `ρ` be the name of the map that takes variables in `Γ`
to variables in `Δ`.  Consider the de Bruijn index of the
variable in `Γ , B`:
-->

令 `ρ` 为从 `Γ` 中变量至 `Δ` 中变量的映射的名称。
考虑 `Γ , B` 中变量的 de Bruijn 因子：

<!--
* If it is `Z`, which has type `B` in `Γ , B`,
  then we return `Z`, which also has type `B` in `Δ , B`.

* If it is `S x`, for some variable `x` in `Γ`, then `ρ x`
  is a variable in `Δ`, and hence `S (ρ x)` is a variable in
  `Δ , B`.
-->

* 如果它是 `Z`，在 `Γ , B` 中的类型是 `B`，那么返回 `Z`，在 `Δ , B` 中的类型也是 `B`。

* 如果它是 `S x`，其中 `x` 是某个 `Γ` 中的变量，那么 `ρ x` 是 `Δ` 中的一个变量，
  因此 `S (ρ x)` 是一个 `Δ , B` 中的变量。

<!--
With extension under our belts, it is straightforward
to define renaming.  If variables in one context map to
variables in another, then terms in the first context map to
terms in the second:
-->

定义了扩充过后，重命名的定义就变得很直接了。
如果一个语境中的变量映射至另一个语境中的变量，那么第一个语境
中的项映射至第二个语境中：

```agda
rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
rename ρ (`zero)        =  `zero
rename ρ (`suc M)       =  `suc (rename ρ M)
rename ρ (case L M N)   =  case (rename ρ L) (rename ρ M) (rename (ext ρ) N)
rename ρ (μ N)          =  μ (rename (ext ρ) N)
```

<!--
Let `ρ` be the name of the map that takes variables in `Γ`
to variables in `Δ`.  Let's unpack the first three cases:
-->

令 `ρ` 为从 `Γ` 中变量至 `Δ` 中变量的映射的名称。
我们首先来解释前三种情况：

<!--
* If the term is a variable, simply apply `ρ`.

* If the term is an abstraction, use the previous result
  to extend the map `ρ` suitably and recursively rename
  the body of the abstraction.

* If the term is an application, recursively rename both
  the function and the argument.
-->

* 如果项是一个变量，直接应用 `ρ`。

* 如果项是一个抽象，使用之前的扩充结论来扩充映射 `ρ`，
  然后在递归地对于抽象本体进行重命名。

* 如果项是一个应用，递归地重命名函数及其参数。

<!--
The remaining cases are similar, recursing on each subterm,
and extending the map whenever the construct introduces a
bound variable.
-->

剩下的情况都很类似，在各个项中递归，并在引入约束变量的时候扩充映射。

<!--
Whereas before renaming was a result that carried evidence
that a term is well typed in one context to evidence that it
is well typed in another context, now it actually transforms
the term, suitably altering the bound variables. Type checking
the code in Agda ensures that it is only passed and returns
terms that are well typed by the rules of simply-typed lambda
calculus.
-->

之前，重命名是一个将项在一个语境中良类型的证明转换成项在另一个语境中
良类型的结论；而现在，它直接转换了整个项，调整了其中的约束变了。
在 Agda 中类型检查这段代码保证了只有在简单类型的 λ-演算中良类型的项
可以作为参数或者作为返回项。

<!--
Here is an example of renaming a term with one free
and one bound variable:
-->

下面的例子将带有一个自由变量，一个约束变量的项进行重命名：

```agda
M₀ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ ⇒ `ℕ
M₀ = ƛ (# 1 · (# 1 · # 0))

M₁ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ ⇒ `ℕ
M₁ = ƛ (# 2 · (# 2 · # 0))

_ : rename S_ M₀ ≡ M₁
_ = refl
```

<!--
In general, `rename S_` will increment the de Bruijn index for
each free variable by one, while leaving the index for each
bound variable unchanged.  The code achieves this naturally:
the map originally increments each variable by one, and is
extended for each bound variable by a map that leaves it
unchanged.
-->

通常来说，`rename S_` 会把所有自由变量的 de Bruijn 因子增加一，
而不改变约束变量的 de Bruijn 因子。
这个代码自然地完成了这样的操作：映射将所有的变量增加一，然而在扩充作用下，
每个约束变量的因子不变。

<!--
We will see below that renaming by `S_` plays a key role in
substitution.  For traditional uses of de Bruijn indices
without intrinsic typing, this is a little tricky. The code
keeps count of a number where all greater indexes are free and
all smaller indexes bound, and increment only indexes greater
than the number. It's easy to have off-by-one errors.  But
it's hard to imagine an off-by-one error that preserves
typing, and hence the Agda code for intrinsically-typed de Bruijn
terms is intrinsically reliable.
-->

我们稍后可以看到，使用 `S_` 进行重命名在替换中起到了重要作用。
对于没有使用内在类型的 de Bruijn 因子表示法来说，这会有一点棘手。
这种方法需要记忆一个因子数，更大的因子为自由变量，更小的因子为约束变量。
这样很容易出现差一错误，而出现差一错误以后很难保证类型的保存性。
因此这里内在类型的 de Bruijn 项的 Agda 代码是本质上更加可靠。

<!--
## Simultaneous Substitution
-->

## 同时替换

<!--
Because de Bruijn indices free us of concerns with renaming,
it becomes easy to provide a definition of substitution that
is more general than the one considered previously.  Instead
of substituting a closed term for a single variable, it
provides a map that takes each free variable of the original
term to another term. Further, the substituted terms are over
an arbitrary context, and need not be closed.
-->

由于 de Bruijn 因子让我们免去了重命名的顾虑，给出一个更广义的替换的定义更加方便。
与其用一个闭项来替换一个单一的变量，广义的替换提供一个将原来项中各个自由变量至另一个项的映射。
除此之外，被替换的项可以在任意语境之中，不需要为闭项。

<!--
The structure of the definition and the proof is remarkably
close to that for renaming.  Again, we first need an extension
lemma that allows us to extend the context when we encounter a
binder.  Whereas renaming concerned a map from variables
in one context to variables in another, substitution takes a
map from variables in one context to _terms_ in another.
Given a map from variables in one context to terms over
another, extension yields a map from the first context
extended to the second context similarly extended:
-->

定义和证明的结构与重命名项类似。
同样，我们首先需要一个扩充引理，让我们能够在遇到约束时扩充语境。
对比在重命名中我们使用从一个语境中的变量至另一语境中变量的映射，
替换使用的是将一个语境中的变量至另一语境中**项**的映射。
给定一个将一个语境中的变量映射至另一个语境中项的映射，扩充会生成一个
从扩充后的第一个语境至以相同方法扩充的第二个语境的映射。

```agda
exts : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ⊢ A)
    ---------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)
```

<!--
Let `σ` be the name of the map that takes variables in `Γ`
to terms over `Δ`.  Consider the de Bruijn index of the
variable in `Γ , B`:
-->

令 `σ` 为从 `Γ` 中变量至 `Δ` 中变量的项的名称。
考虑 `Γ , B` 中变量的 de Bruijn 因子：

<!--
* If it is `Z`, which has type `B` in `Γ , B`,
  then we return the term `` ` Z``, which also has
  type `B` in `Δ , B`.

* If it is `S x`, for some variable `x` in `Γ`, then
  `σ x` is a term in `Δ`, and hence `rename S_ (σ x)`
  is a term in `Δ , B`.
-->

* 如果它是 `Z`，在 `Γ , B` 中的类型是 `B`，
  那么返回 `` ` Z`` 项，在 `Δ , B` 中的类型也是 `B`。

* 如果它是 `S x`，其中 `x` 是某个 `Γ` 中的变量，那么 `σ x` 是 `Δ` 中的一个项，
  因此 `S_ (σ x)` 是一个 `Δ , B` 中的项。

<!--
This is why we had to define renaming first, since
we require it to convert a term over context `Δ`
to a term over the extended context `Δ , B`.
-->

这也是为什么我们需要先定义重命名，因为我们需要这个定义来将
语境 `Δ` 中的项重命名至扩充后的语境 `Δ , B`。

<!--
With extension under our belts, it is straightforward
to define substitution.  If variables in one context map
to terms over another, then terms in the first context
map to terms in the second:
-->

定义了扩充过后，替换的定义就变得很直接了。
如果一个语境中的变量映射至另一个语境中的项，那么第一个语境
中的项映射至第二个语境中：

```agda
subst : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ (` x)          =  σ x
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)
subst σ (`zero)        =  `zero
subst σ (`suc M)       =  `suc (subst σ M)
subst σ (case L M N)   =  case (subst σ L) (subst σ M) (subst (exts σ) N)
subst σ (μ N)          =  μ (subst (exts σ) N)
```

<!--
Let `σ` be the name of the map that takes variables in `Γ`
to terms over `Δ`.  Let's unpack the first three cases:
-->

令 `σ` 为从 `Γ` 中变量至 `Δ` 中项的映射的名称。
我们首先来解释前三种情况：

<!--
* If the term is a variable, simply apply `σ`.

* If the term is an abstraction, use the previous result
  to extend the map `σ` suitably and recursively substitute
  over the body of the abstraction.

* If the term is an application, recursively substitute over
  both the function and the argument.
-->

* 如果项是一个变量，直接应用 `σ`。

* 如果项是一个抽象，使用之前的扩充结论来扩充映射 `σ`，
  然后在递归地对于抽象本体进行进行替换。

* 如果项是一个应用，递归地替换函数及其参数。

<!--
The remaining cases are similar, recursing on each subterm,
and extending the map whenever the construct introduces a
bound variable.
-->

剩下的情况都很类似，在各个项中递归，并在引入约束变量的时候扩充映射。

<!--
## Single substitution
-->

## 单个替换

<!--
From the general case of substitution for multiple free
variables it is easy to define the special case of
substitution for one free variable:
-->

从广义的替换多个自由变量，我们可以定义只替换单个变量的特殊情况：

```agda
_[_] : ∀ {Γ A B}
  → Γ , B ⊢ A
  → Γ ⊢ B
    ---------
  → Γ ⊢ A
_[_] {Γ} {A} {B} N M =  subst {Γ , B} {Γ} σ {A} N
  where
  σ : ∀ {A} → Γ , B ∋ A → Γ ⊢ A
  σ Z      =  M
  σ (S x)  =  ` x
```

<!--
In a term of type `A` over context `Γ , B`, we replace the
variable of type `B` by a term of type `B` over context `Γ`.
To do so, we use a map from the context `Γ , B` to the context
`Γ`, that maps the last variable in the context to the term of
type `B` and every other free variable to itself.
-->

在一个语境 `Γ , B` 中类型为 `A` 的项，我们将类型为 `B` 的变量
替换为语境 `Γ` 中一个类型为 `B` 的项。
为了这么做，我们用一个从 `Γ , B` 语境至 `Γ` 语境的映射，
令语境中最后一个变量映射至类型为 `B` 的替换项，令任何其他自由变量映射至其本身。

<!--
Consider the previous example:
-->

考虑之前的例子：

<!--
* `` (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] `` yields
  `` ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z") ``
-->

* `` (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] `` 得
  `` ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z") ``

<!--
Here is the example formalised:
-->

下面是形式化后的例子：

```agda
M₂ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ ⇒ `ℕ
M₂ = ƛ # 1 · (# 1 · # 0)

M₃ : ∅ ⊢ `ℕ ⇒ `ℕ
M₃ = ƛ `suc # 0

M₄ : ∅ ⊢ `ℕ ⇒ `ℕ
M₄ = ƛ (ƛ `suc # 0) · ((ƛ `suc # 0) · # 0)

_ : M₂ [ M₃ ] ≡ M₄
_ = refl
```

<!--
Previously, we presented an example of substitution that we
did not implement, since it needed to rename the bound
variable to avoid capture:
-->

之前，我们展示了一个我们没有实现的替换的例子，因为它需要将约束变量重命名来防止捕捉：

<!--
* `` (ƛ "x" ⇒ ` "x" · ` "y") [ "y" := ` "x" · `zero ] `` should yield
  `` ƛ "z" ⇒ ` "z" · (` "x" · `zero) ``
-->

* `` (ƛ "x" ⇒ ` "x" · ` "y") [ "y" := ` "x" · `zero ] `` 应当得
  `` ƛ "z" ⇒ ` "z" · (` "x" · `zero) ``

<!--
Say the bound `"x"` has type `` `ℕ ⇒ `ℕ ``, the substituted
`"y"` has type `` `ℕ ``, and the free `"x"` also has type `` `ℕ ⇒ `ℕ ``.
Here is the example formalised:
-->

假设约束的 `"x"` 的类型是 `` `ℕ ⇒ `ℕ ``，被替换的 `"y"` 的类型是 `` `ℕ ``，
自由的 `"x"` 的类型也是 `` `ℕ ⇒ `ℕ ``。
下面是形式化后的例子：

```agda
M₅ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ
M₅ = ƛ # 0 · # 1

M₆ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ
M₆ = # 0 · `zero

M₇ : ∅ , `ℕ ⇒ `ℕ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ
M₇ = ƛ (# 0 · (# 1 · `zero))

_ : M₅ [ M₆ ] ≡ M₇
_ = refl
```

<!--
The logician Haskell Curry observed that getting the
definition of substitution right can be a tricky business.  It
can be even trickier when using de Bruijn indices, which can
often be hard to decipher.  Under the current approach, any
definition of substitution must, of necessity, preserve
types.  While this makes the definition more involved, it
means that once it is done the hardest work is out of the way.
And combining definition with proof makes it harder for errors
to sneak in.
-->

逻辑学家 Haskell Curry 注意到，正确地定义替换可能很棘手。
使用 de Bruijn 因子来定义替换可能更加棘手，且不易理解。
在现在的方法中，任何替换的定义必须保存类型。
虽然这样让定义更加深入，但这也意味着一旦定义完成以后最难的部分就完成了。
将定义和证明结合在一起可以让错误更不易出现。

<!--
## Values
-->

## 值

<!--
The definition of value is much as before:
-->

值的定义与之前差不多：

```agda
data Value : ∀ {Γ A} → Γ ⊢ A → Set where

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ N)

  V-zero : ∀ {Γ}
      -----------------
    → Value (`zero {Γ})

  V-suc : ∀ {Γ} {V : Γ ⊢ `ℕ}
    → Value V
      --------------
    → Value (`suc V)
```

<!--
Here `zero` requires an implicit parameter to aid inference,
much in the same way that `[]` did in
[Lists](/Lists/).
-->

此处的 `zero` 需要一个隐式函数来帮助类型推测，与 [Lists](/Lists/) 中 `[]` 的情况类似。

<!--
## Reduction
-->

## 归约

<!--
The reduction rules are the same as those given earlier, save
that for each term we must specify its types.  As before, we
have compatibility rules that reduce a part of a term,
labelled with `ξ`, and rules that simplify a constructor
combined with a destructor, labelled with `β`:
-->

归约规则和之前给出的类似，除去我们必须给出每个项的类型。
如同之前，兼容性规则归约一个项的一部分，用 `ξ` 标出；
简化构造子与其解构子的规则用 `β` 标出：

```agda
infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      ---------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      ---------------
    → V · M —→ V · M′

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
      --------------------
    → (ƛ N) · W —→ N [ W ]

  ξ-suc : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
    → M —→ M′
      -----------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {Γ A} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → L —→ L′
      -------------------------
    → case L M N —→ case L′ M N

  β-zero :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
      -------------------
    → case `zero M N —→ M

  β-suc : ∀ {Γ A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → Value V
      ----------------------------
    → case (`suc V) M N —→ N [ V ]

  β-μ : ∀ {Γ A} {N : Γ , A ⊢ A}
      ----------------
    → μ N —→ N [ μ N ]
```

<!--
The definition states that `M —→ N` can only hold of terms `M`
and `N` which _both_ have type `Γ ⊢ A` for some context `Γ`
and type `A`.  In other words, it is _built-in_ to our
definition that reduction preserves types.  There is no
separate Preservation theorem to prove.  The Agda type-checker
validates that each term preserves types.  In the case of `β`
rules, preservation depends on the fact that substitution
preserves types, which is built-in to our
definition of substitution.
-->

定义中指出，`M —→ N` 只能由类型**都**是 `Γ ⊢ A` 的两个项 `M` 和 `N` 组成，
其中 `Γ` 是一个语境，`A` 是一个类型。
换句话说，我们的定义中**内置**了归约保存类型的证明。
我们不需要额外证明保型性。
Agda 的类型检查器检验了每个项保存了类型。
在 `β` 规则的情况中，保型性依赖于替换保存类型的性质，而它内置于替换的定义之中。

<!--
## Reflexive and transitive closure
-->

## 自反传递闭包

<!--
The reflexive and transitive closure is exactly as before.
We simply cut-and-paste the previous definition:
-->

自反传递闭包的定义与之前完全一样。
我们直接复制粘贴之前的定义：

```agda
infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : (M : Γ ⊢ A)
      ------
    → M —↠ M

  step—→ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → M —↠ N
    → L —→ M
      ------
    → L —↠ N

pattern _—→⟨_⟩_ L L—→M M—↠N = step—→ L M—↠N L—→M

begin_ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N
```


<!--
## Examples
-->

## 例子 {#examples}

<!--
We reiterate each of our previous examples.  First, the Church
numeral two applied to the successor function and zero yields
the natural number two:
-->

我们重复之前的每一个例子。
首先，将 Church 法表示的二应用于后继函数和零得自然数二：

```agda
_ : twoᶜ · sucᶜ · `zero {∅} —↠ `suc `suc `zero
_ =
  begin
    twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ (sucᶜ · (sucᶜ · # 0))) · `zero
  —→⟨ β-ƛ V-zero ⟩
    sucᶜ · (sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    sucᶜ · `suc `zero
  —→⟨ β-ƛ (V-suc V-zero) ⟩
   `suc (`suc `zero)
  ∎
```
<!--
As before, we need to supply an explicit context to `` `zero ``.
-->

和之前一样，我们需要给出为 `` `zero `` 给出显式的语境。

<!--
Next, a sample reduction demonstrating that two plus two is four:
-->

接下来，展示二加二得四的归约例子：

```agda
_ : plus {∅} · two · two —↠ `suc `suc `suc `suc `zero
_ =
    plus · two · two
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ ƛ case (` S Z) (` Z) (`suc (plus · ` Z · ` S Z))) · two · two
  —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    (ƛ case two (` Z) (`suc (plus · ` Z · ` S Z))) · two
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    case two two (`suc (plus · ` Z · two))
  —→⟨ β-suc (V-suc V-zero) ⟩
    `suc (plus · `suc `zero · two)
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc ((ƛ ƛ case (` S Z) (` Z) (`suc (plus · ` Z · ` S Z)))
      · `suc `zero · two)
  —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
    `suc ((ƛ case (`suc `zero) (` Z) (`suc (plus · ` Z · ` S Z))) · two)
  —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
    `suc (case (`suc `zero) (two) (`suc (plus · ` Z · two)))
  —→⟨ ξ-suc (β-suc V-zero) ⟩
    `suc (`suc (plus · `zero · two))
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
    `suc (`suc ((ƛ ƛ case (` S Z) (` Z) (`suc (plus · ` Z · ` S Z)))
      · `zero · two))
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
    `suc (`suc ((ƛ case `zero (` Z) (`suc (plus · ` Z · ` S Z))) · two))
  —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
    `suc (`suc (case `zero (two) (`suc (plus · ` Z · two))))
  —→⟨ ξ-suc (ξ-suc β-zero) ⟩
   `suc (`suc (`suc (`suc `zero)))
  ∎
```

<!--
And finally, a similar sample reduction for Church numerals:
-->

最后，用 Church 数归约同样的例子：

```agda
_ : plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero —↠ `suc `suc `suc `suc `zero {∅}
_ =
  begin
    plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ))) ⟩
    (ƛ ƛ ƛ twoᶜ · ` S Z · (` S S Z · ` S Z · ` Z)) · twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ ƛ twoᶜ · ` S Z · (twoᶜ · ` S Z · ` Z)) · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ twoᶜ · sucᶜ · (twoᶜ · sucᶜ · ` Z)) · `zero
  —→⟨ β-ƛ V-zero ⟩
    twoᶜ · sucᶜ · (twoᶜ · sucᶜ · `zero)
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ sucᶜ · (sucᶜ · ` Z)) · (twoᶜ · sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ sucᶜ · (sucᶜ · ` Z)) · ((ƛ sucᶜ · (sucᶜ · ` Z)) · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ sucᶜ · (sucᶜ · ` Z)) · (sucᶜ · (sucᶜ · `zero))
  —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ V-zero)) ⟩
    (ƛ sucᶜ · (sucᶜ · ` Z)) · (sucᶜ · `suc `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ sucᶜ · (sucᶜ · ` Z)) · `suc (`suc `zero)
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    sucᶜ · (sucᶜ · `suc (`suc `zero))
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    sucᶜ · `suc (`suc (`suc `zero))
  —→⟨ β-ƛ (V-suc (V-suc (V-suc V-zero))) ⟩
    `suc (`suc (`suc (`suc `zero)))
  ∎
```

<!--
## Values do not reduce
-->

## 值不再归约

<!--
We have now completed all the definitions, which of
necessity subsumed some of the propositions from the
earlier development, namely that
substitution and reduction preserves types.
We now turn to proving the remaining results from the
previous development.
-->

我们现在完成了所有的定义，包含了之前证明的一些推论：替换保存类型和保型性。
我们接下来证明剩下的结论。

<!--
#### Exercise `V¬—→` (practice)
-->

#### 练习 `V¬—→`（习题）

<!--
Following the previous development, show values do
not reduce, and its corollary, terms that reduce are not
values.
-->

使用上文的表示方法，证明值不再归约；以及它的推论：可归约的项不是值。



```agda
-- 请将代码写在此处
```

<!--
## Progress
-->

## 可进性

<!--
As before, every term that is well typed and closed is either
a value or takes a reduction step.  The formulation of progress
is just as before, but annotated with types:
-->

和之前一样，每一个良类型的闭项要么是一个值，要么可以进行归约。
可进性的形式化与之前一样，但是附上了类型：

```agda
data Progress {A} (M : ∅ ⊢ A) : Set where

  step : ∀ {N : ∅ ⊢ A}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M
```

<!--
The statement and proof of progress is much as before,
appropriately annotated:
-->

可进性的声明和证明与之前大抵相同，加上了适当的附注：

```agda
progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress (` ())
progress (ƛ N)                          =  done V-ƛ
progress (L · M) with progress L
...    | step L—→L′                     =  step (ξ-·₁ L—→L′)
...    | done V-ƛ with progress M
...        | step M—→M′                 =  step (ξ-·₂ V-ƛ M—→M′)
...        | done VM                    =  step (β-ƛ VM)
progress (`zero)                        =  done V-zero
progress (`suc M) with progress M
...    | step M—→M′                     =  step (ξ-suc M—→M′)
...    | done VM                        =  done (V-suc VM)
progress (case L M N) with progress L
...    | step L—→L′                     =  step (ξ-case L—→L′)
...    | done V-zero                    =  step (β-zero)
...    | done (V-suc VL)                =  step (β-suc VL)
progress (μ N)                          =  step (β-μ)
```


<!--
## Evaluation
-->

## 求值

<!--
Before, we combined progress and preservation to evaluate a term.
We can do much the same here, but we no longer need to explicitly
refer to preservation, since it is built-in to the definition of reduction.
-->

之前，我们将保型性和可进性结合来对一个项求值。
我们在此处也可以这么做，但是我们不再需要显式地参考保型性，因为它内置于归约的定义中。

<!--
As previously, gas is specified by a natural number:
-->

如同之前，汽油由自然数表示：

```agda
record Gas : Set where
  constructor gas
  field
    amount : ℕ
```

<!--
When our evaluator returns a term `N`, it will either give evidence that
`N` is a value or indicate that it ran out of gas:
-->

当求值器返回项 `N` 时，它要么给出 `N` 是值的证明，要么提示汽油耗尽：

```agda
data Finished {Γ A} (N : Γ ⊢ A) : Set where

   done :
       Value N
       ----------
     → Finished N

   out-of-gas :
       ----------
       Finished N
```

<!--
Given a term `L` of type `A`, the evaluator will, for some `N`, return
a reduction sequence from `L` to `N` and an indication of whether
reduction finished:
-->

给定类型为 `A` 的项 `L`，求值器会返回一个从 `L` 到某个 `N` 的求值序列，并提示归约是否完成：

```agda
data Steps {A} : ∅ ⊢ A → Set where

  steps : {L N : ∅ ⊢ A}
    → L —↠ N
    → Finished N
      ----------
    → Steps L
```

<!--
The evaluator takes gas and a term and returns the corresponding steps:
-->

求值器取汽油和项，返回对应的步骤：

```agda
eval : ∀ {A}
  → Gas
  → (L : ∅ ⊢ A)
    -----------
  → Steps L
eval (gas zero)    L                     =  steps (L ∎) out-of-gas
eval (gas (suc m)) L with progress L
... | done VL                            =  steps (L ∎) (done VL)
... | step {M} L—→M with eval (gas m) M
...    | steps M—↠N fin                  =  steps (L —→⟨ L—→M ⟩ M—↠N) fin
```

<!--
The definition is a little simpler than previously, as we no longer need
to invoke preservation.
-->

由于我们不再需要使用保型性，定义比之前略微简单。

<!--
## Examples
-->

## 例子

<!--
We reiterate each of our previous examples.  We re-define the term
`sucμ` that loops forever:
-->

我们重复之前的例子，重新定义无限循环的项 `sucμ`：

```agda
sucμ : ∅ ⊢ `ℕ
sucμ = μ (`suc (# 0))
```

<!--
To compute the first three steps of the infinite reduction sequence,
we evaluate with three steps worth of gas:
-->

为了计算无限归约序列的前三步，我们使用满足三步的汽油：

```agda
_ : eval (gas 3) sucμ ≡
  steps
   (μ `suc ` Z
   —→⟨ β-μ ⟩
    `suc (μ `suc ` Z)
   —→⟨ ξ-suc β-μ ⟩
    `suc (`suc (μ `suc ` Z))
   —→⟨ ξ-suc (ξ-suc β-μ) ⟩
    `suc (`suc (`suc (μ `suc ` Z)))
   ∎)
   out-of-gas
_ = refl
```

<!--
The Church numeral two applied to successor and zero:
-->

将 Church 法表示的二应用于后继函数和零：

```agda
_ : eval (gas 100) (twoᶜ · sucᶜ · `zero) ≡
  steps
   ((ƛ (ƛ ` (S Z) · (` (S Z) · ` Z))) · (ƛ `suc ` Z) · `zero
   —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ (ƛ `suc ` Z) · ((ƛ `suc ` Z) · ` Z)) · `zero
   —→⟨ β-ƛ V-zero ⟩
    (ƛ `suc ` Z) · ((ƛ `suc ` Z) · `zero)
   —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ `suc ` Z) · `suc `zero
   —→⟨ β-ƛ (V-suc V-zero) ⟩
    `suc (`suc `zero)
   ∎)
   (done (V-suc (V-suc V-zero)))
_ = refl
```

<!--
Two plus two is four:
-->

二加二等于四：

```agda
_ : eval (gas 100) (plus · two · two) ≡
  steps
   ((μ
     (ƛ
      (ƛ
       case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · `suc (`suc `zero)
    · `suc (`suc `zero)
   —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ
     (ƛ
      case (` (S Z)) (` Z)
      (`suc
       ((μ
         (ƛ
          (ƛ
           case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
        · ` Z
        · ` (S Z)))))
    · `suc (`suc `zero)
    · `suc (`suc `zero)
   —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    (ƛ
     case (`suc (`suc `zero)) (` Z)
     (`suc
      ((μ
        (ƛ
         (ƛ
          case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
       · ` Z
       · ` (S Z))))
    · `suc (`suc `zero)
   —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    case (`suc (`suc `zero)) (`suc (`suc `zero))
    (`suc
     ((μ
       (ƛ
        (ƛ
         case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
      · ` Z
      · `suc (`suc `zero)))
   —→⟨ β-suc (V-suc V-zero) ⟩
    `suc
    ((μ
      (ƛ
       (ƛ
        case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
     · `suc `zero
     · `suc (`suc `zero))
   —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc
    ((ƛ
      (ƛ
       case (` (S Z)) (` Z)
       (`suc
        ((μ
          (ƛ
           (ƛ
            case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
         · ` Z
         · ` (S Z)))))
     · `suc `zero
     · `suc (`suc `zero))
   —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
    `suc
    ((ƛ
      case (`suc `zero) (` Z)
      (`suc
       ((μ
         (ƛ
          (ƛ
           case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
        · ` Z
        · ` (S Z))))
     · `suc (`suc `zero))
   —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
    `suc
    case (`suc `zero) (`suc (`suc `zero))
    (`suc
     ((μ
       (ƛ
        (ƛ
         case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
      · ` Z
      · `suc (`suc `zero)))
   —→⟨ ξ-suc (β-suc V-zero) ⟩
    `suc
    (`suc
     ((μ
       (ƛ
        (ƛ
         case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
      · `zero
      · `suc (`suc `zero)))
   —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
    `suc
    (`suc
     ((ƛ
       (ƛ
        case (` (S Z)) (` Z)
        (`suc
         ((μ
           (ƛ
            (ƛ
             case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
          · ` Z
          · ` (S Z)))))
      · `zero
      · `suc (`suc `zero)))
   —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
    `suc
    (`suc
     ((ƛ
       case `zero (` Z)
       (`suc
        ((μ
          (ƛ
           (ƛ
            case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
         · ` Z
         · ` (S Z))))
      · `suc (`suc `zero)))
   —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
    `suc
    (`suc
     case `zero (`suc (`suc `zero))
     (`suc
      ((μ
        (ƛ
         (ƛ
          case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
       · ` Z
       · `suc (`suc `zero))))
   —→⟨ ξ-suc (ξ-suc β-zero) ⟩
    `suc (`suc (`suc (`suc `zero)))
   ∎)
   (done (V-suc (V-suc (V-suc (V-suc V-zero)))))
_ = refl
```

<!--
And the corresponding term for Church numerals:
-->

以及 Church 法表示的对应的项：

```agda
_ : eval (gas 100) (plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero) ≡
  steps
   ((ƛ
     (ƛ
      (ƛ (ƛ ` (S (S (S Z))) · ` (S Z) · (` (S (S Z)) · ` (S Z) · ` Z)))))
    · (ƛ (ƛ ` (S Z) · (` (S Z) · ` Z)))
    · (ƛ (ƛ ` (S Z) · (` (S Z) · ` Z)))
    · (ƛ `suc ` Z)
    · `zero
   —→⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ))) ⟩
    (ƛ
     (ƛ
      (ƛ
       (ƛ (ƛ ` (S Z) · (` (S Z) · ` Z))) · ` (S Z) ·
       (` (S (S Z)) · ` (S Z) · ` Z))))
    · (ƛ (ƛ ` (S Z) · (` (S Z) · ` Z)))
    · (ƛ `suc ` Z)
    · `zero
   —→⟨ ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ
     (ƛ
      (ƛ (ƛ ` (S Z) · (` (S Z) · ` Z))) · ` (S Z) ·
      ((ƛ (ƛ ` (S Z) · (` (S Z) · ` Z))) · ` (S Z) · ` Z)))
    · (ƛ `suc ` Z)
    · `zero
   —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ
     (ƛ (ƛ ` (S Z) · (` (S Z) · ` Z))) · (ƛ `suc ` Z) ·
     ((ƛ (ƛ ` (S Z) · (` (S Z) · ` Z))) · (ƛ `suc ` Z) · ` Z))
    · `zero
   —→⟨ β-ƛ V-zero ⟩
    (ƛ (ƛ ` (S Z) · (` (S Z) · ` Z))) · (ƛ `suc ` Z) ·
    ((ƛ (ƛ ` (S Z) · (` (S Z) · ` Z))) · (ƛ `suc ` Z) · `zero)
   —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ (ƛ `suc ` Z) · ((ƛ `suc ` Z) · ` Z)) ·
    ((ƛ (ƛ ` (S Z) · (` (S Z) · ` Z))) · (ƛ `suc ` Z) · `zero)
   —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ (ƛ `suc ` Z) · ((ƛ `suc ` Z) · ` Z)) ·
    ((ƛ (ƛ `suc ` Z) · ((ƛ `suc ` Z) · ` Z)) · `zero)
   —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ (ƛ `suc ` Z) · ((ƛ `suc ` Z) · ` Z)) ·
    ((ƛ `suc ` Z) · ((ƛ `suc ` Z) · `zero))
   —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ V-zero)) ⟩
    (ƛ (ƛ `suc ` Z) · ((ƛ `suc ` Z) · ` Z)) ·
    ((ƛ `suc ` Z) · `suc `zero)
   —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ (ƛ `suc ` Z) · ((ƛ `suc ` Z) · ` Z)) · `suc (`suc `zero)
   —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    (ƛ `suc ` Z) · ((ƛ `suc ` Z) · `suc (`suc `zero))
   —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    (ƛ `suc ` Z) · `suc (`suc (`suc `zero))
   —→⟨ β-ƛ (V-suc (V-suc (V-suc V-zero))) ⟩
    `suc (`suc (`suc (`suc `zero)))
   ∎)
   (done (V-suc (V-suc (V-suc (V-suc V-zero)))))
_ = refl
```

<!--
We omit the proof that reduction is deterministic, since it is
tedious and almost identical to the previous proof.
-->

我们省去归约是确定的证明，因为它很繁琐，而且与之前的证明几乎完全相同。

<!--
#### Exercise `mul-example` (recommended)
-->

#### 练习 `mul-example` （推荐）

<!--
Using the evaluator, confirm that two times two is four.
-->

使用求值器，确认二乘二等于四。



```agda
-- 请将代码写在此处
```


<!--
## Intrinsic typing is golden
-->

## 内在类型是黄金的

<!--
Counting the lines of code is instructive.  While this chapter
covers the same formal development as the previous two
chapters, it has much less code.  Omitting all the examples,
and all proofs that appear in Properties but not DeBruijn
(such as the proof that reduction is deterministic), the
number of lines of code is as follows:
-->

代码行数是有提示性的。
这一章虽然包括了前两章涵盖的形式化内容，却用了更少的代码。
除去所有的例子，和 Properties 中出现且没有在 DeBruijn 中出现的证明
（例如归约是确定的证明），代码行数如下：

    Lambda                      216
    Properties                  235
    DeBruijn                    276

<!--
The relation between the two approaches approximates the
golden ratio: extrinsically-typed terms
require about 1.6 times as much code as intrinsically-typed.
-->

两种方法的比例接近于黄金比例：外在类型的项代码行数大约是内在类型项的 1.6 倍。

## Unicode

<!--
This chapter uses the following unicode:
-->

本章中使用了以下 Unicode：

    σ  U+03C3  GREEK SMALL LETTER SIGMA (\Gs or \sigma)
    ₀  U+2080  SUBSCRIPT ZERO (\_0)
    ₃  U+20B3  SUBSCRIPT THREE (\_3)
    ₄  U+2084  SUBSCRIPT FOUR (\_4)
    ₅  U+2085  SUBSCRIPT FIVE (\_5)
    ₆  U+2086  SUBSCRIPT SIX (\_6)
    ₇  U+2087  SUBSCRIPT SEVEN (\_7)
    ≠  U+2260  NOT EQUAL TO (\=n)
