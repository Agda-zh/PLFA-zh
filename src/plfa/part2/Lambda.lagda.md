---
title     : "Lambda: λ-演算简介"
layout    : page
prev      : /Lists/
permalink : /Lambda/
next      : /Properties/
---

```
module plfa.part2.Lambda where
```

<!--
The _lambda-calculus_, first published by the logician Alonzo Church in
1932, is a core calculus with only three syntactic constructs:
variables, abstraction, and application.  It captures the key concept of
_functional abstraction_, which appears in pretty much every programming
language, in the form of either functions, procedures, or methods.
The _simply-typed lambda calculus_ (or STLC) is a variant of the
lambda calculus published by Church in 1940.  It has the three
constructs above for function types, plus whatever else is required
for base types. Church had a minimal base type with no operations.
We will instead echo Plotkin's _Programmable Computable
Functions_ (PCF), and add operations on natural numbers and
recursive function definitions.
-->

**λ-演算**，最早由逻辑学家 Alonzo Church 发表，是一种只含有三种构造的演算——
变量（Variable）、抽象（Abstraction）与应用（Application）。
**λ-演算**含括了**函数抽象**（Functional Abstract）的核心概念。这样的概念
以函数、过程和方法的形式，在基本上每一个编程语言中都有体现。
简单类型的 λ-演算 （Simply-Typed Lambda Calculus，简写为 STLC）是 λ-演算的一种变体，
由 Church 在 1940 年发表。
除去之前提到的三种构造，简单类型的 λ-演算还拥有函数类型和任何所需的基本类型。
Church 使用了最简单的没有任何操作的基本类型。
我们在这里使用 Plotkin 的**可编程的可计算函数**（Programmable Computable Functions，PCF），
并加入自然数和递归函数及其相关操作。

<!--
This chapter formalises the simply-typed lambda calculus, giving its
syntax, small-step semantics, and typing rules.  The next chapter
[Properties](/Properties/)
proves its main properties, including
progress and preservation.  Following chapters will look at a number
of variants of lambda calculus.
-->

在这个章节中，我们将形式化简单类型的 λ-演算，给出它的语法、小步语义和类型规则。
在下一个章节 [Properties](/Properties/) 中，我们将
证明它的主要性质，包括可进性与保型性。
后续的章节将研究 λ-演算的不同变体。

<!--
Be aware that the approach we take here is _not_ our recommended
approach to formalisation.  Using de Bruijn indices and
intrinsically-typed terms, as we will do in
Chapter [DeBruijn](/DeBruijn/),
leads to a more compact formulation.  Nonetheless, we begin with named
variables and extrinsically-typed terms,
partly because names are easier than indices to read,
and partly because the development is more traditional.
-->

请注意，我们在这里使用的方法**不是**形式化的推荐方法。使用 de Bruijn 因子和
固有类型的项（我们会在 [DeBruijn](/DeBruijn/) 章节中进一步研究），
可以让我们的形式化更简洁。
尽管如此，我们首先使用带名字的变量和外在类型的项来表示 λ-演算。
这样一方面是因为这样表述的项更易于阅读，另一方面是因为这样的表述更加传统。

<!--
The development in this chapter was inspired by the corresponding
development in Chapter _Stlc_ of _Software Foundations_
(_Programming Language Foundations_).  We differ by
representing contexts explicitly (as lists pairing identifiers with
types) rather than as partial maps (which take identifiers to types),
which corresponds better to our subsequent development of DeBruijn
notation. We also differ by taking natural numbers as the base type
rather than booleans, allowing more sophisticated examples. In
particular, we will be able to show (twice!) that two plus two is
four.
-->

这一章节由《软件基础》（_Software Foundations_）/《程序语言基础》（_Programming Language
Foundations_）的对应的 _Stlc_ 章节所启发。
我们的不同之处在于使用显式的方法来表示上下文（由表示符和类型的有序对组成的列表），
而不是偏映射（从表示符到类型的偏函数）。
这样的做法与后续的 de Bruijn 因子表示方法能更好的对应。
我们使用自然数作为基础类型，而不是布尔值，这样我们可以表示更复杂的例子。
特别的是，我们将可以证明（两次！）二加二得四。

<!--
## Imports
-->

## 导入

```
open import Data.Bool using (T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
```

<!--
## Syntax of terms
-->

## 项的语法

<!--
Terms have seven constructs. Three are for the core lambda calculus:

  * Variables `` ` x ``
  * Abstractions `ƛ x ⇒ N`
  * Applications `L · M`

Three are for the naturals:

  * Zero `` `zero ``
  * Successor `` `suc M ``
  * Case `` case L [zero⇒ M |suc x ⇒ N ] ``

And one is for recursion:

  * Fixpoint `μ x ⇒ M`
-->

项由七种构造组成。首先是 λ-演算中核心的三个构造：

  * 变量 `` ` x ``
  * 抽象 `ƛ x ⇒ N`
  * 应用 `L · M`

三个与自然数有关的构造：

  * 零 `` `zero ``
  * 后继 `` `suc ``
  * 匹配 `` case L [zero⇒ M |suc x ⇒ N ] ``

一个与递归有关的构造：

  * 不动点 `μ x ⇒ M`

<!--
Abstraction is also called _lambda abstraction_, and is the construct
from which the calculus takes its name.
-->

抽象也被叫做 *λ-抽象*，这也是 λ-演算名字的由来。

<!--
With the exception of variables and fixpoints, each term
form either constructs a value of a given type (abstractions yield functions,
zero and successor yield natural numbers) or deconstructs it (applications use functions,
case terms use naturals). We will see this again when we come
to the rules for assigning types to terms, where constructors
correspond to introduction rules and deconstructors to eliminators.
-->

除了变量和不动点以外，每一个项要么构造了一个给定类型的值
（抽象产生了函数，零和后继产生了自然数），
要么析构了一个这样的值 （应用使用了函数，匹配使用了自然数）。
我们在给项赋予类型的时候将重新探讨这一对应关系。
构造子对应了引入规则，析构子对应了消去规则。

<!--
Here is the syntax of terms in Backus-Naur Form (BNF):
-->

下面是以 Backus-Naur 形式（BNF）给出的语法：

    L, M, N  ::=
      ` x  |  ƛ x ⇒ N  |  L · M  |
      `zero  |  `suc M  |  case L [zero⇒ M |suc x ⇒ N ]  |
      μ x ⇒ M

<!--
And here it is formalised in Agda:
-->

而下面是用 Agda 的形式化：

```
Id : Set
Id = String

infix  5  ƛ_⇒_
infix  5  μ_⇒_
infixl 7  _·_
infix  8  `suc_
infix  9  `_

data Term : Set where
  `_                      :  Id → Term
  ƛ_⇒_                    :  Id → Term → Term
  _·_                     :  Term → Term → Term
  `zero                   :  Term
  `suc_                   :  Term → Term
  case_[zero⇒_|suc_⇒_]    :  Term → Term → Id → Term → Term
  μ_⇒_                    :  Id → Term → Term
```
<!--
We represent identifiers by strings.  We choose precedence so that
lambda abstraction and fixpoint bind least tightly, then application,
then successor, and tightest of all is the constructor for variables.
Case expressions are self-bracketing.
-->

我们用字符串来表示表示符。
我们使用的优先级使得 λ-抽象和不动点结合的最不紧密，其次是应用，再是后继，
结合得最紧密的是变量的构造子。
匹配表达式自带了括号。

<!--
### Example terms
-->

### 项的例子

<!--
Here are some example terms: the natural number two,
a function that adds naturals,
and a term that computes two plus two:
-->

下面是一些项的例子：自然数二、一个将自然数相加的函数和一个计算二加二的项：

```
two : Term
two = `suc `suc `zero

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
         case ` "m"
           [zero⇒ ` "n"
           |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]
```
<!--
The recursive definition of addition is similar to our original
definition of `_+_` for naturals, as given in
Chapter [Naturals](/Naturals/#plus).
Here variable "m" is bound twice, once in a lambda abstraction and once in
the successor branch of the case; the first use of "m" refers to
the former and the second to the latter.  Any use of "m" in the successor branch
must refer to the latter binding, and so we say that the latter binding _shadows_
the former.  Later we will confirm that two plus two is four, in other words that
the term

FIXME: shadow 应该翻译成什么？
-->

加法的递归定义与我们一开始在 [Naturals](/Naturals/#plus) 章节中定义的
`_+_` 相似。
在这里，变量「m」被约束了两次，一个在 λ-抽象中，另一次在匹配表达式的后继分支中。
第一次使用的「m」指代前者，第二次使用的指代后者。
任何在后继分支中的「m」必须指代后者，因此我们称之为后者**遮盖**（Shadow）了前者。
后面我们会证实二加二得四，也就是说下面的项

    plus · two · two

<!--
reduces to `` `suc `suc `suc `suc `zero ``.
-->

规约至 `` `suc `suc `suc `suc `zero ``。

<!--
As a second example, we use higher-order functions to represent
natural numbers.  In particular, the number _n_ is represented by a
function that accepts two arguments and applies the first _n_ times to the
second.  This is called the _Church representation_ of the
naturals.  Here are some example terms: the Church numeral two, a
function that adds Church numerals, a function to compute successor,
and a term that computes two plus two:
-->

第二个例子里，我们使用高阶函数来表示自然数。
具体来说，数字 _n_ 是有一个取两个参数的函数来表示，这个函数将第一个参数
应用于第二个参数上 _n_ 次。
这样的表示方法叫做自然数的 **Church 表示法**。
下面是一个项的例子：Church 表示法的数字二、一个将两个用 Church 表示法的表示数字相加的函数、
一个计算后继的函数和一个计算二加二的项：
```
twoᶜ : Term
twoᶜ =  ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

plusᶜ : Term
plusᶜ =  ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
         ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")
```
<!--
The Church numeral for two takes two arguments `s` and `z`
and applies `s` twice to `z`.
Addition takes two numerals `m` and `n`, a
function `s` and an argument `z`, and it uses `m` to apply `s` to the
result of using `n` to apply `s` to `z`; hence `s` is applied `m` plus
`n` times to `z`, yielding the Church numeral for the sum of `m` and
`n`.  For convenience, we define a function that computes successor.
To convert a Church numeral to the corresponding natural, we apply
it to the `sucᶜ` function and the natural number zero.
Again, later we will confirm that two plus two is four,
in other words that the term
-->

Church 法表示的二取两个参数 `s` 和 `z`，将 `s` 运用于 `z` 两次。
加法取两个数 `m` 和 `n`，函数 `s` 和参数 `z`，使用 `m` 将 `s` 应用于
使用 `n` 应用于 `s` 和 `z` 的结果。因此 `s` 对于 `z` 被应用了 `m` 加 `n` 次。
为了方便起见，我们定义一个计算后继的函数。
将一个 Church 数转化为对应的自然数的，我们使用其应用于 `sucᶜ` 函数和自然数零。
同样，我们后续会证实二加二得四，也就是说，下面的项

    plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero

<!--
reduces to `` `suc `suc `suc `suc `zero ``.
-->

规约至 `` `suc `suc `suc `suc `zero ``。


<!--
#### Exercise `mul` (recommended)
-->

#### 练习 `mul` （推荐）

<!--
Write out the definition of a lambda term that multiplies
two natural numbers.  Your definition may use `plus` as
defined earlier.
-->

写出一个项来定义两个自然数的乘法。你可以使用之前定义的 `plus`。

<!--
```
-- Your code goes here
```
-->

```
-- 请将代码写在此处。
```

<!--
#### Exercise `mulᶜ` (practice)
-->

#### 练习 `mulᶜ` （习题）

<!--
Write out the definition of a lambda term that multiplies
two natural numbers represented as Church numerals. Your
definition may use `plusᶜ` as defined earlier (or may not
— there are nice definitions both ways).
-->

写出一个项来定义两个用 Church 法表示的自然数的乘法。
你可以使用之前定义的 `plusᶜ`。
（你也可以不使用，使用或不使用都有好的表示方法）

<!--
```
-- Your code goes here
```
-->

```
-- 请将代码写在此处。
```


<!--
#### Exercise `primed` (stretch) {#primed}
-->

#### 练习 `primed` （延伸）{#primed}

<!--
Some people find it annoying to write `` ` "x" `` instead of `x`.
We can make examples with lambda terms slightly easier to write
by adding the following definitions:
-->

用 `` ` "x" `` 而不是 `x` 来表示变量可能并不是每个人都喜欢。
我们可以加入下面的定义，来帮助我们表示项的例子：

```
ƛ′_⇒_ : Term → Term → Term
ƛ′ (` x) ⇒ N  =  ƛ x ⇒ N
ƛ′ _ ⇒ _      =  ⊥-elim impossible
  where postulate impossible : ⊥

case′_[zero⇒_|suc_⇒_] : Term → Term → Term → Term → Term
case′ L [zero⇒ M |suc (` x) ⇒ N ]  =  case L [zero⇒ M |suc x ⇒ N ]
case′ _ [zero⇒ _ |suc _ ⇒ _ ]      =  ⊥-elim impossible
  where postulate impossible : ⊥

μ′_⇒_ : Term → Term → Term
μ′ (` x) ⇒ N  =  μ x ⇒ N
μ′ _ ⇒ _      =  ⊥-elim impossible
  where postulate impossible : ⊥
```

<!--
We intend to apply the function only when the first term is a variable, which we
indicate by postulating a term `impossible` of the empty type `⊥`.  If we use
C-c C-n to normalise the term
-->

我们希望只在两个参数不相等的时候应用这个函数；
我们假设一个空类型 `⊥` 的项 `impossible`，用来表示第二种情况不会发生。
如果我们使用 C-c C-n 来范式化这个项

    ƛ′ two ⇒ two

<!--
Agda will return an answer warning us that the impossible has occurred:
-->

    ⊥-elim (plfa.part2.Lambda.impossible (`` `suc (`suc `zero)) (`suc (`suc `zero)) ``)

<!--
While postulating the impossible is a useful technique, it must be
used with care, since such postulation could allow us to provide
evidence of _any_ proposition whatsoever, regardless of its truth.
-->

假设一件不可能的事情是一个有用的方法，但是我们必须加以注意。因为这样的假设能让我们
不管真假构造出**任何的**命题。

<!--
The definition of `plus` can now be written as follows:
-->

现在我们可以用下面的形式重新写出 `plus` 的定义：

```
plus′ : Term
plus′ = μ′ + ⇒ ƛ′ m ⇒ ƛ′ n ⇒
          case′ m
            [zero⇒ n
            |suc m ⇒ `suc (+ · m · n) ]
  where
  +  =  ` "+"
  m  =  ` "m"
  n  =  ` "n"
```
<!--
Write out the definition of multiplication in the same style.
-->

用这样的形式写出乘法的定义。

<!--
FIXME: 形式化？正式？

### Formal vs informal
-->

### 正式与非正式

<!--
In informal presentation of formal semantics, one uses choice of
variable name to disambiguate and writes `x` rather than `` ` x ``
for a term that is a variable. Agda requires we distinguish.
-->

在形式化语义的非正式表达中，我们使用变量名来消除歧义，用 `x` 而不是 `` ` x ``
来表示一个变量项。Agda 要求我们对两者进行区分。

<!--
Similarly, informal presentation often use the same notation for
function types, lambda abstraction, and function application in both
the _object language_ (the language one is describing) and the
_meta-language_ (the language in which the description is written),
trusting readers can use context to distinguish the two.  Agda is
not quite so forgiving, so here we use `ƛ x ⇒ N` and `L · M` for the
object language, as compared to `λ x → N` and `L M` in our
meta-language, Agda.
-->

相似地来说，非正式的表达在**对象语言**（Object Language，我们正在描述的语言）
和**元语言**（Meta-Language，我们用来描述对象语言的语言）
中使用相同的记法来表示函数类型、λ-抽象和函数应用，相信读者可以通关上下文区分两种语言。
而 Agda 并不能做到这样，因此我们在目标语言中使用 `ƛ x ⇒ N` 和 `L · M` ，
与我们使用的元语言 Agda 中的 `λ x → N` 和 `L M` 相对。

<!--
### Bound and free variables
-->

### 约束和自由变量

<!--
In an abstraction `ƛ x ⇒ N` we call `x` the _bound_ variable
and `N` the _body_ of the abstraction.  A central feature
of lambda calculus is that consistent renaming of bound variables
leaves the meaning of a term unchanged.  Thus the five terms
-->

在抽象 `ƛ x ⇒ N` 中，我们把 `x` 叫做**约束**变量，`N` 叫做抽象**体**。
λ-演算一个重要的特性是将约束变量连贯一致的重命名不改变一个项的意义。
因此下面的五个项

* `` ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ``
* `` ƛ "f" ⇒ ƛ "x" ⇒ ` "f" · (` "f" · ` "x") ``
* `` ƛ "sam" ⇒ ƛ "zelda" ⇒ ` "sam" · (` "sam" · ` "zelda") ``
* `` ƛ "z" ⇒ ƛ "s" ⇒ ` "z" · (` "z" · ` "s") ``
* `` ƛ "😇" ⇒ ƛ "😈" ⇒ ` "😇" · (` "😇" · ` "😈" ) ``

<!--
are all considered equivalent.  Following the convention introduced
by Haskell Curry, who used the Greek letter `α` (_alpha_) to label such rules,
this equivalence relation is called _alpha renaming_.
-->

可以认为是完全相等的。使用 Haskell Curry 引入的惯例，这样的规则
用希腊字母 `α` （_alpha_） 来表示，因此这样的相等关系也叫做 **α-重命名**。

<!--
As we descend from a term into its subterms, variables
that are bound may become free.  Consider the following terms:
-->

当我们从一个项中观察它的子项时，被约束的变量可能会变成自由变量。
考虑下面的项：

<!--
* `` ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ``
  has both `s` and `z` as bound variables.

* `` ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ``
  has `z` bound and `s` free.

* `` ` "s" · (` "s" · ` "z") ``
  has both `s` and `z` as free variables.
-->

* `` ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ``
  `s` 和 `z` 都是约束变量。

* `` ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ``
  `z` 是约束变量，`s` 是自由变量。

* `` ` "s" · (` "s" · ` "z") ``
  `s` 和 `z` 都是自由变量。

<!--
We say that a term with no free variables is _closed_; otherwise it is
_open_.  Of the three terms above, the first is closed and the other
two are open.  We will focus on reduction of closed terms.
-->

我们将没有自由变量的项叫做**封闭的**（Closed）项，否则它是一个**开放的**（Open）项。
上面的三个项中，第一个是封闭的，剩下两个是开放的。我们在讨论规约时，会注重封闭的项。

<!--
Different occurrences of a variable may be bound and free.
In the term
-->

一个变量在不同地方出现时，可以同时是约束变量和自由变量。在下面的项中：

    (ƛ "x" ⇒ ` "x") · ` "x"

<!--
the inner occurrence of `x` is bound while the outer occurrence is free.
By alpha renaming, the term above is equivalent to
-->

内部的 `x` 是约束变量，外部的是自由变量。使用 α-重命名，上面的项等同于

    (ƛ "y" ⇒ ` "y") · ` "x"

<!--
in which `y` is bound and `x` is free.  A common convention, called the
_Barendregt convention_, is to use alpha renaming to ensure that the bound
variables in a term are distinct from the free variables, which can
avoid confusions that may arise if bound and free variables have the
same names.
-->

在此之中 `y` 是约束变量，`x` 是自由变量。**Barendregt 惯例**，一个常见的惯例，使用 α-重命名
来保证约束变量与自由变量完全不同。这样可以避免因为约束变量和自由变量名称相同而造成的混乱。

<!--
Case and recursion also introduce bound variables, which are also subject
to alpha renaming. In the term
-->

匹配和递归同样引入了约束变量，我们也可以使用 α-重命名。下面的项

    μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m"
        [zero⇒ ` "n"
        |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]

<!--
notice that there are two binding occurrences of `m`, one in the first
line and one in the last line.  It is equivalent to the following term,
-->

注意这个项包括了两个 `m` 的不同绑定，第一次出现在第一行，第二次出现在最后一行。
这个项与下面的项等同

    μ "plus" ⇒ ƛ "x" ⇒ ƛ "y" ⇒
      case ` "x"
        [zero⇒ ` "y"
        |suc "x′" ⇒ `suc (` "plus" · ` "x′" · ` "y") ]

<!--
where the two binding occurrences corresponding to `m` now have distinct
names, `x` and `x′`.
-->

其中两次出现的 `m` 现在用 `x` 和 `x′` 两个不同的名字表示。

<!--
## Values
-->

## 值

<!--
A _value_ is a term that corresponds to an answer.
Thus, `` `suc `suc `suc `suc `zero `` is a value,
while `` plus · two · two `` is not.
Following convention, we treat all function abstractions
as values; thus, `` plus `` by itself is considered a value.
-->

**值**（Value）是一个对应着答案的项。
因此，`` `suc `suc `suc `suc `zero `` 是一个值，
而 `` plus · two · two `` 不是。
根据惯例，我们将所有的抽象当作值；所以 `` plus ``本身是一个值。

<!--
The predicate `Value M` holds if term `M` is a value:
-->

谓词 `Value M` 当一个项 `M` 是一个值时成立：

```
data Value : Term → Set where

  V-ƛ : ∀ {x N}
      ---------------
    → Value (ƛ x ⇒ N)

  V-zero :
      -----------
      Value `zero

  V-suc : ∀ {V}
    → Value V
      --------------
    → Value (`suc V)
```

<!--
In what follows, we let `V` and `W` range over values.
-->

后续文中，我们用 `V` 和 `W` 来表示值。

<!--
### Formal vs informal
-->

### 正式与非正式

<!--
In informal presentations of formal semantics, using
`V` as the name of a metavariable is sufficient to
indicate that it is a value. In Agda, we must explicitly
invoke the `Value` predicate.
-->

在形式化语义的非正式表达中，我们用元变量 `V` 来表示一个值。
在 Agda 中，我们必须使用 `Value` 谓词来显式地表达。

<!--
### Other approaches
-->

### 其他方法

<!--
An alternative is not to focus on closed terms,
to treat variables as values, and to treat
`ƛ x ⇒ N` as a value only if `N` is a value.
Indeed, this is how Agda normalises terms.
We consider this approach in
Chapter [Untyped](/Untyped/).
-->

另一种定义不注重封闭的项，将变量视作值。
`ƛ x ⇒ N` 只有在 `N` 是一个值的时候，才是一个值。
这是 Agda 标准化项的方法，我们在
[Untyped](/Untyped/) 章节中考虑这种方法。


<!--
## Substitution
-->

## 替换

<!--
The heart of lambda calculus is the operation of
substituting one term for a variable in another term.
Substitution plays a key role in defining the
operational semantics of function application.
For instance, we have
-->

λ-演算的核心操作是将一个项中的变量用另一个项来替换。
替换在定义函数应用的操作语义中起到了重要的作用。
比如说，我们有

      (ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) · sucᶜ · `zero
    —→
      (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
    —→
      sucᶜ · (sucᶜ · `zero)

<!--
where we substitute `sucᶜ` for `` ` "s" `` and `` `zero `` for `` ` "z" ``
in the body of the function abstraction.
-->

其中，我们在抽象体中用 `sucᶜ` 替换 `` ` "s" ``，用 `` `zero `` 替换 `` ` "z" ``。

<!--
We write substitution as `N [ x := V ]`, meaning
"substitute term `V` for free occurrences of variable `x` in term `N`",
or, more compactly, "substitute `V` for `x` in `N`",
or equivalently, "in `N` replace `x` by `V`".
Substitution works if `V` is any closed term;
it need not be a value, but we use `V` since in fact we
usually substitute values.
-->

我们将替换写作 `N [ x := V ]`，意为用 `V` 来替换项 `N` 中出现的所有自由变量 `x`。
简短地说，就是用 `V` 来替换 `N` 中的 `x`，或者是把 `N` 中的 `x` 换成 `V`。
替换只在 `V` 是一个封闭项时有效。它不一定是一个值，我们在这里使用 `V` 是因为
常常我们使用值进行替换。

<!--
Here are some examples:
-->

下面是一些例子：

<!--
* `` (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] `` yields
  `` ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z") ``.
* `` (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] `` yields
  `` sucᶜ · (sucᶜ · `zero) ``.
* `` (ƛ "x" ⇒ ` "y") [ "y" := `zero ] `` yields `` ƛ "x" ⇒ `zero ``.
* `` (ƛ "x" ⇒ ` "x") [ "x" := `zero ] `` yields `` ƛ "x" ⇒ ` "x" ``.
* `` (ƛ "y" ⇒ ` "y") [ "x" := `zero ] `` yields `` ƛ "y" ⇒ ` "y" ``.
-->


* `` (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] `` 得
  `` ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z") ``。
* `` (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] `` 得
  `` sucᶜ · (sucᶜ · `zero) ``。
* `` (ƛ "x" ⇒ ` "y") [ "y" := `zero ] `` 得 `` ƛ "x" ⇒ `zero ``。
* `` (ƛ "x" ⇒ ` "x") [ "x" := `zero ] `` 得 `` ƛ "x" ⇒ ` "x" ``。
* `` (ƛ "y" ⇒ ` "y") [ "x" := `zero ] `` 得 `` ƛ "y" ⇒ ` "y" ``。

<!--
In the last but one example, substituting `` `zero `` for `x` in
`` ƛ "x" ⇒ ` "x" `` does _not_ yield `` ƛ "x" ⇒ `zero ``,
since `x` is bound in the lambda abstraction.
The choice of bound names is irrelevant: both
`` ƛ "x" ⇒ ` "x" `` and `` ƛ "y" ⇒ ` "y" `` stand for the
identity function.  One way to think of this is that `x` within
the body of the abstraction stands for a _different_ variable than
`x` outside the abstraction, they just happen to have the same name.
-->

在倒数第二个例子中，用 `` `zero `` 在
`` ƛ "x" ⇒ ` "x" `` 出现的 `x` 得到的**不是** `` ƛ "x" ⇒ `zero ``，
因为 `x` 是抽象中的约束变量。
约束变量的名称是无关的，
`` ƛ "x" ⇒ ` "x" `` 和 `` ƛ "y" ⇒ ` "y" `` 都是恒等函数。
可以认为 `x` 在抽象体内和抽象体外是**不同的**变量，而它们恰好拥有一样的名字。

<!--
We will give a definition of substitution that is only valid
when term substituted for the variable is closed. This is because
substitution by terms that are _not_ closed may require renaming
of bound variables. For example:
-->

我们将要给出替换的定义在用来替换变量的项是封闭时有效。
这是因为用**不**封闭的项可能需要对于约束变量进行重命名。例如：

<!--
* `` (ƛ "x" ⇒ ` "x" · ` "y") [ "y" := ` "x" · `zero] `` should not yield <br/>
  `` (ƛ "x" ⇒ ` "x" · (` "x" · `zero)) ``.
-->

* `` (ƛ "x" ⇒ ` "x" · ` "y") [ "y" := ` "x" · `zero] `` 不应该得到 <br/>
  `` (ƛ "x" ⇒ ` "x" · (` "x" · `zero)) ``.

<!--
Instead, we should rename the bound variable to avoid capture:
-->

不同如上，我们应该将约束变量进行重命名，来防止捕获：

<!--
* `` (ƛ "x" ⇒ ` "x" · ` "y") [ "y" := ` "x" · `zero ] `` should yield <br/>
  `` ƛ "x′" ⇒ ` "x′" · (` "x" · `zero) ``.
-->

* `` (ƛ "x" ⇒ ` "x" · ` "y") [ "y" := ` "x" · `zero ] `` 应该得到 <br/>
  `` ƛ "x′" ⇒ ` "x′" · (` "x" · `zero) ``.

<!--
Here `x′` is a fresh variable distinct from `x`.
Formal definition of substitution with suitable renaming is considerably
more complex, so we avoid it by restricting to substitution by closed terms,
which will be adequate for our purposes.
-->

这里的 `x′` 是一个新的、不同于 `x` 的变量。
带有重命名的替换的形式化定义更加复杂。在这里，我们将替换限制在封闭的项之内，
可以避免重命名的问题，但对于我们要做的后续的内容来说也是足够的。

<!--
Here is the formal definition of substitution by closed terms in Agda:
-->

下面是对于封闭项替换的 Agda 定义：

```
infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _          =  V
... | no  _          =  ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _          =  ƛ x ⇒ N
... | no  _          =  ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ]   =  L [ y := V ] · M [ y := V ]
(`zero) [ y := V ]   =  `zero
(`suc M) [ y := V ]  =  `suc M [ y := V ]
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
... | yes _          =  case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no  _          =  case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _          =  μ x ⇒ N
... | no  _          =  μ x ⇒ N [ y := V ]
```

<!--
Let's unpack the first three cases:
-->

下面我们来看一看前三个情况：

<!--
* For variables, we compare `y`, the substituted variable,
with `x`, the variable in the term. If they are the same,
we yield `V`, otherwise we yield `x` unchanged.
-->

* 对于变量，我们将需要替换的变量 `y` 与项中的变量 `x` 进行比较。
如果它们相同，我们返回 `V`，否则返回 `x` 不变。

<!--
* For abstractions, we compare `y`, the substituted variable,
with `x`, the variable bound in the abstraction. If they are the same,
we yield the abstraction unchanged, otherwise we substitute inside the body.
-->

* 对于抽象，我们将需要替换的变量 `y` 与抽象中的约束变量 `x` 进行比较。
如果它们相同，我们返回抽象不变，否则对于抽象体内部进行替换。

<!--
* For application, we recursively substitute in the function
and the argument.
-->

* 对于应用，我们递归地替换函数和其参数。

<!--
Case expressions and recursion also have bound variables that are
treated similarly to those in lambda abstractions.  Otherwise we
simply push substitution recursively into the subterms.
-->

匹配表达式和递归也有约束变量，我们使用与抽象相似的方法处理它们。
除此之外的情况，我们递归地对于子项进行替换。

<!--
### Examples
-->

### 例子

<!--
Here is confirmation that the examples above are correct:
-->

下面是上述替换正确性的证明：

```
_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] ≡ ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
_ = refl

_ : (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] ≡ sucᶜ · (sucᶜ · `zero)
_ = refl

_ : (ƛ "x" ⇒ ` "y") [ "y" := `zero ] ≡ ƛ "x" ⇒ `zero
_ = refl

_ : (ƛ "x" ⇒ ` "x") [ "x" := `zero ] ≡ ƛ "x" ⇒ ` "x"
_ = refl

_ : (ƛ "y" ⇒ ` "y") [ "x" := `zero ] ≡ ƛ "y" ⇒ ` "y"
_ = refl
```

<!--
#### Quiz
-->

#### 小测验

<!--
What is the result of the following substitution?
-->

下面替换的结束是？

    (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ ` "x")) [ "x" := `zero ]

1. `` (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ ` "x")) ``
2. `` (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ `zero)) ``
3. `` (ƛ "y" ⇒ `zero · (ƛ "x" ⇒ ` "x")) ``
4. `` (ƛ "y" ⇒ `zero · (ƛ "x" ⇒ `zero)) ``

<!--
#### Exercise `_[_:=_]′` (stretch)
-->

#### 练习 `_[_:=_]′` （延伸）

<!--
The definition of substitution above has three clauses (`ƛ`, `case`,
and `μ`) that invoke a `with` clause to deal with bound variables.
Rewrite the definition to factor the common part of these three
clauses into a single function, defined by mutual recursion with
substitution.
-->

上面的替换定义中有三条语句（`ƛ`、 `case` 和 `μ`） 使用了 `with` 语句来处理约束变量。
将上述语句的共同部分提取成一个函数，然后用共同递归重写替换的定义。

<!--
```
-- Your code goes here
```
-->

```
-- 请将代码写在此处。
```


## Reduction

We give the reduction rules for call-by-value lambda calculus.  To
reduce an application, first we reduce the left-hand side until it
becomes a value (which must be an abstraction); then we reduce the
right-hand side until it becomes a value; and finally we substitute
the argument for the variable in the abstraction.

In an informal presentation of the operational semantics,
the rules for reduction of applications are written as follows:

    L —→ L′
    --------------- ξ-·₁
    L · M —→ L′ · M

    M —→ M′
    --------------- ξ-·₂
    V · M —→ V · M′

    ----------------------------- β-ƛ
    (ƛ x ⇒ N) · V —→ N [ x := V ]

The Agda version of the rules below will be similar, except that universal
quantifications are made explicit, and so are the predicates that indicate
which terms are values.

The rules break into two sorts. Compatibility rules direct us to
reduce some part of a term.  We give them names starting with the
Greek letter `ξ` (_xi_).  Once a term is sufficiently reduced, it will
consist of a constructor and a deconstructor, in our case `ƛ` and `·`,
which reduces directly.  We give them names starting with the Greek
letter `β` (_beta_) and such rules are traditionally called _beta rules_.

A bit of terminology: A term that matches the left-hand side of a
reduction rule is called a _redex_. In the redex `(ƛ x ⇒ N) · V`, we
may refer to `x` as the _formal parameter_ of the function, and `V`
as the _actual parameter_ of the function application.  Beta reduction
replaces the formal parameter by the actual parameter.

If a term is a value, then no reduction applies; conversely,
if a reduction applies to a term then it is not a value.
We will show in the next chapter that
this exhausts the possibilities: every well-typed term
either reduces or is a value.

For numbers, zero does not reduce and successor reduces the subterm.
A case expression reduces its argument to a number, and then chooses
the zero or successor branch as appropriate.  A fixpoint replaces
the bound variable by the entire fixpoint term; this is the one
case where we substitute by a term that is not a value.

Here are the rules formalised in Agda:

```
infix 4 _—→_

data _—→_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
      -----------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M —→ M′
      -----------------
    → V · M —→ V · M′

  β-ƛ : ∀ {x N V}
    → Value V
      ------------------------------
    → (ƛ x ⇒ N) · V —→ N [ x := V ]

  ξ-suc : ∀ {M M′}
    → M —→ M′
      ------------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {x L L′ M N}
    → L —→ L′
      -----------------------------------------------------------------
    → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]

  β-zero : ∀ {x M N}
      ----------------------------------------
    → case `zero [zero⇒ M |suc x ⇒ N ] —→ M

  β-suc : ∀ {x V M N}
    → Value V
      ---------------------------------------------------
    → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]

  β-μ : ∀ {x M}
      ------------------------------
    → μ x ⇒ M —→ M [ x := μ x ⇒ M ]
```

The reduction rules are carefully designed to ensure that subterms
of a term are reduced to values before the whole term is reduced.
This is referred to as _call-by-value_ reduction.

Further, we have arranged that subterms are reduced in a
left-to-right order.  This means that reduction is _deterministic_:
for any term, there is at most one other term to which it reduces.
Put another way, our reduction relation `—→` is in fact a function.

This style of explaining the meaning of terms is called
a _small-step operational semantics_.  If `M —→ N`, we say that
term `M` _reduces_ to term `N`, or equivalently,
term `M` _steps_ to term `N`.  Each compatibility rule has
another reduction rule in its premise; so a step always consists
of a beta rule, possibly adjusted by zero or more compatibility rules.


#### Quiz

What does the following term step to?

    (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")  —→  ???

1.  `` (ƛ "x" ⇒ ` "x") ``
2.  `` (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ``
3.  `` (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ``

What does the following term step to?

    (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")  —→  ???

1.  `` (ƛ "x" ⇒ ` "x") ``
2.  `` (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ``
3.  `` (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ``

What does the following term step to?  (Where `twoᶜ` and `sucᶜ` are as
defined above.)

    twoᶜ · sucᶜ · `zero  —→  ???

1.  `` sucᶜ · (sucᶜ · `zero) ``
2.  `` (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero ``
3.  `` `zero ``


## Reflexive and transitive closure

A single step is only part of the story. In general, we wish to repeatedly
step a closed term until it reduces to a value.  We do this by defining
the reflexive and transitive closure `—↠` of the step relation `—→`.

We define reflexive and transitive closure as a sequence of zero or
more steps of the underlying relation, along lines similar to that for
reasoning about chains of equalities in
Chapter [Equality](/Equality/):
```
infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : Term → Term → Set where
  _∎ : ∀ M
      ---------
    → M —↠ M

  _—→⟨_⟩_ : ∀ L {M N}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

begin_ : ∀ {M N}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N
```
We can read this as follows:

* From term `M`, we can take no steps, giving a step of type `M —↠ M`.
  It is written `M ∎`.

* From term `L` we can take a single step of type `L —→ M` followed by zero
  or more steps of type `M —↠ N`, giving a step of type `L —↠ N`. It is
  written `L —→⟨ L—→M ⟩ M—↠N`, where `L—→M` and `M—↠N` are steps of the
  appropriate type.

The notation is chosen to allow us to lay out example reductions in an
appealing way, as we will see in the next section.

An alternative is to define reflexive and transitive closure directly,
as the smallest relation that includes `—→` and is also reflexive
and transitive.  We could do so as follows:
```
data _—↠′_ : Term → Term → Set where

  step′ : ∀ {M N}
    → M —→ N
      -------
    → M —↠′ N

  refl′ : ∀ {M}
      -------
    → M —↠′ M

  trans′ : ∀ {L M N}
    → L —↠′ M
    → M —↠′ N
      -------
    → L —↠′ N
```
The three constructors specify, respectively, that `—↠′` includes `—→`
and is reflexive and transitive.  A good exercise is to show that
the two definitions are equivalent (indeed, one embeds in the other).

#### Exercise `—↠≲—↠′` (practice)

Show that the first notion of reflexive and transitive closure
above embeds into the second. Why are they not isomorphic?

```
-- Your code goes here
```

## Confluence

One important property a reduction relation might satisfy is
to be _confluent_.  If term `L` reduces to two other terms,
`M` and `N`, then both of these reduce to a common term `P`.
It can be illustrated as follows:

               L
              / \
             /   \
            /     \
           M       N
            \     /
             \   /
              \ /
               P

Here `L`, `M`, `N` are universally quantified while `P`
is existentially quantified.  If each line stands for zero
or more reduction steps, this is called confluence,
while if the top two lines stand for a single reduction
step and the bottom two stand for zero or more reduction
steps it is called the diamond property. In symbols:

```
postulate
  confluence : ∀ {L M N}
    → ((L —↠ M) × (L —↠ N))
      --------------------
    → ∃[ P ] ((M —↠ P) × (N —↠ P))

  diamond : ∀ {L M N}
    → ((L —→ M) × (L —→ N))
      --------------------
    → ∃[ P ] ((M —↠ P) × (N —↠ P))
```

The reduction system studied in this chapter is deterministic.
In symbols:

```
postulate
  deterministic : ∀ {L M N}
    → L —→ M
    → L —→ N
      ------
    → M ≡ N
```

It is easy to show that every deterministic relation satisfies
the diamond and confluence properties. Hence, all the reduction
systems studied in this text are trivially confluent.


## Examples

We start with a simple example. The Church numeral two applied to the
successor function and zero yields the natural number two:
```
_ : twoᶜ · sucᶜ · `zero —↠ `suc `suc `zero
_ =
  begin
    twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
  —→⟨ β-ƛ V-zero ⟩
    sucᶜ · (sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    sucᶜ · `suc `zero
  —→⟨ β-ƛ (V-suc V-zero) ⟩
    `suc (`suc `zero)
  ∎
```

Here is a sample reduction demonstrating that two plus two is four:
```
_ : plus · two · two —↠ `suc `suc `suc `suc `zero
_ =
  begin
    plus · two · two
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · two · two
  —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    (ƛ "n" ⇒
      case two [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
         · two
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    case two [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ]
  —→⟨ β-suc (V-suc V-zero) ⟩
    `suc (plus · `suc `zero · two)
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc ((ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · `suc `zero · two)
  —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
    `suc ((ƛ "n" ⇒
      case `suc `zero [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · two)
  —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
    `suc (case `suc `zero [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ])
  —→⟨ ξ-suc (β-suc V-zero) ⟩
    `suc `suc (plus · `zero · two)
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
    `suc `suc ((ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · `zero · two)
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
    `suc `suc ((ƛ "n" ⇒
      case `zero [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · two)
  —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
    `suc `suc (case `zero [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ])
  —→⟨ ξ-suc (ξ-suc β-zero) ⟩
    `suc (`suc (`suc (`suc `zero)))
  ∎
```

And here is a similar sample reduction for Church numerals:
```
_ : plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero —↠ `suc `suc `suc `suc `zero
_ =
  begin
    (ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ ` "m" · ` "s" · (` "n" · ` "s" · ` "z"))
      · twoᶜ · twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ))) ⟩
    (ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ twoᶜ · ` "s" · (` "n" · ` "s" · ` "z"))
      · twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "s" ⇒ ƛ "z" ⇒ twoᶜ · ` "s" · (twoᶜ · ` "s" · ` "z")) · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ twoᶜ · sucᶜ · (twoᶜ · sucᶜ · ` "z")) · `zero
  —→⟨ β-ƛ V-zero ⟩
    twoᶜ · sucᶜ · (twoᶜ · sucᶜ · `zero)
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (twoᶜ · sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · ((ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (sucᶜ · (sucᶜ · `zero))
  —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ V-zero)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (sucᶜ · (`suc `zero))
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (`suc `suc `zero)
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    sucᶜ · (sucᶜ · `suc `suc `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    sucᶜ · (`suc `suc `suc `zero)
  —→⟨ β-ƛ (V-suc (V-suc (V-suc V-zero))) ⟩
   `suc (`suc (`suc (`suc `zero)))
  ∎
```

In the next chapter, we will see how to compute such reduction sequences.


#### Exercise `plus-example` (practice)

Write out the reduction sequence demonstrating that one plus one is two.

```
-- Your code goes here
```


## Syntax of types

We have just two types:

  * Functions, `A ⇒ B`
  * Naturals, `` `ℕ ``

As before, to avoid overlap we use variants of the names used by Agda.

Here is the syntax of types in BNF:

    A, B, C  ::=  A ⇒ B | `ℕ

And here it is formalised in Agda:

```
infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type
```

### Precedence

As in Agda, functions of two or more arguments are represented via
currying. This is made more convenient by declaring `_⇒_` to
associate to the right and `_·_` to associate to the left.
Thus:

* ``(`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ`` stands for ``((`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ))``.
* `plus · two · two` stands for `(plus · two) · two`.

### Quiz

* What is the type of the following term?

    `` ƛ "s" ⇒ ` "s" · (` "s"  · `zero) ``

  1. `` (`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ) ``
  2. `` (`ℕ ⇒ `ℕ) ⇒ `ℕ ``
  3. `` `ℕ ⇒ (`ℕ ⇒ `ℕ) ``
  4. `` `ℕ ⇒ `ℕ ⇒ `ℕ ``
  5. `` `ℕ ⇒ `ℕ ``
  6. `` `ℕ ``

  Give more than one answer if appropriate.

* What is the type of the following term?

    `` (ƛ "s" ⇒ ` "s" · (` "s"  · `zero)) · sucᶜ ``

  1. `` (`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ) ``
  2. `` (`ℕ ⇒ `ℕ) ⇒ `ℕ ``
  3. `` `ℕ ⇒ (`ℕ ⇒ `ℕ) ``
  4. `` `ℕ ⇒ `ℕ ⇒ `ℕ ``
  5. `` `ℕ ⇒ `ℕ ``
  6. `` `ℕ ``

  Give more than one answer if appropriate.


## Typing

### Contexts

While reduction considers only closed terms, typing must
consider terms with free variables.  To type a term,
we must first type its subterms, and in particular in the
body of an abstraction its bound variable may appear free.

A _context_ associates variables with types.  We let `Γ` and `Δ` range
over contexts.  We write `∅` for the empty context, and `Γ , x ⦂ A`
for the context that extends `Γ` by mapping variable `x` to type `A`.
For example,

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ``

is the context that associates variable `` "s" `` with type `` `ℕ ⇒ `ℕ ``,
and variable `` "z" `` with type `` `ℕ ``.

Contexts are formalised as follows:

```
infixl 5  _,_⦂_

data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context
```


#### Exercise `Context-≃` (practice)

Show that `Context` is isomorphic to `List (Id × Type)`.
For instance, the isomorphism relates the context

    ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ

to the list

    [ ⟨ "z" , `ℕ ⟩ , ⟨ "s" , `ℕ ⇒ `ℕ ⟩ ]

```
-- Your code goes here
```

### Lookup judgment

We have two forms of _judgment_.  The first is written

    Γ ∋ x ⦂ A

and indicates in context `Γ` that variable `x` has type `A`.
It is called _lookup_.
For example,

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "z" ⦂ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "s" ⦂ `ℕ ⇒ `ℕ ``

give us the types associated with variables `` "z" `` and `` "s" ``,
respectively.  The symbol `∋` (pronounced "ni", for "in"
backwards) is chosen because checking that `Γ ∋ x ⦂ A` is analogous to
checking whether `x ⦂ A` appears in a list corresponding to `Γ`.

If two variables in a context have the same name, then lookup
should return the most recently bound variable, which _shadows_
the other variables.  For example,

* `` ∅ , "x" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ∋ "x" ⦂ `ℕ ``.

Here `` "x" ⦂ `ℕ ⇒ `ℕ `` is shadowed by `` "x" ⦂ `ℕ ``.

Lookup is formalised as follows:
```
infix  4  _∋_⦂_

data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
      ------------------
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
      ------------------
    → Γ , y ⦂ B ∋ x ⦂ A
```

The constructors `Z` and `S` correspond roughly to the constructors
`here` and `there` for the element-of relation `_∈_` on lists.
Constructor `S` takes an additional parameter, which ensures that
when we look up a variable that it is not _shadowed_ by another
variable with the same name to its left in the list.

It can be rather tedious to use the `S` constructor, as you have to provide
proofs that `x ≢ y` each time. For example:

```
_ : ∅ , "x" ⦂ `ℕ ⇒ `ℕ , "y" ⦂ `ℕ , "z" ⦂ `ℕ ∋ "x" ⦂ `ℕ ⇒ `ℕ
_ = S (λ()) (S (λ()) Z)
```

Instead, we'll use a "smart constructor", which uses [proof by reflection](/Decidable/#proof-by-reflection) to check the inequality while type checking:

```
S′ : ∀ {Γ x y A B}
   → {x≢y : False (x ≟ y)}
   → Γ ∋ x ⦂ A
     ------------------
   → Γ , y ⦂ B ∋ x ⦂ A

S′ {x≢y = x≢y} x = S (toWitnessFalse x≢y) x
```

### Typing judgment

The second judgment is written

    Γ ⊢ M ⦂ A

and indicates in context `Γ` that term `M` has type `A`.
Context `Γ` provides types for all the free variables in `M`.
For example:

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "z" ⦂ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" ⦂ `ℕ ⇒ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" · ` "z" ⦂  `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" · (` "s" · ` "z") ⦂  `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ ⊢ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂  `ℕ ⇒ `ℕ ``
* `` ∅ ⊢ ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂  (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ ``

Typing is formalised as follows:
```
infix  4  _⊢_⦂_

data _⊢_⦂_ : Context → Term → Type → Set where

  -- Axiom
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A

  -- ⇒-I
  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ⦂ B
      -------------------
    → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B

  -- ⇒-E
  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

  -- ℕ-I₁
  ⊢zero : ∀ {Γ}
      --------------
    → Γ ⊢ `zero ⦂ `ℕ

  -- ℕ-I₂
  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ⦂ `ℕ
      ---------------
    → Γ ⊢ `suc M ⦂ `ℕ

  -- ℕ-E
  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ⦂ `ℕ
    → Γ ⊢ M ⦂ A
    → Γ , x ⦂ `ℕ ⊢ N ⦂ A
      -------------------------------------
    → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ⦂ A

  ⊢μ : ∀ {Γ x M A}
    → Γ , x ⦂ A ⊢ M ⦂ A
      -----------------
    → Γ ⊢ μ x ⇒ M ⦂ A
```

Each type rule is named after the constructor for the
corresponding term.

Most of the rules have a second name, derived from a convention in
logic, whereby the rule is named after the type connective that it
concerns; rules to introduce and to eliminate each connective are
labeled `-I` and `-E`, respectively. As we read the rules from top to
bottom, introduction and elimination rules do what they say on the
tin: the first _introduces_ a formula for the connective, which
appears in the conclusion but not in the premises; while the second
_eliminates_ a formula for the connective, which appears in a premise
but not in the conclusion. An introduction rule describes how to
construct a value of the type (abstractions yield functions, successor
and zero yield naturals), while an elimination rule describes how to
deconstruct a value of the given type (applications use functions,
case expressions use naturals).

Note also the three places (in `⊢ƛ`, `⊢case`, and `⊢μ`) where the
context is extended with `x` and an appropriate type, corresponding to
the three places where a bound variable is introduced.

The rules are deterministic, in that at most one rule applies to every term.


### Example type derivations {#derivation}

Type derivations correspond to trees. In informal notation, here
is a type derivation for the Church numeral two,

                            ∋s                     ∋z
                            ------------------ ⊢`  -------------- ⊢`
    ∋s                      Γ₂ ⊢ ` "s" ⦂ A ⇒ A     Γ₂ ⊢ ` "z" ⦂ A
    ------------------ ⊢`   ------------------------------------- _·_
    Γ₂ ⊢ ` "s" ⦂ A ⇒ A      Γ₂ ⊢ ` "s" · ` "z" ⦂ A
    ---------------------------------------------- _·_
    Γ₂ ⊢ ` "s" · (` "s" · ` "z") ⦂ A
    -------------------------------------------- ⊢ƛ
    Γ₁ ⊢ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂ A ⇒ A
    ------------------------------------------------------------- ⊢ƛ
    Γ ⊢ ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂ (A ⇒ A) ⇒ A ⇒ A

where `∋s` and `∋z` abbreviate the two derivations,

                 ---------------- Z
    "s" ≢ "z"    Γ₁ ∋ "s" ⦂ A ⇒ A
    ----------------------------- S       ------------- Z
    Γ₂ ∋ "s" ⦂ A ⇒ A                       Γ₂ ∋ "z" ⦂ A

and where `Γ₁ = Γ , "s" ⦂ A ⇒ A` and `Γ₂ = Γ , "s" ⦂ A ⇒ A , "z" ⦂ A`.
The typing derivation is valid for any `Γ` and `A`, for instance,
we might take `Γ` to be `∅` and `A` to be `` `ℕ ``.

Here is the above typing derivation formalised in Agda:
```
Ch : Type → Type
Ch A = (A ⇒ A) ⇒ A ⇒ A

⊢twoᶜ : ∀ {Γ A} → Γ ⊢ twoᶜ ⦂ Ch A
⊢twoᶜ = ⊢ƛ (⊢ƛ (⊢` ∋s · (⊢` ∋s · ⊢` ∋z)))
  where
  ∋s = S′ Z
  ∋z = Z
```

Here are the typings corresponding to computing two plus two:
```
⊢two : ∀ {Γ} → Γ ⊢ two ⦂ `ℕ
⊢two = ⊢suc (⊢suc ⊢zero)

⊢plus : ∀ {Γ} → Γ ⊢ plus ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢plus = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` ∋m) (⊢` ∋n)
         (⊢suc (⊢` ∋+ · ⊢` ∋m′ · ⊢` ∋n′)))))
  where
  ∋+  = S′ (S′ (S′ Z))
  ∋m  = S′ Z
  ∋n  = Z
  ∋m′ = Z
  ∋n′ = S′ Z

⊢2+2 : ∅ ⊢ plus · two · two ⦂ `ℕ
⊢2+2 = ⊢plus · ⊢two · ⊢two
```
In contrast to our earlier examples, here we have typed `two` and `plus`
in an arbitrary context rather than the empty context; this makes it easy
to use them inside other binding contexts as well as at the top level.
Here the two lookup judgments `∋m` and `∋m′` refer to two different
bindings of variables named `"m"`.  In contrast, the two judgments `∋n` and
`∋n′` both refer to the same binding of `"n"` but accessed in different
contexts, the first where `"n"` is the last binding in the context, and
the second after `"m"` is bound in the successor branch of the case.

And here are typings for the remainder of the Church example:
```
⊢plusᶜ : ∀ {Γ A} → Γ  ⊢ plusᶜ ⦂ Ch A ⇒ Ch A ⇒ Ch A
⊢plusᶜ = ⊢ƛ (⊢ƛ (⊢ƛ (⊢ƛ (⊢` ∋m · ⊢` ∋s · (⊢` ∋n · ⊢` ∋s · ⊢` ∋z)))))
  where
  ∋m = S′ (S′ (S′ Z))
  ∋n = S′ (S′ Z)
  ∋s = S′ Z
  ∋z = Z

⊢sucᶜ : ∀ {Γ} → Γ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ
⊢sucᶜ = ⊢ƛ (⊢suc (⊢` ∋n))
  where
  ∋n = Z

⊢2+2ᶜ : ∅ ⊢ plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero ⦂ `ℕ
⊢2+2ᶜ = ⊢plusᶜ · ⊢twoᶜ · ⊢twoᶜ · ⊢sucᶜ · ⊢zero
```

### Interaction with Agda

Construction of a type derivation may be done interactively.
Start with the declaration:

    ⊢sucᶜ : ∅ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ
    ⊢sucᶜ = ?

Typing C-c C-l causes Agda to create a hole and tell us its expected type:

    ⊢sucᶜ = { }0
    ?0 : ∅ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ

Now we fill in the hole by typing C-c C-r. Agda observes that
the outermost term in `sucᶜ` is `ƛ`, which is typed using `⊢ƛ`. The
`⊢ƛ` rule in turn takes one argument, which Agda leaves as a hole:

    ⊢sucᶜ = ⊢ƛ { }1
    ?1 : ∅ , "n" ⦂ `ℕ ⊢ `suc ` "n" ⦂ `ℕ

We can fill in the hole by typing C-c C-r again:

    ⊢sucᶜ = ⊢ƛ (⊢suc { }2)
    ?2 : ∅ , "n" ⦂ `ℕ ⊢ ` "n" ⦂ `ℕ

And again:

    ⊢sucᶜ = ⊢ƛ (⊢suc (⊢` { }3))
    ?3 : ∅ , "n" ⦂ `ℕ ∋ "n" ⦂ `ℕ

A further attempt with C-c C-r yields the message:

    Don't know which constructor to introduce of Z or S

We can fill in `Z` by hand. If we type C-c C-space, Agda will confirm we are done:

    ⊢sucᶜ = ⊢ƛ (⊢suc (⊢` Z))

The entire process can be automated using Agsy, invoked with C-c C-a.

Chapter [Inference](/Inference/)
will show how to use Agda to compute type derivations directly.


### Lookup is injective

The lookup relation `Γ ∋ x ⦂ A` is injective, in that for each `Γ` and `x`
there is at most one `A` such that the judgment holds:
```
∋-injective : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
∋-injective Z        Z          =  refl
∋-injective Z        (S x≢ _)   =  ⊥-elim (x≢ refl)
∋-injective (S x≢ _) Z          =  ⊥-elim (x≢ refl)
∋-injective (S _ ∋x) (S _ ∋x′)  =  ∋-injective ∋x ∋x′
```

The typing relation `Γ ⊢ M ⦂ A` is not injective. For example, in any `Γ`
the term `` ƛ "x" ⇒ ` "x" `` has type `A ⇒ A` for any type `A`.

### Non-examples

We can also show that terms are _not_ typeable.  For example, here is
a formal proof that it is not possible to type the term
`` `zero · `suc `zero ``.  It cannot be typed, because doing so
requires that the first term in the application is both a natural and
a function:

```
nope₁ : ∀ {A} → ¬ (∅ ⊢ `zero · `suc `zero ⦂ A)
nope₁ (() · _)
```

As a second example, here is a formal proof that it is not possible to
type `` ƛ "x" ⇒ ` "x" · ` "x" ``. It cannot be typed, because
doing so requires types `A` and `B` such that `A ⇒ B ≡ A`:

```
nope₂ : ∀ {A} → ¬ (∅ ⊢ ƛ "x" ⇒ ` "x" · ` "x" ⦂ A)
nope₂ (⊢ƛ (⊢` ∋x · ⊢` ∋x′))  =  contradiction (∋-injective ∋x ∋x′)
  where
  contradiction : ∀ {A B} → ¬ (A ⇒ B ≡ A)
  contradiction ()
```


#### Quiz

For each of the following, give a type `A` for which it is derivable,
or explain why there is no such `A`.

1. `` ∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ ` "y" · ` "x" ⦂ A ``
2. `` ∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ ` "x" · ` "y" ⦂ A ``
3. `` ∅ , "y" ⦂ `ℕ ⇒ `ℕ ⊢ ƛ "x" ⇒ ` "y" · ` "x" ⦂ A ``

For each of the following, give types `A`, `B`, and `C` for which it is derivable,
or explain why there are no such types.

1. `` ∅ , "x" ⦂ A ⊢ ` "x" · ` "x" ⦂ B ``
2. `` ∅ , "x" ⦂ A , "y" ⦂ B ⊢ ƛ "z" ⇒ ` "x" · (` "y" · ` "z") ⦂ C ``


#### Exercise `⊢mul` (recommended)

Using the term `mul` you defined earlier, write out the derivation
showing that it is well typed.

```
-- Your code goes here
```


#### Exercise `⊢mulᶜ` (practice)

Using the term `mulᶜ` you defined earlier, write out the derivation
showing that it is well typed.

```
-- Your code goes here
```


## Unicode

This chapter uses the following unicode:

    ⇒  U+21D2  RIGHTWARDS DOUBLE ARROW (\=>)
    ƛ  U+019B  LATIN SMALL LETTER LAMBDA WITH STROKE (\Gl-)
    ·  U+00B7  MIDDLE DOT (\cdot)
    ≟  U+225F  QUESTIONED EQUAL TO (\?=)
    —  U+2014  EM DASH (\em)
    ↠  U+21A0  RIGHTWARDS TWO HEADED ARROW (\rr-)
    ξ  U+03BE  GREEK SMALL LETTER XI (\Gx or \xi)
    β  U+03B2  GREEK SMALL LETTER BETA (\Gb or \beta)
    Γ  U+0393  GREEK CAPITAL LETTER GAMMA (\GG or \Gamma)
    ≠  U+2260  NOT EQUAL TO (\=n or \ne)
    ∋  U+220B  CONTAINS AS MEMBER (\ni)
    ∅  U+2205  EMPTY SET (\0)
    ⊢  U+22A2  RIGHT TACK (\vdash or \|-)
    ⦂  U+2982  Z NOTATION TYPE COLON (\:)
    😇  U+1F607  SMILING FACE WITH HALO
    😈  U+1F608  SMILING FACE WITH HORNS

We compose reduction `—→` from an em dash `—` and an arrow `→`.
Similarly for reflexive and transitive closure `—↠`.
