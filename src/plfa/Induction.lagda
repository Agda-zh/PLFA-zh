---
title     : "Induction: 归纳证明"
layout    : page
prev      : /Naturals/
permalink : /Induction/
next      : /Relations/
translators : ["Oling Cat"]
progress  : 100
---

\begin{code}
module plfa.Induction where
\end{code}

{::comment}
> Induction makes you feel guilty for getting something out of nothing
> ... but it is one of the greatest ideas of civilization.
> -- Herbert Wilf
{:/}

> 归纳会让你对无中生有感到内疚
> ... 但它却是文明中最伟大的思想之一。
> -- Herbert Wilf

{::comment}
Now that we've defined the naturals and operations upon them, our next
step is to learn how to prove properties that they satisfy.  As hinted
by their name, properties of _inductive datatypes_ are proved by
_induction_.
{:/}

现在我们定义了自然数及其运算，下一步是学习如何证明它们满足的性质。
如其名称所示，**归纳数据类型（inductive datatype）**是通过**归纳（induction）**
来证明的。

{::comment}
## Imports
{:/}

## 导入

{::comment}
We require equality as in the previous chapter, plus the naturals
and some operations upon them.  We also import a couple of new operations,
`cong`, `sym`, and `_≡⟨_⟩_`, which are explained below:
{:/}

我们需要上一章中的相等性，加上自然数及其运算。我们还导入了一些新的运算：
`cong`、`sym` 和 `_≡⟨_⟩_`，之后会解释它们：

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
\end{code}


{::comment}
## Properties of operators
{:/}

## 运算符的性质

{::comment}
Operators pop up all the time, and mathematicians have agreed
on names for some of the most common properties.
{:/}

运算符总是到处出现，而数学家们已经统一了一些最常见的性质的名称。

{::comment}
* _Identity_.   Operator `+` has left identity `0` if `0 + n ≡ n`, and
  right identity `0` if `n + 0 ≡ n`, for all `n`. A value that is both
  a left and right identity is just called an identity. Identity is also
  sometimes called _unit_.

* _Associativity_.   Operator `+` is associative if the location
  of parentheses does not matter: `(m + n) + p ≡ m + (n + p)`,
  for all `m`, `n`, and `p`.

* _Commutativity_.   Operator `+` is commutative if order of
  arguments does not matter: `m + n ≡ n + m`, for all `m` and `n`.

* _Distributivity_.   Operator `*` distributes over operator `+` from the
  left if `(m + n) * p ≡ (m * p) + (n * p)`, for all `m`, `n`, and `p`,
  and from the right if `m * (p + q) ≡ (m * p) + (m * q)`, for all `m`,
  `p`, and `q`.
{:/}

* **幺元（Identity）**。对于所有的 `n`，若 `0 + n ≡ n`，则 `+` 有左幺元 `0`；
  若 `n + 0 ≡ n`，则 `+` 有右幺元 `0`。同时为左幺元和右幺元的值称简称幺元。
  幺元有时也称作**单位元（Unit）**。

* **结合律（Associativity）**。若括号的位置无关紧要，则称运算符 `+` 满足结合律，
  即对于所有的 `m`、`n` 和 `p`，有 `(m + n) + p ≡ m + (n + p)`。

* **交换律（Commutativity）**。若参数的位置无关紧要，则称运算符 `+` 满足交换律，
  即对于所有的 `m` 和 `n`，有 `m + n ≡ n + m`。

* **分配率（Distributivity）**。对于所有的 `m`、`n` 和 `p`，若
  `(m + n) * p ≡ (m * p) + (n * p)`，则运算符 `*` 对运算符 `+` 满足左分配率；
  对于所有的 `m`、`n` 和 `p`，若 `m * (p + q) ≡ (m * p) + (m * q)`，则满足右分配率。

{::comment}
Addition has identity `0` and multiplication has identity `1`;
addition and multiplication are both associative and commutative;
and multiplication distributes over addition.
{:/}

加法的幺元为 `0`，乘法的幺元为 `1`，加法和乘法都满足结合律和交换律，
乘法对加法满足分配率。

If you ever bump into an operator at a party, you now know how
to make small talk, by asking whether it has a unit and is
associative or commutative.  If you bump into two operators, you
might ask them if one distributes over the other.

如果你在一个舞会上碰见了一位操作员，那么你可以跟他闲聊，问问他是否有单位元，
能不能结合或者交换。如果你碰见了两位操作员，那么可以问他们某一位是否在另一位上面分布。
（作者的双关冷笑话，运算符（Operator）也有操作员的意思= =||）

{::comment}
Less frivolously, if you ever bump into an operator while reading a
technical paper, this gives you a way to orient yourself, by checking
whether or not it has an identity, is associative or commutative, or
distributes over another operator.  A careful author will often call
out these properties---or their lack---for instance by pointing out
that a newly introduced operator is associative but not commutative.
{:/}

正经来说，如果你在阅读技术论文时遇到了一个运算符，那么你可以考察它是否拥有一个幺元，
是否满足结合律或分配率，或者是否对另一个运算符满足分配率，这能为你提供一种视角。
细心的作者通常会指出它们是否满足这些性质，比如说指明一个新引入的运算符满足结合率
但不满足交换率。

{::comment}
#### Exercise `operators` {#operators}
{:/}

#### 练习：`operators` {#operators}

{::comment}
Give another example of a pair of operators that have an identity
and are associative, commutative, and distribute over one another.
{:/}

请给出另一对运算符，它们拥有一个幺元，满足结合律、交换律，且其中一个对另一个满足分配率。

{::comment}
\begin{code}
-- Your code goes here
\end{code}
{:/}

\begin{code}
-- 请将代码写在此处。
\end{code}

{::comment}
Give an example of an operator that has an identity and is
associative but is not commutative.
{:/}

请给出一个运算符的例子，它拥有幺元、满足结合律但不满足交换律。


{::comment}
## Associativity
{:/}

## 结合律

{::comment}
One property of addition is that it is _associative_, that is, that the
location of the parentheses does not matter:
{:/}

加法的一个性质是满足**结合律**，即括号的位置无关紧要：

    (m + n) + p ≡ m + (n + p)

{::comment}
Here `m`, `n`, and `p` are variables that range over all natural numbers.
{:/}

这里的 `m`、`n` 和 `p` 都是取值范围是全体自然数的变量。

{::comment}
We can test the proposition by choosing specific numbers for the three
variables:
{:/}

我们可以为这三个变量选取特定的数值来测试此命题：

\begin{code}
_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5
  ≡⟨⟩
    7 + 5
  ≡⟨⟩
    12
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    3 + (4 + 5)
  ∎
\end{code}

{::comment}
Here we have displayed the computation as a chain of equations,
one term to a line.  It is often easiest to read such chains from the top down
until one reaches the simplest term (in this case, `12`), and
then from the bottom up until one reaches the same term.
{:/}

在这里，我们将计算过程写成了等式链，一行一个式子。这样的等式链通常非常易读，
你可以从上到下，直到遇到最简形式（本例中为 `12`），也可以从下到上，直到回到同样的式子。

{::comment}
The test reveals that associativity is perhaps not as obvious as first
it appears.  Why should `7 + 5` be the same as `3 + 9`?  We might want
to gather more evidence, testing the proposition by choosing other
numbers.  But---since there are an infinite number of
naturals---testing can never be complete.  Is there any way we can be
sure that associativity holds for _all_ the natural numbers?
{:/}

该测试揭示了结合律可能没有它初看起来那么显然。为什么 `7 + 5` 与 `3 + 9` 相同？
我们可能需要手机更多证据，选择其它的数值来测试此命题。但由于自然数是无限的，
因此测试永远无法完成。那么我们还有其它可以确保结合律对于**所有**自然数都成立的方法吗？

{::comment}
The answer is yes! We can prove a property holds for all naturals using
_proof by induction_.
{:/}

答案是肯定的！我们可以用**归纳证明（Proof by Induction）**
来确保某个性质对于所有的自然数都成立。


{::comment}
## Proof by induction
{:/}

## 归纳证明

{::comment}
Recall the definition of natural numbers consists of a _base case_
which tells us that `zero` is a natural, and an _inductive case_
which tells us that if `m` is a natural then `suc m` is also a natural.
{:/}

回想自然数的定义，它由一个**起始步骤**「`zero` 是一个自然数」
和一个**归纳步骤**「若 `m` 是一个自然数，则 `suc m` 也是一个自然数」构成。

{::comment}
Proof by induction follows the structure of this definition.  To prove
a property of natural numbers by induction, we need to prove two cases.
First is the _base case_, where we show the property holds for `zero`.
Second is the _inductive case_, where we assume the property holds for
an arbitrary natural `m` (we call this the _inductive hypothesis_), and
then show that the property must also hold for `suc m`.
{:/}

归纳证明遵循此定义的结构。要通过归纳证明自然数的某个性质，我们需要两个步骤。
其一是**起始步骤**，我们需要证明此性质对 `zero` 成立。其二是**归纳步骤**，
我们假设此性质对一个任意自然数 `m` 成立（我们称之为**归纳假设（Induction
Hypothesis）**），然后证明该性质对 `suc m` 必定成立。

{::comment}
If we write `P m` for a property of `m`, then what we need to
demonstrate are the following two inference rules:
{:/}

若我们将 `m` 的某种性质（Property）写作 `P m`，那么我们需要证明的就是以下两个推导规则：

    ------
    P zero

    P m
    ---------
    P (suc m)

{::comment}
Let's unpack these rules.  The first rule is the base case, and
requires we show that property `P` holds for `zero`.  The second rule
is the inductive case, and requires we show that if we assume the
inductive hypothesis---namely that `P` holds for `m`---then it follows that
`P` also holds for `suc m`.
{:/}

我们来分析一下这些规则。第一条规则是起始步骤，它需要我们证明性质 `P` 对 `zero`
成立。第二条规则是归纳步骤，它需要我们证明若归纳假设「`P` 对 `m` 成立」，
那么 `P` 也对 `suc m` 成立。

{::comment}
Why does this work?  Again, it can be explained by a creation story.
To start with, we know no properties:
{:/}

为什么它能够起作用？同样，它也可以用创世故事来讲解。在最开始，我们对性质一无所知：


{::comment}
    -- In the beginning, no properties are known.
{:/}

    -- 起初，世上没有已知的性质。

{::comment}
Now, we apply the two rules to all the properties we know about.  The
base case tells us that `P zero` holds, so we add it to the set of
known properties.  The inductive case tells us that if `P m` holds (on
the day before today) then `P (suc m)` also holds (today).  We didn't
know about any properties before today, so the inductive case doesn't
apply:
{:/}

现在我们对所有已知的性质应用上述两条规则。起始步骤告诉我们 `P zero` 成立，
所以我们将它加入已知的性质集合中。归纳步骤告诉我们若（在昨天）`P m` 成立，
那么（在今天）`P (suc m)` 也成立。我们在今天之前并不知道任何性质，
因此归纳步骤在这里不适用：

{::comment}
    -- On the first day, one property is known.
    P zero
{:/}

    -- 第一天，我们知道了一个性质。
    P zero

{::comment}
Then we repeat the process, so on the next day we know about all the
properties from the day before, plus any properties added by the rules.
The base case tells us that `P zero` holds, but we already
knew that. But now the inductive case tells us that since `P zero`
held yesterday, then `P (suc zero)` holds today:
{:/}

然后我们重复此过程。在接下来的一天我们知道今天之前的所有性质，
以及任何通过此规则添加的性质。起始步骤告诉我们 `P zero`
成立，当然我们已经知道这件事了。而如今归纳步骤告诉我们，由于 `P zero`
在昨天成立，那么 `P (suc zero)` 今天也成立。

{::comment}
    -- On the second day, two properties are known.
    P zero
    P (suc zero)
{:/}

    -- 第二天，我们知道了两个性质。
    P zero
    P (suc zero)

{::comment}
And we repeat the process again. Now the inductive case
tells us that since `P zero` and `P (suc zero)` both hold, then
`P (suc zero)` and `P (suc (suc zero))` also hold. We already knew about
the first of these, but the second is new:
{:/}

我们再重复此过程。现在归纳步骤告诉我们由于 `P zero` 和 `P (suc zero)` 都成立，
因此 `P (suc zero)` 和 `P (suc (suc zero))` 也成立。我们已经知道第一个成立了，
但第二个是新引入的：

{::comment}
    -- On the third day, three properties are known.
    P zero
    P (suc zero)
    P (suc (suc zero))
{:/}

    -- 第三天，我们知道了三个性质。
    P zero
    P (suc zero)
    P (suc (suc zero))

{::comment}
You've got the hang of it by now:
{:/}

此时规律已经很明显了：

{::comment}
    -- On the fourth day, four properties are known.
    P zero
    P (suc zero)
    P (suc (suc zero))
    P (suc (suc (suc zero)))
{:/}

    -- 第四天，我们知道了四个性质。
    P zero
    P (suc zero)
    P (suc (suc zero))
    P (suc (suc (suc zero)))

{::comment}
The process continues.  On the _n_'th day there will be _n_ distinct
properties that hold.  The property of every natural number will appear
on some given day.  In particular, the property `P n` first appears on
day _n+1_.
{:/}

此过程可以继续下去。在第 **n** 天会有 **n** 个不同的性质成立。
每个自然数的性质都会在某一天出现。具体来说，性质 `P n` 会在第 **n+1**
天首次出现。


{::comment}
## Our first proof: associativity
{:/}

## 第一个证明：结合律

{::comment}
To prove associativity, we take `P m` to be the property:
{:/}

要证明结合律，我们需要将 `P m` 看做以下性质：

    (m + n) + p ≡ m + (n + p)

{::comment}
Here `n` and `p` are arbitrary natural numbers, so if we can show the
equation holds for all `m` it will also hold for all `n` and `p`.
The appropriate instances of the inference rules are:
{:/}

这里的 `n` 和 `p` 是任意自然数，因此若我们可以证明该等式对所有的 `m`
都成立，那么它也会对所有的 `n` 和 `p` 成立。其推理规则的对应实例如下：

    -------------------------------
    (zero + n) + p ≡ zero + (n + p)

    (m + n) + p ≡ m + (n + p)
    ---------------------------------
    (suc m + n) + p ≡ suc m + (n + p)

{::comment}
If we can demonstrate both of these, then associativity of addition
follows by induction.
{:/}

如果我们可以证明这两条规则，那么加法结合律就可根据归纳法来证明。

{::comment}
Here is the proposition's statement and proof:
{:/}

以下为此性质的陈述和证明：

\begin{code}
+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
   zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎
\end{code}

{::comment}
We have named the proof `+-assoc`.  In Agda, identifiers can consist of
any sequence of characters not including spaces or the characters `@.(){};_`.
{:/}

我们将此证明命名为 `+-assoc`。在 Agda 中，标识符可以由除空格或 `@.(){};_`
之外的任何字符序列构成。

{::comment}
Let's unpack this code.  The signature states that we are
defining the identifier `+-assoc` which provides evidence for the
proposition:
{:/}

我们来分析一下这段代码。其签名（Signature）描述了我们定义的标识符 `+-assoc`
为以下命题提供了证据（Evidence）：

    ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

{::comment}
The upside down A is pronounced "for all", and the proposition
asserts that for all natural numbers `m`, `n`, and `p`
the equation `(m + n) + p ≡ m + (n + p)` holds.  Evidence for the proposition
is a function that accepts three natural numbers, binds them to `m`, `n`, and `p`,
and returns evidence for the corresponding instance of the equation.
{:/}

倒 A 符号读作「对于所有（for all）」，而该命题断言对于所有的自然数 `m`、`n`
和 `p`，等式 `(m + n) + p ≡ m + (n + p)` 成立。该命题的证据是一个接受三个自然数的函数，
将它们绑定到 `m`、`n` 和 `p`，并返回该等式对应实例的证据。

{::comment}
For the base case, we must show:
{:/}

对于起始步骤，我们必须证明：

    (zero + n) + p ≡ zero + (n + p)

{::comment}
Simplifying both sides with the base case of addition yields the equation:
{:/}

用加法的起始步骤化简等式两边会得到：

    n + p ≡ n + p

{::comment}
This holds trivially.  Reading the chain of equations in the base case of the proof,
the top and bottom of the chain match the two sides of the equation to
be shown, and reading down from the top and up from the bottom takes us to
`n + p` in the middle.  No justification other than simplification is required.
{:/}

此式平凡成立。阅读此证明中起始步骤中的等式链，其最初和最末的式子分别匹配待证等式的两边，
从上到下或从下到上读都会让我们在中间遇到 `n + p` 。此步骤除了化简外不需要任何依据。

{::comment}
For the inductive case, we must show:
{:/}

对于归纳步骤，我们必须证明：

    (suc m + n) + p ≡ suc m + (n + p)

{::comment}
Simplifying both sides with the inductive case of addition yields the equation:
{:/}

用加法的归纳步骤化简等式两边会得到：

    suc ((m + n) + p) ≡ suc (m + (n + p))

{::comment}
This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:
{:/}

反之，它也可以通过在归纳假设

    (m + n) + p ≡ m + (n + p)

两边之前加上 `suc` 得到。

{::comment}
Reading the chain of equations in the inductive case of the proof, the
top and bottom of the chain match the two sides of the equation to be
shown, and reading down from the top and up from the bottom takes us
to the simplified equation above. The remaining equation, does not follow
from simplification alone, so we use an additional operator for chain
reasoning, `_≡⟨_⟩_`, where a justification for the equation appears
within angle brackets.  The justification given is:
{:/}

阅读此证明中归纳步骤的等式链，其最初和最末的式子分别匹配待证等式的两边，
从上到下或从下到上读都会让我们到达上面化简等式的地方。剩下的等式，
不止用化简就行，因此我们需要为推理链使用一个附加的运算符 `_≡⟨_⟩_`，
为等式给出的依据会放在尖括号中。这里给出的依据是：

    ⟨ cong suc (+-assoc m n p) ⟩

{::comment}
Here, the recursive invocation `+-assoc m n p` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.
{:/}

在这里，递归调用的 `+-assoc m n p` 拥有归纳假设的类型，而 `cong suc`
会在等式两边的前面加上 `suc` 以得到需要的等式。

{::comment}
A relation is said to be a _congruence_ for a given function if it is
preserved by applying that function.  If `e` is evidence that `x ≡ y`,
then `cong f e` is evidence that `f x ≡ f y`, for any function `f`.
{:/}

若某个关系在应用给定函数后仍然保持不变，则称该关系满足**合同性（Congruence）**。
若 `e` 是 `x ≡ y` 的证据，那么对于任意函数 `f`，`cong f e` 是 `f x ≡ f y` 的证据。

{::comment}
Here the inductive hypothesis is not assumed, but instead proved by a
recursive invocation of the function we are defining, `+-assoc m n p`.
As with addition, this is well-founded because associativity of
larger numbers is proved in terms of associativity of smaller numbers.
In this case, `assoc (suc m) n p` is proved using `assoc m n p`.
The correspondence between proof by induction and definition by
recursion is one of the most appealing aspects of Agda.
{:/}

在这里并未假定归纳假设，而是通过递归调用我们定义的函数 `+-assoc m n p` 来证明。
对于加法，这是良基的（well-founded），因为更大数值的结合律可基于更小数值的结合律
来证明。在此步骤中，`assoc (suc m) n p` 是用 `assoc m n p` 证明的。
归纳证明和递归定义之间的这种对应是 Agda 中最吸引人的方面之一。


{::comment}
## Our second proof: commutativity
{:/}

## 第二个证明：交换律

{::comment}
Another important property of addition is that it is _commutative_, that is,
that the order of the operands does not matter:
{:/}

加法的另一个重要性质是**交换律（Commutativity）**，即运算数的顺序无关紧要：

    m + n ≡ n + m

{::comment}
The proof requires that we first demonstrate two lemmas.
{:/}

要证明它，我们需要先证明两条引理（Lemma）。

{::comment}
### The first lemma
{:/}

### 第一条引理

{::comment}
The base case of the definition of addition states that zero
is a left-identity:
{:/}

加法定义的起始步骤说明零是一个左幺元：

    zero + n ≡ n

{::comment}
Our first lemma states that zero is also a right-identity:
{:/}

我们的第一条引理则说明零也是一个右幺元：

    m + zero ≡ m

{::comment}
Here is the lemma's statement and proof:
{:/}

以下是此引理的证明：

\begin{code}
+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎
\end{code}

{::comment}
The signature states that we are defining the identifier `+-identityʳ` which
provides evidence for the proposition:
{:/}

其签名描述了我们定义的标识符 `+-identityʳ` 提供了以下命题的证据：

    ∀ (m : ℕ) → m + zero ≡ m

{::comment}
Evidence for the proposition is a function that accepts a natural
number, binds it to `m`, and returns evidence for the corresponding
instance of the equation.  The proof is by induction on `m`.
{:/}

该命题的证据是一个函数，它接受一个自然数，将其绑定到 `m`，然后返回
该等式对应实例的证据。它通过对 `m` 进行归纳来证明。

{::comment}
For the base case, we must show:
{:/}

对于起始步骤，我们必须证明：

    zero + zero ≡ zero

{::comment}
Simplifying with the base case of addition, this is straightforward.
{:/}

根据加法的起始步骤化简，这很直白。

{::comment}
For the inductive case, we must show:
{:/}

对于归纳步骤，我们必须证明：

    (suc m) + zero = suc m

{::comment}
Simplifying both sides with the inductive case of addition yields the equation:
{:/}

根据加法的归纳步骤化简等式两边可得：

    suc (m + zero) = suc m

{::comment}
This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:
{:/}

反之，它也可以通过在归纳假设

    m + zero ≡ m

两边之前加上 `suc` 得到。

{::comment}
Reading the chain of equations down from the top and up from the bottom
takes us to the simplified equation above.  The remaining
equation has the justification:
{:/}

阅读此等式链，从上到下和从下到上读都会让我们到达上面化简等式的地方。
剩下的等式可由以下依据得出：

    ⟨ cong suc (+-identityʳ m) ⟩

{::comment}
Here, the recursive invocation `+-identityʳ m` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.  This completes the first lemma.
{:/}

在这里，递归调用的 `+-identityʳ m` 拥有归纳假设的类型，而 `cong suc`
会在等式两边的前面加上 `suc` 以得到需要的等式。第一条引理证毕。

{::comment}
### The second lemma
{:/}

### 第二条引理

{::comment}
The inductive case of the definition of addition pushes `suc` on the
first argument to the outside:
{:/}

加法定义的归纳步骤将第一个参数的 `suc` 推到了外面：

    suc m + n ≡ suc (m + n)

{::comment}
Our second lemma does the same for `suc` on the second argument:
{:/}

我们的第二条引理则对第二个参数的 `suc` 做同样的事情：

    m + suc n ≡ suc (m + n)

{::comment}
Here is the lemma's statement and proof:
{:/}

下面是该引理的陈述和证明：

\begin{code}
+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎
\end{code}

{::comment}
The signature states that we are defining the identifier `+-suc` which provides
evidence for the proposition:
{:/}

其签名描述了我们定义的标识符 `+-suc` 提供了以下命题的证据：

    ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

{::comment}
Evidence for the proposition is a function that accepts two natural numbers,
binds them to `m` and `n`, and returns evidence for the corresponding instance
of the equation.  The proof is by induction on `m`.
{:/}

该命题的证据是一个函数，它接受两个自然数，将二者分别绑定到 `m` 和 `n`，
并返回该等式对应实例的证据。它通过对 `m` 进行归纳来证明。

{::comment}
For the base case, we must show:
{:/}

对于起始步骤，我们必须证明：

    zero + suc n ≡ suc (zero + n)

{::comment}
Simplifying with the base case of addition, this is straightforward.
{:/}

根据加法的起始步骤化简，这很直白。

{::comment}
For the inductive case, we must show:
{:/}

对于归纳步骤，我们必须证明：

    suc m + suc n ≡ suc (suc m + n)

{::comment}
Simplifying both sides with the inductive case of addition yields the equation:
{:/}

根据加法的归纳步骤化简等式两边可得：

    suc (m + suc n) ≡ suc (suc (m + n))

{::comment}
This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:
{:/}

反之，它也可以通过在归纳假设

    m + suc n ≡ suc (m + n)

两边之前加上 `suc` 得到。

{::comment}
Reading the chain of equations down from the top and up from the bottom
takes us to the simplified equation in the middle.  The remaining
equation has the justification:
{:/}

从上到下或从下到上阅读等式链都会让我们在中间遇到化简后的等式。剩下的等式
可由以下依据得出：

    ⟨ cong suc (+-suc m n) ⟩

{::comment}
Here, the recursive invocation `+-suc m n` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.  This completes the second lemma.
{:/}

在这里，递归调用的 `+-suc m n` 拥有归纳假设的类型，而 `cong suc`
会在等式两边的前面加上 `suc` 以得到需要的等式。第二条引理证毕。

{::comment}
### The proposition
{:/}

### 命题

{::comment}
Finally, here is our proposition's statement and proof:
{:/}

最后，以下是我们的命题的陈述和证明：

\begin{code}
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎
\end{code}

{::comment}
The first line states that we are defining the identifier
`+-comm` which provides evidence for the proposition:
{:/}

第一行描述了我们定义的标识符 `+-comm` 提供了以下命题的证据：

    ∀ (m n : ℕ) → m + n ≡ n + m

{::comment}
Evidence for the proposition is a function that accepts two
natural numbers, binds them to `m` and `n`, and returns evidence for the
corresponding instance of the equation.  The proof is by
induction on `n`.  (Not on `m` this time!)
{:/}

该命题的证据是一个函数，它接受两个自然数，将二者分别绑定到 `m` 和 `n`，
并返回该等式对应实例的证据。它通过对 `n` 进行归纳来证明。（这次不是 `m`！）

{::comment}
For the base case, we must show:
{:/}

对于起始步骤，我们必须证明：

    m + zero ≡ zero + m

{::comment}
Simplifying both sides with the base case of addition yields the equation:
{:/}

根据加法的起始步骤化简等式两边可得：

    m + zero ≡ m

{::comment}
The remaining equation has the justification `⟨ +-identityʳ m ⟩`,
which invokes the first lemma.
{:/}

剩下的等式可由依据 `⟨ +-identityʳ m ⟩` 得出，它调用第一条引理。

{::comment}
For the inductive case, we must show:
{:/}

对于归纳步骤，我们必须证明：

    m + suc n ≡ suc n + m

{::comment}
Simplifying both sides with the inductive case of addition yields the equation:
{:/}

根据加法的归纳步骤化简等式两边可得：

    m + suc n ≡ suc (n + m)

{::comment}
We show this in two steps.  First, we have:
{:/}

我们分两步来证明它。首先，我们有：

    m + suc n ≡ suc (m + n)

{::comment}
which is justified by the second lemma, `⟨ +-suc m n ⟩`.  Then we
have
{:/}

它依据第二条引理 `⟨ +-suc m n ⟩` 得出。之后我们有：

    suc (m + n) ≡ suc (n + m)

{::comment}
which is justified by congruence and the induction hypothesis,
`⟨ cong suc (+-comm m n) ⟩`.  This completes the proof.
{:/}

它依据合同性和归纳假设 `⟨ cong suc (+-comm m n) ⟩` 得出。证毕。

{::comment}
Agda requires that identifiers are defined before they are used,
so we must present the lemmas before the main proposition, as we
have done above.  In practice, one will often attempt to prove
the main proposition first, and the equations required to do so
will suggest what lemmas to prove.
{:/}

Agda 要求标识符必须在使用前定义，因此我们必须在主命题之前展示引理，
如前例所示。在实践中，我们通常会先试着证明主命题，之后所需的等式会表明
需要证明的引理。


{::comment}
## Our first corollary: rearranging {#sections}
{:/}

## 第一个推论：重排定理 {#sections}

{::comment}
We can apply associativity to rearrange parentheses however we like.
Here is an example:
{:/}

我们可以随意应用结合律来重排括号。例如：

\begin{code}
+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ∎
\end{code}

{::comment}
No induction is required, we simply apply associativity twice.
A few points are worthy of note.
{:/}

无需归纳法，我们只不过应用了两次结合律就完成了证明。其中有几点需要注意的地方。

{::comment}
First, addition associates to the left, so `m + (n + p) + q`
stands for `(m + (n + p)) + q`.
{:/}

第一，加法是左结合的，因此 `m + (n + p) + q` 表示 `(m + (n + p)) + q`。

{::comment}
Second, we use `sym` to interchange the sides of an equation.
Proposition `+-assoc n p q` shifts parentheses from right to left:
{:/}

第二，我们用 `sym` 来交换等式的两边。命题 `+-assoc n p q` 会将括号从右边移到左边：

    (n + p) + q ≡ n + (p + q)

{::comment}
To shift them the other way, we use `sym (+-assoc m n p)`:
{:/}

要往另一个方向移动括号，我们要用 `sym (+-assoc m n p)`：

    n + (p + q) ≡ (n + p) + q

{::comment}
In general, if `e` provides evidence for `x ≡ y` then `sym e` provides
evidence for `y ≡ x`.
{:/}

一般来说，若 `e` 提供了 `x ≡ y` 的证据，那么 `sym e` 就提供了 `y ≡ x` 的证据。

{::comment}
Third, Agda supports a variant of the _section_ notation introduced by
Richard Bird.  We write `(x +_)` for the function that applied to `y`
returns `x + y`.  Thus, applying the congruence `cong (m +_)` takes
the above equation into:
{:/}

第三，Agda 支持 Richard Bird 引入的**片段（section）**记法。我们将应用到
`y` 并返回 `x + y` 的函数写作 `(x +_)`。因此，应用合同性 `cong (m +_)`
会将上面的等式转换成：

    m + (n + (p + q)) ≡ m + ((n + p) + q)

{::comment}
Similarly, we write `(_+ x)` for the function that applied to `y`
returns `y + x`; the same works for any infix operator.
{:/}

类似地，我们将应用到 `y` 并返回 `y + x` 的函数写作 `(_+ x)`。
这同样适用于任何中缀运算符。


{::comment}
## Creation, one last time
{:/}

## 创世，最后一次

{::comment}
Returning to the proof of associativity, it may be helpful to view the inductive
proof (or, equivalently, the recursive definition) as a creation story.  This
time we are concerned with judgments asserting associativity:
{:/}

我们回到结合律的证明上来，把归纳证明（或等价地，递归定义）看做一个创世故事会有助于理解。
这次我们专注于判断结合律的断言：

{::comment}
     -- In the beginning, we know nothing about associativity.
{:/}

     -- 起初，我们对结合律一无所知。

{::comment}
Now, we apply the rules to all the judgments we know about.  The base
case tells us that `(zero + n) + p ≡ zero + (n + p)` for every natural
`n` and `p`.  The inductive case tells us that if `(m + n) + p ≡ m +
(n + p)` (on the day before today) then
`(suc m + n) + p ≡ suc m + (n + p)` (today).
We didn't know any judgments about associativity before today, so that
rule doesn't give us any new judgments:
{:/}

现在，我们将规则应用到所有已知的判断上来。起始步骤告诉我们对于所有的自然数
`n` 和 `p` 来说，`(zero + n) + p ≡ zero + (n + p)`。归纳步骤告我我们若
`(m + n) + p ≡ m + (n + p)`（在昨天）成立，那么 `(suc m + n) + p ≡ suc m + (n + p)`
（在今天）也成立。我们在今天之前并不知道任何关于结合律的判断，
因此此规则并未给出任何新的判断：

{::comment}
    -- On the first day, we know about associativity of 0.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
{:/}

    -- 第一天，我们知道了关于 0 的结合律。
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...

{::comment}
Then we repeat the process, so on the next day we know about all the
judgments from the day before, plus any judgments added by the rules.
The base case tells us nothing new, but now the inductive case adds
more judgments:
{:/}

之后我们重复此过程，因此接下来一天我们知道今天以前的所有判断，
以及任何通过此规则添加的判断。起始步骤并未告诉我们新的东西，
而如今归归纳步骤添加了更多的判断：

{::comment}
    -- On the second day, we know about associativity of 0 and 1.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
{:/}

    -- 第二天，我们知道了关于 0 和 1 的结合律。
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...

{::comment}
And we repeat the process again:
{:/}

我们再次重复此过程：

{::comment}
    -- On the third day, we know about associativity of 0, 1, and 2.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...
{:/}

    -- 第三天，我们知道了关于 0、1 和 2 的结合律。
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...

{::comment}
You've got the hang of it by now:
{:/}

此时规律已经很明显了：

{::comment}
    -- On the fourth day, we know about associativity of 0, 1, 2, and 3.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...
    (3 + 0) + 0 ≡ 3 + (0 + 0)   ...   (3 + 4) + 5 ≡ 3 + (4 + 5)   ...
{:/}

    -- 第四天，我们知道了关于 0、1、2 和 3 的结合律。
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...
    (3 + 0) + 0 ≡ 3 + (0 + 0)   ...   (3 + 4) + 5 ≡ 3 + (4 + 5)   ...

{::comment}
The process continues.  On the _m_'th day we will know all the
judgments where the first number is less than _m_.
{:/}

此过程可以继续下去。在第 **m** 天我们会知道所有第一个数小于 **m** 的判断。

{::comment}
There is also a completely finite approach to generating the same equations,
which is left as an exercise for the reader.
{:/}

还有一种完全有限的方法来生成同样的等式，它的证明留作读者的练习。

{::comment}
#### Exercise `finite-+-assoc` (stretch) {#finite-plus-assoc}
{:/}

#### 练习 `finite-+-assoc`（延伸） {#finite-plus-assoc}

{::comment}
Write out what is known about associativity of addition on each of the
first four days using a finite story of creation, as
[earlier][plfa.Naturals#finite-creation].
{:/}

请参考[前文][plfa.Naturals#finite-creation]写出前四天已知的加法结合律的创世故事。

{::comment}
\begin{code}
-- Your code goes here
\end{code}
{:/}

\begin{code}
-- 请将代码写在此处。
\end{code}

{::comment}
## Associativity with rewrite
{:/}

## 用改写来证明结合律

{::comment}
There is more than one way to skin a cat.  Here is a second proof of
associativity of addition in Agda, using `rewrite` rather than chains of
equations:
{:/}

证明可不止一种方法。下面是第二种在 Agda 中证明加法结合律的方法，使用 `rewrite`（改写）
而非等式链：

\begin{code}
+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero    n p                          =  refl
+-assoc′ (suc m) n p  rewrite +-assoc′ m n p  =  refl
\end{code}

{::comment}
For the base case, we must show:
{:/}

对于起始步骤，我们必须证明：

    (zero + n) + p ≡ zero + (n + p)

{::comment}
Simplifying both sides with the base case of addition yields the equation:
{:/}

根据加法的起始步骤化简等式两边可得：

    n + p ≡ n + p

{::comment}
This holds trivially. The proof that a term is equal to itself is written `refl`.
{:/}

此式平凡成立。一个项等于其自身的证明写作 `refl`（自反性）。

{::comment}
For the inductive case, we must show:
{:/}

对于归纳步骤，我们必须证明：

    (suc m + n) + p ≡ suc m + (n + p)

{::comment}
Simplifying both sides with the inductive case of addition yields the equation:
{:/}

根据加法的归纳步骤化简等式两边可得：

    suc ((m + n) + p) ≡ suc (m + (n + p))

{::comment}
After rewriting with the inductive hypothesis these two terms are equal, and the
proof is again given by `refl`.  Rewriting by a given equation is indicated by
the keyword `rewrite` followed by a proof of that equation.  Rewriting avoids
not only chains of equations but also the need to invoke `cong`.
{:/}

在根据归纳假设改写后，这两项相等，其证明同样由 `refl` 给出。根据给定的等式进行改写
可用关键字 `rewrite` 后跟一个该等式的证明来表示。改写不仅可以省去等式链还可以避免
调用 `cong`.


{::comment}
## Commutativity with rewrite
{:/}

## 使用改写证明交换律

{::comment}
Here is a second proof of commutativity of addition, using `rewrite` rather than
chains of equations:
{:/}

下面是加法交换律的第二个证明，使用 `rewrite` 而非等式链：

\begin{code}
+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl
\end{code}

{::comment}
In the final line, rewriting with two equations is
indicated by separating the two proofs of the relevant equations by a
vertical bar; the rewrite on the left is performed before that on the
right.
{:/}

在最后一行中，用两个等式进行改写被表示为用一条竖线分隔两个相关等式的证明。
左边的改写会在右边之前被执行。


{::comment}
## Building proofs interactively
{:/}

## 交互式地构造证明

{::comment}
It is instructive to see how to build the alternative proof of
associativity using the interactive features of Agda in Emacs.
Begin by typing:
{:/}

看看如何在 Emacs 中用 Agda 的交互式特性来构造另一种结合律的证明会很有启发性。
我们从输入以下内容开始：


    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ m n p = ?

{::comment}
The question mark indicates that you would like Agda to help with
filling in that part of the code.  If you type `C-c C-l` (control-c
followed by control-l), the question mark will be replaced:
{:/}

其中的问号表示你想要 Agda 帮你填充的代码。如果你按下 `C-c C-l`
（先按 Ctrl-c 再按 Ctrl-l），那么问号会被替换为：

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ m n p = { }0

{::comment}
The empty braces are called a _hole_, and 0 is a number used for
referring to the hole.  The hole may display highlighted in green.
Emacs will also create a new window at the bottom of the screen
displaying the text:
{:/}

空的大括号叫做**洞（Hole）**，0 是用来指代此洞的编号。洞可能会以绿色高亮显示。
Emacs 还会在屏幕下方创建一个新的窗口并显示文本：

    ?0 : ((m + n) + p) ≡ (m + (n + p))

{::comment}
This indicates that hole 0 is to be filled in with a proof of
the stated judgment.
{:/}

这表示 0 号洞需要以所提示的判断的证明来填充。

{::comment}
We wish to prove the proposition by induction on `m`.  Move
the cursor into the hole and type `C-c C-c`.  You will be given
the prompt:
{:/}

我们希望通过对 `m` 进行归纳来证明此命题。将光标移动到洞中并按下
`C-c C-c`。它会给出提示：

    pattern variables to case (empty for split on result):

{::comment}
Typing `m` will cause a split on that variable, resulting
in an update to the code:
{:/}

按下 `m` 会拆分该变量，并更新此代码：

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = { }0
    +-assoc′ (suc m) n p = { }1

{::comment}
There are now two holes, and the window at the bottom tells you what
each is required to prove:
{:/}

现在有两个洞了，下方的窗口会告诉你每个洞中需要证明的内容：

    ?0 : ((zero + n) + p) ≡ (zero + (n + p))
    ?1 : ((suc m + n) + p) ≡ (suc m + (n + p))

{::comment}
Going into hole 0 and typing `C-c C-,` will display the text:
{:/}

进入 0 号洞并按下 `C-c C-,` 会显示以下文本：

    Goal: (n + p) ≡ (n + p)
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ

{::comment}
This indicates that after simplification the goal for hole 0 is as
stated, and that variables `p` and `n` of the stated types are
available to use in the proof.  The proof of the given goal is
trivial, and going into the goal and typing `C-c C-r` will fill it in.
Typing `C-c C-l` renumbers the remaining hole to 0:
{:/}

它表示在化简之后，0 号洞的目标如上所示，所示类型的变量 `p` 和 `n` 可在证明中使用。
给定目标的证明很平凡，只需进入该目标并按下 `C-c C-r` 即可填充。按下 `C-c C-l`
会将剩下的洞重新编号为 0：

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p = { }0

{::comment}
Going into the new hole 0 and typing `C-c C-,` will display the text:
{:/}

进入新的 0 号洞并按下 `C-c C-,` 会显示以下文本：

    Goal: suc ((m + n) + p) ≡ suc (m + (n + p))
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ
    m : ℕ

{::comment}
Again, this gives the simplified goal and the available variables.
In this case, we need to rewrite by the induction
hypothesis, so let's edit the text accordingly:
{:/}

同样，它会给出化简后的目标和可用的变量。在此步骤中，我们需要根据归纳假设进行改写，
于是我来编辑这些文本：

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p rewrite +-assoc′ m n p = { }0

{::comment}
Going into the remaining hole and typing `C-c C-,` will display the text:
{:/}

进入剩下的洞中并按下 `C-c C-,` 会显示以下文本：

    Goal: suc (m + (n + p)) ≡ suc (m + (n + p))
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ
    m : ℕ

{::comment}
The proof of the given goal is trivial, and going into the goal and
typing `C-c C-r` will fill it in, completing the proof:
{:/}

给定目标的证明很平凡，只需进入该目标并按下 `C-c C-r` 即可填充并完成证明：

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl


{::comment}
#### Exercise `+-swap` (recommended) {#plus-swap}
{:/}

#### 练习：`+-swap`（推荐） {#plus-swap}

{::comment}
Show
{:/}

请证明对于所有的自然数 `m`、`n` 和 `p`，

    m + (n + p) ≡ n + (m + p)

{::comment}
for all naturals `m`, `n`, and `p`. No induction is needed,
just apply the previous results which show addition
is associative and commutative.
{:/}

成立。无需归纳证明，只需应用前面满足结合律和交换律的结果即可。

\begin{code}
-- Your code goes here
\end{code}
{:/}

\begin{code}
-- 请将代码写在此处。
\end{code}

{::comment}
#### Exercise `*-distrib-+` (recommended) {#times-distrib-plus}
{:/}

#### 练习 `*-distrib-+`（推荐） {#times-distrib-plus}

{::comment}
Show multiplication distributes over addition, that is,
{:/}

请证明乘法满足结合律，即对于所有的自然数 `m`、`n` 和 `p`，

    (m + n) * p ≡ m * p + n * p

{::comment}
for all naturals `m`, `n`, and `p`.
{:/}

成立。

{::comment}
\begin{code}
-- Your code goes here
\end{code}
{:/}

\begin{code}
-- 请将代码写在此处。
\end{code}

{::comment}
#### Exercise `*-assoc` (recommended) {#times-assoc}
{:/}

#### 练习 `*-assoc`（推荐） {#times-assoc}

{::comment}
Show multiplication is associative, that is,
{:/}

请证明乘法满足结合律，即对于所有的自然数 `m`、`n` 和 `p`，

    (m * n) * p ≡ m * (n * p)

{::comment}
for all naturals `m`, `n`, and `p`.
{:/}

成立。

{::comment}
\begin{code}
-- Your code goes here
\end{code}
{:/}

\begin{code}
-- 请将代码写在此处。
\end{code}

{::comment}
#### Exercise `*-comm` {#times-comm}
{:/}

#### 练习 `*-comm` {#times-comm}

{::comment}
Show multiplication is commutative, that is,
{:/}

请证明乘法满足交换律，即对于所有的自然数 `m` 和 `n`，

    m * n ≡ n * m

{::comment}
for all naturals `m` and `n`.  As with commutativity of addition,
you will need to formulate and prove suitable lemmas.
{:/}

成立。和加法交换律一样，你需要陈述并证明配套的引理。

{::comment}
\begin{code}
-- Your code goes here
\end{code}
{:/}

\begin{code}
-- 请将代码写在此处。
\end{code}


{::comment}
#### Exercise `0∸n≡0` {#zero-monus}
{:/}

#### 练习 `0∸n≡0` {#zero-monus}

{::comment}
Show
{:/}

请证明对于所有的自然数 `n`，

    zero ∸ n ≡ zero

{::comment}
for all naturals `n`. Did your proof require induction?
{:/}

成立。你的证明需要归纳法吗？

{::comment}
\begin{code}
-- Your code goes here
\end{code}
{:/}

\begin{code}
-- 请将代码写在此处。
\end{code}


{::comment}
#### Exercise `∸-+-assoc` {#monus-plus-assoc}
{:/}

#### 练习 `∸-+-assoc` {#monus-plus-assoc}

{::comment}
Show that monus associates with addition, that is,
{:/}

请证明饱和减法与加法满足结合律，即对于所有的自然数 `m`、`n` 和 `p`，

    m ∸ n ∸ p ≡ m ∸ (n + p)

{::comment}
for all naturals `m`, `n`, and `p`.
{:/}

成立。

{::comment}
\begin{code}
-- Your code goes here
\end{code}
{:/}

\begin{code}
-- 请将代码写在此处。
\end{code}


{::comment}
#### Exercise `Bin-laws` (stretch) {#Bin-laws}
{:/}

#### 练习 `Bin-laws`（延伸） {#Bin-laws}

{::comment}
Recall that
Exercise [Bin][plfa.Naturals#Bin]
defines a datatype of bitstrings representing natural numbers
{:/}

回想练习 [Bin][plfa.Naturals#Bin] 中定义了一种比特串数据类型来表示自然数

\begin{code}
data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin
\end{code}

{::comment}
and asks you to define functions
{:/}

并要求你定义函数

    inc   : Bin → Bin
    to    : ℕ → Bin
    from  : Bin → ℕ

{::comment}
Consider the following laws, where `n` ranges over naturals and `x`
over bitstrings:
{:/}

考虑以下定律，其中 `n` 表示自然数，`x` 表示比特串：

    from (inc x) ≡ suc (from x)
    to (from x) ≡ x
    from (to n) ≡ n

{::comment}
For each law: if it holds, prove; if not, give a counterexample.
{:/}

对于每一条定律：若它成立，请证明；若不成立，请给出一个反例。

{::comment}
\begin{code}
-- Your code goes here
\end{code}
{:/}

\begin{code}
-- 请将代码写在此处。
\end{code}


{::comment}
## Standard library
{:/}

## 标准库

{::comment}
Definitions similar to those in this chapter can be found in the standard library:
{:/}

本章中类似的定义可在标准库中找到：

\begin{code}
import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)
\end{code}

{::comment}
## Unicode
{:/}

## 统一码（Unicode）

{::comment}
This chapter uses the following unicode:
{:/}

本章中使用了以下统一码：

{::comment}
    ∀  U+2200  FOR ALL (\forall, \all)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)
    ′  U+2032  PRIME (\')
    ″  U+2033  DOUBLE PRIME (\')
    ‴  U+2034  TRIPLE PRIME (\')
    ⁗  U+2057  QUADRUPLE PRIME (\')
{:/}

    ∀  U+2200  对于所有 (\forall, \all)
    ʳ  U+02B3  小写字母 r 的变体 (\^r)
    ′  U+2032  撇号 (\')
    ″  U+2033  双撇号 (\')
    ‴  U+2034  三撇号 (\')
    ⁗  U+2057  四撇号 (\')

{::comment}
Similar to `\r`, the command `\^r` gives access to a variety of
superscript rightward arrows, and also a superscript letter `r`.
The command `\'` gives access to a range of primes (`′ ″ ‴ ⁗`).
{:/}

与 `\r` 类似，命令 `\^r` 列出了多种上标右箭头的变体，以及上标的字母 `r`。
命令 `\'` 列出了一些撇号（`′ ″ ‴ ⁗`）。
