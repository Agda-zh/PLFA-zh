---
src       : "src/plfa/Induction.lagda.md"
title     : "Induction: 归纳证明"
layout    : page
prev      : /Naturals/
permalink : /Induction/
next      : /Relations/
translators : ["Oling Cat"]
progress  : 100
---

{% raw %}<pre class="Agda"><a id="176" class="Keyword">module</a> <a id="183" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html" class="Module">plfa.Induction</a> <a id="198" class="Keyword">where</a>
</pre>{% endraw %}
{::comment}
> Induction makes you feel guilty for getting something out of nothing
> ... but it is one of the greatest ideas of civilization.
> -- Herbert Wilf
{:/}

> 归纳会让你对无中生有感到内疚
> ……但它却是文明中最伟大的思想之一。
> —— Herbert Wilf

{::comment}
Now that we've defined the naturals and operations upon them, our next
step is to learn how to prove properties that they satisfy.  As hinted
by their name, properties of _inductive datatypes_ are proved by
_induction_.
{:/}

现在我们定义了自然数及其运算，下一步是学习如何证明它们满足的性质。
顾名思义，**归纳数据类型（Inductive Datatype）**是通过**归纳（Induction）**
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

{% raw %}<pre class="Agda"><a id="1093" class="Keyword">import</a> <a id="1100" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="1138" class="Symbol">as</a> <a id="1141" class="Module">Eq</a>
<a id="1144" class="Keyword">open</a> <a id="1149" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="1152" class="Keyword">using</a> <a id="1158" class="Symbol">(</a><a id="1159" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="1162" class="Symbol">;</a> <a id="1164" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="1168" class="Symbol">;</a> <a id="1170" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a><a id="1174" class="Symbol">;</a> <a id="1176" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#939" class="Function">sym</a><a id="1179" class="Symbol">)</a>
<a id="1181" class="Keyword">open</a> <a id="1186" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2499" class="Module">Eq.≡-Reasoning</a> <a id="1201" class="Keyword">using</a> <a id="1207" class="Symbol">(</a><a id="1208" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin_</a><a id="1214" class="Symbol">;</a> <a id="1216" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">_≡⟨⟩_</a><a id="1221" class="Symbol">;</a> <a id="1223" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">_≡⟨_⟩_</a><a id="1229" class="Symbol">;</a> <a id="1231" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">_∎</a><a id="1233" class="Symbol">)</a>
<a id="1235" class="Keyword">open</a> <a id="1240" class="Keyword">import</a> <a id="1247" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="1256" class="Keyword">using</a> <a id="1262" class="Symbol">(</a><a id="1263" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1264" class="Symbol">;</a> <a id="1266" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="1270" class="Symbol">;</a> <a id="1272" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="1275" class="Symbol">;</a> <a id="1277" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="1280" class="Symbol">;</a> <a id="1282" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">_*_</a><a id="1285" class="Symbol">;</a> <a id="1287" href="Agda.Builtin.Nat.html#388" class="Primitive Operator">_∸_</a><a id="1290" class="Symbol">)</a>
</pre>{% endraw %}

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

* **交换律（Commutativity）**。若参数的顺序无关紧要，则称运算符 `+` 满足交换律，
  即对于所有的 `m` 和 `n`，有 `m + n ≡ n + m`。

* **分配律（Distributivity）**。对于所有的 `m`、`n` 和 `p`，若
  `(m + n) * p ≡ (m * p) + (n * p)`，则运算符 `*` 对运算符 `+` 满足左分配律；
  对于所有的 `m`、`n` 和 `p`，若 `m * (p + q) ≡ (m * p) + (m * q)`，则满足右分配律。

{::comment}
Addition has identity `0` and multiplication has identity `1`;
addition and multiplication are both associative and commutative;
and multiplication distributes over addition.
{:/}

加法的幺元为 `0`，乘法的幺元为 `1`。加法和乘法都满足结合律和交换律，
乘法对加法满足分配律。

If you ever bump into an operator at a party, you now know how
to make small talk, by asking whether it has a unit and is
associative or commutative.  If you bump into two operators, you
might ask them if one distributes over the other.

如果你在一个舞会上碰见了一位操作员，那么你可以跟他闲聊，问问他是否有单位元，
能不能结合或者交换。如果你碰见了两位操作员，那么可以问他们某一位是否在另一位上面分布。

【译注：作者的双关冷笑话，运算符（Operator）也有操作员的意思。】

{::comment}
Less frivolously, if you ever bump into an operator while reading a
technical paper, this gives you a way to orient yourself, by checking
whether or not it has an identity, is associative or commutative, or
distributes over another operator.  A careful author will often call
out these properties---or their lack---for instance by pointing out
that a newly introduced operator is associative but not commutative.
{:/}

正经来说，如果你在阅读技术论文时遇到了一个运算符，那么你可以考察它是否拥有一个幺元，
是否满足结合律或分配律，或者是否对另一个运算符满足分配律，这能为你提供一种视角。
细心的作者通常会指出它们是否满足这些性质，比如说指明一个新引入的运算符满足结合律
但不满足交换律。

{::comment}
#### Exercise `operators` {#operators}
{:/}

#### 练习 `operators` {#operators}

{::comment}
Give another example of a pair of operators that have an identity
and are associative, commutative, and distribute over one another.
{:/}

请给出另一对运算符，它们拥有一个幺元，满足结合律、交换律，且其中一个对另一个满足分配律。

{::comment}
{% raw %}<pre class="Agda"><a id="4286" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="4323" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
Give an example of an operator that has an identity and is
associative but is not commutative.
{:/}

请给出一个运算符的例子，它拥有幺元、满足结合律但不满足交换律。

{% raw %}<pre class="Agda"><a id="4491" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

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

这里的变量 `m`、`n` 和 `p` 的取值范围都是全体自然数。

{::comment}
We can test the proposition by choosing specific numbers for the three
variables:
{:/}

我们可以为这三个变量选取特定的数值来测试此命题：

{% raw %}<pre class="Agda"><a id="5017" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#5017" class="Function">_</a> <a id="5019" class="Symbol">:</a> <a id="5021" class="Symbol">(</a><a id="5022" class="Number">3</a> <a id="5024" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5026" class="Number">4</a><a id="5027" class="Symbol">)</a> <a id="5029" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5031" class="Number">5</a> <a id="5033" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5035" class="Number">3</a> <a id="5037" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5039" class="Symbol">(</a><a id="5040" class="Number">4</a> <a id="5042" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5044" class="Number">5</a><a id="5045" class="Symbol">)</a>
<a id="5047" class="Symbol">_</a> <a id="5049" class="Symbol">=</a>
  <a id="5053" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="5063" class="Symbol">(</a><a id="5064" class="Number">3</a> <a id="5066" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5068" class="Number">4</a><a id="5069" class="Symbol">)</a> <a id="5071" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5073" class="Number">5</a>
  <a id="5077" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="5085" class="Number">7</a> <a id="5087" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5089" class="Number">5</a>
  <a id="5093" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="5101" class="Number">12</a>
  <a id="5106" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="5114" class="Number">3</a> <a id="5116" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5118" class="Number">9</a>
  <a id="5122" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="5130" class="Number">3</a> <a id="5132" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5134" class="Symbol">(</a><a id="5135" class="Number">4</a> <a id="5137" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="5139" class="Number">5</a><a id="5140" class="Symbol">)</a>
  <a id="5144" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}
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
我们可能需要收集更多证据，选择其它的数值来测试此命题。但由于自然数是无限的，
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

此过程可以继续下去。在第 *n* 天会有 *n* 个不同的性质成立。
每个自然数的性质都会在某一天出现。具体来说，性质 `P n` 会在第 *n+1* 天
首次出现。


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

{% raw %}<pre class="Agda"><a id="+-assoc"></a><a id="11496" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11496" class="Function">+-assoc</a> <a id="11504" class="Symbol">:</a> <a id="11506" class="Symbol">∀</a> <a id="11508" class="Symbol">(</a><a id="11509" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11509" class="Bound">m</a> <a id="11511" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11511" class="Bound">n</a> <a id="11513" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11513" class="Bound">p</a> <a id="11515" class="Symbol">:</a> <a id="11517" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11518" class="Symbol">)</a> <a id="11520" class="Symbol">→</a> <a id="11522" class="Symbol">(</a><a id="11523" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11509" class="Bound">m</a> <a id="11525" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11527" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11511" class="Bound">n</a><a id="11528" class="Symbol">)</a> <a id="11530" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11532" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11513" class="Bound">p</a> <a id="11534" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11536" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11509" class="Bound">m</a> <a id="11538" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11540" class="Symbol">(</a><a id="11541" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11511" class="Bound">n</a> <a id="11543" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11545" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11513" class="Bound">p</a><a id="11546" class="Symbol">)</a>
<a id="11548" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11496" class="Function">+-assoc</a> <a id="11556" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="11561" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11561" class="Bound">n</a> <a id="11563" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11563" class="Bound">p</a> <a id="11565" class="Symbol">=</a>
  <a id="11569" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="11579" class="Symbol">(</a><a id="11580" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="11585" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11587" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11561" class="Bound">n</a><a id="11588" class="Symbol">)</a> <a id="11590" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11592" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11563" class="Bound">p</a>
  <a id="11596" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="11604" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11561" class="Bound">n</a> <a id="11606" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11608" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11563" class="Bound">p</a>
  <a id="11612" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="11620" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="11625" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11627" class="Symbol">(</a><a id="11628" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11561" class="Bound">n</a> <a id="11630" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11632" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11563" class="Bound">p</a><a id="11633" class="Symbol">)</a>
  <a id="11637" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
<a id="11639" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11496" class="Function">+-assoc</a> <a id="11647" class="Symbol">(</a><a id="11648" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11652" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11652" class="Bound">m</a><a id="11653" class="Symbol">)</a> <a id="11655" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11655" class="Bound">n</a> <a id="11657" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11657" class="Bound">p</a> <a id="11659" class="Symbol">=</a>
  <a id="11663" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="11673" class="Symbol">(</a><a id="11674" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11678" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11652" class="Bound">m</a> <a id="11680" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11682" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11655" class="Bound">n</a><a id="11683" class="Symbol">)</a> <a id="11685" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11687" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11657" class="Bound">p</a>
  <a id="11691" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="11699" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11703" class="Symbol">(</a><a id="11704" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11652" class="Bound">m</a> <a id="11706" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11708" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11655" class="Bound">n</a><a id="11709" class="Symbol">)</a> <a id="11711" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11713" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11657" class="Bound">p</a>
  <a id="11717" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="11725" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11729" class="Symbol">((</a><a id="11731" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11652" class="Bound">m</a> <a id="11733" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11735" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11655" class="Bound">n</a><a id="11736" class="Symbol">)</a> <a id="11738" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11740" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11657" class="Bound">p</a><a id="11741" class="Symbol">)</a>
  <a id="11745" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="11748" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="11753" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11757" class="Symbol">(</a><a id="11758" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11496" class="Function">+-assoc</a> <a id="11766" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11652" class="Bound">m</a> <a id="11768" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11655" class="Bound">n</a> <a id="11770" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11657" class="Bound">p</a><a id="11771" class="Symbol">)</a> <a id="11773" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="11779" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11783" class="Symbol">(</a><a id="11784" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11652" class="Bound">m</a> <a id="11786" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11788" class="Symbol">(</a><a id="11789" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11655" class="Bound">n</a> <a id="11791" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11793" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11657" class="Bound">p</a><a id="11794" class="Symbol">))</a>
  <a id="11799" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="11807" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11811" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11652" class="Bound">m</a> <a id="11813" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11815" class="Symbol">(</a><a id="11816" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11655" class="Bound">n</a> <a id="11818" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11820" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11657" class="Bound">p</a><a id="11821" class="Symbol">)</a>
  <a id="11825" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}
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
从上到下或从下到上读都会让我们在中间遇到 `n + p` 。此步骤除了化简外不需要其他额外的解释。

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
As with addition, this is well founded because associativity of
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
## Induction as recursion
{:/}

## 归纳即递归

下面是归纳如何对应于递归的具体例子，它是在结合律的证明中，将 `m` 实例化为 `2`
时出现的计算。

{% raw %}<pre class="Agda"><a id="+-assoc-2"></a><a id="15982" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#15982" class="Function">+-assoc-2</a> <a id="15992" class="Symbol">:</a> <a id="15994" class="Symbol">∀</a> <a id="15996" class="Symbol">(</a><a id="15997" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#15997" class="Bound">n</a> <a id="15999" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#15999" class="Bound">p</a> <a id="16001" class="Symbol">:</a> <a id="16003" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="16004" class="Symbol">)</a> <a id="16006" class="Symbol">→</a> <a id="16008" class="Symbol">(</a><a id="16009" class="Number">2</a> <a id="16011" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16013" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#15997" class="Bound">n</a><a id="16014" class="Symbol">)</a> <a id="16016" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16018" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#15999" class="Bound">p</a> <a id="16020" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16022" class="Number">2</a> <a id="16024" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16026" class="Symbol">(</a><a id="16027" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#15997" class="Bound">n</a> <a id="16029" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16031" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#15999" class="Bound">p</a><a id="16032" class="Symbol">)</a>
<a id="16034" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#15982" class="Function">+-assoc-2</a> <a id="16044" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16044" class="Bound">n</a> <a id="16046" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16046" class="Bound">p</a> <a id="16048" class="Symbol">=</a>
  <a id="16052" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="16062" class="Symbol">(</a><a id="16063" class="Number">2</a> <a id="16065" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16067" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16044" class="Bound">n</a><a id="16068" class="Symbol">)</a> <a id="16070" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16072" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16046" class="Bound">p</a>
  <a id="16076" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="16084" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16088" class="Symbol">(</a><a id="16089" class="Number">1</a> <a id="16091" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16093" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16044" class="Bound">n</a><a id="16094" class="Symbol">)</a> <a id="16096" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16098" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16046" class="Bound">p</a>
  <a id="16102" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="16110" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16114" class="Symbol">((</a><a id="16116" class="Number">1</a> <a id="16118" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16120" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16044" class="Bound">n</a><a id="16121" class="Symbol">)</a> <a id="16123" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16125" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16046" class="Bound">p</a><a id="16126" class="Symbol">)</a>
  <a id="16130" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="16133" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="16138" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16142" class="Symbol">(</a><a id="16143" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16218" class="Function">+-assoc-1</a> <a id="16153" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16044" class="Bound">n</a> <a id="16155" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16046" class="Bound">p</a><a id="16156" class="Symbol">)</a> <a id="16158" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="16164" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16168" class="Symbol">(</a><a id="16169" class="Number">1</a> <a id="16171" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16173" class="Symbol">(</a><a id="16174" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16044" class="Bound">n</a> <a id="16176" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16178" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16046" class="Bound">p</a><a id="16179" class="Symbol">))</a>
  <a id="16184" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="16192" class="Number">2</a> <a id="16194" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16196" class="Symbol">(</a><a id="16197" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16044" class="Bound">n</a> <a id="16199" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16201" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16046" class="Bound">p</a><a id="16202" class="Symbol">)</a>
  <a id="16206" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
  <a id="16210" class="Keyword">where</a>
  <a id="16218" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16218" class="Function">+-assoc-1</a> <a id="16228" class="Symbol">:</a> <a id="16230" class="Symbol">∀</a> <a id="16232" class="Symbol">(</a><a id="16233" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16233" class="Bound">n</a> <a id="16235" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16235" class="Bound">p</a> <a id="16237" class="Symbol">:</a> <a id="16239" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="16240" class="Symbol">)</a> <a id="16242" class="Symbol">→</a> <a id="16244" class="Symbol">(</a><a id="16245" class="Number">1</a> <a id="16247" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16249" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16233" class="Bound">n</a><a id="16250" class="Symbol">)</a> <a id="16252" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16254" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16235" class="Bound">p</a> <a id="16256" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16258" class="Number">1</a> <a id="16260" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16262" class="Symbol">(</a><a id="16263" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16233" class="Bound">n</a> <a id="16265" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16267" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16235" class="Bound">p</a><a id="16268" class="Symbol">)</a>
  <a id="16272" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16218" class="Function">+-assoc-1</a> <a id="16282" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16282" class="Bound">n</a> <a id="16284" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16284" class="Bound">p</a> <a id="16286" class="Symbol">=</a>
    <a id="16292" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
      <a id="16304" class="Symbol">(</a><a id="16305" class="Number">1</a> <a id="16307" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16309" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16282" class="Bound">n</a><a id="16310" class="Symbol">)</a> <a id="16312" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16314" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16284" class="Bound">p</a>
    <a id="16320" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
      <a id="16330" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16334" class="Symbol">(</a><a id="16335" class="Number">0</a> <a id="16337" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16339" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16282" class="Bound">n</a><a id="16340" class="Symbol">)</a> <a id="16342" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16344" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16284" class="Bound">p</a>
    <a id="16350" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
      <a id="16360" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16364" class="Symbol">((</a><a id="16366" class="Number">0</a> <a id="16368" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16370" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16282" class="Bound">n</a><a id="16371" class="Symbol">)</a> <a id="16373" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16375" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16284" class="Bound">p</a><a id="16376" class="Symbol">)</a>
    <a id="16382" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="16385" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="16390" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16394" class="Symbol">(</a><a id="16395" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16482" class="Function">+-assoc-0</a> <a id="16405" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16282" class="Bound">n</a> <a id="16407" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16284" class="Bound">p</a><a id="16408" class="Symbol">)</a> <a id="16410" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
      <a id="16418" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16422" class="Symbol">(</a><a id="16423" class="Number">0</a> <a id="16425" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16427" class="Symbol">(</a><a id="16428" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16282" class="Bound">n</a> <a id="16430" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16432" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16284" class="Bound">p</a><a id="16433" class="Symbol">))</a>
    <a id="16440" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
      <a id="16450" class="Number">1</a> <a id="16452" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16454" class="Symbol">(</a><a id="16455" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16282" class="Bound">n</a> <a id="16457" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16459" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16284" class="Bound">p</a><a id="16460" class="Symbol">)</a>
    <a id="16466" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
    <a id="16472" class="Keyword">where</a>
    <a id="16482" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16482" class="Function">+-assoc-0</a> <a id="16492" class="Symbol">:</a> <a id="16494" class="Symbol">∀</a> <a id="16496" class="Symbol">(</a><a id="16497" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16497" class="Bound">n</a> <a id="16499" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16499" class="Bound">p</a> <a id="16501" class="Symbol">:</a> <a id="16503" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="16504" class="Symbol">)</a> <a id="16506" class="Symbol">→</a> <a id="16508" class="Symbol">(</a><a id="16509" class="Number">0</a> <a id="16511" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16513" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16497" class="Bound">n</a><a id="16514" class="Symbol">)</a> <a id="16516" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16518" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16499" class="Bound">p</a> <a id="16520" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16522" class="Number">0</a> <a id="16524" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16526" class="Symbol">(</a><a id="16527" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16497" class="Bound">n</a> <a id="16529" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16531" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16499" class="Bound">p</a><a id="16532" class="Symbol">)</a>
    <a id="16538" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16482" class="Function">+-assoc-0</a> <a id="16548" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16548" class="Bound">n</a> <a id="16550" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16550" class="Bound">p</a> <a id="16552" class="Symbol">=</a>
      <a id="16560" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
        <a id="16574" class="Symbol">(</a><a id="16575" class="Number">0</a> <a id="16577" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16579" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16548" class="Bound">n</a><a id="16580" class="Symbol">)</a> <a id="16582" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16584" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16550" class="Bound">p</a>
      <a id="16592" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
        <a id="16604" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16548" class="Bound">n</a> <a id="16606" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16608" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16550" class="Bound">p</a>
      <a id="16616" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
        <a id="16628" class="Number">0</a> <a id="16630" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16632" class="Symbol">(</a><a id="16633" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16548" class="Bound">n</a> <a id="16635" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16637" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16550" class="Bound">p</a><a id="16638" class="Symbol">)</a>
      <a id="16646" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}

{::comment}
## Terminology and notation
{:/}

## 术语与记法

{::comment}
The symbol `∀` appears in the statement of associativity to indicate that
it holds for all numbers `m`, `n`, and `p`.  We refer to `∀` as the _universal
quantifier_, and it is discussed further in Chapter [Quantifiers]({{ site.baseurl }}/Quantifiers/).
{:/}

在结合律的陈述中出现的符号 `∀` 表示它对于所有的 `m`、`n` 和 `p` 都成立。
我们将 `∀` 称为**全称量词**（Universal Quantifier），我们会在
[Quantifiers]({{ site.baseurl }}/Quantifiers/) 章节中进一步讨论。

{::comment}
Evidence for a universal quantifier is a function.  The notations
{:/}

全称量词的证据是一个函数。记法

    +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

{::comment}
and
{:/}

和

    +-assoc : ∀ (m : ℕ) → ∀ (n : ℕ) → ∀ (p : ℕ) → (m + n) + p ≡ m + (n + p)

{::comment}
are equivalent. They differ from a function type such as `ℕ → ℕ → ℕ`
in that variables are associated with the each argument type, and the
result type may mention (or depend upon) these variables; hence they
are called _dependent functions_.
{:/}

是等价的。它们不同于像 `ℕ → ℕ → ℕ` 这样的函数类型，其中的变量
与每一个实参类型相关联，其结果类型可能会涉及（或依赖于）这些变量，
因此它们叫做**依赖函数**（Dependent Function）。


{::comment}
## Our second proof: commutativity
{:/}

## 第二个证明：交换律

{::comment}
Another important property of addition is that it is _commutative_, that is,
that the order of the operands does not matter:
{:/}

加法的另一个重要性质是满足**交换律（Commutativity）**，即运算数的顺序无关紧要：

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

{% raw %}<pre class="Agda"><a id="+-identityʳ"></a><a id="18520" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18520" class="Function">+-identityʳ</a> <a id="18532" class="Symbol">:</a> <a id="18534" class="Symbol">∀</a> <a id="18536" class="Symbol">(</a><a id="18537" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18537" class="Bound">m</a> <a id="18539" class="Symbol">:</a> <a id="18541" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="18542" class="Symbol">)</a> <a id="18544" class="Symbol">→</a> <a id="18546" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18537" class="Bound">m</a> <a id="18548" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18550" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="18555" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="18557" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18537" class="Bound">m</a>
<a id="18559" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18520" class="Function">+-identityʳ</a> <a id="18571" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="18576" class="Symbol">=</a>
  <a id="18580" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="18590" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="18595" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18597" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
  <a id="18604" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="18612" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
  <a id="18619" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
<a id="18621" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18520" class="Function">+-identityʳ</a> <a id="18633" class="Symbol">(</a><a id="18634" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18638" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18638" class="Bound">m</a><a id="18639" class="Symbol">)</a> <a id="18641" class="Symbol">=</a>
  <a id="18645" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="18655" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18659" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18638" class="Bound">m</a> <a id="18661" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18663" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
  <a id="18670" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="18678" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18682" class="Symbol">(</a><a id="18683" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18638" class="Bound">m</a> <a id="18685" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18687" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="18691" class="Symbol">)</a>
  <a id="18695" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="18698" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="18703" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18707" class="Symbol">(</a><a id="18708" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18520" class="Function">+-identityʳ</a> <a id="18720" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18638" class="Bound">m</a><a id="18721" class="Symbol">)</a> <a id="18723" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="18729" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18733" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18638" class="Bound">m</a>
  <a id="18737" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}
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

{% raw %}<pre class="Agda"><a id="+-suc"></a><a id="20839" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#20839" class="Function">+-suc</a> <a id="20845" class="Symbol">:</a> <a id="20847" class="Symbol">∀</a> <a id="20849" class="Symbol">(</a><a id="20850" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#20850" class="Bound">m</a> <a id="20852" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#20852" class="Bound">n</a> <a id="20854" class="Symbol">:</a> <a id="20856" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="20857" class="Symbol">)</a> <a id="20859" class="Symbol">→</a> <a id="20861" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#20850" class="Bound">m</a> <a id="20863" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="20865" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="20869" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#20852" class="Bound">n</a> <a id="20871" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="20873" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="20877" class="Symbol">(</a><a id="20878" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#20850" class="Bound">m</a> <a id="20880" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="20882" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#20852" class="Bound">n</a><a id="20883" class="Symbol">)</a>
<a id="20885" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#20839" class="Function">+-suc</a> <a id="20891" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="20896" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#20896" class="Bound">n</a> <a id="20898" class="Symbol">=</a>
  <a id="20902" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="20912" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="20917" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="20919" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="20923" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#20896" class="Bound">n</a>
  <a id="20927" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="20935" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="20939" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#20896" class="Bound">n</a>
  <a id="20943" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="20951" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="20955" class="Symbol">(</a><a id="20956" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="20961" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="20963" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#20896" class="Bound">n</a><a id="20964" class="Symbol">)</a>
  <a id="20968" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
<a id="20970" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#20839" class="Function">+-suc</a> <a id="20976" class="Symbol">(</a><a id="20977" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="20981" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#20981" class="Bound">m</a><a id="20982" class="Symbol">)</a> <a id="20984" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#20984" class="Bound">n</a> <a id="20986" class="Symbol">=</a>
  <a id="20990" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="21000" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21004" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#20981" class="Bound">m</a> <a id="21006" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="21008" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21012" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#20984" class="Bound">n</a>
  <a id="21016" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="21024" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21028" class="Symbol">(</a><a id="21029" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#20981" class="Bound">m</a> <a id="21031" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="21033" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21037" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#20984" class="Bound">n</a><a id="21038" class="Symbol">)</a>
  <a id="21042" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="21045" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="21050" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21054" class="Symbol">(</a><a id="21055" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#20839" class="Function">+-suc</a> <a id="21061" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#20981" class="Bound">m</a> <a id="21063" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#20984" class="Bound">n</a><a id="21064" class="Symbol">)</a> <a id="21066" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="21072" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21076" class="Symbol">(</a><a id="21077" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21081" class="Symbol">(</a><a id="21082" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#20981" class="Bound">m</a> <a id="21084" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="21086" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#20984" class="Bound">n</a><a id="21087" class="Symbol">))</a>
  <a id="21092" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="21100" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21104" class="Symbol">(</a><a id="21105" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21109" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#20981" class="Bound">m</a> <a id="21111" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="21113" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#20984" class="Bound">n</a><a id="21114" class="Symbol">)</a>
  <a id="21118" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}
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

{% raw %}<pre class="Agda"><a id="+-comm"></a><a id="22974" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22974" class="Function">+-comm</a> <a id="22981" class="Symbol">:</a> <a id="22983" class="Symbol">∀</a> <a id="22985" class="Symbol">(</a><a id="22986" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22986" class="Bound">m</a> <a id="22988" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22988" class="Bound">n</a> <a id="22990" class="Symbol">:</a> <a id="22992" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="22993" class="Symbol">)</a> <a id="22995" class="Symbol">→</a> <a id="22997" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22986" class="Bound">m</a> <a id="22999" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23001" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22988" class="Bound">n</a> <a id="23003" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="23005" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22988" class="Bound">n</a> <a id="23007" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23009" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22986" class="Bound">m</a>
<a id="23011" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22974" class="Function">+-comm</a> <a id="23018" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23018" class="Bound">m</a> <a id="23020" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="23025" class="Symbol">=</a>
  <a id="23029" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="23039" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23018" class="Bound">m</a> <a id="23041" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23043" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
  <a id="23050" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="23053" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18520" class="Function">+-identityʳ</a> <a id="23065" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23018" class="Bound">m</a> <a id="23067" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="23073" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23018" class="Bound">m</a>
  <a id="23077" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="23085" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="23090" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23092" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23018" class="Bound">m</a>
  <a id="23096" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
<a id="23098" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22974" class="Function">+-comm</a> <a id="23105" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23105" class="Bound">m</a> <a id="23107" class="Symbol">(</a><a id="23108" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23112" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23112" class="Bound">n</a><a id="23113" class="Symbol">)</a> <a id="23115" class="Symbol">=</a>
  <a id="23119" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="23129" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23105" class="Bound">m</a> <a id="23131" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23133" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23137" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23112" class="Bound">n</a>
  <a id="23141" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="23144" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#20839" class="Function">+-suc</a> <a id="23150" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23105" class="Bound">m</a> <a id="23152" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23112" class="Bound">n</a> <a id="23154" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="23160" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23164" class="Symbol">(</a><a id="23165" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23105" class="Bound">m</a> <a id="23167" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23169" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23112" class="Bound">n</a><a id="23170" class="Symbol">)</a>
  <a id="23174" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="23177" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="23182" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23186" class="Symbol">(</a><a id="23187" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22974" class="Function">+-comm</a> <a id="23194" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23105" class="Bound">m</a> <a id="23196" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23112" class="Bound">n</a><a id="23197" class="Symbol">)</a> <a id="23199" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="23205" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23209" class="Symbol">(</a><a id="23210" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23112" class="Bound">n</a> <a id="23212" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23214" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23105" class="Bound">m</a><a id="23215" class="Symbol">)</a>
  <a id="23219" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="23227" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23231" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23112" class="Bound">n</a> <a id="23233" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23235" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23105" class="Bound">m</a>
  <a id="23239" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}
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

{% raw %}<pre class="Agda"><a id="+-rearrange"></a><a id="25481" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25481" class="Function">+-rearrange</a> <a id="25493" class="Symbol">:</a> <a id="25495" class="Symbol">∀</a> <a id="25497" class="Symbol">(</a><a id="25498" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25498" class="Bound">m</a> <a id="25500" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25500" class="Bound">n</a> <a id="25502" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25502" class="Bound">p</a> <a id="25504" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25504" class="Bound">q</a> <a id="25506" class="Symbol">:</a> <a id="25508" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="25509" class="Symbol">)</a> <a id="25511" class="Symbol">→</a> <a id="25513" class="Symbol">(</a><a id="25514" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25498" class="Bound">m</a> <a id="25516" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25518" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25500" class="Bound">n</a><a id="25519" class="Symbol">)</a> <a id="25521" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25523" class="Symbol">(</a><a id="25524" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25502" class="Bound">p</a> <a id="25526" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25528" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25504" class="Bound">q</a><a id="25529" class="Symbol">)</a> <a id="25531" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="25533" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25498" class="Bound">m</a> <a id="25535" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25537" class="Symbol">(</a><a id="25538" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25500" class="Bound">n</a> <a id="25540" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25542" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25502" class="Bound">p</a><a id="25543" class="Symbol">)</a> <a id="25545" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25547" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25504" class="Bound">q</a>
<a id="25549" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25481" class="Function">+-rearrange</a> <a id="25561" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25561" class="Bound">m</a> <a id="25563" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25563" class="Bound">n</a> <a id="25565" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25565" class="Bound">p</a> <a id="25567" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25567" class="Bound">q</a> <a id="25569" class="Symbol">=</a>
  <a id="25573" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="25583" class="Symbol">(</a><a id="25584" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25561" class="Bound">m</a> <a id="25586" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25588" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25563" class="Bound">n</a><a id="25589" class="Symbol">)</a> <a id="25591" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25593" class="Symbol">(</a><a id="25594" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25565" class="Bound">p</a> <a id="25596" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25598" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25567" class="Bound">q</a><a id="25599" class="Symbol">)</a>
  <a id="25603" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="25606" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11496" class="Function">+-assoc</a> <a id="25614" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25561" class="Bound">m</a> <a id="25616" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25563" class="Bound">n</a> <a id="25618" class="Symbol">(</a><a id="25619" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25565" class="Bound">p</a> <a id="25621" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25623" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25567" class="Bound">q</a><a id="25624" class="Symbol">)</a> <a id="25626" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="25632" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25561" class="Bound">m</a> <a id="25634" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25636" class="Symbol">(</a><a id="25637" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25563" class="Bound">n</a> <a id="25639" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25641" class="Symbol">(</a><a id="25642" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25565" class="Bound">p</a> <a id="25644" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25646" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25567" class="Bound">q</a><a id="25647" class="Symbol">))</a>
  <a id="25652" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="25655" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="25660" class="Symbol">(</a><a id="25661" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25561" class="Bound">m</a> <a id="25663" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+_</a><a id="25665" class="Symbol">)</a> <a id="25667" class="Symbol">(</a><a id="25668" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#939" class="Function">sym</a> <a id="25672" class="Symbol">(</a><a id="25673" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11496" class="Function">+-assoc</a> <a id="25681" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25563" class="Bound">n</a> <a id="25683" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25565" class="Bound">p</a> <a id="25685" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25567" class="Bound">q</a><a id="25686" class="Symbol">))</a> <a id="25689" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="25695" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25561" class="Bound">m</a> <a id="25697" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25699" class="Symbol">((</a><a id="25701" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25563" class="Bound">n</a> <a id="25703" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25705" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25565" class="Bound">p</a><a id="25706" class="Symbol">)</a> <a id="25708" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25710" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25567" class="Bound">q</a><a id="25711" class="Symbol">)</a>
  <a id="25715" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="25718" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#939" class="Function">sym</a> <a id="25722" class="Symbol">(</a><a id="25723" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11496" class="Function">+-assoc</a> <a id="25731" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25561" class="Bound">m</a> <a id="25733" class="Symbol">(</a><a id="25734" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25563" class="Bound">n</a> <a id="25736" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25738" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25565" class="Bound">p</a><a id="25739" class="Symbol">)</a> <a id="25741" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25567" class="Bound">q</a><a id="25742" class="Symbol">)</a> <a id="25744" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="25750" class="Symbol">(</a><a id="25751" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25561" class="Bound">m</a> <a id="25753" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25755" class="Symbol">(</a><a id="25756" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25563" class="Bound">n</a> <a id="25758" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25760" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25565" class="Bound">p</a><a id="25761" class="Symbol">))</a> <a id="25764" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25766" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#25567" class="Bound">q</a>
  <a id="25770" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}
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

第三，Agda 支持 Richard Bird 引入的**片段（Section）**记法。我们将应用到
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

此过程可以继续下去。在第 *m* 天我们会知道所有第一个数小于 *m* 的判断。

{::comment}
There is also a completely finite approach to generating the same equations,
which is left as an exercise for the reader.
{:/}

还有一种完全有限的方法来生成同样的等式，它的证明留作读者的练习。

{::comment}
#### Exercise `finite-|-assoc` (stretch) {#finite-plus-assoc}
{:/}

#### 练习 `finite-|-assoc`（延伸） {#finite-plus-assoc}

{::comment}
Write out what is known about associativity of addition on each of the
first four days using a finite story of creation, as
[earlier]({{ site.baseurl }}/Naturals/#finite-creation).
{:/}

请参考[前文]({{ site.baseurl }}/Naturals/#finite-creation)
写出前四天已知的加法结合律的创世故事。

{::comment}
{% raw %}<pre class="Agda"><a id="31460" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="31497" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
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

{% raw %}<pre class="Agda"><a id="+-assoc′"></a><a id="31812" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#31812" class="Function">+-assoc′</a> <a id="31821" class="Symbol">:</a> <a id="31823" class="Symbol">∀</a> <a id="31825" class="Symbol">(</a><a id="31826" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#31826" class="Bound">m</a> <a id="31828" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#31828" class="Bound">n</a> <a id="31830" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#31830" class="Bound">p</a> <a id="31832" class="Symbol">:</a> <a id="31834" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="31835" class="Symbol">)</a> <a id="31837" class="Symbol">→</a> <a id="31839" class="Symbol">(</a><a id="31840" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#31826" class="Bound">m</a> <a id="31842" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="31844" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#31828" class="Bound">n</a><a id="31845" class="Symbol">)</a> <a id="31847" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="31849" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#31830" class="Bound">p</a> <a id="31851" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="31853" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#31826" class="Bound">m</a> <a id="31855" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="31857" class="Symbol">(</a><a id="31858" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#31828" class="Bound">n</a> <a id="31860" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="31862" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#31830" class="Bound">p</a><a id="31863" class="Symbol">)</a>
<a id="31865" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#31812" class="Function">+-assoc′</a> <a id="31874" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="31882" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#31882" class="Bound">n</a> <a id="31884" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#31884" class="Bound">p</a>                          <a id="31911" class="Symbol">=</a>  <a id="31914" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="31919" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#31812" class="Function">+-assoc′</a> <a id="31928" class="Symbol">(</a><a id="31929" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="31933" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#31933" class="Bound">m</a><a id="31934" class="Symbol">)</a> <a id="31936" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#31936" class="Bound">n</a> <a id="31938" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#31938" class="Bound">p</a>  <a id="31941" class="Keyword">rewrite</a> <a id="31949" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#31812" class="Function">+-assoc′</a> <a id="31958" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#31933" class="Bound">m</a> <a id="31960" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#31936" class="Bound">n</a> <a id="31962" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#31938" class="Bound">p</a>  <a id="31965" class="Symbol">=</a>  <a id="31968" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
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

{% raw %}<pre class="Agda"><a id="+-identity′"></a><a id="33270" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33270" class="Function">+-identity′</a> <a id="33282" class="Symbol">:</a> <a id="33284" class="Symbol">∀</a> <a id="33286" class="Symbol">(</a><a id="33287" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33287" class="Bound">n</a> <a id="33289" class="Symbol">:</a> <a id="33291" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="33292" class="Symbol">)</a> <a id="33294" class="Symbol">→</a> <a id="33296" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33287" class="Bound">n</a> <a id="33298" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="33300" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="33305" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="33307" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33287" class="Bound">n</a>
<a id="33309" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33270" class="Function">+-identity′</a> <a id="33321" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="33326" class="Symbol">=</a> <a id="33328" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="33333" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33270" class="Function">+-identity′</a> <a id="33345" class="Symbol">(</a><a id="33346" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="33350" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33350" class="Bound">n</a><a id="33351" class="Symbol">)</a> <a id="33353" class="Keyword">rewrite</a> <a id="33361" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33270" class="Function">+-identity′</a> <a id="33373" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33350" class="Bound">n</a> <a id="33375" class="Symbol">=</a> <a id="33377" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="+-suc′"></a><a id="33383" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33383" class="Function">+-suc′</a> <a id="33390" class="Symbol">:</a> <a id="33392" class="Symbol">∀</a> <a id="33394" class="Symbol">(</a><a id="33395" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33395" class="Bound">m</a> <a id="33397" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33397" class="Bound">n</a> <a id="33399" class="Symbol">:</a> <a id="33401" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="33402" class="Symbol">)</a> <a id="33404" class="Symbol">→</a> <a id="33406" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33395" class="Bound">m</a> <a id="33408" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="33410" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="33414" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33397" class="Bound">n</a> <a id="33416" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="33418" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="33422" class="Symbol">(</a><a id="33423" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33395" class="Bound">m</a> <a id="33425" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="33427" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33397" class="Bound">n</a><a id="33428" class="Symbol">)</a>
<a id="33430" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33383" class="Function">+-suc′</a> <a id="33437" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="33442" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33442" class="Bound">n</a> <a id="33444" class="Symbol">=</a> <a id="33446" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="33451" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33383" class="Function">+-suc′</a> <a id="33458" class="Symbol">(</a><a id="33459" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="33463" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33463" class="Bound">m</a><a id="33464" class="Symbol">)</a> <a id="33466" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33466" class="Bound">n</a> <a id="33468" class="Keyword">rewrite</a> <a id="33476" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33383" class="Function">+-suc′</a> <a id="33483" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33463" class="Bound">m</a> <a id="33485" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33466" class="Bound">n</a> <a id="33487" class="Symbol">=</a> <a id="33489" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="+-comm′"></a><a id="33495" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33495" class="Function">+-comm′</a> <a id="33503" class="Symbol">:</a> <a id="33505" class="Symbol">∀</a> <a id="33507" class="Symbol">(</a><a id="33508" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33508" class="Bound">m</a> <a id="33510" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33510" class="Bound">n</a> <a id="33512" class="Symbol">:</a> <a id="33514" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="33515" class="Symbol">)</a> <a id="33517" class="Symbol">→</a> <a id="33519" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33508" class="Bound">m</a> <a id="33521" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="33523" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33510" class="Bound">n</a> <a id="33525" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="33527" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33510" class="Bound">n</a> <a id="33529" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="33531" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33508" class="Bound">m</a>
<a id="33533" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33495" class="Function">+-comm′</a> <a id="33541" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33541" class="Bound">m</a> <a id="33543" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="33548" class="Keyword">rewrite</a> <a id="33556" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33270" class="Function">+-identity′</a> <a id="33568" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33541" class="Bound">m</a> <a id="33570" class="Symbol">=</a> <a id="33572" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="33577" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33495" class="Function">+-comm′</a> <a id="33585" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33585" class="Bound">m</a> <a id="33587" class="Symbol">(</a><a id="33588" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="33592" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33592" class="Bound">n</a><a id="33593" class="Symbol">)</a> <a id="33595" class="Keyword">rewrite</a> <a id="33603" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33383" class="Function">+-suc′</a> <a id="33610" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33585" class="Bound">m</a> <a id="33612" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33592" class="Bound">n</a> <a id="33614" class="Symbol">|</a> <a id="33616" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33495" class="Function">+-comm′</a> <a id="33624" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33585" class="Bound">m</a> <a id="33626" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#33592" class="Bound">n</a> <a id="33628" class="Symbol">=</a> <a id="33630" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
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

## 交互式构造证明

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
于是我们来编辑这些文本：

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

{% raw %}<pre class="Agda"><a id="38292" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="38329" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
#### Exercise `*-distrib-+` (recommended) {#times-distrib-plus}
{:/}

#### 练习 `*-distrib-+`（推荐） {#times-distrib-plus}

{::comment}
Show multiplication distributes over addition, that is,
{:/}

请证明乘法对加法满足分配律，即对于所有的自然数 `m`、`n` 和 `p`，

    (m + n) * p ≡ m * p + n * p

{::comment}
for all naturals `m`, `n`, and `p`.
{:/}

成立。

{::comment}
{% raw %}<pre class="Agda"><a id="38700" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="38737" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
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
{% raw %}<pre class="Agda"><a id="39070" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="39107" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
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
{% raw %}<pre class="Agda"><a id="39509" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="39546" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

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
{% raw %}<pre class="Agda"><a id="39818" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="39855" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
#### Exercise `∸-|-assoc` {#monus-plus-assoc}
{:/}

#### 练习 `∸-|-assoc` {#monus-plus-assoc}

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
{% raw %}<pre class="Agda"><a id="40194" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="40231" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
#### Exercise `+*^` (stretch)
{:/}

#### 练习 `+*^` （延伸）

{::comment}
Show the following three laws
{:/}

证明下列三条定律

    m ^ (n + p) ≡ (m ^ n) * (m ^ p)
    (m * n) ^ p ≡ (m ^ p) * (n ^ p)
    m ^ (n * p) ≡ (m ^ n) ^ p

{::comment}
for all `m`, `n`, and `p`.
{:/}

对于所有 `m`、`n` 和 `p` 成立。


#### Exercise `Bin-laws` (stretch) {#Bin-laws}
{:/}

#### 练习 `Bin-laws`（延伸） {#Bin-laws}

{::comment}
Recall that
Exercise [Bin]({{ site.baseurl }}/Naturals/#Bin)
defines a datatype of bitstrings representing natural numbers
{:/}

回想练习 [Bin][plfa.Naturals#Bin] 中定义了一种比特串数据类型来表示自然数

{% raw %}<pre class="Agda"><a id="40834" class="Keyword">data</a> <a id="Bin"></a><a id="40839" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#40839" class="Datatype">Bin</a> <a id="40843" class="Symbol">:</a> <a id="40845" class="PrimitiveType">Set</a> <a id="40849" class="Keyword">where</a>
  <a id="Bin.nil"></a><a id="40857" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#40857" class="InductiveConstructor">nil</a> <a id="40861" class="Symbol">:</a> <a id="40863" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#40839" class="Datatype">Bin</a>
  <a id="Bin.x0_"></a><a id="40869" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#40869" class="InductiveConstructor Operator">x0_</a> <a id="40873" class="Symbol">:</a> <a id="40875" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#40839" class="Datatype">Bin</a> <a id="40879" class="Symbol">→</a> <a id="40881" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#40839" class="Datatype">Bin</a>
  <a id="Bin.x1_"></a><a id="40887" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#40887" class="InductiveConstructor Operator">x1_</a> <a id="40891" class="Symbol">:</a> <a id="40893" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#40839" class="Datatype">Bin</a> <a id="40897" class="Symbol">→</a> <a id="40899" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#40839" class="Datatype">Bin</a>
</pre>{% endraw %}
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
{% raw %}<pre class="Agda"><a id="41371" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="41408" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
## Standard library
{:/}

## 标准库

{::comment}
Definitions similar to those in this chapter can be found in the standard library:
{:/}

本章中类似的定义可在标准库中找到：

{% raw %}<pre class="Agda"><a id="41597" class="Keyword">import</a> <a id="41604" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="41624" class="Keyword">using</a> <a id="41630" class="Symbol">(</a><a id="41631" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11578" class="Function">+-assoc</a><a id="41638" class="Symbol">;</a> <a id="41640" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11734" class="Function">+-identityʳ</a><a id="41651" class="Symbol">;</a> <a id="41653" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11370" class="Function">+-suc</a><a id="41658" class="Symbol">;</a> <a id="41660" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a><a id="41666" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
## Unicode
{:/}

## Unicode

{::comment}
This chapter uses the following unicode:
{:/}

本章中使用了以下 Unicode：

{::comment}
    ∀  U+2200  FOR ALL (\forall, \all)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)
    ′  U+2032  PRIME (\')
    ″  U+2033  DOUBLE PRIME (\')
    ‴  U+2034  TRIPLE PRIME (\')
    ⁗  U+2057  QUADRUPLE PRIME (\')
{:/}

    ∀  U+2200  对于所有 (\forall, \all)
    ʳ  U+02B3  修饰符小写字母 r (\^r)
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
