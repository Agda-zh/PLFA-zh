---
src       : "src/plfa/Isomorphism.lagda.md"
title     : "Isomorphism: 同构与嵌入"
layout    : page
prev      : /Equality/
permalink : /Isomorphism/
next      : /Connectives/
translators : ["Fangyi Zhou"]
progress  : 100
---

{% raw %}<pre class="Agda"><a id="185" class="Keyword">module</a> <a id="192" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}" class="Module">plfa.Isomorphism</a> <a id="209" class="Keyword">where</a>
</pre>{% endraw %}
{::comment}
This section introduces isomorphism as a way of asserting that two
types are equal, and embedding as a way of asserting that one type is
smaller than another.  We apply isomorphisms in the next chapter
to demonstrate that operations on types such as product and sum
satisfy properties akin to associativity, commutativity, and
distributivity.
{:/}

本部分介绍同构（Isomorphism）与嵌入（Embedding）。
同构可以断言两个类型是相等的，嵌入可以断言一个类型比另一个类型小。
我们会在下一章中使用同构来展示类型上的运算，例如积或者和，满足类似于交换律、结合律和分配律的性质。


{::comment}
## Imports
{:/}

## 导入

{% raw %}<pre class="Agda"><a id="743" class="Keyword">import</a> <a id="750" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="788" class="Symbol">as</a> <a id="791" class="Module">Eq</a>
<a id="794" class="Keyword">open</a> <a id="799" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="802" class="Keyword">using</a> <a id="808" class="Symbol">(</a><a id="809" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="812" class="Symbol">;</a> <a id="814" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="818" class="Symbol">;</a> <a id="820" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a><a id="824" class="Symbol">;</a> <a id="826" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html#1308" class="Function">cong-app</a><a id="834" class="Symbol">)</a>
<a id="836" class="Keyword">open</a> <a id="841" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2499" class="Module">Eq.≡-Reasoning</a>
<a id="856" class="Keyword">open</a> <a id="861" class="Keyword">import</a> <a id="868" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="877" class="Keyword">using</a> <a id="883" class="Symbol">(</a><a id="884" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="885" class="Symbol">;</a> <a id="887" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="891" class="Symbol">;</a> <a id="893" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="896" class="Symbol">;</a> <a id="898" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="901" class="Symbol">)</a>
<a id="903" class="Keyword">open</a> <a id="908" class="Keyword">import</a> <a id="915" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="935" class="Keyword">using</a> <a id="941" class="Symbol">(</a><a id="942" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a><a id="948" class="Symbol">)</a>
</pre>{% endraw %}

{::comment}
## Lambda expressions
{:/}

## Lambda 表达式

{::comment}
The chapter begins with a few preliminaries that will be useful
here and elsewhere: lambda expressions, function composition, and
extensionality.
{:/}

本章节开头将补充一些有用的基础知识：lambda 表达式，函数组合，以及外延性。

{::comment}
_Lambda expressions_ provide a compact way to define functions without
naming them.  A term of the form
{:/}

*Lambda 表达式*提供了一种简洁的定义函数的方法，且不需要提供函数名。一个如同这样的项：

    λ{ P₁ → N₁; ⋯ ; Pₙ → Nₙ }

{::comment}
is equivalent to a function `f` defined by the equations
{:/}

等同于定义一个函数 `f`，使用下列等式：

    f P₁ = N₁
    ⋯
    f Pₙ = Nₙ

{::comment}
where the `Pₙ` are patterns (left-hand sides of an equation) and the
`Nₙ` are expressions (right-hand side of an equation).
{:/}

其中 `Pₙ` 是模式（即等式的左手边），`Nₙ` 是表达式（即等式的右手边）。

{::comment}
In the case that there is one equation and the pattern is a variable,
we may also use the syntax
{:/}

如果只有一个等式，且模式是一个变量，我们亦可使用下面的语法：

    λ x → N

{::comment}
or
{:/}

或者

    λ (x : A) → N

{::comment}
both of which are equivalent to `λ{x → N}`. The latter allows one to
specify the domain of the function.
{:/}

两个都与 `λ{x → N}` 等价。后者可以指定函数的作用域。

{::comment}
Often using an anonymous lambda expression is more convenient than
using a named function: it avoids a lengthy type declaration; and the
definition appears exactly where the function is used, so there is no
need for the writer to remember to declare it in advance, or for the
reader to search for the definition in the code.
{:/}

往往使用匿名的 lambda 表达式比使用带名字的函数要方便：它避免了冗长的类型声明；
其定义出现在其使用的地方，所以在书写时不需要记得提前声明，在阅读时不需要上下搜索函数定义。


{::comment}
## Function composition
{:/}

## 函数组合 （Function Composition）

{::comment}
In what follows, we will make use of function composition:
{:/}

接下来，我们将使用函数组合：

{% raw %}<pre class="Agda"><a id="_∘_"></a><a id="2703" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2703" class="Function Operator">_∘_</a> <a id="2707" class="Symbol">:</a> <a id="2709" class="Symbol">∀</a> <a id="2711" class="Symbol">{</a><a id="2712" href="plfa.Isomorphism.html#2712" class="Bound">A</a> <a id="2714" href="plfa.Isomorphism.html#2714" class="Bound">B</a> <a id="2716" href="plfa.Isomorphism.html#2716" class="Bound">C</a> <a id="2718" class="Symbol">:</a> <a id="2720" class="PrimitiveType">Set</a><a id="2723" class="Symbol">}</a> <a id="2725" class="Symbol">→</a> <a id="2727" class="Symbol">(</a><a id="2728" href="plfa.Isomorphism.html#2714" class="Bound">B</a> <a id="2730" class="Symbol">→</a> <a id="2732" href="plfa.Isomorphism.html#2716" class="Bound">C</a><a id="2733" class="Symbol">)</a> <a id="2735" class="Symbol">→</a> <a id="2737" class="Symbol">(</a><a id="2738" href="plfa.Isomorphism.html#2712" class="Bound">A</a> <a id="2740" class="Symbol">→</a> <a id="2742" href="plfa.Isomorphism.html#2714" class="Bound">B</a><a id="2743" class="Symbol">)</a> <a id="2745" class="Symbol">→</a> <a id="2747" class="Symbol">(</a><a id="2748" href="plfa.Isomorphism.html#2712" class="Bound">A</a> <a id="2750" class="Symbol">→</a> <a id="2752" href="plfa.Isomorphism.html#2716" class="Bound">C</a><a id="2753" class="Symbol">)</a>
<a id="2755" class="Symbol">(</a><a id="2756" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2756" class="Bound">g</a> <a id="2758" href="plfa.Isomorphism.html#2703" class="Function Operator">∘</a> <a id="2760" href="plfa.Isomorphism.html#2760" class="Bound">f</a><a id="2761" class="Symbol">)</a> <a id="2763" href="plfa.Isomorphism.html#2763" class="Bound">x</a>  <a id="2766" class="Symbol">=</a> <a id="2768" href="plfa.Isomorphism.html#2756" class="Bound">g</a> <a id="2770" class="Symbol">(</a><a id="2771" href="plfa.Isomorphism.html#2760" class="Bound">f</a> <a id="2773" href="plfa.Isomorphism.html#2763" class="Bound">x</a><a id="2774" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Thus, `g ∘ f` is the function that first applies `f` and
then applies `g`.  An equivalent definition, exploiting lambda
expressions, is as follows:
{:/}

`g ∘ f` 是一个函数，先使用函数 `f`，再使用函数 `g`。
一个等价的定义，使用 lambda 表达式，如下：

{% raw %}<pre class="Agda"><a id="_∘′_"></a><a id="3013" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3013" class="Function Operator">_∘′_</a> <a id="3018" class="Symbol">:</a> <a id="3020" class="Symbol">∀</a> <a id="3022" class="Symbol">{</a><a id="3023" href="plfa.Isomorphism.html#3023" class="Bound">A</a> <a id="3025" href="plfa.Isomorphism.html#3025" class="Bound">B</a> <a id="3027" href="plfa.Isomorphism.html#3027" class="Bound">C</a> <a id="3029" class="Symbol">:</a> <a id="3031" class="PrimitiveType">Set</a><a id="3034" class="Symbol">}</a> <a id="3036" class="Symbol">→</a> <a id="3038" class="Symbol">(</a><a id="3039" href="plfa.Isomorphism.html#3025" class="Bound">B</a> <a id="3041" class="Symbol">→</a> <a id="3043" href="plfa.Isomorphism.html#3027" class="Bound">C</a><a id="3044" class="Symbol">)</a> <a id="3046" class="Symbol">→</a> <a id="3048" class="Symbol">(</a><a id="3049" href="plfa.Isomorphism.html#3023" class="Bound">A</a> <a id="3051" class="Symbol">→</a> <a id="3053" href="plfa.Isomorphism.html#3025" class="Bound">B</a><a id="3054" class="Symbol">)</a> <a id="3056" class="Symbol">→</a> <a id="3058" class="Symbol">(</a><a id="3059" href="plfa.Isomorphism.html#3023" class="Bound">A</a> <a id="3061" class="Symbol">→</a> <a id="3063" href="plfa.Isomorphism.html#3027" class="Bound">C</a><a id="3064" class="Symbol">)</a>
<a id="3066" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3066" class="Bound">g</a> <a id="3068" href="plfa.Isomorphism.html#3013" class="Function Operator">∘′</a> <a id="3071" href="plfa.Isomorphism.html#3071" class="Bound">f</a>  <a id="3074" class="Symbol">=</a>  <a id="3077" class="Symbol">λ</a> <a id="3079" href="plfa.Isomorphism.html#3079" class="Bound">x</a> <a id="3081" class="Symbol">→</a> <a id="3083" href="plfa.Isomorphism.html#3066" class="Bound">g</a> <a id="3085" class="Symbol">(</a><a id="3086" href="plfa.Isomorphism.html#3071" class="Bound">f</a> <a id="3088" href="plfa.Isomorphism.html#3079" class="Bound">x</a><a id="3089" class="Symbol">)</a>
</pre>{% endraw %}

{::comment}
## Extensionality {#extensionality}
{:/}

## 外延性（Extensionality） {#extensionality}

{::comment}
Extensionality asserts that the only way to distinguish functions is
by applying them; if two functions applied to the same argument always
yield the same result, then they are the same function.  It is the
converse of `cong-app`, as introduced
[earlier]({{ site.baseurl }}/Equality/#cong).
{:/}

外延性断言了区分函数的唯一方法是应用它们。如果两个函数作用在相同的参数上永远返回相同的结果，
那么两个函数相同。这是 `cong-app` 的逆命题，在[之前]({{ site.baseurl }}/Equality/#cong)有所介绍。

{::comment}
Agda does not presume extensionality, but we can postulate that it holds:
{:/}

Agda 并不预设外延性，但我们可以假设其成立：

{% raw %}<pre class="Agda"><a id="3746" class="Keyword">postulate</a>
  <a id="extensionality"></a><a id="3758" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3758" class="Postulate">extensionality</a> <a id="3773" class="Symbol">:</a> <a id="3775" class="Symbol">∀</a> <a id="3777" class="Symbol">{</a><a id="3778" href="plfa.Isomorphism.html#3778" class="Bound">A</a> <a id="3780" href="plfa.Isomorphism.html#3780" class="Bound">B</a> <a id="3782" class="Symbol">:</a> <a id="3784" class="PrimitiveType">Set</a><a id="3787" class="Symbol">}</a> <a id="3789" class="Symbol">{</a><a id="3790" href="plfa.Isomorphism.html#3790" class="Bound">f</a> <a id="3792" href="plfa.Isomorphism.html#3792" class="Bound">g</a> <a id="3794" class="Symbol">:</a> <a id="3796" href="plfa.Isomorphism.html#3778" class="Bound">A</a> <a id="3798" class="Symbol">→</a> <a id="3800" href="plfa.Isomorphism.html#3780" class="Bound">B</a><a id="3801" class="Symbol">}</a>
    <a id="3807" class="Symbol">→</a> <a id="3809" class="Symbol">(∀</a> <a id="3812" class="Symbol">(</a><a id="3813" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3813" class="Bound">x</a> <a id="3815" class="Symbol">:</a> <a id="3817" href="plfa.Isomorphism.html#3778" class="Bound">A</a><a id="3818" class="Symbol">)</a> <a id="3820" class="Symbol">→</a> <a id="3822" href="plfa.Isomorphism.html#3790" class="Bound">f</a> <a id="3824" href="plfa.Isomorphism.html#3813" class="Bound">x</a> <a id="3826" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="3828" href="plfa.Isomorphism.html#3792" class="Bound">g</a> <a id="3830" href="plfa.Isomorphism.html#3813" class="Bound">x</a><a id="3831" class="Symbol">)</a>
      <a id="3839" class="Comment">-----------------------</a>
    <a id="3867" class="Symbol">→</a> <a id="3869" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3790" class="Bound">f</a> <a id="3871" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="3873" href="plfa.Isomorphism.html#3792" class="Bound">g</a>
</pre>{% endraw %}
{::comment}
Postulating extensionality does not lead to difficulties, as it is
known to be consistent with the theory that underlies Agda.
{:/}

假设外延性不会造成困顿，因为我们知道它与 Agda 使用的理论是连贯一致的。

{::comment}
As an example, consider that we need results from two libraries,
one where addition is defined, as in
Chapter [Naturals]({{ site.baseurl }}/Naturals/),
and one where it is defined the other way around.
{:/}

举个例子，我们考虑两个库都定义了加法，一个按照我们在 [Naturals][plfa.Naturals]
章节中那样定义，另一个如下，反过来定义：

{% raw %}<pre class="Agda"><a id="_+′_"></a><a id="4364" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4364" class="Function Operator">_+′_</a> <a id="4369" class="Symbol">:</a> <a id="4371" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="4373" class="Symbol">→</a> <a id="4375" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="4377" class="Symbol">→</a> <a id="4379" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="4381" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4381" class="Bound">m</a> <a id="4383" href="plfa.Isomorphism.html#4364" class="Function Operator">+′</a> <a id="4386" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>  <a id="4392" class="Symbol">=</a> <a id="4394" href="plfa.Isomorphism.html#4381" class="Bound">m</a>
<a id="4396" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4396" class="Bound">m</a> <a id="4398" href="plfa.Isomorphism.html#4364" class="Function Operator">+′</a> <a id="4401" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="4405" href="plfa.Isomorphism.html#4405" class="Bound">n</a> <a id="4407" class="Symbol">=</a> <a id="4409" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="4413" class="Symbol">(</a><a id="4414" href="plfa.Isomorphism.html#4396" class="Bound">m</a> <a id="4416" href="plfa.Isomorphism.html#4364" class="Function Operator">+′</a> <a id="4419" href="plfa.Isomorphism.html#4405" class="Bound">n</a><a id="4420" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Applying commutativity, it is easy to show that both operators always
return the same result given the same arguments:
{:/}

通过使用交换律，我们可以简单地证明两个运算符在给定相同参数的情况下，
会返回相同的值：

{% raw %}<pre class="Agda"><a id="same-app"></a><a id="4613" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4613" class="Function">same-app</a> <a id="4622" class="Symbol">:</a> <a id="4624" class="Symbol">∀</a> <a id="4626" class="Symbol">(</a><a id="4627" href="plfa.Isomorphism.html#4627" class="Bound">m</a> <a id="4629" href="plfa.Isomorphism.html#4629" class="Bound">n</a> <a id="4631" class="Symbol">:</a> <a id="4633" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="4634" class="Symbol">)</a> <a id="4636" class="Symbol">→</a> <a id="4638" href="plfa.Isomorphism.html#4627" class="Bound">m</a> <a id="4640" href="plfa.Isomorphism.html#4364" class="Function Operator">+′</a> <a id="4643" href="plfa.Isomorphism.html#4629" class="Bound">n</a> <a id="4645" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="4647" href="plfa.Isomorphism.html#4627" class="Bound">m</a> <a id="4649" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="4651" href="plfa.Isomorphism.html#4629" class="Bound">n</a>
<a id="4653" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4613" class="Function">same-app</a> <a id="4662" href="plfa.Isomorphism.html#4662" class="Bound">m</a> <a id="4664" href="plfa.Isomorphism.html#4664" class="Bound">n</a> <a id="4666" class="Keyword">rewrite</a> <a id="4674" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a> <a id="4681" href="plfa.Isomorphism.html#4662" class="Bound">m</a> <a id="4683" href="plfa.Isomorphism.html#4664" class="Bound">n</a> <a id="4685" class="Symbol">=</a> <a id="4687" href="plfa.Isomorphism.html#4708" class="Function">helper</a> <a id="4694" href="plfa.Isomorphism.html#4662" class="Bound">m</a> <a id="4696" href="plfa.Isomorphism.html#4664" class="Bound">n</a>
  <a id="4700" class="Keyword">where</a>
  <a id="4708" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4708" class="Function">helper</a> <a id="4715" class="Symbol">:</a> <a id="4717" class="Symbol">∀</a> <a id="4719" class="Symbol">(</a><a id="4720" href="plfa.Isomorphism.html#4720" class="Bound">m</a> <a id="4722" href="plfa.Isomorphism.html#4722" class="Bound">n</a> <a id="4724" class="Symbol">:</a> <a id="4726" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="4727" class="Symbol">)</a> <a id="4729" class="Symbol">→</a> <a id="4731" href="plfa.Isomorphism.html#4720" class="Bound">m</a> <a id="4733" href="plfa.Isomorphism.html#4364" class="Function Operator">+′</a> <a id="4736" href="plfa.Isomorphism.html#4722" class="Bound">n</a> <a id="4738" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="4740" href="plfa.Isomorphism.html#4722" class="Bound">n</a> <a id="4742" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="4744" href="plfa.Isomorphism.html#4720" class="Bound">m</a>
  <a id="4748" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4708" class="Function">helper</a> <a id="4755" href="plfa.Isomorphism.html#4755" class="Bound">m</a> <a id="4757" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="4765" class="Symbol">=</a> <a id="4767" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
  <a id="4774" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4708" class="Function">helper</a> <a id="4781" href="plfa.Isomorphism.html#4781" class="Bound">m</a> <a id="4783" class="Symbol">(</a><a id="4784" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="4788" href="plfa.Isomorphism.html#4788" class="Bound">n</a><a id="4789" class="Symbol">)</a> <a id="4791" class="Symbol">=</a> <a id="4793" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="4798" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="4802" class="Symbol">(</a><a id="4803" href="plfa.Isomorphism.html#4708" class="Function">helper</a> <a id="4810" href="plfa.Isomorphism.html#4781" class="Bound">m</a> <a id="4812" href="plfa.Isomorphism.html#4788" class="Bound">n</a><a id="4813" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
However, it might be convenient to assert that the two operators are
actually indistinguishable. This we can do via two applications of
extensionality:
{:/}

然而，有时断言两个运算符是无法区分的会更加方便。我们可以使用两次外延性：

{% raw %}<pre class="Agda"><a id="same"></a><a id="5032" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5032" class="Function">same</a> <a id="5037" class="Symbol">:</a> <a id="5039" href="plfa.Isomorphism.html#4364" class="Function Operator">_+′_</a> <a id="5044" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5046" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a>
<a id="5050" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5032" class="Function">same</a> <a id="5055" class="Symbol">=</a> <a id="5057" href="plfa.Isomorphism.html#3758" class="Postulate">extensionality</a> <a id="5072" class="Symbol">(λ</a> <a id="5075" href="plfa.Isomorphism.html#5075" class="Bound">m</a> <a id="5077" class="Symbol">→</a> <a id="5079" href="plfa.Isomorphism.html#3758" class="Postulate">extensionality</a> <a id="5094" class="Symbol">(λ</a> <a id="5097" href="plfa.Isomorphism.html#5097" class="Bound">n</a> <a id="5099" class="Symbol">→</a> <a id="5101" href="plfa.Isomorphism.html#4613" class="Function">same-app</a> <a id="5110" href="plfa.Isomorphism.html#5075" class="Bound">m</a> <a id="5112" href="plfa.Isomorphism.html#5097" class="Bound">n</a><a id="5113" class="Symbol">))</a>
</pre>{% endraw %}
{::comment}
We occasionally need to postulate extensionality in what follows.
{:/}

我们偶尔需要在之后的情况中假设外延性。

More generally, we may wish to postulate extensionality for
dependent functions.
{% raw %}<pre class="Agda"><a id="5311" class="Keyword">postulate</a>
  <a id="∀-extensionality"></a><a id="5323" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5323" class="Postulate">∀-extensionality</a> <a id="5340" class="Symbol">:</a> <a id="5342" class="Symbol">∀</a> <a id="5344" class="Symbol">{</a><a id="5345" href="plfa.Isomorphism.html#5345" class="Bound">A</a> <a id="5347" class="Symbol">:</a> <a id="5349" class="PrimitiveType">Set</a><a id="5352" class="Symbol">}</a> <a id="5354" class="Symbol">{</a><a id="5355" href="plfa.Isomorphism.html#5355" class="Bound">B</a> <a id="5357" class="Symbol">:</a> <a id="5359" href="plfa.Isomorphism.html#5345" class="Bound">A</a> <a id="5361" class="Symbol">→</a> <a id="5363" class="PrimitiveType">Set</a><a id="5366" class="Symbol">}</a> <a id="5368" class="Symbol">{</a><a id="5369" href="plfa.Isomorphism.html#5369" class="Bound">f</a> <a id="5371" href="plfa.Isomorphism.html#5371" class="Bound">g</a> <a id="5373" class="Symbol">:</a> <a id="5375" class="Symbol">∀(</a><a id="5377" href="plfa.Isomorphism.html#5377" class="Bound">x</a> <a id="5379" class="Symbol">:</a> <a id="5381" href="plfa.Isomorphism.html#5345" class="Bound">A</a><a id="5382" class="Symbol">)</a> <a id="5384" class="Symbol">→</a> <a id="5386" href="plfa.Isomorphism.html#5355" class="Bound">B</a> <a id="5388" href="plfa.Isomorphism.html#5377" class="Bound">x</a><a id="5389" class="Symbol">}</a>
    <a id="5395" class="Symbol">→</a> <a id="5397" class="Symbol">(∀</a> <a id="5400" class="Symbol">(</a><a id="5401" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5401" class="Bound">x</a> <a id="5403" class="Symbol">:</a> <a id="5405" href="plfa.Isomorphism.html#5345" class="Bound">A</a><a id="5406" class="Symbol">)</a> <a id="5408" class="Symbol">→</a> <a id="5410" href="plfa.Isomorphism.html#5369" class="Bound">f</a> <a id="5412" href="plfa.Isomorphism.html#5401" class="Bound">x</a> <a id="5414" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5416" href="plfa.Isomorphism.html#5371" class="Bound">g</a> <a id="5418" href="plfa.Isomorphism.html#5401" class="Bound">x</a><a id="5419" class="Symbol">)</a>
      <a id="5427" class="Comment">-----------------------</a>
    <a id="5455" class="Symbol">→</a> <a id="5457" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5369" class="Bound">f</a> <a id="5459" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5461" href="plfa.Isomorphism.html#5371" class="Bound">g</a>
</pre>{% endraw %}Here the type of `f` and `g` has changed from `A → B` to
`∀ (x : A) → B x`, generalising ordinary functions to
dependent functions.


{::comment}
## Isomorphism
{:/}

## 同构（Isomorphism）

{::comment}
Two sets are isomorphic if they are in one-to-one correspondence.
Here is a formal definition of isomorphism:
{:/}

如果两个集合有一一对应的关系，那么它们是同构的。
下面是同构的正式定义：

{% raw %}<pre class="Agda"><a id="5824" class="Keyword">infix</a> <a id="5830" class="Number">0</a> <a id="5832" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5843" class="Record Operator">_≃_</a>
<a id="5836" class="Keyword">record</a> <a id="_≃_"></a><a id="5843" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5843" class="Record Operator">_≃_</a> <a id="5847" class="Symbol">(</a><a id="5848" href="plfa.Isomorphism.html#5848" class="Bound">A</a> <a id="5850" href="plfa.Isomorphism.html#5850" class="Bound">B</a> <a id="5852" class="Symbol">:</a> <a id="5854" class="PrimitiveType">Set</a><a id="5857" class="Symbol">)</a> <a id="5859" class="Symbol">:</a> <a id="5861" class="PrimitiveType">Set</a> <a id="5865" class="Keyword">where</a>
  <a id="5873" class="Keyword">field</a>
    <a id="_≃_.to"></a><a id="5883" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5883" class="Field">to</a>   <a id="5888" class="Symbol">:</a> <a id="5890" href="plfa.Isomorphism.html#5848" class="Bound">A</a> <a id="5892" class="Symbol">→</a> <a id="5894" href="plfa.Isomorphism.html#5850" class="Bound">B</a>
    <a id="_≃_.from"></a><a id="5900" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5900" class="Field">from</a> <a id="5905" class="Symbol">:</a> <a id="5907" href="plfa.Isomorphism.html#5850" class="Bound">B</a> <a id="5909" class="Symbol">→</a> <a id="5911" href="plfa.Isomorphism.html#5848" class="Bound">A</a>
    <a id="_≃_.from∘to"></a><a id="5917" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5917" class="Field">from∘to</a> <a id="5925" class="Symbol">:</a> <a id="5927" class="Symbol">∀</a> <a id="5929" class="Symbol">(</a><a id="5930" href="plfa.Isomorphism.html#5930" class="Bound">x</a> <a id="5932" class="Symbol">:</a> <a id="5934" href="plfa.Isomorphism.html#5848" class="Bound">A</a><a id="5935" class="Symbol">)</a> <a id="5937" class="Symbol">→</a> <a id="5939" href="plfa.Isomorphism.html#5900" class="Field">from</a> <a id="5944" class="Symbol">(</a><a id="5945" href="plfa.Isomorphism.html#5883" class="Field">to</a> <a id="5948" href="plfa.Isomorphism.html#5930" class="Bound">x</a><a id="5949" class="Symbol">)</a> <a id="5951" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5953" href="plfa.Isomorphism.html#5930" class="Bound">x</a>
    <a id="_≃_.to∘from"></a><a id="5959" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5959" class="Field">to∘from</a> <a id="5967" class="Symbol">:</a> <a id="5969" class="Symbol">∀</a> <a id="5971" class="Symbol">(</a><a id="5972" href="plfa.Isomorphism.html#5972" class="Bound">y</a> <a id="5974" class="Symbol">:</a> <a id="5976" href="plfa.Isomorphism.html#5850" class="Bound">B</a><a id="5977" class="Symbol">)</a> <a id="5979" class="Symbol">→</a> <a id="5981" href="plfa.Isomorphism.html#5883" class="Field">to</a> <a id="5984" class="Symbol">(</a><a id="5985" href="plfa.Isomorphism.html#5900" class="Field">from</a> <a id="5990" href="plfa.Isomorphism.html#5972" class="Bound">y</a><a id="5991" class="Symbol">)</a> <a id="5993" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5995" href="plfa.Isomorphism.html#5972" class="Bound">y</a>
<a id="5997" class="Keyword">open</a> <a id="6002" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5843" class="Module Operator">_≃_</a>
</pre>{% endraw %}
{::comment}
Let's unpack the definition. An isomorphism between sets `A` and `B` consists
of four things:
+ A function `to` from `A` to `B`,
+ A function `from` from `B` back to `A`,
+ Evidence `from∘to` asserting that `from` is a *left-inverse* for `to`,
+ Evidence `to∘from` asserting that `from` is a *right-inverse* for `to`.
{:/}

我们来一一展开这个定义。一个集合 `A` 和 `B` 之间的同构有四个要素：
+ 从 `A` 到 `B` 的函数 `to`
+ 从 `B` 回到 `A` 的函数 `from`
+ `from` 是 `to` 的*左逆*（left-inverse）的证明 `from∘to`
+ `from` 是 `to` 的*右逆*（right-inverse）的证明 `to∘from`

{::comment}
In particular, the third asserts that `from ∘ to` is the identity, and
the fourth that `to ∘ from` is the identity, hence the names.
The declaration `open _≃_` makes available the names `to`, `from`,
`from∘to`, and `to∘from`, otherwise we would need to write `_≃_.to` and so on.
{:/}

具体来说，第三条断言了 `from ∘ to` 是恒等函数，第四条断言了 `to ∘ from` 是恒等函数，
它们的名称由此得来。声明 `open _≃_` 使得 `to`、`from`、`from∘to` 和 `to∘from`
在当前作用域内可用，否则我们需要使用类似 `_≃_.to` 的写法。

{::comment}
The above is our first use of records. A record declaration is equivalent
to a corresponding inductive data declaration:
{:/}

这是我们第一次使用记录（Record）。记录声明等同于下面的归纳数据声明：

{% raw %}<pre class="Agda"><a id="7167" class="Keyword">data</a> <a id="_≃′_"></a><a id="7172" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7172" class="Datatype Operator">_≃′_</a> <a id="7177" class="Symbol">(</a><a id="7178" href="plfa.Isomorphism.html#7178" class="Bound">A</a> <a id="7180" href="plfa.Isomorphism.html#7180" class="Bound">B</a> <a id="7182" class="Symbol">:</a> <a id="7184" class="PrimitiveType">Set</a><a id="7187" class="Symbol">):</a> <a id="7190" class="PrimitiveType">Set</a> <a id="7194" class="Keyword">where</a>
  <a id="_≃′_.mk-≃′"></a><a id="7202" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7202" class="InductiveConstructor">mk-≃′</a> <a id="7208" class="Symbol">:</a> <a id="7210" class="Symbol">∀</a> <a id="7212" class="Symbol">(</a><a id="7213" href="plfa.Isomorphism.html#7213" class="Bound">to</a> <a id="7216" class="Symbol">:</a> <a id="7218" href="plfa.Isomorphism.html#7178" class="Bound">A</a> <a id="7220" class="Symbol">→</a> <a id="7222" href="plfa.Isomorphism.html#7180" class="Bound">B</a><a id="7223" class="Symbol">)</a> <a id="7225" class="Symbol">→</a>
          <a id="7237" class="Symbol">∀</a> <a id="7239" class="Symbol">(</a><a id="7240" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7240" class="Bound">from</a> <a id="7245" class="Symbol">:</a> <a id="7247" href="plfa.Isomorphism.html#7180" class="Bound">B</a> <a id="7249" class="Symbol">→</a> <a id="7251" href="plfa.Isomorphism.html#7178" class="Bound">A</a><a id="7252" class="Symbol">)</a> <a id="7254" class="Symbol">→</a>
          <a id="7266" class="Symbol">∀</a> <a id="7268" class="Symbol">(</a><a id="7269" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7269" class="Bound">from∘to</a> <a id="7277" class="Symbol">:</a> <a id="7279" class="Symbol">(∀</a> <a id="7282" class="Symbol">(</a><a id="7283" href="plfa.Isomorphism.html#7283" class="Bound">x</a> <a id="7285" class="Symbol">:</a> <a id="7287" href="plfa.Isomorphism.html#7178" class="Bound">A</a><a id="7288" class="Symbol">)</a> <a id="7290" class="Symbol">→</a> <a id="7292" href="plfa.Isomorphism.html#7240" class="Bound">from</a> <a id="7297" class="Symbol">(</a><a id="7298" href="plfa.Isomorphism.html#7213" class="Bound">to</a> <a id="7301" href="plfa.Isomorphism.html#7283" class="Bound">x</a><a id="7302" class="Symbol">)</a> <a id="7304" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="7306" href="plfa.Isomorphism.html#7283" class="Bound">x</a><a id="7307" class="Symbol">))</a> <a id="7310" class="Symbol">→</a>
          <a id="7322" class="Symbol">∀</a> <a id="7324" class="Symbol">(</a><a id="7325" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7325" class="Bound">to∘from</a> <a id="7333" class="Symbol">:</a> <a id="7335" class="Symbol">(∀</a> <a id="7338" class="Symbol">(</a><a id="7339" href="plfa.Isomorphism.html#7339" class="Bound">y</a> <a id="7341" class="Symbol">:</a> <a id="7343" href="plfa.Isomorphism.html#7180" class="Bound">B</a><a id="7344" class="Symbol">)</a> <a id="7346" class="Symbol">→</a> <a id="7348" href="plfa.Isomorphism.html#7213" class="Bound">to</a> <a id="7351" class="Symbol">(</a><a id="7352" href="plfa.Isomorphism.html#7240" class="Bound">from</a> <a id="7357" href="plfa.Isomorphism.html#7339" class="Bound">y</a><a id="7358" class="Symbol">)</a> <a id="7360" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="7362" href="plfa.Isomorphism.html#7339" class="Bound">y</a><a id="7363" class="Symbol">))</a> <a id="7366" class="Symbol">→</a>
          <a id="7378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7178" class="Bound">A</a> <a id="7380" href="plfa.Isomorphism.html#7172" class="Datatype Operator">≃′</a> <a id="7383" href="plfa.Isomorphism.html#7180" class="Bound">B</a>

<a id="to′"></a><a id="7386" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7386" class="Function">to′</a> <a id="7390" class="Symbol">:</a> <a id="7392" class="Symbol">∀</a> <a id="7394" class="Symbol">{</a><a id="7395" href="plfa.Isomorphism.html#7395" class="Bound">A</a> <a id="7397" href="plfa.Isomorphism.html#7397" class="Bound">B</a> <a id="7399" class="Symbol">:</a> <a id="7401" class="PrimitiveType">Set</a><a id="7404" class="Symbol">}</a> <a id="7406" class="Symbol">→</a> <a id="7408" class="Symbol">(</a><a id="7409" href="plfa.Isomorphism.html#7395" class="Bound">A</a> <a id="7411" href="plfa.Isomorphism.html#7172" class="Datatype Operator">≃′</a> <a id="7414" href="plfa.Isomorphism.html#7397" class="Bound">B</a><a id="7415" class="Symbol">)</a> <a id="7417" class="Symbol">→</a> <a id="7419" class="Symbol">(</a><a id="7420" href="plfa.Isomorphism.html#7395" class="Bound">A</a> <a id="7422" class="Symbol">→</a> <a id="7424" href="plfa.Isomorphism.html#7397" class="Bound">B</a><a id="7425" class="Symbol">)</a>
<a id="7427" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7386" class="Function">to′</a> <a id="7431" class="Symbol">(</a><a id="7432" href="plfa.Isomorphism.html#7202" class="InductiveConstructor">mk-≃′</a> <a id="7438" href="plfa.Isomorphism.html#7438" class="Bound">f</a> <a id="7440" href="plfa.Isomorphism.html#7440" class="Bound">g</a> <a id="7442" href="plfa.Isomorphism.html#7442" class="Bound">g∘f</a> <a id="7446" href="plfa.Isomorphism.html#7446" class="Bound">f∘g</a><a id="7449" class="Symbol">)</a> <a id="7451" class="Symbol">=</a> <a id="7453" href="plfa.Isomorphism.html#7438" class="Bound">f</a>

<a id="from′"></a><a id="7456" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7456" class="Function">from′</a> <a id="7462" class="Symbol">:</a> <a id="7464" class="Symbol">∀</a> <a id="7466" class="Symbol">{</a><a id="7467" href="plfa.Isomorphism.html#7467" class="Bound">A</a> <a id="7469" href="plfa.Isomorphism.html#7469" class="Bound">B</a> <a id="7471" class="Symbol">:</a> <a id="7473" class="PrimitiveType">Set</a><a id="7476" class="Symbol">}</a> <a id="7478" class="Symbol">→</a> <a id="7480" class="Symbol">(</a><a id="7481" href="plfa.Isomorphism.html#7467" class="Bound">A</a> <a id="7483" href="plfa.Isomorphism.html#7172" class="Datatype Operator">≃′</a> <a id="7486" href="plfa.Isomorphism.html#7469" class="Bound">B</a><a id="7487" class="Symbol">)</a> <a id="7489" class="Symbol">→</a> <a id="7491" class="Symbol">(</a><a id="7492" href="plfa.Isomorphism.html#7469" class="Bound">B</a> <a id="7494" class="Symbol">→</a> <a id="7496" href="plfa.Isomorphism.html#7467" class="Bound">A</a><a id="7497" class="Symbol">)</a>
<a id="7499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7456" class="Function">from′</a> <a id="7505" class="Symbol">(</a><a id="7506" href="plfa.Isomorphism.html#7202" class="InductiveConstructor">mk-≃′</a> <a id="7512" href="plfa.Isomorphism.html#7512" class="Bound">f</a> <a id="7514" href="plfa.Isomorphism.html#7514" class="Bound">g</a> <a id="7516" href="plfa.Isomorphism.html#7516" class="Bound">g∘f</a> <a id="7520" href="plfa.Isomorphism.html#7520" class="Bound">f∘g</a><a id="7523" class="Symbol">)</a> <a id="7525" class="Symbol">=</a> <a id="7527" href="plfa.Isomorphism.html#7514" class="Bound">g</a>

<a id="from∘to′"></a><a id="7530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7530" class="Function">from∘to′</a> <a id="7539" class="Symbol">:</a> <a id="7541" class="Symbol">∀</a> <a id="7543" class="Symbol">{</a><a id="7544" href="plfa.Isomorphism.html#7544" class="Bound">A</a> <a id="7546" href="plfa.Isomorphism.html#7546" class="Bound">B</a> <a id="7548" class="Symbol">:</a> <a id="7550" class="PrimitiveType">Set</a><a id="7553" class="Symbol">}</a> <a id="7555" class="Symbol">→</a> <a id="7557" class="Symbol">(</a><a id="7558" href="plfa.Isomorphism.html#7558" class="Bound">A≃B</a> <a id="7562" class="Symbol">:</a> <a id="7564" href="plfa.Isomorphism.html#7544" class="Bound">A</a> <a id="7566" href="plfa.Isomorphism.html#7172" class="Datatype Operator">≃′</a> <a id="7569" href="plfa.Isomorphism.html#7546" class="Bound">B</a><a id="7570" class="Symbol">)</a> <a id="7572" class="Symbol">→</a> <a id="7574" class="Symbol">(∀</a> <a id="7577" class="Symbol">(</a><a id="7578" href="plfa.Isomorphism.html#7578" class="Bound">x</a> <a id="7580" class="Symbol">:</a> <a id="7582" href="plfa.Isomorphism.html#7544" class="Bound">A</a><a id="7583" class="Symbol">)</a> <a id="7585" class="Symbol">→</a> <a id="7587" href="plfa.Isomorphism.html#7456" class="Function">from′</a> <a id="7593" href="plfa.Isomorphism.html#7558" class="Bound">A≃B</a> <a id="7597" class="Symbol">(</a><a id="7598" href="plfa.Isomorphism.html#7386" class="Function">to′</a> <a id="7602" href="plfa.Isomorphism.html#7558" class="Bound">A≃B</a> <a id="7606" href="plfa.Isomorphism.html#7578" class="Bound">x</a><a id="7607" class="Symbol">)</a> <a id="7609" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="7611" href="plfa.Isomorphism.html#7578" class="Bound">x</a><a id="7612" class="Symbol">)</a>
<a id="7614" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7530" class="Function">from∘to′</a> <a id="7623" class="Symbol">(</a><a id="7624" href="plfa.Isomorphism.html#7202" class="InductiveConstructor">mk-≃′</a> <a id="7630" href="plfa.Isomorphism.html#7630" class="Bound">f</a> <a id="7632" href="plfa.Isomorphism.html#7632" class="Bound">g</a> <a id="7634" href="plfa.Isomorphism.html#7634" class="Bound">g∘f</a> <a id="7638" href="plfa.Isomorphism.html#7638" class="Bound">f∘g</a><a id="7641" class="Symbol">)</a> <a id="7643" class="Symbol">=</a> <a id="7645" href="plfa.Isomorphism.html#7634" class="Bound">g∘f</a>

<a id="to∘from′"></a><a id="7650" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7650" class="Function">to∘from′</a> <a id="7659" class="Symbol">:</a> <a id="7661" class="Symbol">∀</a> <a id="7663" class="Symbol">{</a><a id="7664" href="plfa.Isomorphism.html#7664" class="Bound">A</a> <a id="7666" href="plfa.Isomorphism.html#7666" class="Bound">B</a> <a id="7668" class="Symbol">:</a> <a id="7670" class="PrimitiveType">Set</a><a id="7673" class="Symbol">}</a> <a id="7675" class="Symbol">→</a> <a id="7677" class="Symbol">(</a><a id="7678" href="plfa.Isomorphism.html#7678" class="Bound">A≃B</a> <a id="7682" class="Symbol">:</a> <a id="7684" href="plfa.Isomorphism.html#7664" class="Bound">A</a> <a id="7686" href="plfa.Isomorphism.html#7172" class="Datatype Operator">≃′</a> <a id="7689" href="plfa.Isomorphism.html#7666" class="Bound">B</a><a id="7690" class="Symbol">)</a> <a id="7692" class="Symbol">→</a> <a id="7694" class="Symbol">(∀</a> <a id="7697" class="Symbol">(</a><a id="7698" href="plfa.Isomorphism.html#7698" class="Bound">y</a> <a id="7700" class="Symbol">:</a> <a id="7702" href="plfa.Isomorphism.html#7666" class="Bound">B</a><a id="7703" class="Symbol">)</a> <a id="7705" class="Symbol">→</a> <a id="7707" href="plfa.Isomorphism.html#7386" class="Function">to′</a> <a id="7711" href="plfa.Isomorphism.html#7678" class="Bound">A≃B</a> <a id="7715" class="Symbol">(</a><a id="7716" href="plfa.Isomorphism.html#7456" class="Function">from′</a> <a id="7722" href="plfa.Isomorphism.html#7678" class="Bound">A≃B</a> <a id="7726" href="plfa.Isomorphism.html#7698" class="Bound">y</a><a id="7727" class="Symbol">)</a> <a id="7729" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="7731" href="plfa.Isomorphism.html#7698" class="Bound">y</a><a id="7732" class="Symbol">)</a>
<a id="7734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7650" class="Function">to∘from′</a> <a id="7743" class="Symbol">(</a><a id="7744" href="plfa.Isomorphism.html#7202" class="InductiveConstructor">mk-≃′</a> <a id="7750" href="plfa.Isomorphism.html#7750" class="Bound">f</a> <a id="7752" href="plfa.Isomorphism.html#7752" class="Bound">g</a> <a id="7754" href="plfa.Isomorphism.html#7754" class="Bound">g∘f</a> <a id="7758" href="plfa.Isomorphism.html#7758" class="Bound">f∘g</a><a id="7761" class="Symbol">)</a> <a id="7763" class="Symbol">=</a> <a id="7765" href="plfa.Isomorphism.html#7758" class="Bound">f∘g</a>
</pre>{% endraw %}
{::comment}
We construct values of the record type with the syntax
{:/}

我们用下面的语法来构造一个记录类型的值：

    record
      { to    = f
      ; from  = g
      ; from∘to = g∘f
      ; to∘from = f∘g
      }

{::comment}
which corresponds to using the constructor of the corresponding
inductive type
{:/}

这与使用相应的归纳类型的构造子对应：

    mk-≃′ f g g∘f f∘g

{::comment}
where `f`, `g`, `g∘f`, and `f∘g` are values of suitable types.
{:/}

其中 `f`、`g`、`g∘f` 和 `f∘g` 是相应类型的值。


{::comment}
## Isomorphism is an equivalence
{:/}

## 同构是一个等价关系

{::comment}
Isomorphism is an equivalence, meaning that it is reflexive, symmetric,
and transitive.  To show isomorphism is reflexive, we take both `to`
and `from` to be the identity function:
{:/}

同构是一个等价关系。这意味着它自反、对称、传递。要证明同构是自反的，我们用恒等函数
作为 `to` 和 `from`：

{% raw %}<pre class="Agda"><a id="≃-refl"></a><a id="8555" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8555" class="Function">≃-refl</a> <a id="8562" class="Symbol">:</a> <a id="8564" class="Symbol">∀</a> <a id="8566" class="Symbol">{</a><a id="8567" href="plfa.Isomorphism.html#8567" class="Bound">A</a> <a id="8569" class="Symbol">:</a> <a id="8571" class="PrimitiveType">Set</a><a id="8574" class="Symbol">}</a>
    <a id="8580" class="Comment">-----</a>
  <a id="8588" class="Symbol">→</a> <a id="8590" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8567" class="Bound">A</a> <a id="8592" href="plfa.Isomorphism.html#5843" class="Record Operator">≃</a> <a id="8594" href="plfa.Isomorphism.html#8567" class="Bound">A</a>
<a id="8596" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8555" class="Function">≃-refl</a> <a id="8603" class="Symbol">=</a>
  <a id="8607" class="Keyword">record</a>
    <a id="8618" class="Symbol">{</a> <a id="8620" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5883" class="Field">to</a>      <a id="8628" class="Symbol">=</a> <a id="8630" class="Symbol">λ{</a><a id="8632" href="plfa.Isomorphism.html#8632" class="Bound">x</a> <a id="8634" class="Symbol">→</a> <a id="8636" href="plfa.Isomorphism.html#8632" class="Bound">x</a><a id="8637" class="Symbol">}</a>
    <a id="8643" class="Symbol">;</a> <a id="8645" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5900" class="Field">from</a>    <a id="8653" class="Symbol">=</a> <a id="8655" class="Symbol">λ{</a><a id="8657" href="plfa.Isomorphism.html#8657" class="Bound">y</a> <a id="8659" class="Symbol">→</a> <a id="8661" href="plfa.Isomorphism.html#8657" class="Bound">y</a><a id="8662" class="Symbol">}</a>
    <a id="8668" class="Symbol">;</a> <a id="8670" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5917" class="Field">from∘to</a> <a id="8678" class="Symbol">=</a> <a id="8680" class="Symbol">λ{</a><a id="8682" href="plfa.Isomorphism.html#8682" class="Bound">x</a> <a id="8684" class="Symbol">→</a> <a id="8686" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="8690" class="Symbol">}</a>
    <a id="8696" class="Symbol">;</a> <a id="8698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5959" class="Field">to∘from</a> <a id="8706" class="Symbol">=</a> <a id="8708" class="Symbol">λ{</a><a id="8710" href="plfa.Isomorphism.html#8710" class="Bound">y</a> <a id="8712" class="Symbol">→</a> <a id="8714" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="8718" class="Symbol">}</a>
    <a id="8724" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
In the above, `to` and `from` are both bound to identity functions,
and `from∘to` and `to∘from` are both bound to functions that discard
their argument and return `refl`.  In this case, `refl` alone is an
adequate proof since for the left inverse, `from (to x)`
simplifies to `x`, and similarly for the right inverse.
{:/}

如上，`to` 和 `from` 都是恒等函数，`from∘to` 和 `to∘from` 都是丢弃参数、返回
`refl` 的函数。在这样的情况下，`refl` 足够可以证明左逆，因为 `from (to x)`
化简为 `x`。右逆的证明同理。

{::comment}
To show isomorphism is symmetric, we simply swap the roles of `to`
and `from`, and `from∘to` and `to∘from`:
{:/}

要证明同构是对称的，我们把 `to` 和 `from`、`from∘to` 和 `to∘from` 互换：

{% raw %}<pre class="Agda"><a id="≃-sym"></a><a id="9378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9378" class="Function">≃-sym</a> <a id="9384" class="Symbol">:</a> <a id="9386" class="Symbol">∀</a> <a id="9388" class="Symbol">{</a><a id="9389" href="plfa.Isomorphism.html#9389" class="Bound">A</a> <a id="9391" href="plfa.Isomorphism.html#9391" class="Bound">B</a> <a id="9393" class="Symbol">:</a> <a id="9395" class="PrimitiveType">Set</a><a id="9398" class="Symbol">}</a>
  <a id="9402" class="Symbol">→</a> <a id="9404" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9389" class="Bound">A</a> <a id="9406" href="plfa.Isomorphism.html#5843" class="Record Operator">≃</a> <a id="9408" href="plfa.Isomorphism.html#9391" class="Bound">B</a>
    <a id="9414" class="Comment">-----</a>
  <a id="9422" class="Symbol">→</a> <a id="9424" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9391" class="Bound">B</a> <a id="9426" href="plfa.Isomorphism.html#5843" class="Record Operator">≃</a> <a id="9428" href="plfa.Isomorphism.html#9389" class="Bound">A</a>
<a id="9430" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9378" class="Function">≃-sym</a> <a id="9436" href="plfa.Isomorphism.html#9436" class="Bound">A≃B</a> <a id="9440" class="Symbol">=</a>
  <a id="9444" class="Keyword">record</a>
    <a id="9455" class="Symbol">{</a> <a id="9457" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5883" class="Field">to</a>      <a id="9465" class="Symbol">=</a> <a id="9467" href="plfa.Isomorphism.html#5900" class="Field">from</a> <a id="9472" href="plfa.Isomorphism.html#9436" class="Bound">A≃B</a>
    <a id="9480" class="Symbol">;</a> <a id="9482" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5900" class="Field">from</a>    <a id="9490" class="Symbol">=</a> <a id="9492" href="plfa.Isomorphism.html#5883" class="Field">to</a>   <a id="9497" href="plfa.Isomorphism.html#9436" class="Bound">A≃B</a>
    <a id="9505" class="Symbol">;</a> <a id="9507" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5917" class="Field">from∘to</a> <a id="9515" class="Symbol">=</a> <a id="9517" href="plfa.Isomorphism.html#5959" class="Field">to∘from</a> <a id="9525" href="plfa.Isomorphism.html#9436" class="Bound">A≃B</a>
    <a id="9533" class="Symbol">;</a> <a id="9535" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5959" class="Field">to∘from</a> <a id="9543" class="Symbol">=</a> <a id="9545" href="plfa.Isomorphism.html#5917" class="Field">from∘to</a> <a id="9553" href="plfa.Isomorphism.html#9436" class="Bound">A≃B</a>
    <a id="9561" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
To show isomorphism is transitive, we compose the `to` and `from`
functions, and use equational reasoning to combine the inverses:
{:/}

要证明同构是传递的，我们将 `to` 和 `from` 函数进行组合，并使用相等性论证来结合左逆和右逆：

{% raw %}<pre class="Agda"><a id="≃-trans"></a><a id="9775" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9775" class="Function">≃-trans</a> <a id="9783" class="Symbol">:</a> <a id="9785" class="Symbol">∀</a> <a id="9787" class="Symbol">{</a><a id="9788" href="plfa.Isomorphism.html#9788" class="Bound">A</a> <a id="9790" href="plfa.Isomorphism.html#9790" class="Bound">B</a> <a id="9792" href="plfa.Isomorphism.html#9792" class="Bound">C</a> <a id="9794" class="Symbol">:</a> <a id="9796" class="PrimitiveType">Set</a><a id="9799" class="Symbol">}</a>
  <a id="9803" class="Symbol">→</a> <a id="9805" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9788" class="Bound">A</a> <a id="9807" href="plfa.Isomorphism.html#5843" class="Record Operator">≃</a> <a id="9809" href="plfa.Isomorphism.html#9790" class="Bound">B</a>
  <a id="9813" class="Symbol">→</a> <a id="9815" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9790" class="Bound">B</a> <a id="9817" href="plfa.Isomorphism.html#5843" class="Record Operator">≃</a> <a id="9819" href="plfa.Isomorphism.html#9792" class="Bound">C</a>
    <a id="9825" class="Comment">-----</a>
  <a id="9833" class="Symbol">→</a> <a id="9835" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9788" class="Bound">A</a> <a id="9837" href="plfa.Isomorphism.html#5843" class="Record Operator">≃</a> <a id="9839" href="plfa.Isomorphism.html#9792" class="Bound">C</a>
<a id="9841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9775" class="Function">≃-trans</a> <a id="9849" href="plfa.Isomorphism.html#9849" class="Bound">A≃B</a> <a id="9853" href="plfa.Isomorphism.html#9853" class="Bound">B≃C</a> <a id="9857" class="Symbol">=</a>
  <a id="9861" class="Keyword">record</a>
    <a id="9872" class="Symbol">{</a> <a id="9874" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5883" class="Field">to</a>       <a id="9883" class="Symbol">=</a> <a id="9885" href="plfa.Isomorphism.html#5883" class="Field">to</a>   <a id="9890" href="plfa.Isomorphism.html#9853" class="Bound">B≃C</a> <a id="9894" href="plfa.Isomorphism.html#2703" class="Function Operator">∘</a> <a id="9896" href="plfa.Isomorphism.html#5883" class="Field">to</a>   <a id="9901" href="plfa.Isomorphism.html#9849" class="Bound">A≃B</a>
    <a id="9909" class="Symbol">;</a> <a id="9911" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5900" class="Field">from</a>     <a id="9920" class="Symbol">=</a> <a id="9922" href="plfa.Isomorphism.html#5900" class="Field">from</a> <a id="9927" href="plfa.Isomorphism.html#9849" class="Bound">A≃B</a> <a id="9931" href="plfa.Isomorphism.html#2703" class="Function Operator">∘</a> <a id="9933" href="plfa.Isomorphism.html#5900" class="Field">from</a> <a id="9938" href="plfa.Isomorphism.html#9853" class="Bound">B≃C</a>
    <a id="9946" class="Symbol">;</a> <a id="9948" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5917" class="Field">from∘to</a>  <a id="9957" class="Symbol">=</a> <a id="9959" class="Symbol">λ{</a><a id="9961" href="plfa.Isomorphism.html#9961" class="Bound">x</a> <a id="9963" class="Symbol">→</a>
        <a id="9973" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
          <a id="9989" class="Symbol">(</a><a id="9990" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5900" class="Field">from</a> <a id="9995" href="plfa.Isomorphism.html#9849" class="Bound">A≃B</a> <a id="9999" href="plfa.Isomorphism.html#2703" class="Function Operator">∘</a> <a id="10001" href="plfa.Isomorphism.html#5900" class="Field">from</a> <a id="10006" href="plfa.Isomorphism.html#9853" class="Bound">B≃C</a><a id="10009" class="Symbol">)</a> <a id="10011" class="Symbol">((</a><a id="10013" href="plfa.Isomorphism.html#5883" class="Field">to</a> <a id="10016" href="plfa.Isomorphism.html#9853" class="Bound">B≃C</a> <a id="10020" href="plfa.Isomorphism.html#2703" class="Function Operator">∘</a> <a id="10022" href="plfa.Isomorphism.html#5883" class="Field">to</a> <a id="10025" href="plfa.Isomorphism.html#9849" class="Bound">A≃B</a><a id="10028" class="Symbol">)</a> <a id="10030" href="plfa.Isomorphism.html#9961" class="Bound">x</a><a id="10031" class="Symbol">)</a>
        <a id="10041" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
          <a id="10055" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5900" class="Field">from</a> <a id="10060" href="plfa.Isomorphism.html#9849" class="Bound">A≃B</a> <a id="10064" class="Symbol">(</a><a id="10065" href="plfa.Isomorphism.html#5900" class="Field">from</a> <a id="10070" href="plfa.Isomorphism.html#9853" class="Bound">B≃C</a> <a id="10074" class="Symbol">(</a><a id="10075" href="plfa.Isomorphism.html#5883" class="Field">to</a> <a id="10078" href="plfa.Isomorphism.html#9853" class="Bound">B≃C</a> <a id="10082" class="Symbol">(</a><a id="10083" href="plfa.Isomorphism.html#5883" class="Field">to</a> <a id="10086" href="plfa.Isomorphism.html#9849" class="Bound">A≃B</a> <a id="10090" href="plfa.Isomorphism.html#9961" class="Bound">x</a><a id="10091" class="Symbol">)))</a>
        <a id="10103" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="10106" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="10111" class="Symbol">(</a><a id="10112" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5900" class="Field">from</a> <a id="10117" href="plfa.Isomorphism.html#9849" class="Bound">A≃B</a><a id="10120" class="Symbol">)</a> <a id="10122" class="Symbol">(</a><a id="10123" href="plfa.Isomorphism.html#5917" class="Field">from∘to</a> <a id="10131" href="plfa.Isomorphism.html#9853" class="Bound">B≃C</a> <a id="10135" class="Symbol">(</a><a id="10136" href="plfa.Isomorphism.html#5883" class="Field">to</a> <a id="10139" href="plfa.Isomorphism.html#9849" class="Bound">A≃B</a> <a id="10143" href="plfa.Isomorphism.html#9961" class="Bound">x</a><a id="10144" class="Symbol">))</a> <a id="10147" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
          <a id="10159" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5900" class="Field">from</a> <a id="10164" href="plfa.Isomorphism.html#9849" class="Bound">A≃B</a> <a id="10168" class="Symbol">(</a><a id="10169" href="plfa.Isomorphism.html#5883" class="Field">to</a> <a id="10172" href="plfa.Isomorphism.html#9849" class="Bound">A≃B</a> <a id="10176" href="plfa.Isomorphism.html#9961" class="Bound">x</a><a id="10177" class="Symbol">)</a>
        <a id="10187" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="10190" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5917" class="Field">from∘to</a> <a id="10198" href="plfa.Isomorphism.html#9849" class="Bound">A≃B</a> <a id="10202" href="plfa.Isomorphism.html#9961" class="Bound">x</a> <a id="10204" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
          <a id="10216" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9961" class="Bound">x</a>
        <a id="10226" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a><a id="10227" class="Symbol">}</a>
    <a id="10233" class="Symbol">;</a> <a id="10235" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5959" class="Field">to∘from</a> <a id="10243" class="Symbol">=</a> <a id="10245" class="Symbol">λ{</a><a id="10247" href="plfa.Isomorphism.html#10247" class="Bound">y</a> <a id="10249" class="Symbol">→</a>
        <a id="10259" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
          <a id="10275" class="Symbol">(</a><a id="10276" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5883" class="Field">to</a> <a id="10279" href="plfa.Isomorphism.html#9853" class="Bound">B≃C</a> <a id="10283" href="plfa.Isomorphism.html#2703" class="Function Operator">∘</a> <a id="10285" href="plfa.Isomorphism.html#5883" class="Field">to</a> <a id="10288" href="plfa.Isomorphism.html#9849" class="Bound">A≃B</a><a id="10291" class="Symbol">)</a> <a id="10293" class="Symbol">((</a><a id="10295" href="plfa.Isomorphism.html#5900" class="Field">from</a> <a id="10300" href="plfa.Isomorphism.html#9849" class="Bound">A≃B</a> <a id="10304" href="plfa.Isomorphism.html#2703" class="Function Operator">∘</a> <a id="10306" href="plfa.Isomorphism.html#5900" class="Field">from</a> <a id="10311" href="plfa.Isomorphism.html#9853" class="Bound">B≃C</a><a id="10314" class="Symbol">)</a> <a id="10316" href="plfa.Isomorphism.html#10247" class="Bound">y</a><a id="10317" class="Symbol">)</a>
        <a id="10327" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
          <a id="10341" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5883" class="Field">to</a> <a id="10344" href="plfa.Isomorphism.html#9853" class="Bound">B≃C</a> <a id="10348" class="Symbol">(</a><a id="10349" href="plfa.Isomorphism.html#5883" class="Field">to</a> <a id="10352" href="plfa.Isomorphism.html#9849" class="Bound">A≃B</a> <a id="10356" class="Symbol">(</a><a id="10357" href="plfa.Isomorphism.html#5900" class="Field">from</a> <a id="10362" href="plfa.Isomorphism.html#9849" class="Bound">A≃B</a> <a id="10366" class="Symbol">(</a><a id="10367" href="plfa.Isomorphism.html#5900" class="Field">from</a> <a id="10372" href="plfa.Isomorphism.html#9853" class="Bound">B≃C</a> <a id="10376" href="plfa.Isomorphism.html#10247" class="Bound">y</a><a id="10377" class="Symbol">)))</a>
        <a id="10389" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="10392" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="10397" class="Symbol">(</a><a id="10398" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5883" class="Field">to</a> <a id="10401" href="plfa.Isomorphism.html#9853" class="Bound">B≃C</a><a id="10404" class="Symbol">)</a> <a id="10406" class="Symbol">(</a><a id="10407" href="plfa.Isomorphism.html#5959" class="Field">to∘from</a> <a id="10415" href="plfa.Isomorphism.html#9849" class="Bound">A≃B</a> <a id="10419" class="Symbol">(</a><a id="10420" href="plfa.Isomorphism.html#5900" class="Field">from</a> <a id="10425" href="plfa.Isomorphism.html#9853" class="Bound">B≃C</a> <a id="10429" href="plfa.Isomorphism.html#10247" class="Bound">y</a><a id="10430" class="Symbol">))</a> <a id="10433" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
          <a id="10445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5883" class="Field">to</a> <a id="10448" href="plfa.Isomorphism.html#9853" class="Bound">B≃C</a> <a id="10452" class="Symbol">(</a><a id="10453" href="plfa.Isomorphism.html#5900" class="Field">from</a> <a id="10458" href="plfa.Isomorphism.html#9853" class="Bound">B≃C</a> <a id="10462" href="plfa.Isomorphism.html#10247" class="Bound">y</a><a id="10463" class="Symbol">)</a>
        <a id="10473" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="10476" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5959" class="Field">to∘from</a> <a id="10484" href="plfa.Isomorphism.html#9853" class="Bound">B≃C</a> <a id="10488" href="plfa.Isomorphism.html#10247" class="Bound">y</a> <a id="10490" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
          <a id="10502" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10247" class="Bound">y</a>
        <a id="10512" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a><a id="10513" class="Symbol">}</a>
     <a id="10520" class="Symbol">}</a>
</pre>{% endraw %}

{::comment}
## Equational reasoning for isomorphism
{:/}

## 同构的相等性论证

{::comment}
It is straightforward to support a variant of equational reasoning for
isomorphism.  We essentially copy the previous definition
of equality for isomorphism.  We omit the form that corresponds to `_≡⟨⟩_`, since
trivial isomorphisms arise far less often than trivial equalities:
{:/}

我们可以直接的构造一种同构的相等性论证方法。我们对之前的相等性论证定义进行修改。
我们省略 `_≡⟨⟩_` 的定义，因为简单的同构比简单的相等性出现的少很多：

{% raw %}<pre class="Agda"><a id="10980" class="Keyword">module</a> <a id="≃-Reasoning"></a><a id="10987" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10987" class="Module">≃-Reasoning</a> <a id="10999" class="Keyword">where</a>

  <a id="11008" class="Keyword">infix</a>  <a id="11015" class="Number">1</a> <a id="11017" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11063" class="Function Operator">≃-begin_</a>
  <a id="11028" class="Keyword">infixr</a> <a id="11035" class="Number">2</a> <a id="11037" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11147" class="Function Operator">_≃⟨_⟩_</a>
  <a id="11046" class="Keyword">infix</a>  <a id="11053" class="Number">3</a> <a id="11055" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11266" class="Function Operator">_≃-∎</a>

  <a id="≃-Reasoning.≃-begin_"></a><a id="11063" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11063" class="Function Operator">≃-begin_</a> <a id="11072" class="Symbol">:</a> <a id="11074" class="Symbol">∀</a> <a id="11076" class="Symbol">{</a><a id="11077" href="plfa.Isomorphism.html#11077" class="Bound">A</a> <a id="11079" href="plfa.Isomorphism.html#11079" class="Bound">B</a> <a id="11081" class="Symbol">:</a> <a id="11083" class="PrimitiveType">Set</a><a id="11086" class="Symbol">}</a>
    <a id="11092" class="Symbol">→</a> <a id="11094" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11077" class="Bound">A</a> <a id="11096" href="plfa.Isomorphism.html#5843" class="Record Operator">≃</a> <a id="11098" href="plfa.Isomorphism.html#11079" class="Bound">B</a>
      <a id="11106" class="Comment">-----</a>
    <a id="11116" class="Symbol">→</a> <a id="11118" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11077" class="Bound">A</a> <a id="11120" href="plfa.Isomorphism.html#5843" class="Record Operator">≃</a> <a id="11122" href="plfa.Isomorphism.html#11079" class="Bound">B</a>
  <a id="11126" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11063" class="Function Operator">≃-begin</a> <a id="11134" href="plfa.Isomorphism.html#11134" class="Bound">A≃B</a> <a id="11138" class="Symbol">=</a> <a id="11140" href="plfa.Isomorphism.html#11134" class="Bound">A≃B</a>

  <a id="≃-Reasoning._≃⟨_⟩_"></a><a id="11147" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11147" class="Function Operator">_≃⟨_⟩_</a> <a id="11154" class="Symbol">:</a> <a id="11156" class="Symbol">∀</a> <a id="11158" class="Symbol">(</a><a id="11159" href="plfa.Isomorphism.html#11159" class="Bound">A</a> <a id="11161" class="Symbol">:</a> <a id="11163" class="PrimitiveType">Set</a><a id="11166" class="Symbol">)</a> <a id="11168" class="Symbol">{</a><a id="11169" href="plfa.Isomorphism.html#11169" class="Bound">B</a> <a id="11171" href="plfa.Isomorphism.html#11171" class="Bound">C</a> <a id="11173" class="Symbol">:</a> <a id="11175" class="PrimitiveType">Set</a><a id="11178" class="Symbol">}</a>
    <a id="11184" class="Symbol">→</a> <a id="11186" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11159" class="Bound">A</a> <a id="11188" href="plfa.Isomorphism.html#5843" class="Record Operator">≃</a> <a id="11190" href="plfa.Isomorphism.html#11169" class="Bound">B</a>
    <a id="11196" class="Symbol">→</a> <a id="11198" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11169" class="Bound">B</a> <a id="11200" href="plfa.Isomorphism.html#5843" class="Record Operator">≃</a> <a id="11202" href="plfa.Isomorphism.html#11171" class="Bound">C</a>
      <a id="11210" class="Comment">-----</a>
    <a id="11220" class="Symbol">→</a> <a id="11222" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11159" class="Bound">A</a> <a id="11224" href="plfa.Isomorphism.html#5843" class="Record Operator">≃</a> <a id="11226" href="plfa.Isomorphism.html#11171" class="Bound">C</a>
  <a id="11230" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11230" class="Bound">A</a> <a id="11232" href="plfa.Isomorphism.html#11147" class="Function Operator">≃⟨</a> <a id="11235" href="plfa.Isomorphism.html#11235" class="Bound">A≃B</a> <a id="11239" href="plfa.Isomorphism.html#11147" class="Function Operator">⟩</a> <a id="11241" href="plfa.Isomorphism.html#11241" class="Bound">B≃C</a> <a id="11245" class="Symbol">=</a> <a id="11247" href="plfa.Isomorphism.html#9775" class="Function">≃-trans</a> <a id="11255" href="plfa.Isomorphism.html#11235" class="Bound">A≃B</a> <a id="11259" href="plfa.Isomorphism.html#11241" class="Bound">B≃C</a>

  <a id="≃-Reasoning._≃-∎"></a><a id="11266" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11266" class="Function Operator">_≃-∎</a> <a id="11271" class="Symbol">:</a> <a id="11273" class="Symbol">∀</a> <a id="11275" class="Symbol">(</a><a id="11276" href="plfa.Isomorphism.html#11276" class="Bound">A</a> <a id="11278" class="Symbol">:</a> <a id="11280" class="PrimitiveType">Set</a><a id="11283" class="Symbol">)</a>
      <a id="11291" class="Comment">-----</a>
    <a id="11301" class="Symbol">→</a> <a id="11303" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11276" class="Bound">A</a> <a id="11305" href="plfa.Isomorphism.html#5843" class="Record Operator">≃</a> <a id="11307" href="plfa.Isomorphism.html#11276" class="Bound">A</a>
  <a id="11311" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11311" class="Bound">A</a> <a id="11313" href="plfa.Isomorphism.html#11266" class="Function Operator">≃-∎</a> <a id="11317" class="Symbol">=</a> <a id="11319" href="plfa.Isomorphism.html#8555" class="Function">≃-refl</a>

<a id="11327" class="Keyword">open</a> <a id="11332" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10987" class="Module">≃-Reasoning</a>
</pre>{% endraw %}

{::comment}
## Embedding
{:/}

## 嵌入（Embedding）

{::comment}
We also need the notion of _embedding_, which is a weakening of
isomorphism.  While an isomorphism shows that two types are in
one-to-one correspondence, an embedding shows that the first type is
included in the second; or, equivalently, that there is a many-to-one
correspondence between the second type and the first.
{:/}

我们同时也需要*嵌入*的概念，它是同构的弱化概念。同构要求证明两个类型之间的一一对应，
而嵌入只需要第一种类型涵盖在第二种类型内，所以两个类型之间有一对多的对应关系。

{::comment}
Here is the formal definition of embedding:
{:/}

嵌入的正式定义如下：

{% raw %}<pre class="Agda"><a id="11900" class="Keyword">infix</a> <a id="11906" class="Number">0</a> <a id="11908" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11919" class="Record Operator">_≲_</a>
<a id="11912" class="Keyword">record</a> <a id="_≲_"></a><a id="11919" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11919" class="Record Operator">_≲_</a> <a id="11923" class="Symbol">(</a><a id="11924" href="plfa.Isomorphism.html#11924" class="Bound">A</a> <a id="11926" href="plfa.Isomorphism.html#11926" class="Bound">B</a> <a id="11928" class="Symbol">:</a> <a id="11930" class="PrimitiveType">Set</a><a id="11933" class="Symbol">)</a> <a id="11935" class="Symbol">:</a> <a id="11937" class="PrimitiveType">Set</a> <a id="11941" class="Keyword">where</a>
  <a id="11949" class="Keyword">field</a>
    <a id="_≲_.to"></a><a id="11959" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11959" class="Field">to</a>      <a id="11967" class="Symbol">:</a> <a id="11969" href="plfa.Isomorphism.html#11924" class="Bound">A</a> <a id="11971" class="Symbol">→</a> <a id="11973" href="plfa.Isomorphism.html#11926" class="Bound">B</a>
    <a id="_≲_.from"></a><a id="11979" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11979" class="Field">from</a>    <a id="11987" class="Symbol">:</a> <a id="11989" href="plfa.Isomorphism.html#11926" class="Bound">B</a> <a id="11991" class="Symbol">→</a> <a id="11993" href="plfa.Isomorphism.html#11924" class="Bound">A</a>
    <a id="_≲_.from∘to"></a><a id="11999" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11999" class="Field">from∘to</a> <a id="12007" class="Symbol">:</a> <a id="12009" class="Symbol">∀</a> <a id="12011" class="Symbol">(</a><a id="12012" href="plfa.Isomorphism.html#12012" class="Bound">x</a> <a id="12014" class="Symbol">:</a> <a id="12016" href="plfa.Isomorphism.html#11924" class="Bound">A</a><a id="12017" class="Symbol">)</a> <a id="12019" class="Symbol">→</a> <a id="12021" class="Field">from</a> <a id="12026" class="Symbol">(</a><a id="12027" class="Field">to</a> <a id="12030" href="plfa.Isomorphism.html#12012" class="Bound">x</a><a id="12031" class="Symbol">)</a> <a id="12033" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="12035" href="plfa.Isomorphism.html#12012" class="Bound">x</a>
<a id="12037" class="Keyword">open</a> <a id="12042" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11919" class="Module Operator">_≲_</a>
</pre>{% endraw %}
{::comment}
It is the same as an isomorphism, save that it lacks the `to∘from` field.
Hence, we know that `from` is left-inverse to `to`, but not that `from`
is right-inverse to `to`.
{:/}

除了它缺少了 `to∘from` 字段以外，嵌入的定义和同构是一样的。因此，我们可以得知 `from` 是 `to`
的左逆，但是 `from` 不是 `to` 的右逆。

{::comment}
Embedding is reflexive and transitive, but not symmetric.  The proofs
are cut down versions of the similar proofs for isomorphism:
{:/}

嵌入是自反和传递的，但不是对称的。证明与同构类似，不过去除了不需要的部分：

{% raw %}<pre class="Agda"><a id="≲-refl"></a><a id="12520" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12520" class="Function">≲-refl</a> <a id="12527" class="Symbol">:</a> <a id="12529" class="Symbol">∀</a> <a id="12531" class="Symbol">{</a><a id="12532" href="plfa.Isomorphism.html#12532" class="Bound">A</a> <a id="12534" class="Symbol">:</a> <a id="12536" class="PrimitiveType">Set</a><a id="12539" class="Symbol">}</a> <a id="12541" class="Symbol">→</a> <a id="12543" href="plfa.Isomorphism.html#12532" class="Bound">A</a> <a id="12545" href="plfa.Isomorphism.html#11919" class="Record Operator">≲</a> <a id="12547" href="plfa.Isomorphism.html#12532" class="Bound">A</a>
<a id="12549" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12520" class="Function">≲-refl</a> <a id="12556" class="Symbol">=</a>
  <a id="12560" class="Keyword">record</a>
    <a id="12571" class="Symbol">{</a> <a id="12573" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11959" class="Field">to</a>      <a id="12581" class="Symbol">=</a> <a id="12583" class="Symbol">λ{</a><a id="12585" href="plfa.Isomorphism.html#12585" class="Bound">x</a> <a id="12587" class="Symbol">→</a> <a id="12589" href="plfa.Isomorphism.html#12585" class="Bound">x</a><a id="12590" class="Symbol">}</a>
    <a id="12596" class="Symbol">;</a> <a id="12598" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11979" class="Field">from</a>    <a id="12606" class="Symbol">=</a> <a id="12608" class="Symbol">λ{</a><a id="12610" href="plfa.Isomorphism.html#12610" class="Bound">y</a> <a id="12612" class="Symbol">→</a> <a id="12614" href="plfa.Isomorphism.html#12610" class="Bound">y</a><a id="12615" class="Symbol">}</a>
    <a id="12621" class="Symbol">;</a> <a id="12623" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11999" class="Field">from∘to</a> <a id="12631" class="Symbol">=</a> <a id="12633" class="Symbol">λ{</a><a id="12635" href="plfa.Isomorphism.html#12635" class="Bound">x</a> <a id="12637" class="Symbol">→</a> <a id="12639" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="12643" class="Symbol">}</a>
    <a id="12649" class="Symbol">}</a>

<a id="≲-trans"></a><a id="12652" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12652" class="Function">≲-trans</a> <a id="12660" class="Symbol">:</a> <a id="12662" class="Symbol">∀</a> <a id="12664" class="Symbol">{</a><a id="12665" href="plfa.Isomorphism.html#12665" class="Bound">A</a> <a id="12667" href="plfa.Isomorphism.html#12667" class="Bound">B</a> <a id="12669" href="plfa.Isomorphism.html#12669" class="Bound">C</a> <a id="12671" class="Symbol">:</a> <a id="12673" class="PrimitiveType">Set</a><a id="12676" class="Symbol">}</a> <a id="12678" class="Symbol">→</a> <a id="12680" href="plfa.Isomorphism.html#12665" class="Bound">A</a> <a id="12682" href="plfa.Isomorphism.html#11919" class="Record Operator">≲</a> <a id="12684" href="plfa.Isomorphism.html#12667" class="Bound">B</a> <a id="12686" class="Symbol">→</a> <a id="12688" href="plfa.Isomorphism.html#12667" class="Bound">B</a> <a id="12690" href="plfa.Isomorphism.html#11919" class="Record Operator">≲</a> <a id="12692" href="plfa.Isomorphism.html#12669" class="Bound">C</a> <a id="12694" class="Symbol">→</a> <a id="12696" href="plfa.Isomorphism.html#12665" class="Bound">A</a> <a id="12698" href="plfa.Isomorphism.html#11919" class="Record Operator">≲</a> <a id="12700" href="plfa.Isomorphism.html#12669" class="Bound">C</a>
<a id="12702" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12652" class="Function">≲-trans</a> <a id="12710" href="plfa.Isomorphism.html#12710" class="Bound">A≲B</a> <a id="12714" href="plfa.Isomorphism.html#12714" class="Bound">B≲C</a> <a id="12718" class="Symbol">=</a>
  <a id="12722" class="Keyword">record</a>
    <a id="12733" class="Symbol">{</a> <a id="12735" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11959" class="Field">to</a>      <a id="12743" class="Symbol">=</a> <a id="12745" class="Symbol">λ{</a><a id="12747" href="plfa.Isomorphism.html#12747" class="Bound">x</a> <a id="12749" class="Symbol">→</a> <a id="12751" href="plfa.Isomorphism.html#11959" class="Field">to</a>   <a id="12756" href="plfa.Isomorphism.html#12714" class="Bound">B≲C</a> <a id="12760" class="Symbol">(</a><a id="12761" href="plfa.Isomorphism.html#11959" class="Field">to</a>   <a id="12766" href="plfa.Isomorphism.html#12710" class="Bound">A≲B</a> <a id="12770" href="plfa.Isomorphism.html#12747" class="Bound">x</a><a id="12771" class="Symbol">)}</a>
    <a id="12778" class="Symbol">;</a> <a id="12780" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11979" class="Field">from</a>    <a id="12788" class="Symbol">=</a> <a id="12790" class="Symbol">λ{</a><a id="12792" href="plfa.Isomorphism.html#12792" class="Bound">y</a> <a id="12794" class="Symbol">→</a> <a id="12796" href="plfa.Isomorphism.html#11979" class="Field">from</a> <a id="12801" href="plfa.Isomorphism.html#12710" class="Bound">A≲B</a> <a id="12805" class="Symbol">(</a><a id="12806" href="plfa.Isomorphism.html#11979" class="Field">from</a> <a id="12811" href="plfa.Isomorphism.html#12714" class="Bound">B≲C</a> <a id="12815" href="plfa.Isomorphism.html#12792" class="Bound">y</a><a id="12816" class="Symbol">)}</a>
    <a id="12823" class="Symbol">;</a> <a id="12825" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11999" class="Field">from∘to</a> <a id="12833" class="Symbol">=</a> <a id="12835" class="Symbol">λ{</a><a id="12837" href="plfa.Isomorphism.html#12837" class="Bound">x</a> <a id="12839" class="Symbol">→</a>
        <a id="12849" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
          <a id="12865" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11979" class="Field">from</a> <a id="12870" href="plfa.Isomorphism.html#12710" class="Bound">A≲B</a> <a id="12874" class="Symbol">(</a><a id="12875" href="plfa.Isomorphism.html#11979" class="Field">from</a> <a id="12880" href="plfa.Isomorphism.html#12714" class="Bound">B≲C</a> <a id="12884" class="Symbol">(</a><a id="12885" href="plfa.Isomorphism.html#11959" class="Field">to</a> <a id="12888" href="plfa.Isomorphism.html#12714" class="Bound">B≲C</a> <a id="12892" class="Symbol">(</a><a id="12893" href="plfa.Isomorphism.html#11959" class="Field">to</a> <a id="12896" href="plfa.Isomorphism.html#12710" class="Bound">A≲B</a> <a id="12900" href="plfa.Isomorphism.html#12837" class="Bound">x</a><a id="12901" class="Symbol">)))</a>
        <a id="12913" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="12916" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="12921" class="Symbol">(</a><a id="12922" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11979" class="Field">from</a> <a id="12927" href="plfa.Isomorphism.html#12710" class="Bound">A≲B</a><a id="12930" class="Symbol">)</a> <a id="12932" class="Symbol">(</a><a id="12933" href="plfa.Isomorphism.html#11999" class="Field">from∘to</a> <a id="12941" href="plfa.Isomorphism.html#12714" class="Bound">B≲C</a> <a id="12945" class="Symbol">(</a><a id="12946" href="plfa.Isomorphism.html#11959" class="Field">to</a> <a id="12949" href="plfa.Isomorphism.html#12710" class="Bound">A≲B</a> <a id="12953" href="plfa.Isomorphism.html#12837" class="Bound">x</a><a id="12954" class="Symbol">))</a> <a id="12957" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
          <a id="12969" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11979" class="Field">from</a> <a id="12974" href="plfa.Isomorphism.html#12710" class="Bound">A≲B</a> <a id="12978" class="Symbol">(</a><a id="12979" href="plfa.Isomorphism.html#11959" class="Field">to</a> <a id="12982" href="plfa.Isomorphism.html#12710" class="Bound">A≲B</a> <a id="12986" href="plfa.Isomorphism.html#12837" class="Bound">x</a><a id="12987" class="Symbol">)</a>
        <a id="12997" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="13000" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11999" class="Field">from∘to</a> <a id="13008" href="plfa.Isomorphism.html#12710" class="Bound">A≲B</a> <a id="13012" href="plfa.Isomorphism.html#12837" class="Bound">x</a> <a id="13014" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
          <a id="13026" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12837" class="Bound">x</a>
        <a id="13036" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a><a id="13037" class="Symbol">}</a>
     <a id="13044" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
It is also easy to see that if two types embed in each other, and the
embedding functions correspond, then they are isomorphic.  This is a
weak form of anti-symmetry:
{:/}

显而易见的是，如果两个类型相互嵌入，且其嵌入函数相互对应，那么它们是同构的。
这个一种反对称性的弱化形式：

{% raw %}<pre class="Agda"><a id="≲-antisym"></a><a id="13295" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13295" class="Function">≲-antisym</a> <a id="13305" class="Symbol">:</a> <a id="13307" class="Symbol">∀</a> <a id="13309" class="Symbol">{</a><a id="13310" href="plfa.Isomorphism.html#13310" class="Bound">A</a> <a id="13312" href="plfa.Isomorphism.html#13312" class="Bound">B</a> <a id="13314" class="Symbol">:</a> <a id="13316" class="PrimitiveType">Set</a><a id="13319" class="Symbol">}</a>
  <a id="13323" class="Symbol">→</a> <a id="13325" class="Symbol">(</a><a id="13326" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13326" class="Bound">A≲B</a> <a id="13330" class="Symbol">:</a> <a id="13332" href="plfa.Isomorphism.html#13310" class="Bound">A</a> <a id="13334" href="plfa.Isomorphism.html#11919" class="Record Operator">≲</a> <a id="13336" href="plfa.Isomorphism.html#13312" class="Bound">B</a><a id="13337" class="Symbol">)</a>
  <a id="13341" class="Symbol">→</a> <a id="13343" class="Symbol">(</a><a id="13344" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13344" class="Bound">B≲A</a> <a id="13348" class="Symbol">:</a> <a id="13350" href="plfa.Isomorphism.html#13312" class="Bound">B</a> <a id="13352" href="plfa.Isomorphism.html#11919" class="Record Operator">≲</a> <a id="13354" href="plfa.Isomorphism.html#13310" class="Bound">A</a><a id="13355" class="Symbol">)</a>
  <a id="13359" class="Symbol">→</a> <a id="13361" class="Symbol">(</a><a id="13362" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11959" class="Field">to</a> <a id="13365" href="plfa.Isomorphism.html#13326" class="Bound">A≲B</a> <a id="13369" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="13371" href="plfa.Isomorphism.html#11979" class="Field">from</a> <a id="13376" href="plfa.Isomorphism.html#13344" class="Bound">B≲A</a><a id="13379" class="Symbol">)</a>
  <a id="13383" class="Symbol">→</a> <a id="13385" class="Symbol">(</a><a id="13386" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11979" class="Field">from</a> <a id="13391" href="plfa.Isomorphism.html#13326" class="Bound">A≲B</a> <a id="13395" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="13397" href="plfa.Isomorphism.html#11959" class="Field">to</a> <a id="13400" href="plfa.Isomorphism.html#13344" class="Bound">B≲A</a><a id="13403" class="Symbol">)</a>
    <a id="13409" class="Comment">-------------------</a>
  <a id="13431" class="Symbol">→</a> <a id="13433" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13310" class="Bound">A</a> <a id="13435" href="plfa.Isomorphism.html#5843" class="Record Operator">≃</a> <a id="13437" href="plfa.Isomorphism.html#13312" class="Bound">B</a>
<a id="13439" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13295" class="Function">≲-antisym</a> <a id="13449" href="plfa.Isomorphism.html#13449" class="Bound">A≲B</a> <a id="13453" href="plfa.Isomorphism.html#13453" class="Bound">B≲A</a> <a id="13457" href="plfa.Isomorphism.html#13457" class="Bound">to≡from</a> <a id="13465" href="plfa.Isomorphism.html#13465" class="Bound">from≡to</a> <a id="13473" class="Symbol">=</a>
  <a id="13477" class="Keyword">record</a>
    <a id="13488" class="Symbol">{</a> <a id="13490" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5883" class="Field">to</a>      <a id="13498" class="Symbol">=</a> <a id="13500" href="plfa.Isomorphism.html#11959" class="Field">to</a> <a id="13503" href="plfa.Isomorphism.html#13449" class="Bound">A≲B</a>
    <a id="13511" class="Symbol">;</a> <a id="13513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5900" class="Field">from</a>    <a id="13521" class="Symbol">=</a> <a id="13523" href="plfa.Isomorphism.html#11979" class="Field">from</a> <a id="13528" href="plfa.Isomorphism.html#13449" class="Bound">A≲B</a>
    <a id="13536" class="Symbol">;</a> <a id="13538" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5917" class="Field">from∘to</a> <a id="13546" class="Symbol">=</a> <a id="13548" href="plfa.Isomorphism.html#11999" class="Field">from∘to</a> <a id="13556" href="plfa.Isomorphism.html#13449" class="Bound">A≲B</a>
    <a id="13564" class="Symbol">;</a> <a id="13566" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5959" class="Field">to∘from</a> <a id="13574" class="Symbol">=</a> <a id="13576" class="Symbol">λ{</a><a id="13578" href="plfa.Isomorphism.html#13578" class="Bound">y</a> <a id="13580" class="Symbol">→</a>
        <a id="13590" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
          <a id="13606" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11959" class="Field">to</a> <a id="13609" href="plfa.Isomorphism.html#13449" class="Bound">A≲B</a> <a id="13613" class="Symbol">(</a><a id="13614" href="plfa.Isomorphism.html#11979" class="Field">from</a> <a id="13619" href="plfa.Isomorphism.html#13449" class="Bound">A≲B</a> <a id="13623" href="plfa.Isomorphism.html#13578" class="Bound">y</a><a id="13624" class="Symbol">)</a>
        <a id="13634" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="13637" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="13642" class="Symbol">(</a><a id="13643" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11959" class="Field">to</a> <a id="13646" href="plfa.Isomorphism.html#13449" class="Bound">A≲B</a><a id="13649" class="Symbol">)</a> <a id="13651" class="Symbol">(</a><a id="13652" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html#1308" class="Function">cong-app</a> <a id="13661" href="plfa.Isomorphism.html#13465" class="Bound">from≡to</a> <a id="13669" href="plfa.Isomorphism.html#13578" class="Bound">y</a><a id="13670" class="Symbol">)</a> <a id="13672" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
          <a id="13684" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11959" class="Field">to</a> <a id="13687" href="plfa.Isomorphism.html#13449" class="Bound">A≲B</a> <a id="13691" class="Symbol">(</a><a id="13692" href="plfa.Isomorphism.html#11959" class="Field">to</a> <a id="13695" href="plfa.Isomorphism.html#13453" class="Bound">B≲A</a> <a id="13699" href="plfa.Isomorphism.html#13578" class="Bound">y</a><a id="13700" class="Symbol">)</a>
        <a id="13710" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="13713" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html#1308" class="Function">cong-app</a> <a id="13722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13457" class="Bound">to≡from</a> <a id="13730" class="Symbol">(</a><a id="13731" href="plfa.Isomorphism.html#11959" class="Field">to</a> <a id="13734" href="plfa.Isomorphism.html#13453" class="Bound">B≲A</a> <a id="13738" href="plfa.Isomorphism.html#13578" class="Bound">y</a><a id="13739" class="Symbol">)</a> <a id="13741" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
          <a id="13753" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11979" class="Field">from</a> <a id="13758" href="plfa.Isomorphism.html#13453" class="Bound">B≲A</a> <a id="13762" class="Symbol">(</a><a id="13763" href="plfa.Isomorphism.html#11959" class="Field">to</a> <a id="13766" href="plfa.Isomorphism.html#13453" class="Bound">B≲A</a> <a id="13770" href="plfa.Isomorphism.html#13578" class="Bound">y</a><a id="13771" class="Symbol">)</a>
        <a id="13781" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="13784" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11999" class="Field">from∘to</a> <a id="13792" href="plfa.Isomorphism.html#13453" class="Bound">B≲A</a> <a id="13796" href="plfa.Isomorphism.html#13578" class="Bound">y</a> <a id="13798" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
          <a id="13810" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13578" class="Bound">y</a>
        <a id="13820" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a><a id="13821" class="Symbol">}</a>
    <a id="13827" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
The first three components are copied from the embedding, while the
last combines the left inverse of `B ≲ A` with the equivalences of
the `to` and `from` components from the two embeddings to obtain
the right inverse of the isomorphism.
{:/}

前三部分可以直接从嵌入中得来，最后一部分我们可以把 `B ≲ A` 中的左逆和
两个嵌入中的 `to` 与 `from` 部分的相等性来获得同构中的右逆。


{::comment}
## Equational reasoning for embedding
{:/}

## 嵌入的相等性论证

{::comment}
We can also support tabular reasoning for embedding,
analogous to that used for isomorphism:
{:/}

和同构类似，我们亦支持嵌入的相等性论证：

{% raw %}<pre class="Agda"><a id="14376" class="Keyword">module</a> <a id="≲-Reasoning"></a><a id="14383" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14383" class="Module">≲-Reasoning</a> <a id="14395" class="Keyword">where</a>

  <a id="14404" class="Keyword">infix</a>  <a id="14411" class="Number">1</a> <a id="14413" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14459" class="Function Operator">≲-begin_</a>
  <a id="14424" class="Keyword">infixr</a> <a id="14431" class="Number">2</a> <a id="14433" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14543" class="Function Operator">_≲⟨_⟩_</a>
  <a id="14442" class="Keyword">infix</a>  <a id="14449" class="Number">3</a> <a id="14451" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14662" class="Function Operator">_≲-∎</a>

  <a id="≲-Reasoning.≲-begin_"></a><a id="14459" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14459" class="Function Operator">≲-begin_</a> <a id="14468" class="Symbol">:</a> <a id="14470" class="Symbol">∀</a> <a id="14472" class="Symbol">{</a><a id="14473" href="plfa.Isomorphism.html#14473" class="Bound">A</a> <a id="14475" href="plfa.Isomorphism.html#14475" class="Bound">B</a> <a id="14477" class="Symbol">:</a> <a id="14479" class="PrimitiveType">Set</a><a id="14482" class="Symbol">}</a>
    <a id="14488" class="Symbol">→</a> <a id="14490" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14473" class="Bound">A</a> <a id="14492" href="plfa.Isomorphism.html#11919" class="Record Operator">≲</a> <a id="14494" href="plfa.Isomorphism.html#14475" class="Bound">B</a>
      <a id="14502" class="Comment">-----</a>
    <a id="14512" class="Symbol">→</a> <a id="14514" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14473" class="Bound">A</a> <a id="14516" href="plfa.Isomorphism.html#11919" class="Record Operator">≲</a> <a id="14518" href="plfa.Isomorphism.html#14475" class="Bound">B</a>
  <a id="14522" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14459" class="Function Operator">≲-begin</a> <a id="14530" href="plfa.Isomorphism.html#14530" class="Bound">A≲B</a> <a id="14534" class="Symbol">=</a> <a id="14536" href="plfa.Isomorphism.html#14530" class="Bound">A≲B</a>

  <a id="≲-Reasoning._≲⟨_⟩_"></a><a id="14543" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14543" class="Function Operator">_≲⟨_⟩_</a> <a id="14550" class="Symbol">:</a> <a id="14552" class="Symbol">∀</a> <a id="14554" class="Symbol">(</a><a id="14555" href="plfa.Isomorphism.html#14555" class="Bound">A</a> <a id="14557" class="Symbol">:</a> <a id="14559" class="PrimitiveType">Set</a><a id="14562" class="Symbol">)</a> <a id="14564" class="Symbol">{</a><a id="14565" href="plfa.Isomorphism.html#14565" class="Bound">B</a> <a id="14567" href="plfa.Isomorphism.html#14567" class="Bound">C</a> <a id="14569" class="Symbol">:</a> <a id="14571" class="PrimitiveType">Set</a><a id="14574" class="Symbol">}</a>
    <a id="14580" class="Symbol">→</a> <a id="14582" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14555" class="Bound">A</a> <a id="14584" href="plfa.Isomorphism.html#11919" class="Record Operator">≲</a> <a id="14586" href="plfa.Isomorphism.html#14565" class="Bound">B</a>
    <a id="14592" class="Symbol">→</a> <a id="14594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14565" class="Bound">B</a> <a id="14596" href="plfa.Isomorphism.html#11919" class="Record Operator">≲</a> <a id="14598" href="plfa.Isomorphism.html#14567" class="Bound">C</a>
      <a id="14606" class="Comment">-----</a>
    <a id="14616" class="Symbol">→</a> <a id="14618" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14555" class="Bound">A</a> <a id="14620" href="plfa.Isomorphism.html#11919" class="Record Operator">≲</a> <a id="14622" href="plfa.Isomorphism.html#14567" class="Bound">C</a>
  <a id="14626" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14626" class="Bound">A</a> <a id="14628" href="plfa.Isomorphism.html#14543" class="Function Operator">≲⟨</a> <a id="14631" href="plfa.Isomorphism.html#14631" class="Bound">A≲B</a> <a id="14635" href="plfa.Isomorphism.html#14543" class="Function Operator">⟩</a> <a id="14637" href="plfa.Isomorphism.html#14637" class="Bound">B≲C</a> <a id="14641" class="Symbol">=</a> <a id="14643" href="plfa.Isomorphism.html#12652" class="Function">≲-trans</a> <a id="14651" href="plfa.Isomorphism.html#14631" class="Bound">A≲B</a> <a id="14655" href="plfa.Isomorphism.html#14637" class="Bound">B≲C</a>

  <a id="≲-Reasoning._≲-∎"></a><a id="14662" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14662" class="Function Operator">_≲-∎</a> <a id="14667" class="Symbol">:</a> <a id="14669" class="Symbol">∀</a> <a id="14671" class="Symbol">(</a><a id="14672" href="plfa.Isomorphism.html#14672" class="Bound">A</a> <a id="14674" class="Symbol">:</a> <a id="14676" class="PrimitiveType">Set</a><a id="14679" class="Symbol">)</a>
      <a id="14687" class="Comment">-----</a>
    <a id="14697" class="Symbol">→</a> <a id="14699" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14672" class="Bound">A</a> <a id="14701" href="plfa.Isomorphism.html#11919" class="Record Operator">≲</a> <a id="14703" href="plfa.Isomorphism.html#14672" class="Bound">A</a>
  <a id="14707" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14707" class="Bound">A</a> <a id="14709" href="plfa.Isomorphism.html#14662" class="Function Operator">≲-∎</a> <a id="14713" class="Symbol">=</a> <a id="14715" href="plfa.Isomorphism.html#12520" class="Function">≲-refl</a>

<a id="14723" class="Keyword">open</a> <a id="14728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14383" class="Module">≲-Reasoning</a>
</pre>{% endraw %}
{::comment}
#### Exercise `≃-implies-≲`
{:/}

#### 练习 `≃-implies-≲`

{::comment}
Show that every isomorphism implies an embedding.
{:/}

证明每个同构蕴涵了一个嵌入。

{% raw %}<pre class="Agda"><a id="14902" class="Keyword">postulate</a>
  <a id="≃-implies-≲"></a><a id="14914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14914" class="Postulate">≃-implies-≲</a> <a id="14926" class="Symbol">:</a> <a id="14928" class="Symbol">∀</a> <a id="14930" class="Symbol">{</a><a id="14931" href="plfa.Isomorphism.html#14931" class="Bound">A</a> <a id="14933" href="plfa.Isomorphism.html#14933" class="Bound">B</a> <a id="14935" class="Symbol">:</a> <a id="14937" class="PrimitiveType">Set</a><a id="14940" class="Symbol">}</a>
    <a id="14946" class="Symbol">→</a> <a id="14948" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14931" class="Bound">A</a> <a id="14950" href="plfa.Isomorphism.html#5843" class="Record Operator">≃</a> <a id="14952" href="plfa.Isomorphism.html#14933" class="Bound">B</a>
      <a id="14960" class="Comment">-----</a>
    <a id="14970" class="Symbol">→</a> <a id="14972" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14931" class="Bound">A</a> <a id="14974" href="plfa.Isomorphism.html#11919" class="Record Operator">≲</a> <a id="14976" href="plfa.Isomorphism.html#14933" class="Bound">B</a>
</pre>{% endraw %}
{::comment}
{% raw %}<pre class="Agda"><a id="14999" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="15036" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
#### Exercise `_⇔_` {#iff}
{:/}

#### 练习 `_⇔_` {#iff}

{::comment}
Define equivalence of propositions (also known as "if and only if") as follows:
{:/}

按下列形式定义命题的等价性（又名“当且仅当“）：

{% raw %}<pre class="Agda"><a id="15249" class="Keyword">record</a> <a id="_⇔_"></a><a id="15256" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15256" class="Record Operator">_⇔_</a> <a id="15260" class="Symbol">(</a><a id="15261" href="plfa.Isomorphism.html#15261" class="Bound">A</a> <a id="15263" href="plfa.Isomorphism.html#15263" class="Bound">B</a> <a id="15265" class="Symbol">:</a> <a id="15267" class="PrimitiveType">Set</a><a id="15270" class="Symbol">)</a> <a id="15272" class="Symbol">:</a> <a id="15274" class="PrimitiveType">Set</a> <a id="15278" class="Keyword">where</a>
  <a id="15286" class="Keyword">field</a>
    <a id="_⇔_.to"></a><a id="15296" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15296" class="Field">to</a>   <a id="15301" class="Symbol">:</a> <a id="15303" href="plfa.Isomorphism.html#15261" class="Bound">A</a> <a id="15305" class="Symbol">→</a> <a id="15307" href="plfa.Isomorphism.html#15263" class="Bound">B</a>
    <a id="_⇔_.from"></a><a id="15313" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15313" class="Field">from</a> <a id="15318" class="Symbol">:</a> <a id="15320" href="plfa.Isomorphism.html#15263" class="Bound">B</a> <a id="15322" class="Symbol">→</a> <a id="15324" href="plfa.Isomorphism.html#15261" class="Bound">A</a>
</pre>{% endraw %}
{::comment}
Show that equivalence is reflexive, symmetric, and transitive.
{:/}

证明等价性是自反、对称和传递的。

{::comment}
{% raw %}<pre class="Agda"><a id="15446" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="15483" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
#### Exercise `Bin-embedding` (stretch) {#Bin-embedding}
{:/}

#### 练习 `Bin-embedding` （延伸） {#Bin-embedding}

{::comment}
Recall that Exercises
[Bin]({{ site.baseurl }}/Naturals/#Bin) and
[Bin-laws]({{ site.baseurl }}/Induction/#Bin-laws)
define a datatype of bitstrings representing natural numbers:
{:/}

回忆练习 [Bin][plfa.Naturals#Bin] 和
[Bin-laws][plfa.Induction#Bin-laws] 中，
我们定义了一个数据类型来表示二进制比特串来表示自然数：

{% raw %}<pre class="Agda"><a id="15924" class="Keyword">data</a> <a id="Bin"></a><a id="15929" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15929" class="Datatype">Bin</a> <a id="15933" class="Symbol">:</a> <a id="15935" class="PrimitiveType">Set</a> <a id="15939" class="Keyword">where</a>
  <a id="Bin.nil"></a><a id="15947" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15947" class="InductiveConstructor">nil</a> <a id="15951" class="Symbol">:</a> <a id="15953" href="plfa.Isomorphism.html#15929" class="Datatype">Bin</a>
  <a id="Bin.x0_"></a><a id="15959" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15959" class="InductiveConstructor Operator">x0_</a> <a id="15963" class="Symbol">:</a> <a id="15965" href="plfa.Isomorphism.html#15929" class="Datatype">Bin</a> <a id="15969" class="Symbol">→</a> <a id="15971" href="plfa.Isomorphism.html#15929" class="Datatype">Bin</a>
  <a id="Bin.x1_"></a><a id="15977" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15977" class="InductiveConstructor Operator">x1_</a> <a id="15981" class="Symbol">:</a> <a id="15983" href="plfa.Isomorphism.html#15929" class="Datatype">Bin</a> <a id="15987" class="Symbol">→</a> <a id="15989" href="plfa.Isomorphism.html#15929" class="Datatype">Bin</a>
</pre>{% endraw %}
{::comment}
And ask you to define the following functions
{:/}

我们要求你来定义下列函数：

    to : ℕ → Bin
    from : Bin → ℕ

{::comment}
which satisfy the following property:
{:/}

其满足如下性质：

    from (to n) ≡ n

{::comment}
Using the above, establish that there is an embedding of `ℕ` into `Bin`.
{:/}

使用上述条件，证明存在一个从 `ℕ` 到 `Bin` 的嵌入。

{::comment}
{% raw %}<pre class="Agda"><a id="16341" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="16378" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
Why do `to` and `from` not form an isomorphism?
{:/}

为什么 `to` 和 `from` 不能构造一个同构？


{::comment}
## Standard library
{:/}

## 标准库

{::comment}
Definitions similar to those in this chapter can be found in the standard library:
{:/}

标准库中可以找到与本章节中相似的定义：

{% raw %}<pre class="Agda"><a id="16664" class="Keyword">import</a> <a id="16671" href="https://agda.github.io/agda-stdlib/v1.1/Function.html" class="Module">Function</a> <a id="16680" class="Keyword">using</a> <a id="16686" class="Symbol">(</a><a id="16687" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">_∘_</a><a id="16690" class="Symbol">)</a>
<a id="16692" class="Keyword">import</a> <a id="16699" href="https://agda.github.io/agda-stdlib/v1.1/Function.Inverse.html" class="Module">Function.Inverse</a> <a id="16716" class="Keyword">using</a> <a id="16722" class="Symbol">(</a><a id="16723" href="https://agda.github.io/agda-stdlib/v1.1/Function.Inverse.html#2229" class="Function Operator">_↔_</a><a id="16726" class="Symbol">)</a>
<a id="16728" class="Keyword">import</a> <a id="16735" href="https://agda.github.io/agda-stdlib/v1.1/Function.LeftInverse.html" class="Module">Function.LeftInverse</a> <a id="16756" class="Keyword">using</a> <a id="16762" class="Symbol">(</a><a id="16763" href="https://agda.github.io/agda-stdlib/v1.1/Function.LeftInverse.html#2682" class="Function Operator">_↞_</a><a id="16766" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
The standard library `_↔_` and `_↞_` correspond to our `_≃_` and
`_≲_`, respectively, but those in the standard library are less
convenient, since they depend on a nested record structure and are
parameterised with regard to an arbitrary notion of equivalence.
{:/}

标准库中的 `_↔_` 和 `_↞_` 分别对应了我们定义的 `_≃_` 和 `_≲_`，
但是标准库中的定义使用起来不如我们的定义方便，因为标准库中的定义依赖于一个嵌套的记录结构，
并可以由任何相等性的记法来参数化。


## Unicode

{::comment}
This chapter uses the following unicode:

    ∘  U+2218  RING OPERATOR (\o, \circ, \comp)
    λ  U+03BB  GREEK SMALL LETTER LAMBDA (\lambda, \Gl)
    ≃  U+2243  ASYMPTOTICALLY EQUAL TO (\~-)
    ≲  U+2272  LESS-THAN OR EQUIVALENT TO (\<~)
    ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>)
{:/}

本章节使用了如下 Unicode：

    ∘  U+2218  环运算符 (\o, \circ, \comp)
    λ  U+03BB  小写希腊字母 LAMBDA (\lambda, \Gl)
    ≃  U+2243  渐进相等 (\~-)
    ≲  U+2272  小于或等价于 (\<~)
    ⇔  U+21D4  左右双箭头 (\<=>)
