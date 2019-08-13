---
src       : "src/plfa/Quantifiers.lagda.md"
title     : "Quantifiers: 全称量词与存在量词"
layout    : page
prev      : /Negation/
permalink : /Quantifiers/
next      : /Decidable/
translators: ["Fangyi Zhou"]
progress  : 100
---

{% raw %}<pre class="Agda"><a id="186" class="Keyword">module</a> <a id="193" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}" class="Module">plfa.Quantifiers</a> <a id="210" class="Keyword">where</a>
</pre>{% endraw %}
{::comment}
This chapter introduces universal and existential quantification.
{:/}

本章节介绍全称量化（Universal Quantification）和存在量化（Existential Quantification）。

{::comment}
## Imports
{:/}

## 导入

{% raw %}<pre class="Agda"><a id="416" class="Keyword">import</a> <a id="423" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="461" class="Symbol">as</a> <a id="464" class="Module">Eq</a>
<a id="467" class="Keyword">open</a> <a id="472" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="475" class="Keyword">using</a> <a id="481" class="Symbol">(</a><a id="482" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="485" class="Symbol">;</a> <a id="487" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="491" class="Symbol">)</a>
<a id="493" class="Keyword">open</a> <a id="498" class="Keyword">import</a> <a id="505" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="514" class="Keyword">using</a> <a id="520" class="Symbol">(</a><a id="521" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="522" class="Symbol">;</a> <a id="524" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="528" class="Symbol">;</a> <a id="530" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="533" class="Symbol">;</a> <a id="535" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="538" class="Symbol">;</a> <a id="540" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">_*_</a><a id="543" class="Symbol">)</a>
<a id="545" class="Keyword">open</a> <a id="550" class="Keyword">import</a> <a id="557" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="574" class="Keyword">using</a> <a id="580" class="Symbol">(</a><a id="581" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="583" class="Symbol">)</a>
<a id="585" class="Keyword">open</a> <a id="590" class="Keyword">import</a> <a id="597" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="610" class="Keyword">using</a> <a id="616" class="Symbol">(</a><a id="617" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">_×_</a><a id="620" class="Symbol">;</a> <a id="622" href="Agda.Builtin.Sigma.html#225" class="Field">proj₁</a><a id="627" class="Symbol">)</a> <a id="629" class="Keyword">renaming</a> <a id="638" class="Symbol">(</a><a id="639" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a> <a id="643" class="Symbol">to</a> <a id="646" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="651" class="Symbol">)</a>
<a id="653" class="Keyword">open</a> <a id="658" class="Keyword">import</a> <a id="665" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.html" class="Module">Data.Sum</a> <a id="674" class="Keyword">using</a> <a id="680" class="Symbol">(</a><a id="681" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">_⊎_</a><a id="684" class="Symbol">)</a>
<a id="686" class="Keyword">open</a> <a id="691" class="Keyword">import</a> <a id="698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}" class="Module">plfa.Isomorphism</a> <a id="715" class="Keyword">using</a> <a id="721" class="Symbol">(</a><a id="722" href="plfa.Isomorphism.html#5843" class="Record Operator">_≃_</a><a id="725" class="Symbol">;</a> <a id="727" href="plfa.Isomorphism.html#3758" class="Postulate">extensionality</a><a id="741" class="Symbol">)</a>
</pre>{% endraw %}

{::comment}
## Universals
{:/}

## 全称量化

{::comment}
We formalise universal quantification using the
dependent function type, which has appeared throughout this book.
{:/}

我们用依赖函数类型（Dependent Function Type）来形式化全称量化。
这样的形式贯穿全书地出现。


{::comment}
Given a variable `x` of type `A` and a proposition `B x` which
contains `x` as a free variable, the universally quantified
proposition `∀ (x : A) → B x` holds if for every term `M` of type
`A` the proposition `B M` holds.  Here `B M` stands for
the proposition `B x` with each free occurrence of `x` replaced by
`M`.  Variable `x` appears free in `B x` but bound in
`∀ (x : A) → B x`.
{:/}

给定一个 `A` 类型的变量 `x` 和一个带有 `x` 自由变量的命题 `B x`，全称量化
的命题 `∀ (x : A) → B x` 当对于所有类型为 `A` 的项 `M`，命题 `B M` 成立时成立。
在这里，`B M` 代表了将 `B x` 中自由出现的变量 `x` 替换成 `M` 以后的命题。
变量 `x` 在 `B x` 中以自由变量形式出现，但是在 `∀ (x : A) → B x` 中是约束的。

{::comment}
Evidence that `∀ (x : A) → B x` holds is of the form
{:/}

`∀ (x : A) → B x` 成立的证明由以下形式构成：

    λ (x : A) → N x

{::comment}
where `N x` is a term of type `B x`, and `N x` and `B x` both contain
a free variable `x` of type `A`.  Given a term `L` providing evidence
that `∀ (x : A) → B x` holds, and a term `M` of type `A`, the term `L
M` provides evidence that `B M` holds.  In other words, evidence that
`∀ (x : A) → B x` holds is a function that converts a term `M` of type
`A` into evidence that `B M` holds.
{:/}

其中 `N x` 是一个 `B x` 类型的项，`N x` 和 `B x` 都包含了一个 `A` 类型的自由变量 `x`。
给定一个项 `L`， 其提供 `∀ (x : A) → B x` 成立的证明，和一个类型为 `A` 的项 `M`，
`L M` 这一项则是 `B M` 成立的证明。换句话说，`∀ (x : A) → B x` 成立的证明是一个函数，
将类型为 `A` 的项 `M` 转换成 `B M` 成立的证明。

{::comment}
Put another way, if we know that `∀ (x : A) → B x` holds and that `M`
is a term of type `A` then we may conclude that `B M` holds:
{:/}

再换句话说，如果我们知道 `∀ (x : A) → B x` 成立，又知道 `M` 是一个类型为 `A` 的项，
那么我们可以推导出 `B M` 成立：
{% raw %}<pre class="Agda"><a id="∀-elim"></a><a id="2569" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#2569" class="Function">∀-elim</a> <a id="2576" class="Symbol">:</a> <a id="2578" class="Symbol">∀</a> <a id="2580" class="Symbol">{</a><a id="2581" href="plfa.Quantifiers.html#2581" class="Bound">A</a> <a id="2583" class="Symbol">:</a> <a id="2585" class="PrimitiveType">Set</a><a id="2588" class="Symbol">}</a> <a id="2590" class="Symbol">{</a><a id="2591" href="plfa.Quantifiers.html#2591" class="Bound">B</a> <a id="2593" class="Symbol">:</a> <a id="2595" href="plfa.Quantifiers.html#2581" class="Bound">A</a> <a id="2597" class="Symbol">→</a> <a id="2599" class="PrimitiveType">Set</a><a id="2602" class="Symbol">}</a>
  <a id="2606" class="Symbol">→</a> <a id="2608" class="Symbol">(</a><a id="2609" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#2609" class="Bound">L</a> <a id="2611" class="Symbol">:</a> <a id="2613" class="Symbol">∀</a> <a id="2615" class="Symbol">(</a><a id="2616" href="plfa.Quantifiers.html#2616" class="Bound">x</a> <a id="2618" class="Symbol">:</a> <a id="2620" href="plfa.Quantifiers.html#2581" class="Bound">A</a><a id="2621" class="Symbol">)</a> <a id="2623" class="Symbol">→</a> <a id="2625" href="plfa.Quantifiers.html#2591" class="Bound">B</a> <a id="2627" href="plfa.Quantifiers.html#2616" class="Bound">x</a><a id="2628" class="Symbol">)</a>
  <a id="2632" class="Symbol">→</a> <a id="2634" class="Symbol">(</a><a id="2635" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#2635" class="Bound">M</a> <a id="2637" class="Symbol">:</a> <a id="2639" href="plfa.Quantifiers.html#2581" class="Bound">A</a><a id="2640" class="Symbol">)</a>
    <a id="2646" class="Comment">-----------------</a>
  <a id="2666" class="Symbol">→</a> <a id="2668" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#2591" class="Bound">B</a> <a id="2670" href="plfa.Quantifiers.html#2635" class="Bound">M</a>
<a id="2672" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#2569" class="Function">∀-elim</a> <a id="2679" href="plfa.Quantifiers.html#2679" class="Bound">L</a> <a id="2681" href="plfa.Quantifiers.html#2681" class="Bound">M</a> <a id="2683" class="Symbol">=</a> <a id="2685" href="plfa.Quantifiers.html#2679" class="Bound">L</a> <a id="2687" href="plfa.Quantifiers.html#2681" class="Bound">M</a>
</pre>{% endraw %}
{::comment}
As with `→-elim`, the rule corresponds to function application.
{:/}

如 `→-elim` 那样，这条规则对应了函数应用。

{::comment}
Functions arise as a special case of dependent functions,
where the range does not depend on a variable drawn from the domain.
When a function is viewed as evidence of implication, both its
argument and result are viewed as evidence, whereas when a dependent
function is viewed as evidence of a universal, its argument is viewed
as an element of a data type and its result is viewed as evidence of
a proposition that depends on the argument. This difference is largely
a matter of interpretation, since in Agda a value of a type and
evidence of a proposition are indistinguishable.
{:/}

函数是依赖函数的一种特殊形式，其值域不取决于定义域中的变量。当一个函数被视为
蕴涵的证明时，它的参数和结果都是证明，而当一个依赖函数被视为全称量词的证明时，
它的参数被视为数据类型中的一个元素，而结果是一个依赖于参数的命题的证明。因为在
Agda 中，一个数据类型中的一个值和一个命题的证明是无法区别的，这样的区别很大程度上
取决于如何来诠释。

{::comment}
Dependent function types are sometimes referred to as dependent
products, because if `A` is a finite type with values `x₁ , ⋯ , xₙ`,
and if each of the types `B x₁ , ⋯ , B xₙ` has `m₁ , ⋯ , mₙ` distinct
members, then `∀ (x : A) → B x` has `m₁ * ⋯ * mₙ` members.  Indeed,
sometimes the notation `∀ (x : A) → B x` is replaced by a notation
such as `Π[ x ∈ A ] (B x)`, where `Π` stands for product.  However, we
will stick with the name dependent function, because (as we will see)
dependent product is ambiguous.
{:/}

依赖函数类型也被叫做依赖积（Dependent Product），因为如果 `A` 是一个有限的数据类型，
有值 `x₁ , ⋯ , xₙ`，如果每个类型 `B x₁ , ⋯ , B xₙ` 有 `m₁ , ⋯ , mₙ` 个不同的成员，
那么 `∀ (x : A) → B x` 有 `m₁ * ⋯ * mₙ` 个成员。的确，`∀ (x : A) → B x` 的记法有时
也被 `Π[ x ∈ A ] (B x)` 取代，其中 `Π` 代表积。然而，我们还是使用依赖函数这个名称，
因为依赖积这个名称是有歧义的，我们后续会体会到歧义所在。

{::comment}
#### Exercise `∀-distrib-×` (recommended)
{:/}

#### 练习 `∀-distrib-×` （推荐）

{::comment}
Show that universals distribute over conjunction:
{:/}

证明全称量词对于合取满足分配律：

{% raw %}<pre class="Agda"><a id="4558" class="Keyword">postulate</a>
  <a id="∀-distrib-×"></a><a id="4570" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4570" class="Postulate">∀-distrib-×</a> <a id="4582" class="Symbol">:</a> <a id="4584" class="Symbol">∀</a> <a id="4586" class="Symbol">{</a><a id="4587" href="plfa.Quantifiers.html#4587" class="Bound">A</a> <a id="4589" class="Symbol">:</a> <a id="4591" class="PrimitiveType">Set</a><a id="4594" class="Symbol">}</a> <a id="4596" class="Symbol">{</a><a id="4597" href="plfa.Quantifiers.html#4597" class="Bound">B</a> <a id="4599" href="plfa.Quantifiers.html#4599" class="Bound">C</a> <a id="4601" class="Symbol">:</a> <a id="4603" href="plfa.Quantifiers.html#4587" class="Bound">A</a> <a id="4605" class="Symbol">→</a> <a id="4607" class="PrimitiveType">Set</a><a id="4610" class="Symbol">}</a> <a id="4612" class="Symbol">→</a>
    <a id="4618" class="Symbol">(∀</a> <a id="4621" class="Symbol">(</a><a id="4622" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4622" class="Bound">x</a> <a id="4624" class="Symbol">:</a> <a id="4626" href="plfa.Quantifiers.html#4587" class="Bound">A</a><a id="4627" class="Symbol">)</a> <a id="4629" class="Symbol">→</a> <a id="4631" href="plfa.Quantifiers.html#4597" class="Bound">B</a> <a id="4633" href="plfa.Quantifiers.html#4622" class="Bound">x</a> <a id="4635" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="4637" href="plfa.Quantifiers.html#4599" class="Bound">C</a> <a id="4639" href="plfa.Quantifiers.html#4622" class="Bound">x</a><a id="4640" class="Symbol">)</a> <a id="4642" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5843" class="Record Operator">≃</a> <a id="4644" class="Symbol">(∀</a> <a id="4647" class="Symbol">(</a><a id="4648" href="plfa.Quantifiers.html#4648" class="Bound">x</a> <a id="4650" class="Symbol">:</a> <a id="4652" href="plfa.Quantifiers.html#4587" class="Bound">A</a><a id="4653" class="Symbol">)</a> <a id="4655" class="Symbol">→</a> <a id="4657" href="plfa.Quantifiers.html#4597" class="Bound">B</a> <a id="4659" href="plfa.Quantifiers.html#4648" class="Bound">x</a><a id="4660" class="Symbol">)</a> <a id="4662" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="4664" class="Symbol">(∀</a> <a id="4667" class="Symbol">(</a><a id="4668" href="plfa.Quantifiers.html#4668" class="Bound">x</a> <a id="4670" class="Symbol">:</a> <a id="4672" href="plfa.Quantifiers.html#4587" class="Bound">A</a><a id="4673" class="Symbol">)</a> <a id="4675" class="Symbol">→</a> <a id="4677" href="plfa.Quantifiers.html#4599" class="Bound">C</a> <a id="4679" href="plfa.Quantifiers.html#4668" class="Bound">x</a><a id="4680" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Compare this with the result (`→-distrib-×`) in
Chapter [Connectives]({{ site.baseurl }}/Connectives/).
{:/

将这个结果与 [Connectives]({{ site.baseurl }}/Connectives/)
章节中的 (`→-distrib-×`) 结果对比。

{::comment}
#### Exercise `⊎∀-implies-∀⊎`
{:/}

#### 练习 `⊎∀-implies-∀⊎`

{::comment}
Show that a disjunction of universals implies a universal of disjunctions:
{:/}

证明全称命题的析取蕴涵了析取的全称命题：

{% raw %}<pre class="Agda"><a id="5082" class="Keyword">postulate</a>
  <a id="⊎∀-implies-∀⊎"></a><a id="5094" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5094" class="Postulate">⊎∀-implies-∀⊎</a> <a id="5108" class="Symbol">:</a> <a id="5110" class="Symbol">∀</a> <a id="5112" class="Symbol">{</a><a id="5113" href="plfa.Quantifiers.html#5113" class="Bound">A</a> <a id="5115" class="Symbol">:</a> <a id="5117" class="PrimitiveType">Set</a><a id="5120" class="Symbol">}</a> <a id="5122" class="Symbol">{</a><a id="5123" href="plfa.Quantifiers.html#5123" class="Bound">B</a> <a id="5125" href="plfa.Quantifiers.html#5125" class="Bound">C</a> <a id="5127" class="Symbol">:</a> <a id="5129" href="plfa.Quantifiers.html#5113" class="Bound">A</a> <a id="5131" class="Symbol">→</a> <a id="5133" class="PrimitiveType">Set</a><a id="5136" class="Symbol">}</a> <a id="5138" class="Symbol">→</a>
    <a id="5144" class="Symbol">(∀</a> <a id="5147" class="Symbol">(</a><a id="5148" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5148" class="Bound">x</a> <a id="5150" class="Symbol">:</a> <a id="5152" href="plfa.Quantifiers.html#5113" class="Bound">A</a><a id="5153" class="Symbol">)</a> <a id="5155" class="Symbol">→</a> <a id="5157" href="plfa.Quantifiers.html#5123" class="Bound">B</a> <a id="5159" href="plfa.Quantifiers.html#5148" class="Bound">x</a><a id="5160" class="Symbol">)</a> <a id="5162" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="5164" class="Symbol">(∀</a> <a id="5167" class="Symbol">(</a><a id="5168" href="plfa.Quantifiers.html#5168" class="Bound">x</a> <a id="5170" class="Symbol">:</a> <a id="5172" href="plfa.Quantifiers.html#5113" class="Bound">A</a><a id="5173" class="Symbol">)</a> <a id="5175" class="Symbol">→</a> <a id="5177" href="plfa.Quantifiers.html#5125" class="Bound">C</a> <a id="5179" href="plfa.Quantifiers.html#5168" class="Bound">x</a><a id="5180" class="Symbol">)</a>  <a id="5183" class="Symbol">→</a>  <a id="5186" class="Symbol">∀</a> <a id="5188" class="Symbol">(</a><a id="5189" href="plfa.Quantifiers.html#5189" class="Bound">x</a> <a id="5191" class="Symbol">:</a> <a id="5193" href="plfa.Quantifiers.html#5113" class="Bound">A</a><a id="5194" class="Symbol">)</a> <a id="5196" class="Symbol">→</a> <a id="5198" href="plfa.Quantifiers.html#5123" class="Bound">B</a> <a id="5200" href="plfa.Quantifiers.html#5189" class="Bound">x</a> <a id="5202" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="5204" href="plfa.Quantifiers.html#5125" class="Bound">C</a> <a id="5206" href="plfa.Quantifiers.html#5189" class="Bound">x</a>
</pre>{% endraw %}
{::comment}
Does the converse hold? If so, prove; if not, explain why.
{:/}

逆命题成立么？如果成立，给出证明。如果不成立，解释为什么。


{::comment}
#### Exercise `∀-×`
{:/}

#### 练习 `∀-×`

{::comment}
Consider the following type.
{:/}

参考下面的类型：

{% raw %}<pre class="Agda"><a id="5436" class="Keyword">data</a> <a id="Tri"></a><a id="5441" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5441" class="Datatype">Tri</a> <a id="5445" class="Symbol">:</a> <a id="5447" class="PrimitiveType">Set</a> <a id="5451" class="Keyword">where</a>
  <a id="Tri.aa"></a><a id="5459" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5459" class="InductiveConstructor">aa</a> <a id="5462" class="Symbol">:</a> <a id="5464" href="plfa.Quantifiers.html#5441" class="Datatype">Tri</a>
  <a id="Tri.bb"></a><a id="5470" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5470" class="InductiveConstructor">bb</a> <a id="5473" class="Symbol">:</a> <a id="5475" href="plfa.Quantifiers.html#5441" class="Datatype">Tri</a>
  <a id="Tri.cc"></a><a id="5481" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5481" class="InductiveConstructor">cc</a> <a id="5484" class="Symbol">:</a> <a id="5486" href="plfa.Quantifiers.html#5441" class="Datatype">Tri</a>
</pre>{% endraw %}
{::comment}
Let `B` be a type indexed by `Tri`, that is `B : Tri → Set`.
Show that `∀ (x : Tri) → B x` is isomorphic to `B aa × B bb × B cc`.
{:/}

令 `B` 作为由 `Tri` 索引的一个类型，也就是说 `B : Tri → Set`。
证明 `∀ (x : Tri) → B x` 和 `B aa × B bb × B cc` 是同构的。


{::comment}
## Existentials
{:/}

## 存在量化

{::comment}
Given a variable `x` of type `A` and a proposition `B x` which
contains `x` as a free variable, the existentially quantified
proposition `Σ[ x ∈ A ] B x` holds if for some term `M` of type
`A` the proposition `B M` holds.  Here `B M` stands for
the proposition `B x` with each free occurrence of `x` replaced by
`M`.  Variable `x` appears free in `B x` but bound in
`Σ[ x ∈ A ] B x`.
{:/}

给定一个 `A` 类型的变量 `x` 和一个带有 `x` 自由变量的命题 `B x`，存在量化
的命题 `Σ[ x ∈ A ] B x` 当对于一些类型为 `A` 的项 `M`，命题 `B M` 成立时成立。
在这里，`B M` 代表了将 `B x` 中自由出现的变量 `x` 替换成 `M` 以后的命题。
变量 `x` 在 `B x` 中以自由变量形式出现，但是在 `Σ[ x ∈ A ] B x` 中是约束的。

{::comment}
We formalise existential quantification by declaring a suitable
inductive type:
{:/}

我们定义一个合适的归纳数据类型来形式化存在量化：

{% raw %}<pre class="Agda"><a id="6525" class="Keyword">data</a> <a id="Σ"></a><a id="6530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6530" class="Datatype">Σ</a> <a id="6532" class="Symbol">(</a><a id="6533" href="plfa.Quantifiers.html#6533" class="Bound">A</a> <a id="6535" class="Symbol">:</a> <a id="6537" class="PrimitiveType">Set</a><a id="6540" class="Symbol">)</a> <a id="6542" class="Symbol">(</a><a id="6543" href="plfa.Quantifiers.html#6543" class="Bound">B</a> <a id="6545" class="Symbol">:</a> <a id="6547" href="plfa.Quantifiers.html#6533" class="Bound">A</a> <a id="6549" class="Symbol">→</a> <a id="6551" class="PrimitiveType">Set</a><a id="6554" class="Symbol">)</a> <a id="6556" class="Symbol">:</a> <a id="6558" class="PrimitiveType">Set</a> <a id="6562" class="Keyword">where</a>
  <a id="Σ.⟨_,_⟩"></a><a id="6570" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6570" class="InductiveConstructor Operator">⟨_,_⟩</a> <a id="6576" class="Symbol">:</a> <a id="6578" class="Symbol">(</a><a id="6579" href="plfa.Quantifiers.html#6579" class="Bound">x</a> <a id="6581" class="Symbol">:</a> <a id="6583" href="plfa.Quantifiers.html#6533" class="Bound">A</a><a id="6584" class="Symbol">)</a> <a id="6586" class="Symbol">→</a> <a id="6588" href="plfa.Quantifiers.html#6543" class="Bound">B</a> <a id="6590" href="plfa.Quantifiers.html#6579" class="Bound">x</a> <a id="6592" class="Symbol">→</a> <a id="6594" href="plfa.Quantifiers.html#6530" class="Datatype">Σ</a> <a id="6596" href="plfa.Quantifiers.html#6533" class="Bound">A</a> <a id="6598" href="plfa.Quantifiers.html#6543" class="Bound">B</a>
</pre>{% endraw %}
{::comment}
We define a convenient syntax for existentials as follows:
{:/}

我们为存在量词定义一个方便的语法：

{% raw %}<pre class="Agda"><a id="Σ-syntax"></a><a id="6705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6705" class="Function">Σ-syntax</a> <a id="6714" class="Symbol">=</a> <a id="6716" href="plfa.Quantifiers.html#6530" class="Datatype">Σ</a>
<a id="6718" class="Keyword">infix</a> <a id="6724" class="Number">2</a> <a id="6726" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6705" class="Function">Σ-syntax</a>
<a id="6735" class="Keyword">syntax</a> <a id="6742" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6705" class="Function">Σ-syntax</a> <a id="6751" class="Bound">A</a> <a id="6753" class="Symbol">(λ</a> <a id="6756" class="Bound">x</a> <a id="6758" class="Symbol">→</a> <a id="6760" class="Bound">B</a><a id="6761" class="Symbol">)</a> <a id="6763" class="Symbol">=</a> <a id="6765" class="Function">Σ[</a> <a id="6768" class="Bound">x</a> <a id="6770" class="Function">∈</a> <a id="6772" class="Bound">A</a> <a id="6774" class="Function">]</a> <a id="6776" class="Bound">B</a>
</pre>{% endraw %}
{::comment}
This is our first use of a syntax declaration, which specifies that
the term on the left may be written with the syntax on the right.
The special syntax is available only when the identifier
`Σ-syntax` is imported.
{:/}

这是我们第一次使用语法声明，其表示左手边的项可以以右手边的语法来书写。
这种特殊语法只有在标识符 `Σ-syntax` 被导入时可用。

{::comment}
Evidence that `Σ[ x ∈ A ] B x` holds is of the form
`⟨ M , N ⟩` where `M` is a term of type `A`, and `N` is evidence
that `B M` holds.
{:/}

`Σ[ x ∈ A ] B x` 成立的证明由 `⟨ M , N ⟩` 组成，其中 `M` 是类型为 `A` 的项，
`N` 是 `B M` 成立的证明。


{::comment}
Equivalently, we could also declare existentials as a record type:
{:/}

我们也可以用记录类型来等价地定义存在量化。

{% raw %}<pre class="Agda"><a id="7430" class="Keyword">record</a> <a id="Σ′"></a><a id="7437" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#7437" class="Record">Σ′</a> <a id="7440" class="Symbol">(</a><a id="7441" href="plfa.Quantifiers.html#7441" class="Bound">A</a> <a id="7443" class="Symbol">:</a> <a id="7445" class="PrimitiveType">Set</a><a id="7448" class="Symbol">)</a> <a id="7450" class="Symbol">(</a><a id="7451" href="plfa.Quantifiers.html#7451" class="Bound">B</a> <a id="7453" class="Symbol">:</a> <a id="7455" href="plfa.Quantifiers.html#7441" class="Bound">A</a> <a id="7457" class="Symbol">→</a> <a id="7459" class="PrimitiveType">Set</a><a id="7462" class="Symbol">)</a> <a id="7464" class="Symbol">:</a> <a id="7466" class="PrimitiveType">Set</a> <a id="7470" class="Keyword">where</a>
  <a id="7478" class="Keyword">field</a>
    <a id="Σ′.proj₁′"></a><a id="7488" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#7488" class="Field">proj₁′</a> <a id="7495" class="Symbol">:</a> <a id="7497" href="plfa.Quantifiers.html#7441" class="Bound">A</a>
    <a id="Σ′.proj₂′"></a><a id="7503" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#7503" class="Field">proj₂′</a> <a id="7510" class="Symbol">:</a> <a id="7512" href="plfa.Quantifiers.html#7451" class="Bound">B</a> <a id="7514" href="plfa.Quantifiers.html#7488" class="Field">proj₁′</a>
</pre>{% endraw %}
{::comment}
Here record construction
{:/}

这里的记录构造

    record
      { proj₁′ = M
      ; proj₂′ = N
      }

{::comment}
corresponds to the term
{:/}

对应了项

    ⟨ M , N ⟩

{::comment}
where `M` is a term of type `A` and `N` is a term of type `B M`.
{:/}

其中 `M` 是类型为 `A` 的项，`N` 是类型为 `B M` 的项。

{::comment}
Products arise as a special case of existentials, where the second
component does not depend on a variable drawn from the first
component.  When a product is viewed as evidence of a conjunction,
both of its components are viewed as evidence, whereas when it is
viewed as evidence of an existential, the first component is viewed as
an element of a datatype and the second component is viewed as
evidence of a proposition that depends on the first component.  This
difference is largely a matter of interpretation, since in Agda a value
of a type and evidence of a proposition are indistinguishable.
{:/}

积是依赖积的一种特殊形式，其第二分量不取决于第一分量中的变量。当一个积被视为
合取的证明时，它的两个分量都是证明，而当一个依赖积被视为存在量词的证明时，
它的第一分量被视为数据类型中的一个元素，而第二分量是一个依赖于第一分量的命题的证明。因为在
Agda 中，一个数据类型中的一个值一个命题的证明是无法区别的，这样的区别很大程度上
取决于如何来诠释。

{::comment}
Existentials are sometimes referred to as dependent sums,
because if `A` is a finite type with values `x₁ , ⋯ , xₙ`, and if
each of the types `B x₁ , ⋯ B xₙ` has `m₁ , ⋯ , mₙ` distinct members,
then `Σ[ x ∈ A ] B x` has `m₁ + ⋯ + mₙ` members, which explains the
choice of notation for existentials, since `Σ` stands for sum.
{:/}

存在量化也被叫做依赖和（Dependent Sum），因为如果 `A` 是一个有限的数据类型，
有值 `x₁ , ⋯ , xₙ`，如果每个类型 `B x₁ , ⋯ , B xₙ` 有 `m₁ , ⋯ , mₙ` 个不同的成员，
那么 `Σ[ x ∈ A ] B x` 有 `m₁ + ⋯ + mₙ` 个成员，这也解释了选择使用这个记法的原因——
`Σ` 代表和。

{::comment}
Existentials are sometimes referred to as dependent products, since
products arise as a special case.  However, that choice of names is
doubly confusing, since universals also have a claim to the name dependent
product and since existentials also have a claim to the name dependent sum.
{:/}

存在量化有时也被叫做依赖积（Dependent Product），因为积是其中的一种特殊形式。但是，
这样的叫法非常让人困扰，因为全程量化也被叫做依赖积，而存在量化已经有依赖和的叫法。

{::comment}
A common notation for existentials is `∃` (analogous to `∀` for universals).
We follow the convention of the Agda standard library, and reserve this
notation for the case where the domain of the bound variable is left implicit:
{:/}

存在量词的普通记法是 `∃` （与全程量词的 `∀` 记法相类似）。我们使用 Agda 标准库中的惯例，
使用一种隐式申明约束变量定义域的记法。

{% raw %}<pre class="Agda"><a id="∃"></a><a id="9864" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9864" class="Function">∃</a> <a id="9866" class="Symbol">:</a> <a id="9868" class="Symbol">∀</a> <a id="9870" class="Symbol">{</a><a id="9871" href="plfa.Quantifiers.html#9871" class="Bound">A</a> <a id="9873" class="Symbol">:</a> <a id="9875" class="PrimitiveType">Set</a><a id="9878" class="Symbol">}</a> <a id="9880" class="Symbol">(</a><a id="9881" href="plfa.Quantifiers.html#9881" class="Bound">B</a> <a id="9883" class="Symbol">:</a> <a id="9885" href="plfa.Quantifiers.html#9871" class="Bound">A</a> <a id="9887" class="Symbol">→</a> <a id="9889" class="PrimitiveType">Set</a><a id="9892" class="Symbol">)</a> <a id="9894" class="Symbol">→</a> <a id="9896" class="PrimitiveType">Set</a>
<a id="9900" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9864" class="Function">∃</a> <a id="9902" class="Symbol">{</a><a id="9903" href="plfa.Quantifiers.html#9903" class="Bound">A</a><a id="9904" class="Symbol">}</a> <a id="9906" href="plfa.Quantifiers.html#9906" class="Bound">B</a> <a id="9908" class="Symbol">=</a> <a id="9910" href="plfa.Quantifiers.html#6530" class="Datatype">Σ</a> <a id="9912" href="plfa.Quantifiers.html#9903" class="Bound">A</a> <a id="9914" href="plfa.Quantifiers.html#9906" class="Bound">B</a>

<a id="∃-syntax"></a><a id="9917" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9917" class="Function">∃-syntax</a> <a id="9926" class="Symbol">=</a> <a id="9928" href="plfa.Quantifiers.html#9864" class="Function">∃</a>
<a id="9930" class="Keyword">syntax</a> <a id="9937" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9917" class="Function">∃-syntax</a> <a id="9946" class="Symbol">(λ</a> <a id="9949" class="Bound">x</a> <a id="9951" class="Symbol">→</a> <a id="9953" class="Bound">B</a><a id="9954" class="Symbol">)</a> <a id="9956" class="Symbol">=</a> <a id="9958" class="Function">∃[</a> <a id="9961" class="Bound">x</a> <a id="9963" class="Function">]</a> <a id="9965" class="Bound">B</a>
</pre>{% endraw %}
{::comment}
The special syntax is available only when the identifier `∃-syntax` is imported.
We will tend to use this syntax, since it is shorter and more familiar.
{:/}

这种特殊的语法只有在 `∃-syntax` 标识符被导入时可用。我们将倾向于使用这种语法，因为它更短，
而且看上去更熟悉。

{::comment}
Given evidence that `∀ x → B x → C` holds, where `C` does not contain
`x` as a free variable, and given evidence that `∃[ x ] B x` holds, we
may conclude that `C` holds:
{:/}

给定 `∀ x → B x → C` 成立的证明，其中 `C` 不包括自由变量 `x`，给定 `∃[ x ] B x` 成立的
证明，我们可以推导出 `C` 成立。

{% raw %}<pre class="Agda"><a id="∃-elim"></a><a id="10482" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10482" class="Function">∃-elim</a> <a id="10489" class="Symbol">:</a> <a id="10491" class="Symbol">∀</a> <a id="10493" class="Symbol">{</a><a id="10494" href="plfa.Quantifiers.html#10494" class="Bound">A</a> <a id="10496" class="Symbol">:</a> <a id="10498" class="PrimitiveType">Set</a><a id="10501" class="Symbol">}</a> <a id="10503" class="Symbol">{</a><a id="10504" href="plfa.Quantifiers.html#10504" class="Bound">B</a> <a id="10506" class="Symbol">:</a> <a id="10508" href="plfa.Quantifiers.html#10494" class="Bound">A</a> <a id="10510" class="Symbol">→</a> <a id="10512" class="PrimitiveType">Set</a><a id="10515" class="Symbol">}</a> <a id="10517" class="Symbol">{</a><a id="10518" href="plfa.Quantifiers.html#10518" class="Bound">C</a> <a id="10520" class="Symbol">:</a> <a id="10522" class="PrimitiveType">Set</a><a id="10525" class="Symbol">}</a>
  <a id="10529" class="Symbol">→</a> <a id="10531" class="Symbol">(∀</a> <a id="10534" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10534" class="Bound">x</a> <a id="10536" class="Symbol">→</a> <a id="10538" href="plfa.Quantifiers.html#10504" class="Bound">B</a> <a id="10540" href="plfa.Quantifiers.html#10534" class="Bound">x</a> <a id="10542" class="Symbol">→</a> <a id="10544" href="plfa.Quantifiers.html#10518" class="Bound">C</a><a id="10545" class="Symbol">)</a>
  <a id="10549" class="Symbol">→</a> <a id="10551" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9917" class="Function">∃[</a> <a id="10554" href="plfa.Quantifiers.html#10554" class="Bound">x</a> <a id="10556" href="plfa.Quantifiers.html#9917" class="Function">]</a> <a id="10558" href="plfa.Quantifiers.html#10504" class="Bound">B</a> <a id="10560" href="plfa.Quantifiers.html#10554" class="Bound">x</a>
    <a id="10566" class="Comment">---------------</a>
  <a id="10584" class="Symbol">→</a> <a id="10586" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10518" class="Bound">C</a>
<a id="10588" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10482" class="Function">∃-elim</a> <a id="10595" href="plfa.Quantifiers.html#10595" class="Bound">f</a> <a id="10597" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟨</a> <a id="10599" href="plfa.Quantifiers.html#10599" class="Bound">x</a> <a id="10601" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">,</a> <a id="10603" href="plfa.Quantifiers.html#10603" class="Bound">y</a> <a id="10605" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟩</a> <a id="10607" class="Symbol">=</a> <a id="10609" href="plfa.Quantifiers.html#10595" class="Bound">f</a> <a id="10611" href="plfa.Quantifiers.html#10599" class="Bound">x</a> <a id="10613" href="plfa.Quantifiers.html#10603" class="Bound">y</a>
</pre>{% endraw %}
{::comment}
In other words, if we know for every `x` of type `A` that `B x`
implies `C`, and we know for some `x` of type `A` that `B x` holds,
then we may conclude that `C` holds.  This is because we may
instantiate that proof that `∀ x → B x → C` to any value `x` of type
`A` and any `y` of type `B x`, and exactly such values are provided by
the evidence for `∃[ x ] B x`.
{:/}

换句话说，如果我们知道对于任何 `A` 类型的 `x`，`B x` 蕴涵了 `C`，还知道对于某个类型
`A` 的 `x`，`B x` 成立，那么我们可以推导出 `C` 成立。这是因为我们可以先将 `∀ x → B x → C`
的证明对于 `A` 类型的 `x` 和 `B x` 类型的 `y` 实例化，而这样的值恰好可以由 `∃[ x ] B x`
的证明来提供。

{::comment}
Indeed, the converse also holds, and the two together form an isomorphism:
{:/}

的确，逆命题也成立，两者合起来构成一个同构：

{% raw %}<pre class="Agda"><a id="∀∃-currying"></a><a id="11309" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11309" class="Function">∀∃-currying</a> <a id="11321" class="Symbol">:</a> <a id="11323" class="Symbol">∀</a> <a id="11325" class="Symbol">{</a><a id="11326" href="plfa.Quantifiers.html#11326" class="Bound">A</a> <a id="11328" class="Symbol">:</a> <a id="11330" class="PrimitiveType">Set</a><a id="11333" class="Symbol">}</a> <a id="11335" class="Symbol">{</a><a id="11336" href="plfa.Quantifiers.html#11336" class="Bound">B</a> <a id="11338" class="Symbol">:</a> <a id="11340" href="plfa.Quantifiers.html#11326" class="Bound">A</a> <a id="11342" class="Symbol">→</a> <a id="11344" class="PrimitiveType">Set</a><a id="11347" class="Symbol">}</a> <a id="11349" class="Symbol">{</a><a id="11350" href="plfa.Quantifiers.html#11350" class="Bound">C</a> <a id="11352" class="Symbol">:</a> <a id="11354" class="PrimitiveType">Set</a><a id="11357" class="Symbol">}</a>
  <a id="11361" class="Symbol">→</a> <a id="11363" class="Symbol">(∀</a> <a id="11366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11366" class="Bound">x</a> <a id="11368" class="Symbol">→</a> <a id="11370" href="plfa.Quantifiers.html#11336" class="Bound">B</a> <a id="11372" href="plfa.Quantifiers.html#11366" class="Bound">x</a> <a id="11374" class="Symbol">→</a> <a id="11376" href="plfa.Quantifiers.html#11350" class="Bound">C</a><a id="11377" class="Symbol">)</a> <a id="11379" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5843" class="Record Operator">≃</a> <a id="11381" class="Symbol">(</a><a id="11382" href="plfa.Quantifiers.html#9917" class="Function">∃[</a> <a id="11385" href="plfa.Quantifiers.html#11385" class="Bound">x</a> <a id="11387" href="plfa.Quantifiers.html#9917" class="Function">]</a> <a id="11389" href="plfa.Quantifiers.html#11336" class="Bound">B</a> <a id="11391" href="plfa.Quantifiers.html#11385" class="Bound">x</a> <a id="11393" class="Symbol">→</a> <a id="11395" href="plfa.Quantifiers.html#11350" class="Bound">C</a><a id="11396" class="Symbol">)</a>
<a id="11398" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11309" class="Function">∀∃-currying</a> <a id="11410" class="Symbol">=</a>
  <a id="11414" class="Keyword">record</a>
    <a id="11425" class="Symbol">{</a> <a id="11427" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5883" class="Field">to</a>      <a id="11435" class="Symbol">=</a>  <a id="11438" class="Symbol">λ{</a> <a id="11441" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11441" class="Bound">f</a> <a id="11443" class="Symbol">→</a> <a id="11445" class="Symbol">λ{</a> <a id="11448" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟨</a> <a id="11450" href="plfa.Quantifiers.html#11450" class="Bound">x</a> <a id="11452" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">,</a> <a id="11454" href="plfa.Quantifiers.html#11454" class="Bound">y</a> <a id="11456" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟩</a> <a id="11458" class="Symbol">→</a> <a id="11460" href="plfa.Quantifiers.html#11441" class="Bound">f</a> <a id="11462" href="plfa.Quantifiers.html#11450" class="Bound">x</a> <a id="11464" href="plfa.Quantifiers.html#11454" class="Bound">y</a> <a id="11466" class="Symbol">}}</a>
    <a id="11473" class="Symbol">;</a> <a id="11475" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5900" class="Field">from</a>    <a id="11483" class="Symbol">=</a>  <a id="11486" class="Symbol">λ{</a> <a id="11489" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11489" class="Bound">g</a> <a id="11491" class="Symbol">→</a> <a id="11493" class="Symbol">λ{</a> <a id="11496" href="plfa.Quantifiers.html#11496" class="Bound">x</a> <a id="11498" class="Symbol">→</a> <a id="11500" class="Symbol">λ{</a> <a id="11503" href="plfa.Quantifiers.html#11503" class="Bound">y</a> <a id="11505" class="Symbol">→</a> <a id="11507" href="plfa.Quantifiers.html#11489" class="Bound">g</a> <a id="11509" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟨</a> <a id="11511" href="plfa.Quantifiers.html#11496" class="Bound">x</a> <a id="11513" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">,</a> <a id="11515" href="plfa.Quantifiers.html#11503" class="Bound">y</a> <a id="11517" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟩</a> <a id="11519" class="Symbol">}}}</a>
    <a id="11527" class="Symbol">;</a> <a id="11529" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5917" class="Field">from∘to</a> <a id="11537" class="Symbol">=</a>  <a id="11540" class="Symbol">λ{</a> <a id="11543" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11543" class="Bound">f</a> <a id="11545" class="Symbol">→</a> <a id="11547" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="11552" class="Symbol">}</a>
    <a id="11558" class="Symbol">;</a> <a id="11560" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5959" class="Field">to∘from</a> <a id="11568" class="Symbol">=</a>  <a id="11571" class="Symbol">λ{</a> <a id="11574" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11574" class="Bound">g</a> <a id="11576" class="Symbol">→</a> <a id="11578" href="plfa.Isomorphism.html#3758" class="Postulate">extensionality</a> <a id="11593" class="Symbol">λ{</a> <a id="11596" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟨</a> <a id="11598" href="plfa.Quantifiers.html#11598" class="Bound">x</a> <a id="11600" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">,</a> <a id="11602" href="plfa.Quantifiers.html#11602" class="Bound">y</a> <a id="11604" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟩</a> <a id="11606" class="Symbol">→</a> <a id="11608" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="11613" class="Symbol">}}</a>
    <a id="11620" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
The result can be viewed as a generalisation of currying.  Indeed, the code to
establish the isomorphism is identical to what we wrote when discussing
[implication]({{ site.baseurl }}/Connectives/#implication).
{:/}

这可以被看做是将柯里化推广的结果。的确，建立这两者同构的证明与之前我们讨论
[蕴涵]({{ site.baseurl }}/Connectives/#implication)时给出的证明是一样的。

{::comment}
#### Exercise `∃-distrib-⊎` (recommended)
{:/}

#### 练习 `∃-distrib-⊎` （推荐）

{::comment}
Show that existentials distribute over disjunction:
{:/}

证明存在量词对于析取满足分配律：

{% raw %}<pre class="Agda"><a id="12136" class="Keyword">postulate</a>
  <a id="∃-distrib-⊎"></a><a id="12148" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12148" class="Postulate">∃-distrib-⊎</a> <a id="12160" class="Symbol">:</a> <a id="12162" class="Symbol">∀</a> <a id="12164" class="Symbol">{</a><a id="12165" href="plfa.Quantifiers.html#12165" class="Bound">A</a> <a id="12167" class="Symbol">:</a> <a id="12169" class="PrimitiveType">Set</a><a id="12172" class="Symbol">}</a> <a id="12174" class="Symbol">{</a><a id="12175" href="plfa.Quantifiers.html#12175" class="Bound">B</a> <a id="12177" href="plfa.Quantifiers.html#12177" class="Bound">C</a> <a id="12179" class="Symbol">:</a> <a id="12181" href="plfa.Quantifiers.html#12165" class="Bound">A</a> <a id="12183" class="Symbol">→</a> <a id="12185" class="PrimitiveType">Set</a><a id="12188" class="Symbol">}</a> <a id="12190" class="Symbol">→</a>
    <a id="12196" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9917" class="Function">∃[</a> <a id="12199" href="plfa.Quantifiers.html#12199" class="Bound">x</a> <a id="12201" href="plfa.Quantifiers.html#9917" class="Function">]</a> <a id="12203" class="Symbol">(</a><a id="12204" href="plfa.Quantifiers.html#12175" class="Bound">B</a> <a id="12206" href="plfa.Quantifiers.html#12199" class="Bound">x</a> <a id="12208" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="12210" href="plfa.Quantifiers.html#12177" class="Bound">C</a> <a id="12212" href="plfa.Quantifiers.html#12199" class="Bound">x</a><a id="12213" class="Symbol">)</a> <a id="12215" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5843" class="Record Operator">≃</a> <a id="12217" class="Symbol">(</a><a id="12218" href="plfa.Quantifiers.html#9917" class="Function">∃[</a> <a id="12221" href="plfa.Quantifiers.html#12221" class="Bound">x</a> <a id="12223" href="plfa.Quantifiers.html#9917" class="Function">]</a> <a id="12225" href="plfa.Quantifiers.html#12175" class="Bound">B</a> <a id="12227" href="plfa.Quantifiers.html#12221" class="Bound">x</a><a id="12228" class="Symbol">)</a> <a id="12230" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="12232" class="Symbol">(</a><a id="12233" href="plfa.Quantifiers.html#9917" class="Function">∃[</a> <a id="12236" href="plfa.Quantifiers.html#12236" class="Bound">x</a> <a id="12238" href="plfa.Quantifiers.html#9917" class="Function">]</a> <a id="12240" href="plfa.Quantifiers.html#12177" class="Bound">C</a> <a id="12242" href="plfa.Quantifiers.html#12236" class="Bound">x</a><a id="12243" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
#### Exercise `∃×-implies-×∃`
{:/}

#### 练习 `∃×-implies-×∃`

{::comment}
Show that an existential of conjunctions implies a conjunction of existentials:
{:/}

证明合取的存在命题蕴涵了存在命题的合取：

{% raw %}<pre class="Agda"><a id="12447" class="Keyword">postulate</a>
  <a id="∃×-implies-×∃"></a><a id="12459" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12459" class="Postulate">∃×-implies-×∃</a> <a id="12473" class="Symbol">:</a> <a id="12475" class="Symbol">∀</a> <a id="12477" class="Symbol">{</a><a id="12478" href="plfa.Quantifiers.html#12478" class="Bound">A</a> <a id="12480" class="Symbol">:</a> <a id="12482" class="PrimitiveType">Set</a><a id="12485" class="Symbol">}</a> <a id="12487" class="Symbol">{</a><a id="12488" href="plfa.Quantifiers.html#12488" class="Bound">B</a> <a id="12490" href="plfa.Quantifiers.html#12490" class="Bound">C</a> <a id="12492" class="Symbol">:</a> <a id="12494" href="plfa.Quantifiers.html#12478" class="Bound">A</a> <a id="12496" class="Symbol">→</a> <a id="12498" class="PrimitiveType">Set</a><a id="12501" class="Symbol">}</a> <a id="12503" class="Symbol">→</a>
    <a id="12509" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9917" class="Function">∃[</a> <a id="12512" href="plfa.Quantifiers.html#12512" class="Bound">x</a> <a id="12514" href="plfa.Quantifiers.html#9917" class="Function">]</a> <a id="12516" class="Symbol">(</a><a id="12517" href="plfa.Quantifiers.html#12488" class="Bound">B</a> <a id="12519" href="plfa.Quantifiers.html#12512" class="Bound">x</a> <a id="12521" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="12523" href="plfa.Quantifiers.html#12490" class="Bound">C</a> <a id="12525" href="plfa.Quantifiers.html#12512" class="Bound">x</a><a id="12526" class="Symbol">)</a> <a id="12528" class="Symbol">→</a> <a id="12530" class="Symbol">(</a><a id="12531" href="plfa.Quantifiers.html#9917" class="Function">∃[</a> <a id="12534" href="plfa.Quantifiers.html#12534" class="Bound">x</a> <a id="12536" href="plfa.Quantifiers.html#9917" class="Function">]</a> <a id="12538" href="plfa.Quantifiers.html#12488" class="Bound">B</a> <a id="12540" href="plfa.Quantifiers.html#12534" class="Bound">x</a><a id="12541" class="Symbol">)</a> <a id="12543" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="12545" class="Symbol">(</a><a id="12546" href="plfa.Quantifiers.html#9917" class="Function">∃[</a> <a id="12549" href="plfa.Quantifiers.html#12549" class="Bound">x</a> <a id="12551" href="plfa.Quantifiers.html#9917" class="Function">]</a> <a id="12553" href="plfa.Quantifiers.html#12490" class="Bound">C</a> <a id="12555" href="plfa.Quantifiers.html#12549" class="Bound">x</a><a id="12556" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Does the converse hold? If so, prove; if not, explain why.
{:/}

逆命题成立么？如果成立，给出证明。如果不成立，解释为什么。

{::comment}
#### Exercise `∃-⊎`
{:/}

#### 练习 `∃-⊎`

{::comment}
Let `Tri` and `B` be as in Exercise `∀-×`.
Show that `∃[ x ] B x` is isomorphic to `B aa ⊎ B bb ⊎ B cc`.
{:/}

沿用练习 `∀-×` 中的 `Tri` 和 `B` 。
证明 `∃[ x ] B x` 与 `B aa ⊎ B bb ⊎ B cc` 是同构的。

{::comment}
## An existential example
{:/}

## 一个存在量化的例子

{::comment}
Recall the definitions of `even` and `odd` from
Chapter [Relations]({{ site.baseurl }}/Relations/):
{:/}

回忆我们在 [Relations]({{ site.baseurl }}/Relations/)
章节中定义的 `even` 和 `odd`：

{% raw %}<pre class="Agda"><a id="13174" class="Keyword">data</a> <a id="even"></a><a id="13179" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13179" class="Datatype">even</a> <a id="13184" class="Symbol">:</a> <a id="13186" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="13188" class="Symbol">→</a> <a id="13190" class="PrimitiveType">Set</a>
<a id="13194" class="Keyword">data</a> <a id="odd"></a><a id="13199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13199" class="Datatype">odd</a>  <a id="13204" class="Symbol">:</a> <a id="13206" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="13208" class="Symbol">→</a> <a id="13210" class="PrimitiveType">Set</a>

<a id="13215" class="Keyword">data</a> <a id="13220" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13179" class="Datatype">even</a> <a id="13225" class="Keyword">where</a>

  <a id="even.even-zero"></a><a id="13234" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13234" class="InductiveConstructor">even-zero</a> <a id="13244" class="Symbol">:</a> <a id="13246" href="plfa.Quantifiers.html#13179" class="Datatype">even</a> <a id="13251" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>

  <a id="even.even-suc"></a><a id="13259" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13259" class="InductiveConstructor">even-suc</a> <a id="13268" class="Symbol">:</a> <a id="13270" class="Symbol">∀</a> <a id="13272" class="Symbol">{</a><a id="13273" href="plfa.Quantifiers.html#13273" class="Bound">n</a> <a id="13275" class="Symbol">:</a> <a id="13277" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="13278" class="Symbol">}</a>
    <a id="13284" class="Symbol">→</a> <a id="13286" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13199" class="Datatype">odd</a> <a id="13290" href="plfa.Quantifiers.html#13273" class="Bound">n</a>
      <a id="13298" class="Comment">------------</a>
    <a id="13315" class="Symbol">→</a> <a id="13317" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13179" class="Datatype">even</a> <a id="13322" class="Symbol">(</a><a id="13323" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13327" href="plfa.Quantifiers.html#13273" class="Bound">n</a><a id="13328" class="Symbol">)</a>

<a id="13331" class="Keyword">data</a> <a id="13336" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13199" class="Datatype">odd</a> <a id="13340" class="Keyword">where</a>
  <a id="odd.odd-suc"></a><a id="13348" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13348" class="InductiveConstructor">odd-suc</a> <a id="13356" class="Symbol">:</a> <a id="13358" class="Symbol">∀</a> <a id="13360" class="Symbol">{</a><a id="13361" href="plfa.Quantifiers.html#13361" class="Bound">n</a> <a id="13363" class="Symbol">:</a> <a id="13365" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="13366" class="Symbol">}</a>
    <a id="13372" class="Symbol">→</a> <a id="13374" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13179" class="Datatype">even</a> <a id="13379" href="plfa.Quantifiers.html#13361" class="Bound">n</a>
      <a id="13387" class="Comment">-----------</a>
    <a id="13403" class="Symbol">→</a> <a id="13405" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13199" class="Datatype">odd</a> <a id="13409" class="Symbol">(</a><a id="13410" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13414" href="plfa.Quantifiers.html#13361" class="Bound">n</a><a id="13415" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
A number is even if it is zero or the successor of an odd number, and
odd if it is the successor of an even number.
{:/}

如果一个数是 0 或者它是奇数的后继，那么这个数是偶数。如果一个数是偶数的后继，那么这个数是奇数。

{::comment}
We will show that a number is even if and only if it is twice some
other number, and odd if and only if it is one more than twice
some other number.  In other words, we will show:
{:/}

我们接下来要证明，一个数是偶数当且仅当这个数是一个数的两倍，一个数是奇数当且仅当这个数
是一个数的两倍多一。换句话说，我们要证明的是：

{::comment}
`even n`   iff   `∃[ m ] (    m * 2 ≡ n)`

`odd  n`   iff   `∃[ m ] (1 + m * 2 ≡ n)`
{:/}

`even n`   当且仅当   `∃[ m ] (    m * 2 ≡ n)`

`odd  n`   当且仅当   `∃[ m ] (1 + m * 2 ≡ n)`

{::comment}
By convention, one tends to write constant factors first and to put
the constant term in a sum last. Here we've reversed each of those
conventions, because doing so eases the proof.
{:/}

惯例来说，我们往往将常数因子写在前面、将和里的常数项写在后面。但是这里我们没有按照惯例，
而是反了过来，因为这样可以让证明更简单：

{::comment}
Here is the proof in the forward direction:
{:/}

这是向前方向的证明：

{% raw %}<pre class="Agda"><a id="even-∃"></a><a id="14410" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14410" class="Function">even-∃</a> <a id="14417" class="Symbol">:</a> <a id="14419" class="Symbol">∀</a> <a id="14421" class="Symbol">{</a><a id="14422" href="plfa.Quantifiers.html#14422" class="Bound">n</a> <a id="14424" class="Symbol">:</a> <a id="14426" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="14427" class="Symbol">}</a> <a id="14429" class="Symbol">→</a> <a id="14431" href="plfa.Quantifiers.html#13179" class="Datatype">even</a> <a id="14436" href="plfa.Quantifiers.html#14422" class="Bound">n</a> <a id="14438" class="Symbol">→</a> <a id="14440" href="plfa.Quantifiers.html#9917" class="Function">∃[</a> <a id="14443" href="plfa.Quantifiers.html#14443" class="Bound">m</a> <a id="14445" href="plfa.Quantifiers.html#9917" class="Function">]</a> <a id="14447" class="Symbol">(</a>    <a id="14452" href="plfa.Quantifiers.html#14443" class="Bound">m</a> <a id="14454" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="14456" class="Number">2</a> <a id="14458" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="14460" href="plfa.Quantifiers.html#14422" class="Bound">n</a><a id="14461" class="Symbol">)</a>
<a id="odd-∃"></a><a id="14463" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14463" class="Function">odd-∃</a>  <a id="14470" class="Symbol">:</a> <a id="14472" class="Symbol">∀</a> <a id="14474" class="Symbol">{</a><a id="14475" href="plfa.Quantifiers.html#14475" class="Bound">n</a> <a id="14477" class="Symbol">:</a> <a id="14479" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="14480" class="Symbol">}</a> <a id="14482" class="Symbol">→</a>  <a id="14485" href="plfa.Quantifiers.html#13199" class="Datatype">odd</a> <a id="14489" href="plfa.Quantifiers.html#14475" class="Bound">n</a> <a id="14491" class="Symbol">→</a> <a id="14493" href="plfa.Quantifiers.html#9917" class="Function">∃[</a> <a id="14496" href="plfa.Quantifiers.html#14496" class="Bound">m</a> <a id="14498" href="plfa.Quantifiers.html#9917" class="Function">]</a> <a id="14500" class="Symbol">(</a><a id="14501" class="Number">1</a> <a id="14503" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="14505" href="plfa.Quantifiers.html#14496" class="Bound">m</a> <a id="14507" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="14509" class="Number">2</a> <a id="14511" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="14513" href="plfa.Quantifiers.html#14475" class="Bound">n</a><a id="14514" class="Symbol">)</a>

<a id="14517" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14410" class="Function">even-∃</a> <a id="14524" href="plfa.Quantifiers.html#13234" class="InductiveConstructor">even-zero</a>                       <a id="14556" class="Symbol">=</a>  <a id="14559" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟨</a> <a id="14561" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="14566" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">,</a> <a id="14568" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="14573" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟩</a>
<a id="14575" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14410" class="Function">even-∃</a> <a id="14582" class="Symbol">(</a><a id="14583" href="plfa.Quantifiers.html#13259" class="InductiveConstructor">even-suc</a> <a id="14592" href="plfa.Quantifiers.html#14592" class="Bound">o</a><a id="14593" class="Symbol">)</a> <a id="14595" class="Keyword">with</a> <a id="14600" href="plfa.Quantifiers.html#14463" class="Function">odd-∃</a> <a id="14606" href="plfa.Quantifiers.html#14592" class="Bound">o</a>
<a id="14608" class="Symbol">...</a>                    <a id="14631" class="Symbol">|</a> <a id="14633" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6570" class="InductiveConstructor Operator">⟨</a> <a id="14635" href="plfa.Quantifiers.html#14635" class="Bound">m</a> <a id="14637" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">,</a> <a id="14639" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="14644" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟩</a>  <a id="14647" class="Symbol">=</a>  <a id="14650" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟨</a> <a id="14652" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14656" href="plfa.Quantifiers.html#14635" class="Bound">m</a> <a id="14658" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">,</a> <a id="14660" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="14665" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟩</a>

<a id="14668" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14463" class="Function">odd-∃</a>  <a id="14675" class="Symbol">(</a><a id="14676" href="plfa.Quantifiers.html#13348" class="InductiveConstructor">odd-suc</a> <a id="14684" href="plfa.Quantifiers.html#14684" class="Bound">e</a><a id="14685" class="Symbol">)</a>  <a id="14688" class="Keyword">with</a> <a id="14693" href="plfa.Quantifiers.html#14410" class="Function">even-∃</a> <a id="14700" href="plfa.Quantifiers.html#14684" class="Bound">e</a>
<a id="14702" class="Symbol">...</a>                    <a id="14725" class="Symbol">|</a> <a id="14727" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6570" class="InductiveConstructor Operator">⟨</a> <a id="14729" href="plfa.Quantifiers.html#14729" class="Bound">m</a> <a id="14731" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">,</a> <a id="14733" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="14738" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟩</a>  <a id="14741" class="Symbol">=</a>  <a id="14744" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟨</a> <a id="14746" href="plfa.Quantifiers.html#14729" class="Bound">m</a> <a id="14748" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">,</a> <a id="14750" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="14755" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟩</a>
</pre>{% endraw %}
{::comment}
We define two mutually recursive functions. Given
evidence that `n` is even or odd, we return a
number `m` and evidence that `m * 2 ≡ n` or `1 + m * 2 ≡ n`.
We induct over the evidence that `n` is even or odd:
{:/}

我们定义两个相互递归的函数。给定 `n` 是奇数或者是偶数的证明，我们返回一个数
`m`，以及 `m * 2 ≡ n` 或者 `1 + m * 2 ≡ n` 的证明。我们根据 `n` 是奇数
或者是偶数的证明进行归纳：

{::comment}
* If the number is even because it is zero, then we return a pair
consisting of zero and the evidence that twice zero is zero.

* If the number is even because it is one more than an odd number,
then we apply the induction hypothesis to give a number `m` and
evidence that `1 + m * 2 ≡ n`. We return a pair consisting of `suc m`
and evidence that `suc m * 2 ≡ suc n`, which is immediate after
substituting for `n`.

* If the number is odd because it is the successor of an even number,
then we apply the induction hypothesis to give a number `m` and
evidence that `m * 2 ≡ n`. We return a pair consisting of `suc m` and
evidence that `1 + m * 2 ≡ suc n`, which is immediate after
substituting for `n`.
{:/}

* 如果这个数是偶数，因为它是 0，那么我们返回数据对 0 ，以及 0 的两倍是 0 的证明。

* 如果这个数是偶数，因为它是比一个奇数多 1，那么我们可以使用归纳假设，来获得一个数 `m` 和
`1 + m * 2 ≡ n` 的证明。我们返回数据对 `suc m` 以及 `suc m * 2 ≡ suc n` 的证明——
我们可以直接通过替换 `n` 来得到证明。

* 如果这个数是奇数，因为它是一个偶数的后继，那么我们可以使用归纳假设，来获得一个数 `m` 和
`m * 2 ≡ n` 的证明。我们返回数据对 `suc m` 以及 `1 + m * 2 ≡ suc n` 的证明——
我们可以直接通过替换 `n` 来得到证明。

{::comment}
This completes the proof in the forward direction.
{:/}

这样，我们就完成了正方向的证明。

{::comment}
Here is the proof in the reverse direction:
{:/}

接下来是反方向的证明：

{% raw %}<pre class="Agda"><a id="∃-even"></a><a id="16307" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16307" class="Function">∃-even</a> <a id="16314" class="Symbol">:</a> <a id="16316" class="Symbol">∀</a> <a id="16318" class="Symbol">{</a><a id="16319" href="plfa.Quantifiers.html#16319" class="Bound">n</a> <a id="16321" class="Symbol">:</a> <a id="16323" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="16324" class="Symbol">}</a> <a id="16326" class="Symbol">→</a> <a id="16328" href="plfa.Quantifiers.html#9917" class="Function">∃[</a> <a id="16331" href="plfa.Quantifiers.html#16331" class="Bound">m</a> <a id="16333" href="plfa.Quantifiers.html#9917" class="Function">]</a> <a id="16335" class="Symbol">(</a>    <a id="16340" href="plfa.Quantifiers.html#16331" class="Bound">m</a> <a id="16342" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="16344" class="Number">2</a> <a id="16346" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16348" href="plfa.Quantifiers.html#16319" class="Bound">n</a><a id="16349" class="Symbol">)</a> <a id="16351" class="Symbol">→</a> <a id="16353" href="plfa.Quantifiers.html#13179" class="Datatype">even</a> <a id="16358" href="plfa.Quantifiers.html#16319" class="Bound">n</a>
<a id="∃-odd"></a><a id="16360" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16360" class="Function">∃-odd</a>  <a id="16367" class="Symbol">:</a> <a id="16369" class="Symbol">∀</a> <a id="16371" class="Symbol">{</a><a id="16372" href="plfa.Quantifiers.html#16372" class="Bound">n</a> <a id="16374" class="Symbol">:</a> <a id="16376" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="16377" class="Symbol">}</a> <a id="16379" class="Symbol">→</a> <a id="16381" href="plfa.Quantifiers.html#9917" class="Function">∃[</a> <a id="16384" href="plfa.Quantifiers.html#16384" class="Bound">m</a> <a id="16386" href="plfa.Quantifiers.html#9917" class="Function">]</a> <a id="16388" class="Symbol">(</a><a id="16389" class="Number">1</a> <a id="16391" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16393" href="plfa.Quantifiers.html#16384" class="Bound">m</a> <a id="16395" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="16397" class="Number">2</a> <a id="16399" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16401" href="plfa.Quantifiers.html#16372" class="Bound">n</a><a id="16402" class="Symbol">)</a> <a id="16404" class="Symbol">→</a>  <a id="16407" href="plfa.Quantifiers.html#13199" class="Datatype">odd</a> <a id="16411" href="plfa.Quantifiers.html#16372" class="Bound">n</a>

<a id="16414" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16307" class="Function">∃-even</a> <a id="16421" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟨</a>  <a id="16424" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="16429" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">,</a> <a id="16431" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="16436" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟩</a>  <a id="16439" class="Symbol">=</a>  <a id="16442" href="plfa.Quantifiers.html#13234" class="InductiveConstructor">even-zero</a>
<a id="16452" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16307" class="Function">∃-even</a> <a id="16459" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟨</a> <a id="16461" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16465" href="plfa.Quantifiers.html#16465" class="Bound">m</a> <a id="16467" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">,</a> <a id="16469" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="16474" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟩</a>  <a id="16477" class="Symbol">=</a>  <a id="16480" href="plfa.Quantifiers.html#13259" class="InductiveConstructor">even-suc</a> <a id="16489" class="Symbol">(</a><a id="16490" href="plfa.Quantifiers.html#16360" class="Function">∃-odd</a> <a id="16496" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟨</a> <a id="16498" href="plfa.Quantifiers.html#16465" class="Bound">m</a> <a id="16500" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">,</a> <a id="16502" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="16507" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟩</a><a id="16508" class="Symbol">)</a>

<a id="16511" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16360" class="Function">∃-odd</a>  <a id="16518" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟨</a>     <a id="16524" href="plfa.Quantifiers.html#16524" class="Bound">m</a> <a id="16526" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">,</a> <a id="16528" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="16533" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟩</a>  <a id="16536" class="Symbol">=</a>  <a id="16539" href="plfa.Quantifiers.html#13348" class="InductiveConstructor">odd-suc</a> <a id="16547" class="Symbol">(</a><a id="16548" href="plfa.Quantifiers.html#16307" class="Function">∃-even</a> <a id="16555" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟨</a> <a id="16557" href="plfa.Quantifiers.html#16524" class="Bound">m</a> <a id="16559" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">,</a> <a id="16561" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="16566" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟩</a><a id="16567" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Given a number that is twice some other number we must show it is
even, and a number that is one more than twice some other number we
must show it is odd.  We induct over the evidence of the existential,
and in the even case consider the two possibilities for the number
that is doubled:
{:/}

给定一个是另一个数两倍的数，我们需要证明这个数是偶数。给定一个是另一个数两倍多一的数，
我们需要证明这个数是奇数。我们对于存在量化的证明进行归纳。在偶数的情况，我们也需要考虑两种
一个数是另一个数两倍的情况。

{::comment}
- In the even case for `zero`, we must show `zero * 2` is even, which
follows by `even-zero`.

- In the even case for `suc n`, we must show `suc m * 2` is even.  The
inductive hypothesis tells us that `1 + m * 2` is odd, from which the
desired result follows by `even-suc`.

- In the odd case, we must show `1 + m * 2` is odd.  The inductive
hypothesis tell us that `m * 2` is even, from which the desired result
follows by `odd-suc`.
{:/}

- 在偶数是 `zero` 的情况中，我们需要证明 `zero * 2` 是偶数，由 `even-zero` 可得。

- 在偶数是 `suc n` 的情况中，我们需要证明 `suc m * 2` 是偶数。归纳假设告诉我们，
`1 + m * 2` 是奇数，那么所求证的结果由 `even-suc` 可得。

- 在偶数的情况中，我们需要证明 `1 + m * 2` 是奇数。归纳假设告诉我们，`m * 2` 是偶数，
那么所求证的结果由 `odd-suc` 可得。

{::comment}
This completes the proof in the backward direction.
{:/}

这样，我们就完成了向后方向的证明。

{::comment}
#### Exercise `∃-even-odd`
{:/}

#### 练习 `∃-even-odd`

{::comment}
How do the proofs become more difficult if we replace `m * 2` and `1 + m * 2`
by `2 * m` and `2 * m + 1`?  Rewrite the proofs of `∃-even` and `∃-odd` when
restated in this way.
{:/}

如果我们用 `2 * m` 代替 `m * 2`，`2 * m + 1` 代替 `1 + m * 2`，上述证明会变得复杂多少呢？
用这种方法来重写 `∃-even` 和 `∃-odd`。

{::comment}
{% raw %}<pre class="Agda"><a id="18137" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="18174" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
#### Exercise `∃-|-≤`
{:/}

#### 练习 `∃-|-≤`

{::comment}
Show that `y ≤ z` holds if and only if there exists a `x` such that
`x + y ≡ z`.
{:/}

证明 `y ≤ z` 当且仅当存在一个 `x` 使得 `x + y ≡ z` 成立时成立。

{::comment}
{% raw %}<pre class="Agda"><a id="18411" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="18448" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
## Existentials, Universals, and Negation
{:/}

## 存在量化、全称量化和否定

{::comment}
Negation of an existential is isomorphic to the universal
of a negation.  Considering that existentials are generalised
disjunction and universals are generalised conjunction, this
result is analogous to the one which tells us that negation
of a disjunction is isomorphic to a conjunction of negations:
{:/}

存在量化的否定与否定的全称量化是同构的。考虑到存在量化是析构的推广，全称量化是合构的推广，
这样的结果与析构的否定与否定的合构是同构的结果相似。

{% raw %}<pre class="Agda"><a id="¬∃≃∀¬"></a><a id="18942" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#18942" class="Function">¬∃≃∀¬</a> <a id="18948" class="Symbol">:</a> <a id="18950" class="Symbol">∀</a> <a id="18952" class="Symbol">{</a><a id="18953" href="plfa.Quantifiers.html#18953" class="Bound">A</a> <a id="18955" class="Symbol">:</a> <a id="18957" class="PrimitiveType">Set</a><a id="18960" class="Symbol">}</a> <a id="18962" class="Symbol">{</a><a id="18963" href="plfa.Quantifiers.html#18963" class="Bound">B</a> <a id="18965" class="Symbol">:</a> <a id="18967" href="plfa.Quantifiers.html#18953" class="Bound">A</a> <a id="18969" class="Symbol">→</a> <a id="18971" class="PrimitiveType">Set</a><a id="18974" class="Symbol">}</a>
  <a id="18978" class="Symbol">→</a> <a id="18980" class="Symbol">(</a><a id="18981" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="18983" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9917" class="Function">∃[</a> <a id="18986" href="plfa.Quantifiers.html#18986" class="Bound">x</a> <a id="18988" href="plfa.Quantifiers.html#9917" class="Function">]</a> <a id="18990" href="plfa.Quantifiers.html#18963" class="Bound">B</a> <a id="18992" href="plfa.Quantifiers.html#18986" class="Bound">x</a><a id="18993" class="Symbol">)</a> <a id="18995" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5843" class="Record Operator">≃</a> <a id="18997" class="Symbol">∀</a> <a id="18999" href="plfa.Quantifiers.html#18999" class="Bound">x</a> <a id="19001" class="Symbol">→</a> <a id="19003" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="19005" href="plfa.Quantifiers.html#18963" class="Bound">B</a> <a id="19007" href="plfa.Quantifiers.html#18999" class="Bound">x</a>
<a id="19009" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#18942" class="Function">¬∃≃∀¬</a> <a id="19015" class="Symbol">=</a>
  <a id="19019" class="Keyword">record</a>
    <a id="19030" class="Symbol">{</a> <a id="19032" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5883" class="Field">to</a>      <a id="19040" class="Symbol">=</a>  <a id="19043" class="Symbol">λ{</a> <a id="19046" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19046" class="Bound">¬∃xy</a> <a id="19051" href="plfa.Quantifiers.html#19051" class="Bound">x</a> <a id="19053" href="plfa.Quantifiers.html#19053" class="Bound">y</a> <a id="19055" class="Symbol">→</a> <a id="19057" href="plfa.Quantifiers.html#19046" class="Bound">¬∃xy</a> <a id="19062" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟨</a> <a id="19064" href="plfa.Quantifiers.html#19051" class="Bound">x</a> <a id="19066" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">,</a> <a id="19068" href="plfa.Quantifiers.html#19053" class="Bound">y</a> <a id="19070" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟩</a> <a id="19072" class="Symbol">}</a>
    <a id="19078" class="Symbol">;</a> <a id="19080" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5900" class="Field">from</a>    <a id="19088" class="Symbol">=</a>  <a id="19091" class="Symbol">λ{</a> <a id="19094" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19094" class="Bound">∀¬xy</a> <a id="19099" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟨</a> <a id="19101" href="plfa.Quantifiers.html#19101" class="Bound">x</a> <a id="19103" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">,</a> <a id="19105" href="plfa.Quantifiers.html#19105" class="Bound">y</a> <a id="19107" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟩</a> <a id="19109" class="Symbol">→</a> <a id="19111" href="plfa.Quantifiers.html#19094" class="Bound">∀¬xy</a> <a id="19116" href="plfa.Quantifiers.html#19101" class="Bound">x</a> <a id="19118" href="plfa.Quantifiers.html#19105" class="Bound">y</a> <a id="19120" class="Symbol">}</a>
    <a id="19126" class="Symbol">;</a> <a id="19128" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5917" class="Field">from∘to</a> <a id="19136" class="Symbol">=</a>  <a id="19139" class="Symbol">λ{</a> <a id="19142" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19142" class="Bound">¬∃xy</a> <a id="19147" class="Symbol">→</a> <a id="19149" href="plfa.Isomorphism.html#3758" class="Postulate">extensionality</a> <a id="19164" class="Symbol">λ{</a> <a id="19167" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟨</a> <a id="19169" href="plfa.Quantifiers.html#19169" class="Bound">x</a> <a id="19171" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">,</a> <a id="19173" href="plfa.Quantifiers.html#19173" class="Bound">y</a> <a id="19175" href="plfa.Quantifiers.html#6570" class="InductiveConstructor Operator">⟩</a> <a id="19177" class="Symbol">→</a> <a id="19179" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="19184" class="Symbol">}</a> <a id="19186" class="Symbol">}</a>
    <a id="19192" class="Symbol">;</a> <a id="19194" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5959" class="Field">to∘from</a> <a id="19202" class="Symbol">=</a>  <a id="19205" class="Symbol">λ{</a> <a id="19208" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19208" class="Bound">∀¬xy</a> <a id="19213" class="Symbol">→</a> <a id="19215" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="19220" class="Symbol">}</a>
    <a id="19226" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
In the `to` direction, we are given a value `¬∃xy` of type
`¬ ∃[ x ] B x`, and need to show that given a value
`x` that `¬ B x` follows, in other words, from
a value `y` of type `B x` we can derive false.  Combining
`x` and `y` gives us a value `⟨ x , y ⟩` of type `∃[ x ] B x`,
and applying `¬∃xy` to that yields a contradiction.
{:/}

在 `to` 的方向，给定了一个 `¬ ∃[ x ] B x` 类型的值 `¬∃xy`，需要证明给定一个 `x` 的值，
可以推导出 `¬ B x`。换句话说，给定一个 `B x` 类型的值 `y`，我们可以推导出假。将 `x` 和 `y`
合并起来我们就得到了 `∃[ x ] B x` 类型的值 `⟨ x , y ⟩`，对其使用 `¬∃xy` 即可获得矛盾。

{::comment}
In the `from` direction, we are given a value `∀¬xy` of type
`∀ x → ¬ B x`, and need to show that from a value `⟨ x , y ⟩`
of type `∃[ x ] B x` we can derive false.  Applying `∀¬xy`
to `x` gives a value of type `¬ B x`, and applying that to `y` yields
a contradiction.
{:/}

在 `from` 的方向，给定了一个 `∀ x → ¬ B x` 类型的值 `∀¬xy`，需要证明从一个类型为
`∃[ x ] B x` 类型的值 `⟨ x , y ⟩` ，我们可以推导出假。将 `∀¬xy` 使用于 `x` 之上，
可以得到类型为 `¬ B x` 的值，对其使用 `y` 即可获得矛盾。

{::comment}
The two inverse proofs are straightforward, where one direction
requires extensionality.
{:/}

两个逆的证明很直接，其中有一个方向需要外延性。

{::comment}
#### Exercise `∃¬-implies-¬∀` (recommended)
{:/}

#### 练习 `∃¬-implies-¬∀` （推荐）

{::comment}
Show that existential of a negation implies negation of a universal:
{:/}

证明否定的存在量化蕴涵了全称量化的否定：

{% raw %}<pre class="Agda"><a id="20543" class="Keyword">postulate</a>
  <a id="∃¬-implies-¬∀"></a><a id="20555" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#20555" class="Postulate">∃¬-implies-¬∀</a> <a id="20569" class="Symbol">:</a> <a id="20571" class="Symbol">∀</a> <a id="20573" class="Symbol">{</a><a id="20574" href="plfa.Quantifiers.html#20574" class="Bound">A</a> <a id="20576" class="Symbol">:</a> <a id="20578" class="PrimitiveType">Set</a><a id="20581" class="Symbol">}</a> <a id="20583" class="Symbol">{</a><a id="20584" href="plfa.Quantifiers.html#20584" class="Bound">B</a> <a id="20586" class="Symbol">:</a> <a id="20588" href="plfa.Quantifiers.html#20574" class="Bound">A</a> <a id="20590" class="Symbol">→</a> <a id="20592" class="PrimitiveType">Set</a><a id="20595" class="Symbol">}</a>
    <a id="20601" class="Symbol">→</a> <a id="20603" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9917" class="Function">∃[</a> <a id="20606" href="plfa.Quantifiers.html#20606" class="Bound">x</a> <a id="20608" href="plfa.Quantifiers.html#9917" class="Function">]</a> <a id="20610" class="Symbol">(</a><a id="20611" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="20613" href="plfa.Quantifiers.html#20584" class="Bound">B</a> <a id="20615" href="plfa.Quantifiers.html#20606" class="Bound">x</a><a id="20616" class="Symbol">)</a>
      <a id="20624" class="Comment">--------------</a>
    <a id="20643" class="Symbol">→</a> <a id="20645" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="20647" class="Symbol">(∀</a> <a id="20650" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#20650" class="Bound">x</a> <a id="20652" class="Symbol">→</a> <a id="20654" href="plfa.Quantifiers.html#20584" class="Bound">B</a> <a id="20656" href="plfa.Quantifiers.html#20650" class="Bound">x</a><a id="20657" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Does the converse hold? If so, prove; if not, explain why.
{:/}

逆命题成立么？如果成立，给出证明。如果不成立，解释为什么。

{::comment}
#### Exercise `Bin-isomorphism` (stretch) {#Bin-isomorphism}
{:/}

#### 练习 `Bin-isomorphism` （延伸） {#Bin-isomorphism}

{::comment}
Recall that Exercises
[Bin]({{ site.baseurl }}/Naturals/#Bin),
[Bin-laws]({{ site.baseurl }}/Induction/#Bin-laws), and
[Bin-predicates]({{ site.baseurl }}/Relations/#Bin-predicates)
define a datatype of bitstrings representing natural numbers:
{:/}

回忆在练习 [Bin][plfa.Naturals#Bin]、
[Bin-laws][plfa.Induction#Bin-laws] 和
[Bin-predicates][plfa.Relations#Bin-predicates] 中，
我们定义了比特串的数据类型来表示自然数：

{% raw %}<pre class="Agda"><a id="21311" class="Keyword">data</a> <a id="Bin"></a><a id="21316" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#21316" class="Datatype">Bin</a> <a id="21320" class="Symbol">:</a> <a id="21322" class="PrimitiveType">Set</a> <a id="21326" class="Keyword">where</a>
  <a id="Bin.nil"></a><a id="21334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#21334" class="InductiveConstructor">nil</a> <a id="21338" class="Symbol">:</a> <a id="21340" href="plfa.Quantifiers.html#21316" class="Datatype">Bin</a>
  <a id="Bin.x0_"></a><a id="21346" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#21346" class="InductiveConstructor Operator">x0_</a> <a id="21350" class="Symbol">:</a> <a id="21352" href="plfa.Quantifiers.html#21316" class="Datatype">Bin</a> <a id="21356" class="Symbol">→</a> <a id="21358" href="plfa.Quantifiers.html#21316" class="Datatype">Bin</a>
  <a id="Bin.x1_"></a><a id="21364" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#21364" class="InductiveConstructor Operator">x1_</a> <a id="21368" class="Symbol">:</a> <a id="21370" href="plfa.Quantifiers.html#21316" class="Datatype">Bin</a> <a id="21374" class="Symbol">→</a> <a id="21376" href="plfa.Quantifiers.html#21316" class="Datatype">Bin</a>
</pre>{% endraw %}
{::comment}
And ask you to define the following functions and predicates:
{:/}

并要求你来定义下列函数和谓词：

    to   : ℕ → Bin
    from : Bin → ℕ
    Can  : Bin → Set

{::comment}
And to establish the following properties:
{:/}

以及证明下列性质：

    from (to n) ≡ n

    ----------
    Can (to n)

    Can x
    ---------------
    to (from x) ≡ x

{::comment}
Using the above, establish that there is an isomorphism between `ℕ` and
`∃[ x ](Can x)`.
{:/}

使用上述，证明 `ℕ` 与 `∃[ x ](Can x)` 之间存在同构。

{::comment}
{% raw %}<pre class="Agda"><a id="21879" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="21916" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
## Standard library
{:/}

## 标准库

{::comment}
Definitions similar to those in this chapter can be found in the standard library:
{:/}

标准库中可以找到与本章节中相似的定义：

{% raw %}<pre class="Agda"><a id="22106" class="Keyword">import</a> <a id="22113" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="22126" class="Keyword">using</a> <a id="22132" class="Symbol">(</a><a id="22133" href="Agda.Builtin.Sigma.html#139" class="Record">Σ</a><a id="22134" class="Symbol">;</a> <a id="22136" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a><a id="22139" class="Symbol">;</a> <a id="22141" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1364" class="Function">∃</a><a id="22142" class="Symbol">;</a> <a id="22144" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#911" class="Function">Σ-syntax</a><a id="22152" class="Symbol">;</a> <a id="22154" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃-syntax</a><a id="22162" class="Symbol">)</a>
</pre>{% endraw %}

## Unicode

{::comment}
This chapter uses the following unicode:

    Π  U+03A0  GREEK CAPITAL LETTER PI (\Pi)
    Σ  U+03A3  GREEK CAPITAL LETTER SIGMA (\Sigma)
    ∃  U+2203  THERE EXISTS (\ex, \exists)

{:/}

本章节使用下列 Unicode：

    Π  U+03A0  希腊大写字母 PI (\Pi)
    Σ  U+03A3  希腊大写字母 SIGMA (\Sigma)
    ∃  U+2203  存在 (\ex, \exists)
