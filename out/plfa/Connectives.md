---
src       : "src/plfa/Connectives.lagda.md"
title     : "Connectives: 合取、析取与蕴涵"
layout    : page
prev      : /Isomorphism/
permalink : /Connectives/
next      : /Negation/
translators : ["Fangyi Zhou"]
progress  : 100
---

{% raw %}<pre class="Agda"><a id="188" class="Keyword">module</a> <a id="195" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}" class="Module">plfa.Connectives</a> <a id="212" class="Keyword">where</a>
</pre>{% endraw %}
<!-- The ⊥ ⊎ A ≅ A exercise requires a (inj₁ ()) pattern,
     which the reader will not have seen. Restore this
     exercise, and possibly also associativity? Take the
     exercises from the final sections on distributivity
     and exponentials? -->

{::comment}
This chapter introduces the basic logical connectives, by observing a
correspondence between connectives of logic and data types, a
principle known as _Propositions as Types_:
{:/}

本章节介绍基础的逻辑运算符。我们使用逻辑运算符与数据类型之间的对应关系，
即*命题即类型*原理（Propositions as Types）。

{::comment}
  * _conjunction_ is _product_,
  * _disjunction_ is _sum_,
  * _true_ is _unit type_,
  * _false_ is _empty type_,
  * _implication_ is _function space_.
{:/}

  * *合取*（Conjunction）即是*积*（Product）
  * *析取*（Disjunction）即是*和*（Sum）
  * *真*（True）即是*单元类型*（Unit Type）
  * *假*（False）即是*空类型*（Empty Type）
  * *蕴涵*（Implication）即是*函数空间*（Function Space）

{::comment}
## Imports
{:/}

## 导入

{% raw %}<pre class="Agda"><a id="1140" class="Keyword">import</a> <a id="1147" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="1185" class="Symbol">as</a> <a id="1188" class="Module">Eq</a>
<a id="1191" class="Keyword">open</a> <a id="1196" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="1199" class="Keyword">using</a> <a id="1205" class="Symbol">(</a><a id="1206" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="1209" class="Symbol">;</a> <a id="1211" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="1215" class="Symbol">)</a>
<a id="1217" class="Keyword">open</a> <a id="1222" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2499" class="Module">Eq.≡-Reasoning</a>
<a id="1237" class="Keyword">open</a> <a id="1242" class="Keyword">import</a> <a id="1249" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="1258" class="Keyword">using</a> <a id="1264" class="Symbol">(</a><a id="1265" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1266" class="Symbol">)</a>
<a id="1268" class="Keyword">open</a> <a id="1273" class="Keyword">import</a> <a id="1280" href="https://agda.github.io/agda-stdlib/v1.1/Function.html" class="Module">Function</a> <a id="1289" class="Keyword">using</a> <a id="1295" class="Symbol">(</a><a id="1296" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">_∘_</a><a id="1299" class="Symbol">)</a>
<a id="1301" class="Keyword">open</a> <a id="1306" class="Keyword">import</a> <a id="1313" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}" class="Module">plfa.Isomorphism</a> <a id="1330" class="Keyword">using</a> <a id="1336" class="Symbol">(</a><a id="1337" href="plfa.Isomorphism.html#5843" class="Record Operator">_≃_</a><a id="1340" class="Symbol">;</a> <a id="1342" href="plfa.Isomorphism.html#11919" class="Record Operator">_≲_</a><a id="1345" class="Symbol">;</a> <a id="1347" href="plfa.Isomorphism.html#3758" class="Postulate">extensionality</a><a id="1361" class="Symbol">)</a>
<a id="1363" class="Keyword">open</a> <a id="1368" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10987" class="Module">plfa.Isomorphism.≃-Reasoning</a>
</pre>{% endraw %}

{::comment}
## Conjunction is product
{:/}

## 合取即是积

{::comment}
Given two propositions `A` and `B`, the conjunction `A × B` holds
if both `A` holds and `B` holds.  We formalise this idea by
declaring a suitable inductive type:
{:/}

给定两个命题 `A` 和 `B`，其合取 `A × B` 成立当 `A` 成立和 `B` 成立。
我们将这样的概念形式化，使用如下的归纳类型：

{% raw %}<pre class="Agda"><a id="1715" class="Keyword">data</a> <a id="_×_"></a><a id="1720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1720" class="Datatype Operator">_×_</a> <a id="1724" class="Symbol">(</a><a id="1725" href="plfa.Connectives.html#1725" class="Bound">A</a> <a id="1727" href="plfa.Connectives.html#1727" class="Bound">B</a> <a id="1729" class="Symbol">:</a> <a id="1731" class="PrimitiveType">Set</a><a id="1734" class="Symbol">)</a> <a id="1736" class="Symbol">:</a> <a id="1738" class="PrimitiveType">Set</a> <a id="1742" class="Keyword">where</a>

  <a id="_×_.⟨_,_⟩"></a><a id="1751" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨_,_⟩</a> <a id="1757" class="Symbol">:</a>
      <a id="1765" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1725" class="Bound">A</a>
    <a id="1771" class="Symbol">→</a> <a id="1773" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1727" class="Bound">B</a>
      <a id="1781" class="Comment">-----</a>
    <a id="1791" class="Symbol">→</a> <a id="1793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1725" class="Bound">A</a> <a id="1795" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="1797" href="plfa.Connectives.html#1727" class="Bound">B</a>
</pre>{% endraw %}
{::comment}
Evidence that `A × B` holds is of the form `⟨ M , N ⟩`, where `M`
provides evidence that `A` holds and `N` provides evidence that `B`
holds.
{:/}

`A × B` 成立的证明由 `⟨ M , N ⟩` 的形式表现，其中 `M` 是 `A` 成立的证明，
`N` 是 `B` 成立的证明。

{::comment}
Given evidence that `A × B` holds, we can conclude that either
`A` holds or `B` holds:
{:/}

给定 `A × B` 成立的证明，我们可以得出 `A` 成立或者 `B` 成立。

{% raw %}<pre class="Agda"><a id="proj₁"></a><a id="2185" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#2185" class="Function">proj₁</a> <a id="2191" class="Symbol">:</a> <a id="2193" class="Symbol">∀</a> <a id="2195" class="Symbol">{</a><a id="2196" href="plfa.Connectives.html#2196" class="Bound">A</a> <a id="2198" href="plfa.Connectives.html#2198" class="Bound">B</a> <a id="2200" class="Symbol">:</a> <a id="2202" class="PrimitiveType">Set</a><a id="2205" class="Symbol">}</a>
  <a id="2209" class="Symbol">→</a> <a id="2211" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#2196" class="Bound">A</a> <a id="2213" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="2215" href="plfa.Connectives.html#2198" class="Bound">B</a>
    <a id="2221" class="Comment">-----</a>
  <a id="2229" class="Symbol">→</a> <a id="2231" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#2196" class="Bound">A</a>
<a id="2233" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#2185" class="Function">proj₁</a> <a id="2239" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="2241" href="plfa.Connectives.html#2241" class="Bound">x</a> <a id="2243" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="2245" href="plfa.Connectives.html#2245" class="Bound">y</a> <a id="2247" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="2249" class="Symbol">=</a> <a id="2251" href="plfa.Connectives.html#2241" class="Bound">x</a>

<a id="proj₂"></a><a id="2254" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#2254" class="Function">proj₂</a> <a id="2260" class="Symbol">:</a> <a id="2262" class="Symbol">∀</a> <a id="2264" class="Symbol">{</a><a id="2265" href="plfa.Connectives.html#2265" class="Bound">A</a> <a id="2267" href="plfa.Connectives.html#2267" class="Bound">B</a> <a id="2269" class="Symbol">:</a> <a id="2271" class="PrimitiveType">Set</a><a id="2274" class="Symbol">}</a>
  <a id="2278" class="Symbol">→</a> <a id="2280" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#2265" class="Bound">A</a> <a id="2282" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="2284" href="plfa.Connectives.html#2267" class="Bound">B</a>
    <a id="2290" class="Comment">-----</a>
  <a id="2298" class="Symbol">→</a> <a id="2300" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#2267" class="Bound">B</a>
<a id="2302" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#2254" class="Function">proj₂</a> <a id="2308" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="2310" href="plfa.Connectives.html#2310" class="Bound">x</a> <a id="2312" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="2314" href="plfa.Connectives.html#2314" class="Bound">y</a> <a id="2316" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="2318" class="Symbol">=</a> <a id="2320" href="plfa.Connectives.html#2314" class="Bound">y</a>
</pre>{% endraw %}
{::comment}
If `L` provides evidence that `A × B` holds, then `proj₁ L` provides evidence
that `A` holds, and `proj₂ L` provides evidence that `B` holds.
{:/}

如果 `L` 是 `A × B` 成立的证据, 那么 `proj₁ L` 是 `A` 成立的证据，
`proj₂ L` 是 `B` 成立的证据。

{::comment}
Equivalently, we could also declare conjunction as a record type:
{:/}

等价地，我们亦可以将合取定义为一个记录类型：

{% raw %}<pre class="Agda"><a id="2673" class="Keyword">record</a> <a id="_×′_"></a><a id="2680" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#2680" class="Record Operator">_×′_</a> <a id="2685" class="Symbol">(</a><a id="2686" href="plfa.Connectives.html#2686" class="Bound">A</a> <a id="2688" href="plfa.Connectives.html#2688" class="Bound">B</a> <a id="2690" class="Symbol">:</a> <a id="2692" class="PrimitiveType">Set</a><a id="2695" class="Symbol">)</a> <a id="2697" class="Symbol">:</a> <a id="2699" class="PrimitiveType">Set</a> <a id="2703" class="Keyword">where</a>
  <a id="2711" class="Keyword">field</a>
    <a id="_×′_.proj₁′"></a><a id="2721" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#2721" class="Field">proj₁′</a> <a id="2728" class="Symbol">:</a> <a id="2730" href="plfa.Connectives.html#2686" class="Bound">A</a>
    <a id="_×′_.proj₂′"></a><a id="2736" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#2736" class="Field">proj₂′</a> <a id="2743" class="Symbol">:</a> <a id="2745" href="plfa.Connectives.html#2688" class="Bound">B</a>
<a id="2747" class="Keyword">open</a> <a id="2752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#2680" class="Module Operator">_×′_</a>
</pre>{% endraw %}
{::comment}
Here record construction
{:/}

在这里，记录的构造

    record
      { proj₁′ = M
      ; proj₂′ = N
      }

{::comment}
corresponds to the term
{:/}

对应

    ⟨ M , N ⟩

{::comment}
where `M` is a term of type `A` and `N` is a term of type `B`.
{:/}

其中 `M` 是 `A` 类型的项，`N` 是 `B` 类型的项。

{::comment}
When `⟨_,_⟩` appears in a term on the right-hand side of an equation
we refer to it as a _constructor_, and when it appears in a pattern on
the left-hand side of an equation we refer to it as a _destructor_.
We may also refer to `proj₁` and `proj₂` as destructors, since they
play a similar role.
{:/}

当 `⟨_,_⟩` 在等式右手边的项中出现的时候，我们将其称作*构造子*（Constructor），
当它出现在等式左边时，我们将其称作*析构器*（Destructor）。我们亦可将 `proj₁` 和 `proj₂`
称作析构器，因为它们起到相似的效果。

{::comment}
Other terminology refers to `⟨_,_⟩` as _introducing_ a conjunction, and
to `proj₁` and `proj₂` as _eliminating_ a conjunction; indeed, the
former is sometimes given the name `×-I` and the latter two the names
`×-E₁` and `×-E₂`.  As we read the rules from top to bottom,
introduction and elimination do what they say on the tin: the first
_introduces_ a formula for the connective, which appears in the
conclusion but not in the hypotheses; the second _eliminates_ a
formula for the connective, which appears in a hypothesis but not in
the conclusion. An introduction rule describes under what conditions
we say the connective holds---how to _define_ the connective. An
elimination rule describes what we may conclude when the connective
holds---how to _use_ the connective.
{:/}

其他的术语将 `⟨_,_⟩` 称作*引入*（Introduce）合取，将 `proj₁` 和 `proj₂` 称作*消去*（Eliminate）合取。
前者亦记作 `×-I`，后者 `×-E₁` 和 `×-E₂`。如果我们从上到下来阅读这些规则，引入和消去
正如其名字所说的那样：第一条*引入*一个运算符，所以运算符出现在结论中，而不是假设中；
第二条*消去*一个带有运算符的式子，而运算符出现在假设中，而不是结论中。引入规则描述了
运算符在什么情况下成立——即怎么样*定义*一个运算符。消去规则描述了运算符成立时，可以得出
什么样的结论——即怎么样*使用*一个运算符。

{::comment}
(The paragraph above was adopted from "Propositions as Types", Philip Wadler,
_Communications of the ACM_, December 2015.)
{:/}

（上面一段内容由此处改编得来：*Propositions as Types*，作者：Philip Wadler，
发表于 《ACM 通讯》，2015 年 9 月）

{::comment}
In this case, applying each destructor and reassembling the results with the
constructor is the identity over products:
{:/}

在这样的情况下，先使用析构器，再使用构造子将结果重组，得到还是原来的积。

{% raw %}<pre class="Agda"><a id="η-×"></a><a id="4979" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#4979" class="Function">η-×</a> <a id="4983" class="Symbol">:</a> <a id="4985" class="Symbol">∀</a> <a id="4987" class="Symbol">{</a><a id="4988" href="plfa.Connectives.html#4988" class="Bound">A</a> <a id="4990" href="plfa.Connectives.html#4990" class="Bound">B</a> <a id="4992" class="Symbol">:</a> <a id="4994" class="PrimitiveType">Set</a><a id="4997" class="Symbol">}</a> <a id="4999" class="Symbol">(</a><a id="5000" href="plfa.Connectives.html#5000" class="Bound">w</a> <a id="5002" class="Symbol">:</a> <a id="5004" href="plfa.Connectives.html#4988" class="Bound">A</a> <a id="5006" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="5008" href="plfa.Connectives.html#4990" class="Bound">B</a><a id="5009" class="Symbol">)</a> <a id="5011" class="Symbol">→</a> <a id="5013" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="5015" href="plfa.Connectives.html#2185" class="Function">proj₁</a> <a id="5021" href="plfa.Connectives.html#5000" class="Bound">w</a> <a id="5023" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="5025" href="plfa.Connectives.html#2254" class="Function">proj₂</a> <a id="5031" href="plfa.Connectives.html#5000" class="Bound">w</a> <a id="5033" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="5035" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5037" href="plfa.Connectives.html#5000" class="Bound">w</a>
<a id="5039" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#4979" class="Function">η-×</a> <a id="5043" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="5045" href="plfa.Connectives.html#5045" class="Bound">x</a> <a id="5047" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="5049" href="plfa.Connectives.html#5049" class="Bound">y</a> <a id="5051" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="5053" class="Symbol">=</a> <a id="5055" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
The pattern matching on the left-hand side is essential, since
replacing `w` by `⟨ x , y ⟩` allows both sides of the
propositional equality to simplify to the same term.
{:/}

左手边的模式匹配是必要的。用 `⟨ x , y ⟩` 来替换 `w` 让等式的两边可以化简成相同的项。

{::comment}
We set the precedence of conjunction so that it binds less
tightly than anything save disjunction:
{:/}

我们设置合取的优先级，使它与除了析取之外结合的都不紧密：

{% raw %}<pre class="Agda"><a id="5457" class="Keyword">infixr</a> <a id="5464" class="Number">2</a> <a id="5466" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1720" class="Datatype Operator">_×_</a>
</pre>{% endraw %}
{::comment}
Thus, `m ≤ n × n ≤ p` parses as `(m ≤ n) × (n ≤ p)`.
{:/}

因此，`m ≤ n × n ≤ p` 解析为 `(m ≤ n) × (n ≤ p)`。

{::comment}
Given two types `A` and `B`, we refer to `A × B` as the
_product_ of `A` and `B`.  In set theory, it is also sometimes
called the _Cartesian product_, and in computing it corresponds
to a _record_ type. Among other reasons for
calling it the product, note that if type `A` has `m`
distinct members, and type `B` has `n` distinct members,
then the type `A × B` has `m * n` distinct members.
For instance, consider a type `Bool` with two members, and
a type `Tri` with three members:
{:/}

给定两个类型 `A` 和 `B`，我们将 `A × B` 称为 `A` 与 `B` 的*积*。
在集合论中它也被称作*笛卡尔积*（Cartesian Product），在计算机科学中它对应*记录*类型。
如果类型 `A` 有 `m` 个不同的成员，类型 `B` 有 `n` 个不同的成员，
那么类型 `A × B` 有 `m * n` 个不同的成员。这也是它被称为积的原因之一。
例如，考虑有两个成员的 `Bool` 类型，和有三个成员的 `Tri` 类型：

{% raw %}<pre class="Agda"><a id="6326" class="Keyword">data</a> <a id="Bool"></a><a id="6331" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6331" class="Datatype">Bool</a> <a id="6336" class="Symbol">:</a> <a id="6338" class="PrimitiveType">Set</a> <a id="6342" class="Keyword">where</a>
  <a id="Bool.true"></a><a id="6350" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6350" class="InductiveConstructor">true</a>  <a id="6356" class="Symbol">:</a> <a id="6358" href="plfa.Connectives.html#6331" class="Datatype">Bool</a>
  <a id="Bool.false"></a><a id="6365" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6365" class="InductiveConstructor">false</a> <a id="6371" class="Symbol">:</a> <a id="6373" href="plfa.Connectives.html#6331" class="Datatype">Bool</a>

<a id="6379" class="Keyword">data</a> <a id="Tri"></a><a id="6384" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6384" class="Datatype">Tri</a> <a id="6388" class="Symbol">:</a> <a id="6390" class="PrimitiveType">Set</a> <a id="6394" class="Keyword">where</a>
  <a id="Tri.aa"></a><a id="6402" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6402" class="InductiveConstructor">aa</a> <a id="6405" class="Symbol">:</a> <a id="6407" href="plfa.Connectives.html#6384" class="Datatype">Tri</a>
  <a id="Tri.bb"></a><a id="6413" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6413" class="InductiveConstructor">bb</a> <a id="6416" class="Symbol">:</a> <a id="6418" href="plfa.Connectives.html#6384" class="Datatype">Tri</a>
  <a id="Tri.cc"></a><a id="6424" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6424" class="InductiveConstructor">cc</a> <a id="6427" class="Symbol">:</a> <a id="6429" href="plfa.Connectives.html#6384" class="Datatype">Tri</a>
</pre>{% endraw %}
{::comment}
Then the type `Bool × Tri` has six members:
{:/}

那么，`Bool × Tri` 类型有如下的六个成员：

    ⟨ true  , aa ⟩    ⟨ true  , bb ⟩    ⟨ true ,  cc ⟩
    ⟨ false , aa ⟩    ⟨ false , bb ⟩    ⟨ false , cc ⟩

{::comment}
For example, the following function enumerates all
possible arguments of type `Bool × Tri`:
{:/}

下面的函数枚举了所有类型为 `Bool × Tri` 的参数：

{% raw %}<pre class="Agda"><a id="×-count"></a><a id="6787" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6787" class="Function">×-count</a> <a id="6795" class="Symbol">:</a> <a id="6797" href="plfa.Connectives.html#6331" class="Datatype">Bool</a> <a id="6802" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="6804" href="plfa.Connectives.html#6384" class="Datatype">Tri</a> <a id="6808" class="Symbol">→</a> <a id="6810" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="6812" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6787" class="Function">×-count</a> <a id="6820" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="6822" href="plfa.Connectives.html#6350" class="InductiveConstructor">true</a>  <a id="6828" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="6830" href="plfa.Connectives.html#6402" class="InductiveConstructor">aa</a> <a id="6833" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a>  <a id="6836" class="Symbol">=</a>  <a id="6839" class="Number">1</a>
<a id="6841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6787" class="Function">×-count</a> <a id="6849" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="6851" href="plfa.Connectives.html#6350" class="InductiveConstructor">true</a>  <a id="6857" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="6859" href="plfa.Connectives.html#6413" class="InductiveConstructor">bb</a> <a id="6862" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a>  <a id="6865" class="Symbol">=</a>  <a id="6868" class="Number">2</a>
<a id="6870" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6787" class="Function">×-count</a> <a id="6878" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="6880" href="plfa.Connectives.html#6350" class="InductiveConstructor">true</a>  <a id="6886" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="6888" href="plfa.Connectives.html#6424" class="InductiveConstructor">cc</a> <a id="6891" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a>  <a id="6894" class="Symbol">=</a>  <a id="6897" class="Number">3</a>
<a id="6899" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6787" class="Function">×-count</a> <a id="6907" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="6909" href="plfa.Connectives.html#6365" class="InductiveConstructor">false</a> <a id="6915" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="6917" href="plfa.Connectives.html#6402" class="InductiveConstructor">aa</a> <a id="6920" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a>  <a id="6923" class="Symbol">=</a>  <a id="6926" class="Number">4</a>
<a id="6928" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6787" class="Function">×-count</a> <a id="6936" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="6938" href="plfa.Connectives.html#6365" class="InductiveConstructor">false</a> <a id="6944" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="6946" href="plfa.Connectives.html#6413" class="InductiveConstructor">bb</a> <a id="6949" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a>  <a id="6952" class="Symbol">=</a>  <a id="6955" class="Number">5</a>
<a id="6957" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6787" class="Function">×-count</a> <a id="6965" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="6967" href="plfa.Connectives.html#6365" class="InductiveConstructor">false</a> <a id="6973" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="6975" href="plfa.Connectives.html#6424" class="InductiveConstructor">cc</a> <a id="6978" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a>  <a id="6981" class="Symbol">=</a>  <a id="6984" class="Number">6</a>
</pre>{% endraw %}
{::comment}
Product on types also shares a property with product on numbers in
that there is a sense in which it is commutative and associative.  In
particular, product is commutative and associative _up to
isomorphism_.
{:/}

类型上的积与数的积有相似的性质——它们满足交换律和结合律。
更确切地说，积在*在同构意义下*满足交换律和结合率。

{::comment}
For commutativity, the `to` function swaps a pair, taking `⟨ x , y ⟩` to
`⟨ y , x ⟩`, and the `from` function does the same (up to renaming).
Instantiating the patterns correctly in `from∘to` and `to∘from` is essential.
Replacing the definition of `from∘to` by `λ w → refl` will not work;
and similarly for `to∘from`:
{:/}

对于交换律，`to` 函数将有序对交换，将 `⟨ x , y ⟩` 变为 `⟨ y , x ⟩`，`from`
函数亦是如此（忽略命名）。
在 `from∘to` 和 `to∘from` 中正确地实例化要匹配的模式是很重要的。
使用 `λ w → refl` 作为 `from∘to` 的定义是不可行的，`to∘from` 同理。

{% raw %}<pre class="Agda"><a id="×-comm"></a><a id="7783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#7783" class="Function">×-comm</a> <a id="7790" class="Symbol">:</a> <a id="7792" class="Symbol">∀</a> <a id="7794" class="Symbol">{</a><a id="7795" href="plfa.Connectives.html#7795" class="Bound">A</a> <a id="7797" href="plfa.Connectives.html#7797" class="Bound">B</a> <a id="7799" class="Symbol">:</a> <a id="7801" class="PrimitiveType">Set</a><a id="7804" class="Symbol">}</a> <a id="7806" class="Symbol">→</a> <a id="7808" href="plfa.Connectives.html#7795" class="Bound">A</a> <a id="7810" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="7812" href="plfa.Connectives.html#7797" class="Bound">B</a> <a id="7814" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5843" class="Record Operator">≃</a> <a id="7816" href="plfa.Connectives.html#7797" class="Bound">B</a> <a id="7818" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="7820" href="plfa.Connectives.html#7795" class="Bound">A</a>
<a id="7822" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#7783" class="Function">×-comm</a> <a id="7829" class="Symbol">=</a>
  <a id="7833" class="Keyword">record</a>
    <a id="7844" class="Symbol">{</a> <a id="7846" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5883" class="Field">to</a>       <a id="7855" class="Symbol">=</a>  <a id="7858" class="Symbol">λ{</a> <a id="7861" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="7863" href="plfa.Connectives.html#7863" class="Bound">x</a> <a id="7865" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="7867" href="plfa.Connectives.html#7867" class="Bound">y</a> <a id="7869" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="7871" class="Symbol">→</a> <a id="7873" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="7875" href="plfa.Connectives.html#7867" class="Bound">y</a> <a id="7877" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="7879" href="plfa.Connectives.html#7863" class="Bound">x</a> <a id="7881" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="7883" class="Symbol">}</a>
    <a id="7889" class="Symbol">;</a> <a id="7891" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5900" class="Field">from</a>     <a id="7900" class="Symbol">=</a>  <a id="7903" class="Symbol">λ{</a> <a id="7906" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="7908" href="plfa.Connectives.html#7908" class="Bound">y</a> <a id="7910" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="7912" href="plfa.Connectives.html#7912" class="Bound">x</a> <a id="7914" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="7916" class="Symbol">→</a> <a id="7918" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="7920" href="plfa.Connectives.html#7912" class="Bound">x</a> <a id="7922" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="7924" href="plfa.Connectives.html#7908" class="Bound">y</a> <a id="7926" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="7928" class="Symbol">}</a>
    <a id="7934" class="Symbol">;</a> <a id="7936" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5917" class="Field">from∘to</a>  <a id="7945" class="Symbol">=</a>  <a id="7948" class="Symbol">λ{</a> <a id="7951" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="7953" href="plfa.Connectives.html#7953" class="Bound">x</a> <a id="7955" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="7957" href="plfa.Connectives.html#7957" class="Bound">y</a> <a id="7959" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="7961" class="Symbol">→</a> <a id="7963" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="7968" class="Symbol">}</a>
    <a id="7974" class="Symbol">;</a> <a id="7976" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5959" class="Field">to∘from</a>  <a id="7985" class="Symbol">=</a>  <a id="7988" class="Symbol">λ{</a> <a id="7991" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="7993" href="plfa.Connectives.html#7993" class="Bound">y</a> <a id="7995" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="7997" href="plfa.Connectives.html#7997" class="Bound">x</a> <a id="7999" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="8001" class="Symbol">→</a> <a id="8003" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="8008" class="Symbol">}</a>
    <a id="8014" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
Being _commutative_ is different from being _commutative up to
isomorphism_.  Compare the two statements:
{:/}

满足*交换律*和*在同构意义下满足交换律*是不一样的。比较下列两个命题：

    m * n ≡ n * m
    A × B ≃ B × A

{::comment}
In the first case, we might have that `m` is `2` and `n` is `3`, and
both `m * n` and `n * m` are equal to `6`.  In the second case, we
might have that `A` is `Bool` and `B` is `Tri`, and `Bool × Tri` is
_not_ the same as `Tri × Bool`.  But there is an isomorphism between
the two types.  For instance, `⟨ true , aa ⟩`, which is a member of the
former, corresponds to `⟨ aa , true ⟩`, which is a member of the latter.
{:/}

在第一个情况下，我们可能有 `m` 是 `2`、`n` 是 `3`，那么 `m * n` 和 `n * m` 都是 `6`。
在第二个情况下，我们可能有 `A` 是 `Bool` 和 `B` 是 `Tri`，但是 `Bool × Tri` 和
`Tri × Bool` *不是*一样的。但是存在一个两者之间的同构。例如：`⟨ true , aa ⟩` 是前者的成员，
其对应后者的成员 `⟨ aa , true ⟩`。

{::comment}
For associativity, the `to` function reassociates two uses of pairing,
taking `⟨ ⟨ x , y ⟩ , z ⟩` to `⟨ x , ⟨ y , z ⟩ ⟩`, and the `from` function does
the inverse.  Again, the evidence of left and right inverse requires
matching against a suitable pattern to enable simplification:
{:/}

对于结合律来说，`to` 函数将两个有序对进行重组：将 `⟨ ⟨ x , y ⟩ , z ⟩` 转换为 `⟨ x , ⟨ y , z ⟩ ⟩`，
`from` 函数则为其逆。同样，左逆和右逆的证明需要在一个合适的模式来匹配，从而可以直接化简：

{% raw %}<pre class="Agda"><a id="×-assoc"></a><a id="9294" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#9294" class="Function">×-assoc</a> <a id="9302" class="Symbol">:</a> <a id="9304" class="Symbol">∀</a> <a id="9306" class="Symbol">{</a><a id="9307" href="plfa.Connectives.html#9307" class="Bound">A</a> <a id="9309" href="plfa.Connectives.html#9309" class="Bound">B</a> <a id="9311" href="plfa.Connectives.html#9311" class="Bound">C</a> <a id="9313" class="Symbol">:</a> <a id="9315" class="PrimitiveType">Set</a><a id="9318" class="Symbol">}</a> <a id="9320" class="Symbol">→</a> <a id="9322" class="Symbol">(</a><a id="9323" href="plfa.Connectives.html#9307" class="Bound">A</a> <a id="9325" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="9327" href="plfa.Connectives.html#9309" class="Bound">B</a><a id="9328" class="Symbol">)</a> <a id="9330" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="9332" href="plfa.Connectives.html#9311" class="Bound">C</a> <a id="9334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5843" class="Record Operator">≃</a> <a id="9336" href="plfa.Connectives.html#9307" class="Bound">A</a> <a id="9338" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="9340" class="Symbol">(</a><a id="9341" href="plfa.Connectives.html#9309" class="Bound">B</a> <a id="9343" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="9345" href="plfa.Connectives.html#9311" class="Bound">C</a><a id="9346" class="Symbol">)</a>
<a id="9348" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#9294" class="Function">×-assoc</a> <a id="9356" class="Symbol">=</a>
  <a id="9360" class="Keyword">record</a>
    <a id="9371" class="Symbol">{</a> <a id="9373" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5883" class="Field">to</a>      <a id="9381" class="Symbol">=</a> <a id="9383" class="Symbol">λ{</a> <a id="9386" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="9388" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="9390" href="plfa.Connectives.html#9390" class="Bound">x</a> <a id="9392" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="9394" href="plfa.Connectives.html#9394" class="Bound">y</a> <a id="9396" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="9398" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="9400" href="plfa.Connectives.html#9400" class="Bound">z</a> <a id="9402" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="9404" class="Symbol">→</a> <a id="9406" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="9408" href="plfa.Connectives.html#9390" class="Bound">x</a> <a id="9410" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="9412" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="9414" href="plfa.Connectives.html#9394" class="Bound">y</a> <a id="9416" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="9418" href="plfa.Connectives.html#9400" class="Bound">z</a> <a id="9420" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="9422" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="9424" class="Symbol">}</a>
    <a id="9430" class="Symbol">;</a> <a id="9432" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5900" class="Field">from</a>    <a id="9440" class="Symbol">=</a> <a id="9442" class="Symbol">λ{</a> <a id="9445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="9447" href="plfa.Connectives.html#9447" class="Bound">x</a> <a id="9449" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="9451" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="9453" href="plfa.Connectives.html#9453" class="Bound">y</a> <a id="9455" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="9457" href="plfa.Connectives.html#9457" class="Bound">z</a> <a id="9459" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="9461" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="9463" class="Symbol">→</a> <a id="9465" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="9467" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="9469" href="plfa.Connectives.html#9447" class="Bound">x</a> <a id="9471" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="9473" href="plfa.Connectives.html#9453" class="Bound">y</a> <a id="9475" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="9477" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="9479" href="plfa.Connectives.html#9457" class="Bound">z</a> <a id="9481" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="9483" class="Symbol">}</a>
    <a id="9489" class="Symbol">;</a> <a id="9491" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5917" class="Field">from∘to</a> <a id="9499" class="Symbol">=</a> <a id="9501" class="Symbol">λ{</a> <a id="9504" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="9506" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="9508" href="plfa.Connectives.html#9508" class="Bound">x</a> <a id="9510" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="9512" href="plfa.Connectives.html#9512" class="Bound">y</a> <a id="9514" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="9516" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="9518" href="plfa.Connectives.html#9518" class="Bound">z</a> <a id="9520" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="9522" class="Symbol">→</a> <a id="9524" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="9529" class="Symbol">}</a>
    <a id="9535" class="Symbol">;</a> <a id="9537" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5959" class="Field">to∘from</a> <a id="9545" class="Symbol">=</a> <a id="9547" class="Symbol">λ{</a> <a id="9550" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="9552" href="plfa.Connectives.html#9552" class="Bound">x</a> <a id="9554" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="9556" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="9558" href="plfa.Connectives.html#9558" class="Bound">y</a> <a id="9560" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="9562" href="plfa.Connectives.html#9562" class="Bound">z</a> <a id="9564" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="9566" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="9568" class="Symbol">→</a> <a id="9570" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="9575" class="Symbol">}</a>
    <a id="9581" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
Being _associative_ is not the same as being _associative
up to isomorphism_.  Compare the two statements:
{:/}

满足*结合律*和*在同构意义下满足结合律*是不一样的。比较下列两个命题：

    (m * n) * p ≡ m * (n * p)
    (A × B) × C ≃ A × (B × C)

{::comment}
For example, the type `(ℕ × Bool) × Tri` is _not_ the same as `ℕ ×
(Bool × Tri)`. But there is an isomorphism between the two types. For
instance `⟨ ⟨ 1 , true ⟩ , aa ⟩`, which is a member of the former,
corresponds to `⟨ 1 , ⟨ true , aa ⟩ ⟩`, which is a member of the latter.
{:/}

举个例子，`(ℕ × Bool) × Tri` 与 `ℕ × (Bool × Tri)` *不同*，但是两个类型之间
存在同构。例如 `⟨ ⟨ 1 , true ⟩ , aa ⟩`，一个前者的成员，与 `⟨ 1 , ⟨ true , aa ⟩ ⟩`，
一个后者的成员，相对应。

{::comment}
#### Exercise `⇔≃×` (recommended)
{:/}

#### 练习 `⇔≃×` （推荐）

{::comment}
Show that `A ⇔ B` as defined [earlier]({{ site.baseurl }}/Isomorphism/#iff)
is isomorphic to `(A → B) × (B → A)`.
{:/}

证明[之前]({{ site.baseurl }}/Isomorphism/#iff)定义的 `A ⇔ B` 与 `(A → B) × (B → A)` 同构。

{::comment}
{% raw %}<pre class="Agda"><a id="10549" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="10586" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
## Truth is unit
{:/}

## 真即是单元类型

{::comment}
Truth `⊤` always holds. We formalise this idea by
declaring a suitable inductive type:
{:/}

恒真 `⊤` 恒成立。我们将这个概念用合适的归纳类型来形式化：

{% raw %}<pre class="Agda"><a id="10793" class="Keyword">data</a> <a id="⊤"></a><a id="10798" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10798" class="Datatype">⊤</a> <a id="10800" class="Symbol">:</a> <a id="10802" class="PrimitiveType">Set</a> <a id="10806" class="Keyword">where</a>

  <a id="⊤.tt"></a><a id="10815" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10815" class="InductiveConstructor">tt</a> <a id="10818" class="Symbol">:</a>
    <a id="10824" class="Comment">--</a>
    <a id="10831" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10798" class="Datatype">⊤</a>
</pre>{% endraw %}
{::comment}
Evidence that `⊤` holds is of the form `tt`.
{:/}

`⊤` 成立的证明由 `tt` 的形式构成。

{::comment}
There is an introduction rule, but no elimination rule.
Given evidence that `⊤` holds, there is nothing more of interest we
can conclude.  Since truth always holds, knowing that it holds tells
us nothing new.
{:/}

恒真有引入规则，但没有消去规则。给定一个 `⊤` 成立的证明，我们不能得出任何有趣的结论。
因为恒真恒成立，知道恒真成立不会给我们带来新的知识。

{::comment}
The nullary case of `η-×` is `η-⊤`, which asserts that any
value of type `⊤` must be equal to `tt`:
{:/}

`η-×` 的 零元形式是 `η-⊤`，其断言了任何 `⊤` 类型的值一定等于 `tt`：

{% raw %}<pre class="Agda"><a id="η-⊤"></a><a id="11395" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#11395" class="Function">η-⊤</a> <a id="11399" class="Symbol">:</a> <a id="11401" class="Symbol">∀</a> <a id="11403" class="Symbol">(</a><a id="11404" href="plfa.Connectives.html#11404" class="Bound">w</a> <a id="11406" class="Symbol">:</a> <a id="11408" href="plfa.Connectives.html#10798" class="Datatype">⊤</a><a id="11409" class="Symbol">)</a> <a id="11411" class="Symbol">→</a> <a id="11413" href="plfa.Connectives.html#10815" class="InductiveConstructor">tt</a> <a id="11416" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11418" href="plfa.Connectives.html#11404" class="Bound">w</a>
<a id="11420" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#11395" class="Function">η-⊤</a> <a id="11424" href="plfa.Connectives.html#10815" class="InductiveConstructor">tt</a> <a id="11427" class="Symbol">=</a> <a id="11429" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
The pattern matching on the left-hand side is essential.  Replacing
`w` by `tt` allows both sides of the propositional equality to
simplify to the same term.
{:/}

左手边的模式匹配是必要的。将 `w` 替换为 `tt` 让等式两边可以化简为相同的值。

{::comment}
We refer to `⊤` as the _unit_ type. And, indeed,
type `⊤` has exactly one member, `tt`.  For example, the following
function enumerates all possible arguments of type `⊤`:

我们将 `⊤` 称为*单元*类型（Unit Type）。实际上，`⊤` 类型只有一个成员 `tt`。
例如，下面的函数枚举了所有 `⊤` 类型的参数：

{:/}
{% raw %}<pre class="Agda"><a id="⊤-count"></a><a id="11931" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#11931" class="Function">⊤-count</a> <a id="11939" class="Symbol">:</a> <a id="11941" href="plfa.Connectives.html#10798" class="Datatype">⊤</a> <a id="11943" class="Symbol">→</a> <a id="11945" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="11947" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#11931" class="Function">⊤-count</a> <a id="11955" href="plfa.Connectives.html#10815" class="InductiveConstructor">tt</a> <a id="11958" class="Symbol">=</a> <a id="11960" class="Number">1</a>
</pre>{% endraw %}
{::comment}
For numbers, one is the identity of multiplication. Correspondingly,
unit is the identity of product _up to isomorphism_.  For left
identity, the `to` function takes `⟨ tt , x ⟩` to `x`, and the `from`
function does the inverse.  The evidence of left inverse requires
matching against a suitable pattern to enable simplification:
{:/}

对于数来说，1 是乘法的幺元。对应地，单元是积的幺元（*在同构意义下*）。对于左幺元来说，
`to` 函数将 `⟨ tt , x ⟩` 转换成 `x`， `from` 函数则是其反函数。左逆的证明需要
匹配一个合适的模式来化简：

{% raw %}<pre class="Agda"><a id="⊤-identityˡ"></a><a id="12435" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#12435" class="Function">⊤-identityˡ</a> <a id="12447" class="Symbol">:</a> <a id="12449" class="Symbol">∀</a> <a id="12451" class="Symbol">{</a><a id="12452" href="plfa.Connectives.html#12452" class="Bound">A</a> <a id="12454" class="Symbol">:</a> <a id="12456" class="PrimitiveType">Set</a><a id="12459" class="Symbol">}</a> <a id="12461" class="Symbol">→</a> <a id="12463" href="plfa.Connectives.html#10798" class="Datatype">⊤</a> <a id="12465" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="12467" href="plfa.Connectives.html#12452" class="Bound">A</a> <a id="12469" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5843" class="Record Operator">≃</a> <a id="12471" href="plfa.Connectives.html#12452" class="Bound">A</a>
<a id="12473" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#12435" class="Function">⊤-identityˡ</a> <a id="12485" class="Symbol">=</a>
  <a id="12489" class="Keyword">record</a>
    <a id="12500" class="Symbol">{</a> <a id="12502" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5883" class="Field">to</a>      <a id="12510" class="Symbol">=</a> <a id="12512" class="Symbol">λ{</a> <a id="12515" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="12517" href="plfa.Connectives.html#10815" class="InductiveConstructor">tt</a> <a id="12520" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="12522" href="plfa.Connectives.html#12522" class="Bound">x</a> <a id="12524" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="12526" class="Symbol">→</a> <a id="12528" href="plfa.Connectives.html#12522" class="Bound">x</a> <a id="12530" class="Symbol">}</a>
    <a id="12536" class="Symbol">;</a> <a id="12538" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5900" class="Field">from</a>    <a id="12546" class="Symbol">=</a> <a id="12548" class="Symbol">λ{</a> <a id="12551" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#12551" class="Bound">x</a> <a id="12553" class="Symbol">→</a> <a id="12555" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="12557" href="plfa.Connectives.html#10815" class="InductiveConstructor">tt</a> <a id="12560" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="12562" href="plfa.Connectives.html#12551" class="Bound">x</a> <a id="12564" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="12566" class="Symbol">}</a>
    <a id="12572" class="Symbol">;</a> <a id="12574" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5917" class="Field">from∘to</a> <a id="12582" class="Symbol">=</a> <a id="12584" class="Symbol">λ{</a> <a id="12587" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="12589" href="plfa.Connectives.html#10815" class="InductiveConstructor">tt</a> <a id="12592" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="12594" href="plfa.Connectives.html#12594" class="Bound">x</a> <a id="12596" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="12598" class="Symbol">→</a> <a id="12600" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="12605" class="Symbol">}</a>
    <a id="12611" class="Symbol">;</a> <a id="12613" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5959" class="Field">to∘from</a> <a id="12621" class="Symbol">=</a> <a id="12623" class="Symbol">λ{</a> <a id="12626" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#12626" class="Bound">x</a> <a id="12628" class="Symbol">→</a> <a id="12630" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="12635" class="Symbol">}</a>
    <a id="12641" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
Having an _identity_ is different from having an identity
_up to isomorphism_.  Compare the two statements:
{:/}

*幺元*和*在同构意义下的幺元*是不一样的。比较下列两个命题：

    1 * m ≡ m
    ⊤ × A ≃ A

{::comment}
In the first case, we might have that `m` is `2`, and both
`1 * m` and `m` are equal to `2`.  In the second
case, we might have that `A` is `Bool`, and `⊤ × Bool` is _not_ the
same as `Bool`.  But there is an isomorphism between the two types.
For instance, `⟨ tt , true ⟩`, which is a member of the former,
corresponds to `true`, which is a member of the latter.
{:/}

在第一种情况下，我们可能有 `m` 是 `2`，那么 `1 * m` 和 `m` 都为 `2`。
在第二种情况下，我们可能有 `A` 是 `Bool`，但是 `⊤ × Bool` 和 `Bool` 是不同的。
例如：`⟨ tt , true ⟩` 是前者的成员，其对应后者的成员 `true`。

{::comment}
Right identity follows from commutativity of product and left identity:
{:/}

右幺元可以由积的交换律得来：

{% raw %}<pre class="Agda"><a id="⊤-identityʳ"></a><a id="13477" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#13477" class="Function">⊤-identityʳ</a> <a id="13489" class="Symbol">:</a> <a id="13491" class="Symbol">∀</a> <a id="13493" class="Symbol">{</a><a id="13494" href="plfa.Connectives.html#13494" class="Bound">A</a> <a id="13496" class="Symbol">:</a> <a id="13498" class="PrimitiveType">Set</a><a id="13501" class="Symbol">}</a> <a id="13503" class="Symbol">→</a> <a id="13505" class="Symbol">(</a><a id="13506" href="plfa.Connectives.html#13494" class="Bound">A</a> <a id="13508" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="13510" href="plfa.Connectives.html#10798" class="Datatype">⊤</a><a id="13511" class="Symbol">)</a> <a id="13513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5843" class="Record Operator">≃</a> <a id="13515" href="plfa.Connectives.html#13494" class="Bound">A</a>
<a id="13517" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#13477" class="Function">⊤-identityʳ</a> <a id="13529" class="Symbol">{</a><a id="13530" href="plfa.Connectives.html#13530" class="Bound">A</a><a id="13531" class="Symbol">}</a> <a id="13533" class="Symbol">=</a>
  <a id="13537" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11063" class="Function Operator">≃-begin</a>
    <a id="13549" class="Symbol">(</a><a id="13550" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#13530" class="Bound">A</a> <a id="13552" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="13554" href="plfa.Connectives.html#10798" class="Datatype">⊤</a><a id="13555" class="Symbol">)</a>
  <a id="13559" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11147" class="Function Operator">≃⟨</a> <a id="13562" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#7783" class="Function">×-comm</a> <a id="13569" href="plfa.Isomorphism.html#11147" class="Function Operator">⟩</a>
    <a id="13575" class="Symbol">(</a><a id="13576" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10798" class="Datatype">⊤</a> <a id="13578" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="13580" href="plfa.Connectives.html#13530" class="Bound">A</a><a id="13581" class="Symbol">)</a>
  <a id="13585" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11147" class="Function Operator">≃⟨</a> <a id="13588" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#12435" class="Function">⊤-identityˡ</a> <a id="13600" href="plfa.Isomorphism.html#11147" class="Function Operator">⟩</a>
    <a id="13606" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#13530" class="Bound">A</a>
  <a id="13610" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11266" class="Function Operator">≃-∎</a>
</pre>{% endraw %}
{::comment}
Here we have used a chain of isomorphisms, analogous to that used for
equality.
{:/}

我们在此使用了同构链，与等式链相似。

{::comment}
## Disjunction is sum
{:/}

## 析取即是和

{::comment}
Given two propositions `A` and `B`, the disjunction `A ⊎ B` holds
if either `A` holds or `B` holds.  We formalise this idea by
declaring a suitable inductive type:
{:/}

给定两个命题 `A` 和 `B`，析取 `A ⊎ B` 在 `A` 成立或者 `B` 成立时成立。
我们将这个概念用合适的归纳类型来形式化：

{% raw %}<pre class="Agda"><a id="14045" class="Keyword">data</a> <a id="_⊎_"></a><a id="14050" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14050" class="Datatype Operator">_⊎_</a> <a id="14054" class="Symbol">(</a><a id="14055" href="plfa.Connectives.html#14055" class="Bound">A</a> <a id="14057" href="plfa.Connectives.html#14057" class="Bound">B</a> <a id="14059" class="Symbol">:</a> <a id="14061" class="PrimitiveType">Set</a><a id="14064" class="Symbol">)</a> <a id="14066" class="Symbol">:</a> <a id="14068" class="PrimitiveType">Set</a> <a id="14072" class="Keyword">where</a>

  <a id="_⊎_.inj₁"></a><a id="14081" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14081" class="InductiveConstructor">inj₁</a> <a id="14086" class="Symbol">:</a>
      <a id="14094" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14055" class="Bound">A</a>
      <a id="14102" class="Comment">-----</a>
    <a id="14112" class="Symbol">→</a> <a id="14114" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14055" class="Bound">A</a> <a id="14116" href="plfa.Connectives.html#14050" class="Datatype Operator">⊎</a> <a id="14118" href="plfa.Connectives.html#14057" class="Bound">B</a>

  <a id="_⊎_.inj₂"></a><a id="14123" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14123" class="InductiveConstructor">inj₂</a> <a id="14128" class="Symbol">:</a>
      <a id="14136" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14057" class="Bound">B</a>
      <a id="14144" class="Comment">-----</a>
    <a id="14154" class="Symbol">→</a> <a id="14156" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14055" class="Bound">A</a> <a id="14158" href="plfa.Connectives.html#14050" class="Datatype Operator">⊎</a> <a id="14160" href="plfa.Connectives.html#14057" class="Bound">B</a>
</pre>{% endraw %}
{::comment}
Evidence that `A ⊎ B` holds is either of the form `inj₁ M`, where `M`
provides evidence that `A` holds, or `inj₂ N`, where `N` provides
evidence that `B` holds.
{:/}

`A ⊎ B` 成立的证明有两个形式： `inj₁ M`，其中 `M` 是 `A` 成立的证明，或者
`inj₂ N`，其中 `N` 是 `B` 成立的证明。

{::comment}
Given evidence that `A → C` and `B → C` both hold, then given
evidence that `A ⊎ B` holds we can conclude that `C` holds:
{:/}

给定 `A → C` 和 `B → C` 成立的证明，那么给定一个 `A ⊎ B` 的证明，我们可以得出 `C` 成立：

{% raw %}<pre class="Agda"><a id="case-⊎"></a><a id="14633" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14633" class="Function">case-⊎</a> <a id="14640" class="Symbol">:</a> <a id="14642" class="Symbol">∀</a> <a id="14644" class="Symbol">{</a><a id="14645" href="plfa.Connectives.html#14645" class="Bound">A</a> <a id="14647" href="plfa.Connectives.html#14647" class="Bound">B</a> <a id="14649" href="plfa.Connectives.html#14649" class="Bound">C</a> <a id="14651" class="Symbol">:</a> <a id="14653" class="PrimitiveType">Set</a><a id="14656" class="Symbol">}</a>
  <a id="14660" class="Symbol">→</a> <a id="14662" class="Symbol">(</a><a id="14663" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14645" class="Bound">A</a> <a id="14665" class="Symbol">→</a> <a id="14667" href="plfa.Connectives.html#14649" class="Bound">C</a><a id="14668" class="Symbol">)</a>
  <a id="14672" class="Symbol">→</a> <a id="14674" class="Symbol">(</a><a id="14675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14647" class="Bound">B</a> <a id="14677" class="Symbol">→</a> <a id="14679" href="plfa.Connectives.html#14649" class="Bound">C</a><a id="14680" class="Symbol">)</a>
  <a id="14684" class="Symbol">→</a> <a id="14686" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14645" class="Bound">A</a> <a id="14688" href="plfa.Connectives.html#14050" class="Datatype Operator">⊎</a> <a id="14690" href="plfa.Connectives.html#14647" class="Bound">B</a>
    <a id="14696" class="Comment">-----------</a>
  <a id="14710" class="Symbol">→</a> <a id="14712" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14649" class="Bound">C</a>
<a id="14714" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14633" class="Function">case-⊎</a> <a id="14721" href="plfa.Connectives.html#14721" class="Bound">f</a> <a id="14723" href="plfa.Connectives.html#14723" class="Bound">g</a> <a id="14725" class="Symbol">(</a><a id="14726" href="plfa.Connectives.html#14081" class="InductiveConstructor">inj₁</a> <a id="14731" href="plfa.Connectives.html#14731" class="Bound">x</a><a id="14732" class="Symbol">)</a> <a id="14734" class="Symbol">=</a> <a id="14736" href="plfa.Connectives.html#14721" class="Bound">f</a> <a id="14738" href="plfa.Connectives.html#14731" class="Bound">x</a>
<a id="14740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14633" class="Function">case-⊎</a> <a id="14747" href="plfa.Connectives.html#14747" class="Bound">f</a> <a id="14749" href="plfa.Connectives.html#14749" class="Bound">g</a> <a id="14751" class="Symbol">(</a><a id="14752" href="plfa.Connectives.html#14123" class="InductiveConstructor">inj₂</a> <a id="14757" href="plfa.Connectives.html#14757" class="Bound">y</a><a id="14758" class="Symbol">)</a> <a id="14760" class="Symbol">=</a> <a id="14762" href="plfa.Connectives.html#14749" class="Bound">g</a> <a id="14764" href="plfa.Connectives.html#14757" class="Bound">y</a>
</pre>{% endraw %}
{::comment}
Pattern matching against `inj₁` and `inj₂` is typical of how we exploit
evidence that a disjunction holds.
{:/}

对 `inj₁` 和 `inj₂` 进行模式匹配，是我们使用析取成立的证明的常见方法。

{::comment}
When `inj₁` and `inj₂` appear on the right-hand side of an equation we
refer to them as _constructors_, and when they appear on the
left-hand side we refer to them as _destructors_.  We also refer to
`case-⊎` as a destructor, since it plays a similar role.  Other
terminology refers to `inj₁` and `inj₂` as _introducing_ a
disjunction, and to `case-⊎` as _eliminating_ a disjunction; indeed
the former are sometimes given the names `⊎-I₁` and `⊎-I₂` and the
latter the name `⊎-E`.
{:/}

当 `inj₁` 和 `inj₂` 在等式右手边出现的时候，我们将其称作*构造子*，
当它出现在等式左边时，我们将其称作*析构器*。我们亦可将 `case-⊎`
称作析构器，因为它们起到相似的效果。其他术语将 `inj₁` 和 `inj₂` 称为*引入*析取，
将 `case-⊎` 称为*消去*析取。前者亦被称为 `⊎-I₁` 和 `⊎-I₂`，后者 `⊎-E`。

{::comment}
Applying the destructor to each of the constructors is the identity:
{:/}

对每个构造子使用析构器得到的是原来的值：

{% raw %}<pre class="Agda"><a id="η-⊎"></a><a id="15738" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#15738" class="Function">η-⊎</a> <a id="15742" class="Symbol">:</a> <a id="15744" class="Symbol">∀</a> <a id="15746" class="Symbol">{</a><a id="15747" href="plfa.Connectives.html#15747" class="Bound">A</a> <a id="15749" href="plfa.Connectives.html#15749" class="Bound">B</a> <a id="15751" class="Symbol">:</a> <a id="15753" class="PrimitiveType">Set</a><a id="15756" class="Symbol">}</a> <a id="15758" class="Symbol">(</a><a id="15759" href="plfa.Connectives.html#15759" class="Bound">w</a> <a id="15761" class="Symbol">:</a> <a id="15763" href="plfa.Connectives.html#15747" class="Bound">A</a> <a id="15765" href="plfa.Connectives.html#14050" class="Datatype Operator">⊎</a> <a id="15767" href="plfa.Connectives.html#15749" class="Bound">B</a><a id="15768" class="Symbol">)</a> <a id="15770" class="Symbol">→</a> <a id="15772" href="plfa.Connectives.html#14633" class="Function">case-⊎</a> <a id="15779" href="plfa.Connectives.html#14081" class="InductiveConstructor">inj₁</a> <a id="15784" href="plfa.Connectives.html#14123" class="InductiveConstructor">inj₂</a> <a id="15789" href="plfa.Connectives.html#15759" class="Bound">w</a> <a id="15791" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="15793" href="plfa.Connectives.html#15759" class="Bound">w</a>
<a id="15795" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#15738" class="Function">η-⊎</a> <a id="15799" class="Symbol">(</a><a id="15800" href="plfa.Connectives.html#14081" class="InductiveConstructor">inj₁</a> <a id="15805" href="plfa.Connectives.html#15805" class="Bound">x</a><a id="15806" class="Symbol">)</a> <a id="15808" class="Symbol">=</a> <a id="15810" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="15815" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#15738" class="Function">η-⊎</a> <a id="15819" class="Symbol">(</a><a id="15820" href="plfa.Connectives.html#14123" class="InductiveConstructor">inj₂</a> <a id="15825" href="plfa.Connectives.html#15825" class="Bound">y</a><a id="15826" class="Symbol">)</a> <a id="15828" class="Symbol">=</a> <a id="15830" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
More generally, we can also throw in an arbitrary function from a disjunction:
{:/}

更普遍地来说，我们亦可对于析取使用一个任意的函数：

{% raw %}<pre class="Agda"><a id="uniq-⊎"></a><a id="15968" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#15968" class="Function">uniq-⊎</a> <a id="15975" class="Symbol">:</a> <a id="15977" class="Symbol">∀</a> <a id="15979" class="Symbol">{</a><a id="15980" href="plfa.Connectives.html#15980" class="Bound">A</a> <a id="15982" href="plfa.Connectives.html#15982" class="Bound">B</a> <a id="15984" href="plfa.Connectives.html#15984" class="Bound">C</a> <a id="15986" class="Symbol">:</a> <a id="15988" class="PrimitiveType">Set</a><a id="15991" class="Symbol">}</a> <a id="15993" class="Symbol">(</a><a id="15994" href="plfa.Connectives.html#15994" class="Bound">h</a> <a id="15996" class="Symbol">:</a> <a id="15998" href="plfa.Connectives.html#15980" class="Bound">A</a> <a id="16000" href="plfa.Connectives.html#14050" class="Datatype Operator">⊎</a> <a id="16002" href="plfa.Connectives.html#15982" class="Bound">B</a> <a id="16004" class="Symbol">→</a> <a id="16006" href="plfa.Connectives.html#15984" class="Bound">C</a><a id="16007" class="Symbol">)</a> <a id="16009" class="Symbol">(</a><a id="16010" href="plfa.Connectives.html#16010" class="Bound">w</a> <a id="16012" class="Symbol">:</a> <a id="16014" href="plfa.Connectives.html#15980" class="Bound">A</a> <a id="16016" href="plfa.Connectives.html#14050" class="Datatype Operator">⊎</a> <a id="16018" href="plfa.Connectives.html#15982" class="Bound">B</a><a id="16019" class="Symbol">)</a> <a id="16021" class="Symbol">→</a>
  <a id="16025" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14633" class="Function">case-⊎</a> <a id="16032" class="Symbol">(</a><a id="16033" href="plfa.Connectives.html#15994" class="Bound">h</a> <a id="16035" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="16037" href="plfa.Connectives.html#14081" class="InductiveConstructor">inj₁</a><a id="16041" class="Symbol">)</a> <a id="16043" class="Symbol">(</a><a id="16044" href="plfa.Connectives.html#15994" class="Bound">h</a> <a id="16046" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="16048" href="plfa.Connectives.html#14123" class="InductiveConstructor">inj₂</a><a id="16052" class="Symbol">)</a> <a id="16054" href="plfa.Connectives.html#16010" class="Bound">w</a> <a id="16056" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16058" href="plfa.Connectives.html#15994" class="Bound">h</a> <a id="16060" href="plfa.Connectives.html#16010" class="Bound">w</a>
<a id="16062" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#15968" class="Function">uniq-⊎</a> <a id="16069" href="plfa.Connectives.html#16069" class="Bound">h</a> <a id="16071" class="Symbol">(</a><a id="16072" href="plfa.Connectives.html#14081" class="InductiveConstructor">inj₁</a> <a id="16077" href="plfa.Connectives.html#16077" class="Bound">x</a><a id="16078" class="Symbol">)</a> <a id="16080" class="Symbol">=</a> <a id="16082" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="16087" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#15968" class="Function">uniq-⊎</a> <a id="16094" href="plfa.Connectives.html#16094" class="Bound">h</a> <a id="16096" class="Symbol">(</a><a id="16097" href="plfa.Connectives.html#14123" class="InductiveConstructor">inj₂</a> <a id="16102" href="plfa.Connectives.html#16102" class="Bound">y</a><a id="16103" class="Symbol">)</a> <a id="16105" class="Symbol">=</a> <a id="16107" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
The pattern matching on the left-hand side is essential.  Replacing
`w` by `inj₁ x` allows both sides of the propositional equality to
simplify to the same term, and similarly for `inj₂ y`.
{:/}

左手边的模式匹配是必要的。用 `inj₁ x` 来替换 `w` 让等式的两边可以化简成相同的项，
`inj₂ y` 同理。

{::comment}
We set the precedence of disjunction so that it binds less tightly
than any other declared operator:
{:/}

我们设置析取的优先级，使它与任何已经定义的运算符都结合的不紧密：

{% raw %}<pre class="Agda"><a id="16545" class="Keyword">infix</a> <a id="16551" class="Number">1</a> <a id="16553" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14050" class="Datatype Operator">_⊎_</a>
</pre>{% endraw %}
{::comment}
Thus, `A × C ⊎ B × C` parses as `(A × C) ⊎ (B × C)`.
{:/}

因此 `A × C ⊎ B × C` 解析为 `(A × C) ⊎ (B × C)`。

{::comment}
Given two types `A` and `B`, we refer to `A ⊎ B` as the
_sum_ of `A` and `B`.  In set theory, it is also sometimes
called the _disjoint union_, and in computing it corresponds
to a _variant record_ type. Among other reasons for
calling it the sum, note that if type `A` has `m`
distinct members, and type `B` has `n` distinct members,
then the type `A ⊎ B` has `m + n` distinct members.
For instance, consider a type `Bool` with two members, and
a type `Tri` with three members, as defined earlier.
Then the type `Bool ⊎ Tri` has five
members:
{:/}

给定两个类型 `A` 和 `B`，我们将 `A ⊎ B` 称为 `A` 与 `B` 的*和*。
在集合论中它也被称作*不交并*（Disjoint Union），在计算机科学中它对应*变体记录*类型。
如果类型 `A` 有 `m` 个不同的成员，类型 `B` 有 `n` 个不同的成员，
那么类型 `A ⊎ B` 有 `m + n` 个不同的成员。这也是它被称为和的原因之一。
例如，考虑有两个成员的 `Bool` 类型，和有三个成员的 `Tri` 类型，如之前的定义。
那么，`Bool ⊎ Tri` 类型有如下的五个成员：

    inj₁ true     inj₂ aa
    inj₁ false    inj₂ bb
                  inj₂ cc

{::comment}
For example, the following function enumerates all
possible arguments of type `Bool ⊎ Tri`:
{:/}

下面的函数枚举了所有类型为 `Bool ⊎ Tri` 的参数：

{% raw %}<pre class="Agda"><a id="⊎-count"></a><a id="17730" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#17730" class="Function">⊎-count</a> <a id="17738" class="Symbol">:</a> <a id="17740" href="plfa.Connectives.html#6331" class="Datatype">Bool</a> <a id="17745" href="plfa.Connectives.html#14050" class="Datatype Operator">⊎</a> <a id="17747" href="plfa.Connectives.html#6384" class="Datatype">Tri</a> <a id="17751" class="Symbol">→</a> <a id="17753" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="17755" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#17730" class="Function">⊎-count</a> <a id="17763" class="Symbol">(</a><a id="17764" href="plfa.Connectives.html#14081" class="InductiveConstructor">inj₁</a> <a id="17769" href="plfa.Connectives.html#6350" class="InductiveConstructor">true</a><a id="17773" class="Symbol">)</a>   <a id="17777" class="Symbol">=</a>  <a id="17780" class="Number">1</a>
<a id="17782" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#17730" class="Function">⊎-count</a> <a id="17790" class="Symbol">(</a><a id="17791" href="plfa.Connectives.html#14081" class="InductiveConstructor">inj₁</a> <a id="17796" href="plfa.Connectives.html#6365" class="InductiveConstructor">false</a><a id="17801" class="Symbol">)</a>  <a id="17804" class="Symbol">=</a>  <a id="17807" class="Number">2</a>
<a id="17809" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#17730" class="Function">⊎-count</a> <a id="17817" class="Symbol">(</a><a id="17818" href="plfa.Connectives.html#14123" class="InductiveConstructor">inj₂</a> <a id="17823" href="plfa.Connectives.html#6402" class="InductiveConstructor">aa</a><a id="17825" class="Symbol">)</a>     <a id="17831" class="Symbol">=</a>  <a id="17834" class="Number">3</a>
<a id="17836" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#17730" class="Function">⊎-count</a> <a id="17844" class="Symbol">(</a><a id="17845" href="plfa.Connectives.html#14123" class="InductiveConstructor">inj₂</a> <a id="17850" href="plfa.Connectives.html#6413" class="InductiveConstructor">bb</a><a id="17852" class="Symbol">)</a>     <a id="17858" class="Symbol">=</a>  <a id="17861" class="Number">4</a>
<a id="17863" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#17730" class="Function">⊎-count</a> <a id="17871" class="Symbol">(</a><a id="17872" href="plfa.Connectives.html#14123" class="InductiveConstructor">inj₂</a> <a id="17877" href="plfa.Connectives.html#6424" class="InductiveConstructor">cc</a><a id="17879" class="Symbol">)</a>     <a id="17885" class="Symbol">=</a>  <a id="17888" class="Number">5</a>
</pre>{% endraw %}
{::comment}
Sum on types also shares a property with sum on numbers in that it is
commutative and associative _up to isomorphism_.
{:/}

类型上的和与数的和有相似的性质——它们满足交换律和结合律。
更确切地说，和在*在同构意义下*是交换和结合的。

{::comment}
#### Exercise `⊎-comm` (recommended)
{:/}

#### 练习 `⊎-comm` （推荐）

{::comment}
Show sum is commutative up to isomorphism.
{:/}

证明和类型在同构意义下满足交换律。

{::comment}
{% raw %}<pre class="Agda"><a id="18262" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="18299" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
#### Exercise `⊎-assoc`
{:/}

#### 练习 `⊎-assoc`

{::comment}
Show sum is associative up to isomorphism.
{:/}

证明和类型在同构意义下满足结合律。

{::comment}
{% raw %}<pre class="Agda"><a id="18474" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="18511" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
## False is empty
{:/}

## 假即是空类型

{::comment}
False `⊥` never holds.  We formalise this idea by declaring
a suitable inductive type:
{:/}

恒假 `⊥` 从不成立。我们将这个概念用合适的归纳类型来形式化：

{::comment}
FIXME: the code block is removed to make Agda not recognise this as code.
data ⊥ : Set where
  -- no clauses!
{:/}

{% raw %}<pre class="Agda"><a id="18847" class="Keyword">data</a> <a id="⊥"></a><a id="18852" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#18852" class="Datatype">⊥</a> <a id="18854" class="Symbol">:</a> <a id="18856" class="PrimitiveType">Set</a> <a id="18860" class="Keyword">where</a>
  <a id="18868" class="Comment">-- 没有语句！</a>
</pre>{% endraw %}
{::comment}
There is no possible evidence that `⊥` holds.
{:/}

没有 `⊥` 成立的证明。

{::comment}
Dual to `⊤`, for `⊥` there is no introduction rule but an elimination rule.
Since false never holds, knowing that it holds tells us we are in a
paradoxical situation.  Given evidence that `⊥` holds, we might
conclude anything!  This is a basic principle of logic, known in
medieval times by the Latin phrase _ex falso_, and known to children
through phrases such as "if pigs had wings, then I'd be the Queen of
Sheba".  We formalise it as follows:
{:/}

与 `⊤` 相对偶，`⊥` 没有引入规则，但是有消去规则。因为恒假从不成立，
如果它一旦成立，我们就进入了矛盾之中。给定 `⊥` 成立的证明，我们可以得出任何结论！
这是逻辑学的基本原理，又由中世纪的拉丁文词组 _ex falso_ 为名。小孩子也由诸如
“如果猪有翅膀，那我就是示巴女王”的词组中知晓。我们如下将它形式化：

{% raw %}<pre class="Agda"><a id="⊥-elim"></a><a id="19595" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#19595" class="Function">⊥-elim</a> <a id="19602" class="Symbol">:</a> <a id="19604" class="Symbol">∀</a> <a id="19606" class="Symbol">{</a><a id="19607" href="plfa.Connectives.html#19607" class="Bound">A</a> <a id="19609" class="Symbol">:</a> <a id="19611" class="PrimitiveType">Set</a><a id="19614" class="Symbol">}</a>
  <a id="19618" class="Symbol">→</a> <a id="19620" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#18852" class="Datatype">⊥</a>
    <a id="19626" class="Comment">--</a>
  <a id="19631" class="Symbol">→</a> <a id="19633" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#19607" class="Bound">A</a>
<a id="19635" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#19595" class="Function">⊥-elim</a> <a id="19642" class="Symbol">()</a>
</pre>{% endraw %}
{::comment}
This is our first use of the _absurd pattern_ `()`.
Here since `⊥` is a type with no members, we indicate that it is
_never_ possible to match against a value of this type by using
the pattern `()`.
{:/}

这是我们第一次使用*荒谬模式*（Absurd Pattern） `()`。在这里，因为 `⊥`
是一个没有成员的类型，我们用 `()` 模式来指明这里不可能匹配任何这个类型的值。

{::comment}
The nullary case of `case-⊎` is `⊥-elim`.  By analogy,
we might have called it `case-⊥`, but chose to stick with the name
in the standard library.
{:/}

`case-⊎` 的零元形式是 `⊥-elim`。类比的来说，它应该叫做 `case-⊥`，
但是我们在此使用标准库中使用的名字。

{::comment}
The nullary case of `uniq-⊎` is `uniq-⊥`, which asserts that `⊥-elim`
is equal to any arbitrary function from `⊥`:
{:/}

`uniq-⊎` 的零元形式是 `uniq-⊥`，其断言了 `⊥-elim` 和任何取 `⊥` 的函数是等价的。

{% raw %}<pre class="Agda"><a id="uniq-⊥"></a><a id="20385" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#20385" class="Function">uniq-⊥</a> <a id="20392" class="Symbol">:</a> <a id="20394" class="Symbol">∀</a> <a id="20396" class="Symbol">{</a><a id="20397" href="plfa.Connectives.html#20397" class="Bound">C</a> <a id="20399" class="Symbol">:</a> <a id="20401" class="PrimitiveType">Set</a><a id="20404" class="Symbol">}</a> <a id="20406" class="Symbol">(</a><a id="20407" href="plfa.Connectives.html#20407" class="Bound">h</a> <a id="20409" class="Symbol">:</a> <a id="20411" href="plfa.Connectives.html#18852" class="Datatype">⊥</a> <a id="20413" class="Symbol">→</a> <a id="20415" href="plfa.Connectives.html#20397" class="Bound">C</a><a id="20416" class="Symbol">)</a> <a id="20418" class="Symbol">(</a><a id="20419" href="plfa.Connectives.html#20419" class="Bound">w</a> <a id="20421" class="Symbol">:</a> <a id="20423" href="plfa.Connectives.html#18852" class="Datatype">⊥</a><a id="20424" class="Symbol">)</a> <a id="20426" class="Symbol">→</a> <a id="20428" href="plfa.Connectives.html#19595" class="Function">⊥-elim</a> <a id="20435" href="plfa.Connectives.html#20419" class="Bound">w</a> <a id="20437" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="20439" href="plfa.Connectives.html#20407" class="Bound">h</a> <a id="20441" href="plfa.Connectives.html#20419" class="Bound">w</a>
<a id="20443" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#20385" class="Function">uniq-⊥</a> <a id="20450" href="plfa.Connectives.html#20450" class="Bound">h</a> <a id="20452" class="Symbol">()</a>
</pre>{% endraw %}
{::comment}
Using the absurd pattern asserts there are no possible values for `w`,
so the equation holds trivially.
{:/}

使用荒谬模式断言了 `w` 没有任何可能的值，因此等式显然成立。

{::comment}
We refer to `⊥` as the _empty_ type. And, indeed,
type `⊥` has no members. For example, the following function
enumerates all possible arguments of type `⊥`:

我们将 `⊥` 成为*空*类型（Empty Type）。实际上，`⊥` 类型没有成员。
例如，下面的函数枚举了所有 `⊥` 类型的参数：

{:/}
{% raw %}<pre class="Agda"><a id="⊥-count"></a><a id="20866" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#20866" class="Function">⊥-count</a> <a id="20874" class="Symbol">:</a> <a id="20876" href="plfa.Connectives.html#18852" class="Datatype">⊥</a> <a id="20878" class="Symbol">→</a> <a id="20880" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="20882" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#20866" class="Function">⊥-count</a> <a id="20890" class="Symbol">()</a>
</pre>{% endraw %}
{::comment}
Here again the absurd pattern `()` indicates that no value can match
type `⊥`.
{:/}

同样，荒谬模式告诉我们没有值可以来匹配类型 `⊥`。

{::comment}
For numbers, zero is the identity of addition. Correspondingly, empty
is the identity of sums _up to isomorphism_.
{:/}

对于数来说，0 是加法的幺元。对应地，空是和的幺元（*在同构意义下*）。

{::comment}
#### Exercise `⊥-identityˡ` (recommended)
{:/}

#### 练习 `⊥-identityˡ` （推荐）

{::comment}
Show empty is the left identity of sums up to isomorphism.
{:/}

证明空在同构意义下是和的左幺元。

{::comment}
{% raw %}<pre class="Agda"><a id="21393" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="21430" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
#### Exercise `⊥-identityʳ`
{:/}

#### 练习 `⊥-identityʳ`

{::comment}
Show empty is the right identity of sums up to isomorphism.
{:/}

证明空在同构意义下是和的右幺元。

{::comment}
{% raw %}<pre class="Agda"><a id="21629" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="21666" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
## Implication is function {#implication}
{:/}

## 蕴涵即是函数 {#implication}

{::comment}
Given two propositions `A` and `B`, the implication `A → B` holds if
whenever `A` holds then `B` must also hold.  We formalise implication using
the function type, which has appeared throughout this book.
{:/}

给定两个命题 `A` 和 `B`，其蕴涵 `A → B` 在任何 `A` 成立的时候，`B` 也成立时成立。
我们用函数类型来形式化蕴涵，如本书中通篇出现的那样。


{::comment}
Evidence that `A → B` holds is of the form
{:/}

`A → B` 成立的证据由下面的形式组成：

    λ (x : A) → N

{::comment}
where `N` is a term of type `B` containing as a free variable `x` of type `A`.
Given a term `L` providing evidence that `A → B` holds, and a term `M`
providing evidence that `A` holds, the term `L M` provides evidence that
`B` holds.  In other words, evidence that `A → B` holds is a function that
converts evidence that `A` holds into evidence that `B` holds.
{:/}

其中 `N` 是一个类型为 `B` 的项，其包括了一个类型为 `A` 的自由变量 `x`。
给定一个 `A → B` 成立的证明 `L`，和一个 `A` 成立的证明 `M`，那么 `L M` 是 `B` 成立的证明。
也就是说，`A → B` 成立的证明是一个函数，将 `A` 成立的证明转换成 `B` 成立的证明。

{::comment}
Put another way, if we know that `A → B` and `A` both hold,
then we may conclude that `B` holds:
{:/}

换句话说，如果知道 `A → B` 和 `A` 同时成立，那么我们可以推出 `B` 成立：

{% raw %}<pre class="Agda"><a id="→-elim"></a><a id="22886" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#22886" class="Function">→-elim</a> <a id="22893" class="Symbol">:</a> <a id="22895" class="Symbol">∀</a> <a id="22897" class="Symbol">{</a><a id="22898" href="plfa.Connectives.html#22898" class="Bound">A</a> <a id="22900" href="plfa.Connectives.html#22900" class="Bound">B</a> <a id="22902" class="Symbol">:</a> <a id="22904" class="PrimitiveType">Set</a><a id="22907" class="Symbol">}</a>
  <a id="22911" class="Symbol">→</a> <a id="22913" class="Symbol">(</a><a id="22914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#22898" class="Bound">A</a> <a id="22916" class="Symbol">→</a> <a id="22918" href="plfa.Connectives.html#22900" class="Bound">B</a><a id="22919" class="Symbol">)</a>
  <a id="22923" class="Symbol">→</a> <a id="22925" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#22898" class="Bound">A</a>
    <a id="22931" class="Comment">-------</a>
  <a id="22941" class="Symbol">→</a> <a id="22943" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#22900" class="Bound">B</a>
<a id="22945" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#22886" class="Function">→-elim</a> <a id="22952" href="plfa.Connectives.html#22952" class="Bound">L</a> <a id="22954" href="plfa.Connectives.html#22954" class="Bound">M</a> <a id="22956" class="Symbol">=</a> <a id="22958" href="plfa.Connectives.html#22952" class="Bound">L</a> <a id="22960" href="plfa.Connectives.html#22954" class="Bound">M</a>
</pre>{% endraw %}
{::comment}
In medieval times, this rule was known by the name _modus ponens_.
It corresponds to function application.
{:/}

在中世纪，这条规则被叫做 _modus ponens_，它与函数应用相对应。

{::comment}
Defining a function, with a named definition or a lambda abstraction,
is referred to as _introducing_ a function,
while applying a function is referred to as _eliminating_ the function.
{:/}

定义一个函数，不管是带名字的定义或是使用 Lambda 抽象，被称为*引入*一个函数，
使用一个函数被称为*消去*一个函数。

{::comment}
Elimination followed by introduction is the identity:
{:/}

引入后接着消去，得到的还是原来的值：

{% raw %}<pre class="Agda"><a id="η-→"></a><a id="23496" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#23496" class="Function">η-→</a> <a id="23500" class="Symbol">:</a> <a id="23502" class="Symbol">∀</a> <a id="23504" class="Symbol">{</a><a id="23505" href="plfa.Connectives.html#23505" class="Bound">A</a> <a id="23507" href="plfa.Connectives.html#23507" class="Bound">B</a> <a id="23509" class="Symbol">:</a> <a id="23511" class="PrimitiveType">Set</a><a id="23514" class="Symbol">}</a> <a id="23516" class="Symbol">(</a><a id="23517" href="plfa.Connectives.html#23517" class="Bound">f</a> <a id="23519" class="Symbol">:</a> <a id="23521" href="plfa.Connectives.html#23505" class="Bound">A</a> <a id="23523" class="Symbol">→</a> <a id="23525" href="plfa.Connectives.html#23507" class="Bound">B</a><a id="23526" class="Symbol">)</a> <a id="23528" class="Symbol">→</a> <a id="23530" class="Symbol">(λ</a> <a id="23533" class="Symbol">(</a><a id="23534" href="plfa.Connectives.html#23534" class="Bound">x</a> <a id="23536" class="Symbol">:</a> <a id="23538" href="plfa.Connectives.html#23505" class="Bound">A</a><a id="23539" class="Symbol">)</a> <a id="23541" class="Symbol">→</a> <a id="23543" href="plfa.Connectives.html#23517" class="Bound">f</a> <a id="23545" href="plfa.Connectives.html#23534" class="Bound">x</a><a id="23546" class="Symbol">)</a> <a id="23548" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="23550" href="plfa.Connectives.html#23517" class="Bound">f</a>
<a id="23552" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#23496" class="Function">η-→</a> <a id="23556" href="plfa.Connectives.html#23556" class="Bound">f</a> <a id="23558" class="Symbol">=</a> <a id="23560" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
Implication binds less tightly than any other operator. Thus, `A ⊎ B →
B ⊎ A` parses as `(A ⊎ B) → (B ⊎ A)`.
{:/}

蕴涵比其他的运算符结合得都不紧密。因此 `A ⊎ B → B ⊎ A` 被解析为 `(A ⊎ B) → (B ⊎ A)`。

{::comment}
Given two types `A` and `B`, we refer to `A → B` as the _function_
space from `A` to `B`.  It is also sometimes called the _exponential_,
with `B` raised to the `A` power.  Among other reasons for calling
it the exponential, note that if type `A` has `m` distinct
members, and type `B` has `n` distinct members, then the type
`A → B` has `nᵐ` distinct members.  For instance, consider a
type `Bool` with two members and a type `Tri` with three members,
as defined earlier. Then the type `Bool → Tri` has nine (that is,
three squared) members:
{:/}

给定两个类型 `A` 和 `B`，我们将 `A → B` 称为从 `A` 到 `B` 的*函数*空间。
它有时也被称作以 `B` 为底，`A` 为次数的*幂*。如果类型 `A` 有 `m` 个不同的成员，
类型 `B` 有 `n` 个不同的成员，那么类型 `A → B` 有 `nᵐ` 个不同的成员。
这也是它被称为幂的原因之一。例如，考虑有两个成员的 `Bool` 类型，和有三个成员的 `Tri` 类型，
如之前的定义。那么，`Bool → Tri` 类型有如下的九个成员（三的平方）：

    λ{true → aa; false → aa}  λ{true → aa; false → bb}  λ{true → aa; false → cc}
    λ{true → bb; false → aa}  λ{true → bb; false → bb}  λ{true → bb; false → cc}
    λ{true → cc; false → aa}  λ{true → cc; false → bb}  λ{true → cc; false → cc}

{::comment}
For example, the following function enumerates all possible
arguments of the type `Bool → Tri`:
{:/}

下面的函数枚举了所有类型为 `Bool → Tri` 的参数：

{% raw %}<pre class="Agda"><a id="→-count"></a><a id="24963" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#24963" class="Function">→-count</a> <a id="24971" class="Symbol">:</a> <a id="24973" class="Symbol">(</a><a id="24974" href="plfa.Connectives.html#6331" class="Datatype">Bool</a> <a id="24979" class="Symbol">→</a> <a id="24981" href="plfa.Connectives.html#6384" class="Datatype">Tri</a><a id="24984" class="Symbol">)</a> <a id="24986" class="Symbol">→</a> <a id="24988" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="24990" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#24963" class="Function">→-count</a> <a id="24998" href="plfa.Connectives.html#24998" class="Bound">f</a> <a id="25000" class="Keyword">with</a> <a id="25005" href="plfa.Connectives.html#24998" class="Bound">f</a> <a id="25007" href="plfa.Connectives.html#6350" class="InductiveConstructor">true</a> <a id="25012" class="Symbol">|</a> <a id="25014" href="plfa.Connectives.html#24998" class="Bound">f</a> <a id="25016" href="plfa.Connectives.html#6365" class="InductiveConstructor">false</a>
<a id="25022" class="Symbol">...</a>          <a id="25035" class="Symbol">|</a> <a id="25037" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6402" class="InductiveConstructor">aa</a>     <a id="25044" class="Symbol">|</a> <a id="25046" href="plfa.Connectives.html#6402" class="InductiveConstructor">aa</a>      <a id="25054" class="Symbol">=</a>   <a id="25058" class="Number">1</a>
<a id="25060" class="Symbol">...</a>          <a id="25073" class="Symbol">|</a> <a id="25075" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6402" class="InductiveConstructor">aa</a>     <a id="25082" class="Symbol">|</a> <a id="25084" href="plfa.Connectives.html#6413" class="InductiveConstructor">bb</a>      <a id="25092" class="Symbol">=</a>   <a id="25096" class="Number">2</a>
<a id="25098" class="Symbol">...</a>          <a id="25111" class="Symbol">|</a> <a id="25113" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6402" class="InductiveConstructor">aa</a>     <a id="25120" class="Symbol">|</a> <a id="25122" href="plfa.Connectives.html#6424" class="InductiveConstructor">cc</a>      <a id="25130" class="Symbol">=</a>   <a id="25134" class="Number">3</a>
<a id="25136" class="Symbol">...</a>          <a id="25149" class="Symbol">|</a> <a id="25151" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6413" class="InductiveConstructor">bb</a>     <a id="25158" class="Symbol">|</a> <a id="25160" href="plfa.Connectives.html#6402" class="InductiveConstructor">aa</a>      <a id="25168" class="Symbol">=</a>   <a id="25172" class="Number">4</a>
<a id="25174" class="Symbol">...</a>          <a id="25187" class="Symbol">|</a> <a id="25189" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6413" class="InductiveConstructor">bb</a>     <a id="25196" class="Symbol">|</a> <a id="25198" href="plfa.Connectives.html#6413" class="InductiveConstructor">bb</a>      <a id="25206" class="Symbol">=</a>   <a id="25210" class="Number">5</a>
<a id="25212" class="Symbol">...</a>          <a id="25225" class="Symbol">|</a> <a id="25227" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6413" class="InductiveConstructor">bb</a>     <a id="25234" class="Symbol">|</a> <a id="25236" href="plfa.Connectives.html#6424" class="InductiveConstructor">cc</a>      <a id="25244" class="Symbol">=</a>   <a id="25248" class="Number">6</a>
<a id="25250" class="Symbol">...</a>          <a id="25263" class="Symbol">|</a> <a id="25265" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6424" class="InductiveConstructor">cc</a>     <a id="25272" class="Symbol">|</a> <a id="25274" href="plfa.Connectives.html#6402" class="InductiveConstructor">aa</a>      <a id="25282" class="Symbol">=</a>   <a id="25286" class="Number">7</a>
<a id="25288" class="Symbol">...</a>          <a id="25301" class="Symbol">|</a> <a id="25303" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6424" class="InductiveConstructor">cc</a>     <a id="25310" class="Symbol">|</a> <a id="25312" href="plfa.Connectives.html#6413" class="InductiveConstructor">bb</a>      <a id="25320" class="Symbol">=</a>   <a id="25324" class="Number">8</a>
<a id="25326" class="Symbol">...</a>          <a id="25339" class="Symbol">|</a> <a id="25341" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6424" class="InductiveConstructor">cc</a>     <a id="25348" class="Symbol">|</a> <a id="25350" href="plfa.Connectives.html#6424" class="InductiveConstructor">cc</a>      <a id="25358" class="Symbol">=</a>   <a id="25362" class="Number">9</a>
</pre>{% endraw %}
{::comment}
Exponential on types also share a property with exponential on
numbers in that many of the standard identities for numbers carry
over to the types.
{:/}

类型上的幂与数的幂有相似的性质，很多数上成立的关系式也可以在类型上成立。

{::comment}
Corresponding to the law
{:/}

对应如下的定律：

    (p ^ n) ^ m  ≡  p ^ (n * m)

{::comment}
we have the isomorphism
{:/}

我们有如下的同构：

    A → (B → C)  ≃  (A × B) → C

{::comment}
Both types can be viewed as functions that given evidence that `A` holds
and evidence that `B` holds can return evidence that `C` holds.
This isomorphism sometimes goes by the name *currying*.
The proof of the right inverse requires extensionality:
{:/}

两个类型可以被看作给定 `A` 成立的证据和 `B` 成立的证据，返回 `C` 成立的证据。
这个同构有时也被称作*柯里化*（Currying）。右逆的证明需要外延性：

{% raw %}<pre class="Agda"><a id="currying"></a><a id="26102" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#26102" class="Function">currying</a> <a id="26111" class="Symbol">:</a> <a id="26113" class="Symbol">∀</a> <a id="26115" class="Symbol">{</a><a id="26116" href="plfa.Connectives.html#26116" class="Bound">A</a> <a id="26118" href="plfa.Connectives.html#26118" class="Bound">B</a> <a id="26120" href="plfa.Connectives.html#26120" class="Bound">C</a> <a id="26122" class="Symbol">:</a> <a id="26124" class="PrimitiveType">Set</a><a id="26127" class="Symbol">}</a> <a id="26129" class="Symbol">→</a> <a id="26131" class="Symbol">(</a><a id="26132" href="plfa.Connectives.html#26116" class="Bound">A</a> <a id="26134" class="Symbol">→</a> <a id="26136" href="plfa.Connectives.html#26118" class="Bound">B</a> <a id="26138" class="Symbol">→</a> <a id="26140" href="plfa.Connectives.html#26120" class="Bound">C</a><a id="26141" class="Symbol">)</a> <a id="26143" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5843" class="Record Operator">≃</a> <a id="26145" class="Symbol">(</a><a id="26146" href="plfa.Connectives.html#26116" class="Bound">A</a> <a id="26148" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="26150" href="plfa.Connectives.html#26118" class="Bound">B</a> <a id="26152" class="Symbol">→</a> <a id="26154" href="plfa.Connectives.html#26120" class="Bound">C</a><a id="26155" class="Symbol">)</a>
<a id="26157" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#26102" class="Function">currying</a> <a id="26166" class="Symbol">=</a>
  <a id="26170" class="Keyword">record</a>
    <a id="26181" class="Symbol">{</a> <a id="26183" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5883" class="Field">to</a>      <a id="26191" class="Symbol">=</a>  <a id="26194" class="Symbol">λ{</a> <a id="26197" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#26197" class="Bound">f</a> <a id="26199" class="Symbol">→</a> <a id="26201" class="Symbol">λ{</a> <a id="26204" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="26206" href="plfa.Connectives.html#26206" class="Bound">x</a> <a id="26208" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="26210" href="plfa.Connectives.html#26210" class="Bound">y</a> <a id="26212" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="26214" class="Symbol">→</a> <a id="26216" href="plfa.Connectives.html#26197" class="Bound">f</a> <a id="26218" href="plfa.Connectives.html#26206" class="Bound">x</a> <a id="26220" href="plfa.Connectives.html#26210" class="Bound">y</a> <a id="26222" class="Symbol">}}</a>
    <a id="26229" class="Symbol">;</a> <a id="26231" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5900" class="Field">from</a>    <a id="26239" class="Symbol">=</a>  <a id="26242" class="Symbol">λ{</a> <a id="26245" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#26245" class="Bound">g</a> <a id="26247" class="Symbol">→</a> <a id="26249" class="Symbol">λ{</a> <a id="26252" href="plfa.Connectives.html#26252" class="Bound">x</a> <a id="26254" class="Symbol">→</a> <a id="26256" class="Symbol">λ{</a> <a id="26259" href="plfa.Connectives.html#26259" class="Bound">y</a> <a id="26261" class="Symbol">→</a> <a id="26263" href="plfa.Connectives.html#26245" class="Bound">g</a> <a id="26265" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="26267" href="plfa.Connectives.html#26252" class="Bound">x</a> <a id="26269" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="26271" href="plfa.Connectives.html#26259" class="Bound">y</a> <a id="26273" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="26275" class="Symbol">}}}</a>
    <a id="26283" class="Symbol">;</a> <a id="26285" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5917" class="Field">from∘to</a> <a id="26293" class="Symbol">=</a>  <a id="26296" class="Symbol">λ{</a> <a id="26299" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#26299" class="Bound">f</a> <a id="26301" class="Symbol">→</a> <a id="26303" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="26308" class="Symbol">}</a>
    <a id="26314" class="Symbol">;</a> <a id="26316" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5959" class="Field">to∘from</a> <a id="26324" class="Symbol">=</a>  <a id="26327" class="Symbol">λ{</a> <a id="26330" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#26330" class="Bound">g</a> <a id="26332" class="Symbol">→</a> <a id="26334" href="plfa.Isomorphism.html#3758" class="Postulate">extensionality</a> <a id="26349" class="Symbol">λ{</a> <a id="26352" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="26354" href="plfa.Connectives.html#26354" class="Bound">x</a> <a id="26356" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="26358" href="plfa.Connectives.html#26358" class="Bound">y</a> <a id="26360" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="26362" class="Symbol">→</a> <a id="26364" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="26369" class="Symbol">}}</a>
    <a id="26376" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
Currying tells us that instead of a function that takes a pair of arguments,
we can have a function that takes the first argument and returns a function that
expects the second argument.  Thus, for instance, our way of writing addition
{:/}

柯里化告诉我们，如果一个函数有取一个数据对作为参数，
那么我们可以构造一个函数，取第一个参数，返回一个取第二个参数，返回最终结果的函数。
因此，举例来说，下面表示加法的形式：

    _+_ : ℕ → ℕ → ℕ

{::comment}
is isomorphic to a function that accepts a pair of arguments:
{:/}

和下面的一个带有一个数据对作为参数的函数是同构的：

    _+′_ : (ℕ × ℕ) → ℕ

{::comment}
Agda is optimised for currying, so `2 + 3` abbreviates `_+_ 2 3`.
In a language optimised for pairing, we would instead take `2 +′ 3` as
an abbreviation for `_+′_ ⟨ 2 , 3 ⟩`.
{:/}

Agda 对柯里化进行了优化，因此 `2 + 3` 是 `_+_ 2 3` 的简写。在一个对有序对进行优化的语言里，
`2 +′ 3` 可能是 `_+′_ ⟨ 2 , 3 ⟩` 的简写。

{::comment}
Corresponding to the law
{:/}

对应如下的定律：

    p ^ (n + m) = (p ^ n) * (p ^ m)

{::comment}
we have the isomorphism:
{:/}

我们有如下的同构：

    (A ⊎ B) → C  ≃  (A → C) × (B → C)

{::comment}
That is, the assertion that if either `A` holds or `B` holds then `C` holds
is the same as the assertion that if `A` holds then `C` holds and if
`B` holds then `C` holds.  The proof of the left inverse requires extensionality:
{:/}

命题如果 `A` 成立或者 `B` 成立，那么 `C` 成立，和命题如果 `A` 成立，那么 `C` 成立以及
如果 `B` 成立，那么 `C` 成立，是一样的。左逆的证明需要外延性：

{% raw %}<pre class="Agda"><a id="→-distrib-⊎"></a><a id="27692" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#27692" class="Function">→-distrib-⊎</a> <a id="27704" class="Symbol">:</a> <a id="27706" class="Symbol">∀</a> <a id="27708" class="Symbol">{</a><a id="27709" href="plfa.Connectives.html#27709" class="Bound">A</a> <a id="27711" href="plfa.Connectives.html#27711" class="Bound">B</a> <a id="27713" href="plfa.Connectives.html#27713" class="Bound">C</a> <a id="27715" class="Symbol">:</a> <a id="27717" class="PrimitiveType">Set</a><a id="27720" class="Symbol">}</a> <a id="27722" class="Symbol">→</a> <a id="27724" class="Symbol">(</a><a id="27725" href="plfa.Connectives.html#27709" class="Bound">A</a> <a id="27727" href="plfa.Connectives.html#14050" class="Datatype Operator">⊎</a> <a id="27729" href="plfa.Connectives.html#27711" class="Bound">B</a> <a id="27731" class="Symbol">→</a> <a id="27733" href="plfa.Connectives.html#27713" class="Bound">C</a><a id="27734" class="Symbol">)</a> <a id="27736" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5843" class="Record Operator">≃</a> <a id="27738" class="Symbol">((</a><a id="27740" href="plfa.Connectives.html#27709" class="Bound">A</a> <a id="27742" class="Symbol">→</a> <a id="27744" href="plfa.Connectives.html#27713" class="Bound">C</a><a id="27745" class="Symbol">)</a> <a id="27747" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="27749" class="Symbol">(</a><a id="27750" href="plfa.Connectives.html#27711" class="Bound">B</a> <a id="27752" class="Symbol">→</a> <a id="27754" href="plfa.Connectives.html#27713" class="Bound">C</a><a id="27755" class="Symbol">))</a>
<a id="27758" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#27692" class="Function">→-distrib-⊎</a> <a id="27770" class="Symbol">=</a>
  <a id="27774" class="Keyword">record</a>
    <a id="27785" class="Symbol">{</a> <a id="27787" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5883" class="Field">to</a>      <a id="27795" class="Symbol">=</a> <a id="27797" class="Symbol">λ{</a> <a id="27800" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#27800" class="Bound">f</a> <a id="27802" class="Symbol">→</a> <a id="27804" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="27806" href="plfa.Connectives.html#27800" class="Bound">f</a> <a id="27808" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="27810" href="plfa.Connectives.html#14081" class="InductiveConstructor">inj₁</a> <a id="27815" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="27817" href="plfa.Connectives.html#27800" class="Bound">f</a> <a id="27819" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="27821" href="plfa.Connectives.html#14123" class="InductiveConstructor">inj₂</a> <a id="27826" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="27828" class="Symbol">}</a>
    <a id="27834" class="Symbol">;</a> <a id="27836" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5900" class="Field">from</a>    <a id="27844" class="Symbol">=</a> <a id="27846" class="Symbol">λ{</a> <a id="27849" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="27851" href="plfa.Connectives.html#27851" class="Bound">g</a> <a id="27853" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="27855" href="plfa.Connectives.html#27855" class="Bound">h</a> <a id="27857" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="27859" class="Symbol">→</a> <a id="27861" class="Symbol">λ{</a> <a id="27864" class="Symbol">(</a><a id="27865" href="plfa.Connectives.html#14081" class="InductiveConstructor">inj₁</a> <a id="27870" href="plfa.Connectives.html#27870" class="Bound">x</a><a id="27871" class="Symbol">)</a> <a id="27873" class="Symbol">→</a> <a id="27875" href="plfa.Connectives.html#27851" class="Bound">g</a> <a id="27877" href="plfa.Connectives.html#27870" class="Bound">x</a> <a id="27879" class="Symbol">;</a> <a id="27881" class="Symbol">(</a><a id="27882" href="plfa.Connectives.html#14123" class="InductiveConstructor">inj₂</a> <a id="27887" href="plfa.Connectives.html#27887" class="Bound">y</a><a id="27888" class="Symbol">)</a> <a id="27890" class="Symbol">→</a> <a id="27892" href="plfa.Connectives.html#27855" class="Bound">h</a> <a id="27894" href="plfa.Connectives.html#27887" class="Bound">y</a> <a id="27896" class="Symbol">}</a> <a id="27898" class="Symbol">}</a>
    <a id="27904" class="Symbol">;</a> <a id="27906" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5917" class="Field">from∘to</a> <a id="27914" class="Symbol">=</a> <a id="27916" class="Symbol">λ{</a> <a id="27919" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#27919" class="Bound">f</a> <a id="27921" class="Symbol">→</a> <a id="27923" href="plfa.Isomorphism.html#3758" class="Postulate">extensionality</a> <a id="27938" class="Symbol">λ{</a> <a id="27941" class="Symbol">(</a><a id="27942" href="plfa.Connectives.html#14081" class="InductiveConstructor">inj₁</a> <a id="27947" href="plfa.Connectives.html#27947" class="Bound">x</a><a id="27948" class="Symbol">)</a> <a id="27950" class="Symbol">→</a> <a id="27952" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="27957" class="Symbol">;</a> <a id="27959" class="Symbol">(</a><a id="27960" href="plfa.Connectives.html#14123" class="InductiveConstructor">inj₂</a> <a id="27965" href="plfa.Connectives.html#27965" class="Bound">y</a><a id="27966" class="Symbol">)</a> <a id="27968" class="Symbol">→</a> <a id="27970" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="27975" class="Symbol">}</a> <a id="27977" class="Symbol">}</a>
    <a id="27983" class="Symbol">;</a> <a id="27985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5959" class="Field">to∘from</a> <a id="27993" class="Symbol">=</a> <a id="27995" class="Symbol">λ{</a> <a id="27998" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="28000" href="plfa.Connectives.html#28000" class="Bound">g</a> <a id="28002" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="28004" href="plfa.Connectives.html#28004" class="Bound">h</a> <a id="28006" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="28008" class="Symbol">→</a> <a id="28010" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="28015" class="Symbol">}</a>
    <a id="28021" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
Corresponding to the law
{:/}

对应如下的定律：

    (p * n) ^ m = (p ^ m) * (n ^ m)

{::comment}
we have the isomorphism:
{:/}

我们有如下的同构：

    A → B × C  ≃  (A → B) × (A → C)

{::comment}
That is, the assertion that if `A` holds then `B` holds and `C` holds
is the same as the assertion that if `A` holds then `B` holds and if
`A` holds then `C` holds.  The proof of left inverse requires both extensionality
and the rule `η-×` for products:
{:/}

命题如果 `A` 成立，那么 `B` 成立和 `C` 成立，和命题如果 `A` 成立，那么 `B` 成立以及
如果 `A` 成立，那么 `C` 成立，是一样的。左逆的证明需要外延性和积的 `η-×` 规则：

{% raw %}<pre class="Agda"><a id="→-distrib-×"></a><a id="28590" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#28590" class="Function">→-distrib-×</a> <a id="28602" class="Symbol">:</a> <a id="28604" class="Symbol">∀</a> <a id="28606" class="Symbol">{</a><a id="28607" href="plfa.Connectives.html#28607" class="Bound">A</a> <a id="28609" href="plfa.Connectives.html#28609" class="Bound">B</a> <a id="28611" href="plfa.Connectives.html#28611" class="Bound">C</a> <a id="28613" class="Symbol">:</a> <a id="28615" class="PrimitiveType">Set</a><a id="28618" class="Symbol">}</a> <a id="28620" class="Symbol">→</a> <a id="28622" class="Symbol">(</a><a id="28623" href="plfa.Connectives.html#28607" class="Bound">A</a> <a id="28625" class="Symbol">→</a> <a id="28627" href="plfa.Connectives.html#28609" class="Bound">B</a> <a id="28629" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="28631" href="plfa.Connectives.html#28611" class="Bound">C</a><a id="28632" class="Symbol">)</a> <a id="28634" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5843" class="Record Operator">≃</a> <a id="28636" class="Symbol">(</a><a id="28637" href="plfa.Connectives.html#28607" class="Bound">A</a> <a id="28639" class="Symbol">→</a> <a id="28641" href="plfa.Connectives.html#28609" class="Bound">B</a><a id="28642" class="Symbol">)</a> <a id="28644" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="28646" class="Symbol">(</a><a id="28647" href="plfa.Connectives.html#28607" class="Bound">A</a> <a id="28649" class="Symbol">→</a> <a id="28651" href="plfa.Connectives.html#28611" class="Bound">C</a><a id="28652" class="Symbol">)</a>
<a id="28654" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#28590" class="Function">→-distrib-×</a> <a id="28666" class="Symbol">=</a>
  <a id="28670" class="Keyword">record</a>
    <a id="28681" class="Symbol">{</a> <a id="28683" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5883" class="Field">to</a>      <a id="28691" class="Symbol">=</a> <a id="28693" class="Symbol">λ{</a> <a id="28696" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#28696" class="Bound">f</a> <a id="28698" class="Symbol">→</a> <a id="28700" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="28702" href="plfa.Connectives.html#2185" class="Function">proj₁</a> <a id="28708" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="28710" href="plfa.Connectives.html#28696" class="Bound">f</a> <a id="28712" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="28714" href="plfa.Connectives.html#2254" class="Function">proj₂</a> <a id="28720" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="28722" href="plfa.Connectives.html#28696" class="Bound">f</a> <a id="28724" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="28726" class="Symbol">}</a>
    <a id="28732" class="Symbol">;</a> <a id="28734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5900" class="Field">from</a>    <a id="28742" class="Symbol">=</a> <a id="28744" class="Symbol">λ{</a> <a id="28747" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="28749" href="plfa.Connectives.html#28749" class="Bound">g</a> <a id="28751" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="28753" href="plfa.Connectives.html#28753" class="Bound">h</a> <a id="28755" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="28757" class="Symbol">→</a> <a id="28759" class="Symbol">λ</a> <a id="28761" href="plfa.Connectives.html#28761" class="Bound">x</a> <a id="28763" class="Symbol">→</a> <a id="28765" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="28767" href="plfa.Connectives.html#28749" class="Bound">g</a> <a id="28769" href="plfa.Connectives.html#28761" class="Bound">x</a> <a id="28771" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="28773" href="plfa.Connectives.html#28753" class="Bound">h</a> <a id="28775" href="plfa.Connectives.html#28761" class="Bound">x</a> <a id="28777" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="28779" class="Symbol">}</a>
    <a id="28785" class="Symbol">;</a> <a id="28787" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5917" class="Field">from∘to</a> <a id="28795" class="Symbol">=</a> <a id="28797" class="Symbol">λ{</a> <a id="28800" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#28800" class="Bound">f</a> <a id="28802" class="Symbol">→</a> <a id="28804" href="plfa.Isomorphism.html#3758" class="Postulate">extensionality</a> <a id="28819" class="Symbol">λ{</a> <a id="28822" href="plfa.Connectives.html#28822" class="Bound">x</a> <a id="28824" class="Symbol">→</a> <a id="28826" href="plfa.Connectives.html#4979" class="Function">η-×</a> <a id="28830" class="Symbol">(</a><a id="28831" href="plfa.Connectives.html#28800" class="Bound">f</a> <a id="28833" href="plfa.Connectives.html#28822" class="Bound">x</a><a id="28834" class="Symbol">)</a> <a id="28836" class="Symbol">}</a> <a id="28838" class="Symbol">}</a>
    <a id="28844" class="Symbol">;</a> <a id="28846" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5959" class="Field">to∘from</a> <a id="28854" class="Symbol">=</a> <a id="28856" class="Symbol">λ{</a> <a id="28859" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="28861" href="plfa.Connectives.html#28861" class="Bound">g</a> <a id="28863" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="28865" href="plfa.Connectives.html#28865" class="Bound">h</a> <a id="28867" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="28869" class="Symbol">→</a> <a id="28871" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="28876" class="Symbol">}</a>
    <a id="28882" class="Symbol">}</a>
</pre>{% endraw %}

{::comment}
## Distribution
{:/}

## 分配律

{::comment}
Products distribute over sum, up to isomorphism.  The code to validate
this fact is similar in structure to our previous results:
{:/}

在同构意义下，积对于和满足分配律。验证这条形式的代码和之前的证明相似：

{% raw %}<pre class="Agda"><a id="×-distrib-⊎"></a><a id="29121" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#29121" class="Function">×-distrib-⊎</a> <a id="29133" class="Symbol">:</a> <a id="29135" class="Symbol">∀</a> <a id="29137" class="Symbol">{</a><a id="29138" href="plfa.Connectives.html#29138" class="Bound">A</a> <a id="29140" href="plfa.Connectives.html#29140" class="Bound">B</a> <a id="29142" href="plfa.Connectives.html#29142" class="Bound">C</a> <a id="29144" class="Symbol">:</a> <a id="29146" class="PrimitiveType">Set</a><a id="29149" class="Symbol">}</a> <a id="29151" class="Symbol">→</a> <a id="29153" class="Symbol">(</a><a id="29154" href="plfa.Connectives.html#29138" class="Bound">A</a> <a id="29156" href="plfa.Connectives.html#14050" class="Datatype Operator">⊎</a> <a id="29158" href="plfa.Connectives.html#29140" class="Bound">B</a><a id="29159" class="Symbol">)</a> <a id="29161" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="29163" href="plfa.Connectives.html#29142" class="Bound">C</a> <a id="29165" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5843" class="Record Operator">≃</a> <a id="29167" class="Symbol">(</a><a id="29168" href="plfa.Connectives.html#29138" class="Bound">A</a> <a id="29170" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="29172" href="plfa.Connectives.html#29142" class="Bound">C</a><a id="29173" class="Symbol">)</a> <a id="29175" href="plfa.Connectives.html#14050" class="Datatype Operator">⊎</a> <a id="29177" class="Symbol">(</a><a id="29178" href="plfa.Connectives.html#29140" class="Bound">B</a> <a id="29180" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="29182" href="plfa.Connectives.html#29142" class="Bound">C</a><a id="29183" class="Symbol">)</a>
<a id="29185" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#29121" class="Function">×-distrib-⊎</a> <a id="29197" class="Symbol">=</a>
  <a id="29201" class="Keyword">record</a>
    <a id="29212" class="Symbol">{</a> <a id="29214" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5883" class="Field">to</a>      <a id="29222" class="Symbol">=</a> <a id="29224" class="Symbol">λ{</a> <a id="29227" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="29229" href="plfa.Connectives.html#14081" class="InductiveConstructor">inj₁</a> <a id="29234" href="plfa.Connectives.html#29234" class="Bound">x</a> <a id="29236" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29238" href="plfa.Connectives.html#29238" class="Bound">z</a> <a id="29240" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="29242" class="Symbol">→</a> <a id="29244" class="Symbol">(</a><a id="29245" href="plfa.Connectives.html#14081" class="InductiveConstructor">inj₁</a> <a id="29250" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="29252" href="plfa.Connectives.html#29234" class="Bound">x</a> <a id="29254" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29256" href="plfa.Connectives.html#29238" class="Bound">z</a> <a id="29258" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a><a id="29259" class="Symbol">)</a>
                 <a id="29278" class="Symbol">;</a> <a id="29280" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="29282" href="plfa.Connectives.html#14123" class="InductiveConstructor">inj₂</a> <a id="29287" href="plfa.Connectives.html#29287" class="Bound">y</a> <a id="29289" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29291" href="plfa.Connectives.html#29291" class="Bound">z</a> <a id="29293" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="29295" class="Symbol">→</a> <a id="29297" class="Symbol">(</a><a id="29298" href="plfa.Connectives.html#14123" class="InductiveConstructor">inj₂</a> <a id="29303" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="29305" href="plfa.Connectives.html#29287" class="Bound">y</a> <a id="29307" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29309" href="plfa.Connectives.html#29291" class="Bound">z</a> <a id="29311" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a><a id="29312" class="Symbol">)</a>
                 <a id="29331" class="Symbol">}</a>
    <a id="29337" class="Symbol">;</a> <a id="29339" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5900" class="Field">from</a>    <a id="29347" class="Symbol">=</a> <a id="29349" class="Symbol">λ{</a> <a id="29352" class="Symbol">(</a><a id="29353" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14081" class="InductiveConstructor">inj₁</a> <a id="29358" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="29360" href="plfa.Connectives.html#29360" class="Bound">x</a> <a id="29362" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29364" href="plfa.Connectives.html#29364" class="Bound">z</a> <a id="29366" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a><a id="29367" class="Symbol">)</a> <a id="29369" class="Symbol">→</a> <a id="29371" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="29373" href="plfa.Connectives.html#14081" class="InductiveConstructor">inj₁</a> <a id="29378" href="plfa.Connectives.html#29360" class="Bound">x</a> <a id="29380" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29382" href="plfa.Connectives.html#29364" class="Bound">z</a> <a id="29384" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a>
                 <a id="29403" class="Symbol">;</a> <a id="29405" class="Symbol">(</a><a id="29406" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14123" class="InductiveConstructor">inj₂</a> <a id="29411" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="29413" href="plfa.Connectives.html#29413" class="Bound">y</a> <a id="29415" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29417" href="plfa.Connectives.html#29417" class="Bound">z</a> <a id="29419" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a><a id="29420" class="Symbol">)</a> <a id="29422" class="Symbol">→</a> <a id="29424" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="29426" href="plfa.Connectives.html#14123" class="InductiveConstructor">inj₂</a> <a id="29431" href="plfa.Connectives.html#29413" class="Bound">y</a> <a id="29433" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29435" href="plfa.Connectives.html#29417" class="Bound">z</a> <a id="29437" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a>
                 <a id="29456" class="Symbol">}</a>
    <a id="29462" class="Symbol">;</a> <a id="29464" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5917" class="Field">from∘to</a> <a id="29472" class="Symbol">=</a> <a id="29474" class="Symbol">λ{</a> <a id="29477" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="29479" href="plfa.Connectives.html#14081" class="InductiveConstructor">inj₁</a> <a id="29484" href="plfa.Connectives.html#29484" class="Bound">x</a> <a id="29486" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29488" href="plfa.Connectives.html#29488" class="Bound">z</a> <a id="29490" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="29492" class="Symbol">→</a> <a id="29494" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="29516" class="Symbol">;</a> <a id="29518" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="29520" href="plfa.Connectives.html#14123" class="InductiveConstructor">inj₂</a> <a id="29525" href="plfa.Connectives.html#29525" class="Bound">y</a> <a id="29527" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29529" href="plfa.Connectives.html#29529" class="Bound">z</a> <a id="29531" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="29533" class="Symbol">→</a> <a id="29535" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="29557" class="Symbol">}</a>
    <a id="29563" class="Symbol">;</a> <a id="29565" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5959" class="Field">to∘from</a> <a id="29573" class="Symbol">=</a> <a id="29575" class="Symbol">λ{</a> <a id="29578" class="Symbol">(</a><a id="29579" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14081" class="InductiveConstructor">inj₁</a> <a id="29584" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="29586" href="plfa.Connectives.html#29586" class="Bound">x</a> <a id="29588" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29590" href="plfa.Connectives.html#29590" class="Bound">z</a> <a id="29592" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a><a id="29593" class="Symbol">)</a> <a id="29595" class="Symbol">→</a> <a id="29597" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="29619" class="Symbol">;</a> <a id="29621" class="Symbol">(</a><a id="29622" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14123" class="InductiveConstructor">inj₂</a> <a id="29627" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="29629" href="plfa.Connectives.html#29629" class="Bound">y</a> <a id="29631" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29633" href="plfa.Connectives.html#29633" class="Bound">z</a> <a id="29635" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a><a id="29636" class="Symbol">)</a> <a id="29638" class="Symbol">→</a> <a id="29640" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="29662" class="Symbol">}</a>
    <a id="29668" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
Sums do not distribute over products up to isomorphism, but it is an embedding:
{:/}

和对于积不满足分配律，但满足嵌入：

{% raw %}<pre class="Agda"><a id="⊎-distrib-×"></a><a id="29796" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#29796" class="Function">⊎-distrib-×</a> <a id="29808" class="Symbol">:</a> <a id="29810" class="Symbol">∀</a> <a id="29812" class="Symbol">{</a><a id="29813" href="plfa.Connectives.html#29813" class="Bound">A</a> <a id="29815" href="plfa.Connectives.html#29815" class="Bound">B</a> <a id="29817" href="plfa.Connectives.html#29817" class="Bound">C</a> <a id="29819" class="Symbol">:</a> <a id="29821" class="PrimitiveType">Set</a><a id="29824" class="Symbol">}</a> <a id="29826" class="Symbol">→</a> <a id="29828" class="Symbol">(</a><a id="29829" href="plfa.Connectives.html#29813" class="Bound">A</a> <a id="29831" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="29833" href="plfa.Connectives.html#29815" class="Bound">B</a><a id="29834" class="Symbol">)</a> <a id="29836" href="plfa.Connectives.html#14050" class="Datatype Operator">⊎</a> <a id="29838" href="plfa.Connectives.html#29817" class="Bound">C</a> <a id="29840" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11919" class="Record Operator">≲</a> <a id="29842" class="Symbol">(</a><a id="29843" href="plfa.Connectives.html#29813" class="Bound">A</a> <a id="29845" href="plfa.Connectives.html#14050" class="Datatype Operator">⊎</a> <a id="29847" href="plfa.Connectives.html#29817" class="Bound">C</a><a id="29848" class="Symbol">)</a> <a id="29850" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="29852" class="Symbol">(</a><a id="29853" href="plfa.Connectives.html#29815" class="Bound">B</a> <a id="29855" href="plfa.Connectives.html#14050" class="Datatype Operator">⊎</a> <a id="29857" href="plfa.Connectives.html#29817" class="Bound">C</a><a id="29858" class="Symbol">)</a>
<a id="29860" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#29796" class="Function">⊎-distrib-×</a> <a id="29872" class="Symbol">=</a>
  <a id="29876" class="Keyword">record</a>
    <a id="29887" class="Symbol">{</a> <a id="29889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11959" class="Field">to</a>      <a id="29897" class="Symbol">=</a> <a id="29899" class="Symbol">λ{</a> <a id="29902" class="Symbol">(</a><a id="29903" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14081" class="InductiveConstructor">inj₁</a> <a id="29908" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="29910" href="plfa.Connectives.html#29910" class="Bound">x</a> <a id="29912" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29914" href="plfa.Connectives.html#29914" class="Bound">y</a> <a id="29916" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a><a id="29917" class="Symbol">)</a> <a id="29919" class="Symbol">→</a> <a id="29921" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="29923" href="plfa.Connectives.html#14081" class="InductiveConstructor">inj₁</a> <a id="29928" href="plfa.Connectives.html#29910" class="Bound">x</a> <a id="29930" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29932" href="plfa.Connectives.html#14081" class="InductiveConstructor">inj₁</a> <a id="29937" href="plfa.Connectives.html#29914" class="Bound">y</a> <a id="29939" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a>
                 <a id="29958" class="Symbol">;</a> <a id="29960" class="Symbol">(</a><a id="29961" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14123" class="InductiveConstructor">inj₂</a> <a id="29966" href="plfa.Connectives.html#29966" class="Bound">z</a><a id="29967" class="Symbol">)</a>         <a id="29977" class="Symbol">→</a> <a id="29979" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="29981" href="plfa.Connectives.html#14123" class="InductiveConstructor">inj₂</a> <a id="29986" href="plfa.Connectives.html#29966" class="Bound">z</a> <a id="29988" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29990" href="plfa.Connectives.html#14123" class="InductiveConstructor">inj₂</a> <a id="29995" href="plfa.Connectives.html#29966" class="Bound">z</a> <a id="29997" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a>
                 <a id="30016" class="Symbol">}</a>
    <a id="30022" class="Symbol">;</a> <a id="30024" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11979" class="Field">from</a>    <a id="30032" class="Symbol">=</a> <a id="30034" class="Symbol">λ{</a> <a id="30037" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="30039" href="plfa.Connectives.html#14081" class="InductiveConstructor">inj₁</a> <a id="30044" href="plfa.Connectives.html#30044" class="Bound">x</a> <a id="30046" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="30048" href="plfa.Connectives.html#14081" class="InductiveConstructor">inj₁</a> <a id="30053" href="plfa.Connectives.html#30053" class="Bound">y</a> <a id="30055" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="30057" class="Symbol">→</a> <a id="30059" class="Symbol">(</a><a id="30060" href="plfa.Connectives.html#14081" class="InductiveConstructor">inj₁</a> <a id="30065" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="30067" href="plfa.Connectives.html#30044" class="Bound">x</a> <a id="30069" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="30071" href="plfa.Connectives.html#30053" class="Bound">y</a> <a id="30073" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a><a id="30074" class="Symbol">)</a>
                 <a id="30093" class="Symbol">;</a> <a id="30095" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="30097" href="plfa.Connectives.html#14081" class="InductiveConstructor">inj₁</a> <a id="30102" href="plfa.Connectives.html#30102" class="Bound">x</a> <a id="30104" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="30106" href="plfa.Connectives.html#14123" class="InductiveConstructor">inj₂</a> <a id="30111" href="plfa.Connectives.html#30111" class="Bound">z</a> <a id="30113" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="30115" class="Symbol">→</a> <a id="30117" class="Symbol">(</a><a id="30118" href="plfa.Connectives.html#14123" class="InductiveConstructor">inj₂</a> <a id="30123" href="plfa.Connectives.html#30111" class="Bound">z</a><a id="30124" class="Symbol">)</a>
                 <a id="30143" class="Symbol">;</a> <a id="30145" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="30147" href="plfa.Connectives.html#14123" class="InductiveConstructor">inj₂</a> <a id="30152" href="plfa.Connectives.html#30152" class="Bound">z</a> <a id="30154" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="30156" class="Symbol">_</a>      <a id="30163" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="30165" class="Symbol">→</a> <a id="30167" class="Symbol">(</a><a id="30168" href="plfa.Connectives.html#14123" class="InductiveConstructor">inj₂</a> <a id="30173" href="plfa.Connectives.html#30152" class="Bound">z</a><a id="30174" class="Symbol">)</a>
                 <a id="30193" class="Symbol">}</a>
    <a id="30199" class="Symbol">;</a> <a id="30201" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11999" class="Field">from∘to</a> <a id="30209" class="Symbol">=</a> <a id="30211" class="Symbol">λ{</a> <a id="30214" class="Symbol">(</a><a id="30215" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14081" class="InductiveConstructor">inj₁</a> <a id="30220" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="30222" href="plfa.Connectives.html#30222" class="Bound">x</a> <a id="30224" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="30226" href="plfa.Connectives.html#30226" class="Bound">y</a> <a id="30228" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a><a id="30229" class="Symbol">)</a> <a id="30231" class="Symbol">→</a> <a id="30233" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="30255" class="Symbol">;</a> <a id="30257" class="Symbol">(</a><a id="30258" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14123" class="InductiveConstructor">inj₂</a> <a id="30263" href="plfa.Connectives.html#30263" class="Bound">z</a><a id="30264" class="Symbol">)</a>         <a id="30274" class="Symbol">→</a> <a id="30276" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="30298" class="Symbol">}</a>
    <a id="30304" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
Note that there is a choice in how we write the `from` function.
As given, it takes `⟨ inj₂ z , inj₂ z′ ⟩` to `inj₂ z`, but it is
easy to write a variant that instead returns `inj₂ z′`.  We have
an embedding rather than an isomorphism because the
`from` function must discard either `z` or `z′` in this case.
{:/}

我们在定义 `from` 函数的时候可以有选择。给定的定义中，它将 `⟨ inj₂ z , inj₂ z′ ⟩`
转换为 `inj₂ z`，但我们也可以返回 `inj₂ z′` 作为嵌入证明的变种。我们在这里只能证明嵌入，
而不能证明同构，因为 `from` 函数必须丢弃 `z` 或者 `z′` 其中的一个。

{::comment}
In the usual approach to logic, both of the distribution laws
are given as equivalences, where each side implies the other:
{:/}

在一般的逻辑学方法中，两条分配律都以等价的形式给出，每一边都蕴涵了另一边：

    A × (B ⊎ C) ⇔ (A × B) ⊎ (A × C)
    A ⊎ (B × C) ⇔ (A ⊎ B) × (A ⊎ C)

{::comment}
But when we consider the functions that provide evidence for these
implications, then the first corresponds to an isomorphism while the
second only corresponds to an embedding, revealing a sense in which
one of these laws is "more true" than the other.
{:/}

但当我们考虑提供上述蕴涵证明的函数时，第一条对应同构而第二条只能对应嵌入，
揭示了有些定理比另一个更加的”正确“。


{::comment}
#### Exercise `⊎-weak-×` (recommended)
{:/}

#### 练习 `⊎-weak-×` （推荐）

{::comment}
Show that the following property holds:
{:/}

证明如下性质成立：

{% raw %}<pre class="Agda"><a id="31535" class="Keyword">postulate</a>
  <a id="⊎-weak-×"></a><a id="31547" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#31547" class="Postulate">⊎-weak-×</a> <a id="31556" class="Symbol">:</a> <a id="31558" class="Symbol">∀</a> <a id="31560" class="Symbol">{</a><a id="31561" href="plfa.Connectives.html#31561" class="Bound">A</a> <a id="31563" href="plfa.Connectives.html#31563" class="Bound">B</a> <a id="31565" href="plfa.Connectives.html#31565" class="Bound">C</a> <a id="31567" class="Symbol">:</a> <a id="31569" class="PrimitiveType">Set</a><a id="31572" class="Symbol">}</a> <a id="31574" class="Symbol">→</a> <a id="31576" class="Symbol">(</a><a id="31577" href="plfa.Connectives.html#31561" class="Bound">A</a> <a id="31579" href="plfa.Connectives.html#14050" class="Datatype Operator">⊎</a> <a id="31581" href="plfa.Connectives.html#31563" class="Bound">B</a><a id="31582" class="Symbol">)</a> <a id="31584" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="31586" href="plfa.Connectives.html#31565" class="Bound">C</a> <a id="31588" class="Symbol">→</a> <a id="31590" href="plfa.Connectives.html#31561" class="Bound">A</a> <a id="31592" href="plfa.Connectives.html#14050" class="Datatype Operator">⊎</a> <a id="31594" class="Symbol">(</a><a id="31595" href="plfa.Connectives.html#31563" class="Bound">B</a> <a id="31597" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="31599" href="plfa.Connectives.html#31565" class="Bound">C</a><a id="31600" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
This is called a _weak distributive law_. Give the corresponding
distributive law, and explain how it relates to the weak version.
{:/}

这被称为*弱分配律*。给出相对应的分配律，并解释分配律与弱分配律的关系。

{::comment}
{% raw %}<pre class="Agda"><a id="31810" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="31847" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}


{::comment}
#### Exercise `⊎×-implies-×⊎`
{:/}

#### 练习 `⊎×-implies-×⊎`

{::comment}
Show that a disjunct of conjuncts implies a conjunct of disjuncts:
{:/}

证明合取的析取蕴涵了析取的合取：

{% raw %}<pre class="Agda"><a id="32047" class="Keyword">postulate</a>
  <a id="⊎×-implies-×⊎"></a><a id="32059" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#32059" class="Postulate">⊎×-implies-×⊎</a> <a id="32073" class="Symbol">:</a> <a id="32075" class="Symbol">∀</a> <a id="32077" class="Symbol">{</a><a id="32078" href="plfa.Connectives.html#32078" class="Bound">A</a> <a id="32080" href="plfa.Connectives.html#32080" class="Bound">B</a> <a id="32082" href="plfa.Connectives.html#32082" class="Bound">C</a> <a id="32084" href="plfa.Connectives.html#32084" class="Bound">D</a> <a id="32086" class="Symbol">:</a> <a id="32088" class="PrimitiveType">Set</a><a id="32091" class="Symbol">}</a> <a id="32093" class="Symbol">→</a> <a id="32095" class="Symbol">(</a><a id="32096" href="plfa.Connectives.html#32078" class="Bound">A</a> <a id="32098" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="32100" href="plfa.Connectives.html#32080" class="Bound">B</a><a id="32101" class="Symbol">)</a> <a id="32103" href="plfa.Connectives.html#14050" class="Datatype Operator">⊎</a> <a id="32105" class="Symbol">(</a><a id="32106" href="plfa.Connectives.html#32082" class="Bound">C</a> <a id="32108" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="32110" href="plfa.Connectives.html#32084" class="Bound">D</a><a id="32111" class="Symbol">)</a> <a id="32113" class="Symbol">→</a> <a id="32115" class="Symbol">(</a><a id="32116" href="plfa.Connectives.html#32078" class="Bound">A</a> <a id="32118" href="plfa.Connectives.html#14050" class="Datatype Operator">⊎</a> <a id="32120" href="plfa.Connectives.html#32082" class="Bound">C</a><a id="32121" class="Symbol">)</a> <a id="32123" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="32125" class="Symbol">(</a><a id="32126" href="plfa.Connectives.html#32080" class="Bound">B</a> <a id="32128" href="plfa.Connectives.html#14050" class="Datatype Operator">⊎</a> <a id="32130" href="plfa.Connectives.html#32084" class="Bound">D</a><a id="32131" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Does the converse hold? If so, prove; if not, give a counterexample.
{:/}

反命题成立吗？如果成立，给出证明；如果不成立，给出反例。

{::comment}
{% raw %}<pre class="Agda"><a id="32271" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="32308" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
## Standard library
{:/}

## 标准库

{::comment}
Definitions similar to those in this chapter can be found in the standard library:
{:/}

标准库中可以找到与本章节中相似的定义：

{% raw %}<pre class="Agda"><a id="32498" class="Keyword">import</a> <a id="32505" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="32518" class="Keyword">using</a> <a id="32524" class="Symbol">(</a><a id="32525" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">_×_</a><a id="32528" class="Symbol">;</a> <a id="32530" href="Agda.Builtin.Sigma.html#225" class="Field">proj₁</a><a id="32535" class="Symbol">;</a> <a id="32537" href="Agda.Builtin.Sigma.html#237" class="Field">proj₂</a><a id="32542" class="Symbol">)</a> <a id="32544" class="Keyword">renaming</a> <a id="32553" class="Symbol">(</a><a id="32554" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a> <a id="32558" class="Symbol">to</a> <a id="32561" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="32566" class="Symbol">)</a>
<a id="32568" class="Keyword">import</a> <a id="32575" href="https://agda.github.io/agda-stdlib/v1.1/Data.Unit.html" class="Module">Data.Unit</a> <a id="32585" class="Keyword">using</a> <a id="32591" class="Symbol">(</a><a id="32592" href="Agda.Builtin.Unit.html#137" class="Record">⊤</a><a id="32593" class="Symbol">;</a> <a id="32595" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a><a id="32597" class="Symbol">)</a>
<a id="32599" class="Keyword">import</a> <a id="32606" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.html" class="Module">Data.Sum</a> <a id="32615" class="Keyword">using</a> <a id="32621" class="Symbol">(</a><a id="32622" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">_⊎_</a><a id="32625" class="Symbol">;</a> <a id="32627" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a><a id="32631" class="Symbol">;</a> <a id="32633" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a><a id="32637" class="Symbol">)</a> <a id="32639" class="Keyword">renaming</a> <a id="32648" class="Symbol">(</a><a id="32649" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#798" class="Function Operator">[_,_]</a> <a id="32655" class="Symbol">to</a> <a id="32658" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#798" class="Function Operator">case-⊎</a><a id="32664" class="Symbol">)</a>
<a id="32666" class="Keyword">import</a> <a id="32673" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html" class="Module">Data.Empty</a> <a id="32684" class="Keyword">using</a> <a id="32690" class="Symbol">(</a><a id="32691" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a><a id="32692" class="Symbol">;</a> <a id="32694" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a><a id="32700" class="Symbol">)</a>
<a id="32702" class="Keyword">import</a> <a id="32709" href="https://agda.github.io/agda-stdlib/v1.1/Function.Equivalence.html" class="Module">Function.Equivalence</a> <a id="32730" class="Keyword">using</a> <a id="32736" class="Symbol">(</a><a id="32737" href="https://agda.github.io/agda-stdlib/v1.1/Function.Equivalence.html#971" class="Function Operator">_⇔_</a><a id="32740" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
The standard library constructs pairs with `_,_` whereas we use `⟨_,_⟩`.
The former makes it convenient to build triples or larger tuples from pairs,
permitting `a , b , c` to stand for `(a , (b , c))`.  But it conflicts with
other useful notations, such as `[_,_]` to construct a list of two elements in
Chapter [Lists]({{ site.baseurl }}/Lists/)
and `Γ , A` to extend environments in
Chapter [DeBruijn]({{ site.baseurl }}/DeBruijn/).
The standard library `_⇔_` is similar to ours, but the one in the
standard library is less convenient, since it is parameterised with
respect to an arbitrary notion of equivalence.
{:/}

标准库中使用 `_,_` 构造数据对，而我们使用 `⟨_,_⟩`。前者在从数据对构造三元对或者更大的
元组时更加的方便，允许 `a , b , c` 作为 `(a, (b , c))` 的记法。但它与其他有用的记法相冲突，
比如说 [Lists][plfa.Lists] 中的 `[_,_]` 记法表示两个元素的列表，
或者 [DeBruijn][plfa.DeBruijn] 章节中的 `Γ , A` 来表示环境的扩展。
标准库中的 `_⇔_` 和我们的相似，但使用起来比较不便，
因为它可以根据任意的相等性定义进行参数化。

## Unicode

{::comment}
This chapter uses the following unicode:

    ×  U+00D7  MULTIPLICATION SIGN (\x)
    ⊎  U+228E  MULTISET UNION (\u+)
    ⊤  U+22A4  DOWN TACK (\top)
    ⊥  U+22A5  UP TACK (\bot)
    η  U+03B7  GREEK SMALL LETTER ETA (\eta)
    ₁  U+2081  SUBSCRIPT ONE (\_1)
    ₂  U+2082  SUBSCRIPT TWO (\_2)
    ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>)
{:/}

本章节使用下列 Unicode：

    ×  U+00D7  乘法符号 (\x)
    ⊎  U+228E  多重集并集 (\u+)
    ⊤  U+22A4  向下图钉 (\top)
    ⊥  U+22A5  向上图钉 (\bot)
    η  U+03B7  希腊小写字母 ETA (\eta)
    ₁  U+2081  下标 1 (\_1)
    ₂  U+2082  下标 2 (\_2)
    ⇔  U+21D4  左右双箭头 (\<=>)
