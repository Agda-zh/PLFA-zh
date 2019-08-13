---
src       : "src/plfa/Decidable.lagda.md"
title     : "Decidable: 布尔值与判定过程"
layout    : page
prev      : /Quantifiers/
permalink : /Decidable/
next      : /Lists/
translators : ["Fangyi Zhou"]
progress  : 100
---

{% raw %}<pre class="Agda"><a id="181" class="Keyword">module</a> <a id="188" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}" class="Module">plfa.Decidable</a> <a id="203" class="Keyword">where</a>
</pre>{% endraw %}
{::comment}
We have a choice as to how to represent relations:
as an inductive data type of _evidence_ that the relation holds,
or as a function that _computes_ whether the relation holds.
Here we explore the relation between these choices.
We first explore the familiar notion of _booleans_,
but later discover that these are best avoided in favour
of a new notion of _decidable_.
{:/}

我们有两种不同的方式来表示关系：一是表示为由关系成立的*证明*（Evidence）所构成的数据类型；
二是表示为一个*计算*（Compute）关系是否成立的函数。在本章中，我们将探讨这两种方式之间的关系。
我们首先研究大家熟悉的*布尔值*（Boolean）记法，但是之后我们会发现，相较布尔值记法，
使用一种新的*可判定性*（Decidable）记法将会是更好的选择。

{::comment}
## Imports
{:/}

## 导入

{% raw %}<pre class="Agda"><a id="828" class="Keyword">import</a> <a id="835" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="873" class="Symbol">as</a> <a id="876" class="Module">Eq</a>
<a id="879" class="Keyword">open</a> <a id="884" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="887" class="Keyword">using</a> <a id="893" class="Symbol">(</a><a id="894" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="897" class="Symbol">;</a> <a id="899" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="903" class="Symbol">)</a>
<a id="905" class="Keyword">open</a> <a id="910" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2499" class="Module">Eq.≡-Reasoning</a>
<a id="925" class="Keyword">open</a> <a id="930" class="Keyword">import</a> <a id="937" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="946" class="Keyword">using</a> <a id="952" class="Symbol">(</a><a id="953" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="954" class="Symbol">;</a> <a id="956" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="960" class="Symbol">;</a> <a id="962" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="965" class="Symbol">)</a>
<a id="967" class="Keyword">open</a> <a id="972" class="Keyword">import</a> <a id="979" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="992" class="Keyword">using</a> <a id="998" class="Symbol">(</a><a id="999" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">_×_</a><a id="1002" class="Symbol">)</a> <a id="1004" class="Keyword">renaming</a> <a id="1013" class="Symbol">(</a><a id="1014" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a> <a id="1018" class="Symbol">to</a> <a id="1021" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="1026" class="Symbol">)</a>
<a id="1028" class="Keyword">open</a> <a id="1033" class="Keyword">import</a> <a id="1040" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.html" class="Module">Data.Sum</a> <a id="1049" class="Keyword">using</a> <a id="1055" class="Symbol">(</a><a id="1056" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">_⊎_</a><a id="1059" class="Symbol">;</a> <a id="1061" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a><a id="1065" class="Symbol">;</a> <a id="1067" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a><a id="1071" class="Symbol">)</a>
<a id="1073" class="Keyword">open</a> <a id="1078" class="Keyword">import</a> <a id="1085" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="1102" class="Keyword">using</a> <a id="1108" class="Symbol">(</a><a id="1109" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="1111" class="Symbol">)</a>
<a id="1113" class="Keyword">open</a> <a id="1118" class="Keyword">import</a> <a id="1125" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="1151" class="Keyword">using</a> <a id="1157" class="Symbol">()</a>
  <a id="1162" class="Keyword">renaming</a> <a id="1171" class="Symbol">(</a><a id="1172" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#809" class="Function">contradiction</a> <a id="1186" class="Symbol">to</a> <a id="1189" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#809" class="Function">¬¬-intro</a><a id="1197" class="Symbol">)</a>
<a id="1199" class="Keyword">open</a> <a id="1204" class="Keyword">import</a> <a id="1211" href="https://agda.github.io/agda-stdlib/v1.1/Data.Unit.html" class="Module">Data.Unit</a> <a id="1221" class="Keyword">using</a> <a id="1227" class="Symbol">(</a><a id="1228" href="Agda.Builtin.Unit.html#137" class="Record">⊤</a><a id="1229" class="Symbol">;</a> <a id="1231" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a><a id="1233" class="Symbol">)</a>
<a id="1235" class="Keyword">open</a> <a id="1240" class="Keyword">import</a> <a id="1247" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html" class="Module">Data.Empty</a> <a id="1258" class="Keyword">using</a> <a id="1264" class="Symbol">(</a><a id="1265" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a><a id="1266" class="Symbol">;</a> <a id="1268" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a><a id="1274" class="Symbol">)</a>
<a id="1276" class="Keyword">open</a> <a id="1281" class="Keyword">import</a> <a id="1288" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}" class="Module">plfa.Relations</a> <a id="1303" class="Keyword">using</a> <a id="1309" class="Symbol">(</a><a id="1310" href="plfa.Relations.html#26522" class="Datatype Operator">_&lt;_</a><a id="1313" class="Symbol">;</a> <a id="1315" href="plfa.Relations.html#26549" class="InductiveConstructor">z&lt;s</a><a id="1318" class="Symbol">;</a> <a id="1320" href="plfa.Relations.html#26606" class="InductiveConstructor">s&lt;s</a><a id="1323" class="Symbol">)</a>
<a id="1325" class="Keyword">open</a> <a id="1330" class="Keyword">import</a> <a id="1337" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}" class="Module">plfa.Isomorphism</a> <a id="1354" class="Keyword">using</a> <a id="1360" class="Symbol">(</a><a id="1361" href="plfa.Isomorphism.html#15256" class="Record Operator">_⇔_</a><a id="1364" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
## Evidence vs Computation
{:/}

## 证据 vs 计算

{::comment}
Recall that Chapter [Relations]({{ site.baseurl }}/Relations/)
defined comparison as an inductive datatype,
which provides _evidence_ that one number
is less than or equal to another:
{:/}

回忆我们在 [Relations]({{ site.baseurl }}/Relations/)
章节中将比较定义为一个归纳数据类型，其提供了一个数小于或等于另外一个数的证明：

{% raw %}<pre class="Agda"><a id="1725" class="Keyword">infix</a> <a id="1731" class="Number">4</a> <a id="1733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#1743" class="Datatype Operator">_≤_</a>

<a id="1738" class="Keyword">data</a> <a id="_≤_"></a><a id="1743" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#1743" class="Datatype Operator">_≤_</a> <a id="1747" class="Symbol">:</a> <a id="1749" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="1751" class="Symbol">→</a> <a id="1753" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="1755" class="Symbol">→</a> <a id="1757" class="PrimitiveType">Set</a> <a id="1761" class="Keyword">where</a>

  <a id="_≤_.z≤n"></a><a id="1770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#1770" class="InductiveConstructor">z≤n</a> <a id="1774" class="Symbol">:</a> <a id="1776" class="Symbol">∀</a> <a id="1778" class="Symbol">{</a><a id="1779" href="plfa.Decidable.html#1779" class="Bound">n</a> <a id="1781" class="Symbol">:</a> <a id="1783" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1784" class="Symbol">}</a>
      <a id="1792" class="Comment">--------</a>
    <a id="1805" class="Symbol">→</a> <a id="1807" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="1812" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#1743" class="Datatype Operator">≤</a> <a id="1814" href="plfa.Decidable.html#1779" class="Bound">n</a>

  <a id="_≤_.s≤s"></a><a id="1819" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#1819" class="InductiveConstructor">s≤s</a> <a id="1823" class="Symbol">:</a> <a id="1825" class="Symbol">∀</a> <a id="1827" class="Symbol">{</a><a id="1828" href="plfa.Decidable.html#1828" class="Bound">m</a> <a id="1830" href="plfa.Decidable.html#1830" class="Bound">n</a> <a id="1832" class="Symbol">:</a> <a id="1834" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1835" class="Symbol">}</a>
    <a id="1841" class="Symbol">→</a> <a id="1843" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#1828" class="Bound">m</a> <a id="1845" href="plfa.Decidable.html#1743" class="Datatype Operator">≤</a> <a id="1847" href="plfa.Decidable.html#1830" class="Bound">n</a>
      <a id="1855" class="Comment">-------------</a>
    <a id="1873" class="Symbol">→</a> <a id="1875" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="1879" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#1828" class="Bound">m</a> <a id="1881" href="plfa.Decidable.html#1743" class="Datatype Operator">≤</a> <a id="1883" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="1887" href="plfa.Decidable.html#1830" class="Bound">n</a>
</pre>{% endraw %}
{::comment}
For example, we can provide evidence that `2 ≤ 4`,
and show there is no possible evidence that `4 ≤ 2`:
{:/}

举例来说，我们提供 `2 ≤ 4` 成立的证明，也可以证明没有 `4 ≤ 2` 成立的证明。

{% raw %}<pre class="Agda"><a id="2≤4"></a><a id="2068" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2068" class="Function">2≤4</a> <a id="2072" class="Symbol">:</a> <a id="2074" class="Number">2</a> <a id="2076" href="plfa.Decidable.html#1743" class="Datatype Operator">≤</a> <a id="2078" class="Number">4</a>
<a id="2080" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2068" class="Function">2≤4</a> <a id="2084" class="Symbol">=</a> <a id="2086" href="plfa.Decidable.html#1819" class="InductiveConstructor">s≤s</a> <a id="2090" class="Symbol">(</a><a id="2091" href="plfa.Decidable.html#1819" class="InductiveConstructor">s≤s</a> <a id="2095" href="plfa.Decidable.html#1770" class="InductiveConstructor">z≤n</a><a id="2098" class="Symbol">)</a>

<a id="¬4≤2"></a><a id="2101" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2101" class="Function">¬4≤2</a> <a id="2106" class="Symbol">:</a> <a id="2108" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="2110" class="Symbol">(</a><a id="2111" class="Number">4</a> <a id="2113" href="plfa.Decidable.html#1743" class="Datatype Operator">≤</a> <a id="2115" class="Number">2</a><a id="2116" class="Symbol">)</a>
<a id="2118" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2101" class="Function">¬4≤2</a> <a id="2123" class="Symbol">(</a><a id="2124" href="plfa.Decidable.html#1819" class="InductiveConstructor">s≤s</a> <a id="2128" class="Symbol">(</a><a id="2129" href="plfa.Decidable.html#1819" class="InductiveConstructor">s≤s</a> <a id="2133" class="Symbol">()))</a>
</pre>{% endraw %}
{::comment}
The occurrence of `()` attests to the fact that there is
no possible evidence for `2 ≤ 0`, which `z≤n` cannot match
(because `2` is not `zero`) and `s≤s` cannot match
(because `0` cannot match `suc n`).
{:/}

`()` 的出现表明了没有 `2 ≤ 0` 成立的证明：`z≤n` 不能匹配（因为 `2` 不是
`zero`），`s≤s` 也不能匹配（因为 `0` 不能匹配 `suc n`）。

{::comment}
An alternative, which may seem more familiar, is to define a
type of booleans:
{:/}

作为替代的定义，我们可以定义一个大家可能比较熟悉的布尔类型：

{% raw %}<pre class="Agda"><a id="2589" class="Keyword">data</a> <a id="Bool"></a><a id="2594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2594" class="Datatype">Bool</a> <a id="2599" class="Symbol">:</a> <a id="2601" class="PrimitiveType">Set</a> <a id="2605" class="Keyword">where</a>
  <a id="Bool.true"></a><a id="2613" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2613" class="InductiveConstructor">true</a>  <a id="2619" class="Symbol">:</a> <a id="2621" href="plfa.Decidable.html#2594" class="Datatype">Bool</a>
  <a id="Bool.false"></a><a id="2628" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2628" class="InductiveConstructor">false</a> <a id="2634" class="Symbol">:</a> <a id="2636" href="plfa.Decidable.html#2594" class="Datatype">Bool</a>
</pre>{% endraw %}
{::comment}
Given booleans, we can define a function of two numbers that
_computes_ to `true` if the comparison holds and to `false` otherwise:
{:/}

给定了布尔类型，我们可以定义一个两个数的函数在比较关系成立时来*计算*出 `true`，
否则计算出 `false`：

{% raw %}<pre class="Agda"><a id="2861" class="Keyword">infix</a> <a id="2867" class="Number">4</a> <a id="2869" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2875" class="Function Operator">_≤ᵇ_</a>

<a id="_≤ᵇ_"></a><a id="2875" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2875" class="Function Operator">_≤ᵇ_</a> <a id="2880" class="Symbol">:</a> <a id="2882" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="2884" class="Symbol">→</a> <a id="2886" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="2888" class="Symbol">→</a> <a id="2890" href="plfa.Decidable.html#2594" class="Datatype">Bool</a>
<a id="2895" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="2900" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2875" class="Function Operator">≤ᵇ</a> <a id="2903" href="plfa.Decidable.html#2903" class="Bound">n</a>       <a id="2911" class="Symbol">=</a>  <a id="2914" href="plfa.Decidable.html#2613" class="InductiveConstructor">true</a>
<a id="2919" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="2923" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2923" class="Bound">m</a> <a id="2925" href="plfa.Decidable.html#2875" class="Function Operator">≤ᵇ</a> <a id="2928" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>   <a id="2935" class="Symbol">=</a>  <a id="2938" href="plfa.Decidable.html#2628" class="InductiveConstructor">false</a>
<a id="2944" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="2948" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2948" class="Bound">m</a> <a id="2950" href="plfa.Decidable.html#2875" class="Function Operator">≤ᵇ</a> <a id="2953" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="2957" href="plfa.Decidable.html#2957" class="Bound">n</a>  <a id="2960" class="Symbol">=</a>  <a id="2963" href="plfa.Decidable.html#2948" class="Bound">m</a> <a id="2965" href="plfa.Decidable.html#2875" class="Function Operator">≤ᵇ</a> <a id="2968" href="plfa.Decidable.html#2957" class="Bound">n</a>
</pre>{% endraw %}
{::comment}
The first and last clauses of this definition resemble the two
constructors of the corresponding inductive datatype, while the
middle clause arises because there is no possible evidence that
`suc m ≤ zero` for any `m`.
For example, we can compute that `2 ≤ᵇ 4` holds,
and we can compute that `4 ≤ᵇ 2` does not hold:
{:/}

定义中的第一条与最后一条与归纳数据类型中的两个构造子相对应。因为对于任意的 `m`，不可能出现
`suc m ≤ zero` 的证明，我们使用中间一条定义来表示。
举个例子，我们可以计算 `2 ≤ᵇ 4` 成立，也可以计算 `4 ≤ᵇ 2` 不成立：

{% raw %}<pre class="Agda"><a id="3440" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#3440" class="Function">_</a> <a id="3442" class="Symbol">:</a> <a id="3444" class="Symbol">(</a><a id="3445" class="Number">2</a> <a id="3447" href="plfa.Decidable.html#2875" class="Function Operator">≤ᵇ</a> <a id="3450" class="Number">4</a><a id="3451" class="Symbol">)</a> <a id="3453" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="3455" href="plfa.Decidable.html#2613" class="InductiveConstructor">true</a>
<a id="3460" class="Symbol">_</a> <a id="3462" class="Symbol">=</a>
  <a id="3466" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="3476" class="Number">2</a> <a id="3478" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2875" class="Function Operator">≤ᵇ</a> <a id="3481" class="Number">4</a>
  <a id="3485" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3493" class="Number">1</a> <a id="3495" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2875" class="Function Operator">≤ᵇ</a> <a id="3498" class="Number">3</a>
  <a id="3502" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3510" class="Number">0</a> <a id="3512" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2875" class="Function Operator">≤ᵇ</a> <a id="3515" class="Number">2</a>
  <a id="3519" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3527" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2613" class="InductiveConstructor">true</a>
  <a id="3534" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>

<a id="3537" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#3537" class="Function">_</a> <a id="3539" class="Symbol">:</a> <a id="3541" class="Symbol">(</a><a id="3542" class="Number">4</a> <a id="3544" href="plfa.Decidable.html#2875" class="Function Operator">≤ᵇ</a> <a id="3547" class="Number">2</a><a id="3548" class="Symbol">)</a> <a id="3550" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="3552" href="plfa.Decidable.html#2628" class="InductiveConstructor">false</a>
<a id="3558" class="Symbol">_</a> <a id="3560" class="Symbol">=</a>
  <a id="3564" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="3574" class="Number">4</a> <a id="3576" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2875" class="Function Operator">≤ᵇ</a> <a id="3579" class="Number">2</a>
  <a id="3583" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3591" class="Number">3</a> <a id="3593" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2875" class="Function Operator">≤ᵇ</a> <a id="3596" class="Number">1</a>
  <a id="3600" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3608" class="Number">2</a> <a id="3610" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2875" class="Function Operator">≤ᵇ</a> <a id="3613" class="Number">0</a>
  <a id="3617" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3625" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2628" class="InductiveConstructor">false</a>
  <a id="3633" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}
{::comment}
In the first case, it takes two steps to reduce the first argument to zero,
and one more step to compute true, corresponding to the two uses of `s≤s`
and the one use of `z≤n` when providing evidence that `2 ≤ 4`.
In the second case, it takes two steps to reduce the second argument to zero,
and one more step to compute false, corresponding to the two uses of `s≤s`
and the one use of `()` when showing there can be no evidence that `4 ≤ 2`.
{:/}

在第一种情况中，我们需要两步来将第一个参数降低到 0，再用一步来计算出真，这对应着我们需要
使用两次 `s≤s` 和一次 `z≤n` 来证明 `2 ≤ 4`。
在第二种情况中，我们需要两步来将第二个参数降低到 0，再用一步来计算出假，这对应着我们需要
使用两次 `s≤s` 和一次 `()` 来说明没有 `4 ≤ 2` 的证明。

{::comment}
## Relating evidence and computation
{:/}

## 将证明与计算相联系

{::comment}
We would hope to be able to show these two approaches are related, and
indeed we can.  First, we define a function that lets us map from the
computation world to the evidence world:
{:/}

我们希望能够证明这两种方法是有联系的，而我们的确可以。
首先，我们定义一个函数来把计算世界映射到证明世界：

{% raw %}<pre class="Agda"><a id="T"></a><a id="4594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#4594" class="Function">T</a> <a id="4596" class="Symbol">:</a> <a id="4598" href="plfa.Decidable.html#2594" class="Datatype">Bool</a> <a id="4603" class="Symbol">→</a> <a id="4605" class="PrimitiveType">Set</a>
<a id="4609" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#4594" class="Function">T</a> <a id="4611" href="plfa.Decidable.html#2613" class="InductiveConstructor">true</a>   <a id="4618" class="Symbol">=</a>  <a id="4621" href="Agda.Builtin.Unit.html#137" class="Record">⊤</a>
<a id="4623" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#4594" class="Function">T</a> <a id="4625" href="plfa.Decidable.html#2628" class="InductiveConstructor">false</a>  <a id="4632" class="Symbol">=</a>  <a id="4635" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>
</pre>{% endraw %}
{::comment}
Recall that `⊤` is the unit type which contains the single element `tt`,
and the `⊥` is the empty type which contains no values.  (Also note that
`T` is a capital letter t, and distinct from `⊤`.)  If `b` is of type `Bool`,
then `tt` provides evidence that `T b` holds if `b` is true, while there is
no possible evidence that `T b` holds if `b` is false.
{:/}

回忆到 `⊤` 是只有一个元素 `tt` 的单元类型，`⊥` 是没有值的空类型。（注意 `T` 是大写字母 `t`，
与 `⊤` 不同。）如果 `b` 是 `Bool` 类型的，那么如果 `b` 为真，`tt` 可以提供 `T b` 成立的证明；
如果 `b` 为假，则不可能有 `T b` 成立的证明。

{::comment}
Another way to put this is that `T b` is inhabited exactly when `b ≡ true`
is inhabited.
In the forward direction, we need to do a case analysis on the boolean `b`:
{:/}

换句话说，`T b` 当且仅当 `b ≡ true` 成立时成立。在向前的方向，我们需要针对 `b` 进行情况分析：

{% raw %}<pre class="Agda"><a id="T→≡"></a><a id="5416" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#5416" class="Function">T→≡</a> <a id="5420" class="Symbol">:</a> <a id="5422" class="Symbol">∀</a> <a id="5424" class="Symbol">(</a><a id="5425" href="plfa.Decidable.html#5425" class="Bound">b</a> <a id="5427" class="Symbol">:</a> <a id="5429" href="plfa.Decidable.html#2594" class="Datatype">Bool</a><a id="5433" class="Symbol">)</a> <a id="5435" class="Symbol">→</a> <a id="5437" href="plfa.Decidable.html#4594" class="Function">T</a> <a id="5439" href="plfa.Decidable.html#5425" class="Bound">b</a> <a id="5441" class="Symbol">→</a> <a id="5443" href="plfa.Decidable.html#5425" class="Bound">b</a> <a id="5445" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5447" href="plfa.Decidable.html#2613" class="InductiveConstructor">true</a>
<a id="5452" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#5416" class="Function">T→≡</a> <a id="5456" href="plfa.Decidable.html#2613" class="InductiveConstructor">true</a> <a id="5461" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a>   <a id="5466" class="Symbol">=</a>  <a id="5469" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="5474" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#5416" class="Function">T→≡</a> <a id="5478" href="plfa.Decidable.html#2628" class="InductiveConstructor">false</a> <a id="5484" class="Symbol">()</a>
</pre>{% endraw %}
{::comment}
If `b` is true then `T b` is inhabited by `tt` and `b ≡ true` is inhabited
by `refl`, while if `b` is false then `T b` in uninhabited.
{:/}

如果 `b` 为真，那么 `T b` 由 `tt` 证明，`b ≡ true` 由 `refl` 证明。
当 `b` 为假，那么 `T b` 无法证明。

{::comment}
In the reverse direction, there is no need for a case analysis on the boolean `b`:
{:/}

在向后的方向，不需要针对布尔值 `b` 的情况分析：

{% raw %}<pre class="Agda"><a id="≡→T"></a><a id="5856" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#5856" class="Function">≡→T</a> <a id="5860" class="Symbol">:</a> <a id="5862" class="Symbol">∀</a> <a id="5864" class="Symbol">{</a><a id="5865" href="plfa.Decidable.html#5865" class="Bound">b</a> <a id="5867" class="Symbol">:</a> <a id="5869" href="plfa.Decidable.html#2594" class="Datatype">Bool</a><a id="5873" class="Symbol">}</a> <a id="5875" class="Symbol">→</a> <a id="5877" href="plfa.Decidable.html#5865" class="Bound">b</a> <a id="5879" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5881" href="plfa.Decidable.html#2613" class="InductiveConstructor">true</a> <a id="5886" class="Symbol">→</a> <a id="5888" href="plfa.Decidable.html#4594" class="Function">T</a> <a id="5890" href="plfa.Decidable.html#5865" class="Bound">b</a>
<a id="5892" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#5856" class="Function">≡→T</a> <a id="5896" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>  <a id="5902" class="Symbol">=</a>  <a id="5905" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a>
</pre>{% endraw %}
{::comment}
If `b ≡ true` is inhabited by `refl` we know that `b` is `true` and
hence `T b` is inhabited by `tt`.
{:/}

如果 `b ≡ true` 由 `refl` 证明，我们知道 `b` 是 `true`，因此 `T b` 由 `tt` 证明。

{::comment}
Now we can show that `T (m ≤ᵇ n)` is inhabited exactly when `m ≤ n` is inhabited.
{:/}

现在我们可以证明 `T (m ≤ᵇ n)` 当且仅当 `m ≤ n` 成立时成立。

{::comment}
In the forward direction, we consider the three clauses in the definition
of `_≤ᵇ_`:
{:/}

在向前的方向，我们考虑 `_≤ᵇ_` 定义中的三条语句：

{% raw %}<pre class="Agda"><a id="≤ᵇ→≤"></a><a id="6378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#6378" class="Function">≤ᵇ→≤</a> <a id="6383" class="Symbol">:</a> <a id="6385" class="Symbol">∀</a> <a id="6387" class="Symbol">(</a><a id="6388" href="plfa.Decidable.html#6388" class="Bound">m</a> <a id="6390" href="plfa.Decidable.html#6390" class="Bound">n</a> <a id="6392" class="Symbol">:</a> <a id="6394" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="6395" class="Symbol">)</a> <a id="6397" class="Symbol">→</a> <a id="6399" href="plfa.Decidable.html#4594" class="Function">T</a> <a id="6401" class="Symbol">(</a><a id="6402" href="plfa.Decidable.html#6388" class="Bound">m</a> <a id="6404" href="plfa.Decidable.html#2875" class="Function Operator">≤ᵇ</a> <a id="6407" href="plfa.Decidable.html#6390" class="Bound">n</a><a id="6408" class="Symbol">)</a> <a id="6410" class="Symbol">→</a> <a id="6412" href="plfa.Decidable.html#6388" class="Bound">m</a> <a id="6414" href="plfa.Decidable.html#1743" class="Datatype Operator">≤</a> <a id="6416" href="plfa.Decidable.html#6390" class="Bound">n</a>
<a id="6418" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#6378" class="Function">≤ᵇ→≤</a> <a id="6423" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="6431" href="plfa.Decidable.html#6431" class="Bound">n</a>       <a id="6439" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a>  <a id="6443" class="Symbol">=</a>  <a id="6446" href="plfa.Decidable.html#1770" class="InductiveConstructor">z≤n</a>
<a id="6450" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#6378" class="Function">≤ᵇ→≤</a> <a id="6455" class="Symbol">(</a><a id="6456" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="6460" href="plfa.Decidable.html#6460" class="Bound">m</a><a id="6461" class="Symbol">)</a> <a id="6463" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="6471" class="Symbol">()</a>
<a id="6474" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#6378" class="Function">≤ᵇ→≤</a> <a id="6479" class="Symbol">(</a><a id="6480" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="6484" href="plfa.Decidable.html#6484" class="Bound">m</a><a id="6485" class="Symbol">)</a> <a id="6487" class="Symbol">(</a><a id="6488" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="6492" href="plfa.Decidable.html#6492" class="Bound">n</a><a id="6493" class="Symbol">)</a> <a id="6495" href="plfa.Decidable.html#6495" class="Bound">t</a>   <a id="6499" class="Symbol">=</a>  <a id="6502" href="plfa.Decidable.html#1819" class="InductiveConstructor">s≤s</a> <a id="6506" class="Symbol">(</a><a id="6507" href="plfa.Decidable.html#6378" class="Function">≤ᵇ→≤</a> <a id="6512" href="plfa.Decidable.html#6484" class="Bound">m</a> <a id="6514" href="plfa.Decidable.html#6492" class="Bound">n</a> <a id="6516" href="plfa.Decidable.html#6495" class="Bound">t</a><a id="6517" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
In the first clause, we immediately have that `zero ≤ᵇ n` is
true, so `T (m ≤ᵇ n)` is evidenced by `tt`, and correspondingly `m ≤ n` is
evidenced by `z≤n`. In the middle clause, we immediately have that
`suc m ≤ᵇ zero` is false, and hence `T (m ≤ᵇ n)` is empty, so we need
not provide evidence that `m ≤ n`, which is just as well since there is no
such evidence.  In the last clause, we have that `suc m ≤ᵇ suc n` recurses
to `m ≤ᵇ n`.  We let `t` be the evidence of `T (suc m ≤ᵇ suc n)` if it exists,
which, by definition of `_≤ᵇ_`, will also be evidence of `T (m ≤ᵇ n)`.
We recursively invoke the function to get evidence that `m ≤ n`, which
`s≤s` converts to evidence that `suc m ≤ suc n`.
{:/}

第一条语句中，我们立即可以得出 `zero ≤ᵇ n` 为真，所以 `T (m ≤ᵇ n)` 由 `tt` 而得，
相对应地 `m ≤ n` 由 `z≤n` 而证明。在中间的语句中，我们立刻得出 `suc m ≤ᵇ zero` 为假，则
`T (m ≤ᵇ n)` 为空，因此我们无需证明 `m ≤ n`，同时也不存在这样的证明。在最后的语句中，我们对于
`suc m ≤ᵇ suc n` 递归至 `m ≤ᵇ n`。令 `t` 为 `T (suc m ≤ᵇ suc n)` 的证明，如果其存在。
根据 `_≤ᵇ_` 的定义，这也是 `T (m ≤ᵇ n)` 的证明。我们递归地应用函数来获得 `m ≤ n` 的证明，再使用
`s≤s` 将其转换成为 `suc m ≤ suc n` 的证明。

{::comment}
In the reverse direction, we consider the possible forms of evidence
that `m ≤ n`:
{:/}

在向后的方向，我们考虑 `m ≤ n` 成立证明的可能形式：

{% raw %}<pre class="Agda"><a id="≤→≤ᵇ"></a><a id="7718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#7718" class="Function">≤→≤ᵇ</a> <a id="7723" class="Symbol">:</a> <a id="7725" class="Symbol">∀</a> <a id="7727" class="Symbol">{</a><a id="7728" href="plfa.Decidable.html#7728" class="Bound">m</a> <a id="7730" href="plfa.Decidable.html#7730" class="Bound">n</a> <a id="7732" class="Symbol">:</a> <a id="7734" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="7735" class="Symbol">}</a> <a id="7737" class="Symbol">→</a> <a id="7739" href="plfa.Decidable.html#7728" class="Bound">m</a> <a id="7741" href="plfa.Decidable.html#1743" class="Datatype Operator">≤</a> <a id="7743" href="plfa.Decidable.html#7730" class="Bound">n</a> <a id="7745" class="Symbol">→</a> <a id="7747" href="plfa.Decidable.html#4594" class="Function">T</a> <a id="7749" class="Symbol">(</a><a id="7750" href="plfa.Decidable.html#7728" class="Bound">m</a> <a id="7752" href="plfa.Decidable.html#2875" class="Function Operator">≤ᵇ</a> <a id="7755" href="plfa.Decidable.html#7730" class="Bound">n</a><a id="7756" class="Symbol">)</a>
<a id="7758" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#7718" class="Function">≤→≤ᵇ</a> <a id="7763" href="plfa.Decidable.html#1770" class="InductiveConstructor">z≤n</a>        <a id="7774" class="Symbol">=</a>  <a id="7777" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a>
<a id="7780" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#7718" class="Function">≤→≤ᵇ</a> <a id="7785" class="Symbol">(</a><a id="7786" href="plfa.Decidable.html#1819" class="InductiveConstructor">s≤s</a> <a id="7790" href="plfa.Decidable.html#7790" class="Bound">m≤n</a><a id="7793" class="Symbol">)</a>  <a id="7796" class="Symbol">=</a>  <a id="7799" href="plfa.Decidable.html#7718" class="Function">≤→≤ᵇ</a> <a id="7804" href="plfa.Decidable.html#7790" class="Bound">m≤n</a>
</pre>{% endraw %}
{::comment}
If the evidence is `z≤n` then we immediately have that `zero ≤ᵇ n` is
true, so `T (m ≤ᵇ n)` is evidenced by `tt`. If the evidence is `s≤s`
applied to `m≤n`, then `suc m ≤ᵇ suc n` reduces to `m ≤ᵇ n`, and we
may recursively invoke the function to produce evidence that `T (m ≤ᵇ n)`.
{:/}

如果证明是 `z≤n`，我们立即可以得到 `zero ≤ᵇ n` 为真，所以 `T (m ≤ᵇ n)` 由 `tt` 证明。
如果证明是 `s≤s` 作用于 `m≤n`，那么 `suc m ≤ᵇ suc n` 规约到 `m ≤ᵇ n`，我们可以递归地使用函数
来获得 `T (m ≤ᵇ n)` 的证明。

{::comment}
The forward proof has one more clause than the reverse proof,
precisely because in the forward proof we need clauses corresponding to
the comparison yielding both true and false, while in the reverse proof
we only need clauses corresponding to the case where there is evidence
that the comparison holds.  This is exactly why we tend to prefer the
evidence formulation to the computation formulation, because it allows
us to do less work: we consider only cases where the relation holds,
and can ignore those where it does not.
{:/}

向前方向的证明比向后方向的证明多一条语句，因为在向前方向的证明中我们需要考虑比较结果为真和假
的语句，而向后方向的证明只需要考虑比较成立的语句。这也是为什么我们比起计算的形式，更加偏爱证明的形式，
因为这样让我们做更少的工作：我们只需要考虑关系成立时的情况，而可以忽略不成立的情况。

{::comment}
On the other hand, sometimes the computation formulation may be just what
we want.  Given a non-obvious relation over large values, it might be
handy to have the computer work out the answer for us.  Fortunately,
rather than choosing between _evidence_ and _computation_,
there is a way to get the benefits of both.
{:/}

从另一个角度来说，有时计算的性质可能正是我们所需要的。面对一个大数值上的非显然关系，
使用电脑来计算出答案可能会更加方便。幸运的是，比起在*证明*或*计算*之中犹豫，
我们有一种更好的方法来兼取其优。

{::comment}
## The best of both worlds
{:/}

## 取二者之精华

{::comment}
A function that returns a boolean returns exactly a single bit of information:
does the relation hold or does it not? Conversely, the evidence approach tells
us exactly why the relation holds, but we are responsible for generating the
evidence.  But it is easy to define a type that combines the benefits of
both approaches.  It is called `Dec A`, where `Dec` is short for _decidable_:
{:/}

一个返回布尔值的函数提供恰好一比特的信息：这个关系成立或是不成立。相反地，证明的形式告诉我们
为什么这个关系成立，但却需要我们自行完成这个证明。不过，我们其实可以简单地定义一个类型来取二者之精华。
我们把它叫做：`Dec A`，其中 `Dec` 是*可判定的*（Decidable）的意思。

{% raw %}<pre class="Agda"><a id="10001" class="Keyword">data</a> <a id="Dec"></a><a id="10006" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#10006" class="Datatype">Dec</a> <a id="10010" class="Symbol">(</a><a id="10011" href="plfa.Decidable.html#10011" class="Bound">A</a> <a id="10013" class="Symbol">:</a> <a id="10015" class="PrimitiveType">Set</a><a id="10018" class="Symbol">)</a> <a id="10020" class="Symbol">:</a> <a id="10022" class="PrimitiveType">Set</a> <a id="10026" class="Keyword">where</a>
  <a id="Dec.yes"></a><a id="10034" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#10034" class="InductiveConstructor">yes</a> <a id="10038" class="Symbol">:</a>   <a id="10042" href="plfa.Decidable.html#10011" class="Bound">A</a> <a id="10044" class="Symbol">→</a> <a id="10046" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="10050" href="plfa.Decidable.html#10011" class="Bound">A</a>
  <a id="Dec.no"></a><a id="10054" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#10054" class="InductiveConstructor">no</a>  <a id="10058" class="Symbol">:</a> <a id="10060" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="10062" href="plfa.Decidable.html#10011" class="Bound">A</a> <a id="10064" class="Symbol">→</a> <a id="10066" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="10070" href="plfa.Decidable.html#10011" class="Bound">A</a>
</pre>{% endraw %}
{::comment}
Like booleans, the type has two constructors.  A value of type `Dec A`
is either of the form `yes x`, where `x` provides evidence that `A` holds,
or of the form `no ¬x`, where `¬x` provides evidence that `A` cannot hold
(that is, `¬x` is a function which given evidence of `A` yields a contradiction).
{:/}

正如布尔值，这个类型有两个构造子。一个 `Dec A` 类型的值要么是以 `yes x` 的形式，其中 `x` 提供 `A`
成立的证明，或者是以 `no ¬x` 的形式，其中 `x` 提供了 `A` 无法成立的证明。（也就是说，`¬x` 是一个给定
`A` 成立的证据，返回矛盾的函数）

{::comment}
For example, we define a function `_≤?_` which given two numbers decides whether one
is less than or equal to the other, and provides evidence to justify its conclusion.
{:/}

比如说，我们定义一个函数 `_≤?_`，给定两个数，判定是否一个数小于等于另一个，并提供证明来说明结论。

{::comment}
First, we introduce two functions useful for constructing evidence that
an inequality does not hold:
{:/}

首先，我们使用两个有用的函数，用于构造不等式不成立的证明：

{% raw %}<pre class="Agda"><a id="¬s≤z"></a><a id="10939" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#10939" class="Function">¬s≤z</a> <a id="10944" class="Symbol">:</a> <a id="10946" class="Symbol">∀</a> <a id="10948" class="Symbol">{</a><a id="10949" href="plfa.Decidable.html#10949" class="Bound">m</a> <a id="10951" class="Symbol">:</a> <a id="10953" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="10954" class="Symbol">}</a> <a id="10956" class="Symbol">→</a> <a id="10958" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="10960" class="Symbol">(</a><a id="10961" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="10965" href="plfa.Decidable.html#10949" class="Bound">m</a> <a id="10967" href="plfa.Decidable.html#1743" class="Datatype Operator">≤</a> <a id="10969" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="10973" class="Symbol">)</a>
<a id="10975" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#10939" class="Function">¬s≤z</a> <a id="10980" class="Symbol">()</a>

<a id="¬s≤s"></a><a id="10984" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#10984" class="Function">¬s≤s</a> <a id="10989" class="Symbol">:</a> <a id="10991" class="Symbol">∀</a> <a id="10993" class="Symbol">{</a><a id="10994" href="plfa.Decidable.html#10994" class="Bound">m</a> <a id="10996" href="plfa.Decidable.html#10996" class="Bound">n</a> <a id="10998" class="Symbol">:</a> <a id="11000" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11001" class="Symbol">}</a> <a id="11003" class="Symbol">→</a> <a id="11005" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="11007" class="Symbol">(</a><a id="11008" href="plfa.Decidable.html#10994" class="Bound">m</a> <a id="11010" href="plfa.Decidable.html#1743" class="Datatype Operator">≤</a> <a id="11012" href="plfa.Decidable.html#10996" class="Bound">n</a><a id="11013" class="Symbol">)</a> <a id="11015" class="Symbol">→</a> <a id="11017" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="11019" class="Symbol">(</a><a id="11020" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11024" href="plfa.Decidable.html#10994" class="Bound">m</a> <a id="11026" href="plfa.Decidable.html#1743" class="Datatype Operator">≤</a> <a id="11028" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11032" href="plfa.Decidable.html#10996" class="Bound">n</a><a id="11033" class="Symbol">)</a>
<a id="11035" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#10984" class="Function">¬s≤s</a> <a id="11040" href="plfa.Decidable.html#11040" class="Bound">¬m≤n</a> <a id="11045" class="Symbol">(</a><a id="11046" href="plfa.Decidable.html#1819" class="InductiveConstructor">s≤s</a> <a id="11050" href="plfa.Decidable.html#11050" class="Bound">m≤n</a><a id="11053" class="Symbol">)</a> <a id="11055" class="Symbol">=</a> <a id="11057" href="plfa.Decidable.html#11040" class="Bound">¬m≤n</a> <a id="11062" href="plfa.Decidable.html#11050" class="Bound">m≤n</a>
</pre>{% endraw %}
{::comment}
The first of these asserts that `¬ (suc m ≤ zero)`, and follows by
absurdity, since any evidence of inequality has the form `zero ≤ n`
or `suc m ≤ suc n`, neither of which match `suc m ≤ zero`. The second
of these takes evidence `¬m≤n` of `¬ (m ≤ n)` and returns a proof of
`¬ (suc m ≤ suc n)`.  Any evidence of `suc m ≤ suc n` must have the
form `s≤s m≤n` where `m≤n` is evidence that `m ≤ n`.  Hence, we have
a contradiction, evidenced by `¬m≤n m≤n`.
{:/}

第一个函数断言了 `¬ (suc m ≤ zero)`，由荒谬可得。因为每个不等式的成立证明必须是
`zero ≤ n` 或者 `suc m ≤ suc n` 的形式，两者都无法匹配 `suc m ≤ zero`。
第二个函数取 `¬ (m ≤ n)` 的证明 `¬m≤n`，返回 `¬ (suc m ≤ suc n)` 的证明。
所有形如 `suc m ≤ suc n` 的证明必须是以 `s≤s m≤n` 的形式给出。因此我们可以构造一个
矛盾，以 `¬m≤n m≤n` 来证明。

{::comment}
Using these, it is straightforward to decide an inequality:
{:/}

使用这些，我们可以直接的判定不等关系：

{% raw %}<pre class="Agda"><a id="_≤?_"></a><a id="11889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#11889" class="Function Operator">_≤?_</a> <a id="11894" class="Symbol">:</a> <a id="11896" class="Symbol">∀</a> <a id="11898" class="Symbol">(</a><a id="11899" href="plfa.Decidable.html#11899" class="Bound">m</a> <a id="11901" href="plfa.Decidable.html#11901" class="Bound">n</a> <a id="11903" class="Symbol">:</a> <a id="11905" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11906" class="Symbol">)</a> <a id="11908" class="Symbol">→</a> <a id="11910" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="11914" class="Symbol">(</a><a id="11915" href="plfa.Decidable.html#11899" class="Bound">m</a> <a id="11917" href="plfa.Decidable.html#1743" class="Datatype Operator">≤</a> <a id="11919" href="plfa.Decidable.html#11901" class="Bound">n</a><a id="11920" class="Symbol">)</a>
<a id="11922" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>  <a id="11928" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#11889" class="Function Operator">≤?</a> <a id="11931" href="plfa.Decidable.html#11931" class="Bound">n</a>                   <a id="11951" class="Symbol">=</a>  <a id="11954" href="plfa.Decidable.html#10034" class="InductiveConstructor">yes</a> <a id="11958" href="plfa.Decidable.html#1770" class="InductiveConstructor">z≤n</a>
<a id="11962" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11966" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#11966" class="Bound">m</a> <a id="11968" href="plfa.Decidable.html#11889" class="Function Operator">≤?</a> <a id="11971" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>                <a id="11991" class="Symbol">=</a>  <a id="11994" href="plfa.Decidable.html#10054" class="InductiveConstructor">no</a> <a id="11997" href="plfa.Decidable.html#10939" class="Function">¬s≤z</a>
<a id="12002" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="12006" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#12006" class="Bound">m</a> <a id="12008" href="plfa.Decidable.html#11889" class="Function Operator">≤?</a> <a id="12011" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="12015" href="plfa.Decidable.html#12015" class="Bound">n</a> <a id="12017" class="Keyword">with</a> <a id="12022" href="plfa.Decidable.html#12006" class="Bound">m</a> <a id="12024" href="plfa.Decidable.html#11889" class="Function Operator">≤?</a> <a id="12027" href="plfa.Decidable.html#12015" class="Bound">n</a>
<a id="12029" class="Symbol">...</a>               <a id="12047" class="Symbol">|</a> <a id="12049" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#10034" class="InductiveConstructor">yes</a> <a id="12053" href="plfa.Decidable.html#12053" class="Bound">m≤n</a>  <a id="12058" class="Symbol">=</a>  <a id="12061" href="plfa.Decidable.html#10034" class="InductiveConstructor">yes</a> <a id="12065" class="Symbol">(</a><a id="12066" href="plfa.Decidable.html#1819" class="InductiveConstructor">s≤s</a> <a id="12070" href="plfa.Decidable.html#12053" class="Bound">m≤n</a><a id="12073" class="Symbol">)</a>
<a id="12075" class="Symbol">...</a>               <a id="12093" class="Symbol">|</a> <a id="12095" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#10054" class="InductiveConstructor">no</a> <a id="12098" href="plfa.Decidable.html#12098" class="Bound">¬m≤n</a>  <a id="12104" class="Symbol">=</a>  <a id="12107" href="plfa.Decidable.html#10054" class="InductiveConstructor">no</a> <a id="12110" class="Symbol">(</a><a id="12111" href="plfa.Decidable.html#10984" class="Function">¬s≤s</a> <a id="12116" href="plfa.Decidable.html#12098" class="Bound">¬m≤n</a><a id="12120" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
As with `_≤ᵇ_`, the definition has three clauses.  In the first
clause, it is immediate that `zero ≤ n` holds, and it is evidenced by
`z≤n`.  In the second clause, it is immediate that `suc m ≤ zero` does
not hold, and it is evidenced by `¬s≤z`.
In the third clause, to decide whether `suc m ≤ suc n` holds we
recursively invoke `m ≤? n`.  There are two possibilities.  In the
`yes` case it returns evidence `m≤n` that `m ≤ n`, and `s≤s m≤n`
provides evidence that `suc m ≤ suc n`.  In the `no` case it returns
evidence `¬m≤n` that `¬ (m ≤ n)`, and `¬s≤s ¬m≤n` provides evidence
that `¬ (suc m ≤ suc n)`.
{:/}

与 `_≤ᵇ_` 一样，定义有三条语句。第一条语句中，`zero ≤ n` 立即成立，由 `z≤n` 证明。
第二条语句中，`suc m ≤ zero` 立即不成立，由 `¬s≤z` 证明。
第三条语句中，我们需要递归地应用 `m ≤? n`。有两种可能性，在 `yes` 的情况中，它会返回
`m ≤ n` 的证明 `m≤n`，所以 `s≤s m≤n` 即可作为 `suc m ≤ suc n` 的证明；在 `no` 的情况中，
它会返回 `¬ (m ≤ n)` 的证明 `¬m≤n`，所以 `¬s≤s ¬m≤n` 即可作为 `¬ (suc m ≤ suc n)` 的证明。

{::comment}
When we wrote `_≤ᵇ_`, we had to write two other functions, `≤ᵇ→≤` and `≤→≤ᵇ`,
in order to show that it was correct.  In contrast, the definition of `_≤?_`
proves itself correct, as attested to by its type.  The code of `_≤?_`
is far more compact than the combined code of `_≤ᵇ_`, `≤ᵇ→≤`, and `≤→≤ᵇ`.
As we will later show, if you really want the latter three, it is easy
to derive them from `_≤?_`.
{:/}

当我们写 `_≤ᵇ_` 时，我们必须写两个其他的函数 `≤ᵇ→≤` 和 `≤→≤ᵇ` 来证明其正确性。
作为对比，`_≤?_` 的定义自身就证明了其正确性，由类型即可得知。`_≤?_` 的代码也比
`_≤ᵇ_`、`≤ᵇ→≤` 和 `≤→≤ᵇ` 加起来要简洁的多。我们稍后将会证明，如果我们需要后三者，
我们亦可简单地从 `_≤?_` 中派生出来。

{::comment}
We can use our new function to _compute_ the _evidence_ that earlier we had to
think up on our own:
{:/}

我们可以使用我们新的函数来*计算*出我们之前需要自己想出来的*证明*。

{% raw %}<pre class="Agda"><a id="13791" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#13791" class="Function">_</a> <a id="13793" class="Symbol">:</a> <a id="13795" class="Number">2</a> <a id="13797" href="plfa.Decidable.html#11889" class="Function Operator">≤?</a> <a id="13800" class="Number">4</a> <a id="13802" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="13804" href="plfa.Decidable.html#10034" class="InductiveConstructor">yes</a> <a id="13808" class="Symbol">(</a><a id="13809" href="plfa.Decidable.html#1819" class="InductiveConstructor">s≤s</a> <a id="13813" class="Symbol">(</a><a id="13814" href="plfa.Decidable.html#1819" class="InductiveConstructor">s≤s</a> <a id="13818" href="plfa.Decidable.html#1770" class="InductiveConstructor">z≤n</a><a id="13821" class="Symbol">))</a>
<a id="13824" class="Symbol">_</a> <a id="13826" class="Symbol">=</a> <a id="13828" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="13834" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#13834" class="Function">_</a> <a id="13836" class="Symbol">:</a> <a id="13838" class="Number">4</a> <a id="13840" href="plfa.Decidable.html#11889" class="Function Operator">≤?</a> <a id="13843" class="Number">2</a> <a id="13845" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="13847" href="plfa.Decidable.html#10054" class="InductiveConstructor">no</a> <a id="13850" class="Symbol">(</a><a id="13851" href="plfa.Decidable.html#10984" class="Function">¬s≤s</a> <a id="13856" class="Symbol">(</a><a id="13857" href="plfa.Decidable.html#10984" class="Function">¬s≤s</a> <a id="13862" href="plfa.Decidable.html#10939" class="Function">¬s≤z</a><a id="13866" class="Symbol">))</a>
<a id="13869" class="Symbol">_</a> <a id="13871" class="Symbol">=</a> <a id="13873" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
You can check that Agda will indeed compute these values.  Typing
`C-c C-n` and providing `2 ≤? 4` or `4 ≤? 2` as the requested expression
causes Agda to print the values given above.
{:/}

你可以验证 Agda 的确计算出了这些值。输入 `C-c C-n` 并给出 `2 ≤? 4` 或者 `4 ≤? 2` 作为
需要的表达式，Agda 会输出如上的值。

{::comment}
(A subtlety: if we do not define `¬s≤z` and `¬s≤s` as top-level functions,
but instead use inline anonymous functions then Agda may have
trouble normalising evidence of negation.)
{:/}

（小细节：如果我们不把 `¬s≤z` 和 `¬s≤s` 作为顶层函数来定义，而是使用内嵌的匿名函数，
Agda 可能会在规范化否定的证明中出现问题。）


{::comment}
#### Exercise `_<?_` (recommended)
{:/}

#### 练习 `_<?_` （推荐）

{::comment}
Analogous to the function above, define a function to decide strict inequality:
{:/}

与上面的函数相似，定义一个判定严格不等性的函数：

{% raw %}<pre class="Agda"><a id="14647" class="Keyword">postulate</a>
  <a id="_&lt;?_"></a><a id="14659" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#14659" class="Postulate Operator">_&lt;?_</a> <a id="14664" class="Symbol">:</a> <a id="14666" class="Symbol">∀</a> <a id="14668" class="Symbol">(</a><a id="14669" href="plfa.Decidable.html#14669" class="Bound">m</a> <a id="14671" href="plfa.Decidable.html#14671" class="Bound">n</a> <a id="14673" class="Symbol">:</a> <a id="14675" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="14676" class="Symbol">)</a> <a id="14678" class="Symbol">→</a> <a id="14680" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="14684" class="Symbol">(</a><a id="14685" href="plfa.Decidable.html#14669" class="Bound">m</a> <a id="14687" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26522" class="Datatype Operator">&lt;</a> <a id="14689" href="plfa.Decidable.html#14671" class="Bound">n</a><a id="14690" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
{% raw %}<pre class="Agda"><a id="14713" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="14750" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
#### Exercise `_≡ℕ?_`
{:/}

#### 练习 `_≡ℕ?_`

{::comment}
Define a function to decide whether two naturals are equal:
{:/}

定义一个函数来判定两个自然数是否相等。

{% raw %}<pre class="Agda"><a id="14928" class="Keyword">postulate</a>
  <a id="_≡ℕ?_"></a><a id="14940" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#14940" class="Postulate Operator">_≡ℕ?_</a> <a id="14946" class="Symbol">:</a> <a id="14948" class="Symbol">∀</a> <a id="14950" class="Symbol">(</a><a id="14951" href="plfa.Decidable.html#14951" class="Bound">m</a> <a id="14953" href="plfa.Decidable.html#14953" class="Bound">n</a> <a id="14955" class="Symbol">:</a> <a id="14957" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="14958" class="Symbol">)</a> <a id="14960" class="Symbol">→</a> <a id="14962" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="14966" class="Symbol">(</a><a id="14967" href="plfa.Decidable.html#14951" class="Bound">m</a> <a id="14969" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="14971" href="plfa.Decidable.html#14953" class="Bound">n</a><a id="14972" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
{% raw %}<pre class="Agda"><a id="14995" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="15032" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
## Decidables from booleans, and booleans from decidables
{:/}

## 从可判定的值到布尔值，从布尔值到可判定的值

{::comment}
Curious readers might wonder if we could reuse the definition of
`m ≤ᵇ n`, together with the proofs that it is equivalent to `m ≤ n`, to show
decidability.  Indeed, we can do so as follows:
{:/}

好奇的读者可能会思考能不能重用 `m ≤ᵇ n` 的定义，加上它与 `m ≤ n` 等价的证明，
来证明可判定性。的确，我们是可以做到的：

{% raw %}<pre class="Agda"><a id="_≤?′_"></a><a id="15436" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#15436" class="Function Operator">_≤?′_</a> <a id="15442" class="Symbol">:</a> <a id="15444" class="Symbol">∀</a> <a id="15446" class="Symbol">(</a><a id="15447" href="plfa.Decidable.html#15447" class="Bound">m</a> <a id="15449" href="plfa.Decidable.html#15449" class="Bound">n</a> <a id="15451" class="Symbol">:</a> <a id="15453" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="15454" class="Symbol">)</a> <a id="15456" class="Symbol">→</a> <a id="15458" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="15462" class="Symbol">(</a><a id="15463" href="plfa.Decidable.html#15447" class="Bound">m</a> <a id="15465" href="plfa.Decidable.html#1743" class="Datatype Operator">≤</a> <a id="15467" href="plfa.Decidable.html#15449" class="Bound">n</a><a id="15468" class="Symbol">)</a>
<a id="15470" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#15470" class="Bound">m</a> <a id="15472" href="plfa.Decidable.html#15436" class="Function Operator">≤?′</a> <a id="15476" href="plfa.Decidable.html#15476" class="Bound">n</a> <a id="15478" class="Keyword">with</a> <a id="15483" href="plfa.Decidable.html#15470" class="Bound">m</a> <a id="15485" href="plfa.Decidable.html#2875" class="Function Operator">≤ᵇ</a> <a id="15488" href="plfa.Decidable.html#15476" class="Bound">n</a> <a id="15490" class="Symbol">|</a> <a id="15492" href="plfa.Decidable.html#6378" class="Function">≤ᵇ→≤</a> <a id="15497" href="plfa.Decidable.html#15470" class="Bound">m</a> <a id="15499" href="plfa.Decidable.html#15476" class="Bound">n</a> <a id="15501" class="Symbol">|</a> <a id="15503" href="plfa.Decidable.html#7718" class="Function">≤→≤ᵇ</a> <a id="15508" class="Symbol">{</a><a id="15509" href="plfa.Decidable.html#15470" class="Bound">m</a><a id="15510" class="Symbol">}</a> <a id="15512" class="Symbol">{</a><a id="15513" href="plfa.Decidable.html#15476" class="Bound">n</a><a id="15514" class="Symbol">}</a>
<a id="15516" class="Symbol">...</a>        <a id="15527" class="Symbol">|</a> <a id="15529" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2613" class="InductiveConstructor">true</a>   <a id="15536" class="Symbol">|</a> <a id="15538" href="plfa.Decidable.html#15538" class="Bound">p</a>        <a id="15547" class="Symbol">|</a> <a id="15549" class="Symbol">_</a>            <a id="15562" class="Symbol">=</a> <a id="15564" href="plfa.Decidable.html#10034" class="InductiveConstructor">yes</a> <a id="15568" class="Symbol">(</a><a id="15569" href="plfa.Decidable.html#15538" class="Bound">p</a> <a id="15571" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a><a id="15573" class="Symbol">)</a>
<a id="15575" class="Symbol">...</a>        <a id="15586" class="Symbol">|</a> <a id="15588" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2628" class="InductiveConstructor">false</a>  <a id="15595" class="Symbol">|</a> <a id="15597" class="Symbol">_</a>        <a id="15606" class="Symbol">|</a> <a id="15608" href="plfa.Decidable.html#15608" class="Bound">¬p</a>           <a id="15621" class="Symbol">=</a> <a id="15623" href="plfa.Decidable.html#10054" class="InductiveConstructor">no</a> <a id="15626" href="plfa.Decidable.html#15608" class="Bound">¬p</a>
</pre>{% endraw %}
{::comment}
If `m ≤ᵇ n` is true then `≤ᵇ→≤` yields a proof that `m ≤ n` holds,
while if it is false then `≤→≤ᵇ` takes a proof that `m ≤ n` holds into a contradiction.
{:/}

如果 `m ≤ᵇ n` 为真，那么 `≤ᵇ→≤` 会返回一个 `m ≤ n` 成立的证明。
如果 `m ≤ᵇ n` 为假，那么 `≤→≤ᵇ` 会取一个 `m ≤ n` 成立的证明，将其转换为一个矛盾。

{::comment}
The triple binding of the `with` clause in this proof is essential.
If instead we wrote:
{:/}

在这个证明中，`with` 语句的三重约束是必须的。如果我们取而代之的写：

    _≤?″_ : ∀ (m n : ℕ) → Dec (m ≤ n)
    m ≤?″ n with m ≤ᵇ n
    ... | true   =  yes (≤ᵇ→≤ m n tt)
    ... | false  =  no (≤→≤ᵇ {m} {n})

{::comment}
then Agda would make two complaints, one for each clause:
{:/}

那么 Agda 对于每条语句会有一个抱怨：

    ⊤ !=< (T (m ≤ᵇ n)) of type Set
    when checking that the expression tt has type T (m ≤ᵇ n)

    T (m ≤ᵇ n) !=< ⊥ of type Set
    when checking that the expression ≤→≤ᵇ {m} {n} has type ¬ m ≤ n

{::comment}
Putting the expressions into the `with` clause permits Agda to exploit
the fact that `T (m ≤ᵇ n)` is `⊤` when `m ≤ᵇ n` is true, and that
`T (m ≤ᵇ n)` is `⊥` when `m ≤ᵇ n` is false.
{:/}

将表达式放在 `with` 语句中能让 Agda 利用下列事实：当 `m ≤ᵇ n` 为真时，`T (m ≤ᵇ n)` 是
`⊤`；当 `m ≤ᵇ n` 为假时，`T (m ≤ᵇ n)` 是 `⊥`。

{::comment}
However, overall it is simpler to just define `_≤?_` directly, as in the previous
section.  If one really wants `_≤ᵇ_`, then it and its properties are easily derived
from `_≤?_`, as we will now show.
{:/}

然而，总体来说还是直接定义 `_≤?_` 比较方便，正如之前部分中那样。如果有人真的很需要 `_≤ᵇ_`，
那么它和它的性质可以简单地从 `_≤?_` 中派生出来，正如我们接下来要展示的一样。

{::comment}
Erasure takes a decidable value to a boolean:
{:/}

擦除（Erasure）将一个可判定的值转换为一个布尔值：

{% raw %}<pre class="Agda"><a id="⌊_⌋"></a><a id="17207" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#17207" class="Function Operator">⌊_⌋</a> <a id="17211" class="Symbol">:</a> <a id="17213" class="Symbol">∀</a> <a id="17215" class="Symbol">{</a><a id="17216" href="plfa.Decidable.html#17216" class="Bound">A</a> <a id="17218" class="Symbol">:</a> <a id="17220" class="PrimitiveType">Set</a><a id="17223" class="Symbol">}</a> <a id="17225" class="Symbol">→</a> <a id="17227" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="17231" href="plfa.Decidable.html#17216" class="Bound">A</a> <a id="17233" class="Symbol">→</a> <a id="17235" href="plfa.Decidable.html#2594" class="Datatype">Bool</a>
<a id="17240" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#17207" class="Function Operator">⌊</a> <a id="17242" href="plfa.Decidable.html#10034" class="InductiveConstructor">yes</a> <a id="17246" href="plfa.Decidable.html#17246" class="Bound">x</a> <a id="17248" href="plfa.Decidable.html#17207" class="Function Operator">⌋</a>  <a id="17251" class="Symbol">=</a>  <a id="17254" href="plfa.Decidable.html#2613" class="InductiveConstructor">true</a>
<a id="17259" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#17207" class="Function Operator">⌊</a> <a id="17261" href="plfa.Decidable.html#10054" class="InductiveConstructor">no</a> <a id="17264" href="plfa.Decidable.html#17264" class="Bound">¬x</a> <a id="17267" href="plfa.Decidable.html#17207" class="Function Operator">⌋</a>  <a id="17270" class="Symbol">=</a>  <a id="17273" href="plfa.Decidable.html#2628" class="InductiveConstructor">false</a>
</pre>{% endraw %}
{::comment}
Using erasure, we can easily derive `_≤ᵇ_` from `_≤?_`:
{:/}

使用擦除，我们可以简单地从 `_≤?_` 中派生出 `_≤ᵇ_`：

{% raw %}<pre class="Agda"><a id="_≤ᵇ′_"></a><a id="17397" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#17397" class="Function Operator">_≤ᵇ′_</a> <a id="17403" class="Symbol">:</a> <a id="17405" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="17407" class="Symbol">→</a> <a id="17409" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="17411" class="Symbol">→</a> <a id="17413" href="plfa.Decidable.html#2594" class="Datatype">Bool</a>
<a id="17418" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#17418" class="Bound">m</a> <a id="17420" href="plfa.Decidable.html#17397" class="Function Operator">≤ᵇ′</a> <a id="17424" href="plfa.Decidable.html#17424" class="Bound">n</a>  <a id="17427" class="Symbol">=</a>  <a id="17430" href="plfa.Decidable.html#17207" class="Function Operator">⌊</a> <a id="17432" href="plfa.Decidable.html#17418" class="Bound">m</a> <a id="17434" href="plfa.Decidable.html#11889" class="Function Operator">≤?</a> <a id="17437" href="plfa.Decidable.html#17424" class="Bound">n</a> <a id="17439" href="plfa.Decidable.html#17207" class="Function Operator">⌋</a>
</pre>{% endraw %}
{::comment}
Further, if `D` is a value of type `Dec A`, then `T ⌊ D ⌋` is
inhabited exactly when `A` is inhabited:
{:/}

更进一步来说，如果 `D` 是一个类型为 `Dec A` 的值，那么 `T ⌊ D ⌋`
当且仅当 `A` 成立时成立：
{% raw %}<pre class="Agda"><a id="toWitness"></a><a id="17632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#17632" class="Function">toWitness</a> <a id="17642" class="Symbol">:</a> <a id="17644" class="Symbol">∀</a> <a id="17646" class="Symbol">{</a><a id="17647" href="plfa.Decidable.html#17647" class="Bound">A</a> <a id="17649" class="Symbol">:</a> <a id="17651" class="PrimitiveType">Set</a><a id="17654" class="Symbol">}</a> <a id="17656" class="Symbol">{</a><a id="17657" href="plfa.Decidable.html#17657" class="Bound">D</a> <a id="17659" class="Symbol">:</a> <a id="17661" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="17665" href="plfa.Decidable.html#17647" class="Bound">A</a><a id="17666" class="Symbol">}</a> <a id="17668" class="Symbol">→</a> <a id="17670" href="plfa.Decidable.html#4594" class="Function">T</a> <a id="17672" href="plfa.Decidable.html#17207" class="Function Operator">⌊</a> <a id="17674" href="plfa.Decidable.html#17657" class="Bound">D</a> <a id="17676" href="plfa.Decidable.html#17207" class="Function Operator">⌋</a> <a id="17678" class="Symbol">→</a> <a id="17680" href="plfa.Decidable.html#17647" class="Bound">A</a>
<a id="17682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#17632" class="Function">toWitness</a> <a id="17692" class="Symbol">{</a><a id="17693" href="plfa.Decidable.html#17693" class="Bound">A</a><a id="17694" class="Symbol">}</a> <a id="17696" class="Symbol">{</a><a id="17697" href="plfa.Decidable.html#10034" class="InductiveConstructor">yes</a> <a id="17701" href="plfa.Decidable.html#17701" class="Bound">x</a><a id="17702" class="Symbol">}</a> <a id="17704" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a>  <a id="17708" class="Symbol">=</a>  <a id="17711" href="plfa.Decidable.html#17701" class="Bound">x</a>
<a id="17713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#17632" class="Function">toWitness</a> <a id="17723" class="Symbol">{</a><a id="17724" href="plfa.Decidable.html#17724" class="Bound">A</a><a id="17725" class="Symbol">}</a> <a id="17727" class="Symbol">{</a><a id="17728" href="plfa.Decidable.html#10054" class="InductiveConstructor">no</a> <a id="17731" href="plfa.Decidable.html#17731" class="Bound">¬x</a><a id="17733" class="Symbol">}</a> <a id="17735" class="Symbol">()</a>

<a id="fromWitness"></a><a id="17739" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#17739" class="Function">fromWitness</a> <a id="17751" class="Symbol">:</a> <a id="17753" class="Symbol">∀</a> <a id="17755" class="Symbol">{</a><a id="17756" href="plfa.Decidable.html#17756" class="Bound">A</a> <a id="17758" class="Symbol">:</a> <a id="17760" class="PrimitiveType">Set</a><a id="17763" class="Symbol">}</a> <a id="17765" class="Symbol">{</a><a id="17766" href="plfa.Decidable.html#17766" class="Bound">D</a> <a id="17768" class="Symbol">:</a> <a id="17770" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="17774" href="plfa.Decidable.html#17756" class="Bound">A</a><a id="17775" class="Symbol">}</a> <a id="17777" class="Symbol">→</a> <a id="17779" href="plfa.Decidable.html#17756" class="Bound">A</a> <a id="17781" class="Symbol">→</a> <a id="17783" href="plfa.Decidable.html#4594" class="Function">T</a> <a id="17785" href="plfa.Decidable.html#17207" class="Function Operator">⌊</a> <a id="17787" href="plfa.Decidable.html#17766" class="Bound">D</a> <a id="17789" href="plfa.Decidable.html#17207" class="Function Operator">⌋</a>
<a id="17791" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#17739" class="Function">fromWitness</a> <a id="17803" class="Symbol">{</a><a id="17804" href="plfa.Decidable.html#17804" class="Bound">A</a><a id="17805" class="Symbol">}</a> <a id="17807" class="Symbol">{</a><a id="17808" href="plfa.Decidable.html#10034" class="InductiveConstructor">yes</a> <a id="17812" href="plfa.Decidable.html#17812" class="Bound">x</a><a id="17813" class="Symbol">}</a> <a id="17815" class="Symbol">_</a>  <a id="17818" class="Symbol">=</a>  <a id="17821" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a>
<a id="17824" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#17739" class="Function">fromWitness</a> <a id="17836" class="Symbol">{</a><a id="17837" href="plfa.Decidable.html#17837" class="Bound">A</a><a id="17838" class="Symbol">}</a> <a id="17840" class="Symbol">{</a><a id="17841" href="plfa.Decidable.html#10054" class="InductiveConstructor">no</a> <a id="17844" href="plfa.Decidable.html#17844" class="Bound">¬x</a><a id="17846" class="Symbol">}</a> <a id="17848" href="plfa.Decidable.html#17848" class="Bound">x</a>  <a id="17851" class="Symbol">=</a>  <a id="17854" href="plfa.Decidable.html#17844" class="Bound">¬x</a> <a id="17857" href="plfa.Decidable.html#17848" class="Bound">x</a>
</pre>{% endraw %}
{::comment}
Using these, we can easily derive that `T (m ≤ᵇ′ n)` is inhabited
exactly when `m ≤ n` is inhabited:
{:/}

使用这些，我们可以简单地派生出 `T (m ≤ᵇ′ n)` 当且仅当 `m ≤ n` 成立时成立。

{% raw %}<pre class="Agda"><a id="≤ᵇ′→≤"></a><a id="18038" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#18038" class="Function">≤ᵇ′→≤</a> <a id="18044" class="Symbol">:</a> <a id="18046" class="Symbol">∀</a> <a id="18048" class="Symbol">{</a><a id="18049" href="plfa.Decidable.html#18049" class="Bound">m</a> <a id="18051" href="plfa.Decidable.html#18051" class="Bound">n</a> <a id="18053" class="Symbol">:</a> <a id="18055" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="18056" class="Symbol">}</a> <a id="18058" class="Symbol">→</a> <a id="18060" href="plfa.Decidable.html#4594" class="Function">T</a> <a id="18062" class="Symbol">(</a><a id="18063" href="plfa.Decidable.html#18049" class="Bound">m</a> <a id="18065" href="plfa.Decidable.html#17397" class="Function Operator">≤ᵇ′</a> <a id="18069" href="plfa.Decidable.html#18051" class="Bound">n</a><a id="18070" class="Symbol">)</a> <a id="18072" class="Symbol">→</a> <a id="18074" href="plfa.Decidable.html#18049" class="Bound">m</a> <a id="18076" href="plfa.Decidable.html#1743" class="Datatype Operator">≤</a> <a id="18078" href="plfa.Decidable.html#18051" class="Bound">n</a>
<a id="18080" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#18038" class="Function">≤ᵇ′→≤</a>  <a id="18087" class="Symbol">=</a>  <a id="18090" href="plfa.Decidable.html#17632" class="Function">toWitness</a>

<a id="≤→≤ᵇ′"></a><a id="18101" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#18101" class="Function">≤→≤ᵇ′</a> <a id="18107" class="Symbol">:</a> <a id="18109" class="Symbol">∀</a> <a id="18111" class="Symbol">{</a><a id="18112" href="plfa.Decidable.html#18112" class="Bound">m</a> <a id="18114" href="plfa.Decidable.html#18114" class="Bound">n</a> <a id="18116" class="Symbol">:</a> <a id="18118" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="18119" class="Symbol">}</a> <a id="18121" class="Symbol">→</a> <a id="18123" href="plfa.Decidable.html#18112" class="Bound">m</a> <a id="18125" href="plfa.Decidable.html#1743" class="Datatype Operator">≤</a> <a id="18127" href="plfa.Decidable.html#18114" class="Bound">n</a> <a id="18129" class="Symbol">→</a> <a id="18131" href="plfa.Decidable.html#4594" class="Function">T</a> <a id="18133" class="Symbol">(</a><a id="18134" href="plfa.Decidable.html#18112" class="Bound">m</a> <a id="18136" href="plfa.Decidable.html#17397" class="Function Operator">≤ᵇ′</a> <a id="18140" href="plfa.Decidable.html#18114" class="Bound">n</a><a id="18141" class="Symbol">)</a>
<a id="18143" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#18101" class="Function">≤→≤ᵇ′</a>  <a id="18150" class="Symbol">=</a>  <a id="18153" href="plfa.Decidable.html#17739" class="Function">fromWitness</a>
</pre>{% endraw %}
{::comment}
In summary, it is usually best to eschew booleans and rely on decidables.
If you need booleans, they and their properties are easily derived from the
corresponding decidables.
{:/}

总结来说，最好避免直接使用布尔值，而使用可判定的值。如果有需要布尔值的时候，它们和它们的性质
可以简单地从对应的可判定的值中派生而来。


{::comment}
## Logical connectives
{:/}

{::comment}
Most readers will be familiar with the logical connectives for booleans.
Each of these extends to decidables.
{:/}

大多数读者对于布尔值的逻辑运算符很熟悉了。每个逻辑运算符都可以被延伸至可判定的值。

{::comment}
The conjunction of two booleans is true if both are true,
and false if either is false:
{:/}

两个布尔值的合取当两者都为真时为真，当任一为假时为假：

{% raw %}<pre class="Agda"><a id="18785" class="Keyword">infixr</a> <a id="18792" class="Number">6</a> <a id="18794" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#18799" class="Function Operator">_∧_</a>

<a id="_∧_"></a><a id="18799" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#18799" class="Function Operator">_∧_</a> <a id="18803" class="Symbol">:</a> <a id="18805" href="plfa.Decidable.html#2594" class="Datatype">Bool</a> <a id="18810" class="Symbol">→</a> <a id="18812" href="plfa.Decidable.html#2594" class="Datatype">Bool</a> <a id="18817" class="Symbol">→</a> <a id="18819" href="plfa.Decidable.html#2594" class="Datatype">Bool</a>
<a id="18824" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2613" class="InductiveConstructor">true</a>  <a id="18830" href="plfa.Decidable.html#18799" class="Function Operator">∧</a> <a id="18832" href="plfa.Decidable.html#2613" class="InductiveConstructor">true</a>  <a id="18838" class="Symbol">=</a> <a id="18840" href="plfa.Decidable.html#2613" class="InductiveConstructor">true</a>
<a id="18845" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2628" class="InductiveConstructor">false</a> <a id="18851" href="plfa.Decidable.html#18799" class="Function Operator">∧</a> <a id="18853" class="Symbol">_</a>     <a id="18859" class="Symbol">=</a> <a id="18861" href="plfa.Decidable.html#2628" class="InductiveConstructor">false</a>
<a id="18867" class="CatchallClause Symbol">_</a><a id="18868" class="CatchallClause">     </a><a id="18873" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#18799" class="CatchallClause Function Operator">∧</a><a id="18874" class="CatchallClause"> </a><a id="18875" href="plfa.Decidable.html#2628" class="CatchallClause InductiveConstructor">false</a> <a id="18881" class="Symbol">=</a> <a id="18883" href="plfa.Decidable.html#2628" class="InductiveConstructor">false</a>
</pre>{% endraw %}
{::comment}
In Emacs, the left-hand side of the third equation displays in grey,
indicating that the order of the equations determines which of the
second or the third can match.  However, regardless of which matches
the answer is the same.
{:/}

在 Emacs 中，第三个等式的左手边显示为灰色，表示这些等式出现的顺序决定了是第二条还是第三条
会被匹配到。然而，不管是哪一条被匹配到，结果都是一样的。

{::comment}
Correspondingly, given two decidable propositions, we can
decide their conjunction:
{:/}

相应地，给定两个可判定的命题，我们可以判定它们的合取：

{% raw %}<pre class="Agda"><a id="19355" class="Keyword">infixr</a> <a id="19362" class="Number">6</a> <a id="19364" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#19373" class="Function Operator">_×-dec_</a>

<a id="_×-dec_"></a><a id="19373" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#19373" class="Function Operator">_×-dec_</a> <a id="19381" class="Symbol">:</a> <a id="19383" class="Symbol">∀</a> <a id="19385" class="Symbol">{</a><a id="19386" href="plfa.Decidable.html#19386" class="Bound">A</a> <a id="19388" href="plfa.Decidable.html#19388" class="Bound">B</a> <a id="19390" class="Symbol">:</a> <a id="19392" class="PrimitiveType">Set</a><a id="19395" class="Symbol">}</a> <a id="19397" class="Symbol">→</a> <a id="19399" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="19403" href="plfa.Decidable.html#19386" class="Bound">A</a> <a id="19405" class="Symbol">→</a> <a id="19407" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="19411" href="plfa.Decidable.html#19388" class="Bound">B</a> <a id="19413" class="Symbol">→</a> <a id="19415" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="19419" class="Symbol">(</a><a id="19420" href="plfa.Decidable.html#19386" class="Bound">A</a> <a id="19422" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="19424" href="plfa.Decidable.html#19388" class="Bound">B</a><a id="19425" class="Symbol">)</a>
<a id="19427" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#10034" class="InductiveConstructor">yes</a> <a id="19431" href="plfa.Decidable.html#19431" class="Bound">x</a> <a id="19433" href="plfa.Decidable.html#19373" class="Function Operator">×-dec</a> <a id="19439" href="plfa.Decidable.html#10034" class="InductiveConstructor">yes</a> <a id="19443" href="plfa.Decidable.html#19443" class="Bound">y</a> <a id="19445" class="Symbol">=</a> <a id="19447" href="plfa.Decidable.html#10034" class="InductiveConstructor">yes</a> <a id="19451" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨</a> <a id="19453" href="plfa.Decidable.html#19431" class="Bound">x</a> <a id="19455" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">,</a> <a id="19457" href="plfa.Decidable.html#19443" class="Bound">y</a> <a id="19459" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟩</a>
<a id="19461" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#10054" class="InductiveConstructor">no</a> <a id="19464" href="plfa.Decidable.html#19464" class="Bound">¬x</a> <a id="19467" href="plfa.Decidable.html#19373" class="Function Operator">×-dec</a> <a id="19473" class="Symbol">_</a>     <a id="19479" class="Symbol">=</a> <a id="19481" href="plfa.Decidable.html#10054" class="InductiveConstructor">no</a> <a id="19484" class="Symbol">λ{</a> <a id="19487" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨</a> <a id="19489" href="plfa.Decidable.html#19489" class="Bound">x</a> <a id="19491" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">,</a> <a id="19493" href="plfa.Decidable.html#19493" class="Bound">y</a> <a id="19495" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟩</a> <a id="19497" class="Symbol">→</a> <a id="19499" href="plfa.Decidable.html#19464" class="Bound">¬x</a> <a id="19502" href="plfa.Decidable.html#19489" class="Bound">x</a> <a id="19504" class="Symbol">}</a>
<a id="19506" class="CatchallClause Symbol">_</a><a id="19507" class="CatchallClause">     </a><a id="19512" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#19373" class="CatchallClause Function Operator">×-dec</a><a id="19517" class="CatchallClause"> </a><a id="19518" href="plfa.Decidable.html#10054" class="CatchallClause InductiveConstructor">no</a><a id="19520" class="CatchallClause"> </a><a id="19521" href="plfa.Decidable.html#19521" class="CatchallClause Bound">¬y</a> <a id="19524" class="Symbol">=</a> <a id="19526" href="plfa.Decidable.html#10054" class="InductiveConstructor">no</a> <a id="19529" class="Symbol">λ{</a> <a id="19532" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨</a> <a id="19534" href="plfa.Decidable.html#19534" class="Bound">x</a> <a id="19536" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">,</a> <a id="19538" href="plfa.Decidable.html#19538" class="Bound">y</a> <a id="19540" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟩</a> <a id="19542" class="Symbol">→</a> <a id="19544" href="plfa.Decidable.html#19521" class="Bound">¬y</a> <a id="19547" href="plfa.Decidable.html#19538" class="Bound">y</a> <a id="19549" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
The conjunction of two propositions holds if they both hold,
and its negation holds if the negation of either holds.
If both hold, then we pair the evidence for each to yield
evidence of the conjunct.  If the negation of either holds,
assuming the conjunct will lead to a contradiction.
{:/}

两个命题的合取当两者都成立时成立，其否定则当任意一者否定成立时成立。如果两个都成立，
我们将每一证明放入数据对中，作为合取的证明。如果任意一者的否定成立，假设整个合取将会引入一个矛盾。

{::comment}
Again in Emacs, the left-hand side of the third equation displays in grey,
indicating that the order of the equations determines which of the
second or the third can match.  This time the answer is different depending
on which matches; if both conjuncts fail to hold we pick the first to
yield the contradiction, but it would be equally valid to pick the second.
{:/}

同样地，在 Emacs 中，第三条等式在左手边以灰色显示，说明等式的顺序决定了第二条还是第三条会被匹配。
这一次，我们给出的结果会因为是第二条还是第三条而不一样。如果两个命题都不成立，我们选择第一个来构造矛盾，
但选择第二个也是同样正确的。

{::comment}
The disjunction of two booleans is true if either is true,
and false if both are false:
{:/}

两个布尔值的析取当任意为真时为真，当两者为假时为假：

{% raw %}<pre class="Agda"><a id="20596" class="Keyword">infixr</a> <a id="20603" class="Number">5</a> <a id="20605" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#20610" class="Function Operator">_∨_</a>

<a id="_∨_"></a><a id="20610" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#20610" class="Function Operator">_∨_</a> <a id="20614" class="Symbol">:</a> <a id="20616" href="plfa.Decidable.html#2594" class="Datatype">Bool</a> <a id="20621" class="Symbol">→</a> <a id="20623" href="plfa.Decidable.html#2594" class="Datatype">Bool</a> <a id="20628" class="Symbol">→</a> <a id="20630" href="plfa.Decidable.html#2594" class="Datatype">Bool</a>
<a id="20635" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2613" class="InductiveConstructor">true</a>  <a id="20641" href="plfa.Decidable.html#20610" class="Function Operator">∨</a> <a id="20643" class="Symbol">_</a>      <a id="20650" class="Symbol">=</a> <a id="20652" href="plfa.Decidable.html#2613" class="InductiveConstructor">true</a>
<a id="20657" class="CatchallClause Symbol">_</a><a id="20658" class="CatchallClause">     </a><a id="20663" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#20610" class="CatchallClause Function Operator">∨</a><a id="20664" class="CatchallClause"> </a><a id="20665" href="plfa.Decidable.html#2613" class="CatchallClause InductiveConstructor">true</a>   <a id="20672" class="Symbol">=</a> <a id="20674" href="plfa.Decidable.html#2613" class="InductiveConstructor">true</a>
<a id="20679" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2628" class="InductiveConstructor">false</a> <a id="20685" href="plfa.Decidable.html#20610" class="Function Operator">∨</a> <a id="20687" href="plfa.Decidable.html#2628" class="InductiveConstructor">false</a>  <a id="20694" class="Symbol">=</a> <a id="20696" href="plfa.Decidable.html#2628" class="InductiveConstructor">false</a>
</pre>{% endraw %}
{::comment}
In Emacs, the left-hand side of the second equation displays in grey,
indicating that the order of the equations determines which of the
first or the second can match.  However, regardless of which matches
the answer is the same.
{:/}

在 Emacs 中，第二个等式的左手边显示为灰色，表示这些等式出现的顺序决定了是第一条还是第二条
会被匹配到。然而，不管是哪一条被匹配到，结果都是一样的。

{::comment}
Correspondingly, given two decidable propositions, we can
decide their disjunction:
{:/}

相应地，给定两个可判定的命题，我们可以判定它们的析取：

{% raw %}<pre class="Agda"><a id="21169" class="Keyword">infixr</a> <a id="21176" class="Number">5</a> <a id="21178" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#21187" class="Function Operator">_⊎-dec_</a>

<a id="_⊎-dec_"></a><a id="21187" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#21187" class="Function Operator">_⊎-dec_</a> <a id="21195" class="Symbol">:</a> <a id="21197" class="Symbol">∀</a> <a id="21199" class="Symbol">{</a><a id="21200" href="plfa.Decidable.html#21200" class="Bound">A</a> <a id="21202" href="plfa.Decidable.html#21202" class="Bound">B</a> <a id="21204" class="Symbol">:</a> <a id="21206" class="PrimitiveType">Set</a><a id="21209" class="Symbol">}</a> <a id="21211" class="Symbol">→</a> <a id="21213" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="21217" href="plfa.Decidable.html#21200" class="Bound">A</a> <a id="21219" class="Symbol">→</a> <a id="21221" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="21225" href="plfa.Decidable.html#21202" class="Bound">B</a> <a id="21227" class="Symbol">→</a> <a id="21229" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="21233" class="Symbol">(</a><a id="21234" href="plfa.Decidable.html#21200" class="Bound">A</a> <a id="21236" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="21238" href="plfa.Decidable.html#21202" class="Bound">B</a><a id="21239" class="Symbol">)</a>
<a id="21241" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#10034" class="InductiveConstructor">yes</a> <a id="21245" href="plfa.Decidable.html#21245" class="Bound">x</a> <a id="21247" href="plfa.Decidable.html#21187" class="Function Operator">⊎-dec</a> <a id="21253" class="Symbol">_</a>     <a id="21259" class="Symbol">=</a> <a id="21261" href="plfa.Decidable.html#10034" class="InductiveConstructor">yes</a> <a id="21265" class="Symbol">(</a><a id="21266" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a> <a id="21271" href="plfa.Decidable.html#21245" class="Bound">x</a><a id="21272" class="Symbol">)</a>
<a id="21274" class="CatchallClause Symbol">_</a><a id="21275" class="CatchallClause">     </a><a id="21280" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#21187" class="CatchallClause Function Operator">⊎-dec</a><a id="21285" class="CatchallClause"> </a><a id="21286" href="plfa.Decidable.html#10034" class="CatchallClause InductiveConstructor">yes</a><a id="21289" class="CatchallClause"> </a><a id="21290" href="plfa.Decidable.html#21290" class="CatchallClause Bound">y</a> <a id="21292" class="Symbol">=</a> <a id="21294" href="plfa.Decidable.html#10034" class="InductiveConstructor">yes</a> <a id="21298" class="Symbol">(</a><a id="21299" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a> <a id="21304" href="plfa.Decidable.html#21290" class="Bound">y</a><a id="21305" class="Symbol">)</a>
<a id="21307" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#10054" class="InductiveConstructor">no</a> <a id="21310" href="plfa.Decidable.html#21310" class="Bound">¬x</a> <a id="21313" href="plfa.Decidable.html#21187" class="Function Operator">⊎-dec</a> <a id="21319" href="plfa.Decidable.html#10054" class="InductiveConstructor">no</a> <a id="21322" href="plfa.Decidable.html#21322" class="Bound">¬y</a> <a id="21325" class="Symbol">=</a> <a id="21327" href="plfa.Decidable.html#10054" class="InductiveConstructor">no</a> <a id="21330" class="Symbol">λ{</a> <a id="21333" class="Symbol">(</a><a id="21334" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a> <a id="21339" href="plfa.Decidable.html#21339" class="Bound">x</a><a id="21340" class="Symbol">)</a> <a id="21342" class="Symbol">→</a> <a id="21344" href="plfa.Decidable.html#21310" class="Bound">¬x</a> <a id="21347" href="plfa.Decidable.html#21339" class="Bound">x</a> <a id="21349" class="Symbol">;</a> <a id="21351" class="Symbol">(</a><a id="21352" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a> <a id="21357" href="plfa.Decidable.html#21357" class="Bound">y</a><a id="21358" class="Symbol">)</a> <a id="21360" class="Symbol">→</a> <a id="21362" href="plfa.Decidable.html#21322" class="Bound">¬y</a> <a id="21365" href="plfa.Decidable.html#21357" class="Bound">y</a> <a id="21367" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
The disjunction of two propositions holds if either holds,
and its negation holds if the negation of both hold.
If either holds, we inject the evidence to yield
evidence of the disjunct.  If the negation of both hold,
assuming either disjunct will lead to a contradiction.
{:/}

两个命题的析取当任意一者成立时成立，其否定则当两者的否定成立时成立。如果任意一者成立，
我们使用其证明来作为析取的证明。如果两个的否定都成立，假设任意一者都会引入一个矛盾。

{::comment}
Again in Emacs, the left-hand side of the second equation displays in grey,
indicating that the order of the equations determines which of the
first or the second can match.  This time the answer is different depending
on which matches; if both disjuncts hold we pick the first,
but it would be equally valid to pick the second.
{:/}

同样地，在 Emacs 中，第二条等式在左手边以灰色显示，说明等式的顺序决定了第一条还是第二条会被匹配。
这一次，我们给出的结果会因为是第二条还是第三条而不一样。如果两个命题都成立，我们选择第一个来构造析取，
但选择第二个也是同样正确的。

{::comment}
The negation of a boolean is false if its argument is true,
and vice versa:
{:/}

一个布尔值的否定当值为真时为假，反之亦然：

{% raw %}<pre class="Agda"><a id="not"></a><a id="22342" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#22342" class="Function">not</a> <a id="22346" class="Symbol">:</a> <a id="22348" href="plfa.Decidable.html#2594" class="Datatype">Bool</a> <a id="22353" class="Symbol">→</a> <a id="22355" href="plfa.Decidable.html#2594" class="Datatype">Bool</a>
<a id="22360" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#22342" class="Function">not</a> <a id="22364" href="plfa.Decidable.html#2613" class="InductiveConstructor">true</a>  <a id="22370" class="Symbol">=</a> <a id="22372" href="plfa.Decidable.html#2628" class="InductiveConstructor">false</a>
<a id="22378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#22342" class="Function">not</a> <a id="22382" href="plfa.Decidable.html#2628" class="InductiveConstructor">false</a> <a id="22388" class="Symbol">=</a> <a id="22390" href="plfa.Decidable.html#2613" class="InductiveConstructor">true</a>
</pre>{% endraw %}
{::comment}
Correspondingly, given a decidable proposition, we
can decide its negation:
{:/}

相应地，给定一个可判定的命题，我们可以判定它的否定：

{% raw %}<pre class="Agda"><a id="¬?"></a><a id="22526" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#22526" class="Function">¬?</a> <a id="22529" class="Symbol">:</a> <a id="22531" class="Symbol">∀</a> <a id="22533" class="Symbol">{</a><a id="22534" href="plfa.Decidable.html#22534" class="Bound">A</a> <a id="22536" class="Symbol">:</a> <a id="22538" class="PrimitiveType">Set</a><a id="22541" class="Symbol">}</a> <a id="22543" class="Symbol">→</a> <a id="22545" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="22549" href="plfa.Decidable.html#22534" class="Bound">A</a> <a id="22551" class="Symbol">→</a> <a id="22553" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="22557" class="Symbol">(</a><a id="22558" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="22560" href="plfa.Decidable.html#22534" class="Bound">A</a><a id="22561" class="Symbol">)</a>
<a id="22563" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#22526" class="Function">¬?</a> <a id="22566" class="Symbol">(</a><a id="22567" href="plfa.Decidable.html#10034" class="InductiveConstructor">yes</a> <a id="22571" href="plfa.Decidable.html#22571" class="Bound">x</a><a id="22572" class="Symbol">)</a>  <a id="22575" class="Symbol">=</a>  <a id="22578" href="plfa.Decidable.html#10054" class="InductiveConstructor">no</a> <a id="22581" class="Symbol">(</a><a id="22582" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#809" class="Function">¬¬-intro</a> <a id="22591" href="plfa.Decidable.html#22571" class="Bound">x</a><a id="22592" class="Symbol">)</a>
<a id="22594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#22526" class="Function">¬?</a> <a id="22597" class="Symbol">(</a><a id="22598" href="plfa.Decidable.html#10054" class="InductiveConstructor">no</a> <a id="22601" href="plfa.Decidable.html#22601" class="Bound">¬x</a><a id="22603" class="Symbol">)</a>  <a id="22606" class="Symbol">=</a>  <a id="22609" href="plfa.Decidable.html#10034" class="InductiveConstructor">yes</a> <a id="22613" href="plfa.Decidable.html#22601" class="Bound">¬x</a>
</pre>{% endraw %}
{::comment}
We simply swap yes and no.  In the first equation,
the right-hand side asserts that the negation of `¬ A` holds,
in other words, that `¬ ¬ A` holds, which is an easy consequence
of the fact that `A` holds.
{:/}

我们直接把 yes 和 no 交换。在第一个等式中，右手边断言了 `¬ A` 的否定成立，也就是说
`¬ ¬ A` 成立——这是一个 `A` 成立时可以简单得到的推论。

{::comment}
There is also a slightly less familiar connective,
corresponding to implication:
{:/}

还有一个与蕴涵相对应，但是稍微不那么知名的运算符：

{% raw %}<pre class="Agda"><a id="_⊃_"></a><a id="23061" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#23061" class="Function Operator">_⊃_</a> <a id="23065" class="Symbol">:</a> <a id="23067" href="plfa.Decidable.html#2594" class="Datatype">Bool</a> <a id="23072" class="Symbol">→</a> <a id="23074" href="plfa.Decidable.html#2594" class="Datatype">Bool</a> <a id="23079" class="Symbol">→</a> <a id="23081" href="plfa.Decidable.html#2594" class="Datatype">Bool</a>
<a id="23086" class="Symbol">_</a>     <a id="23092" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#23061" class="Function Operator">⊃</a> <a id="23094" href="plfa.Decidable.html#2613" class="InductiveConstructor">true</a>   <a id="23101" class="Symbol">=</a>  <a id="23104" href="plfa.Decidable.html#2613" class="InductiveConstructor">true</a>
<a id="23109" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2628" class="CatchallClause InductiveConstructor">false</a><a id="23114" class="CatchallClause"> </a><a id="23115" href="plfa.Decidable.html#23061" class="CatchallClause Function Operator">⊃</a><a id="23116" class="CatchallClause"> </a><a id="23117" class="CatchallClause Symbol">_</a>      <a id="23124" class="Symbol">=</a>  <a id="23127" href="plfa.Decidable.html#2613" class="InductiveConstructor">true</a>
<a id="23132" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2613" class="InductiveConstructor">true</a>  <a id="23138" href="plfa.Decidable.html#23061" class="Function Operator">⊃</a> <a id="23140" href="plfa.Decidable.html#2628" class="InductiveConstructor">false</a>  <a id="23147" class="Symbol">=</a>  <a id="23150" href="plfa.Decidable.html#2628" class="InductiveConstructor">false</a>
</pre>{% endraw %}
{::comment}
One boolean implies another if
whenever the first is true then the second is true.
Hence, the implication of two booleans is true if
the second is true or the first is false,
and false if the first is true and the second is false.
In Emacs, the left-hand side of the second equation displays in grey,
indicating that the order of the equations determines which of the
first or the second can match.  However, regardless of which matches
the answer is the same.
{:/}

当任何一个布尔值为真的时候，另一个布尔值恒为真，我们成为第一个布尔值蕴涵第二个布尔值。
因此，两者的蕴涵在第二个为真或者第一个为假时为真，在第一个为真而第二个为假时为假。
在 Emacs 中，第二个等式的左手边显示为灰色，表示这些等式出现的顺序决定了是第一条还是第二条
会被匹配到。然而，不管是哪一条被匹配到，结果都是一样的。

{::comment}
Correspondingly, given two decidable propositions,
we can decide if the first implies the second:
{:/}

相应地，给定两个可判定的命题，我们可以判定它们的析取：

{% raw %}<pre class="Agda"><a id="_→-dec_"></a><a id="23954" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#23954" class="Function Operator">_→-dec_</a> <a id="23962" class="Symbol">:</a> <a id="23964" class="Symbol">∀</a> <a id="23966" class="Symbol">{</a><a id="23967" href="plfa.Decidable.html#23967" class="Bound">A</a> <a id="23969" href="plfa.Decidable.html#23969" class="Bound">B</a> <a id="23971" class="Symbol">:</a> <a id="23973" class="PrimitiveType">Set</a><a id="23976" class="Symbol">}</a> <a id="23978" class="Symbol">→</a> <a id="23980" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="23984" href="plfa.Decidable.html#23967" class="Bound">A</a> <a id="23986" class="Symbol">→</a> <a id="23988" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="23992" href="plfa.Decidable.html#23969" class="Bound">B</a> <a id="23994" class="Symbol">→</a> <a id="23996" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="24000" class="Symbol">(</a><a id="24001" href="plfa.Decidable.html#23967" class="Bound">A</a> <a id="24003" class="Symbol">→</a> <a id="24005" href="plfa.Decidable.html#23969" class="Bound">B</a><a id="24006" class="Symbol">)</a>
<a id="24008" class="Symbol">_</a>     <a id="24014" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#23954" class="Function Operator">→-dec</a> <a id="24020" href="plfa.Decidable.html#10034" class="InductiveConstructor">yes</a> <a id="24024" href="plfa.Decidable.html#24024" class="Bound">y</a>  <a id="24027" class="Symbol">=</a>  <a id="24030" href="plfa.Decidable.html#10034" class="InductiveConstructor">yes</a> <a id="24034" class="Symbol">(λ</a> <a id="24037" href="plfa.Decidable.html#24037" class="Bound">_</a> <a id="24039" class="Symbol">→</a> <a id="24041" href="plfa.Decidable.html#24024" class="Bound">y</a><a id="24042" class="Symbol">)</a>
<a id="24044" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#10054" class="CatchallClause InductiveConstructor">no</a><a id="24046" class="CatchallClause"> </a><a id="24047" href="plfa.Decidable.html#24047" class="CatchallClause Bound">¬x</a><a id="24049" class="CatchallClause"> </a><a id="24050" href="plfa.Decidable.html#23954" class="CatchallClause Function Operator">→-dec</a><a id="24055" class="CatchallClause"> </a><a id="24056" class="CatchallClause Symbol">_</a>      <a id="24063" class="Symbol">=</a>  <a id="24066" href="plfa.Decidable.html#10034" class="InductiveConstructor">yes</a> <a id="24070" class="Symbol">(λ</a> <a id="24073" href="plfa.Decidable.html#24073" class="Bound">x</a> <a id="24075" class="Symbol">→</a> <a id="24077" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="24084" class="Symbol">(</a><a id="24085" href="plfa.Decidable.html#24047" class="Bound">¬x</a> <a id="24088" href="plfa.Decidable.html#24073" class="Bound">x</a><a id="24089" class="Symbol">))</a>
<a id="24092" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#10034" class="InductiveConstructor">yes</a> <a id="24096" href="plfa.Decidable.html#24096" class="Bound">x</a> <a id="24098" href="plfa.Decidable.html#23954" class="Function Operator">→-dec</a> <a id="24104" href="plfa.Decidable.html#10054" class="InductiveConstructor">no</a> <a id="24107" href="plfa.Decidable.html#24107" class="Bound">¬y</a>  <a id="24111" class="Symbol">=</a>  <a id="24114" href="plfa.Decidable.html#10054" class="InductiveConstructor">no</a> <a id="24117" class="Symbol">(λ</a> <a id="24120" href="plfa.Decidable.html#24120" class="Bound">f</a> <a id="24122" class="Symbol">→</a> <a id="24124" href="plfa.Decidable.html#24107" class="Bound">¬y</a> <a id="24127" class="Symbol">(</a><a id="24128" href="plfa.Decidable.html#24120" class="Bound">f</a> <a id="24130" href="plfa.Decidable.html#24096" class="Bound">x</a><a id="24131" class="Symbol">))</a>
</pre>{% endraw %}
{::comment}
The implication holds if either the second holds or
the negation of the first holds, and its negation
holds if the first holds and the negation of the second holds.
Evidence for the implication is a function from evidence
of the first to evidence of the second.
If the second holds, the function returns the evidence for it.
If the negation of the first holds, the function takes the
evidence of the first and derives a contradiction.
If the first holds and the negation of the second holds,
given evidence of the implication we must derive a contradiction;
we apply the evidence of the implication `f` to the evidence of the
first `x`, yielding a contradiction with the evidence `¬y` of
the negation of the second.
{:/}

两者的蕴涵在第二者成立或者第一者的否定成立时成立，其否定在第一者成立而第二者否定成立时成立。
蕴涵成立的证明是一个从第一者成立的证明到第二者成立的证明的函数。如果第二者成立，那么这个函数
直接返回第二者的证明。如果第一者的否定成立，那么使用第一者成立的证明，构造一个矛盾。
如果第一者成立，第二者不成立，给定蕴涵成立的证明，我们必须构造一个矛盾：我们将成立的证明 `f`
应用于第一者成立的证明 `x`，再加以第二者否定成立的证明 `¬y` 来构造矛盾。

{::comment}
Again in Emacs, the left-hand side of the second equation displays in grey,
indicating that the order of the equations determines which of the
first or the second can match.  This time the answer is different depending
on which matches; but either is equally valid.
{:/}

同样地，在 Emacs 中，第二条等式在左手边以灰色显示，说明等式的顺序决定了第一条还是第二条会被匹配。
这一次，我们给出的结果会因为是哪一条被匹配而不一样，但两者都是同样正确的。

{::comment}
#### Exercise `erasure`
{:/}

#### 练习 `erasure`

{::comment}
Show that erasure relates corresponding boolean and decidable operations:
{:/}

证明擦除将对应的布尔值和可判定的值的操作联系了起来：

{% raw %}<pre class="Agda"><a id="25663" class="Keyword">postulate</a>
  <a id="∧-×"></a><a id="25675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#25675" class="Postulate">∧-×</a> <a id="25679" class="Symbol">:</a> <a id="25681" class="Symbol">∀</a> <a id="25683" class="Symbol">{</a><a id="25684" href="plfa.Decidable.html#25684" class="Bound">A</a> <a id="25686" href="plfa.Decidable.html#25686" class="Bound">B</a> <a id="25688" class="Symbol">:</a> <a id="25690" class="PrimitiveType">Set</a><a id="25693" class="Symbol">}</a> <a id="25695" class="Symbol">(</a><a id="25696" href="plfa.Decidable.html#25696" class="Bound">x</a> <a id="25698" class="Symbol">:</a> <a id="25700" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="25704" href="plfa.Decidable.html#25684" class="Bound">A</a><a id="25705" class="Symbol">)</a> <a id="25707" class="Symbol">(</a><a id="25708" href="plfa.Decidable.html#25708" class="Bound">y</a> <a id="25710" class="Symbol">:</a> <a id="25712" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="25716" href="plfa.Decidable.html#25686" class="Bound">B</a><a id="25717" class="Symbol">)</a> <a id="25719" class="Symbol">→</a> <a id="25721" href="plfa.Decidable.html#17207" class="Function Operator">⌊</a> <a id="25723" href="plfa.Decidable.html#25696" class="Bound">x</a> <a id="25725" href="plfa.Decidable.html#17207" class="Function Operator">⌋</a> <a id="25727" href="plfa.Decidable.html#18799" class="Function Operator">∧</a> <a id="25729" href="plfa.Decidable.html#17207" class="Function Operator">⌊</a> <a id="25731" href="plfa.Decidable.html#25708" class="Bound">y</a> <a id="25733" href="plfa.Decidable.html#17207" class="Function Operator">⌋</a> <a id="25735" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="25737" href="plfa.Decidable.html#17207" class="Function Operator">⌊</a> <a id="25739" href="plfa.Decidable.html#25696" class="Bound">x</a> <a id="25741" href="plfa.Decidable.html#19373" class="Function Operator">×-dec</a> <a id="25747" href="plfa.Decidable.html#25708" class="Bound">y</a> <a id="25749" href="plfa.Decidable.html#17207" class="Function Operator">⌋</a>
  <a id="∨-⊎"></a><a id="25753" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#25753" class="Postulate">∨-⊎</a> <a id="25757" class="Symbol">:</a> <a id="25759" class="Symbol">∀</a> <a id="25761" class="Symbol">{</a><a id="25762" href="plfa.Decidable.html#25762" class="Bound">A</a> <a id="25764" href="plfa.Decidable.html#25764" class="Bound">B</a> <a id="25766" class="Symbol">:</a> <a id="25768" class="PrimitiveType">Set</a><a id="25771" class="Symbol">}</a> <a id="25773" class="Symbol">(</a><a id="25774" href="plfa.Decidable.html#25774" class="Bound">x</a> <a id="25776" class="Symbol">:</a> <a id="25778" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="25782" href="plfa.Decidable.html#25762" class="Bound">A</a><a id="25783" class="Symbol">)</a> <a id="25785" class="Symbol">(</a><a id="25786" href="plfa.Decidable.html#25786" class="Bound">y</a> <a id="25788" class="Symbol">:</a> <a id="25790" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="25794" href="plfa.Decidable.html#25764" class="Bound">B</a><a id="25795" class="Symbol">)</a> <a id="25797" class="Symbol">→</a> <a id="25799" href="plfa.Decidable.html#17207" class="Function Operator">⌊</a> <a id="25801" href="plfa.Decidable.html#25774" class="Bound">x</a> <a id="25803" href="plfa.Decidable.html#17207" class="Function Operator">⌋</a> <a id="25805" href="plfa.Decidable.html#20610" class="Function Operator">∨</a> <a id="25807" href="plfa.Decidable.html#17207" class="Function Operator">⌊</a> <a id="25809" href="plfa.Decidable.html#25786" class="Bound">y</a> <a id="25811" href="plfa.Decidable.html#17207" class="Function Operator">⌋</a> <a id="25813" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="25815" href="plfa.Decidable.html#17207" class="Function Operator">⌊</a> <a id="25817" href="plfa.Decidable.html#25774" class="Bound">x</a> <a id="25819" href="plfa.Decidable.html#21187" class="Function Operator">⊎-dec</a> <a id="25825" href="plfa.Decidable.html#25786" class="Bound">y</a> <a id="25827" href="plfa.Decidable.html#17207" class="Function Operator">⌋</a>
  <a id="not-¬"></a><a id="25831" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#25831" class="Postulate">not-¬</a> <a id="25837" class="Symbol">:</a> <a id="25839" class="Symbol">∀</a> <a id="25841" class="Symbol">{</a><a id="25842" href="plfa.Decidable.html#25842" class="Bound">A</a> <a id="25844" class="Symbol">:</a> <a id="25846" class="PrimitiveType">Set</a><a id="25849" class="Symbol">}</a> <a id="25851" class="Symbol">(</a><a id="25852" href="plfa.Decidable.html#25852" class="Bound">x</a> <a id="25854" class="Symbol">:</a> <a id="25856" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="25860" href="plfa.Decidable.html#25842" class="Bound">A</a><a id="25861" class="Symbol">)</a> <a id="25863" class="Symbol">→</a> <a id="25865" href="plfa.Decidable.html#22342" class="Function">not</a> <a id="25869" href="plfa.Decidable.html#17207" class="Function Operator">⌊</a> <a id="25871" href="plfa.Decidable.html#25852" class="Bound">x</a> <a id="25873" href="plfa.Decidable.html#17207" class="Function Operator">⌋</a> <a id="25875" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="25877" href="plfa.Decidable.html#17207" class="Function Operator">⌊</a> <a id="25879" href="plfa.Decidable.html#22526" class="Function">¬?</a> <a id="25882" href="plfa.Decidable.html#25852" class="Bound">x</a> <a id="25884" href="plfa.Decidable.html#17207" class="Function Operator">⌋</a>
</pre>{% endraw %}
{::comment}
#### Exercise `iff-erasure` (recommended)
{:/}

#### 练习 `iff-erasure` （推荐）

{::comment}
Give analogues of the `_⇔_` operation from
Chapter [Isomorphism]({{ site.baseurl }}/Isomorphism/#iff),
operation on booleans and decidables, and also show the corresponding erasure:
{:/}

给出与 [Isomorphism][plfa.Isomorphism#iff] 章节中 `_↔_` 相对应的布尔值与可判定的值的操作，
并证明其对应的擦除：

{% raw %}<pre class="Agda"><a id="26263" class="Keyword">postulate</a>
  <a id="_iff_"></a><a id="26275" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#26275" class="Postulate Operator">_iff_</a> <a id="26281" class="Symbol">:</a> <a id="26283" href="plfa.Decidable.html#2594" class="Datatype">Bool</a> <a id="26288" class="Symbol">→</a> <a id="26290" href="plfa.Decidable.html#2594" class="Datatype">Bool</a> <a id="26295" class="Symbol">→</a> <a id="26297" href="plfa.Decidable.html#2594" class="Datatype">Bool</a>
  <a id="_⇔-dec_"></a><a id="26304" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#26304" class="Postulate Operator">_⇔-dec_</a> <a id="26312" class="Symbol">:</a> <a id="26314" class="Symbol">∀</a> <a id="26316" class="Symbol">{</a><a id="26317" href="plfa.Decidable.html#26317" class="Bound">A</a> <a id="26319" href="plfa.Decidable.html#26319" class="Bound">B</a> <a id="26321" class="Symbol">:</a> <a id="26323" class="PrimitiveType">Set</a><a id="26326" class="Symbol">}</a> <a id="26328" class="Symbol">→</a> <a id="26330" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="26334" href="plfa.Decidable.html#26317" class="Bound">A</a> <a id="26336" class="Symbol">→</a> <a id="26338" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="26342" href="plfa.Decidable.html#26319" class="Bound">B</a> <a id="26344" class="Symbol">→</a> <a id="26346" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="26350" class="Symbol">(</a><a id="26351" href="plfa.Decidable.html#26317" class="Bound">A</a> <a id="26353" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15256" class="Record Operator">⇔</a> <a id="26355" href="plfa.Decidable.html#26319" class="Bound">B</a><a id="26356" class="Symbol">)</a>
  <a id="iff-⇔"></a><a id="26360" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#26360" class="Postulate">iff-⇔</a> <a id="26366" class="Symbol">:</a> <a id="26368" class="Symbol">∀</a> <a id="26370" class="Symbol">{</a><a id="26371" href="plfa.Decidable.html#26371" class="Bound">A</a> <a id="26373" href="plfa.Decidable.html#26373" class="Bound">B</a> <a id="26375" class="Symbol">:</a> <a id="26377" class="PrimitiveType">Set</a><a id="26380" class="Symbol">}</a> <a id="26382" class="Symbol">(</a><a id="26383" href="plfa.Decidable.html#26383" class="Bound">x</a> <a id="26385" class="Symbol">:</a> <a id="26387" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="26391" href="plfa.Decidable.html#26371" class="Bound">A</a><a id="26392" class="Symbol">)</a> <a id="26394" class="Symbol">(</a><a id="26395" href="plfa.Decidable.html#26395" class="Bound">y</a> <a id="26397" class="Symbol">:</a> <a id="26399" href="plfa.Decidable.html#10006" class="Datatype">Dec</a> <a id="26403" href="plfa.Decidable.html#26373" class="Bound">B</a><a id="26404" class="Symbol">)</a> <a id="26406" class="Symbol">→</a> <a id="26408" href="plfa.Decidable.html#17207" class="Function Operator">⌊</a> <a id="26410" href="plfa.Decidable.html#26383" class="Bound">x</a> <a id="26412" href="plfa.Decidable.html#17207" class="Function Operator">⌋</a> <a id="26414" href="plfa.Decidable.html#26275" class="Postulate Operator">iff</a> <a id="26418" href="plfa.Decidable.html#17207" class="Function Operator">⌊</a> <a id="26420" href="plfa.Decidable.html#26395" class="Bound">y</a> <a id="26422" href="plfa.Decidable.html#17207" class="Function Operator">⌋</a> <a id="26424" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="26426" href="plfa.Decidable.html#17207" class="Function Operator">⌊</a> <a id="26428" href="plfa.Decidable.html#26383" class="Bound">x</a> <a id="26430" href="plfa.Decidable.html#26304" class="Postulate Operator">⇔-dec</a> <a id="26436" href="plfa.Decidable.html#26395" class="Bound">y</a> <a id="26438" href="plfa.Decidable.html#17207" class="Function Operator">⌋</a>
</pre>{% endraw %}
{::comment}
{% raw %}<pre class="Agda"><a id="26461" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="26498" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
## Standard Library
{:/}

## 标准库

{% raw %}<pre class="Agda"><a id="26566" class="Keyword">import</a> <a id="26573" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html" class="Module">Data.Bool.Base</a> <a id="26588" class="Keyword">using</a> <a id="26594" class="Symbol">(</a><a id="26595" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a><a id="26599" class="Symbol">;</a> <a id="26601" href="Agda.Builtin.Bool.html#160" class="InductiveConstructor">true</a><a id="26605" class="Symbol">;</a> <a id="26607" href="Agda.Builtin.Bool.html#154" class="InductiveConstructor">false</a><a id="26612" class="Symbol">;</a> <a id="26614" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1480" class="Function">T</a><a id="26615" class="Symbol">;</a> <a id="26617" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1015" class="Function Operator">_∧_</a><a id="26620" class="Symbol">;</a> <a id="26622" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1073" class="Function Operator">_∨_</a><a id="26625" class="Symbol">;</a> <a id="26627" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#961" class="Function">not</a><a id="26630" class="Symbol">)</a>
<a id="26632" class="Keyword">import</a> <a id="26639" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="26648" class="Keyword">using</a> <a id="26654" class="Symbol">(</a><a id="26655" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#4585" class="Function Operator">_≤?_</a><a id="26659" class="Symbol">)</a>
<a id="26661" class="Keyword">import</a> <a id="26668" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="26685" class="Keyword">using</a> <a id="26691" class="Symbol">(</a><a id="26692" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a><a id="26695" class="Symbol">;</a> <a id="26697" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a><a id="26700" class="Symbol">;</a> <a id="26702" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a><a id="26704" class="Symbol">)</a>
<a id="26706" class="Keyword">import</a> <a id="26713" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.html" class="Module">Relation.Nullary.Decidable</a> <a id="26740" class="Keyword">using</a> <a id="26746" class="Symbol">(</a><a id="26747" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊_⌋</a><a id="26750" class="Symbol">;</a> <a id="26752" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#926" class="Function">toWitness</a><a id="26761" class="Symbol">;</a> <a id="26763" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#1062" class="Function">fromWitness</a><a id="26774" class="Symbol">)</a>
<a id="26776" class="Keyword">import</a> <a id="26783" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="26809" class="Keyword">using</a> <a id="26815" class="Symbol">(</a><a id="26816" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#1115" class="Function">¬?</a><a id="26818" class="Symbol">)</a>
<a id="26820" class="Keyword">import</a> <a id="26827" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Product.html" class="Module">Relation.Nullary.Product</a> <a id="26852" class="Keyword">using</a> <a id="26858" class="Symbol">(</a><a id="26859" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Product.html#585" class="Function Operator">_×-dec_</a><a id="26866" class="Symbol">)</a>
<a id="26868" class="Keyword">import</a> <a id="26875" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Sum.html" class="Module">Relation.Nullary.Sum</a> <a id="26896" class="Keyword">using</a> <a id="26902" class="Symbol">(</a><a id="26903" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Sum.html#668" class="Function Operator">_⊎-dec_</a><a id="26910" class="Symbol">)</a>
<a id="26912" class="Keyword">import</a> <a id="26919" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.html" class="Module">Relation.Binary</a> <a id="26935" class="Keyword">using</a> <a id="26941" class="Symbol">(</a><a id="26942" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.Core.html#5557" class="Function">Decidable</a><a id="26951" class="Symbol">)</a>
</pre>{% endraw %}

## Unicode

{::comment}
    ∧  U+2227  LOGICAL AND (\and, \wedge)
    ∨  U+2228  LOGICAL OR (\or, \vee)
    ⊃  U+2283  SUPERSET OF (\sup)
    ᵇ  U+1D47  MODIFIER LETTER SMALL B  (\^b)
    ⌊  U+230A  LEFT FLOOR (\cll)
    ⌋  U+230B  RIGHT FLOOR (\clr)
{:/}

    ∧  U+2227  逻辑和 (\and, \wedge)
    ∨  U+2228  逻辑或 (\or, \vee)
    ⊃  U+2283  超集 (\sup)
    ᵇ  U+1D47  修饰符小写 B  (\^b)
    ⌊  U+230A  左向下取整 (\cll)
    ⌋  U+230B  右向下取整 (\clr)
