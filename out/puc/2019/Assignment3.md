---
src       : "courses/puc/2019/Assignment3.lagda.md"
title     : "Assignment3: PUC Assignment 3"
layout    : page
permalink : /PUC/2019/Assignment3/
---

{% raw %}<pre class="Agda"><a id="110" class="Keyword">module</a> <a id="117" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}" class="Module">Assignment3</a> <a id="129" class="Keyword">where</a>
</pre>{% endraw %}
## YOUR NAME AND EMAIL GOES HERE

## Introduction

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises without a label are optional, and may be done if you want
some extra practice.

Please ensure your files execute correctly under Agda!

## Imports

{% raw %}<pre class="Agda"><a id="555" class="Keyword">import</a> <a id="562" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="600" class="Symbol">as</a> <a id="603" class="Module">Eq</a>
<a id="606" class="Keyword">open</a> <a id="611" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="614" class="Keyword">using</a> <a id="620" class="Symbol">(</a><a id="621" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="624" class="Symbol">;</a> <a id="626" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="630" class="Symbol">;</a> <a id="632" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a><a id="636" class="Symbol">;</a> <a id="638" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#939" class="Function">sym</a><a id="641" class="Symbol">)</a>
<a id="643" class="Keyword">open</a> <a id="648" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2499" class="Module">Eq.≡-Reasoning</a> <a id="663" class="Keyword">using</a> <a id="669" class="Symbol">(</a><a id="670" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin_</a><a id="676" class="Symbol">;</a> <a id="678" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">_≡⟨⟩_</a><a id="683" class="Symbol">;</a> <a id="685" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">_≡⟨_⟩_</a><a id="691" class="Symbol">;</a> <a id="693" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">_∎</a><a id="695" class="Symbol">)</a>
<a id="697" class="Keyword">open</a> <a id="702" class="Keyword">import</a> <a id="709" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html" class="Module">Data.Bool.Base</a> <a id="724" class="Keyword">using</a> <a id="730" class="Symbol">(</a><a id="731" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a><a id="735" class="Symbol">;</a> <a id="737" href="Agda.Builtin.Bool.html#160" class="InductiveConstructor">true</a><a id="741" class="Symbol">;</a> <a id="743" href="Agda.Builtin.Bool.html#154" class="InductiveConstructor">false</a><a id="748" class="Symbol">;</a> <a id="750" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1480" class="Function">T</a><a id="751" class="Symbol">;</a> <a id="753" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1015" class="Function Operator">_∧_</a><a id="756" class="Symbol">;</a> <a id="758" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1073" class="Function Operator">_∨_</a><a id="761" class="Symbol">;</a> <a id="763" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#961" class="Function">not</a><a id="766" class="Symbol">)</a>
<a id="768" class="Keyword">open</a> <a id="773" class="Keyword">import</a> <a id="780" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="789" class="Keyword">using</a> <a id="795" class="Symbol">(</a><a id="796" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="797" class="Symbol">;</a> <a id="799" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="803" class="Symbol">;</a> <a id="805" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="808" class="Symbol">;</a> <a id="810" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="813" class="Symbol">;</a> <a id="815" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">_*_</a><a id="818" class="Symbol">;</a> <a id="820" href="Agda.Builtin.Nat.html#388" class="Primitive Operator">_∸_</a><a id="823" class="Symbol">;</a> <a id="825" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#895" class="Datatype Operator">_≤_</a><a id="828" class="Symbol">;</a> <a id="830" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#960" class="InductiveConstructor">s≤s</a><a id="833" class="Symbol">;</a> <a id="835" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#918" class="InductiveConstructor">z≤n</a><a id="838" class="Symbol">)</a>
<a id="840" class="Keyword">open</a> <a id="845" class="Keyword">import</a> <a id="852" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="872" class="Keyword">using</a>
  <a id="880" class="Symbol">(</a><a id="881" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11578" class="Function">+-assoc</a><a id="888" class="Symbol">;</a> <a id="890" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11679" class="Function">+-identityˡ</a><a id="901" class="Symbol">;</a> <a id="903" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11734" class="Function">+-identityʳ</a><a id="914" class="Symbol">;</a> <a id="916" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#18464" class="Function">*-assoc</a><a id="923" class="Symbol">;</a> <a id="925" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#17362" class="Function">*-identityˡ</a><a id="936" class="Symbol">;</a> <a id="938" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#17426" class="Function">*-identityʳ</a><a id="949" class="Symbol">)</a>
<a id="951" class="Keyword">open</a> <a id="956" class="Keyword">import</a> <a id="963" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="980" class="Keyword">using</a> <a id="986" class="Symbol">(</a><a id="987" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="989" class="Symbol">;</a> <a id="991" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a><a id="994" class="Symbol">;</a> <a id="996" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a><a id="999" class="Symbol">;</a> <a id="1001" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a><a id="1003" class="Symbol">)</a>
<a id="1005" class="Keyword">open</a> <a id="1010" class="Keyword">import</a> <a id="1017" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="1030" class="Keyword">using</a> <a id="1036" class="Symbol">(</a><a id="1037" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">_×_</a><a id="1040" class="Symbol">;</a> <a id="1042" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1364" class="Function">∃</a><a id="1043" class="Symbol">;</a> <a id="1045" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃-syntax</a><a id="1053" class="Symbol">)</a> <a id="1055" class="Keyword">renaming</a> <a id="1064" class="Symbol">(</a><a id="1065" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a> <a id="1069" class="Symbol">to</a> <a id="1072" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="1077" class="Symbol">)</a>
<a id="1079" class="Keyword">open</a> <a id="1084" class="Keyword">import</a> <a id="1091" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html" class="Module">Data.Empty</a> <a id="1102" class="Keyword">using</a> <a id="1108" class="Symbol">(</a><a id="1109" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a><a id="1110" class="Symbol">;</a> <a id="1112" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a><a id="1118" class="Symbol">)</a>
<a id="1120" class="Keyword">open</a> <a id="1125" class="Keyword">import</a> <a id="1132" href="https://agda.github.io/agda-stdlib/v1.1/Function.html" class="Module">Function</a> <a id="1141" class="Keyword">using</a> <a id="1147" class="Symbol">(</a><a id="1148" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">_∘_</a><a id="1151" class="Symbol">)</a>
<a id="1153" class="Keyword">open</a> <a id="1158" class="Keyword">import</a> <a id="1165" href="https://agda.github.io/agda-stdlib/v1.1/Algebra.Structures.html" class="Module">Algebra.Structures</a> <a id="1184" class="Keyword">using</a> <a id="1190" class="Symbol">(</a><a id="1191" href="https://agda.github.io/agda-stdlib/v1.1/Algebra.Structures.html#2215" class="Record">IsMonoid</a><a id="1199" class="Symbol">)</a>
<a id="1201" class="Keyword">open</a> <a id="1206" class="Keyword">import</a> <a id="1213" href="https://agda.github.io/agda-stdlib/v1.1/Level.html" class="Module">Level</a> <a id="1219" class="Keyword">using</a> <a id="1225" class="Symbol">(</a><a id="1226" href="Agda.Primitive.html#408" class="Postulate">Level</a><a id="1231" class="Symbol">)</a>
<a id="1233" class="Keyword">open</a> <a id="1238" class="Keyword">import</a> <a id="1245" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Unary.html" class="Module">Relation.Unary</a> <a id="1260" class="Keyword">using</a> <a id="1266" class="Symbol">(</a><a id="1267" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Unary.html#3474" class="Function">Decidable</a><a id="1276" class="Symbol">)</a>
<a id="1278" class="Keyword">open</a> <a id="1283" class="Keyword">import</a> <a id="1290" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}" class="Module">plfa.Relations</a> <a id="1305" class="Keyword">using</a> <a id="1311" class="Symbol">(</a><a id="1312" href="plfa.Relations.html#26522" class="Datatype Operator">_&lt;_</a><a id="1315" class="Symbol">;</a> <a id="1317" href="plfa.Relations.html#26549" class="InductiveConstructor">z&lt;s</a><a id="1320" class="Symbol">;</a> <a id="1322" href="plfa.Relations.html#26606" class="InductiveConstructor">s&lt;s</a><a id="1325" class="Symbol">)</a>
<a id="1327" class="Keyword">open</a> <a id="1332" class="Keyword">import</a> <a id="1339" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}" class="Module">plfa.Isomorphism</a> <a id="1356" class="Keyword">using</a> <a id="1362" class="Symbol">(</a><a id="1363" href="plfa.Isomorphism.html#5843" class="Record Operator">_≃_</a><a id="1366" class="Symbol">;</a> <a id="1368" href="plfa.Isomorphism.html#9378" class="Function">≃-sym</a><a id="1373" class="Symbol">;</a> <a id="1375" href="plfa.Isomorphism.html#9775" class="Function">≃-trans</a><a id="1382" class="Symbol">;</a> <a id="1384" href="plfa.Isomorphism.html#11919" class="Record Operator">_≲_</a><a id="1387" class="Symbol">;</a> <a id="1389" href="plfa.Isomorphism.html#3758" class="Postulate">extensionality</a><a id="1403" class="Symbol">)</a>
<a id="1405" class="Keyword">open</a> <a id="1410" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10987" class="Module">plfa.Isomorphism.≃-Reasoning</a>
<a id="1439" class="Keyword">open</a> <a id="1444" class="Keyword">import</a> <a id="1451" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lists.md %}{% raw %}" class="Module">plfa.Lists</a> <a id="1462" class="Keyword">using</a> <a id="1468" class="Symbol">(</a><a id="1469" href="plfa.Lists.html#1284" class="Datatype">List</a><a id="1473" class="Symbol">;</a> <a id="1475" href="plfa.Lists.html#1313" class="InductiveConstructor">[]</a><a id="1477" class="Symbol">;</a> <a id="1479" href="plfa.Lists.html#1328" class="InductiveConstructor Operator">_∷_</a><a id="1482" class="Symbol">;</a> <a id="1484" href="plfa.Lists.html#3818" class="Operator">[_]</a><a id="1487" class="Symbol">;</a> <a id="1489" href="plfa.Lists.html#3841" class="Operator">[_,_]</a><a id="1494" class="Symbol">;</a> <a id="1496" href="plfa.Lists.html#3872" class="Operator">[_,_,_]</a><a id="1503" class="Symbol">;</a> <a id="1505" href="plfa.Lists.html#3911" class="Operator">[_,_,_,_]</a><a id="1514" class="Symbol">;</a>
  <a id="1518" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lists.md %}{% raw %}#4651" class="Function Operator">_++_</a><a id="1522" class="Symbol">;</a> <a id="1524" href="plfa.Lists.html#10957" class="Function">reverse</a><a id="1531" class="Symbol">;</a> <a id="1533" href="plfa.Lists.html#16959" class="Function">map</a><a id="1536" class="Symbol">;</a> <a id="1538" href="plfa.Lists.html#20225" class="Function">foldr</a><a id="1543" class="Symbol">;</a> <a id="1545" href="plfa.Lists.html#21337" class="Function">sum</a><a id="1548" class="Symbol">;</a> <a id="1550" href="plfa.Lists.html#27650" class="Datatype">All</a><a id="1553" class="Symbol">;</a> <a id="1555" href="plfa.Lists.html#29796" class="Datatype">Any</a><a id="1558" class="Symbol">;</a> <a id="1560" href="plfa.Lists.html#29847" class="InductiveConstructor">here</a><a id="1564" class="Symbol">;</a> <a id="1566" href="plfa.Lists.html#29904" class="InductiveConstructor">there</a><a id="1571" class="Symbol">;</a> <a id="1573" href="plfa.Lists.html#30311" class="Function Operator">_∈_</a><a id="1576" class="Symbol">)</a>
<a id="1578" class="Keyword">open</a> <a id="1583" class="Keyword">import</a> <a id="1590" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}" class="Module">plfa.Lambda</a> <a id="1602" class="Keyword">hiding</a> <a id="1609" class="Symbol">(</a><a id="1610" href="plfa.Lambda.html#7314" class="Function Operator">ƛ′_⇒_</a><a id="1615" class="Symbol">;</a> <a id="1617" href="plfa.Lambda.html#7435" class="Function Operator">case′_[zero⇒_|suc_⇒_]</a><a id="1638" class="Symbol">;</a> <a id="1640" href="plfa.Lambda.html#7649" class="Function Operator">μ′_⇒_</a><a id="1645" class="Symbol">;</a> <a id="1647" href="plfa.Lambda.html#7833" class="Function">plus′</a><a id="1652" class="Symbol">)</a>
<a id="1654" class="Keyword">open</a> <a id="1659" class="Keyword">import</a> <a id="1666" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Properties.md %}{% raw %}" class="Module">plfa.Properties</a> <a id="1682" class="Keyword">hiding</a> <a id="1689" class="Symbol">(</a><a id="1690" href="plfa.Properties.html#11716" class="Postulate">value?</a><a id="1696" class="Symbol">;</a> <a id="1698" href="plfa.Properties.html#41540" class="Postulate">unstuck</a><a id="1705" class="Symbol">;</a> <a id="1707" href="plfa.Properties.html#41740" class="Postulate">preserves</a><a id="1716" class="Symbol">;</a> <a id="1718" href="plfa.Properties.html#41977" class="Postulate">wttdgs</a><a id="1724" class="Symbol">)</a>
</pre>{% endraw %}
## Lambda

#### Exercise `mul` (recommended)

Write out the definition of a lambda term that multiplies
two natural numbers.


#### Exercise `primed` (stretch)

We can make examples with lambda terms slightly easier to write
by adding the following definitions.
{% raw %}<pre class="Agda"><a id="ƛ′_⇒_"></a><a id="1997" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#1997" class="Function Operator">ƛ′_⇒_</a> <a id="2003" class="Symbol">:</a> <a id="2005" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3748" class="Datatype">Term</a> <a id="2010" class="Symbol">→</a> <a id="2012" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="2017" class="Symbol">→</a> <a id="2019" href="plfa.Lambda.html#3748" class="Datatype">Term</a>
<a id="2024" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#1997" class="Function Operator">ƛ′</a> <a id="2027" class="Symbol">(</a><a id="2028" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3767" class="InductiveConstructor Operator">`</a> <a id="2030" href="Assignment3.html#2030" class="Bound">x</a><a id="2031" class="Symbol">)</a> <a id="2033" href="Assignment3.html#1997" class="Function Operator">⇒</a> <a id="2035" href="Assignment3.html#2035" class="Bound">N</a>  <a id="2038" class="Symbol">=</a>  <a id="2041" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="2043" href="Assignment3.html#2030" class="Bound">x</a> <a id="2045" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="2047" href="Assignment3.html#2035" class="Bound">N</a>
<a id="2049" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#1997" class="CatchallClause Function Operator">ƛ′</a><a id="2051" class="CatchallClause"> </a><a id="2052" class="CatchallClause Symbol">_</a><a id="2053" class="CatchallClause"> </a><a id="2054" href="Assignment3.html#1997" class="CatchallClause Function Operator">⇒</a><a id="2055" class="CatchallClause"> </a><a id="2056" class="CatchallClause Symbol">_</a>      <a id="2063" class="Symbol">=</a>  <a id="2066" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="2073" href="Assignment3.html#2102" class="Postulate">impossible</a>
  <a id="2086" class="Keyword">where</a> <a id="2092" class="Keyword">postulate</a> <a id="2102" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2102" class="Postulate">impossible</a> <a id="2113" class="Symbol">:</a> <a id="2115" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>

<a id="case′_[zero⇒_|suc_⇒_]"></a><a id="2118" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2118" class="Function Operator">case′_[zero⇒_|suc_⇒_]</a> <a id="2140" class="Symbol">:</a> <a id="2142" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3748" class="Datatype">Term</a> <a id="2147" class="Symbol">→</a> <a id="2149" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="2154" class="Symbol">→</a> <a id="2156" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="2161" class="Symbol">→</a> <a id="2163" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="2168" class="Symbol">→</a> <a id="2170" href="plfa.Lambda.html#3748" class="Datatype">Term</a>
<a id="2175" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2118" class="Function Operator">case′</a> <a id="2181" href="Assignment3.html#2181" class="Bound">L</a> <a id="2183" href="Assignment3.html#2118" class="Function Operator">[zero⇒</a> <a id="2190" href="Assignment3.html#2190" class="Bound">M</a> <a id="2192" href="Assignment3.html#2118" class="Function Operator">|suc</a> <a id="2197" class="Symbol">(</a><a id="2198" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3767" class="InductiveConstructor Operator">`</a> <a id="2200" href="Assignment3.html#2200" class="Bound">x</a><a id="2201" class="Symbol">)</a> <a id="2203" href="Assignment3.html#2118" class="Function Operator">⇒</a> <a id="2205" href="Assignment3.html#2205" class="Bound">N</a> <a id="2207" href="Assignment3.html#2118" class="Function Operator">]</a>  <a id="2210" class="Symbol">=</a>  <a id="2213" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">case</a> <a id="2218" href="Assignment3.html#2181" class="Bound">L</a> <a id="2220" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">[zero⇒</a> <a id="2227" href="Assignment3.html#2190" class="Bound">M</a> <a id="2229" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">|suc</a> <a id="2234" href="Assignment3.html#2200" class="Bound">x</a> <a id="2236" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">⇒</a> <a id="2238" href="Assignment3.html#2205" class="Bound">N</a> <a id="2240" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">]</a>
<a id="2242" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2118" class="CatchallClause Function Operator">case′</a><a id="2247" class="CatchallClause"> </a><a id="2248" class="CatchallClause Symbol">_</a><a id="2249" class="CatchallClause"> </a><a id="2250" href="Assignment3.html#2118" class="CatchallClause Function Operator">[zero⇒</a><a id="2256" class="CatchallClause"> </a><a id="2257" class="CatchallClause Symbol">_</a><a id="2258" class="CatchallClause"> </a><a id="2259" href="Assignment3.html#2118" class="CatchallClause Function Operator">|suc</a><a id="2263" class="CatchallClause"> </a><a id="2264" class="CatchallClause Symbol">_</a><a id="2265" class="CatchallClause"> </a><a id="2266" href="Assignment3.html#2118" class="CatchallClause Function Operator">⇒</a><a id="2267" class="CatchallClause"> </a><a id="2268" class="CatchallClause Symbol">_</a><a id="2269" class="CatchallClause"> </a><a id="2270" href="Assignment3.html#2118" class="CatchallClause Function Operator">]</a>      <a id="2277" class="Symbol">=</a>  <a id="2280" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="2287" href="Assignment3.html#2316" class="Postulate">impossible</a>
  <a id="2300" class="Keyword">where</a> <a id="2306" class="Keyword">postulate</a> <a id="2316" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2316" class="Postulate">impossible</a> <a id="2327" class="Symbol">:</a> <a id="2329" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>

<a id="μ′_⇒_"></a><a id="2332" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2332" class="Function Operator">μ′_⇒_</a> <a id="2338" class="Symbol">:</a> <a id="2340" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3748" class="Datatype">Term</a> <a id="2345" class="Symbol">→</a> <a id="2347" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="2352" class="Symbol">→</a> <a id="2354" href="plfa.Lambda.html#3748" class="Datatype">Term</a>
<a id="2359" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2332" class="Function Operator">μ′</a> <a id="2362" class="Symbol">(</a><a id="2363" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3767" class="InductiveConstructor Operator">`</a> <a id="2365" href="Assignment3.html#2365" class="Bound">x</a><a id="2366" class="Symbol">)</a> <a id="2368" href="Assignment3.html#2332" class="Function Operator">⇒</a> <a id="2370" href="Assignment3.html#2370" class="Bound">N</a>  <a id="2373" class="Symbol">=</a>  <a id="2376" href="plfa.Lambda.html#4035" class="InductiveConstructor Operator">μ</a> <a id="2378" href="Assignment3.html#2365" class="Bound">x</a> <a id="2380" href="plfa.Lambda.html#4035" class="InductiveConstructor Operator">⇒</a> <a id="2382" href="Assignment3.html#2370" class="Bound">N</a>
<a id="2384" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2332" class="CatchallClause Function Operator">μ′</a><a id="2386" class="CatchallClause"> </a><a id="2387" class="CatchallClause Symbol">_</a><a id="2388" class="CatchallClause"> </a><a id="2389" href="Assignment3.html#2332" class="CatchallClause Function Operator">⇒</a><a id="2390" class="CatchallClause"> </a><a id="2391" class="CatchallClause Symbol">_</a>      <a id="2398" class="Symbol">=</a>  <a id="2401" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="2408" href="Assignment3.html#2437" class="Postulate">impossible</a>
  <a id="2421" class="Keyword">where</a> <a id="2427" class="Keyword">postulate</a> <a id="2437" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2437" class="Postulate">impossible</a> <a id="2448" class="Symbol">:</a> <a id="2450" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>
</pre>{% endraw %}The definition of `plus` can now be written as follows.
{% raw %}<pre class="Agda"><a id="plus′"></a><a id="2516" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2516" class="Function">plus′</a> <a id="2522" class="Symbol">:</a> <a id="2524" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3748" class="Datatype">Term</a>
<a id="2529" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2516" class="Function">plus′</a> <a id="2535" class="Symbol">=</a> <a id="2537" href="Assignment3.html#2332" class="Function Operator">μ′</a> <a id="2540" href="Assignment3.html#2647" class="Function">+</a> <a id="2542" href="Assignment3.html#2332" class="Function Operator">⇒</a> <a id="2544" href="Assignment3.html#1997" class="Function Operator">ƛ′</a> <a id="2547" href="Assignment3.html#2661" class="Function">m</a> <a id="2549" href="Assignment3.html#1997" class="Function Operator">⇒</a> <a id="2551" href="Assignment3.html#1997" class="Function Operator">ƛ′</a> <a id="2554" href="Assignment3.html#2675" class="Function">n</a> <a id="2556" href="Assignment3.html#1997" class="Function Operator">⇒</a>
          <a id="2568" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2118" class="Function Operator">case′</a> <a id="2574" href="Assignment3.html#2661" class="Function">m</a>
            <a id="2588" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2118" class="Function Operator">[zero⇒</a> <a id="2595" href="Assignment3.html#2675" class="Function">n</a>
            <a id="2609" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2118" class="Function Operator">|suc</a> <a id="2614" href="Assignment3.html#2661" class="Function">m</a> <a id="2616" href="Assignment3.html#2118" class="Function Operator">⇒</a> <a id="2618" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3934" class="InductiveConstructor Operator">`suc</a> <a id="2623" class="Symbol">(</a><a id="2624" href="Assignment3.html#2647" class="Function">+</a> <a id="2626" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="2628" href="Assignment3.html#2661" class="Function">m</a> <a id="2630" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="2632" href="Assignment3.html#2675" class="Function">n</a><a id="2633" class="Symbol">)</a> <a id="2635" href="Assignment3.html#2118" class="Function Operator">]</a>
  <a id="2639" class="Keyword">where</a>
  <a id="2647" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2647" class="Function">+</a>  <a id="2650" class="Symbol">=</a>  <a id="2653" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3767" class="InductiveConstructor Operator">`</a> <a id="2655" class="String">&quot;+&quot;</a>
  <a id="2661" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2661" class="Function">m</a>  <a id="2664" class="Symbol">=</a>  <a id="2667" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3767" class="InductiveConstructor Operator">`</a> <a id="2669" class="String">&quot;m&quot;</a>
  <a id="2675" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#2675" class="Function">n</a>  <a id="2678" class="Symbol">=</a>  <a id="2681" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3767" class="InductiveConstructor Operator">`</a> <a id="2683" class="String">&quot;n&quot;</a>
</pre>{% endraw %}Write out the definition of multiplication in the same style.

#### Exercise `_[_:=_]′` (stretch)

The definition of substitution above has three clauses (`ƛ`, `case`,
and `μ`) that invoke a with clause to deal with bound variables.
Rewrite the definition to factor the common part of these three
clauses into a single function, defined by mutual recursion with
substitution.


#### Exercise `—↠≲—↠′`

Show that the first notion of reflexive and transitive closure
above embeds into the second. Why are they not isomorphic?


#### Exercise `plus-example`

Write out the reduction sequence demonstrating that one plus one is two.


#### Exercise `mul-type` (recommended)

Using the term `mul` you defined earlier, write out the derivation
showing that it is well-typed.


## Properties


#### Exercise `Progress-≃`

Show that `Progress M` is isomorphic to `Value M ⊎ ∃[ N ](M —→ N)`.


#### Exercise `progress′`

Write out the proof of `progress′` in full, and compare it to the
proof of `progress` above.


#### Exercise `value?`

Combine `progress` and `—→¬V` to write a program that decides
whether a well-typed term is a value.
{% raw %}<pre class="Agda"><a id="3826" class="Keyword">postulate</a>
  <a id="value?"></a><a id="3838" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment3.md %}{% raw %}#3838" class="Postulate">value?</a> <a id="3845" class="Symbol">:</a> <a id="3847" class="Symbol">∀</a> <a id="3849" class="Symbol">{</a><a id="3850" href="Assignment3.html#3850" class="Bound">A</a> <a id="3852" href="Assignment3.html#3852" class="Bound">M</a><a id="3853" class="Symbol">}</a> <a id="3855" class="Symbol">→</a> <a id="3857" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#31053" class="InductiveConstructor">∅</a> <a id="3859" href="plfa.Lambda.html#33418" class="Datatype Operator">⊢</a> <a id="3861" href="Assignment3.html#3852" class="Bound">M</a> <a id="3863" href="plfa.Lambda.html#33418" class="Datatype Operator">⦂</a> <a id="3865" href="Assignment3.html#3850" class="Bound">A</a> <a id="3867" class="Symbol">→</a> <a id="3869" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="3873" class="Symbol">(</a><a id="3874" href="plfa.Lambda.html#11536" class="Datatype">Value</a> <a id="3880" href="Assignment3.html#3852" class="Bound">M</a><a id="3881" class="Symbol">)</a>
</pre>{% endraw %}

#### Exercise `subst′` (stretch)

Rewrite `subst` to work with the modified definition `_[_:=_]′`
from the exercise in the previous chapter.  As before, this
should factor dealing with bound variables into a single function,
defined by mutual recursion with the proof that substitution
preserves types.


#### Exercise `mul-example` (recommended)

Using the evaluator, confirm that two times two is four.


#### Exercise: `progress-preservation`

Without peeking at their statements above, write down the progress
and preservation theorems for the simply typed lambda-calculus.


#### Exercise `subject-expansion`

We say that `M` _reduces_ to `N` if `M —→ N`,
and conversely that `M` _expands_ to `N` if `N —→ M`.
The preservation property is sometimes called _subject reduction_.
Its opposite is _subject expansion_, which holds if
`M —→ N` and `∅ ⊢ N ⦂ A` imply `∅ ⊢ M ⦂ A`.
Find two counter-examples to subject expansion, one
with case expressions and one not involving case expressions.


#### Exercise `stuck`

Give an example of an ill-typed term that does get stuck.


#### Exercise `unstuck` (recommended)

Provide proofs of the three postulates, `unstuck`, `preserves`, and `wttdgs` above.
