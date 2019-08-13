---
src       : "courses/tspl/2018/Assignment2.lagda.md"
title     : "Assignment2: TSPL Assignment 2"
layout    : page
permalink : /TSPL/2018/Assignment2/
---

{% raw %}<pre class="Agda"><a id="112" class="Keyword">module</a> <a id="119" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}" class="Module">Assignment2</a> <a id="131" class="Keyword">where</a>
</pre>{% endraw %}
## YOUR NAME AND EMAIL GOES HERE

## Introduction

<!-- This assignment is due **4pm Thursday 18 October** (Week 5). -->

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises without a label are optional, and may be done if you want
some extra practice.

<!-- Submit your homework using the "submit" command. -->
Please ensure your files execute correctly under Agda!

## Imports

{% raw %}<pre class="Agda"><a id="686" class="Keyword">import</a> <a id="693" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="731" class="Symbol">as</a> <a id="734" class="Module">Eq</a>
<a id="737" class="Keyword">open</a> <a id="742" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="745" class="Keyword">using</a> <a id="751" class="Symbol">(</a><a id="752" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="755" class="Symbol">;</a> <a id="757" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="761" class="Symbol">;</a> <a id="763" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a><a id="767" class="Symbol">;</a> <a id="769" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#939" class="Function">sym</a><a id="772" class="Symbol">)</a>
<a id="774" class="Keyword">open</a> <a id="779" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2499" class="Module">Eq.≡-Reasoning</a> <a id="794" class="Keyword">using</a> <a id="800" class="Symbol">(</a><a id="801" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin_</a><a id="807" class="Symbol">;</a> <a id="809" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">_≡⟨⟩_</a><a id="814" class="Symbol">;</a> <a id="816" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">_≡⟨_⟩_</a><a id="822" class="Symbol">;</a> <a id="824" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">_∎</a><a id="826" class="Symbol">)</a>
<a id="828" class="Keyword">open</a> <a id="833" class="Keyword">import</a> <a id="840" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="849" class="Keyword">using</a> <a id="855" class="Symbol">(</a><a id="856" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="857" class="Symbol">;</a> <a id="859" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="863" class="Symbol">;</a> <a id="865" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="868" class="Symbol">;</a> <a id="870" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="873" class="Symbol">;</a> <a id="875" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">_*_</a><a id="878" class="Symbol">;</a> <a id="880" href="Agda.Builtin.Nat.html#388" class="Primitive Operator">_∸_</a><a id="883" class="Symbol">;</a> <a id="885" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#895" class="Datatype Operator">_≤_</a><a id="888" class="Symbol">;</a> <a id="890" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#918" class="InductiveConstructor">z≤n</a><a id="893" class="Symbol">;</a> <a id="895" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#960" class="InductiveConstructor">s≤s</a><a id="898" class="Symbol">)</a>
<a id="900" class="Keyword">open</a> <a id="905" class="Keyword">import</a> <a id="912" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="932" class="Keyword">using</a> <a id="938" class="Symbol">(</a><a id="939" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11578" class="Function">+-assoc</a><a id="946" class="Symbol">;</a> <a id="948" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11734" class="Function">+-identityʳ</a><a id="959" class="Symbol">;</a> <a id="961" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11370" class="Function">+-suc</a><a id="966" class="Symbol">;</a> <a id="968" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a><a id="974" class="Symbol">;</a>
  <a id="978" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3632" class="Function">≤-refl</a><a id="984" class="Symbol">;</a> <a id="986" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3815" class="Function">≤-trans</a><a id="993" class="Symbol">;</a> <a id="995" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3682" class="Function">≤-antisym</a><a id="1004" class="Symbol">;</a> <a id="1006" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3927" class="Function">≤-total</a><a id="1013" class="Symbol">;</a> <a id="1015" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15619" class="Function">+-monoʳ-≤</a><a id="1024" class="Symbol">;</a> <a id="1026" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15529" class="Function">+-monoˡ-≤</a><a id="1035" class="Symbol">;</a> <a id="1037" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15373" class="Function">+-mono-≤</a><a id="1045" class="Symbol">)</a>
<a id="1047" class="Keyword">open</a> <a id="1052" class="Keyword">import</a> <a id="1059" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}" class="Module">plfa.Relations</a> <a id="1074" class="Keyword">using</a> <a id="1080" class="Symbol">(</a><a id="1081" href="plfa.Relations.html#26522" class="Datatype Operator">_&lt;_</a><a id="1084" class="Symbol">;</a> <a id="1086" href="plfa.Relations.html#26549" class="InductiveConstructor">z&lt;s</a><a id="1089" class="Symbol">;</a> <a id="1091" href="plfa.Relations.html#26606" class="InductiveConstructor">s&lt;s</a><a id="1094" class="Symbol">)</a>
<a id="1096" class="Keyword">open</a> <a id="1101" class="Keyword">import</a> <a id="1108" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="1121" class="Keyword">using</a> <a id="1127" class="Symbol">(</a><a id="1128" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">_×_</a><a id="1131" class="Symbol">;</a> <a id="1133" href="Agda.Builtin.Sigma.html#225" class="Field">proj₁</a><a id="1138" class="Symbol">;</a> <a id="1140" href="Agda.Builtin.Sigma.html#237" class="Field">proj₂</a><a id="1145" class="Symbol">)</a> <a id="1147" class="Keyword">renaming</a> <a id="1156" class="Symbol">(</a><a id="1157" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a> <a id="1161" class="Symbol">to</a> <a id="1164" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="1169" class="Symbol">)</a>
<a id="1171" class="Keyword">open</a> <a id="1176" class="Keyword">import</a> <a id="1183" href="https://agda.github.io/agda-stdlib/v1.1/Data.Unit.html" class="Module">Data.Unit</a> <a id="1193" class="Keyword">using</a> <a id="1199" class="Symbol">(</a><a id="1200" href="Agda.Builtin.Unit.html#137" class="Record">⊤</a><a id="1201" class="Symbol">;</a> <a id="1203" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a><a id="1205" class="Symbol">)</a>
<a id="1207" class="Keyword">open</a> <a id="1212" class="Keyword">import</a> <a id="1219" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.html" class="Module">Data.Sum</a> <a id="1228" class="Keyword">using</a> <a id="1234" class="Symbol">(</a><a id="1235" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">_⊎_</a><a id="1238" class="Symbol">;</a> <a id="1240" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a><a id="1244" class="Symbol">;</a> <a id="1246" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a><a id="1250" class="Symbol">)</a> <a id="1252" class="Keyword">renaming</a> <a id="1261" class="Symbol">(</a><a id="1262" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#798" class="Function Operator">[_,_]</a> <a id="1268" class="Symbol">to</a> <a id="1271" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#798" class="Function Operator">case-⊎</a><a id="1277" class="Symbol">)</a>
<a id="1279" class="Keyword">open</a> <a id="1284" class="Keyword">import</a> <a id="1291" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html" class="Module">Data.Empty</a> <a id="1302" class="Keyword">using</a> <a id="1308" class="Symbol">(</a><a id="1309" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a><a id="1310" class="Symbol">;</a> <a id="1312" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a><a id="1318" class="Symbol">)</a>
<a id="1320" class="Keyword">open</a> <a id="1325" class="Keyword">import</a> <a id="1332" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html" class="Module">Data.Bool.Base</a> <a id="1347" class="Keyword">using</a> <a id="1353" class="Symbol">(</a><a id="1354" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a><a id="1358" class="Symbol">;</a> <a id="1360" href="Agda.Builtin.Bool.html#160" class="InductiveConstructor">true</a><a id="1364" class="Symbol">;</a> <a id="1366" href="Agda.Builtin.Bool.html#154" class="InductiveConstructor">false</a><a id="1371" class="Symbol">;</a> <a id="1373" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1480" class="Function">T</a><a id="1374" class="Symbol">;</a> <a id="1376" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1015" class="Function Operator">_∧_</a><a id="1379" class="Symbol">;</a> <a id="1381" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1073" class="Function Operator">_∨_</a><a id="1384" class="Symbol">;</a> <a id="1386" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#961" class="Function">not</a><a id="1389" class="Symbol">)</a>
<a id="1391" class="Keyword">open</a> <a id="1396" class="Keyword">import</a> <a id="1403" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="1420" class="Keyword">using</a> <a id="1426" class="Symbol">(</a><a id="1427" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="1429" class="Symbol">;</a> <a id="1431" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a><a id="1434" class="Symbol">;</a> <a id="1436" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a><a id="1439" class="Symbol">;</a> <a id="1441" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a><a id="1443" class="Symbol">)</a>
<a id="1445" class="Keyword">open</a> <a id="1450" class="Keyword">import</a> <a id="1457" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.html" class="Module">Relation.Nullary.Decidable</a> <a id="1484" class="Keyword">using</a> <a id="1490" class="Symbol">(</a><a id="1491" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊_⌋</a><a id="1494" class="Symbol">;</a> <a id="1496" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#926" class="Function">toWitness</a><a id="1505" class="Symbol">;</a> <a id="1507" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#1062" class="Function">fromWitness</a><a id="1518" class="Symbol">)</a>
<a id="1520" class="Keyword">open</a> <a id="1525" class="Keyword">import</a> <a id="1532" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="1558" class="Keyword">using</a> <a id="1564" class="Symbol">(</a><a id="1565" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#1115" class="Function">¬?</a><a id="1567" class="Symbol">)</a>
<a id="1569" class="Keyword">open</a> <a id="1574" class="Keyword">import</a> <a id="1581" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Product.html" class="Module">Relation.Nullary.Product</a> <a id="1606" class="Keyword">using</a> <a id="1612" class="Symbol">(</a><a id="1613" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Product.html#585" class="Function Operator">_×-dec_</a><a id="1620" class="Symbol">)</a>
<a id="1622" class="Keyword">open</a> <a id="1627" class="Keyword">import</a> <a id="1634" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Sum.html" class="Module">Relation.Nullary.Sum</a> <a id="1655" class="Keyword">using</a> <a id="1661" class="Symbol">(</a><a id="1662" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Sum.html#668" class="Function Operator">_⊎-dec_</a><a id="1669" class="Symbol">)</a>
<a id="1671" class="Keyword">open</a> <a id="1676" class="Keyword">import</a> <a id="1683" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="1709" class="Keyword">using</a> <a id="1715" class="Symbol">(</a><a id="1716" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#880" class="Function">contraposition</a><a id="1730" class="Symbol">)</a>
<a id="1732" class="Keyword">open</a> <a id="1737" class="Keyword">import</a> <a id="1744" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="1757" class="Keyword">using</a> <a id="1763" class="Symbol">(</a><a id="1764" href="Agda.Builtin.Sigma.html#139" class="Record">Σ</a><a id="1765" class="Symbol">;</a> <a id="1767" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a><a id="1770" class="Symbol">;</a> <a id="1772" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1364" class="Function">∃</a><a id="1773" class="Symbol">;</a> <a id="1775" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#911" class="Function">Σ-syntax</a><a id="1783" class="Symbol">;</a> <a id="1785" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃-syntax</a><a id="1793" class="Symbol">)</a>
<a id="1795" class="Keyword">open</a> <a id="1800" class="Keyword">import</a> <a id="1807" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}" class="Module">plfa.Relations</a> <a id="1822" class="Keyword">using</a> <a id="1828" class="Symbol">(</a><a id="1829" href="plfa.Relations.html#26522" class="Datatype Operator">_&lt;_</a><a id="1832" class="Symbol">;</a> <a id="1834" href="plfa.Relations.html#26549" class="InductiveConstructor">z&lt;s</a><a id="1837" class="Symbol">;</a> <a id="1839" href="plfa.Relations.html#26606" class="InductiveConstructor">s&lt;s</a><a id="1842" class="Symbol">)</a>
<a id="1844" class="Keyword">open</a> <a id="1849" class="Keyword">import</a> <a id="1856" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}" class="Module">plfa.Isomorphism</a> <a id="1873" class="Keyword">using</a> <a id="1879" class="Symbol">(</a><a id="1880" href="plfa.Isomorphism.html#5843" class="Record Operator">_≃_</a><a id="1883" class="Symbol">;</a> <a id="1885" href="plfa.Isomorphism.html#9378" class="Function">≃-sym</a><a id="1890" class="Symbol">;</a> <a id="1892" href="plfa.Isomorphism.html#9775" class="Function">≃-trans</a><a id="1899" class="Symbol">;</a> <a id="1901" href="plfa.Isomorphism.html#11919" class="Record Operator">_≲_</a><a id="1904" class="Symbol">;</a> <a id="1906" href="plfa.Isomorphism.html#3758" class="Postulate">extensionality</a><a id="1920" class="Symbol">)</a>
<a id="1922" class="Keyword">open</a> <a id="1927" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10987" class="Module">plfa.Isomorphism.≃-Reasoning</a>
</pre>{% endraw %}
## Equality

#### Exercise `≤-reasoning` (stretch)

The proof of monotonicity from
Chapter [Relations][plfa.Relations]
can be written in a more readable form by using an anologue of our
notation for `≡-reasoning`.  Define `≤-reasoning` analogously, and use
it to write out an alternative proof that addition is monotonic with
regard to inequality.  Rewrite both `+-monoˡ-≤` and `+-mono-≤`.



## Isomorphism

#### Exercise `≃-implies-≲`

Show that every isomorphism implies an embedding.
{% raw %}<pre class="Agda"><a id="2453" class="Keyword">postulate</a>
  <a id="≃-implies-≲"></a><a id="2465" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#2465" class="Postulate">≃-implies-≲</a> <a id="2477" class="Symbol">:</a> <a id="2479" class="Symbol">∀</a> <a id="2481" class="Symbol">{</a><a id="2482" href="Assignment2.html#2482" class="Bound">A</a> <a id="2484" href="Assignment2.html#2484" class="Bound">B</a> <a id="2486" class="Symbol">:</a> <a id="2488" class="PrimitiveType">Set</a><a id="2491" class="Symbol">}</a>
    <a id="2497" class="Symbol">→</a> <a id="2499" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#2482" class="Bound">A</a> <a id="2501" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5843" class="Record Operator">≃</a> <a id="2503" href="Assignment2.html#2484" class="Bound">B</a>
      <a id="2511" class="Comment">-----</a>
    <a id="2521" class="Symbol">→</a> <a id="2523" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#2482" class="Bound">A</a> <a id="2525" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11919" class="Record Operator">≲</a> <a id="2527" href="Assignment2.html#2484" class="Bound">B</a>
</pre>{% endraw %}
#### Exercise `_⇔_` (recommended) {#iff}

Define equivalence of propositions (also known as "if and only if") as follows.
{% raw %}<pre class="Agda"><a id="2660" class="Keyword">record</a> <a id="_⇔_"></a><a id="2667" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#2667" class="Record Operator">_⇔_</a> <a id="2671" class="Symbol">(</a><a id="2672" href="Assignment2.html#2672" class="Bound">A</a> <a id="2674" href="Assignment2.html#2674" class="Bound">B</a> <a id="2676" class="Symbol">:</a> <a id="2678" class="PrimitiveType">Set</a><a id="2681" class="Symbol">)</a> <a id="2683" class="Symbol">:</a> <a id="2685" class="PrimitiveType">Set</a> <a id="2689" class="Keyword">where</a>
  <a id="2697" class="Keyword">field</a>
    <a id="_⇔_.to"></a><a id="2707" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#2707" class="Field">to</a>   <a id="2712" class="Symbol">:</a> <a id="2714" href="Assignment2.html#2672" class="Bound">A</a> <a id="2716" class="Symbol">→</a> <a id="2718" href="Assignment2.html#2674" class="Bound">B</a>
    <a id="_⇔_.from"></a><a id="2724" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#2724" class="Field">from</a> <a id="2729" class="Symbol">:</a> <a id="2731" href="Assignment2.html#2674" class="Bound">B</a> <a id="2733" class="Symbol">→</a> <a id="2735" href="Assignment2.html#2672" class="Bound">A</a>

<a id="2738" class="Keyword">open</a> <a id="2743" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#2667" class="Module Operator">_⇔_</a>
</pre>{% endraw %}Show that equivalence is reflexive, symmetric, and transitive.

#### Exercise `Bin-embedding` (stretch) {#Bin-embedding}

Recall that Exercises
[Bin][plfa.Naturals#Bin] and
[Bin-laws][plfa.Induction#Bin-laws]
define a datatype of bitstrings representing natural numbers.
{% raw %}<pre class="Agda"><a id="3026" class="Keyword">data</a> <a id="Bin"></a><a id="3031" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#3031" class="Datatype">Bin</a> <a id="3035" class="Symbol">:</a> <a id="3037" class="PrimitiveType">Set</a> <a id="3041" class="Keyword">where</a>
  <a id="Bin.nil"></a><a id="3049" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#3049" class="InductiveConstructor">nil</a> <a id="3053" class="Symbol">:</a> <a id="3055" href="Assignment2.html#3031" class="Datatype">Bin</a>
  <a id="Bin.x0_"></a><a id="3061" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#3061" class="InductiveConstructor Operator">x0_</a> <a id="3065" class="Symbol">:</a> <a id="3067" href="Assignment2.html#3031" class="Datatype">Bin</a> <a id="3071" class="Symbol">→</a> <a id="3073" href="Assignment2.html#3031" class="Datatype">Bin</a>
  <a id="Bin.x1_"></a><a id="3079" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#3079" class="InductiveConstructor Operator">x1_</a> <a id="3083" class="Symbol">:</a> <a id="3085" href="Assignment2.html#3031" class="Datatype">Bin</a> <a id="3089" class="Symbol">→</a> <a id="3091" href="Assignment2.html#3031" class="Datatype">Bin</a>
</pre>{% endraw %}And ask you to define the following functions:

    to : ℕ → Bin
    from : Bin → ℕ

which satisfy the following property:

    from (to n) ≡ n

Using the above, establish that there is an embedding of `ℕ` into `Bin`.
Why is there not an isomorphism?


## Connectives

#### Exercise `⇔≃×` (recommended)

Show that `A ⇔ B` as defined [earlier][plfa.Isomorphism#iff]
is isomorphic to `(A → B) × (B → A)`.

#### Exercise `⊎-comm` (recommended)

Show sum is commutative up to isomorphism.

#### Exercise `⊎-assoc`

Show sum is associative up to ismorphism.

#### Exercise `⊥-identityˡ` (recommended)

Show zero is the left identity of addition.

#### Exercise `⊥-identityʳ`

Show zero is the right identity of addition.

#### Exercise `⊎-weak-×` (recommended)

Show that the following property holds.
{% raw %}<pre class="Agda"><a id="3900" class="Keyword">postulate</a>
  <a id="⊎-weak-×"></a><a id="3912" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#3912" class="Postulate">⊎-weak-×</a> <a id="3921" class="Symbol">:</a> <a id="3923" class="Symbol">∀</a> <a id="3925" class="Symbol">{</a><a id="3926" href="Assignment2.html#3926" class="Bound">A</a> <a id="3928" href="Assignment2.html#3928" class="Bound">B</a> <a id="3930" href="Assignment2.html#3930" class="Bound">C</a> <a id="3932" class="Symbol">:</a> <a id="3934" class="PrimitiveType">Set</a><a id="3937" class="Symbol">}</a> <a id="3939" class="Symbol">→</a> <a id="3941" class="Symbol">(</a><a id="3942" href="Assignment2.html#3926" class="Bound">A</a> <a id="3944" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="3946" href="Assignment2.html#3928" class="Bound">B</a><a id="3947" class="Symbol">)</a> <a id="3949" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="3951" href="Assignment2.html#3930" class="Bound">C</a> <a id="3953" class="Symbol">→</a> <a id="3955" href="Assignment2.html#3926" class="Bound">A</a> <a id="3957" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="3959" class="Symbol">(</a><a id="3960" href="Assignment2.html#3928" class="Bound">B</a> <a id="3962" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="3964" href="Assignment2.html#3930" class="Bound">C</a><a id="3965" class="Symbol">)</a>
</pre>{% endraw %}This is called a _weak distributive law_. Give the corresponding
distributive law, and explain how it relates to the weak version.

#### Exercise `⊎×-implies-×⊎`

Show that a disjunct of conjuncts implies a conjunct of disjuncts.
{% raw %}<pre class="Agda"><a id="4205" class="Keyword">postulate</a>
  <a id="⊎×-implies-×⊎"></a><a id="4217" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#4217" class="Postulate">⊎×-implies-×⊎</a> <a id="4231" class="Symbol">:</a> <a id="4233" class="Symbol">∀</a> <a id="4235" class="Symbol">{</a><a id="4236" href="Assignment2.html#4236" class="Bound">A</a> <a id="4238" href="Assignment2.html#4238" class="Bound">B</a> <a id="4240" href="Assignment2.html#4240" class="Bound">C</a> <a id="4242" href="Assignment2.html#4242" class="Bound">D</a> <a id="4244" class="Symbol">:</a> <a id="4246" class="PrimitiveType">Set</a><a id="4249" class="Symbol">}</a> <a id="4251" class="Symbol">→</a> <a id="4253" class="Symbol">(</a><a id="4254" href="Assignment2.html#4236" class="Bound">A</a> <a id="4256" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="4258" href="Assignment2.html#4238" class="Bound">B</a><a id="4259" class="Symbol">)</a> <a id="4261" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="4263" class="Symbol">(</a><a id="4264" href="Assignment2.html#4240" class="Bound">C</a> <a id="4266" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="4268" href="Assignment2.html#4242" class="Bound">D</a><a id="4269" class="Symbol">)</a> <a id="4271" class="Symbol">→</a> <a id="4273" class="Symbol">(</a><a id="4274" href="Assignment2.html#4236" class="Bound">A</a> <a id="4276" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="4278" href="Assignment2.html#4240" class="Bound">C</a><a id="4279" class="Symbol">)</a> <a id="4281" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="4283" class="Symbol">(</a><a id="4284" href="Assignment2.html#4238" class="Bound">B</a> <a id="4286" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="4288" href="Assignment2.html#4242" class="Bound">D</a><a id="4289" class="Symbol">)</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, give a counterexample.


## Negation

#### Exercise `<-irreflexive` (recommended)

Using negation, show that
[strict inequality][plfa.Relations#strict-inequality]
is irreflexive, that is, `n < n` holds for no `n`.


#### Exercise `trichotomy`

Show that strict inequality satisfies
[trichotomy][plfa.Relations#trichotomy],
that is, for any naturals `m` and `n` exactly one of the following holds:

* `m < n`
* `m ≡ n`
* `m > n`

Here "exactly one" means that one of the three must hold, and each implies the
negation of the other two.


#### Exercise `⊎-dual-×` (recommended)

Show that conjunction, disjunction, and negation are related by a
version of De Morgan's Law.

    ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)

This result is an easy consequence of something we've proved previously.

Do we also have the following?

    ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)

If so, prove; if not, give a variant that does hold.


#### Exercise `Classical` (stretch)

Consider the following principles.

  * Excluded Middle: `A ⊎ ¬ A`, for all `A`
  * Double Negation Elimination: `¬ ¬ A → A`, for all `A`
  * Peirce's Law: `((A → B) → A) → A`, for all `A` and `B`.
  * Implication as disjunction: `(A → B) → ¬ A ⊎ B`, for all `A` and `B`.
  * De Morgan: `¬ (¬ A × ¬ B) → A ⊎ B`, for all `A` and `B`.

Show that each of these implies all the others.


#### Exercise `Stable` (stretch)

Say that a formula is _stable_ if double negation elimination holds for it.
{% raw %}<pre class="Agda"><a id="Stable"></a><a id="5771" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#5771" class="Function">Stable</a> <a id="5778" class="Symbol">:</a> <a id="5780" class="PrimitiveType">Set</a> <a id="5784" class="Symbol">→</a> <a id="5786" class="PrimitiveType">Set</a>
<a id="5790" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#5771" class="Function">Stable</a> <a id="5797" href="Assignment2.html#5797" class="Bound">A</a> <a id="5799" class="Symbol">=</a> <a id="5801" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="5803" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="5805" href="Assignment2.html#5797" class="Bound">A</a> <a id="5807" class="Symbol">→</a> <a id="5809" href="Assignment2.html#5797" class="Bound">A</a>
</pre>{% endraw %}Show that any negated formula is stable, and that the conjunction
of two stable formulas is stable.


## Quantifiers

#### Exercise `∀-distrib-×` (recommended)

Show that universals distribute over conjunction.
{% raw %}<pre class="Agda"><a id="6030" class="Keyword">postulate</a>
  <a id="∀-distrib-×"></a><a id="6042" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#6042" class="Postulate">∀-distrib-×</a> <a id="6054" class="Symbol">:</a> <a id="6056" class="Symbol">∀</a> <a id="6058" class="Symbol">{</a><a id="6059" href="Assignment2.html#6059" class="Bound">A</a> <a id="6061" class="Symbol">:</a> <a id="6063" class="PrimitiveType">Set</a><a id="6066" class="Symbol">}</a> <a id="6068" class="Symbol">{</a><a id="6069" href="Assignment2.html#6069" class="Bound">B</a> <a id="6071" href="Assignment2.html#6071" class="Bound">C</a> <a id="6073" class="Symbol">:</a> <a id="6075" href="Assignment2.html#6059" class="Bound">A</a> <a id="6077" class="Symbol">→</a> <a id="6079" class="PrimitiveType">Set</a><a id="6082" class="Symbol">}</a> <a id="6084" class="Symbol">→</a>
    <a id="6090" class="Symbol">(∀</a> <a id="6093" class="Symbol">(</a><a id="6094" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#6094" class="Bound">x</a> <a id="6096" class="Symbol">:</a> <a id="6098" href="Assignment2.html#6059" class="Bound">A</a><a id="6099" class="Symbol">)</a> <a id="6101" class="Symbol">→</a> <a id="6103" href="Assignment2.html#6069" class="Bound">B</a> <a id="6105" href="Assignment2.html#6094" class="Bound">x</a> <a id="6107" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="6109" href="Assignment2.html#6071" class="Bound">C</a> <a id="6111" href="Assignment2.html#6094" class="Bound">x</a><a id="6112" class="Symbol">)</a> <a id="6114" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5843" class="Record Operator">≃</a> <a id="6116" class="Symbol">(∀</a> <a id="6119" class="Symbol">(</a><a id="6120" href="Assignment2.html#6120" class="Bound">x</a> <a id="6122" class="Symbol">:</a> <a id="6124" href="Assignment2.html#6059" class="Bound">A</a><a id="6125" class="Symbol">)</a> <a id="6127" class="Symbol">→</a> <a id="6129" href="Assignment2.html#6069" class="Bound">B</a> <a id="6131" href="Assignment2.html#6120" class="Bound">x</a><a id="6132" class="Symbol">)</a> <a id="6134" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="6136" class="Symbol">(∀</a> <a id="6139" class="Symbol">(</a><a id="6140" href="Assignment2.html#6140" class="Bound">x</a> <a id="6142" class="Symbol">:</a> <a id="6144" href="Assignment2.html#6059" class="Bound">A</a><a id="6145" class="Symbol">)</a> <a id="6147" class="Symbol">→</a> <a id="6149" href="Assignment2.html#6071" class="Bound">C</a> <a id="6151" href="Assignment2.html#6140" class="Bound">x</a><a id="6152" class="Symbol">)</a>
</pre>{% endraw %}Compare this with the result (`→-distrib-×`) in
Chapter [Connectives][plfa.Connectives].

#### Exercise `⊎∀-implies-∀⊎`

Show that a disjunction of universals implies a universal of disjunctions.
{% raw %}<pre class="Agda"><a id="6358" class="Keyword">postulate</a>
  <a id="⊎∀-implies-∀⊎"></a><a id="6370" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#6370" class="Postulate">⊎∀-implies-∀⊎</a> <a id="6384" class="Symbol">:</a> <a id="6386" class="Symbol">∀</a> <a id="6388" class="Symbol">{</a><a id="6389" href="Assignment2.html#6389" class="Bound">A</a> <a id="6391" class="Symbol">:</a> <a id="6393" class="PrimitiveType">Set</a><a id="6396" class="Symbol">}</a> <a id="6398" class="Symbol">{</a> <a id="6400" href="Assignment2.html#6400" class="Bound">B</a> <a id="6402" href="Assignment2.html#6402" class="Bound">C</a> <a id="6404" class="Symbol">:</a> <a id="6406" href="Assignment2.html#6389" class="Bound">A</a> <a id="6408" class="Symbol">→</a> <a id="6410" class="PrimitiveType">Set</a> <a id="6414" class="Symbol">}</a> <a id="6416" class="Symbol">→</a>
    <a id="6422" class="Symbol">(∀</a> <a id="6425" class="Symbol">(</a><a id="6426" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#6426" class="Bound">x</a> <a id="6428" class="Symbol">:</a> <a id="6430" href="Assignment2.html#6389" class="Bound">A</a><a id="6431" class="Symbol">)</a> <a id="6433" class="Symbol">→</a> <a id="6435" href="Assignment2.html#6400" class="Bound">B</a> <a id="6437" href="Assignment2.html#6426" class="Bound">x</a><a id="6438" class="Symbol">)</a> <a id="6440" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="6442" class="Symbol">(∀</a> <a id="6445" class="Symbol">(</a><a id="6446" href="Assignment2.html#6446" class="Bound">x</a> <a id="6448" class="Symbol">:</a> <a id="6450" href="Assignment2.html#6389" class="Bound">A</a><a id="6451" class="Symbol">)</a> <a id="6453" class="Symbol">→</a> <a id="6455" href="Assignment2.html#6402" class="Bound">C</a> <a id="6457" href="Assignment2.html#6446" class="Bound">x</a><a id="6458" class="Symbol">)</a>  <a id="6461" class="Symbol">→</a>  <a id="6464" class="Symbol">∀</a> <a id="6466" class="Symbol">(</a><a id="6467" href="Assignment2.html#6467" class="Bound">x</a> <a id="6469" class="Symbol">:</a> <a id="6471" href="Assignment2.html#6389" class="Bound">A</a><a id="6472" class="Symbol">)</a> <a id="6474" class="Symbol">→</a> <a id="6476" href="Assignment2.html#6400" class="Bound">B</a> <a id="6478" href="Assignment2.html#6467" class="Bound">x</a> <a id="6480" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="6482" href="Assignment2.html#6402" class="Bound">C</a> <a id="6484" href="Assignment2.html#6467" class="Bound">x</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.

#### Exercise `∃-distrib-⊎` (recommended)

Show that existentials distribute over disjunction.
{% raw %}<pre class="Agda"><a id="6649" class="Keyword">postulate</a>
  <a id="∃-distrib-⊎"></a><a id="6661" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#6661" class="Postulate">∃-distrib-⊎</a> <a id="6673" class="Symbol">:</a> <a id="6675" class="Symbol">∀</a> <a id="6677" class="Symbol">{</a><a id="6678" href="Assignment2.html#6678" class="Bound">A</a> <a id="6680" class="Symbol">:</a> <a id="6682" class="PrimitiveType">Set</a><a id="6685" class="Symbol">}</a> <a id="6687" class="Symbol">{</a><a id="6688" href="Assignment2.html#6688" class="Bound">B</a> <a id="6690" href="Assignment2.html#6690" class="Bound">C</a> <a id="6692" class="Symbol">:</a> <a id="6694" href="Assignment2.html#6678" class="Bound">A</a> <a id="6696" class="Symbol">→</a> <a id="6698" class="PrimitiveType">Set</a><a id="6701" class="Symbol">}</a> <a id="6703" class="Symbol">→</a>
    <a id="6709" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="6712" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#6712" class="Bound">x</a> <a id="6714" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="6716" class="Symbol">(</a><a id="6717" href="Assignment2.html#6688" class="Bound">B</a> <a id="6719" href="Assignment2.html#6712" class="Bound">x</a> <a id="6721" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="6723" href="Assignment2.html#6690" class="Bound">C</a> <a id="6725" href="Assignment2.html#6712" class="Bound">x</a><a id="6726" class="Symbol">)</a> <a id="6728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5843" class="Record Operator">≃</a> <a id="6730" class="Symbol">(</a><a id="6731" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="6734" href="Assignment2.html#6734" class="Bound">x</a> <a id="6736" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="6738" href="Assignment2.html#6688" class="Bound">B</a> <a id="6740" href="Assignment2.html#6734" class="Bound">x</a><a id="6741" class="Symbol">)</a> <a id="6743" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="6745" class="Symbol">(</a><a id="6746" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="6749" href="Assignment2.html#6749" class="Bound">x</a> <a id="6751" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="6753" href="Assignment2.html#6690" class="Bound">C</a> <a id="6755" href="Assignment2.html#6749" class="Bound">x</a><a id="6756" class="Symbol">)</a>
</pre>{% endraw %}
#### Exercise `∃×-implies-×∃`

Show that an existential of conjunctions implies a conjunction of existentials.
{% raw %}<pre class="Agda"><a id="6878" class="Keyword">postulate</a>
  <a id="∃×-implies-×∃"></a><a id="6890" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#6890" class="Postulate">∃×-implies-×∃</a> <a id="6904" class="Symbol">:</a> <a id="6906" class="Symbol">∀</a> <a id="6908" class="Symbol">{</a><a id="6909" href="Assignment2.html#6909" class="Bound">A</a> <a id="6911" class="Symbol">:</a> <a id="6913" class="PrimitiveType">Set</a><a id="6916" class="Symbol">}</a> <a id="6918" class="Symbol">{</a> <a id="6920" href="Assignment2.html#6920" class="Bound">B</a> <a id="6922" href="Assignment2.html#6922" class="Bound">C</a> <a id="6924" class="Symbol">:</a> <a id="6926" href="Assignment2.html#6909" class="Bound">A</a> <a id="6928" class="Symbol">→</a> <a id="6930" class="PrimitiveType">Set</a> <a id="6934" class="Symbol">}</a> <a id="6936" class="Symbol">→</a>
    <a id="6942" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="6945" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#6945" class="Bound">x</a> <a id="6947" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="6949" class="Symbol">(</a><a id="6950" href="Assignment2.html#6920" class="Bound">B</a> <a id="6952" href="Assignment2.html#6945" class="Bound">x</a> <a id="6954" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="6956" href="Assignment2.html#6922" class="Bound">C</a> <a id="6958" href="Assignment2.html#6945" class="Bound">x</a><a id="6959" class="Symbol">)</a> <a id="6961" class="Symbol">→</a> <a id="6963" class="Symbol">(</a><a id="6964" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="6967" href="Assignment2.html#6967" class="Bound">x</a> <a id="6969" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="6971" href="Assignment2.html#6920" class="Bound">B</a> <a id="6973" href="Assignment2.html#6967" class="Bound">x</a><a id="6974" class="Symbol">)</a> <a id="6976" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="6978" class="Symbol">(</a><a id="6979" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="6982" href="Assignment2.html#6982" class="Bound">x</a> <a id="6984" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="6986" href="Assignment2.html#6922" class="Bound">C</a> <a id="6988" href="Assignment2.html#6982" class="Bound">x</a><a id="6989" class="Symbol">)</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.

#### Exercise `∃-even-odd`

How do the proofs become more difficult if we replace `m * 2` and `1 + m * 2`
by `2 * m` and `2 * m + 1`?  Rewrite the proofs of `∃-even` and `∃-odd` when
restated in this way.

#### Exercise `∃-+-≤`

Show that `y ≤ z` holds if and only if there exists a `x` such that
`x + y ≡ z`.

#### Exercise `∃¬-implies-¬∀` (recommended)

Show that existential of a negation implies negation of a universal.
{% raw %}<pre class="Agda"><a id="7484" class="Keyword">postulate</a>
  <a id="∃¬-implies-¬∀"></a><a id="7496" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#7496" class="Postulate">∃¬-implies-¬∀</a> <a id="7510" class="Symbol">:</a> <a id="7512" class="Symbol">∀</a> <a id="7514" class="Symbol">{</a><a id="7515" href="Assignment2.html#7515" class="Bound">A</a> <a id="7517" class="Symbol">:</a> <a id="7519" class="PrimitiveType">Set</a><a id="7522" class="Symbol">}</a> <a id="7524" class="Symbol">{</a><a id="7525" href="Assignment2.html#7525" class="Bound">B</a> <a id="7527" class="Symbol">:</a> <a id="7529" href="Assignment2.html#7515" class="Bound">A</a> <a id="7531" class="Symbol">→</a> <a id="7533" class="PrimitiveType">Set</a><a id="7536" class="Symbol">}</a>
    <a id="7542" class="Symbol">→</a> <a id="7544" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="7547" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#7547" class="Bound">x</a> <a id="7549" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="7551" class="Symbol">(</a><a id="7552" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="7554" href="Assignment2.html#7525" class="Bound">B</a> <a id="7556" href="Assignment2.html#7547" class="Bound">x</a><a id="7557" class="Symbol">)</a>
      <a id="7565" class="Comment">--------------</a>
    <a id="7584" class="Symbol">→</a> <a id="7586" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="7588" class="Symbol">(∀</a> <a id="7591" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#7591" class="Bound">x</a> <a id="7593" class="Symbol">→</a> <a id="7595" href="Assignment2.html#7525" class="Bound">B</a> <a id="7597" href="Assignment2.html#7591" class="Bound">x</a><a id="7598" class="Symbol">)</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.


#### Exercise `Bin-isomorphism` (stretch) {#Bin-isomorphism}

Recall that Exercises
[Bin][plfa.Naturals#Bin],
[Bin-laws][plfa.Induction#Bin-laws], and
[Bin-predicates][plfa.Relations#Bin-predicates]
define a datatype of bitstrings representing natural numbers.

    data Bin : Set where
      nil : Bin
      x0_ : Bin → Bin
      x1_ : Bin → Bin

And ask you to define the following functions and predicates.

    to   : ℕ → Bin
    from : Bin → ℕ
    Can  : Bin → Set

And to establish the following properties.

    from (to n) ≡ n

    ----------
    Can (to n)

    Can x
    ---------------
    to (from x) ≡ x

Using the above, establish that there is an isomorphism between `ℕ` and
`∃[ x ](Can x)`.


## Decidable

#### Exercise `_<?_` (recommended)

Analogous to the function above, define a function to decide strict inequality.
{% raw %}<pre class="Agda"><a id="8508" class="Keyword">postulate</a>
  <a id="_&lt;?_"></a><a id="8520" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#8520" class="Postulate Operator">_&lt;?_</a> <a id="8525" class="Symbol">:</a> <a id="8527" class="Symbol">∀</a> <a id="8529" class="Symbol">(</a><a id="8530" href="Assignment2.html#8530" class="Bound">m</a> <a id="8532" href="Assignment2.html#8532" class="Bound">n</a> <a id="8534" class="Symbol">:</a> <a id="8536" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="8537" class="Symbol">)</a> <a id="8539" class="Symbol">→</a> <a id="8541" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8545" class="Symbol">(</a><a id="8546" href="Assignment2.html#8530" class="Bound">m</a> <a id="8548" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26522" class="Datatype Operator">&lt;</a> <a id="8550" href="Assignment2.html#8532" class="Bound">n</a><a id="8551" class="Symbol">)</a>
</pre>{% endraw %}
#### Exercise `_≡ℕ?_`

Define a function to decide whether two naturals are equal.
{% raw %}<pre class="Agda"><a id="8645" class="Keyword">postulate</a>
  <a id="_≡ℕ?_"></a><a id="8657" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#8657" class="Postulate Operator">_≡ℕ?_</a> <a id="8663" class="Symbol">:</a> <a id="8665" class="Symbol">∀</a> <a id="8667" class="Symbol">(</a><a id="8668" href="Assignment2.html#8668" class="Bound">m</a> <a id="8670" href="Assignment2.html#8670" class="Bound">n</a> <a id="8672" class="Symbol">:</a> <a id="8674" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="8675" class="Symbol">)</a> <a id="8677" class="Symbol">→</a> <a id="8679" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8683" class="Symbol">(</a><a id="8684" href="Assignment2.html#8668" class="Bound">m</a> <a id="8686" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="8688" href="Assignment2.html#8670" class="Bound">n</a><a id="8689" class="Symbol">)</a>
</pre>{% endraw %}

#### Exercise `erasure`

Show that erasure relates corresponding boolean and decidable operations.
{% raw %}<pre class="Agda"><a id="8800" class="Keyword">postulate</a>
  <a id="∧-×"></a><a id="8812" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#8812" class="Postulate">∧-×</a> <a id="8816" class="Symbol">:</a> <a id="8818" class="Symbol">∀</a> <a id="8820" class="Symbol">{</a><a id="8821" href="Assignment2.html#8821" class="Bound">A</a> <a id="8823" href="Assignment2.html#8823" class="Bound">B</a> <a id="8825" class="Symbol">:</a> <a id="8827" class="PrimitiveType">Set</a><a id="8830" class="Symbol">}</a> <a id="8832" class="Symbol">(</a><a id="8833" href="Assignment2.html#8833" class="Bound">x</a> <a id="8835" class="Symbol">:</a> <a id="8837" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8841" href="Assignment2.html#8821" class="Bound">A</a><a id="8842" class="Symbol">)</a> <a id="8844" class="Symbol">(</a><a id="8845" href="Assignment2.html#8845" class="Bound">y</a> <a id="8847" class="Symbol">:</a> <a id="8849" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8853" href="Assignment2.html#8823" class="Bound">B</a><a id="8854" class="Symbol">)</a> <a id="8856" class="Symbol">→</a> <a id="8858" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="8860" href="Assignment2.html#8833" class="Bound">x</a> <a id="8862" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="8864" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1015" class="Function Operator">∧</a> <a id="8866" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="8868" href="Assignment2.html#8845" class="Bound">y</a> <a id="8870" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="8872" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="8874" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="8876" href="Assignment2.html#8833" class="Bound">x</a> <a id="8878" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Product.html#585" class="Function Operator">×-dec</a> <a id="8884" href="Assignment2.html#8845" class="Bound">y</a> <a id="8886" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a>
  <a id="∨-×"></a><a id="8890" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#8890" class="Postulate">∨-×</a> <a id="8894" class="Symbol">:</a> <a id="8896" class="Symbol">∀</a> <a id="8898" class="Symbol">{</a><a id="8899" href="Assignment2.html#8899" class="Bound">A</a> <a id="8901" href="Assignment2.html#8901" class="Bound">B</a> <a id="8903" class="Symbol">:</a> <a id="8905" class="PrimitiveType">Set</a><a id="8908" class="Symbol">}</a> <a id="8910" class="Symbol">(</a><a id="8911" href="Assignment2.html#8911" class="Bound">x</a> <a id="8913" class="Symbol">:</a> <a id="8915" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8919" href="Assignment2.html#8899" class="Bound">A</a><a id="8920" class="Symbol">)</a> <a id="8922" class="Symbol">(</a><a id="8923" href="Assignment2.html#8923" class="Bound">y</a> <a id="8925" class="Symbol">:</a> <a id="8927" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8931" href="Assignment2.html#8901" class="Bound">B</a><a id="8932" class="Symbol">)</a> <a id="8934" class="Symbol">→</a> <a id="8936" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="8938" href="Assignment2.html#8911" class="Bound">x</a> <a id="8940" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="8942" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1073" class="Function Operator">∨</a> <a id="8944" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="8946" href="Assignment2.html#8923" class="Bound">y</a> <a id="8948" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="8950" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="8952" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="8954" href="Assignment2.html#8911" class="Bound">x</a> <a id="8956" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Sum.html#668" class="Function Operator">⊎-dec</a> <a id="8962" href="Assignment2.html#8923" class="Bound">y</a> <a id="8964" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a>
  <a id="not-¬"></a><a id="8968" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#8968" class="Postulate">not-¬</a> <a id="8974" class="Symbol">:</a> <a id="8976" class="Symbol">∀</a> <a id="8978" class="Symbol">{</a><a id="8979" href="Assignment2.html#8979" class="Bound">A</a> <a id="8981" class="Symbol">:</a> <a id="8983" class="PrimitiveType">Set</a><a id="8986" class="Symbol">}</a> <a id="8988" class="Symbol">(</a><a id="8989" href="Assignment2.html#8989" class="Bound">x</a> <a id="8991" class="Symbol">:</a> <a id="8993" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8997" href="Assignment2.html#8979" class="Bound">A</a><a id="8998" class="Symbol">)</a> <a id="9000" class="Symbol">→</a> <a id="9002" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#961" class="Function">not</a> <a id="9006" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="9008" href="Assignment2.html#8989" class="Bound">x</a> <a id="9010" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="9012" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="9014" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="9016" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#1115" class="Function">¬?</a> <a id="9019" href="Assignment2.html#8989" class="Bound">x</a> <a id="9021" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a>
</pre>{% endraw %}
#### Exercise `iff-erasure` (recommended)

Give analogues of the `_⇔_` operation from
Chapter [Isomorphism][plfa.Isomorphism#iff],
operation on booleans and decidables, and also show the corresponding erasure.
{% raw %}<pre class="Agda"><a id="9242" class="Keyword">postulate</a>
  <a id="_iff_"></a><a id="9254" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#9254" class="Postulate Operator">_iff_</a> <a id="9260" class="Symbol">:</a> <a id="9262" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a> <a id="9267" class="Symbol">→</a> <a id="9269" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a> <a id="9274" class="Symbol">→</a> <a id="9276" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a>
  <a id="_⇔-dec_"></a><a id="9283" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#9283" class="Postulate Operator">_⇔-dec_</a> <a id="9291" class="Symbol">:</a> <a id="9293" class="Symbol">∀</a> <a id="9295" class="Symbol">{</a><a id="9296" href="Assignment2.html#9296" class="Bound">A</a> <a id="9298" href="Assignment2.html#9298" class="Bound">B</a> <a id="9300" class="Symbol">:</a> <a id="9302" class="PrimitiveType">Set</a><a id="9305" class="Symbol">}</a> <a id="9307" class="Symbol">→</a> <a id="9309" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9313" href="Assignment2.html#9296" class="Bound">A</a> <a id="9315" class="Symbol">→</a> <a id="9317" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9321" href="Assignment2.html#9298" class="Bound">B</a> <a id="9323" class="Symbol">→</a> <a id="9325" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9329" class="Symbol">(</a><a id="9330" href="Assignment2.html#9296" class="Bound">A</a> <a id="9332" href="Assignment2.html#2667" class="Record Operator">⇔</a> <a id="9334" href="Assignment2.html#9298" class="Bound">B</a><a id="9335" class="Symbol">)</a>
  <a id="iff-⇔"></a><a id="9339" href="{% endraw %}{{ site.baseurl }}{% link out/tspl/2018/Assignment2.md %}{% raw %}#9339" class="Postulate">iff-⇔</a> <a id="9345" class="Symbol">:</a> <a id="9347" class="Symbol">∀</a> <a id="9349" class="Symbol">{</a><a id="9350" href="Assignment2.html#9350" class="Bound">A</a> <a id="9352" href="Assignment2.html#9352" class="Bound">B</a> <a id="9354" class="Symbol">:</a> <a id="9356" class="PrimitiveType">Set</a><a id="9359" class="Symbol">}</a> <a id="9361" class="Symbol">(</a><a id="9362" href="Assignment2.html#9362" class="Bound">x</a> <a id="9364" class="Symbol">:</a> <a id="9366" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9370" href="Assignment2.html#9350" class="Bound">A</a><a id="9371" class="Symbol">)</a> <a id="9373" class="Symbol">(</a><a id="9374" href="Assignment2.html#9374" class="Bound">y</a> <a id="9376" class="Symbol">:</a> <a id="9378" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9382" href="Assignment2.html#9352" class="Bound">B</a><a id="9383" class="Symbol">)</a> <a id="9385" class="Symbol">→</a> <a id="9387" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="9389" href="Assignment2.html#9362" class="Bound">x</a> <a id="9391" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="9393" href="Assignment2.html#9254" class="Postulate Operator">iff</a> <a id="9397" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="9399" href="Assignment2.html#9374" class="Bound">y</a> <a id="9401" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="9403" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="9405" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="9407" href="Assignment2.html#9362" class="Bound">x</a> <a id="9409" href="Assignment2.html#9283" class="Postulate Operator">⇔-dec</a> <a id="9415" href="Assignment2.html#9374" class="Bound">y</a> <a id="9417" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a>
</pre>{% endraw %}
