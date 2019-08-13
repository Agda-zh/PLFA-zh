---
src       : "src/plfa/Bisimulation.lagda.md"
title     : "Bisimulation: Relating reduction systems"
layout    : page
prev      : /More/
permalink : /Bisimulation/
next      : /Inference/
---

{% raw %}<pre class="Agda"><a id="156" class="Keyword">module</a> <a id="163" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}" class="Module">plfa.Bisimulation</a> <a id="181" class="Keyword">where</a>
</pre>{% endraw %}
Some constructs can be defined in terms of other constructs.  In the
previous chapter, we saw how _let_ terms can be rewritten as an
application of an abstraction, and how two alternative formulations of
products — one with projections and one with case — can be formulated
in terms of each other.  In this chapter, we look at how to formalise
such claims.

Given two different systems, with different terms and reduction rules,
we define what it means to claim that one _simulates_ the other.
Let's call our two systems _source_ and _target_.  Let `M`, `N` range
over terms of the source, and `M†`, `N†` range over terms of the
target.  We define a relation

    M ~ M†

between corresponding terms of the two systems. We have a
_simulation_ of the source by the target if every reduction
in the source has a corresponding reduction sequence
in the target:

_Simulation_: For every `M`, `M†`, and `N`:
If `M ~ M†` and `M —→ N`
then `M† —↠ N†` and `N ~ N†`
for some `N†`.

Or, in a diagram:

    M  --- —→ --- N
    |             |
    |             |
    ~             ~
    |             |
    |             |
    M† --- —↠ --- N†

Sometimes we will have a stronger condition, where each reduction in the source
corresponds to a reduction (rather than a reduction sequence)
in the target:

    M  --- —→ --- N
    |             |
    |             |
    ~             ~
    |             |
    |             |
    M† --- —→ --- N†

This stronger condition is known as _lock-step_ or _on the nose_ simulation.

We are particularly interested in the situation where there is also
a simulation from the target to the source: every reduction in the
target has a corresponding reduction sequence in the source.  This
situation is called a _bisimulation_.

Simulation is established by case analysis over all possible
reductions and all possible terms to which they are related.  For each
reduction step in the source we must show a corresponding reduction
sequence in the target.

For instance, the source might be lambda calculus with _let_
added, and the target the same system with `let` translated out.
The key rule defining our relation will be:

    M ~ M†
    N ~ N†
    --------------------------------
    let x = M in N ~ (ƛ x ⇒ N†) · M†

All the other rules are congruences: variables relate to
themselves, and abstractions and applications relate if their
components relate:

    -----
    x ~ x

    N ~ N†
    ------------------
    ƛ x ⇒ N ~ ƛ x ⇒ N†

    L ~ L†
    M ~ M†
    ---------------
    L · M ~ L† · M†

Covering the other constructs of our language — naturals,
fixpoints, products, and so on — would add little save length.

In this case, our relation can be specified by a function
from source to target:

    (x) †               =  x
    (ƛ x ⇒ N) †         =  ƛ x ⇒ (N †)
    (L · M) †           =  (L †) · (M †)
    (let x = M in N) †  =  (ƛ x ⇒ (N †)) · (M †)

And we have

    M † ≡ N
    -------
    M ~ N

and conversely. But in general we may have a relation without any
corresponding function.

This chapter formalises establishing that `~` as defined
above is a simulation from source to target.  We leave
establishing it in the reverse direction as an exercise.
Another exercise is to show the alternative formulations
of products in
Chapter [More]({{ site.baseurl }}/More/)
are in bisimulation.


## Imports

We import our source language from
Chapter [More]({{ site.baseurl }}/More/):
{% raw %}<pre class="Agda"><a id="3619" class="Keyword">open</a> <a id="3624" class="Keyword">import</a> <a id="3631" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}" class="Module">plfa.More</a>
</pre>{% endraw %}

## Simulation

The simulation is a straightforward formalisation of the rules
in the introduction:
{% raw %}<pre class="Agda"><a id="3750" class="Keyword">infix</a>  <a id="3757" class="Number">4</a> <a id="3759" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3796" class="Datatype Operator">_~_</a>
<a id="3763" class="Keyword">infix</a>  <a id="3770" class="Number">5</a> <a id="3772" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3903" class="InductiveConstructor Operator">~ƛ_</a>
<a id="3776" class="Keyword">infix</a>  <a id="3783" class="Number">7</a> <a id="3785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3988" class="InductiveConstructor Operator">_~·_</a>

<a id="3791" class="Keyword">data</a> <a id="_~_"></a><a id="3796" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3796" class="Datatype Operator">_~_</a> <a id="3800" class="Symbol">:</a> <a id="3802" class="Symbol">∀</a> <a id="3804" class="Symbol">{</a><a id="3805" href="plfa.Bisimulation.html#3805" class="Bound">Γ</a> <a id="3807" href="plfa.Bisimulation.html#3807" class="Bound">A</a><a id="3808" class="Symbol">}</a> <a id="3810" class="Symbol">→</a> <a id="3812" class="Symbol">(</a><a id="3813" href="plfa.Bisimulation.html#3805" class="Bound">Γ</a> <a id="3815" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14946" class="Datatype Operator">⊢</a> <a id="3817" href="plfa.Bisimulation.html#3807" class="Bound">A</a><a id="3818" class="Symbol">)</a> <a id="3820" class="Symbol">→</a> <a id="3822" class="Symbol">(</a><a id="3823" href="plfa.Bisimulation.html#3805" class="Bound">Γ</a> <a id="3825" href="plfa.More.html#14946" class="Datatype Operator">⊢</a> <a id="3827" href="plfa.Bisimulation.html#3807" class="Bound">A</a><a id="3828" class="Symbol">)</a> <a id="3830" class="Symbol">→</a> <a id="3832" class="PrimitiveType">Set</a> <a id="3836" class="Keyword">where</a>

  <a id="_~_.~`"></a><a id="3845" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3845" class="InductiveConstructor">~`</a> <a id="3848" class="Symbol">:</a> <a id="3850" class="Symbol">∀</a> <a id="3852" class="Symbol">{</a><a id="3853" href="plfa.Bisimulation.html#3853" class="Bound">Γ</a> <a id="3855" href="plfa.Bisimulation.html#3855" class="Bound">A</a><a id="3856" class="Symbol">}</a> <a id="3858" class="Symbol">{</a><a id="3859" href="plfa.Bisimulation.html#3859" class="Bound">x</a> <a id="3861" class="Symbol">:</a> <a id="3863" href="plfa.Bisimulation.html#3853" class="Bound">Γ</a> <a id="3865" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14755" class="Datatype Operator">∋</a> <a id="3867" href="plfa.Bisimulation.html#3855" class="Bound">A</a><a id="3868" class="Symbol">}</a>
     <a id="3875" class="Comment">---------</a>
   <a id="3888" class="Symbol">→</a> <a id="3890" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14998" class="InductiveConstructor Operator">`</a> <a id="3892" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3859" class="Bound">x</a> <a id="3894" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="3896" href="plfa.More.html#14998" class="InductiveConstructor Operator">`</a> <a id="3898" href="plfa.Bisimulation.html#3859" class="Bound">x</a>

  <a id="_~_.~ƛ_"></a><a id="3903" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3903" class="InductiveConstructor Operator">~ƛ_</a> <a id="3907" class="Symbol">:</a> <a id="3909" class="Symbol">∀</a> <a id="3911" class="Symbol">{</a><a id="3912" href="plfa.Bisimulation.html#3912" class="Bound">Γ</a> <a id="3914" href="plfa.Bisimulation.html#3914" class="Bound">A</a> <a id="3916" href="plfa.Bisimulation.html#3916" class="Bound">B</a><a id="3917" class="Symbol">}</a> <a id="3919" class="Symbol">{</a><a id="3920" href="plfa.Bisimulation.html#3920" class="Bound">N</a> <a id="3922" href="plfa.Bisimulation.html#3922" class="Bound">N†</a> <a id="3925" class="Symbol">:</a> <a id="3927" href="plfa.Bisimulation.html#3912" class="Bound">Γ</a> <a id="3929" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14671" class="InductiveConstructor Operator">,</a> <a id="3931" href="plfa.Bisimulation.html#3914" class="Bound">A</a> <a id="3933" href="plfa.More.html#14946" class="Datatype Operator">⊢</a> <a id="3935" href="plfa.Bisimulation.html#3916" class="Bound">B</a><a id="3936" class="Symbol">}</a>
    <a id="3942" class="Symbol">→</a> <a id="3944" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3920" class="Bound">N</a> <a id="3946" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="3948" href="plfa.Bisimulation.html#3922" class="Bound">N†</a>
      <a id="3957" class="Comment">----------</a>
    <a id="3972" class="Symbol">→</a> <a id="3974" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#15066" class="InductiveConstructor Operator">ƛ</a> <a id="3976" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3920" class="Bound">N</a> <a id="3978" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="3980" href="plfa.More.html#15066" class="InductiveConstructor Operator">ƛ</a> <a id="3982" href="plfa.Bisimulation.html#3922" class="Bound">N†</a>

  <a id="_~_._~·_"></a><a id="3988" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3988" class="InductiveConstructor Operator">_~·_</a> <a id="3993" class="Symbol">:</a> <a id="3995" class="Symbol">∀</a> <a id="3997" class="Symbol">{</a><a id="3998" href="plfa.Bisimulation.html#3998" class="Bound">Γ</a> <a id="4000" href="plfa.Bisimulation.html#4000" class="Bound">A</a> <a id="4002" href="plfa.Bisimulation.html#4002" class="Bound">B</a><a id="4003" class="Symbol">}</a> <a id="4005" class="Symbol">{</a><a id="4006" href="plfa.Bisimulation.html#4006" class="Bound">L</a> <a id="4008" href="plfa.Bisimulation.html#4008" class="Bound">L†</a> <a id="4011" class="Symbol">:</a> <a id="4013" href="plfa.Bisimulation.html#3998" class="Bound">Γ</a> <a id="4015" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14946" class="Datatype Operator">⊢</a> <a id="4017" href="plfa.Bisimulation.html#4000" class="Bound">A</a> <a id="4019" href="plfa.More.html#14534" class="InductiveConstructor Operator">⇒</a> <a id="4021" href="plfa.Bisimulation.html#4002" class="Bound">B</a><a id="4022" class="Symbol">}</a> <a id="4024" class="Symbol">{</a><a id="4025" href="plfa.Bisimulation.html#4025" class="Bound">M</a> <a id="4027" href="plfa.Bisimulation.html#4027" class="Bound">M†</a> <a id="4030" class="Symbol">:</a> <a id="4032" href="plfa.Bisimulation.html#3998" class="Bound">Γ</a> <a id="4034" href="plfa.More.html#14946" class="Datatype Operator">⊢</a> <a id="4036" href="plfa.Bisimulation.html#4000" class="Bound">A</a><a id="4037" class="Symbol">}</a>
    <a id="4043" class="Symbol">→</a> <a id="4045" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4006" class="Bound">L</a> <a id="4047" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="4049" href="plfa.Bisimulation.html#4008" class="Bound">L†</a>
    <a id="4056" class="Symbol">→</a> <a id="4058" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4025" class="Bound">M</a> <a id="4060" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="4062" href="plfa.Bisimulation.html#4027" class="Bound">M†</a>
      <a id="4071" class="Comment">---------------</a>
    <a id="4091" class="Symbol">→</a> <a id="4093" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4006" class="Bound">L</a> <a id="4095" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#15134" class="InductiveConstructor Operator">·</a> <a id="4097" href="plfa.Bisimulation.html#4025" class="Bound">M</a> <a id="4099" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="4101" href="plfa.Bisimulation.html#4008" class="Bound">L†</a> <a id="4104" href="plfa.More.html#15134" class="InductiveConstructor Operator">·</a> <a id="4106" href="plfa.Bisimulation.html#4027" class="Bound">M†</a>

  <a id="_~_.~let"></a><a id="4112" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4112" class="InductiveConstructor">~let</a> <a id="4117" class="Symbol">:</a> <a id="4119" class="Symbol">∀</a> <a id="4121" class="Symbol">{</a><a id="4122" href="plfa.Bisimulation.html#4122" class="Bound">Γ</a> <a id="4124" href="plfa.Bisimulation.html#4124" class="Bound">A</a> <a id="4126" href="plfa.Bisimulation.html#4126" class="Bound">B</a><a id="4127" class="Symbol">}</a> <a id="4129" class="Symbol">{</a><a id="4130" href="plfa.Bisimulation.html#4130" class="Bound">M</a> <a id="4132" href="plfa.Bisimulation.html#4132" class="Bound">M†</a> <a id="4135" class="Symbol">:</a> <a id="4137" href="plfa.Bisimulation.html#4122" class="Bound">Γ</a> <a id="4139" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14946" class="Datatype Operator">⊢</a> <a id="4141" href="plfa.Bisimulation.html#4124" class="Bound">A</a><a id="4142" class="Symbol">}</a> <a id="4144" class="Symbol">{</a><a id="4145" href="plfa.Bisimulation.html#4145" class="Bound">N</a> <a id="4147" href="plfa.Bisimulation.html#4147" class="Bound">N†</a> <a id="4150" class="Symbol">:</a> <a id="4152" href="plfa.Bisimulation.html#4122" class="Bound">Γ</a> <a id="4154" href="plfa.More.html#14671" class="InductiveConstructor Operator">,</a> <a id="4156" href="plfa.Bisimulation.html#4124" class="Bound">A</a> <a id="4158" href="plfa.More.html#14946" class="Datatype Operator">⊢</a> <a id="4160" href="plfa.Bisimulation.html#4126" class="Bound">B</a><a id="4161" class="Symbol">}</a>
    <a id="4167" class="Symbol">→</a> <a id="4169" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4130" class="Bound">M</a> <a id="4171" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="4173" href="plfa.Bisimulation.html#4132" class="Bound">M†</a>
    <a id="4180" class="Symbol">→</a> <a id="4182" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4145" class="Bound">N</a> <a id="4184" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="4186" href="plfa.Bisimulation.html#4147" class="Bound">N†</a>
      <a id="4195" class="Comment">----------------------</a>
    <a id="4222" class="Symbol">→</a> <a id="4224" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#15640" class="InductiveConstructor">`let</a> <a id="4229" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4130" class="Bound">M</a> <a id="4231" href="plfa.Bisimulation.html#4145" class="Bound">N</a> <a id="4233" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="4235" class="Symbol">(</a><a id="4236" href="plfa.More.html#15066" class="InductiveConstructor Operator">ƛ</a> <a id="4238" href="plfa.Bisimulation.html#4147" class="Bound">N†</a><a id="4240" class="Symbol">)</a> <a id="4242" href="plfa.More.html#15134" class="InductiveConstructor Operator">·</a> <a id="4244" href="plfa.Bisimulation.html#4132" class="Bound">M†</a>
</pre>{% endraw %}The language in Chapter [More]({{ site.baseurl }}/More/) has more constructs, which we could easily add.
However, leaving the simulation small let's us focus on the essence.
It's a handy technical trick that we can have a large source language,
but only bother to include in the simulation the terms of interest.

#### Exercise `_†`

Formalise the translation from source to target given in the introduction.
Show that `M † ≡ N` implies `M ~ N`, and conversely.

{% raw %}<pre class="Agda"><a id="4718" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Simulation commutes with values

We need a number of technical results. The first is that simulation
commutes with values.  That is, if `M ~ M†` and `M` is a value then
`M†` is also a value:
{% raw %}<pre class="Agda"><a id="~val"></a><a id="4945" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4945" class="Function">~val</a> <a id="4950" class="Symbol">:</a> <a id="4952" class="Symbol">∀</a> <a id="4954" class="Symbol">{</a><a id="4955" href="plfa.Bisimulation.html#4955" class="Bound">Γ</a> <a id="4957" href="plfa.Bisimulation.html#4957" class="Bound">A</a><a id="4958" class="Symbol">}</a> <a id="4960" class="Symbol">{</a><a id="4961" href="plfa.Bisimulation.html#4961" class="Bound">M</a> <a id="4963" href="plfa.Bisimulation.html#4963" class="Bound">M†</a> <a id="4966" class="Symbol">:</a> <a id="4968" href="plfa.Bisimulation.html#4955" class="Bound">Γ</a> <a id="4970" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14946" class="Datatype Operator">⊢</a> <a id="4972" href="plfa.Bisimulation.html#4957" class="Bound">A</a><a id="4973" class="Symbol">}</a>
  <a id="4977" class="Symbol">→</a> <a id="4979" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4961" class="Bound">M</a> <a id="4981" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="4983" href="plfa.Bisimulation.html#4963" class="Bound">M†</a>
  <a id="4988" class="Symbol">→</a> <a id="4990" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#18888" class="Datatype">Value</a> <a id="4996" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4961" class="Bound">M</a>
    <a id="5002" class="Comment">--------</a>
  <a id="5013" class="Symbol">→</a> <a id="5015" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#18888" class="Datatype">Value</a> <a id="5021" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4963" class="Bound">M†</a>
<a id="5024" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4945" class="Function">~val</a> <a id="5029" href="plfa.Bisimulation.html#3845" class="InductiveConstructor">~`</a>           <a id="5042" class="Symbol">()</a>
<a id="5045" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4945" class="Function">~val</a> <a id="5050" class="Symbol">(</a><a id="5051" href="plfa.Bisimulation.html#3903" class="InductiveConstructor Operator">~ƛ</a> <a id="5054" href="plfa.Bisimulation.html#5054" class="Bound">~N</a><a id="5056" class="Symbol">)</a>      <a id="5063" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#18943" class="InductiveConstructor">V-ƛ</a>  <a id="5068" class="Symbol">=</a>  <a id="5071" href="plfa.More.html#18943" class="InductiveConstructor">V-ƛ</a>
<a id="5075" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4945" class="Function">~val</a> <a id="5080" class="Symbol">(</a><a id="5081" href="plfa.Bisimulation.html#5081" class="Bound">~L</a> <a id="5084" href="plfa.Bisimulation.html#3988" class="InductiveConstructor Operator">~·</a> <a id="5087" href="plfa.Bisimulation.html#5087" class="Bound">~M</a><a id="5089" class="Symbol">)</a>   <a id="5093" class="Symbol">()</a>
<a id="5096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4945" class="Function">~val</a> <a id="5101" class="Symbol">(</a><a id="5102" href="plfa.Bisimulation.html#4112" class="InductiveConstructor">~let</a> <a id="5107" href="plfa.Bisimulation.html#5107" class="Bound">~M</a> <a id="5110" href="plfa.Bisimulation.html#5110" class="Bound">~N</a><a id="5112" class="Symbol">)</a> <a id="5114" class="Symbol">()</a>
</pre>{% endraw %}It is a straightforward case analysis, where here the only value
of interest is a lambda abstraction.

#### Exercise `~val⁻¹`

Show that this also holds in the reverse direction: if `M ~ M†`
and `Value M†` then `Value M`.

{% raw %}<pre class="Agda"><a id="5348" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Simulation commutes with renaming

The next technical result is that simulation commutes with renaming.
That is, if `ρ` maps any judgment `Γ ∋ A` to a judgment `Δ ∋ A`,
and if `M ~ M†` then `rename ρ M ~ rename ρ M†`:

{% raw %}<pre class="Agda"><a id="~rename"></a><a id="5603" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#5603" class="Function">~rename</a> <a id="5611" class="Symbol">:</a> <a id="5613" class="Symbol">∀</a> <a id="5615" class="Symbol">{</a><a id="5616" href="plfa.Bisimulation.html#5616" class="Bound">Γ</a> <a id="5618" href="plfa.Bisimulation.html#5618" class="Bound">Δ</a><a id="5619" class="Symbol">}</a>
  <a id="5623" class="Symbol">→</a> <a id="5625" class="Symbol">(</a><a id="5626" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#5626" class="Bound">ρ</a> <a id="5628" class="Symbol">:</a> <a id="5630" class="Symbol">∀</a> <a id="5632" class="Symbol">{</a><a id="5633" href="plfa.Bisimulation.html#5633" class="Bound">A</a><a id="5634" class="Symbol">}</a> <a id="5636" class="Symbol">→</a> <a id="5638" href="plfa.Bisimulation.html#5616" class="Bound">Γ</a> <a id="5640" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14755" class="Datatype Operator">∋</a> <a id="5642" href="plfa.Bisimulation.html#5633" class="Bound">A</a> <a id="5644" class="Symbol">→</a> <a id="5646" href="plfa.Bisimulation.html#5618" class="Bound">Δ</a> <a id="5648" href="plfa.More.html#14755" class="Datatype Operator">∋</a> <a id="5650" href="plfa.Bisimulation.html#5633" class="Bound">A</a><a id="5651" class="Symbol">)</a>
    <a id="5657" class="Comment">----------------------------------------------------------</a>
  <a id="5718" class="Symbol">→</a> <a id="5720" class="Symbol">(∀</a> <a id="5723" class="Symbol">{</a><a id="5724" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#5724" class="Bound">A</a><a id="5725" class="Symbol">}</a> <a id="5727" class="Symbol">{</a><a id="5728" href="plfa.Bisimulation.html#5728" class="Bound">M</a> <a id="5730" href="plfa.Bisimulation.html#5730" class="Bound">M†</a> <a id="5733" class="Symbol">:</a> <a id="5735" href="plfa.Bisimulation.html#5616" class="Bound">Γ</a> <a id="5737" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14946" class="Datatype Operator">⊢</a> <a id="5739" href="plfa.Bisimulation.html#5724" class="Bound">A</a><a id="5740" class="Symbol">}</a> <a id="5742" class="Symbol">→</a> <a id="5744" href="plfa.Bisimulation.html#5728" class="Bound">M</a> <a id="5746" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="5748" href="plfa.Bisimulation.html#5730" class="Bound">M†</a> <a id="5751" class="Symbol">→</a> <a id="5753" href="plfa.More.html#16685" class="Function">rename</a> <a id="5760" href="plfa.Bisimulation.html#5626" class="Bound">ρ</a> <a id="5762" href="plfa.Bisimulation.html#5728" class="Bound">M</a> <a id="5764" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="5766" href="plfa.More.html#16685" class="Function">rename</a> <a id="5773" href="plfa.Bisimulation.html#5626" class="Bound">ρ</a> <a id="5775" href="plfa.Bisimulation.html#5730" class="Bound">M†</a><a id="5777" class="Symbol">)</a>
<a id="5779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#5603" class="Function">~rename</a> <a id="5787" href="plfa.Bisimulation.html#5787" class="Bound">ρ</a> <a id="5789" class="Symbol">(</a><a id="5790" href="plfa.Bisimulation.html#3845" class="InductiveConstructor">~`</a><a id="5792" class="Symbol">)</a>          <a id="5803" class="Symbol">=</a>  <a id="5806" href="plfa.Bisimulation.html#3845" class="InductiveConstructor">~`</a>
<a id="5809" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#5603" class="Function">~rename</a> <a id="5817" href="plfa.Bisimulation.html#5817" class="Bound">ρ</a> <a id="5819" class="Symbol">(</a><a id="5820" href="plfa.Bisimulation.html#3903" class="InductiveConstructor Operator">~ƛ</a> <a id="5823" href="plfa.Bisimulation.html#5823" class="Bound">~N</a><a id="5825" class="Symbol">)</a>       <a id="5833" class="Symbol">=</a>  <a id="5836" href="plfa.Bisimulation.html#3903" class="InductiveConstructor Operator">~ƛ</a> <a id="5839" class="Symbol">(</a><a id="5840" href="plfa.Bisimulation.html#5603" class="Function">~rename</a> <a id="5848" class="Symbol">(</a><a id="5849" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#16566" class="Function">ext</a> <a id="5853" href="plfa.Bisimulation.html#5817" class="Bound">ρ</a><a id="5854" class="Symbol">)</a> <a id="5856" href="plfa.Bisimulation.html#5823" class="Bound">~N</a><a id="5858" class="Symbol">)</a>
<a id="5860" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#5603" class="Function">~rename</a> <a id="5868" href="plfa.Bisimulation.html#5868" class="Bound">ρ</a> <a id="5870" class="Symbol">(</a><a id="5871" href="plfa.Bisimulation.html#5871" class="Bound">~L</a> <a id="5874" href="plfa.Bisimulation.html#3988" class="InductiveConstructor Operator">~·</a> <a id="5877" href="plfa.Bisimulation.html#5877" class="Bound">~M</a><a id="5879" class="Symbol">)</a>    <a id="5884" class="Symbol">=</a>  <a id="5887" class="Symbol">(</a><a id="5888" href="plfa.Bisimulation.html#5603" class="Function">~rename</a> <a id="5896" href="plfa.Bisimulation.html#5868" class="Bound">ρ</a> <a id="5898" href="plfa.Bisimulation.html#5871" class="Bound">~L</a><a id="5900" class="Symbol">)</a> <a id="5902" href="plfa.Bisimulation.html#3988" class="InductiveConstructor Operator">~·</a> <a id="5905" class="Symbol">(</a><a id="5906" href="plfa.Bisimulation.html#5603" class="Function">~rename</a> <a id="5914" href="plfa.Bisimulation.html#5868" class="Bound">ρ</a> <a id="5916" href="plfa.Bisimulation.html#5877" class="Bound">~M</a><a id="5918" class="Symbol">)</a>
<a id="5920" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#5603" class="Function">~rename</a> <a id="5928" href="plfa.Bisimulation.html#5928" class="Bound">ρ</a> <a id="5930" class="Symbol">(</a><a id="5931" href="plfa.Bisimulation.html#4112" class="InductiveConstructor">~let</a> <a id="5936" href="plfa.Bisimulation.html#5936" class="Bound">~M</a> <a id="5939" href="plfa.Bisimulation.html#5939" class="Bound">~N</a><a id="5941" class="Symbol">)</a>  <a id="5944" class="Symbol">=</a>  <a id="5947" href="plfa.Bisimulation.html#4112" class="InductiveConstructor">~let</a> <a id="5952" class="Symbol">(</a><a id="5953" href="plfa.Bisimulation.html#5603" class="Function">~rename</a> <a id="5961" href="plfa.Bisimulation.html#5928" class="Bound">ρ</a> <a id="5963" href="plfa.Bisimulation.html#5936" class="Bound">~M</a><a id="5965" class="Symbol">)</a> <a id="5967" class="Symbol">(</a><a id="5968" href="plfa.Bisimulation.html#5603" class="Function">~rename</a> <a id="5976" class="Symbol">(</a><a id="5977" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#16566" class="Function">ext</a> <a id="5981" href="plfa.Bisimulation.html#5928" class="Bound">ρ</a><a id="5982" class="Symbol">)</a> <a id="5984" href="plfa.Bisimulation.html#5939" class="Bound">~N</a><a id="5986" class="Symbol">)</a>
</pre>{% endraw %}The structure of the proof is similar to the structure of renaming itself:
reconstruct each term with recursive invocation, extending the environment
where appropriate (in this case, only for the body of an abstraction).


## Simulation commutes with substitution

The third technical result is that simulation commutes with substitution.
It is more complex than substitution, because where we had one renaming map
`ρ` here we need two substitution maps, `σ` and `σ†`.

The proof first requires we establish an analogue of extension.
If `σ` and `σ†` both map any judgment `Γ ∋ A` to a judgment `Δ ⊢ A`,
such that for every `x` in `Γ ∋ A` we have `σ x ~ σ† x`,
then for any `x` in `Γ , B ∋ A` we have `exts σ x ~ exts σ† x`:
{% raw %}<pre class="Agda"><a id="~exts"></a><a id="6720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#6720" class="Function">~exts</a> <a id="6726" class="Symbol">:</a> <a id="6728" class="Symbol">∀</a> <a id="6730" class="Symbol">{</a><a id="6731" href="plfa.Bisimulation.html#6731" class="Bound">Γ</a> <a id="6733" href="plfa.Bisimulation.html#6733" class="Bound">Δ</a><a id="6734" class="Symbol">}</a>
  <a id="6738" class="Symbol">→</a> <a id="6740" class="Symbol">{</a><a id="6741" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#6741" class="Bound">σ</a>  <a id="6744" class="Symbol">:</a> <a id="6746" class="Symbol">∀</a> <a id="6748" class="Symbol">{</a><a id="6749" href="plfa.Bisimulation.html#6749" class="Bound">A</a><a id="6750" class="Symbol">}</a> <a id="6752" class="Symbol">→</a> <a id="6754" href="plfa.Bisimulation.html#6731" class="Bound">Γ</a> <a id="6756" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14755" class="Datatype Operator">∋</a> <a id="6758" href="plfa.Bisimulation.html#6749" class="Bound">A</a> <a id="6760" class="Symbol">→</a> <a id="6762" href="plfa.Bisimulation.html#6733" class="Bound">Δ</a> <a id="6764" href="plfa.More.html#14946" class="Datatype Operator">⊢</a> <a id="6766" href="plfa.Bisimulation.html#6749" class="Bound">A</a><a id="6767" class="Symbol">}</a>
  <a id="6771" class="Symbol">→</a> <a id="6773" class="Symbol">{</a><a id="6774" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#6774" class="Bound">σ†</a> <a id="6777" class="Symbol">:</a> <a id="6779" class="Symbol">∀</a> <a id="6781" class="Symbol">{</a><a id="6782" href="plfa.Bisimulation.html#6782" class="Bound">A</a><a id="6783" class="Symbol">}</a> <a id="6785" class="Symbol">→</a> <a id="6787" href="plfa.Bisimulation.html#6731" class="Bound">Γ</a> <a id="6789" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14755" class="Datatype Operator">∋</a> <a id="6791" href="plfa.Bisimulation.html#6782" class="Bound">A</a> <a id="6793" class="Symbol">→</a> <a id="6795" href="plfa.Bisimulation.html#6733" class="Bound">Δ</a> <a id="6797" href="plfa.More.html#14946" class="Datatype Operator">⊢</a> <a id="6799" href="plfa.Bisimulation.html#6782" class="Bound">A</a><a id="6800" class="Symbol">}</a>
  <a id="6804" class="Symbol">→</a> <a id="6806" class="Symbol">(∀</a> <a id="6809" class="Symbol">{</a><a id="6810" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#6810" class="Bound">A</a><a id="6811" class="Symbol">}</a> <a id="6813" class="Symbol">→</a> <a id="6815" class="Symbol">(</a><a id="6816" href="plfa.Bisimulation.html#6816" class="Bound">x</a> <a id="6818" class="Symbol">:</a> <a id="6820" href="plfa.Bisimulation.html#6731" class="Bound">Γ</a> <a id="6822" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14755" class="Datatype Operator">∋</a> <a id="6824" href="plfa.Bisimulation.html#6810" class="Bound">A</a><a id="6825" class="Symbol">)</a> <a id="6827" class="Symbol">→</a> <a id="6829" href="plfa.Bisimulation.html#6741" class="Bound">σ</a> <a id="6831" href="plfa.Bisimulation.html#6816" class="Bound">x</a> <a id="6833" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="6835" href="plfa.Bisimulation.html#6774" class="Bound">σ†</a> <a id="6838" href="plfa.Bisimulation.html#6816" class="Bound">x</a><a id="6839" class="Symbol">)</a>
    <a id="6845" class="Comment">--------------------------------------------------</a>
  <a id="6898" class="Symbol">→</a> <a id="6900" class="Symbol">(∀</a> <a id="6903" class="Symbol">{</a><a id="6904" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#6904" class="Bound">A</a> <a id="6906" href="plfa.Bisimulation.html#6906" class="Bound">B</a><a id="6907" class="Symbol">}</a> <a id="6909" class="Symbol">→</a> <a id="6911" class="Symbol">(</a><a id="6912" href="plfa.Bisimulation.html#6912" class="Bound">x</a> <a id="6914" class="Symbol">:</a> <a id="6916" href="plfa.Bisimulation.html#6731" class="Bound">Γ</a> <a id="6918" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14671" class="InductiveConstructor Operator">,</a> <a id="6920" href="plfa.Bisimulation.html#6906" class="Bound">B</a> <a id="6922" href="plfa.More.html#14755" class="Datatype Operator">∋</a> <a id="6924" href="plfa.Bisimulation.html#6904" class="Bound">A</a><a id="6925" class="Symbol">)</a> <a id="6927" class="Symbol">→</a> <a id="6929" href="plfa.More.html#17504" class="Function">exts</a> <a id="6934" href="plfa.Bisimulation.html#6741" class="Bound">σ</a> <a id="6936" href="plfa.Bisimulation.html#6912" class="Bound">x</a> <a id="6938" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="6940" href="plfa.More.html#17504" class="Function">exts</a> <a id="6945" href="plfa.Bisimulation.html#6774" class="Bound">σ†</a> <a id="6948" href="plfa.Bisimulation.html#6912" class="Bound">x</a><a id="6949" class="Symbol">)</a>
<a id="6951" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#6720" class="Function">~exts</a> <a id="6957" href="plfa.Bisimulation.html#6957" class="Bound">~σ</a> <a id="6960" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14791" class="InductiveConstructor">Z</a>      <a id="6967" class="Symbol">=</a>  <a id="6970" href="plfa.Bisimulation.html#3845" class="InductiveConstructor">~`</a>
<a id="6973" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#6720" class="Function">~exts</a> <a id="6979" href="plfa.Bisimulation.html#6979" class="Bound">~σ</a> <a id="6982" class="Symbol">(</a><a id="6983" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14838" class="InductiveConstructor Operator">S</a> <a id="6985" href="plfa.Bisimulation.html#6985" class="Bound">x</a><a id="6986" class="Symbol">)</a>  <a id="6989" class="Symbol">=</a>  <a id="6992" href="plfa.Bisimulation.html#5603" class="Function">~rename</a> <a id="7000" href="plfa.More.html#14838" class="InductiveConstructor Operator">S_</a> <a id="7003" class="Symbol">(</a><a id="7004" href="plfa.Bisimulation.html#6979" class="Bound">~σ</a> <a id="7007" href="plfa.Bisimulation.html#6985" class="Bound">x</a><a id="7008" class="Symbol">)</a>
</pre>{% endraw %}The structure of the proof is similar to the structure of extension itself.
The newly introduced variable trivially relates to itself, and otherwise
we apply renaming to the hypothesis.

With extension under our belts, it is straightforward to show
substitution commutes.  If `σ` and `σ†` both map any judgment `Γ ∋ A`
to a judgment `Δ ⊢ A`, such that for every `x` in `Γ ∋ A` we have `σ
x ~ σ† x`, and if `M ~ M†`, then `subst σ M ~ subst σ† M†`:
{% raw %}<pre class="Agda"><a id="~subst"></a><a id="7466" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#7466" class="Function">~subst</a> <a id="7473" class="Symbol">:</a> <a id="7475" class="Symbol">∀</a> <a id="7477" class="Symbol">{</a><a id="7478" href="plfa.Bisimulation.html#7478" class="Bound">Γ</a> <a id="7480" href="plfa.Bisimulation.html#7480" class="Bound">Δ</a><a id="7481" class="Symbol">}</a>
  <a id="7485" class="Symbol">→</a> <a id="7487" class="Symbol">{</a><a id="7488" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#7488" class="Bound">σ</a>  <a id="7491" class="Symbol">:</a> <a id="7493" class="Symbol">∀</a> <a id="7495" class="Symbol">{</a><a id="7496" href="plfa.Bisimulation.html#7496" class="Bound">A</a><a id="7497" class="Symbol">}</a> <a id="7499" class="Symbol">→</a> <a id="7501" href="plfa.Bisimulation.html#7478" class="Bound">Γ</a> <a id="7503" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14755" class="Datatype Operator">∋</a> <a id="7505" href="plfa.Bisimulation.html#7496" class="Bound">A</a> <a id="7507" class="Symbol">→</a> <a id="7509" href="plfa.Bisimulation.html#7480" class="Bound">Δ</a> <a id="7511" href="plfa.More.html#14946" class="Datatype Operator">⊢</a> <a id="7513" href="plfa.Bisimulation.html#7496" class="Bound">A</a><a id="7514" class="Symbol">}</a>
  <a id="7518" class="Symbol">→</a> <a id="7520" class="Symbol">{</a><a id="7521" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#7521" class="Bound">σ†</a> <a id="7524" class="Symbol">:</a> <a id="7526" class="Symbol">∀</a> <a id="7528" class="Symbol">{</a><a id="7529" href="plfa.Bisimulation.html#7529" class="Bound">A</a><a id="7530" class="Symbol">}</a> <a id="7532" class="Symbol">→</a> <a id="7534" href="plfa.Bisimulation.html#7478" class="Bound">Γ</a> <a id="7536" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14755" class="Datatype Operator">∋</a> <a id="7538" href="plfa.Bisimulation.html#7529" class="Bound">A</a> <a id="7540" class="Symbol">→</a> <a id="7542" href="plfa.Bisimulation.html#7480" class="Bound">Δ</a> <a id="7544" href="plfa.More.html#14946" class="Datatype Operator">⊢</a> <a id="7546" href="plfa.Bisimulation.html#7529" class="Bound">A</a><a id="7547" class="Symbol">}</a>
  <a id="7551" class="Symbol">→</a> <a id="7553" class="Symbol">(∀</a> <a id="7556" class="Symbol">{</a><a id="7557" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#7557" class="Bound">A</a><a id="7558" class="Symbol">}</a> <a id="7560" class="Symbol">→</a> <a id="7562" class="Symbol">(</a><a id="7563" href="plfa.Bisimulation.html#7563" class="Bound">x</a> <a id="7565" class="Symbol">:</a> <a id="7567" href="plfa.Bisimulation.html#7478" class="Bound">Γ</a> <a id="7569" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14755" class="Datatype Operator">∋</a> <a id="7571" href="plfa.Bisimulation.html#7557" class="Bound">A</a><a id="7572" class="Symbol">)</a> <a id="7574" class="Symbol">→</a> <a id="7576" href="plfa.Bisimulation.html#7488" class="Bound">σ</a> <a id="7578" href="plfa.Bisimulation.html#7563" class="Bound">x</a> <a id="7580" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="7582" href="plfa.Bisimulation.html#7521" class="Bound">σ†</a> <a id="7585" href="plfa.Bisimulation.html#7563" class="Bound">x</a><a id="7586" class="Symbol">)</a>
    <a id="7592" class="Comment">---------------------------------------------------------</a>
  <a id="7652" class="Symbol">→</a> <a id="7654" class="Symbol">(∀</a> <a id="7657" class="Symbol">{</a><a id="7658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#7658" class="Bound">A</a><a id="7659" class="Symbol">}</a> <a id="7661" class="Symbol">{</a><a id="7662" href="plfa.Bisimulation.html#7662" class="Bound">M</a> <a id="7664" href="plfa.Bisimulation.html#7664" class="Bound">M†</a> <a id="7667" class="Symbol">:</a> <a id="7669" href="plfa.Bisimulation.html#7478" class="Bound">Γ</a> <a id="7671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14946" class="Datatype Operator">⊢</a> <a id="7673" href="plfa.Bisimulation.html#7658" class="Bound">A</a><a id="7674" class="Symbol">}</a> <a id="7676" class="Symbol">→</a> <a id="7678" href="plfa.Bisimulation.html#7662" class="Bound">M</a> <a id="7680" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="7682" href="plfa.Bisimulation.html#7664" class="Bound">M†</a> <a id="7685" class="Symbol">→</a> <a id="7687" href="plfa.More.html#17636" class="Function">subst</a> <a id="7693" href="plfa.Bisimulation.html#7488" class="Bound">σ</a> <a id="7695" href="plfa.Bisimulation.html#7662" class="Bound">M</a> <a id="7697" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="7699" href="plfa.More.html#17636" class="Function">subst</a> <a id="7705" href="plfa.Bisimulation.html#7521" class="Bound">σ†</a> <a id="7708" href="plfa.Bisimulation.html#7664" class="Bound">M†</a><a id="7710" class="Symbol">)</a>
<a id="7712" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#7466" class="Function">~subst</a> <a id="7719" href="plfa.Bisimulation.html#7719" class="Bound">~σ</a> <a id="7722" class="Symbol">(</a><a id="7723" href="plfa.Bisimulation.html#3845" class="InductiveConstructor">~`</a> <a id="7726" class="Symbol">{</a><a id="7727" class="Argument">x</a> <a id="7729" class="Symbol">=</a> <a id="7731" href="plfa.Bisimulation.html#7731" class="Bound">x</a><a id="7732" class="Symbol">})</a>  <a id="7736" class="Symbol">=</a>  <a id="7739" href="plfa.Bisimulation.html#7719" class="Bound">~σ</a> <a id="7742" href="plfa.Bisimulation.html#7731" class="Bound">x</a>
<a id="7744" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#7466" class="Function">~subst</a> <a id="7751" href="plfa.Bisimulation.html#7751" class="Bound">~σ</a> <a id="7754" class="Symbol">(</a><a id="7755" href="plfa.Bisimulation.html#3903" class="InductiveConstructor Operator">~ƛ</a> <a id="7758" href="plfa.Bisimulation.html#7758" class="Bound">~N</a><a id="7760" class="Symbol">)</a>       <a id="7768" class="Symbol">=</a>  <a id="7771" href="plfa.Bisimulation.html#3903" class="InductiveConstructor Operator">~ƛ</a> <a id="7774" class="Symbol">(</a><a id="7775" href="plfa.Bisimulation.html#7466" class="Function">~subst</a> <a id="7782" class="Symbol">(</a><a id="7783" href="plfa.Bisimulation.html#6720" class="Function">~exts</a> <a id="7789" href="plfa.Bisimulation.html#7751" class="Bound">~σ</a><a id="7791" class="Symbol">)</a> <a id="7793" href="plfa.Bisimulation.html#7758" class="Bound">~N</a><a id="7795" class="Symbol">)</a>
<a id="7797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#7466" class="Function">~subst</a> <a id="7804" href="plfa.Bisimulation.html#7804" class="Bound">~σ</a> <a id="7807" class="Symbol">(</a><a id="7808" href="plfa.Bisimulation.html#7808" class="Bound">~L</a> <a id="7811" href="plfa.Bisimulation.html#3988" class="InductiveConstructor Operator">~·</a> <a id="7814" href="plfa.Bisimulation.html#7814" class="Bound">~M</a><a id="7816" class="Symbol">)</a>    <a id="7821" class="Symbol">=</a>  <a id="7824" class="Symbol">(</a><a id="7825" href="plfa.Bisimulation.html#7466" class="Function">~subst</a> <a id="7832" href="plfa.Bisimulation.html#7804" class="Bound">~σ</a> <a id="7835" href="plfa.Bisimulation.html#7808" class="Bound">~L</a><a id="7837" class="Symbol">)</a> <a id="7839" href="plfa.Bisimulation.html#3988" class="InductiveConstructor Operator">~·</a> <a id="7842" class="Symbol">(</a><a id="7843" href="plfa.Bisimulation.html#7466" class="Function">~subst</a> <a id="7850" href="plfa.Bisimulation.html#7804" class="Bound">~σ</a> <a id="7853" href="plfa.Bisimulation.html#7814" class="Bound">~M</a><a id="7855" class="Symbol">)</a>
<a id="7857" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#7466" class="Function">~subst</a> <a id="7864" href="plfa.Bisimulation.html#7864" class="Bound">~σ</a> <a id="7867" class="Symbol">(</a><a id="7868" href="plfa.Bisimulation.html#4112" class="InductiveConstructor">~let</a> <a id="7873" href="plfa.Bisimulation.html#7873" class="Bound">~M</a> <a id="7876" href="plfa.Bisimulation.html#7876" class="Bound">~N</a><a id="7878" class="Symbol">)</a>  <a id="7881" class="Symbol">=</a>  <a id="7884" href="plfa.Bisimulation.html#4112" class="InductiveConstructor">~let</a> <a id="7889" class="Symbol">(</a><a id="7890" href="plfa.Bisimulation.html#7466" class="Function">~subst</a> <a id="7897" href="plfa.Bisimulation.html#7864" class="Bound">~σ</a> <a id="7900" href="plfa.Bisimulation.html#7873" class="Bound">~M</a><a id="7902" class="Symbol">)</a> <a id="7904" class="Symbol">(</a><a id="7905" href="plfa.Bisimulation.html#7466" class="Function">~subst</a> <a id="7912" class="Symbol">(</a><a id="7913" href="plfa.Bisimulation.html#6720" class="Function">~exts</a> <a id="7919" href="plfa.Bisimulation.html#7864" class="Bound">~σ</a><a id="7921" class="Symbol">)</a> <a id="7923" href="plfa.Bisimulation.html#7876" class="Bound">~N</a><a id="7925" class="Symbol">)</a>
</pre>{% endraw %}Again, the structure of the proof is similar to the structure of
substitution itself: reconstruct each term with recursive invocation,
extending the environment where appropriate (in this case, only for
the body of an abstraction).

From the general case of substitution, it is also easy to derive
the required special case.  If `N ~ N†` and `M ~ M†`, then
`N [ M ] ~ N† [ M† ]`:
{% raw %}<pre class="Agda"><a id="~sub"></a><a id="8315" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#8315" class="Function">~sub</a> <a id="8320" class="Symbol">:</a> <a id="8322" class="Symbol">∀</a> <a id="8324" class="Symbol">{</a><a id="8325" href="plfa.Bisimulation.html#8325" class="Bound">Γ</a> <a id="8327" href="plfa.Bisimulation.html#8327" class="Bound">A</a> <a id="8329" href="plfa.Bisimulation.html#8329" class="Bound">B</a><a id="8330" class="Symbol">}</a> <a id="8332" class="Symbol">{</a><a id="8333" href="plfa.Bisimulation.html#8333" class="Bound">N</a> <a id="8335" href="plfa.Bisimulation.html#8335" class="Bound">N†</a> <a id="8338" class="Symbol">:</a> <a id="8340" href="plfa.Bisimulation.html#8325" class="Bound">Γ</a> <a id="8342" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14671" class="InductiveConstructor Operator">,</a> <a id="8344" href="plfa.Bisimulation.html#8329" class="Bound">B</a> <a id="8346" href="plfa.More.html#14946" class="Datatype Operator">⊢</a> <a id="8348" href="plfa.Bisimulation.html#8327" class="Bound">A</a><a id="8349" class="Symbol">}</a> <a id="8351" class="Symbol">{</a><a id="8352" href="plfa.Bisimulation.html#8352" class="Bound">M</a> <a id="8354" href="plfa.Bisimulation.html#8354" class="Bound">M†</a> <a id="8357" class="Symbol">:</a> <a id="8359" href="plfa.Bisimulation.html#8325" class="Bound">Γ</a> <a id="8361" href="plfa.More.html#14946" class="Datatype Operator">⊢</a> <a id="8363" href="plfa.Bisimulation.html#8329" class="Bound">B</a><a id="8364" class="Symbol">}</a>
  <a id="8368" class="Symbol">→</a> <a id="8370" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#8333" class="Bound">N</a> <a id="8372" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="8374" href="plfa.Bisimulation.html#8335" class="Bound">N†</a>
  <a id="8379" class="Symbol">→</a> <a id="8381" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#8352" class="Bound">M</a> <a id="8383" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="8385" href="plfa.Bisimulation.html#8354" class="Bound">M†</a>
    <a id="8392" class="Comment">-----------------------</a>
  <a id="8418" class="Symbol">→</a> <a id="8420" class="Symbol">(</a><a id="8421" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#8333" class="Bound">N</a> <a id="8423" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#18429" class="Function Operator">[</a> <a id="8425" href="plfa.Bisimulation.html#8352" class="Bound">M</a> <a id="8427" href="plfa.More.html#18429" class="Function Operator">]</a><a id="8428" class="Symbol">)</a> <a id="8430" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="8432" class="Symbol">(</a><a id="8433" href="plfa.Bisimulation.html#8335" class="Bound">N†</a> <a id="8436" href="plfa.More.html#18429" class="Function Operator">[</a> <a id="8438" href="plfa.Bisimulation.html#8354" class="Bound">M†</a> <a id="8441" href="plfa.More.html#18429" class="Function Operator">]</a><a id="8442" class="Symbol">)</a>
<a id="8444" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#8315" class="Function">~sub</a> <a id="8449" class="Symbol">{</a><a id="8450" href="plfa.Bisimulation.html#8450" class="Bound">Γ</a><a id="8451" class="Symbol">}</a> <a id="8453" class="Symbol">{</a><a id="8454" href="plfa.Bisimulation.html#8454" class="Bound">A</a><a id="8455" class="Symbol">}</a> <a id="8457" class="Symbol">{</a><a id="8458" href="plfa.Bisimulation.html#8458" class="Bound">B</a><a id="8459" class="Symbol">}</a> <a id="8461" href="plfa.Bisimulation.html#8461" class="Bound">~N</a> <a id="8464" href="plfa.Bisimulation.html#8464" class="Bound">~M</a> <a id="8467" class="Symbol">=</a> <a id="8469" href="plfa.Bisimulation.html#7466" class="Function">~subst</a> <a id="8476" class="Symbol">{</a><a id="8477" href="plfa.Bisimulation.html#8450" class="Bound">Γ</a> <a id="8479" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14671" class="InductiveConstructor Operator">,</a> <a id="8481" href="plfa.Bisimulation.html#8458" class="Bound">B</a><a id="8482" class="Symbol">}</a> <a id="8484" class="Symbol">{</a><a id="8485" href="plfa.Bisimulation.html#8450" class="Bound">Γ</a><a id="8486" class="Symbol">}</a> <a id="8488" href="plfa.Bisimulation.html#8508" class="Function">~σ</a> <a id="8491" class="Symbol">{</a><a id="8492" href="plfa.Bisimulation.html#8454" class="Bound">A</a><a id="8493" class="Symbol">}</a> <a id="8495" href="plfa.Bisimulation.html#8461" class="Bound">~N</a>
  <a id="8500" class="Keyword">where</a>
  <a id="8508" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#8508" class="Function">~σ</a> <a id="8511" class="Symbol">:</a> <a id="8513" class="Symbol">∀</a> <a id="8515" class="Symbol">{</a><a id="8516" href="plfa.Bisimulation.html#8516" class="Bound">A</a><a id="8517" class="Symbol">}</a> <a id="8519" class="Symbol">→</a> <a id="8521" class="Symbol">(</a><a id="8522" href="plfa.Bisimulation.html#8522" class="Bound">x</a> <a id="8524" class="Symbol">:</a> <a id="8526" href="plfa.Bisimulation.html#8450" class="Bound">Γ</a> <a id="8528" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14671" class="InductiveConstructor Operator">,</a> <a id="8530" href="plfa.Bisimulation.html#8458" class="Bound">B</a> <a id="8532" href="plfa.More.html#14755" class="Datatype Operator">∋</a> <a id="8534" href="plfa.Bisimulation.html#8516" class="Bound">A</a><a id="8535" class="Symbol">)</a> <a id="8537" class="Symbol">→</a> <a id="8539" class="Symbol">_</a> <a id="8541" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="8543" class="Symbol">_</a>
  <a id="8547" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#8508" class="Function">~σ</a> <a id="8550" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14791" class="InductiveConstructor">Z</a>      <a id="8557" class="Symbol">=</a>  <a id="8560" href="plfa.Bisimulation.html#8464" class="Bound">~M</a>
  <a id="8565" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#8508" class="Function">~σ</a> <a id="8568" class="Symbol">(</a><a id="8569" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14838" class="InductiveConstructor Operator">S</a> <a id="8571" href="plfa.Bisimulation.html#8571" class="Bound">x</a><a id="8572" class="Symbol">)</a>  <a id="8575" class="Symbol">=</a>  <a id="8578" href="plfa.Bisimulation.html#3845" class="InductiveConstructor">~`</a>
</pre>{% endraw %}Once more, the structure of the proof resembles the original.


## The relation is a simulation

Finally, we can show that the relation actually is a simulation.
In fact, we will show the stronger condition of a lock-step simulation.
What we wish to show is:

_Lock-step simulation_: For every `M`, `M†`, and `N`:
If `M ~ M†` and `M —→ N`
then `M† —→ N†` and `N ~ N†`
for some `N†`.

Or, in a diagram:

    M  --- —→ --- N
    |             |
    |             |
    ~             ~
    |             |
    |             |
    M† --- —→ --- N†

We first formulate a concept corresponding to the lower leg
of the diagram, that is, its right and bottom edges:
{% raw %}<pre class="Agda"><a id="9247" class="Keyword">data</a> <a id="Leg"></a><a id="9252" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9252" class="Datatype">Leg</a> <a id="9256" class="Symbol">{</a><a id="9257" href="plfa.Bisimulation.html#9257" class="Bound">Γ</a> <a id="9259" href="plfa.Bisimulation.html#9259" class="Bound">A</a><a id="9260" class="Symbol">}</a> <a id="9262" class="Symbol">(</a><a id="9263" href="plfa.Bisimulation.html#9263" class="Bound">M†</a> <a id="9266" href="plfa.Bisimulation.html#9266" class="Bound">N</a> <a id="9268" class="Symbol">:</a> <a id="9270" href="plfa.Bisimulation.html#9257" class="Bound">Γ</a> <a id="9272" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14946" class="Datatype Operator">⊢</a> <a id="9274" href="plfa.Bisimulation.html#9259" class="Bound">A</a><a id="9275" class="Symbol">)</a> <a id="9277" class="Symbol">:</a> <a id="9279" class="PrimitiveType">Set</a> <a id="9283" class="Keyword">where</a>

  <a id="Leg.leg"></a><a id="9292" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9292" class="InductiveConstructor">leg</a> <a id="9296" class="Symbol">:</a> <a id="9298" class="Symbol">∀</a> <a id="9300" class="Symbol">{</a><a id="9301" href="plfa.Bisimulation.html#9301" class="Bound">N†</a> <a id="9304" class="Symbol">:</a> <a id="9306" href="plfa.Bisimulation.html#9257" class="Bound">Γ</a> <a id="9308" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14946" class="Datatype Operator">⊢</a> <a id="9310" href="plfa.Bisimulation.html#9259" class="Bound">A</a><a id="9311" class="Symbol">}</a>
    <a id="9317" class="Symbol">→</a> <a id="9319" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9266" class="Bound">N</a> <a id="9321" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="9323" href="plfa.Bisimulation.html#9301" class="Bound">N†</a>
    <a id="9330" class="Symbol">→</a> <a id="9332" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9263" class="Bound">M†</a> <a id="9335" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#19555" class="Datatype Operator">—→</a> <a id="9338" href="plfa.Bisimulation.html#9301" class="Bound">N†</a>
      <a id="9347" class="Comment">--------</a>
    <a id="9360" class="Symbol">→</a> <a id="9362" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9252" class="Datatype">Leg</a> <a id="9366" href="plfa.Bisimulation.html#9263" class="Bound">M†</a> <a id="9369" href="plfa.Bisimulation.html#9266" class="Bound">N</a>
</pre>{% endraw %}For our formalisation, in this case, we can use a stronger
relation than `—↠`, replacing it by `—→`.

We can now state and prove that the relation is a simulation.
Again, in this case, we can use a stronger relation than
`—↠`, replacing it by `—→`:
{% raw %}<pre class="Agda"><a id="sim"></a><a id="9628" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9628" class="Function">sim</a> <a id="9632" class="Symbol">:</a> <a id="9634" class="Symbol">∀</a> <a id="9636" class="Symbol">{</a><a id="9637" href="plfa.Bisimulation.html#9637" class="Bound">Γ</a> <a id="9639" href="plfa.Bisimulation.html#9639" class="Bound">A</a><a id="9640" class="Symbol">}</a> <a id="9642" class="Symbol">{</a><a id="9643" href="plfa.Bisimulation.html#9643" class="Bound">M</a> <a id="9645" href="plfa.Bisimulation.html#9645" class="Bound">M†</a> <a id="9648" href="plfa.Bisimulation.html#9648" class="Bound">N</a> <a id="9650" class="Symbol">:</a> <a id="9652" href="plfa.Bisimulation.html#9637" class="Bound">Γ</a> <a id="9654" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14946" class="Datatype Operator">⊢</a> <a id="9656" href="plfa.Bisimulation.html#9639" class="Bound">A</a><a id="9657" class="Symbol">}</a>
  <a id="9661" class="Symbol">→</a> <a id="9663" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9643" class="Bound">M</a> <a id="9665" href="plfa.Bisimulation.html#3796" class="Datatype Operator">~</a> <a id="9667" href="plfa.Bisimulation.html#9645" class="Bound">M†</a>
  <a id="9672" class="Symbol">→</a> <a id="9674" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9643" class="Bound">M</a> <a id="9676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#19555" class="Datatype Operator">—→</a> <a id="9679" href="plfa.Bisimulation.html#9648" class="Bound">N</a>
    <a id="9685" class="Comment">---------</a>
  <a id="9697" class="Symbol">→</a> <a id="9699" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9252" class="Datatype">Leg</a>  <a id="9704" href="plfa.Bisimulation.html#9645" class="Bound">M†</a> <a id="9707" href="plfa.Bisimulation.html#9648" class="Bound">N</a>
<a id="9709" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9628" class="Function">sim</a> <a id="9713" href="plfa.Bisimulation.html#3845" class="InductiveConstructor">~`</a>              <a id="9729" class="Symbol">()</a>
<a id="9732" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9628" class="Function">sim</a> <a id="9736" class="Symbol">(</a><a id="9737" href="plfa.Bisimulation.html#3903" class="InductiveConstructor Operator">~ƛ</a> <a id="9740" href="plfa.Bisimulation.html#9740" class="Bound">~N</a><a id="9742" class="Symbol">)</a>         <a id="9752" class="Symbol">()</a>
<a id="9755" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9628" class="Function">sim</a> <a id="9759" class="Symbol">(</a><a id="9760" href="plfa.Bisimulation.html#9760" class="Bound">~L</a> <a id="9763" href="plfa.Bisimulation.html#3988" class="InductiveConstructor Operator">~·</a> <a id="9766" href="plfa.Bisimulation.html#9766" class="Bound">~M</a><a id="9768" class="Symbol">)</a>      <a id="9775" class="Symbol">(</a><a id="9776" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#19621" class="InductiveConstructor">ξ-·₁</a> <a id="9781" href="plfa.Bisimulation.html#9781" class="Bound">L—→</a><a id="9784" class="Symbol">)</a>
  <a id="9788" class="Keyword">with</a> <a id="9793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9628" class="Function">sim</a> <a id="9797" href="plfa.Bisimulation.html#9760" class="Bound">~L</a> <a id="9800" href="plfa.Bisimulation.html#9781" class="Bound">L—→</a>
<a id="9804" class="Symbol">...</a>  <a id="9809" class="Symbol">|</a> <a id="9811" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9292" class="InductiveConstructor">leg</a> <a id="9815" href="plfa.Bisimulation.html#9815" class="Bound">~L′</a> <a id="9819" href="plfa.Bisimulation.html#9819" class="Bound">L†—→</a>                 <a id="9840" class="Symbol">=</a>  <a id="9843" href="plfa.Bisimulation.html#9292" class="InductiveConstructor">leg</a> <a id="9847" class="Symbol">(</a><a id="9848" href="plfa.Bisimulation.html#9815" class="Bound">~L′</a> <a id="9852" href="plfa.Bisimulation.html#3988" class="InductiveConstructor Operator">~·</a> <a id="9855" class="Bound">~M</a><a id="9857" class="Symbol">)</a>   <a id="9861" class="Symbol">(</a><a id="9862" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#19621" class="InductiveConstructor">ξ-·₁</a> <a id="9867" href="plfa.Bisimulation.html#9819" class="Bound">L†—→</a><a id="9871" class="Symbol">)</a>
<a id="9873" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9628" class="Function">sim</a> <a id="9877" class="Symbol">(</a><a id="9878" href="plfa.Bisimulation.html#9878" class="Bound">~V</a> <a id="9881" href="plfa.Bisimulation.html#3988" class="InductiveConstructor Operator">~·</a> <a id="9884" href="plfa.Bisimulation.html#9884" class="Bound">~M</a><a id="9886" class="Symbol">)</a>      <a id="9893" class="Symbol">(</a><a id="9894" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#19730" class="InductiveConstructor">ξ-·₂</a> <a id="9899" href="plfa.Bisimulation.html#9899" class="Bound">VV</a> <a id="9902" href="plfa.Bisimulation.html#9902" class="Bound">M—→</a><a id="9905" class="Symbol">)</a>
  <a id="9909" class="Keyword">with</a> <a id="9914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9628" class="Function">sim</a> <a id="9918" href="plfa.Bisimulation.html#9884" class="Bound">~M</a> <a id="9921" href="plfa.Bisimulation.html#9902" class="Bound">M—→</a>
<a id="9925" class="Symbol">...</a>  <a id="9930" class="Symbol">|</a> <a id="9932" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9292" class="InductiveConstructor">leg</a> <a id="9936" href="plfa.Bisimulation.html#9936" class="Bound">~M′</a> <a id="9940" href="plfa.Bisimulation.html#9940" class="Bound">M†—→</a>                 <a id="9961" class="Symbol">=</a>  <a id="9964" href="plfa.Bisimulation.html#9292" class="InductiveConstructor">leg</a> <a id="9968" class="Symbol">(</a><a id="9969" class="Bound">~V</a> <a id="9972" href="plfa.Bisimulation.html#3988" class="InductiveConstructor Operator">~·</a> <a id="9975" href="plfa.Bisimulation.html#9936" class="Bound">~M′</a><a id="9978" class="Symbol">)</a>   <a id="9982" class="Symbol">(</a><a id="9983" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#19730" class="InductiveConstructor">ξ-·₂</a> <a id="9988" class="Symbol">(</a><a id="9989" href="plfa.Bisimulation.html#4945" class="Function">~val</a> <a id="9994" class="Bound">~V</a> <a id="9997" class="Bound">VV</a><a id="9999" class="Symbol">)</a> <a id="10001" href="plfa.Bisimulation.html#9940" class="Bound">M†—→</a><a id="10005" class="Symbol">)</a>
<a id="10007" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9628" class="Function">sim</a> <a id="10011" class="Symbol">((</a><a id="10013" href="plfa.Bisimulation.html#3903" class="InductiveConstructor Operator">~ƛ</a> <a id="10016" href="plfa.Bisimulation.html#10016" class="Bound">~N</a><a id="10018" class="Symbol">)</a> <a id="10020" href="plfa.Bisimulation.html#3988" class="InductiveConstructor Operator">~·</a> <a id="10023" href="plfa.Bisimulation.html#10023" class="Bound">~V</a><a id="10025" class="Symbol">)</a> <a id="10027" class="Symbol">(</a><a id="10028" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#19853" class="InductiveConstructor">β-ƛ</a> <a id="10032" href="plfa.Bisimulation.html#10032" class="Bound">VV</a><a id="10034" class="Symbol">)</a>        <a id="10043" class="Symbol">=</a>  <a id="10046" href="plfa.Bisimulation.html#9292" class="InductiveConstructor">leg</a> <a id="10050" class="Symbol">(</a><a id="10051" href="plfa.Bisimulation.html#8315" class="Function">~sub</a> <a id="10056" href="plfa.Bisimulation.html#10016" class="Bound">~N</a> <a id="10059" href="plfa.Bisimulation.html#10023" class="Bound">~V</a><a id="10061" class="Symbol">)</a>  <a id="10064" class="Symbol">(</a><a id="10065" href="plfa.More.html#19853" class="InductiveConstructor">β-ƛ</a> <a id="10069" class="Symbol">(</a><a id="10070" href="plfa.Bisimulation.html#4945" class="Function">~val</a> <a id="10075" href="plfa.Bisimulation.html#10023" class="Bound">~V</a> <a id="10078" href="plfa.Bisimulation.html#10032" class="Bound">VV</a><a id="10080" class="Symbol">))</a>
<a id="10083" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9628" class="Function">sim</a> <a id="10087" class="Symbol">(</a><a id="10088" href="plfa.Bisimulation.html#4112" class="InductiveConstructor">~let</a> <a id="10093" href="plfa.Bisimulation.html#10093" class="Bound">~M</a> <a id="10096" href="plfa.Bisimulation.html#10096" class="Bound">~N</a><a id="10098" class="Symbol">)</a>    <a id="10103" class="Symbol">(</a><a id="10104" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#20911" class="InductiveConstructor">ξ-let</a> <a id="10110" href="plfa.Bisimulation.html#10110" class="Bound">M—→</a><a id="10113" class="Symbol">)</a>
  <a id="10117" class="Keyword">with</a> <a id="10122" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9628" class="Function">sim</a> <a id="10126" href="plfa.Bisimulation.html#10093" class="Bound">~M</a> <a id="10129" href="plfa.Bisimulation.html#10110" class="Bound">M—→</a>
<a id="10133" class="Symbol">...</a>  <a id="10138" class="Symbol">|</a> <a id="10140" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9292" class="InductiveConstructor">leg</a> <a id="10144" href="plfa.Bisimulation.html#10144" class="Bound">~M′</a> <a id="10148" href="plfa.Bisimulation.html#10148" class="Bound">M†—→</a>                 <a id="10169" class="Symbol">=</a>  <a id="10172" href="plfa.Bisimulation.html#9292" class="InductiveConstructor">leg</a> <a id="10176" class="Symbol">(</a><a id="10177" href="plfa.Bisimulation.html#4112" class="InductiveConstructor">~let</a> <a id="10182" href="plfa.Bisimulation.html#10144" class="Bound">~M′</a> <a id="10186" class="Bound">~N</a><a id="10188" class="Symbol">)</a> <a id="10190" class="Symbol">(</a><a id="10191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#19730" class="InductiveConstructor">ξ-·₂</a> <a id="10196" href="plfa.More.html#18943" class="InductiveConstructor">V-ƛ</a> <a id="10200" href="plfa.Bisimulation.html#10148" class="Bound">M†—→</a><a id="10204" class="Symbol">)</a>
<a id="10206" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9628" class="Function">sim</a> <a id="10210" class="Symbol">(</a><a id="10211" href="plfa.Bisimulation.html#4112" class="InductiveConstructor">~let</a> <a id="10216" href="plfa.Bisimulation.html#10216" class="Bound">~V</a> <a id="10219" href="plfa.Bisimulation.html#10219" class="Bound">~N</a><a id="10221" class="Symbol">)</a>    <a id="10226" class="Symbol">(</a><a id="10227" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#21033" class="InductiveConstructor">β-let</a> <a id="10233" href="plfa.Bisimulation.html#10233" class="Bound">VV</a><a id="10235" class="Symbol">)</a>      <a id="10242" class="Symbol">=</a>  <a id="10245" href="plfa.Bisimulation.html#9292" class="InductiveConstructor">leg</a> <a id="10249" class="Symbol">(</a><a id="10250" href="plfa.Bisimulation.html#8315" class="Function">~sub</a> <a id="10255" href="plfa.Bisimulation.html#10219" class="Bound">~N</a> <a id="10258" href="plfa.Bisimulation.html#10216" class="Bound">~V</a><a id="10260" class="Symbol">)</a>  <a id="10263" class="Symbol">(</a><a id="10264" href="plfa.More.html#19853" class="InductiveConstructor">β-ƛ</a> <a id="10268" class="Symbol">(</a><a id="10269" href="plfa.Bisimulation.html#4945" class="Function">~val</a> <a id="10274" href="plfa.Bisimulation.html#10216" class="Bound">~V</a> <a id="10277" href="plfa.Bisimulation.html#10233" class="Bound">VV</a><a id="10279" class="Symbol">))</a>
</pre>{% endraw %}The proof is by case analysis, examining each possible instance of `M ~ M†`
and each possible instance of `M —→ M†`, using recursive invocation whenever
the reduction is by a `ξ` rule, and hence contains another reduction.
In its structure, it looks a little bit like a proof of progress:

* If the related terms are variables, no reduction applies.
* If the related terms are abstractions, no reduction applies.
* If the related terms are applications, there are three subcases:
  - The source term reduces via `ξ-·₁`, in which case the target term does as well.
    Recursive invocation gives us

        L  --- —→ ---  L′
        |              |
        |              |
        ~              ~
        |              |
        |              |
        L† --- —→ --- L′†

    from which follows:

         L · M  --- —→ ---  L′ · M
           |                   |
           |                   |
           ~                   ~
           |                   |
           |                   |
        L† · M† --- —→ --- L′† · M†

  - The source term reduces via `ξ-·₂`, in which case the target term does as well.
    Recursive invocation gives us

        M  --- —→ ---  M′
        |              |
        |              |
        ~              ~
        |              |
        |              |
        M† --- —→ --- M′†

    from which follows:

         V · M  --- —→ ---  V · M′
           |                  |
           |                  |
           ~                  ~
           |                  |
           |                  |
        V† · M† --- —→ --- V† · M′†

    Since simulation commutes with values and `V` is a value, `V†` is also a value.

  - The source term reduces via `β-ƛ`, in which case the target term does as well:

         (ƛ x ⇒ N) · V  --- —→ ---  N [ x := V ]
              |                           |
              |                           |
              ~                           ~
              |                           |
              |                           |
        (ƛ x ⇒ N†) · V† --- —→ --- N† [ x :=  V† ]

    Since simulation commutes with values and `V` is a value, `V†` is also a value.
    Since simulation commutes with substitution and `N ~ N†` and `V ~ V†`,
    we have `N [ x := V] ~ N† [ x := V† ]`.

* If the related terms are a let and an application of an abstraction,
  there are two subcases:

  - The source term reduces via `ξ-let`, in which case the target term
    reduces via `ξ-·₂`.  Recursive invocation gives us

        M  --- —→ ---  M′
        |              |
        |              |
        ~              ~
        |              |
        |              |
        M† --- —→ --- M′†

    from which follows:

        let x = M in N --- —→ --- let x = M′ in N
              |                         |
              |                         |
              ~                         ~
              |                         |
              |                         |
        (ƛ x ⇒ N) · M  --- —→ --- (ƛ x ⇒ N) · M′

  - The source term reduces via `β-let`, in which case the target
    term reduces via `β-ƛ`:

        let x = V in N  --- —→ ---  N [ x := V ]
              |                         |
              |                         |
              ~                         ~
              |                         |
              |                         |
        (ƛ x ⇒ N†) · V† --- —→ --- N† [ x := V ]

    Since simulation commutes with values and `V` is a value, `V†` is also a value.
    Since simulation commutes with substitution and `N ~ N†` and `V ~ V†`,
    we have `N [ x := V] ~ N† [ x := V† ]`.


#### Exercise `sim⁻¹`

Show that we also have a simulation in the other direction, and hence that we have
a bisimulation.

{% raw %}<pre class="Agda"><a id="14047" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `products`

Show that the two formulations of products in
Chapter [More]({{ site.baseurl }}/More/)
are in bisimulation.  The only constructs you need to include are
variables, and those connected to functions and products.
In this case, the simulation is _not_ lock-step.

{% raw %}<pre class="Agda"><a id="14366" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Unicode

This chapter uses the following unicode:

    †  U+2020  DAGGER (\dag)
    ⁻  U+207B  SUPERSCRIPT MINUS (\^-)
    ¹  U+00B9  SUPERSCRIPT ONE (\^1)
