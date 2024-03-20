---
title       : "Compositional: 指称语义是可组合的"
permalink   : /Compositional/
translators : ["OlingCat"]
---

```agda
module plfa.part3.Compositional where
```

<!--
## Introduction
-->

## 简介

<!--
In this chapter we prove that the denotational semantics is compositional,
which means we fill in the ellipses in the following equations.
-->

本章我们会证明指称语义是可组合的，即我们会填补以下等式中省略号的部分。

    ℰ (` x) ≃ ...
    ℰ (ƛ M) ≃ ... ℰ M ...
    ℰ (M · N) ≃ ... ℰ M ... ℰ N ...

<!--
Such equations would imply that the denotational semantics could be
instead defined as a recursive function. Indeed, we end this chapter
with such a definition and prove that it is equivalent to ℰ.
-->

这些等式蕴含了指称语义也可以定义为一个递归函数。
我们会在本章的结尾给出它的定义，并证明它等价于 ℰ。


<!--
## Imports
-->

## 导入

```agda
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import plfa.part2.Untyped
  using (Context; _,_; ★; _∋_; _⊢_; `_; ƛ_; _·_)
open import plfa.part3.Denotational
  using (Value; _↦_; _`,_; _⊔_; ⊥; _⊑_; _⊢_↓_;
         ⊑-bot; ⊑-fun; ⊑-conj-L; ⊑-conj-R1; ⊑-conj-R2;
         ⊑-dist; ⊑-refl; ⊑-trans; ⊔↦⊔-dist;
         var; ↦-intro; ↦-elim; ⊔-intro; ⊥-intro; sub;
         up-env; ℰ; _≃_; ≃-sym; Denotation; Env)
open plfa.part3.Denotational.≃-Reasoning
```

<!--
## Equation for lambda abstraction
-->

## λ-抽象的等式

<!--
Regarding the first equation
-->

考虑第一个等式

    ℰ (ƛ M) ≃ ... ℰ M ...

<!--
we need to define a function that maps a `Denotation (Γ , ★)` to a
`Denotation Γ`. This function, let us name it `ℱ`, should mimic the
non-recursive part of the semantics when applied to a lambda term.  In
particular, we need to consider the rules `↦-intro`, `⊥-intro`, and
`⊔-intro`. So `ℱ` has three parameters, the denotation `D` of the
subterm `M`, an environment `γ`, and a value `v`.  If we define `ℱ` by
recursion on the value `v`, then it matches up nicely with the three
rules `↦-intro`, `⊥-intro`, and `⊔-intro`.
-->

我们需要定义一个函数，它将 `Denotation (Γ , ★)` 映射到 `Denotation Γ`，
我们将此函数命名为 `ℱ`。在应用到 λ-项时，它能够模拟语义中非递归的部分。
具体来说，我们需要考虑规则 `↦-intro`、`⊥-intro` 和 `⊔-intro`，因此 `ℱ`
有三个参数：子项 `M` 的指称 `D`、环境 `γ`，以及值 `v`。如果我们通过对值
`v` 进行递归来定义 `ℱ`，那么它正好匹配 `↦-intro`、`⊥-intro` 和 `⊔-intro`
这三条规则。

```agda
ℱ : ∀{Γ} → Denotation (Γ , ★) → Denotation Γ
ℱ D γ (v ↦ w) = D (γ `, v) w
ℱ D γ ⊥ = ⊤
ℱ D γ (u ⊔ v) = (ℱ D γ u) × (ℱ D γ v)
```

<!--
If one squints hard enough, the `ℱ` function starts to look like the
`curry` operation familiar to functional programmers. It turns a
function that expects a tuple of length `n + 1` (the environment `Γ , ★`)
into a function that expects a tuple of length `n` and returns a
function of one parameter.
-->

如果你仔细观察，就会发现 `ℱ` 函数看起来像函数式程序员熟悉的 `curry`
化操作：它将一个以长度为 `n + 1` 的元组（即环境 `Γ , ★`）作为参数的函数，
转化为一个以长度为 `n` 的元组作为参数，并返回一个单参函数的函数。

<!--
Using this `ℱ`, we hope to prove that
-->

我们希望通过 `ℱ` 函数证明

    ℰ (ƛ N) ≃ ℱ (ℰ N)

<!--
The function `ℱ` is preserved when going from a larger value `v` to a
smaller value `u`. The proof is a straightforward induction on the
derivation of `u ⊑ v`, using the `up-env` lemma in the case for the
`⊑-fun` rule.
-->

当从一个更大的值 `v` 映射到一个更小的值 `u` 时，函数 `ℱ` 会保持成立。
它的证明就是在 `⊑-fun` 规则的情况中使用 `up-env` 引理，对 `u ⊑ v` 推导过程的直接归纳。

```agda
sub-ℱ : ∀{Γ}{N : Γ , ★ ⊢ ★}{γ v u}
  → ℱ (ℰ N) γ v
  → u ⊑ v
    ------------
  → ℱ (ℰ N) γ u
sub-ℱ d ⊑-bot = tt
sub-ℱ d (⊑-fun lt lt′) = sub (up-env d lt) lt′
sub-ℱ d (⊑-conj-L lt lt₁) = ⟨ sub-ℱ d lt , sub-ℱ d lt₁ ⟩
sub-ℱ d (⊑-conj-R1 lt) = sub-ℱ (proj₁ d) lt
sub-ℱ d (⊑-conj-R2 lt) = sub-ℱ (proj₂ d) lt
sub-ℱ {v = v₁ ↦ v₂ ⊔ v₁ ↦ v₃} {v₁ ↦ (v₂ ⊔ v₃)} ⟨ N2 , N3 ⟩ ⊑-dist =
   ⊔-intro N2 N3
sub-ℱ d (⊑-trans x₁ x₂) = sub-ℱ (sub-ℱ d x₂) x₁
```

<!--
With this subsumption property in hand, we can prove the forward
direction of the semantic equation for lambda.  The proof is by
induction on the semantics, using `sub-ℱ` in the case for the `sub`
rule.
-->

有了这个小前提的性质，我们就可以证明 λ-等式语义前进的方向。
证明是通过在 `sub` 规则的情况下使用 `sub-ℱ`，对语义进行归纳得出的。

```agda
ℰƛ→ℱℰ : ∀{Γ}{γ : Env Γ}{N : Γ , ★ ⊢ ★}{v : Value}
  → ℰ (ƛ N) γ v
    ------------
  → ℱ (ℰ N) γ v
ℰƛ→ℱℰ (↦-intro d) = d
ℰƛ→ℱℰ ⊥-intro = tt
ℰƛ→ℱℰ (⊔-intro d₁ d₂) = ⟨ ℰƛ→ℱℰ d₁ , ℰƛ→ℱℰ d₂ ⟩
ℰƛ→ℱℰ (sub d lt) = sub-ℱ (ℰƛ→ℱℰ d) lt
```

<!--
The "inversion lemma" for lambda abstraction is a special case of the
above. The inversion lemma is useful in proving that denotations are
preserved by reduction.
-->

λ-抽象的「反演引理」是上面定理的一种特例。反演引理在证明「归约会保持指称不变」时会很有用。

```agda
lambda-inversion : ∀{Γ}{γ : Env Γ}{N : Γ , ★ ⊢ ★}{v₁ v₂ : Value}
  → γ ⊢ ƛ N ↓ v₁ ↦ v₂
    -----------------
  → (γ `, v₁) ⊢ N ↓ v₂
lambda-inversion{v₁ = v₁}{v₂ = v₂} d = ℰƛ→ℱℰ{v = v₁ ↦ v₂} d
```

<!--
The backward direction of the semantic equation for lambda is even
easier to prove than the forward direction. We proceed by induction on
the value v.
-->

λ-等式的语义后退的方向甚至比前进的方向更容易证明，我们只需对值 `v` 进行归纳：

```agda
ℱℰ→ℰƛ : ∀{Γ}{γ : Env Γ}{N : Γ , ★ ⊢ ★}{v : Value}
  → ℱ (ℰ N) γ v
    ------------
  → ℰ (ƛ N) γ v
ℱℰ→ℰƛ {v = ⊥} d = ⊥-intro
ℱℰ→ℰƛ {v = v₁ ↦ v₂} d = ↦-intro d
ℱℰ→ℰƛ {v = v₁ ⊔ v₂} ⟨ d1 , d2 ⟩ = ⊔-intro (ℱℰ→ℰƛ d1) (ℱℰ→ℰƛ d2)
```

<!--
So indeed, the denotational semantics is compositional with respect
to lambda abstraction, as witnessed by the function `ℱ`.
-->

因此，指称语义对 λ-抽象来说是可组合的，正如函数 `ℱ` 所证明的那样：

```agda
lam-equiv : ∀{Γ}{N : Γ , ★ ⊢ ★}
  → ℰ (ƛ N) ≃ ℱ (ℰ N)
lam-equiv γ v = ⟨ ℰƛ→ℱℰ , ℱℰ→ℰƛ ⟩
```


<!--
## Equation for function application
-->

## 函数应用的等式

<!--
Next we fill in the ellipses for the equation concerning function
application.
-->

接下来我们填补关于函数应用的等式中的省略号。

    ℰ (M · N) ≃ ... ℰ M ... ℰ N ...

<!--
For this we need to define a function that takes two denotations, both
in context `Γ`, and produces another one in context `Γ`. This
function, let us name it `●`, needs to mimic the non-recursive aspects
of the semantics of an application `L · M`.  We cannot proceed as
easily as for `ℱ` and define the function by recursion on value `v`
because, for example, the rule `↦-elim` applies to any value. Instead
we shall define `●` in a way that directly deals with the `↦-elim` and
`⊥-intro` rules but ignores `⊔-intro`. This makes the forward
direction of the proof more difficult, and the case for `⊔-intro`
demonstrates why the `⊑-dist` rule is important.
-->

为此我们需要定义一个函数，它接受语境 `Γ` 中的两个指称，并产生语境 `Γ`
中的另一个指称。我们将此函数命名为 `●`，以模拟应用语义 `L · M`
中非递归的部分。我们无法像处理 `ℱ` 那样简单地对值 `v` 进行递归来定义函数，
因为 `↦-elim` 这类的规则可应用于任何值。相反，我们将通过直接处理 `↦-elim`
和 `⊥-intro` 规则而忽略 `⊔-intro` 的方式来定义 `●`。这使得证明的前进方向变得更加困难，
而 `⊔-intro` 的情况说明了为什么 `⊑-dist` 规则很重要。

<!--
So we define the application of `D₁` to `D₂`, written `D₁ ● D₂`, to include
any value `w` equivalent to `⊥`, for the `⊥-intro` rule, and to include any
value `w` that is the output of an entry `v ↦ w` in `D₁`, provided the
input `v` is in `D₂`, for the `↦-elim` rule.
-->

这样我们就定义了 `D₁` 应用于 `D₂`，记作 `D₁ ● D₂`，来包含 `⊥-intro`
规则中所有等价于 `⊥` 的值 `w`，以及对于 `↦-elim` 规则，在 `D₁` 中的条目
`v ↦ w` 的所有输出值 `w`，前提是它的输入值 `v` 在 `D₂` 中。

```agda
infixl 7 _●_

_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ
(D₁ ● D₂) γ w = w ⊑ ⊥ ⊎ Σ[ v ∈ Value ]( D₁ γ (v ↦ w) × D₂ γ v )
```

<!--
If one squints hard enough, the `_●_` operator starts to look
like the `apply` operation familiar to functional programmers.
It takes two parameters and applies the first to the second.
-->

<!--
If one squints hard enough, the `_●_` operator starts to look
like the `apply` operation familiar to functional programmers.
It takes two parameters and applies the first to the second.
-->

如果你仔细观察一下，就会发现 `_●_` 运算符看起来像函数式程序员熟悉的
`apply` 操作：它接受两个参数，并将第一个参数应用于第二个参数。

<!--
Next we consider the inversion lemma for application, which is also
the forward direction of the semantic equation for application.  We
describe the proof below.
-->

接下来我们考虑应用的反演引理，它同样是应用的语义等式的前进方向。
下面是它的证明：

```agda
ℰ·→●ℰ : ∀{Γ}{γ : Env Γ}{L M : Γ ⊢ ★}{v : Value}
  → ℰ (L · M) γ v
    ----------------
  → (ℰ L ● ℰ M) γ v
ℰ·→●ℰ (↦-elim{v = v′} d₁ d₂) = inj₂ ⟨ v′ , ⟨ d₁ , d₂ ⟩ ⟩
ℰ·→●ℰ {v = ⊥} ⊥-intro = inj₁ ⊑-bot
ℰ·→●ℰ {Γ}{γ}{L}{M}{v} (⊔-intro{v = v₁}{w = v₂} d₁ d₂)
    with ℰ·→●ℰ d₁ | ℰ·→●ℰ d₂
... | inj₁ lt1 | inj₁ lt2 = inj₁ (⊑-conj-L lt1 lt2)
... | inj₁ lt1 | inj₂ ⟨ v₁′ , ⟨ L↓v12 , M↓v3 ⟩ ⟩ =
      inj₂ ⟨ v₁′ , ⟨ sub L↓v12 lt , M↓v3 ⟩ ⟩
      where lt : v₁′ ↦ (v₁ ⊔ v₂) ⊑ v₁′ ↦ v₂
            lt = (⊑-fun ⊑-refl (⊑-conj-L (⊑-trans lt1 ⊑-bot) ⊑-refl))
... | inj₂ ⟨ v₁′ , ⟨ L↓v12 , M↓v3 ⟩ ⟩ | inj₁ lt2 =
      inj₂ ⟨ v₁′ , ⟨ sub L↓v12 lt , M↓v3 ⟩ ⟩
      where lt : v₁′ ↦ (v₁ ⊔ v₂) ⊑ v₁′ ↦ v₁
            lt = (⊑-fun ⊑-refl (⊑-conj-L ⊑-refl (⊑-trans lt2 ⊑-bot)))
... | inj₂ ⟨ v₁′ , ⟨ L↓v12 , M↓v3 ⟩ ⟩ | inj₂ ⟨ v₁′′ , ⟨ L↓v12′ , M↓v3′ ⟩ ⟩ =
      let L↓⊔ = ⊔-intro L↓v12 L↓v12′ in
      let M↓⊔ = ⊔-intro M↓v3 M↓v3′ in
      inj₂ ⟨ v₁′ ⊔ v₁′′ , ⟨ sub L↓⊔ ⊔↦⊔-dist , M↓⊔ ⟩ ⟩
ℰ·→●ℰ {Γ}{γ}{L}{M}{v} (sub d lt)
    with ℰ·→●ℰ d
... | inj₁ lt2 = inj₁ (⊑-trans lt lt2)
... | inj₂ ⟨ v₁ , ⟨ L↓v12 , M↓v3 ⟩ ⟩ =
      inj₂ ⟨ v₁ , ⟨ sub L↓v12 (⊑-fun ⊑-refl lt) , M↓v3 ⟩ ⟩
```

<!--
We proceed by induction on the semantics.
-->

我们通过对语义进行归纳来证明：

<!--
* In case `↦-elim` we have `γ ⊢ L ↓ (v′ ↦ v)` and `γ ⊢ M ↓ v′`,
  which is all we need to show `(ℰ L ● ℰ M) γ v`.

* In case `⊥-intro` we have `v = ⊥`. We conclude that `v ⊑ ⊥`.
-->

* 对于 `↦-elim` 的情况，我们有 `γ ⊢ L ↓ (v′ ↦ v)` 和 `γ ⊢ M ↓ v′`，
  只需证明 `(ℰ L ● ℰ M) γ v` 即可。

* 对于 `⊥-intro` 的情况，我们有 `v = ⊥`，于是可推出 `v ⊑ ⊥`。

<!--
* In case `⊔-intro` we have `ℰ (L · M) γ v₁` and `ℰ (L · M) γ v₂`
  and need to show `(ℰ L ● ℰ M) γ (v₁ ⊔ v₂)`. By the induction
  hypothesis, we have `(ℰ L ● ℰ M) γ v₁` and `(ℰ L ● ℰ M) γ v₂`.
  We have four subcases to consider.

    * Suppose `v₁ ⊑ ⊥` and `v₂ ⊑ ⊥`. Then `v₁ ⊔ v₂ ⊑ ⊥`.
    * Suppose `v₁ ⊑ ⊥`, `γ ⊢ L ↓ v₁′ ↦ v₂`, and `γ ⊢ M ↓ v₁′`.
      We have `γ ⊢ L ↓ v₁′ ↦ (v₁ ⊔ v₂)` by rule `sub`
      because `v₁′ ↦ (v₁ ⊔ v₂) ⊑ v₁′ ↦ v₂`.
    * Suppose `γ ⊢ L ↓ v₁′ ↦ v₁`, `γ ⊢ M ↓ v₁′`, and `v₂ ⊑ ⊥`.
      We have `γ ⊢ L ↓ v₁′ ↦ (v₁ ⊔ v₂)` by rule `sub`
      because `v₁′ ↦ (v₁ ⊔ v₂) ⊑ v₁′ ↦ v₁`.
    * Suppose `γ ⊢ L ↓ v₁′′ ↦ v₁, γ ⊢ M ↓ v₁′′`,
      `γ ⊢ L ↓ v₁′ ↦ v₂`, and `γ ⊢ M ↓ v₁′`.
      This case is the most interesting.
      By two uses of the rule `⊔-intro` we have
      `γ ⊢ L ↓ (v₁′ ↦ v₂) ⊔ (v₁′′ ↦ v₁)` and
      `γ ⊢ M ↓ (v₁′ ⊔ v₁′′)`. But this does not yet match
      what we need for `ℰ L ● ℰ M` because the result of
      `L` must be an `↦` whose input entry is `v₁′ ⊔ v₁′′`.
      So we use the `sub` rule to obtain
      `γ ⊢ L ↓ (v₁′ ⊔ v₁′′) ↦ (v₁ ⊔ v₂)`,
      using the `⊔↦⊔-dist` lemma (thanks to the `⊑-dist` rule) to
      show that

            (v₁′ ⊔ v₁′′) ↦ (v₁ ⊔ v₂) ⊑ (v₁′ ↦ v₂) ⊔ (v₁′′ ↦ v₁)

      So we have proved what is needed for this case.
-->

* 对于 `⊔-intro` 的情况，我们有 `ℰ (L · M) γ v₁` 和 `ℰ (L · M) γ v₂`，
  且需要证明 `(ℰ L ● ℰ M) γ (v₁ ⊔ v₂)`。根据归纳假设，我们有
  `(ℰ L ● ℰ M) γ v₁` 和 `(ℰ L ● ℰ M) γ v₂`，于是我们需要考虑四种子情况：

    * 假设 `v₁ ⊑ ⊥` 且 `v₂ ⊑ ⊥`，那么 `v₁ ⊔ v₂ ⊑ ⊥`。
    * 假设 `v₁ ⊑ ⊥`，`γ ⊢ L ↓ v₁′ ↦ v₂` 且 `γ ⊢ M ↓ v₁′`，
      根据 `sub` 规则我们有 `γ ⊢ L ↓ v₁′ ↦ (v₁ ⊔ v₂)`，因为
      `v₁′ ↦ (v₁ ⊔ v₂) ⊑ v₁′ ↦ v₂`。
    * 假设 `γ ⊢ L ↓ v₁′ ↦ v₁`，`γ ⊢ M ↓ v₁′` 且 `v₂ ⊑ ⊥`，
      根据 `sub` 规则我们有 `γ ⊢ L ↓ v₁′ ↦ (v₁ ⊔ v₂)`，因为
      `v₁′ ↦ (v₁ ⊔ v₂) ⊑ v₁′ ↦ v₁`。
    * 假设 `γ ⊢ L ↓ v₁′′ ↦ v₁, γ ⊢ M ↓ v₁′′`，
      `γ ⊢ L ↓ v₁′ ↦ v₂` 且 `γ ⊢ M ↓ v₁′`，
      这种情况是最有趣的部分。通过使用两次 `⊔-intro`，我们有
      `γ ⊢ L ↓ (v₁′ ↦ v₂) ⊔ (v₁′′ ↦ v₁)` 且
      `γ ⊢ M ↓ (v₁′ ⊔ v₁′′)`。但它对 `ℰ L ● ℰ M` 来说与我们的需要尚不匹配，
      因为 `L` 的结果必须是一个输入条目为 `v₁′ ⊔ v₁′′` 的 `↦`。
      因此我们需要使用 `sub` 规则来得到 `γ ⊢ L ↓ (v₁′ ⊔ v₁′′) ↦ (v₁ ⊔ v₂)`；
      使用 `⊔↦⊔-dist` 引理（感谢 `⊑-dist` 规则）来证明：

            (v₁′ ⊔ v₁′′) ↦ (v₁ ⊔ v₂) ⊑ (v₁′ ↦ v₂) ⊔ (v₁′′ ↦ v₁)

      这样我们就证明了该情况所有的子情况。

* 对于情况 `sub`，我们有 `Γ ⊢ L · M ↓ v₁` 且 `v ⊑ v₁`。
  根据归纳假设，我们有 `(ℰ L ● ℰ M) γ v₁`，于是我们需要考虑两种子情况：

    * 假设 `v₁ ⊑ ⊥`，我们可推出 `v ⊑ ⊥`。
    * 假设 `Γ ⊢ L ↓ v′ → v₁` 且 `Γ ⊢ M ↓ v′`，我们可根据规则 `sub`
      推出 `Γ ⊢ L ↓ v′ → v`，因为 `v′ → v ⊑ v′ → v₁`。

<!--
The backward direction is proved by cases on the premise `(ℰ L ● ℰ M) γ v`.
In case `v ⊑ ⊥`, we obtain `Γ ⊢ L · M ↓ ⊥` by rule `⊥-intro`.
Otherwise, we conclude immediately by rule `↦-elim`.
-->

后退的方向可通过在前提 `(ℰ L ● ℰ M) γ v` 下进行情况分析来证明。
对于情况 `v ⊑ ⊥`，我们可通过规则 `⊥-intro` 得到 `Γ ⊢ L · M ↓ ⊥`。
否则，我们可直接通过规则 `↦-elim` 得出结论：

```agda
●ℰ→ℰ· : ∀{Γ}{γ : Env Γ}{L M : Γ ⊢ ★}{v}
  → (ℰ L ● ℰ M) γ v
    ----------------
  → ℰ (L · M) γ v
●ℰ→ℰ· {γ}{v} (inj₁ lt) = sub ⊥-intro lt
●ℰ→ℰ· {γ}{v} (inj₂ ⟨ v₁ , ⟨ d1 , d2 ⟩ ⟩) = ↦-elim d1 d2
```

<!--
So we have proved that the semantics is compositional with respect to
function application, as witnessed by the `●` function.
-->

这样我们就通过 `●` 函数的相关定理，证明了对于函数应用来说，语义是可组合的。

```agda
app-equiv : ∀{Γ}{L M : Γ ⊢ ★}
  → ℰ (L · M) ≃ (ℰ L) ● (ℰ M)
app-equiv γ v = ⟨ ℰ·→●ℰ , ●ℰ→ℰ· ⟩
```

<!--
We also need an inversion lemma for variables.
If `Γ ⊢ x ↓ v`, then `v ⊑ γ x`. The proof is a straightforward
induction on the semantics.
-->

我们还需要一个变量的反演引理：若 `Γ ⊢ x ↓ v`，则 `v ⊑ γ x`。
它的证明就是对语义的直接归纳：

```agda
var-inv : ∀ {Γ v x} {γ : Env Γ}
  → ℰ (` x) γ v
    -------------------
  → v ⊑ γ x
var-inv (var) = ⊑-refl
var-inv (⊔-intro d₁ d₂) = ⊑-conj-L (var-inv d₁) (var-inv d₂)
var-inv (sub d lt) = ⊑-trans lt (var-inv d)
var-inv ⊥-intro = ⊑-bot
```

<!--
To round-out the semantic equations, we establish the following one
for variables.
-->

为了完善语义等式，我们建立以下变量等式：

```agda
var-equiv : ∀{Γ}{x : Γ ∋ ★} → ℰ (` x) ≃ (λ γ v → v ⊑ γ x)
var-equiv γ v = ⟨ var-inv , (λ lt → sub var lt) ⟩
```


<!--
## Congruence
-->

## 合同性

<!--
The main work of this chapter is complete: we have established
semantic equations that show how the denotational semantics is
compositional. In this section and the next we make use of these
equations to prove some corollaries: that denotational equality is a
_congruence_ and to prove the _compositionality property_, which states
that surrounding two denotationally-equal terms in the same context
produces two programs that are denotationally equal.
-->

本章的主要工作已经完成：我们建立了语义等式来展示指称语义是如何组合的。
在本节和下一节中，我们将利用这些等式来证明一些推论：指称相等满足**合同性（congruence）**，
并证明指称具有**可组合性（compositionality property）**，
该性质指出在同一语境中，两个指称相等的项会产生两个指称相等的程序 。

<!--
We begin by showing that denotational equality is a congruence with
respect to lambda abstraction: that `ℰ N ≃ ℰ N′` implies `ℰ (ƛ N) ≃ ℰ
(ƛ N′)`. We shall use the `lam-equiv` equation to reduce this question to
whether `ℱ` is a congruence.
-->

我们首先证明指称相等对 λ-抽象满足合同性：`ℰ N ≃ ℰ N′` 蕴含
`ℰ (ƛ N) ≃ ℰ (ƛ N′)`。我们用 `lam-equiv` 等式将这个问题简化为
`ℱ` 是否满足合同性：

```agda
ℱ-cong : ∀{Γ}{D D′ : Denotation (Γ , ★)}
  → D ≃ D′
    -----------
  → ℱ D ≃ ℱ D′
ℱ-cong{Γ} D≃D′ γ v =
  ⟨ (λ x → ℱ≃{γ}{v} x D≃D′) , (λ x → ℱ≃{γ}{v} x (≃-sym D≃D′)) ⟩
  where
  ℱ≃ : ∀{γ : Env Γ}{v}{D D′ : Denotation (Γ , ★)}
    → ℱ D γ v  →  D ≃ D′ → ℱ D′ γ v
  ℱ≃ {v = ⊥} fd dd′ = tt
  ℱ≃ {γ}{v ↦ w} fd dd′ = proj₁ (dd′ (γ `, v) w) fd
  ℱ≃ {γ}{u ⊔ w} fd dd′ = ⟨ ℱ≃{γ}{u} (proj₁ fd) dd′ , ℱ≃{γ}{w} (proj₂ fd) dd′ ⟩
```

<!--
The proof of `ℱ-cong` uses the lemma `ℱ≃` to handle both directions of
the if-and-only-if. That lemma is proved by a straightforward
induction on the value `v`.
-->

`ℱ-cong` 的证明使用了 `ℱ≃` 来处理「当且仅当」的两个方向。
该引理直接通过对值 `v` 进行归纳得证。

<!--
We now prove that lambda abstraction is a congruence by direct
equational reasoning.
-->

现在我们通过直白的等式推理证明 λ-抽象满足合同性：

```agda
lam-cong : ∀{Γ}{N N′ : Γ , ★ ⊢ ★}
  → ℰ N ≃ ℰ N′
    -----------------
  → ℰ (ƛ N) ≃ ℰ (ƛ N′)
lam-cong {Γ}{N}{N′} N≃N′ =
  start
    ℰ (ƛ N)
  ≃⟨ lam-equiv ⟩
    ℱ (ℰ N)
  ≃⟨ ℱ-cong N≃N′ ⟩
    ℱ (ℰ N′)
  ≃⟨ ≃-sym lam-equiv ⟩
    ℰ (ƛ N′)
  ☐
```

<!--
Next we prove that denotational equality is a congruence for
application: that `ℰ L ≃ ℰ L′` and `ℰ M ≃ ℰ M′` imply
`ℰ (L · M) ≃ ℰ (L′ · M′)`. The `app-equiv` equation
reduces this to the question of whether the `●` operator
is a congruence.
-->

接下来我们证明指称相等对于应用也满足合同性：`ℰ L ≃ ℰ L′` 和 `ℰ M ≃ ℰ M′`
蕴含 `ℰ (L · M) ≃ ℰ (L′ · M′)`。等式 `app-equiv` 将其归约为 `●`
运算符是否满足合同性的问题。

```agda
●-cong : ∀{Γ}{D₁ D₁′ D₂ D₂′ : Denotation Γ}
  → D₁ ≃ D₁′ → D₂ ≃ D₂′
  → (D₁ ● D₂) ≃ (D₁′ ● D₂′)
●-cong {Γ} d1 d2 γ v = ⟨ (λ x → ●≃ x d1 d2) ,
                         (λ x → ●≃ x (≃-sym d1) (≃-sym d2)) ⟩
  where
  ●≃ : ∀{γ : Env Γ}{v}{D₁ D₁′ D₂ D₂′ : Denotation Γ}
    → (D₁ ● D₂) γ v  →  D₁ ≃ D₁′  →  D₂ ≃ D₂′
    → (D₁′ ● D₂′) γ v
  ●≃ (inj₁ v⊑⊥) eq₁ eq₂ = inj₁ v⊑⊥
  ●≃ {γ} {w} (inj₂ ⟨ v , ⟨ Dv↦w , Dv ⟩ ⟩) eq₁ eq₂ =
    inj₂ ⟨ v , ⟨ proj₁ (eq₁ γ (v ↦ w)) Dv↦w , proj₁ (eq₂ γ v) Dv ⟩ ⟩
```

<!--
Again, both directions of the if-and-only-if are proved via a lemma.
This time the lemma is proved by cases on `(D₁ ● D₂) γ v`.
-->

同样，「当且仅当」的两个方向需要通过一个引理来证明，而该引理则通过对
`(D₁ ● D₂) γ v` 进行情况分析来证明。

<!--
With the congruence of `●`, we can prove that application is a
congruence by direct equational reasoning.
-->

根据 `●` 的合同性，我们可以直接通过等式推理证明应用也满足合同性。

```agda
app-cong : ∀{Γ}{L L′ M M′ : Γ ⊢ ★}
  → ℰ L ≃ ℰ L′
  → ℰ M ≃ ℰ M′
    -------------------------
  → ℰ (L · M) ≃ ℰ (L′ · M′)
app-cong {Γ}{L}{L′}{M}{M′} L≅L′ M≅M′ =
  start
    ℰ (L · M)
  ≃⟨ app-equiv ⟩
    ℰ L ● ℰ M
  ≃⟨ ●-cong L≅L′ M≅M′ ⟩
    ℰ L′ ● ℰ M′
  ≃⟨ ≃-sym app-equiv ⟩
    ℰ (L′ · M′)
  ☐
```


<!--
## Compositionality
-->

## 可组合性

<!--
The _compositionality property_ states that surrounding two terms that
are denotationally equal in the same context produces two programs
that are denotationally equal. To make this precise, we define what we
mean by "context" and "surround".
-->

**可组合性（Compositionality Property）**说明了在同一语境下，
两个指称相等的项会产生两个指称相等的程序。为准确起见，我们定义了
「语境」和「在语境下」的含义。

<!--
A _context_ is a program with one hole in it. The following data
definition `Ctx` makes this idea explicit. We index the `Ctx` data
type with two contexts for variables: one for the hole and one for
terms that result from filling the hole.
-->

<!--
A _context_ is a program with one hole in it. The following data
definition `Ctx` makes this idea explicit. We index the `Ctx` data
type with two contexts for variables: one for the hole and one for
terms that result from filling the hole.
-->

**语境（Context）**是一个带洞的程序。以下数据定义 `Ctx` 将这个概念表示了出来。
我们使用两个变量语境来索引 `Ctx` 数据类型：一个表示洞，另一个表示填洞所产生的项。

```agda
data Ctx : Context → Context → Set where
  ctx-hole : ∀{Γ} → Ctx Γ Γ
  ctx-lam :  ∀{Γ Δ} → Ctx (Γ , ★) (Δ , ★) → Ctx (Γ , ★) Δ
  ctx-app-L : ∀{Γ Δ} → Ctx Γ Δ → Δ ⊢ ★ → Ctx Γ Δ
  ctx-app-R : ∀{Γ Δ} → Δ ⊢ ★ → Ctx Γ Δ → Ctx Γ Δ
```

<!--
* The constructor `ctx-hole` represents the hole, and in this case the
  variable context for the hole is the same as the variable context
  for the term that results from filling the hole.
-->

* 构造子 `ctx-hole` 表示洞，且在此情况中洞的变量语境
  与填洞所产生的项的变量语境相同。

<!--
* The constructor `ctx-lam` takes a `Ctx` and produces a larger one that
  adds a lambda abstraction at the top. The variable context of the
  hole stays the same, whereas we remove one variable from the context
  of the resulting term because it is bound by this lambda
  abstraction.
-->

* 构造子 `ctx-lam` 接受一个 `Ctx` 并在顶部添加 λ-抽象来产生一个更大的 `Ctx`。
  洞的变量语境保持不变，而我们从结果项的语境中删除一个变量，因为它被此
  λ-抽象约束。

<!--
* There are two constructions for application, `ctx-app-L` and
  `ctx-app-R`. The `ctx-app-L` is for when the hole is inside the left-hand
  term (the operator) and the later is when the hole is inside the
  right-hand term (the operand).
-->

* 应用有两种构造，`ctx-app-L` 和 `ctx-app-R`。`ctx-app-L`
  对应洞位于左侧项（运算符）内的情况，`ctx-app-R`
  对应洞位于右侧项（运算数）内的情况。

<!--
The action of surrounding a term with a context is defined by the
following `plug` function. It is defined by recursion on the context.
-->

将项插入到某个语境下的操作由以下 `plug` 函数定义，它是通过对语境进行递归来定义的：

```agda
plug : ∀{Γ}{Δ} → Ctx Γ Δ → Γ ⊢ ★ → Δ ⊢ ★
plug ctx-hole M = M
plug (ctx-lam C) N = ƛ plug C N
plug (ctx-app-L C N) L = (plug C L) · N
plug (ctx-app-R L C) M = L · (plug C M)
```

<!--
We are ready to state and prove the compositionality principle.  Given
two terms `M` and `N` that are denotationally equal, plugging them both
into an arbitrary context `C` produces two programs that are
denotationally equal.
-->

我们接下来陈述并证明组合性原则：给定两个项 `M` 和 `N`，若它们的指称相等，
那么将它们插入到任意语境 `C` 中都会产生两个指称相等的程序：

```agda
compositionality : ∀{Γ Δ}{C : Ctx Γ Δ} {M N : Γ ⊢ ★}
  → ℰ M ≃ ℰ N
    ---------------------------
  → ℰ (plug C M) ≃ ℰ (plug C N)
compositionality {C = ctx-hole} M≃N =
  M≃N
compositionality {C = ctx-lam C′} M≃N =
  lam-cong (compositionality {C = C′} M≃N)
compositionality {C = ctx-app-L C′ L} M≃N =
  app-cong (compositionality {C = C′} M≃N) λ γ v → ⟨ (λ x → x) , (λ x → x) ⟩
compositionality {C = ctx-app-R L C′} M≃N =
  app-cong (λ γ v → ⟨ (λ x → x) , (λ x → x) ⟩) (compositionality {C = C′} M≃N)
```

<!--
The proof is a straightforward induction on the context `C`, using the
congruence properties `lam-cong` and `app-cong` that we established
above.
-->

它可以通过直接对语境 `C` 进行归纳，用我们之前建立的合同性质
`lam-cong` 和 `app-cong` 来证明。

<!--
## The denotational semantics defined as a function
-->

## 指称语义作为函数来定义

<!--
Having established the three equations `var-equiv`, `lam-equiv`, and
`app-equiv`, one should be able to define the denotational semantics
as a recursive function over the input term `M`. Indeed, we define the
following function `⟦ M ⟧` that maps terms to denotations, using the
auxiliary curry `ℱ` and apply `●` functions in the cases for lambda
and application, respectively.
-->

建立了 `var-equiv`、`lam-equiv` 和 `app-equiv` 三个等式后，
我们就能将指称语义定义为一个在输入项 `M` 上递归的函数。其实，
我们可以定义以下函数 `⟦ M ⟧`，利用辅助的柯里化函数 `ℱ`，
并分别在 λ-抽象和应用的情况下应用 `●` 函数来将项映射到指称。

```agda
⟦_⟧ : ∀{Γ} → (M : Γ ⊢ ★) → Denotation Γ
⟦ ` x ⟧ γ v = v ⊑ γ x
⟦ ƛ N ⟧ = ℱ ⟦ N ⟧
⟦ L · M ⟧ = ⟦ L ⟧ ● ⟦ M ⟧
```

<!--
The proof that `ℰ M` is denotationally equal to `⟦ M ⟧` is a
straightforward induction, using the three equations
`var-equiv`, `lam-equiv`, and `app-equiv` together
with the congruence lemmas for `ℱ` and `●`.
-->

`ℰ M` 和 `⟦ M ⟧` 指称相等的证明可通过 `var-equiv`、`lam-equiv`
和 `app-equiv` 三个等式以及 `ℱ` 和 `●` 的合同性引理直接归纳得出。

```agda
ℰ≃⟦⟧ : ∀ {Γ} {M : Γ ⊢ ★} → ℰ M ≃ ⟦ M ⟧
ℰ≃⟦⟧ {Γ} {` x} = var-equiv
ℰ≃⟦⟧ {Γ} {ƛ N} =
  let ih = ℰ≃⟦⟧ {M = N} in
    ℰ (ƛ N)
  ≃⟨ lam-equiv ⟩
    ℱ (ℰ N)
  ≃⟨ ℱ-cong (ℰ≃⟦⟧ {M = N}) ⟩
    ℱ ⟦ N ⟧
  ≃⟨⟩
    ⟦ ƛ N ⟧
  ☐
ℰ≃⟦⟧ {Γ} {L · M} =
   ℰ (L · M)
  ≃⟨ app-equiv ⟩
   ℰ L ● ℰ M
  ≃⟨ ●-cong (ℰ≃⟦⟧ {M = L}) (ℰ≃⟦⟧ {M = M}) ⟩
   ⟦ L ⟧ ● ⟦ M ⟧
  ≃⟨⟩
    ⟦ L · M ⟧
  ☐
```


## Unicode

<!--
This chapter uses the following unicode:
-->

本章使用了以下 Unicode：

    ℱ  U+2131  SCRIPT CAPITAL F (\McF)
    ●  U+2131  BLACK CIRCLE (\cib)
