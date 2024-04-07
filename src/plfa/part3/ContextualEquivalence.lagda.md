---
title     : "ContextualEquivalence: 指称相等蕴含语境等价"
permalink : /ContextualEquivalence/
translators : ["OlingCat"]
---

```agda
module plfa.part3.ContextualEquivalence where
```

<!--
## Imports
-->

## 导入

```agda
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
     renaming (_,_ to ⟨_,_⟩)
open import plfa.part2.Untyped using (_⊢_; ★; ∅; _,_; ƛ_; _—↠_)
open import plfa.part2.BigStep using (_⊢_⇓_; cbn→reduce)
open import plfa.part3.Denotational using (ℰ; _≃_; ≃-sym; ≃-trans; _iff_)
open import plfa.part3.Compositional using (Ctx; plug; compositionality)
open import plfa.part3.Soundness using (soundness)
open import plfa.part3.Adequacy using (↓→⇓)
```

<!--
## Contextual Equivalence
-->

## 语境等价

<!--
The notion of _contextual equivalence_ is an important one for
programming languages because it is the sufficient condition for
changing a subterm of a program while maintaining the program's
overall behavior. Two terms `M` and `N` are contextually equivalent
if they can plugged into any context `C` and produce equivalent
results. As discuss in the Denotational chapter, the result of
a program in the lambda calculus is to terminate or not.
We characterize termination with the reduction semantics as follows.
-->

**语境等价（Contextual Equivalence）**对编程语言来说是一种很重要的概念，
因为它是在保持程序整体行为的同时更改程序子项的充分条件。若两个项 `M`
和 `N` 分别插入到任意语境 `C` 中所产生的结果等价，则二者语境等价。
正如指称语义一章中所讨论过的，λ-演算中程序所产生的结果要么停机要么发散。
我们用下面的归约语义来刻画停机：

```agda
terminates : ∀{Γ} → (M : Γ ⊢ ★) → Set
terminates {Γ} M = Σ[ N ∈ (Γ , ★ ⊢ ★) ] (M —↠ ƛ N)
```

<!--
So two terms are contextually equivalent if plugging them into the
same context produces two programs that either terminate or diverge
together.
-->

因此将语境等价的两个项插入到相同的语境中，产生的两个程序要么都停机，
要么都发散。

```agda
_≅_ : ∀{Γ} → (M N : Γ ⊢ ★) → Set
(_≅_ {Γ} M N) = ∀ {C : Ctx Γ ∅}
                → (terminates (plug C M)) iff (terminates (plug C N))
```

<!--
The contextual equivalence of two terms is difficult to prove directly
based on the above definition because of the universal quantification
of the context `C`. One of the main motivations for developing
denotational semantics is to have an alternative way to prove
contextual equivalence that instead only requires reasoning about the
two terms.
-->

由于语境 `C` 是全称量化的，因此两个项是否语境等价很难直接基于上述定义来证明。
发展指称语义的主要动机之一就是找到一种方式，只需要对两个项进行论证就能证明二者语境等价。


<!--
## Denotational equivalence implies contextual equivalence
-->

## 指称等价蕴含语境等价

<!--
Thankfully, the proof that denotational equality implies contextual
equivalence is an easy corollary of the results that we have already
established. Furthermore, the two directions of the if-and-only-if are
symmetric, so we can prove one lemma and then use it twice in the
theorem.
-->

值得庆幸的是，「指称等价蕴含语境等价」的证明是我们已经证明的结果的一个简单推论。
除此之外，「当且仅当」的两个方向是对称的，因此我们可以证明一个引理，
然后在主定理中应用它两次。

<!--
The lemma states that if `M` and `N` are denotationally equal
and if `M` plugged into `C` terminates, then so does
`N` plugged into `C`.
-->

该引理陈述了，若 `M` 和 `N` 指称等价，并且若将 `M` 插入到 `C`
中可停机，则将 `N` 插入到 `C` 中也停机。

```agda
denot-equal-terminates : ∀{Γ} {M N : Γ ⊢ ★} {C : Ctx Γ ∅}
  → ℰ M ≃ ℰ N  →  terminates (plug C M)
    -----------------------------------
  → terminates (plug C N)
denot-equal-terminates {Γ}{M}{N}{C} ℰM≃ℰN ⟨ N′ , CM—↠ƛN′ ⟩ =
  let ℰCM≃ℰƛN′ = soundness CM—↠ƛN′ in
  let ℰCM≃ℰCN = compositionality{Γ = Γ}{Δ = ∅}{C = C} ℰM≃ℰN in
  let ℰCN≃ℰƛN′ = ≃-trans (≃-sym ℰCM≃ℰCN) ℰCM≃ℰƛN′ in
    cbn→reduce (proj₂ (proj₂ (proj₂ (↓→⇓ ℰCN≃ℰƛN′))))
```

<!--
The proof is direct. Because `plug C —↠ plug C (ƛ N′)`,
we can apply soundness to obtain
-->

证明过程很直白，因为 `plug C —↠ plug C (ƛ N′)`，我们应用可靠性定理得到

    ℰ (plug C M) ≃ ℰ (ƛ N′)

<!--
From `ℰ M ≃ ℰ N`, compositionality gives us
-->

根据 `ℰ M ≃ ℰ N`，应用组合性定理可得

    ℰ (plug C M) ≃ ℰ (plug C N).

<!--
Putting these two facts together gives us
-->

将两个事实合并可得

    ℰ (plug C N) ≃ ℰ (ƛ N′).

<!--
We then apply `↓→⇓` from Chapter [Adequacy](/Adequacy/) to deduce
-->

应用[充分性](/Adequacy/)一章中的 `↓→⇓` 可推出

    ∅' ⊢ plug C N ⇓ clos (ƛ N′′) δ).

<!--
Call-by-name evaluation implies reduction to a lambda abstraction,
so we conclude that
-->

由于「传名调用求值」蕴含「可归约到 λ-抽象」，因此可得

    terminates (plug C N).


<!--
The main theorem follows by two applications of the lemma.
-->

两次应用该引理后，主定理即可得证。

```agda
denot-equal-contex-equal : ∀{Γ} {M N : Γ ⊢ ★}
  → ℰ M ≃ ℰ N
    ---------
  → M ≅ N
denot-equal-contex-equal{Γ}{M}{N} eq {C} =
   ⟨ (λ tm → denot-equal-terminates eq tm) ,
     (λ tn → denot-equal-terminates (≃-sym eq) tn) ⟩
```


## Unicode

<!--
This chapter uses the following unicode:
-->

本章使用了以下 Unicode：

    ≅  U+2245  APPROXIMATELY EQUAL TO (\~= or \cong)
