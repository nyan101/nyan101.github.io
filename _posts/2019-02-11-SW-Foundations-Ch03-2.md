---
layout: post
title:  "SW Foundations - Ch03. Working with Structured Data (2) (작성중)"
date:   2019-02-11 22:01:56
author: nyan101
categories: 자습
tags:	Coq
use_math: true
---



## Reasoning About Lists

리스트에 대한 간단한 정리를 증명해보자.

```Coq
Theorem nil_app : forall l:natlist, [] ++ l = l.
Proof.
reflexivity.
Qed.
```

대상이 natlist라는 점만 제외하면 이전의 `forall n:nat, 0+n=n`과 같은 형태이다. 마찬가지로 natlist도 `destruct`를 통해 생성규칙에 따라 경우를 나눌 수 있다.

```Coq
Theorem tl_length_pred :
 forall l:natlist, pred (length l) = length (tl l).
Proof.
intros l.
destruct l as [| n l'] eqn:E.
- (* l = [] *)
  reflexivity.
- (* l = n::l' *)
  reflexivity.
```

마찬가지로 수학적 귀납법(induction tactic) 역시 적용 가능하다. nat에서의 귀납법과 마찬가지로 base step과 induction step으로 이루어져 있으며, 각각

* base step : `l = []`인 경우, nat에서 `n = 0`인 경우에 해당한다.
* induction step : `l = n :: l'`인 경우, nat에서 `n = S n'`인 경우에 해당한다.

이때 `n::l'`, 다시 말해 `cons n l'`은 2개의 인자를 받는다는 점에 유의하자. 예시를 통해 natlist에서의 induction이 어떻게 이루어지는지 살펴보자.

```Coq
Theorem app_assoc :
  forall (l1 l2 l3 : natlist), (l1++l2)++l3 = l1++(l2++l3).
Proof.
intros l1 l2 l3.
induction l1 as [| n l1' IH1].
- (* l1 = [] *)
  reflexivity.
- (* l1 = n :: l1' *)
  simpl.
  rewrite -> IH1.
  reflexivity.
Qed.
```

