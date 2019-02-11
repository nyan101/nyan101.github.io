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

대상이 natlist라는 점만 제외하면 이전의 `forall n:nat, 0+n=n`과 같은 형태이다. nat에서와 마찬가지로 natlist도 `destruct`를 통해 생성규칙에 따라 경우를 나눌 수 있다.

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

nat에서와 거의 동일한 방식으로 증명이 끝났다. 그러면 이제 그렇지 않은 경우를 통해 Coq를 어떤 식으로 사용하는지 감을 잡아보자.

이전 글에서 natlist를 뒤집어주는 `rev`함수를 정의했다. 편의를 위해 아래에 코드를 다시 가져왔다.

```Coq
Fixpoint rev (l : natlist) : natlist :=
match l with
| nil => nil
| h::t => rev t ++ [h]
end.
```

증명하고자 하는 정리(성질)는 다음과 같다.

\\( \\forall l:natlist,\\,length\\,(rev\\,l) = length\\,l \\)

그런데 지금까지 배운 것들을 이용해 증명을 시도하면 도중에 막히는 부분을 마주하게 된다.
```Coq
Theorem rev_length : forall l:natlist, length (rev l) = length l.
Proof.
intros l.
induction l as [| n l' IH].
- (* l = [] *)
  reflexivity.
- (* l = n :: l' *)
  simpl.
  rewrite <- IH.
  Abort.
```

이 시점의 subgoal을 살펴보자.

```Coq
1 subgoal
n : nat
l' : natlist
IH : length (rev l') = length l'
______________________________________(1/1)
length (rev l' ++ [n]) = S (length (rev l'))
```

이 subgoal을 해결하기 위해서는 length 와 `++` 연산(app) 사이의 연관관계를 이용할 수 있어야 한다. 그런데 현재로서는 이에 대해 별다른 유의미한 성질을 가지고 있지 않다. 그렇다면 유의미한 성질을 찾아 증명을 추가하자.

직관적으로 다음 성질을 생각해 볼 수 있다. 증명은 induction을 이용하면 비교적 간단하게 진행할 수 있다.

```Coq
Theorem app_length :
  forall (l1 l2 : natlist), length(l1 ++ l2) = (length l1) + (length l2).
Proof.
intros l1 l2.
induction l1 as [| n l1'].
- (* l1 = [] *)
  reflexivity.
- (* l1 = n::l1' *)
  simpl.
  rewrite -> IHl1'.
  reflexivity.
Qed.
```

