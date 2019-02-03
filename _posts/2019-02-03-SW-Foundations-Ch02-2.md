---
layout: post
title:  "SW Foundations - Ch02. Proof by tactics (2)"
date:   2019-02-03 22:16:28
author: nyan101
categories: 자습
tags:	Coq
use_math: true
---



## Proof by Case Analysis
simpl이나 rewriting만으로는 충분하지 않은 경우가 있다. [예전 글](https://nyan101.github.io/%EC%9E%90%EC%8A%B5/2019/01/31/SW-Foundations-Ch01-2.html)에서 정의했던 `is_equal`에 새 Notation을 정의하자.

```Coq
Fixpoint is_equal (n m : nat) : bool :=
match n with
| O => match m with
       | O => true
       | S m' => false
       end
| S n' => match m with
          | O => false
          | S m' => is_equal n' m'
          end
end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
```



이제 다음 두 명제를 생각해보자. 

* \\( \\forall n : nat, 1+n \\neq 0 \\)
* \\( \\forall n : nat, n+1 \\neq 0 \\)



먼저 1+n은 plus와 notation의 정의로부터 `S n`으로 simplified될 수 있고, 이를 이용하면 위의 명제는 `simpl.` 로 증명이 끝난다.

```Coq
Theorem O_cannot_be_1_n : forall n:nat, (1+n =? 0) = false.
Proof.
intros n.
simpl.
reflexivity.
Qed.
```

하지만 `n+1`은 `simpl.`을 시도해도 아무런 변화가 일어나지 않는다. 그런데 `reflexivity.`를 적용하(려고 시도하)면 _Unable to unify "false" with "n + 1 =? 0"_ 라는 오류를 볼 수 있다. `1+n`과 달리 `n+1`은 n이 `O`인지 `S n'` 형태인지에 따라 결과값이 달라지기 때문에 Coq가 한번에 처리할 수 있는 역량을 벗어난다. 그렇다면 **경우를 나누어서** 처리해보자. `destruct` tactic이 그 역할을 담당한다.

```Coq
Theorem O_cannot_be_n_1 : forall n:nat, n+1 =? 0 = false.
intros n.
simpl.
destruct n.
```

여기까지 적용했다면 각 경우가 나뉘어지면서 2개의 subgoal이 나타난다.

```Coq
2 subgoals
______________________________________(1/2)
(0 + 1 =? 0) = false
______________________________________(2/2)
(S n + 1 =? 0) = false
```








 있다.

<img src="/assets/images/2019/02/SWF-02-1-Subgoal.png" width="800px">


