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

이어서 증명을 진행해도 되지만, Coq에서는 각 subgoal에 대한 증명임을 명확히 하기 위해 보조 마크를 사용할 수 있다 (LaTeX의 itemize를 생각하면 된다). 이번 경우 각 subgoal은 `reflexivity.`로 바로 증명이 끝난다.

```Coq
Theorem O_cannot_be_n_1 : forall n:nat, n+1 =? 0 = false.
intros n.
simpl.
destruct n as [ | n'] eqn:E.
- reflexivity.
- reflexivity.
Qed.
```

처음 -를 수행하면 subgoal 창에 나타난 목표가 하나로 한정되는 것을 볼 수 있다. -나 +, \*같은 bullet이 일종의 scope 한정자 역할을 하는 셈이다.

여기서 `as [ | n']`은 n을 경우에 따라 나누면서 만들어지는 새로운 변수에 이름을 제공하기 위해 사용했다 (`O`는 새로운 변수가 필요하지 않지만 `S xxx` 의 경우는 `xxx` 자리에 사용할 새로운 변수가 필요). as를 사용하지 않아도 Coq에서 자동으로 이름을 제공하지만, 의미를 명확히 하기 위해 가능하면 직접 이름을 제시하는 것이 좋다.

마찬가지로 `eqn:E` 역시 추가적인 가독성을 제공한다. 조금 전 `n`을 경우에 따라 나누었지만 그게 `n = O`인 경우와, `n = S n'`인 2가지라는 사실을 알기 위해서는 (디테일을 기억하고 있지 않다면) `nat`의 정의까지 다시 올라가야 한다.`destruct` tactic을 사용할 때 `eqn:(name)`을 덧붙이면 각 경우를 가정으로 표기해 현재 다루고 있는 subgoal이 어떤 경우에 해당하는지를 조금 더 친절하게 알려준다. 각 경우를 처리할 때 subgoals 창에 나타난 메시지를 보면 이를 좀더 잘 이해할 수 있다.


<table>
<tr>
<td>
<pre><code class="language-Coq">1 subgoal
n : nat
E : n = 0
______________________________________(1/1)
(0 + 1 =? 0) = false
</code></pre>
</td>
<td>
<pre><code class="language-Coq">1 subgoal
n, n' : nat
E : n = S n'
______________________________________(1/1)
(S n' + 1 =? 0) = false
</code></pre>
</td>
</tr>
</table>
<hr>

scope의 활용을 좀더 이해하기 위해 다른 예제를 살펴보자. 

```Coq
Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b. eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.
```

중첩이 조금 더 깊게(nested) 이루어지는 상황을 대비해 \{, \}을 사용해서도 scope 표기가 가능하다.

```Coq
Theorem andb_commutative' : ∀b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
Qed.
```

