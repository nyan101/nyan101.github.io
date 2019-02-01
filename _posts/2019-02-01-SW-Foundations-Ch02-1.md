---
layout: post
title:  "SW Foundations - Ch02. Proof by ..."
date:   2019-02-01 20:15:17
author: nyan101
categories: 자습
tags:	Coq
use_math: true
---



이제 Coq를 이용해 간단한 증명을 직접 작성해보자.

## Notation
본론을 시작하기에 앞서 전에 만들었던 `plus`, `mult` 에  infix notation을 정의하자.

```Coq
Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.
```

이전에 `bool`에 대해 `x && y` 를 정의하던 때보다 뭔가 이것저것 늘어났다. prefix, postfix notation과는 달리 infix notation에서는 모호한(ambiguous) 문장이 생길 수 있다. 일반적으로 `x+y*z`라는 표현식을 쓸 때 우리는 `(x+y)*z`가 아닌 `x+(y*z)`를 의도한다. 위 코드에서의 역할을 간단히 요약하면

* level (0 ~ 100 사이의 정수)
  : `x+y`의 level이 50, `x*y`의 level이 40으로, `x+y*z`가 `x+(y*z)`로 해석되도록 한다.
* associativity (left associativity)
  : `x+y+z`가 `x+(y+z)`가 아닌 `(x+y)+z`로 해석되도록 한다.

가 된다. ~~사실 여기까지는 Coq에 이미 정의되어 있으므로 굳이 새로 타이핑할 필요는 없다~~



## Proof by simplification

이제 Coq로 수학적 정리를 표현해보자. Coq에서 정리는 다음 형태를 가진다. (`Theorem`, `Lemma`, `Corollary`, `Example` 모두 동일한 형태인데 이것들이 어떻게 다른지는 아직 잘 모르겠다.)

```Coq
Theorem (name) : (statement).
Proof.
(tactics)
Qed.
```

그럼 앞서 정의된(혹은 이미 Coq에 정의되어 있는) `nat` 타입에 대해 다음 문장을 생각해보자

> O은 `nat`에서 덧셈에 대한 왼쪽 항등원이다. (i.e. \\( \\forall n:nat, 0+n=n \\) )

참고를 위해 `plus`의 정의를 다시 가져왔다.

```Coq
Fixpoint plus (n m : nat) :=
match n with
| O => m
| S n' => S (plus n' m)
end.
```

먼저 증명하고자 하는 명제를 서술하자. 이름은 `plus_0_n`으로 지었다.

```Coq
Theorem plus_0_n : forall n:nat, 0 + n = n.
```

다음으로 증명 시작을 나타내는 `Proof`를 쓴다.

```Coq
Proof.
```

그럼 (CoqIDE 기준) 오른쪽 위에 subgoal이 나타난 것을 확인할 수 있다.

<img src="/assets/images/2019/02/SWF-02-1-Subgoal.png" width="800px">



subgoal에서 `n` 앞에 `forall` 한정자(quantifier)가 붙어있다. 종이에 펜으로 증명을 시작할 때와 마찬가지로 "어떤 자연수 n에 대해" 를 쓰면서 forall을 떼놓고 생각하자. Coq에서는 `intros` tactic이 그 역할을 수행한다.

```Coq
intros n.
```

subgoal이 어떻게 변했는지 살펴보자. 이제 simplification을 적용할 수 있다. `simpl.` 을 적용하면 subgoal 창은 다음과 같이 변한다.



(`simpl.` 적용 이전)

```Coq
1 subgoal
n : nat
______________________________________(1/1)
0 + n = n
```

(`simpl.` 적용 이후)

```Coq
1 subgoal
n : nat
______________________________________(1/1)
n = n
```

등호 왼쪽이 바뀌었다. Coq에서 `0 + n`, 다시 말해 `plus O n`을 인식하고 `plus`의 정의에 따라 이를 `n`으로 단순화시킨 것이다. (`plus n m`에서 `n`이 `O`이면 `match...with` 에 따라 결과는 `m`이 된다. 정의를 다시 살펴보자)



마지막으로 ~~`n=n` 정도는 맞다고 자동으로 넘어가줘도 될거같지만~~ `reflexivity.`를 이용하자. 그러면 `n=n`임이 받아들여지면서 _"No more subgoals."_ 라는 메시지를 볼 수 있다. 이제 `Qed.`를 통해 증명을 끝낼 수 있다.



<img src="/assets/images/2019/02/SWF-02-1-Qed.png" width="800px">



그런데 위 코드에서 `simpl.`을 지워도 Coq는 정상적으로 동작하고 `plus_0_n`이 증명되었음을 받아들인다. 사실 `reflexivity.`는 `simpl.`과 유사한 방식으로 치환을 수행할 수 있으며, 실제로 `simpl.`보다 조금 더 넓은 범위를 수행한다. 그런데 왜 굳이 `simpl.`을 썼을까?



이는 두 tactic의 목적 차이에서 나온다. `reflexivity`는 주로 `a=b` 형태의 subgoal을 만족시키는 데 사용하고, 치환/확장을 수행해 양변이 일치하면 subgoal을 달성시킨다. 반면 `simpl.`은 subgoal 자체를 달성시키려는 기능은 없이, 사용자의 이해를 돕는 선까지만 치환/확장을 수행한다고 보면 된다.