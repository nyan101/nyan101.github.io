---
layout: post
title:  "[Coq 입문] Ch04. Polymorphism & Higher-Order Functions (2)"
date:   2019-02-27 19:47:20
author: nyan101
categories: 자습
tags:	[Coq, Software Foundations]
use_math: true
---



## High-Order Functions

다른 함수를 다룰 수 있는 함수를 고차 함수(higher-order function)라고 한다. 다음 예를 보자.

```Coq
Definition do3times {X:Type} (f:X->X) (a:X) : X := f (f (f a)).
```

```Coq
>> Check @do3times

   : @do3times : forall X : Type, (X -> X) -> X -> X
```

이 `do3times`는 함수 f와 인자 a를 받아 a에 f를 3번 적용한 결과를 돌려준다. 함수를 인자로 제공한다는게 어떤 의미인지 살펴보자

```Coq
>> Definition doubleMe (n:nat) : nat := n+n.

   : doubleMe is defined
>> Compute do3times doubleMe 3.

   : 24 : nat
```



## Filter

이제 좀더 유용한 고차 함수들에 대해 알아보자. filter는 X타입의 리스트(list X)와 원소 X에 대한 판정함수(predicate, \\(f:X\\rightarrow bool\\))를 받아 주어진 predicate를 만족하는(i.e. true를 리턴하는) 원소들만을 남긴다.

```Coq
Fixpoint filter {X:Type} (test:X->bool) (l:list X) : (list X) :=
match l with
| [] => []
| h::t => if test h then h::(filter test t)
                    else (filter test t)
end.
```

```Coq
>> Compute filter evenb [1;2;3;4;5;6].

   : [2; 4; 6] : list nat
```

조금 더 복잡한 predicate에서도 마찬가지로 잘 동작한다.

```Coq
Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.
```

```Coq
 >> filter length_is_1 [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
 
    : [ [3]; [4]; [8] ] : list (list nat).
```

filter를 이용하면 다양한 함수를 쉽게 작성할 수 있다. nat으로 이루어진 리스트에서 짝수의 개수를 세는 함수를 생각해보자. 고차 함수를 사용하지 않는다면 아래처럼 작성될 것이다.

```Coq
Fixpoint count_even (l : list nat) : nat :=
match l with
| [] => O
| h::t => if evenb h then (count_even t) + 1
                     else (count_even t)
end.
```

그런데 filter를 이용하면 동일한 내용을 다음과 같이 간결한 형태로 작성할 수 있다.

```Coq
Definition count_even' (l:list nat) : nat := length (filter evenb l).
```

Compute를 통해 확인해보자

```Coq
>> Compute count_even [1;2;3;4;5;6].

   : 3 : nat
>> Compute count_even' [1;2;3;4;5;6].

   : 3 : nat
```



## Anonymous Functions

앞서 filter를 테스트할 때 `length_is_1`이라는 함수를 작성했다. 그런데 이렇게 한번 쓰고 말 함수를 위해 따로 정의를 작성하고 이름을 붙이는 건 조금 낭비라는 생각이 든다. 이렇게 단순한 내용이면 즉석에서 바로 만들어서 써도 되지 않을까? 다른 많은 함수형 언어들과 마찬가지로 Coq도 람다식(lambda expression)을 지원한다.

```Coq
>> Compute do3times (fun n => n*n) 2.

   : 256 : nat
```

위 코드에서 `(fun n => n*n)`은 "n을 받아 n*n을 반환하는 함수"를 의미한다. 이를 이용하면 앞서 작성한 `length_is_1`예제를 다음과 같이 다시 쓸 수 있다.

```Coq
>> filter (fun l ⇒ (length l) =? 1) [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ].

   : [ [3]; [4]; [8] ] : list (list nat)
```



## Map