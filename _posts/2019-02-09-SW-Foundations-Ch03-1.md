---
layout: post
title:  "SW Foundations - Ch03. Working with Structured Data (1)"
date:   2019-02-09 15:33:11
author: nyan101
categories: 자습
tags:	Coq
use_math: true
---



본 장에서는 Structured Data, 그중에서도 List에 대해 다룬다.

## Pairs of Numbers
지난번 `nybble`을 정의할 때 언급했듯이, Coq의 생성자(constructor)는 여러 개의 인자를 받을 수 있다.

```Coq
Inductive natprod : Type :=
| pair (n1 n2 : nat).
```

이렇게 정의된 `natprod`에는 오직 하나의 생성규칙만 존재한다.(ex: `pair 3 5`)

이제 몇 가지 함수와 함께 새로운 notation을 정의해보자. `fst`, `snd`는 각각 natprod의 첫 번째, 두 번째 인자를 추출하는 함수가 된다.

```Coq
Definition fst (p : natprod) : nat :=
match p with
| pair x y => x
end.

Definition snd (p : natprod) : nat :=
match p with
| pair x y => y
end.

Notation "( x , y )" := (pair x y).
```

이렇게 정의된 notation은 함수 정의에서도 사용할 수 있다. fst, snd를 (x,y) notation을 사용해 다시 작성해보자.

```Coq
Definition fst2 (p : natprod) : nat :=
match p with
| (x,y) => x
end.

Definition snd2 (p : natprod) : nat :=
match p with
| (x,y) => y
end.
```

작성이 끝나면 Compute를 통해 두 방식 모두 예상대로 잘 동작하는 것을 확인할 수 있다.

```Coq
>> Compute fst (pair 3 5). (* fst2도 동일 *)

   3 : nat
>> Compute snd (3,5). (* snd2도 동일 *)

   5 : nat
```

여기서 `fst2`, `snd2`를 정의할 때 사용한 패턴 매칭은 얼핏 x,y 둘을 매칭하는 다중 매칭처럼 보이지만 실제로는 `pair x y` 하나에 대응되는 **단일 매칭**임에 유의해야 한다. (C++ 의 pair STL 기준으로 _void f(int x, int y)_ 와 _void f(pair<int,int> p)_의 차이라고 이해하면 된다.)



다음으로 natprod를 다루는 간단한 명제에 대한 증명을 시도해보자.

```Coq
Theorem surjective_pairing :
 forall (n m : nat), (n,m) = (fst (n,m), snd(n,m)).
Proof.
reflexivity.
Qed.
```

그런데 정리하고자 하는 명제를 서술할 때 (x,y) notation을 사용하지 않고 바로 natprod를 이용해 작성하면 reflexivity tactic이 이를 인식하지 못한다.

```Coq
Theorem surjective_pairing2 :
  forall (p : natprod), p = (fst p, snd p).
Proof.
reflexivity. (* ERROR *)
Qed.
```

이런 경우 `p : natprod`가 `( (n : nat), (m : nat) )` 형태임을 인식시켜줘야 한다. 이는 destruct tactic을 사용해 해결할 수 있다. 이번 기회에 destruct의 정확한 기능을 알아보자.

```Coq
Theorem surjective_pairing2 :
  forall (p : natprod), p = (fst p, snd p).
Proof.
intros p.
destruct p as [n m].
reflexivity.
Qed.
```

`destruct p as [n m].`을 적용하는 순간 subgoal의 `p`가 `(n,m)`으로 바뀌고, `reflexivity`가 적용되는 것을 볼 수 있다. [이전 글](https://nyan101.github.io/%EC%9E%90%EC%8A%B5/2019/02/03/SW-Foundations-Ch02-2.html)에서 destruct tactic을 단순히 "경우를 나누는" 용법이라고 설명했는데, 구체적으로는 "가능한 생성규칙별로 경우를 나누고, 인자가 있는 경우 \[ \] 에 제시된 순서대로 대응시키는" 기능이라고 이해할 수 있다. 다시 말해, natprod는 유일한 생성규칙이 `pair (n1 n2 : nat)`이었으므로 2개의 인자명(n,m)을 받아 `destruct p as [n m]`이, nat의 경우 2개의 생성규칙별로 \[ \](`O`는 0개의 인자)과 \[n'\] (`S (n:nat)`은 1개의 인자)이 되어 전체 `destruct n as [ | n']`이 되는 것이다.



## Lists of Numbers

pair에서 한발 더 나아가, 임의 개수의 원소를 가질 수 있는 list를 만들어보자. 원문의 표현을 빌리면 "_A list is either the empty list or else a pair of a number and another list._"가 된다.

```Coq
Inductive natlist : Type :=
| nil
| cons (n : nat) (l : natlist).
```

이 생성규칙으로 만들어지는 예를 하나 살펴보자.

```Coq
>> Check (cons 1 (cons 2 (cons 3 nil))).

    : natlist
```

구조는 이해했는데 매번 이렇게 작성하기는 너무 길고 번거롭다. 이를 단순화시킬 수 있도록 새로운 notation을 정의하자.

```Coq
Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
```

다음 Definition들은 모두 동일한 의미를 가진다.

```Coq
Definition mylist1 := (cons 1 (cons 2 (cons 3 (cons 4 nil)))).
Definition mylist2 := 1::(2::(3::(4::nil))).
Definition mylist3 := 1::2::3::4::nil (* 1::2::3::4::[] *).
Definition mylist4 := [1;2;3;4].
Definition mylist5 := 1::[2;3;4].
Definition mylist6 := 1::2::[3;4].
```



## Functions on Lists

그러면 이제 natlist를 다루는 함수를 만들 수 있다. 하스켈 프로그래밍 언어를 사용해봤다면 익숙한 함수들이 몇 보일 것이다.

#### Head & Tail

먼저 pair의 fst, snd와 유사하게 hd(head), tl(tail) 함수를 정의하자. 이때 `hd nil`의 경우 기본값(default)에 해당하는 값을 정의해줘야 함에 유의하자. 여기서는 O을 기본값으로 삼았다.

```Coq
Definition hd (l:natlist) : nat :=
match l with
| nil => O
| h::t => h
end.

Definition tl (l:natlist) : natlist :=
match l with
| nil => nil
| h::t => t
end.
```

#### Repeat

n, count를 받아 count개수 만큼의 n을 원소로 가지는 natlist를 생성한다.

```Coq
Fixpoint repeat (n count : nat) : natlist :=
match count with
| O => nil
| S count' => n :: (repeat n count')
end.
```

```Coq
>> Compute repeat 5 3.

   [5; 5; 5] : natlist
```

#### Length

주어진 리스트의 길이를 계산한다.

```Coq
Fixpoint length (l : natlist) : nat :=
match l with
| nil => O
| h::t => S (length t)
end.
```

```Coq
>> length [1;2;3;4;5].

   5 : nat
```

#### Append

주어진 두 리스트를 연결(concatenate)한다.

```Coq
Fixpoint app (l1 l2 : natlist) : natlist :=
match l1 with
| nil => l2
| h::t => h::(app t l2)
end.
```

```Coq
>> Compute app [1;3;5] [2;4].

   [1; 3; 5; 2; 4] : natlist
```

append는 왠지 쓸모가 많아보인다. infix notation을 추가하자.

```Coq
Notation "x ++ y" := (app x y) (right associativity, at level 60).
```



p.s. 파이썬을 사용해본 입장에서 리스트 더하기가 concatenate 연산인 건 자연스러워도, append함수의 기능을 고려해봤을 때 `app`이라는 이름 대신 `concat` 이 더 자연스러워 보인다. 하지만 Coq에서 제공하는 함수 중 범용 타입(polymorphic) 리스트에 동일한 기능을 제공하는 함수가 `app`이라는 이름으로 존재하므로 통일성을 위해 해당 명칭을 그대로 사용했다.



#### Reverse

주어진 리스트를 뒤집는다.

```Coq
Fixpoint rev (l : natlist) : natlist :=
match l with
| nil => nil
| h::t => rev t ++ [h]
end.
```

```Coq
>> Compute rev [1;2;3;4;5].

   [5; 4; 3; 2; 1] : natlist
```



#### Bag(multiset)

리스트를 이용해 multiset(동일 원소가 여러 개인 경우를 허용하는 집합)을 구현할 수 있다.

```Coq
Definition bag := natlist.
```

연습삼아 주어진 bag 안에 특정 원소가 얼마나 포함되어있는지를 계산하는 `count` 를 작성해보자. 이를 위해 먼저 이전에 작성했던 `is_equal`을 가져오자. 다중 매칭을 이용한 버전을 아래에 다시 작성했다.

```Coq
Fixpoint is_equal (n m : nat) : bool :=
match n, m with
| O, O       => true
| S n', S m' => is_equal n' m'
| _, _       => false
end.

Notation "x =? y" := (is_equal x y) (at level 70).
```

이제 count 함수를 마저 작성하자.

```Coq
Fixpoint count (v:nat) (b:bag) : nat :=
match b with
| nil => O
| h::t => match (v =? h) with
          | true  => S (count v t)
          | false => (count v t)
          end
end.
```

```Coq
>> count 3 [1;2;3;4;5;4;3;2].

   2 : nat
>> count 5 [1;2;3;4].

   O : nat
>> count 2 [2;2;2;2;2].

   5 : nat
```

그런데 count 함수의 정의에서 두 번째 `match...with`을 보면 bool 타입에서 true / false 2가지 경우만을 매칭시킨다. 이런 경우 굳이 match까지 쓸 필요가 있을까? Coq 역시 일반적인 프로그래밍 언어에서와 마찬가지로 `if` 가 존재한다. 이를 이용하면 count 함수는 다음과 같이 다시 쓸 수 있다.

```Coq
Fixpoint count2 (v:nat) (b:bag) : nat :=
match b with
| nil => O
| h::t => if (v =? h) then S (count2 v t)
          else (count2 v t)
end.
```

그런데 true, false는 앞서 `bool` 타입을 정의할 때 만들어준 생성자일뿐 여기에 참/거짓이라는 의미를 덧붙여준 기억은 없다. 사실 굳이 bool이 아니어도 Coq에서는 어떤 Inductive하게 정의된 타입이 2개의 생성자를 가지기만 하면 `if`를 적용할 수 있으며, 이때 if로 제시된 표현식이 첫 번째 생성자와 매칭될 경우 `then` 부분이, 두 번째 생성자와 매칭될 경우 `else` 부분이 계산된다.



이번 글에서는 리스트 타입 `natlist`를 정의하는 방법과 이를 다루는 함수들을 작성해봤다. 다음 글에서는 이런 함수들의 성질에 대해 논증(reasoning)을 진행해보자.