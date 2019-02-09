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
예전 `nybble`을 정의할 때 언급했듯이, Coq의 생성자(constructor)는 여러 개의 인자를 받을 수 있다.

```Coq
Inductive natprod : Type :=
| pair (n1 n2 : nat).
```

이렇게 정의된 `natprod`에는 오직 하나의 생성규칙만 존재한다.(ex: `pair 3 5`)

이제 몇 가지 함수와 함께 새로운 notation을 정의해보자.

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

이렇게 정의된 notation은 함수 정의에서도 사용할 수 있다.

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

Compute를 사용해 테스트해보자.

```Coq
>> Compute fst (3,5). (* fst2도 동일 *)

   3 : nat
>> Compute snd (3,5). (* snd2도 동일 *)

   5 : nat
```

여기서 `fst2`, `snd2`를 정의할 때 사용한 패턴 매칭은 얼핏 x,y 둘을 매칭하는 다중 매칭처럼 보이지만 실제로는 `pair x y` 하나에 대응되는 **단일 매칭**임에 유의해야 한다. (C++ 의 pair STL 기준으로 _void f(int x, int y)_ 와 _void f(pair<int,int> p)_의 차이라고 이해하면 된다.)



다음으로 이렇게 정의한 `natprod`에 대한 성질들을 알아보자.

```Coq
Theorem surjective_pairing :
 forall (n m : nat), (n,m) = (fst (n,m), snd(n,m)).
Proof.
reflexivity.
Qed.
```

그런데 이걸 (x,y) notation을 사용하지 않고 바로 `natprod`를 이용해 서술하면 `reflexivity`가 인식하지 못한다.

```Coq
Theorem surjective_pairing2 :
  forall (p : natprod), p = (fst p, snd p).
Proof.
reflexivity. (* ERROR *)
Qed.
```

이런 경우 `p : natprod`가 `( (n : nat), (m : nat) )` 형태임을 인식시켜줘야 한다. `destruct`의 구체적인 용법이 여기에서 등장한다.

```Coq
Theorem surjective_pairing2 :
  forall (p : natprod), p = (fst p, snd p).
Proof.
intros p.
destruct p as [n m].
reflexivity.
Qed.
```

`destruct p as [n m].`을 적용하는 순간 subgoal의 `p`가 `(n,m)`으로 바뀌고, `reflexivity`가 적용되는 것을 볼 수 있다. 예전 글에서 `destruct` tactic을 단순히 "경우를 나누는" 용법이라고 설명했는데, 구체적으로는 "가능한 생성규칙별로 경우를 나누고, 인자가 있는 경우 \[ \] 에 제시된 순서대로 대응시키는" 기능이라고 이해할 수 있다. 다시 말해, `natprod`는 유일한 생성규칙이 `pair (n1 n2 : nat)`이었으므로 2개의 인자명(n,m)을 받아 `destruct p as [n m]`이, `nat`의 경우 2개의 생성규칙별로 \[ \](`O`는 0개의 인자)과 \[n'\] (`S (n:nat)`은 1개의 인자)이 되어 전체 `destruct n as [ | n']`이 되는 것이다.



## Lists of Numbers

pair에서 한발 더 나아가, 임의 개수의 원소를 가질 수 있는 list를 만들어보자. 원문의 표현을 빌리면 _"A list is either the empty list or else a pair of a number and another list."_가 된다.

```Coq
Inductive natlist : Type :=
| nil
| cons (n : nat) (l : natlist).
```

