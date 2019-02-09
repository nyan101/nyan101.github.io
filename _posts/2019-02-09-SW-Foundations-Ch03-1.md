---
layout: post
title:  "SW Foundations - Ch03. Working with Structured Data (1) (작성중)"
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

`destruct p as [n m].`을 적용하는 순간 subgoal의 `p`가 `(n,m)`으로 바뀌고, `reflexivity`가 적용되는 것을 볼 수 있다. [이전 글](https://nyan101.github.io/%EC%9E%90%EC%8A%B5/2019/02/03/SW-Foundations-Ch02-2.html)에서 `destruct` tactic을 단순히 "경우를 나누는" 용법이라고 설명했는데, 구체적으로는 "가능한 생성규칙별로 경우를 나누고, 인자가 있는 경우 \[ \] 에 제시된 순서대로 대응시키는" 기능이라고 이해할 수 있다. 다시 말해, natprod는 유일한 생성규칙이 `pair (n1 n2 : nat)`이었으므로 2개의 인자명(n,m)을 받아 `destruct p as [n m]`이, nat의 경우 2개의 생성규칙별로 \[ \](`O`는 0개의 인자)과 \[n'\] (`S (n:nat)`은 1개의 인자)이 되어 전체 `destruct n as [ | n']`이 되는 것이다.



## Lists of Numbers

pair에서 한발 더 나아가, 임의 개수의 원소를 가질 수 있는 list를 만들어보자. 원문의 표현을 빌리면 "_A list is either the empty list or else a pair of a number and another list._"가 된다.

```Coq
Inductive natlist : Type :=
| nil
| cons (n : nat) (l : natlist).
```

