---
layout: post
title:  "SW Foundations - Ch01. Functional Programming in Coq (1)"
date:   2019-01-29 00:47:23
author: nyan101
categories: 자습
tags:	Coq
use_math: true
---



## Introduction

여기서는 Coq에서 사용되는 Galina라는 functional programming language의 기초적인 사용법과, Coq에서 증명에 실제 활용되는 기초적인 tactic에 대해 다룬다.

## Data and Functions

### Days of the Week

먼저 Coq에서 타입을 선언하는 법을 알아보자. 모든 Coq 구문은 .(마침표)로 끝남에 유의하자

```Coq
Inductive day : Type :=
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday
| sunday.
```

day 타입에는 monday, tuesday 등의 원소가 있다. 편의상 원소라는 용어를 사용하지만 엄밀히 말해 '원소'라는 표현보단는 '인자 0개를 가지는 생성자'로 이해하는 편이 좋다.

이제 day 타입을 다루는 함수를 하나 정의하자

```Coq
Definition next_weekday (d:day) : day :=
match d with
| monday => tuesday
| tuesday => wednesday
| wednesday => thursday
| thursday => friday
| friday => monday
| saturday => monday
| sunday => monday
end.
```

`next_weekday` 함수는 day 타입의 인자 `d`를 받아 day 타입을 반환한다.  `Compute` 를 통해 함수를 실행시켜볼 수 있다.

<img src="/assets/images/2019/01/SWF-01-CoqIDE.png" width="700px">

공간상의 문제로 앞으로는 간단히 아래처럼 표기하자. \>\> 가 있는 줄은 입력. 빈 줄 이후에 이어지는 내용은 그에 대한 출력을 의미한다.

```
>> Compute (next_weekday (next_weekday friday)).
  
  = tuesday
    : day
```



`Example` 키워드로 함수의 동작 예시에 이름을 붙여 기록할 수 있다.

```Coq
Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
```

Example도 증명이 필요하다. 아래쪽에 다음을 추가해 `test_next_weekday`에 대한 증명을 추가할 수 있다.

```
Proof. simpl. reflexivity. Qed.
```

`Proof`, `Qed`, `simpl` 등 키워드에 대해서는 다시 설명하겠지만 잠시 [과거의 잔재](https://nyan101.github.io/%EC%A0%84%EC%82%B0/2018/01/08/Coq-02-mynat.html)를 통해 어떻게 동작하는지 감을 잡을 수 있다.



### Booleans

앞서 `day` 타입을 정의한 것과 유사하게, 이번엔 `bool` 타입을 정의해보자. 상식을 거스르지 않고 이번에 만들 bool 타입도 2개의 원소를 가진다.

```Coq
Inductive bool : Type :=
| true
| false.
```

`day` 때와 비슷하게 함수를 정의할 수 있다. 2변수 함수를 정의하는 부분에 유의해서 살펴보자. (`orb`는 `andb`와 거의 동일하므로 생략)

```Coq
Definition negb (b:bool) : bool :=
match b with
| true => false
| false => true
end.

Definition andb (b1:bool) (b2:bool) : bool :=
match b1 with
| true => b2
| false => false
end.
```

Coq에서는 Notation 키워드를 통해 함수에 새로운 표기를 추가할 수 있다.

```Coq
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
```

그러면 추가된 표기를 이용한 표현이 가능하다.

```
>> Compute (true || (false && true)).

  true : bool
```



### Types

모든 expression은 타입을 가지고 있다. Check 키워드를 통해 기존에 만든 원소들의 타입을 확인해보자.

```Coq
>> Check true.

  true : bool
>> Check andb.

  andb : bool -> bool -> bool
```



### New Types from Old

기존에 정의된 타입을 이용해 새로운 타입을 정의할 수 있다. '생성자(constructor)'라는 용어를 염두에 두고 아래 정의를 살펴보자.

```Coq
Inductive rgb : Type :=
| red
| green
| blue.

Inductive color : Type :=
| black
| white
| primary (p : rgb).
```

`red`, `green`, `blue`는 rgb타입의 원소이고, `black`, `white`는 color타입의 원소가 된다. 또한 `primary red`는 color 타입의 원소가 된다. 마찬가지로 `primary green`, `primary blue`는 color 타입이 되지만, `primary true`는 color 타입이 아니다. 

이렇게 만들어진 타입에 대해서도 함수를 정의할 수 있으며, 하스켈과 유사하게 \_를 더미(dummy)로 하는 패턴 매칭을 사용할 수 있다.

```Coq
Definition isred (c:color) : bool :=
match c with
| black => false
| white => false
| primary red => true
| primary _ => false
end.
```

`isred`가 `color -> bool`인 함수이므로 `(isred red)`는 올바른 expression이 아님에 주의하자.(단, `(isred (primary red))`는 올바른 expression)



### Tuples

한 constructor가 여러 인자를 가질 수도, 패턴 매칭에서 여러 인자를 한번에 매칭시킬 수도 있다.

```Coq
Inductive bit : Type :=
| B0
| B1.

Inductive nybble : Type :=
| bits (b0 b1 b2 b3 : bit).

Definition all_zero (nb:nybble) : bool :=
match nb with
| (bits B0 B0 B0 B0) => true
| (bits _ _ _ _) => false
end.
```

`Check`, `Compute`를 통해 생각한 대로 동작하는지 확인해보자.



### Modules

지금까지 작성한 모든 코드는 전역(global scope)에 속한다. 단순히 예제를 따라해보는 거라면 몰라도 코드가 복잡해질수록 모든 걸 전역으로 두는 대신, 영역을 나눠야 할 필요성이 커진다. 자바의 패키지, C++의 네임스페이스처럼 Coq에서는 모듈을 제공한다.

```Coq
Module XXX.
(* code *)
End XXX.
```

이렇게 모듈 내부에 정의된 요소들은 모듈 바깥에서 `XXX.Y` 로 불러올 수 있다.