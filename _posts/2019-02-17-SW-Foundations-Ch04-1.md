---
layout: post
title:  "[Coq 입문] Ch04. Polymorphism & Higher-Order Functions (1) (작성중)"
date:   2019-02-17 22:22:37
author: nyan101
categories: 자습
tags:	[Coq, Software Foundations]
use_math: true
---



## Polymorphic Lists
이전 장에서 natlist, 다시 말해 nat으로 이루어진 리스트에 대해 다뤘다. 마찬가지 방법으로 문자열 리스트, bool 리스트, 리스트의 리스트 등 다양한 리스트를 정의할 수 있다. 예를 들어 bool 리스트는

```Coq
Inductive boollist : Type :=
| bool_nil
| bool_cons (b : bool) (l : boollist).
```

로 정의된다. 

그런데 매번 새로운 타입의 리스트가 필요할 때마다 (거의) 동일한 정의를 다시 써주는 건 낭비일 것이다. 새로운 타입에 맞게 정의를 다시 쓴다는 말은 단순히 `nil`이나 `cons`의 문제가 아니라, length, reverse, append 등 앞서 natlist에서 정의했던 모든 함수를 전부 새로 작성해야 한다는 의미가 된다. 이런 불필요한 중복을 피하기 위해 Coq에서는 _다형적(polymorphic)_ 타입을 지원한다. 

```Coq
Inductive list (X : Type) : Type :=
| nil
| cons (x : X) (l : list X).
```

기존 natlist와 거의 유사하지만 한 가지가 더 추가됐다. 이렇게 정의한 list는 단순한 타입보다는 **Type에서 Inductive 정의(Type)로 가는 함수**로 작용한다. 임의의 타입 X에 대해 `list X`는 타입X의 원소를 요소로 가지는 리스트에 대한 inductive한 정의가 된다.

```Coq
>> Check list.

   list : Type -> Type
```

list 정의에서 등장한 인자 X는 