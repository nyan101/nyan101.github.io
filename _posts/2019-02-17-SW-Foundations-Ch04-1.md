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

기존 natlist와 거의 유사하지만 한 가지가 더 추가됐다. 이렇게 정의한 list는 단일 타입보다는 **Type에서 Inductive 정의(Type)로 가는 함수**로 작용한다. 임의의 타입 X에 대해 `list X`는 타입X의 원소를 요소로 가지는 리스트에 대한 inductive한 정의가 된다.

```Coq
>> Check list.

   list : Type -> Type
```

list 정의에서 등장한 인자 X는 자동적으로 nil, cons의 인자가 된다. 다시 말해, nil과 cons는 _다형 생성자(polymorphic constructor)_가 되며, 생성규칙을 통해 요소를 만들 때 타입 X를 인자로 포함시켜줘야 한다. 예시를 통해 살펴보자.

```Coq
>> Check (nil nat).

   nil nat : list nat
>> Check (cons nat 3 (nil nat)).

   cons nat 3 (nil nat) : list nat
```

그러면 `nil nat`이 아닌 그냥 `nil`은 어떤 타입이라고 할 수 있을까? 정의상으로는 `list X` 타입이어야 하지만 여기선 타입 X를 지정(bind)하지 않았다. 따라서 단순히 \\(Type \\rightarrow list\\,X\\) 라고 하기에도 무리가 있다. 굳이 표현하자면 \\((X\\,:\\,Type) \\rightarrow list\\,X\\) 정도가 그나마 가까울 것이다. Coq에서는 이런 경우를 설명하기 위해 \\(\\forall X\\,:\\,Type, \\,\\,list\\,X\\)라는 표현을 사용한다.

```Coq
>> Check nil.

   nil : forall X : Type, list X
```

마찬가지로 `cons`의 타입 역시 비슷하게 나타난다.

```Coq
>> Check cons.

   cons : forall X : Type, X -> list X -> list X
```

같은 방법을 통해 기존에 만들었던 함수들을 다시 polymorphic 버전으로 작성할 수 있다.

```Coq
Fixpoint repeat (X:Type) (x:X) (count:nat) : list X :=
match count with
| O => nil X
| S count' => cons X x (repeat X x count')
end.
```

```Coq
>> Compute repeat nat 5 3.

   cons nat 5 (cons nat 5 (cons nat 5 (nil nat)))
    : list nat
```

#### Type Annotation Inference

이번에는 위와 동일한 코드에서 인자에 대한 타입 정보를 빼고 작성해보자.

```Coq
Fixpoint repeat_noType X x count : list X :=
match count with
| O => nil X
| S count' => cons X x (repeat_noType X x count')
end.
```

그런데 `repeat_noType`과 앞서 작성했던 `repeat`을 비교하면 동일한 것을 확인할 수 있다.

```Coq
>> Check repeat.

   forall X : Type, X -> nat -> list X
>> Check repeat_noType.

   forall X : Type, X -> nat -> list X
>> Compute repeat_noType nat 4 2.

   cons nat 4 (cons nat 4 (nil nat)) : list nat
```

Coq는 명시적으로 지정되지 않은 타입들에 대해 _타입 추론(Type Inference)_을 수행한다. repeat\_noType에서 X는 cons의 첫 번째 인자로 들어갔으므로 Type이어야 하고, O나 S 생성자로부터 count가 nat타입임을 추론해내는 것이다. 이런 기능 덕에 굳이 명시적으로 타입을 지정할 필요성은 없지만, 코드 이해를 돕기 위해 일부 핵심적인 인자에는 타입을 표기하는 편이 권장된다.

#### Type Argument Synthesis

todo