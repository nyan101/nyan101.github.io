---
layout: post
title:  "[Coq 입문] Ch04. Polymorphism & Higher-Order Functions (1)"
date:   2019-02-17 22:22:37
author: nyan101
categories: 자습
tags:	[Coq, Software Foundations]
use_math: true
---



## Polymorphic Lists
이전 장에서 natlist, 다시 말해 nat으로 이루어진 리스트에 대해 다뤘다. 마찬가지 방법으로 문자열 리스트, bool 리스트, 리스트의 리스트 등 다양한 리스트를 정의할 수 있다. 예를 들어 bool 리스트는

```coq
Inductive boollist : Type :=
| bool_nil
| bool_cons (b : bool) (l : boollist).
```

로 정의된다. 

그런데 매번 새로운 타입의 리스트가 필요할 때마다 (거의) 동일한 정의를 다시 써주는 건 낭비일 것이다. 새로운 타입에 맞게 정의를 다시 쓴다는 말은 단순히 `nil`이나 `cons`의 문제가 아니라, length, reverse, append 등 앞서 natlist에서 정의했던 모든 함수를 전부 새로 작성해야 한다는 의미가 된다. 이런 불필요한 중복을 피하기 위해 Coq에서는 _다형적(polymorphic)_ 타입을 지원한다. 

```coq
Inductive list (X : Type) : Type :=
| nil
| cons (x : X) (l : list X).
```

기존 natlist와 거의 유사하지만 한 가지가 더 추가됐다. 이렇게 정의한 list는 단일 타입보다는 **Type에서 Inductive 정의(Type)로 가는 함수**로 작용한다. 임의의 타입 X에 대해 `list X`는 타입X의 원소를 요소로 가지는 리스트에 대한 inductive한 정의가 된다.

```coq
>> Check list.

   list : Type -> Type
```

list 정의에서 등장한 인자 X는 자동적으로 nil, cons의 인자가 된다. 다시 말해, nil과 cons는 _다형 생성자(polymorphic constructor)_가 되며, 생성규칙을 통해 요소를 만들 때 타입 X를 인자로 포함시켜줘야 한다. 예시를 통해 살펴보자.

```coq
>> Check (nil nat).

   nil nat : list nat
>> Check (cons nat 3 (nil nat)).

   cons nat 3 (nil nat) : list nat
```

그러면 `nil nat`이 아닌 그냥 `nil`은 어떤 타입이라고 할 수 있을까? 정의상으로는 `list X` 타입이어야 하지만 여기선 타입 X를 지정(bind)하지 않았다. 따라서 단순히 \\(Type \\rightarrow list\\,X\\) 라고 하기에도 무리가 있다. 굳이 표현하자면 \\((X\\,:\\,Type) \\rightarrow list\\,X\\) 정도가 그나마 가까울 것이다. Coq에서는 이런 경우를 설명하기 위해 \\(\\forall X\\,:\\,Type, \\,\\,list\\,X\\)라는 표현을 사용한다.

```coq
>> Check nil.

   nil : forall X : Type, list X
```

마찬가지로 `cons`의 타입 역시 비슷하게 나타난다.

```coq
>> Check cons.

   cons : forall X : Type, X -> list X -> list X
```

같은 방법을 통해 기존에 만들었던 함수들을 다시 polymorphic 버전으로 작성할 수 있다.

```coq
Fixpoint repeat (X:Type) (x:X) (count:nat) : list X :=
match count with
| O => nil X
| S count' => cons X x (repeat X x count')
end.
```

```coq
>> Compute repeat nat 5 3.

   cons nat 5 (cons nat 5 (cons nat 5 (nil nat)))
    : list nat
```

#### Type Annotation Inference

이번에는 위와 동일한 코드를 인자에 대한 타입 정보만 빼고 다시 작성해보자.

```coq
Fixpoint repeat_noType X x count : list X :=
match count with
| O => nil X
| S count' => cons X x (repeat_noType X x count')
end.
```

그런데 `repeat_noType`과 앞서 작성했던 `repeat`을 비교하면 동일하게 나타난다.

```coq
>> Check repeat.

   forall X : Type, X -> nat -> list X
>> Check repeat_noType.

   forall X : Type, X -> nat -> list X
>> Compute repeat_noType nat 4 2.

   cons nat 4 (cons nat 4 (nil nat)) : list nat
```

Coq는 명시적으로 지정되지 않은 타입들에 대해 _타입 추론(Type Inference)_을 수행한다. repeat\_noType에서 X는 cons의 첫 번째 인자로 들어갔으므로 Type이어야 하고, O나 S 생성자로부터 count가 nat타입임을 추론해내는 것이다. 이런 기능 덕에 굳이 명시적으로 타입을 지정할 필요성은 없지만, 코드 이해를 돕기 위해 일부 핵심적인 인자에는 타입을 표기하는 편이 권장된다.

#### Type Argument Synthesis

앞서 굳이 타입을 명시하지 않아도 앞뒤 문맥을 통해 각각이 어떤 타입인지를 추론해낼 수 있었다. 마찬가지 추론을 조금 다른 시각에서 사용해보자. 모든 인자를 전부 명시하는 대신 **\_**를 사용해 표현하는 것이다. Coq는 "\_"를 만나면 해당 시점에서 가능한 모든 정보들을 활용해 그 공백을 채우려 시도한다. 다시 말해 앞뒤 문맥으로부터 공백( \_ )에 들어갈 대상이 명백한 경우 단순히 **\_**로 표현할 수 있는 것이다. 다음 예시를 살펴보자

```coq
Fixpoint repeat2 X x count : list X :=
match count with
| 0 => nil _
| S count' => cons _ x (repeat2 _ x count')
end.
```

위 정의의 `nil _`나 `cons _ x (...)`에서 공백을 채워보자. `repeat_`는 list X 타입을 반환해야 하므로 nil의 인자로는 X (: Type) 밖에 들어갈 수 없고, 같은 이유로 cons에 붙은 \_도 마찬가지로 채울 수 있다.

물론 여기까지만 해서는 딱히 줄어든 느낌이 나지 않는다. X가 \_로 대체되었을 뿐 같은 1글자이므로 타이핑 수에 있어서는 별다른 차이가 없는 것은 사실이다. 그렇다면 가독성을 비교해보자.

```coq
Definition list123  := cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

Definition list123_ := cons _ 1 (cons _ 2 (cons _ 3 (nil _))).
```

~~힘의 차이가 느껴지십니까~~ 형식적인 인자(nat)가 사라진 아래쪽에서는 좀더 내용 파악이 손쉬워진 것을 확인할 수 있다.

#### Implicit Arguments

여기서 더 나아나서, \_로나마 표현하는 대신 아예 생략해버리는 것 또한 가능하다. Coq의 `Arguments` 명령어(directives) 뒤에 함수의 이름과 그 인자를 나열하고, 이때 implicit하게 만들고 싶은 인자들을 **{, }** 로 둘러싸면 된다. 마찬가지로 이 경우에도 인자 이름 대신 \_를 사용할 수 있다.

```coq
Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.
```

Compute를 통해 확인해보자.

```coq
>> Compute cons 1 (cons 2 (cons 3 nil)).

   : cons 1 (cons 2 (cons 3 nil)) : list nat

>> Compute repeat 5 3.

   :  cons 5 (cons 5 (cons 5 nil)) : list nat
```

혹은 함수를 정의하는 단계에서부터 인자를 implicit하게 만들 수도 있다.

```coq
Fixpoint repeat3 {X : Type} (x : X) (count : nat) : list X :=
match count with
| 0 => nil
| S count' => cons x (repeat3 x count')
end.
```

그런데 이를 타입 정의에 사용할 때는 주의해야 한다. 이 글 처음에 정의했던 list 타입(polymorphic list)을 다음과 같이 정의했다고 해보자.

```coq
Inductive list' {X:Type} : Type :=
| nil'
| cons' (x : X) (l : list').
```

인자로 들어가는 X를 implicit하게 정의했기 때문에 이후 list와 관여된 모든 서술을 `list nat`, `list bool`처럼 특정하지 않고 `list`로 일반화해야 한다. polymorphic type에 대한 일반적인 서술이 이론적으로 불가능한 것은 아니지만 대부분의 경우 굉장히 먼 길을 돌아가야 하고 그만큼 핵심을 벗어나기 쉽다.

#### Supplying Type Arguments Explicitly

앞서 아무 인자나 implicit하게 만드는 것이 어떻게 위험할 수 있는지 설명했다. 그렇다면 모든 인자를 explicit하게 유지해야만 할까? 인자를 implicit하게 만드는 법이 있다면 반대로 implicit하게 된 인자를 다시 explicit하게 명시할 수 있는 방법이 존재해야 하지 않을까? 결론부터 말하자면 그렇다.

다음 문장을 실행하려고 시도해보자. Coq는 이에 대해 implicit 인자 X를 추론할 수 없다는 에러를 내뱉는다.

```coq
>> Definition mynil := nil.

   : (ERR) Cannot infer the implicit parameter X of nil whose type is "Type".
```

이를 해결하기 위해 Coq가 타입 X를 추론할 수 있도록 힌트를 제공할 수 있다.

```coq
>> Definition mynil : list nat := nil.
```

이는 완곡어법이라고 생각할 수도 있다. 조금 더 직접적인 방법을 알아보자. Coq에서는 이미 일부 인자가 implicit화 된 `nil`의 explicit 버전(모든 인자를 명시적으로 제공해야 함)을 `@nil`이라는 이름으로 사용할 수 있다.

```coq
>> Definition mynil' = @nil nat.
```

@는 repeat이나 cons 등에도 마찬가지로 적용할 수 있다. `Check nil`과 `Check @nil`을 통해 둘이 어떻게 다른지 감을 잡아보자.

이렇게 list nat에서 작성했던 함수들을 다시 polymorphic 버전으로 만들고 적절한 implicit argument를 추가했다면, 다시 편리했던 notation으로 돌아가자.

```coq
Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).
```



## Polymorphic Pairs

pair도 다시 polymorphic하게 만들어보자. 이전에는 nat타입 인자 둘을 묶는 데 사용했지만 이젠 두 타입이 꼭 같을 필요는 없다. 이렇게 정의된 polymorphic pair는 일반적으로 **product**라는 이름으로 불린다.

```coq
Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y} _ _.
```

마찬가지로 notation을 추가하자.

```coq
Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.
```

여기서 `: type_scope`는 X*Y가 타입일 때의 곱셈과 다른 원소일 때(ex: nat)의 곱셈을 구분하기 위해 명시했다. 타입끼리의 product를 집합에서의 cartesian product로 생각하면 좀더 쉽게 이해할 수 있다.

예시 함수를 하나 작성해보자. 파이썬을 비롯한 대부분의 언어에서 `zip`이라는 이름으로 익숙한, 두 리스트를 하나로 합쳐주는 함수이다. 여기에서는 Coq라이브러리와의 일관성을 위해 `combine`이라는 이름을 사용했다.

```coq
Fixpoint combine {X Y:Type} (lx:list X) (ly:list Y) : list (X*Y) :=
match lx, ly with
| [], _ => []
| _, [] => []
| x :: tx, y :: ty => (x, y) :: (combine tx ty)
end.
```



## Polymorphic Options

이전 natoption을 다룰 때 모나드(monad)에 대해 잠깐 언급했다. 엄밀히 말해 natoption 자체는 단일 타입이므로 모나드라고 할 수 없다. (추가 영상에 설명된) maybe monad의 역할을 떠올리면서 아래 정의를 보자.

```coq
Inductive option (X:Type) : Type :=
| Some (x : X)
| None.

Arguments Some {X} _.
Arguments None {X}.
```

이렇게 만들어진 `option`은 타입 X를 받아 `option X` 타입으로 만들어주는 모나드라고 할 수 있다. 타입 option X가 가지는 의미는 이전에 natoption을 통해 설명했으니 여기에서는 생략한다. 마지막으로 `nth_error` 함수의 polymorphic 버전을 작성하면서 설명을 마친다.

```coq
Fixpoint nth_error {X:Type} (l:list X) (n:nat) : option X :=
match l with
| [] => None
| a :: l' => if n =? O then Some a else nth_error l' (pred n)
end.
```

```coq
>> Compute nth_error [4;5;6;7] 0.

   : Some 4 : option nat 
>> Compute nth_error [[1];[2]] 1.

   : Some [2] : option (list nat)

>> Compute nth_error [true] 2.

   : None : option bool
```

