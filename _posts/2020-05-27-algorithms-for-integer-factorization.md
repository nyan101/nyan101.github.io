---
layout: post
title:  "소인수분해 알고리즘(Pollard-(p-1), Pollard-rho, Dixon's Random Square)"
date:   2020-05-27 01:25:33
author: nyan101
categories: 전산
tags:	[전산, 수학]
use_math: true
---

[지난번 글](https://nyan101.github.io/blog/algorithms-for-discrete-logarithm-problem)에서는 이산 로그 문제에 대해 다뤘으니 이번엔 소인수분해 문제를 해결하는 알고리즘에 대해 알아보자. 코드는 이전과 마찬가지로 아래와 같은 수정이 들어간 파이썬 문법을 따랐다. 

* 양 끝을 명시적으로 나타내기 위해 `range(st, ed+1)` 대신 `[st...ed]`와 같은 표기를 사용했다.
* 파이썬에서 거듭제곱을 나타내는 `a**b` 대신 일반적으로 사용되는 `a^b` 표기를 사용했다.

지난 이산 로그 문제와는 달리 이번에는 ~~모두가 알 것이라 믿고~~ 소인수분해 문제에 대한 자세한 설명은 생략한다. 또한 알고리즘 설계를 간단히 하기 위해 소인수분해 문제의 요구조건을 **주어진 자연수 n에 대해, 1과 자기 자신(=n)을 제외한 약수를 발견하는 것**으로 정했다.



## Brute-Force

가장 간단한 방법은 모든 경우를 계산해보는 것이다. 그런데 $n$이 $a$를 약수로 가지면 $n/a$도 약수로 가진다는 사실을 이용하면 전체 $n$이 아닌 $\sqrt{n}$ 까지만 시도해보면 충분함을 알 수 있다.

```python
def factor(n):
    for d in [2, ..., floor(sqrt(n))]:
        if n % d == 0:
            return d
    return None
```

이는 $O(\sqrt{n})$ 만큼의 시간이 소요된다. 1억 이하의 작은 수들에 대해서는 충분할 수 있으나, 이보다 큰 숫자들에 대해서는 이후 소개할 알고리즘들을 사용해야 한다.



## Pollard-(p-1) Algorithm

Pollard-(p-1) 알고리즘은 페르마 소정리(Fermat's Little Theorem)을 활용한다. 주어진 $n$이 어떤 소수 $p$를 약수로 가진다면 페르마 소정리에 의해 $a^{p-1} \equiv 1 \pmod p$ 이 성립하고, 이는 자연수 $k$에 대해 $(a^{(p-1)\cdot k} - 1)$이 $p$의 배수가 됨을 의미한다. 다시 말해,  어떤 자연수 $m$이 $(p-1)$의 배수가 된다면  $gcd(a^m - 1, n)$ 은 최소한 $p$를 약수로 가지게 된다.

pollard-(p-1) 알고리즘에서는 적당히 큰 $B$에 대해 $(p-1) \| B!$ 이 성립하기를 기대한다. 만일 $(p-1)$이 $B$보다 큰 소인수를 가지지 않고[^1], 각 소인수가 포함된 개수[^2]가 크지 않다면 $(p-1) \| B!$ 을 만족할 수 있다. 이를 이용한 코드를 아래에 작성했다. 알고리즘에서 $a$의 선택은 영향을 미치지 않으나 일반적으로 2를 사용한다.

[^1]: 이러한 성질을 *B-smooth* 라고 한다.
[^2]: $p-1 = \prod q_i^{c_i}$에서 $c_i$

```python
def factor(n):
    a = 2
    B = (some value)
    for i in [1, ..., B]:
        a = (a^i) % n
    d = gcd(a-1, n)
    if 0 < d < n:
        return d
    else:
        return None
```

역으로 말해, 이러한 알고리즘으로 소인수분해되지 않게 하려면 n의 소인수 p가 **(p-1)​이 큰 소인수를 가진다**는 조건을 만족하도록 설정해야 한다.



## Pollard-rho Algorithm

pollard-rho(ρ) 알고리즘은 지난 이산 로그 문제에서와 마찬가지로 일종의 충돌쌍을 이용해 소인수를 찾는 방식이다. 구체적으로, 어떤 $x, x'$이 $x\neq x'$, $x \equiv x' \pmod p$을 만족한다면 $gcd(x - x', n)$ 은 최소한 $p$를 약수로 가진다는 사실을 이용한다. 랜덤한 $a, b$들을 시험해보면서 $gcd(a - b, n)>1$ 을 만족하는지 알아보는 대신, 조사를 효율적으로 진행하기 위해 변환규칙을 사용한다.

> 위 알고리즘에서의 변환규칙 $f()$를 보면 한번 충돌($x_{i}=x_{2i}$)이 발생하면 $x_{i+1}=x_{2i+1},\cdots$ 로 계속 이어짐을 쉽게 파악할 수 있다. 따라서 1칸씩 움직이는 $s_i$와 2칸씩 움직이는 $s_{2i}$, 이렇게 2개만을 이용해도 많은 쌍을 동시에 검증하는 효과를 얻을 수 있다.
>
> *[이전 글](https://nyan101.github.io/blog/algorithms-for-discrete-logarithm-problem)에서의 Pollard-rho 알고리즘 설명 중*

이산 로그 문제에서와 달리 이번에는 변환규칙 $x_{i+1} = f(x_i)$을 정할 때 경우를 나누지 않으며, 일반적으로 $f(x) = x^2 + 1$을 많이 사용한다.

```python
def factor(n, max_iter=1000):
    # transition rule
    def f(x):
        return (x*x + 1) % n
    # function main
    x1 = x2 = 1
    for i in [0...max_iter]:
        x1 = f(x1)
        x2 = f(f(x2))
        d = gcd(x1 - x2, n)
        if 1 < d < n:
            return d
    return None
```



## Dixon's Random Square Algorithm

만일 $x^2 \equiv y^2 \pmod n$이고 $x \not \equiv \pm y \pmod n$ 를 만족하는 $x,y$를 찾으면 $gcd(x-y, n) > 1$이 성립하므로 $n$의 약수를 찾을 수 있게 된다. Dixon's Random Square 알고리즘은 이러한 $x, y$를 찾는 방법을 제시한다.

알고리즘은 다음과 같이 진행된다.

1. 소수들의 집합 $B = \{p_1, p_2, \cdots, p_t\}$를 정한다. (일반적으로 작은 순으로 $t$개의 소수들을 사용)
2. 랜덤한 $x_1, x_2, \cdots$들에 대해 다음을 진행한다.
  
   * $x_i^2 \equiv b_i \pmod n$에 대해 $b_i$를 $B$에 속한 소수들로 인수분해한다. $b_i = \prod_{p_j \in B} p_j^{c_j}$ 꼴로 정리하면 $b_i$를 $\langle c_1, c_2, \cdots, c_t \rangle$ 로 쓸 수 있으며, $B$에 속한 소수들만으로 인수분해가 불가능할 경우 새로운 $x_i$를 뽑는다.
3. 2번 과정을 거치면서 구한 벡터들 $\langle c_1, c_2, \cdots, c_t \rangle_{\{i\}}$ 을 결합해 모든 원소가 짝수인 벡터(=제곱수)를 만들 수 있는지 확인한다.

    → 해당 벡터를 만드는 $\prod x_i$와 $\sqrt{\prod b_i}$가 각각 $a^2 \equiv b^2 , a \not \equiv \pm b \pmod n$ 를 만족하는 $a, b$가 된다. 이때 $a \equiv b \pmod n$이 되는 경우 계속 탐색을 진행한다

실제 예시를 통해 살펴보자. $B = \{2, 3, 5, 7, 11, 13\}$ 을 이용해 $n=15770708441$을 소인수분해하려고 하고, 아래와 같은 정보를 얻었다고 하자.

$$
\begin{align*}
(2773700011)^2 & \equiv 2  \times 3\times 13  &\pmod n\\
(8340934156)^2 & \equiv   3  \times 7           &\pmod n\\
(12044942944)^2 & \equiv 2  \times 7  \times 13 & \pmod n
\end{align*}
$$

이를 종합하면 다음을 얻을 수 있다.

$$
(8340934156 \times 12044942944 \times 2773700011)^2 \equiv (2 \times 3 \times 7 \times 13)^2 \pmod n
$$

계산하면 식의 왼쪽은 $(9503435785)^2$, 오른쪽은 $(246)^2$ 이 되고, 여기에 유클리드 알고리즘을 이용해 $(9503435785 - 246)$과 $15770708441$ 의 공약수를 구하면 n의 자명하지 않은 약수 $15770708441$을 얻을 수 있다.

알고리즘의 핵심이 되는 3번 과정은 $\langle c_1, c_2, \cdots, c_t \rangle_{\{i\}}$ 에 $\mathbb{Z}_2$ 위에서의 가우스 소거법을 적용하는 방법으로 수행할 수 있다.

---