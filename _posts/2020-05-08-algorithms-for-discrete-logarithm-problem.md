---
layout: post
title:  "이산 로그 문제(DLP)에 대한 알고리즘(Shanks, Pollard-rho, Pohlig-Hellman)"
date:   2020-05-08 16:36:14
author: nyan101
categories: 전산
tags:	[전산, 수학]
use_math: true
---

암호학, 특히 공개키 기반 암호시스템은 주로 1)소인수분해 문제 혹은 2)이산 로그 문제를 기반으로 설계되는 경우가 많다. 그중 이산 로그 문제와 이를 해결하는 알고리즘에 대해 알아보자. 예시로 든 코드는 기본적으로 파이썬 문법을 따라 작성했으며 가독성을 위해 다음과 같은 부분을 수정했다.

* 파이썬에서 `range(n)`은 0부터 시작해 n이 아닌 n-1까지를 포함한다. 양 끝을 명시적으로 나타내기 위해 `[st...ed]`와 같은 표기를 사용했다.
* 파이썬에서 거듭제곱을 나타내는 `a**b` 대신 일반적으로 사용되는 `a^b` 표기를 사용했다.
* mod p에서의 역원을 `a^(-1)`로 표기했다. 실제 구현에서는 a의 (p-2)제곱으로 구할 수 있다.
  * 페르마 소정리에 의해 $a^{p-1} \equiv 1 \pmod p$이므로 $a\cdot a^{p-2} \equiv 1$에서 $a^{-1} \equiv a^{p-2}$.



## 이산 로그 문제
이산 로그 문제는 이산 대수 문제라고도 하며, 순환군 $\langle g \rangle$와 군의 원시근(primitive root) $g$, 그리고 $y \in \langle g \rangle$ 가 주어졌을 때, $y=g^k$를 만족하는 최소의 자연수 $k$를 찾는 문제이다. 암호학에서는 큰 소수 $p$에 대해 $p$로 나눈 나머지들의 모임인 $\mathbb{Z}_p^\ast$를 사용하는 경우가 많다.

일반적인 실수($\mathbb{R}$) 체계에서 이는 $\log_{g}y$ 가 된다는 점에서 이산 **로그** 라는 이름이 붙었으며, $a < b$ 이면 $\log_g{a} < \log_g{b}$라는 성질을 이용해 산술적으로 쉽게 해를 구할 수 있는 일반적인 로그 문제와 달리 군에서는 이러한 대소 비교가 원활하지 않기에 어려움이 있다.

예로 mod 13에 대해 원시근 g가 2인 상황을 살펴보자

| $k$   | 0    | 1    | 2    | 3    | 4    | 5    | 6    | 7    | 8    | 9    | 10   | 11   |  12  |
| ----- | ---- | ---- | ---- | ---- | ---- | ---- | ---- | ---- | ---- | ---- | ---- | ---- | -- |
| $g^k$ | 1 | 2 | 4 | 8 | 3 | 6 | 12 | 11 | 9 | 5 | 10 | 7 | 1 |

6 > 5 이지만 $g^k=5$를 만족하는 k는 5, $g^k=5$를 만족하는 k는 9로 대소 관계가 유지되지 않는다. 이러한 불규칙성으로 인해 일반적인 이산 대수 문제를 해결하는 효율적인 알고리즘은 아직 발견되지 않았다.

이제 이를 해결하는 몇 가지 방법들에 대해 알아보자. 단 문제를 풀 순환군이 소수 $p$에 대해 $\mathbb{Z}_p^\ast$ 인 경우만을 생각하며, 편의상 군의 크기를 $n(=p-1)$으로 표현하기로 한다.



## Brute-Force

가장 간단한 방법은 모든 경우를 계산해보는 것이다. 이를 코드로 표현하면 다음과 같다.

```python
def solveDLP(y, g, p):
    t = 1
    for i in [0...p-2]:
        if t == y:
            return i
        t = (t * g) % p
    return None
```

이는 추가 메모리는 $O(1)$로 거의 필요하지 않지만 최악의 경우 순환군의 원소의 개수, 즉 $O(n)$ 만큼의 시간이 소요된다.



## Shanks' Algorithm

Shanks 알고리즘은 **baby-step, giant-step 알고리즘**이라고도 불리며 다음과 같이 동작한다.

1. 군의 크기(n, 여기서는 n=p-1)에 대해 $m=\sqrt{n}$을 지정한다.

2. $i=0, 1, \cdots, (m-1)$에 대해 $(a_i, b_i) = (y\cdot g^{-i}, i)$들을 기록한다.

3. $j=0, 1, \cdots, \lceil p/m \rceil$ 에 대해 $(a_j, b_j) = (g^{m\cdot j}, m \cdot j)$들을 기록한다.

4. 2, 3에서 $a_i = a_j$인 쌍을 찾으면 $\log_g{y} = (b_i + b_j)$ 가 성립한다.

위 알고리즘의 정당성은 4. 에서 $a_i = y\cdot g^{-i} = g^{m\cdot j} = a_j$ 라는 사실을 생각하면 쉽게 알 수 있다. 거듭제곱을 1칸씩 뛰는 2단계(baby step)과 m칸씩 뛰는 3단계(giant step)로 이루어져 있어 이같은 이름이 붙었다. 알고리즘을 코드로 나타내면 다음과 같다.

```python
def solveDLP(y, g, p):
    m = sqrt(p)
    baby, giant = {}, {}
    val = 0
    gm = (g^m) % p
    for i in [0...p//m]:
        giant[val] = m * i  # giant[g^(m*i)] = m*i
        val = (val * gm) % p
    val = y
    for i in [0...m-1]:
        baby[val] = i       # baby[y * g^(-i)] = i
        if val in giant.keys():
            return giant[val] + i
        val = (val * g^(-1)) % p
    return None
```

딕셔너리에 키의 존재성을 확인하는 단계에서 균형이진트리를 가정하면, 위 알고리즘은 메모리 $O(\sqrt{n})$, 시간 $O(\sqrt{n} \log n)$의 복잡도를 가진다.



## Pollard-rho Algorithm

pollard-rho(ρ) 알고리즘은 $g, y$에 대해 $g^{a}y^{b}=g^{a'}y^{b'}$를 만족하는 쌍 $(a, b) \neq (a', b')$을 찾을 수 있다면 이로부터 $\log_g y =  (a - a') \cdot (b' - b)^{-1}$를 구할 수 있다는 점에 착안한다. 그러나 임의의 $a, a', b, b'$에 대해 $g^a b^y, g^{a'}y^{b'}$를 계산해 두 값이 동일하기를 기대하는 것은 비효율적이므로, 이를 위해 다음과 같은 방식을 사용한다.

1. 순환군 $G(=\mathbb{Z}_p^\ast)$의 원소를 3종류로 분할한다. ($G = S_0 \cup S_1 \cup S_2, i\neq j \rightarrow S_i \cap S_j = \emptyset$)
  * 분할방식은 무관하며, 일반적으로 $S_i = \\{x \| x \equiv i \pmod 3\\}$ 을 사용
2. $s_0 = (x_0, a_0, b_0) = (1, 0, 0)$에서 시작한다.

3. $(x_i, a_i, b_i)$에서 $x_i$에 따라 $(x_{i+1}, a_{i+1}, b_{i+1})$를 구하는 규칙 $s_{i+1} = f(s_i)$를 설정한다.

$$
f(s_i) = (x_{i+1}, a_{i+1}, b_{i+1})=
\begin{cases}
(y\cdot x_{i},& a_i,& b_i+1)&\mathrm{if}\,\,x_i \in S_0 \\
(x_{i}^2,& 2a_i,& 2b_i)&\mathrm{if}\,\,x_i \in S_1\\
(g\cdot x_{i},& a_i+1,& b_i)&\mathrm{if}\,\,x_i \in S_2
\end{cases}
$$

4. $s_{i+1} = f(s_i), s_{2i+2} = f(f(s_{2i}))$임을 이용해 $s_i, s_{2i}$들을 탐색해 $x_i = x_{2i}$ 여부를 확인한다.

위 알고리즘에서의 변환규칙 $f( )$를 보면 한번 충돌($x_i = x_{2i}$)이 발생하면 $x_{i+1} = x_{2i+1}, \cdots$ 로 계속 이어짐을 쉽게 파악할 수 있다. 따라서 1칸씩 움직이는 $s_i$와 2칸씩 움직이는 $s_{2i}$, 이렇게 2개만을 이용해도 많은 쌍을 동시에 검증하는 효과를 얻을 수 있다. 이를 코드로 나타내면 다음과 같다.

```python
def solveDLP(y, g, p, max_iter=1000):
    # transition rule
    def f(x, a, b):
        if x % 3 == 0:
            return (y*x)%p, a, b+1
        elif x % 3 == 1:
            return (x*x)%p, 2*a, 2*b
        else:
            return (g*x)%p, a+1, b
    # function main
    (x1, a1, b1) = (x2, a2, b2) = (1, 0, 0)
    for i in [0...max_iter]:
        x1, a1, b1 = f(x1, a1, b1)
        x2, a2, b2 = f(f(x2, a2, b2))
        if x1 == x2:
            return ((a1 - a2) * (b2 - b1)^(-1)) % p
    return None
```

이 알고리즘의 수행시간은 transition rule $f$의 설정, 그리고 분할 $(S_0,S_1,S_2)$에 따라 달라질 수 있으며, 근사적으로 $O(\sqrt n)$ 정도임이 알려져 있다.




## Pohlig-Hellman Algorithm

pohlig-hellman 알고리즘은 순환군 $\mathbb{Z}_p^\ast$의 크기 n(=p-1)이 작은 소인수들로 인수분해될 때 사용할 수 있는 방식이다. 구체적으로, 소수 $q_i$들을 이용해
$$
|G| = |\mathbb{Z}_p^\ast| = n = (p-1) = \prod_{i=1}^m q_i^{c_i}
$$
로 표현했을 때 $q_i$들이 모두 작은 경우에 사용할 수 있다. 이 알고리즘은 페르마 소정리(Fermat's Little Theorem)에 의해 $g^{p-1}\equiv 1 \pmod p$라는 사실과, 중국인의 나머지 정리에 의해 $g^k \equiv y \pmod p$를 만족하는 k는

$$
k \equiv k_1 \pmod {q_1^{c_1}}\\
k \equiv k_2 \pmod {q_2^{c_2}}\\
\vdots\\
k \equiv k_2 \pmod {q_m^{c_m}}
$$

들이 주어졌을 때 유일하게 결정된다는 사실을 이용한다.

이제 $k \pmod {q_1^{c_1}}$을 구하는 방법을 알아보자. 가독성을 위해 $q_i, c_i$ 대신 $q, c$로 표기했다.

먼저 $k = a_0 + a_1 \cdot q + \cdots + a_{c-1} \cdot q^{c-1} + s \cdot q^c$으로 쓸 수 있다. 그러면 주어진 y에 대해

$$
\begin{aligned}
y^{n/q} = (g^k)^{n/q} &= (g^{a_0 + a_1 \cdot q + \cdots + a_{c-1} \cdot q^{c-1} + s \cdot q^c})^{n/q}\\
&= (g^{a_0+S\cdot q})^{n/q}\\
&= g^{a_0 \cdot n/q}\cdot g^{S\cdot n}\\
&= g^{a_0 \cdot n/q}\cdot 1^{S}
\end{aligned}
$$

가 성립하고, 이를 이용해 $a_0$를 최대 q번의 시도로 구할 수 있다. 마찬가지 방법으로 $y^{n/{q^2}}$을 통해 $a_1$을 구할 수 있고, 이를 계속해 $a_i$들을 구해가면 최종적으로 $k \pmod {q^{c}}$를 얻는다.

이제 이를 다른 소인수에도 마찬가지로 적용하면서 m가지 식 $k \equiv k_i \pmod {q_i^{c_i}}$ 을 모두 세우면, 중국인의 나머지 정리를 통해 $k \pmod p$를 구할 수 있다. $p-1$을 소인수분해하는 과정을 제외하면 이 알고리즘은 $O\left(\sum (c_i \cdot q_i \cdot \log p) + C\right)$의 복잡도를 가진다.  (Square-and-Multiply 방식을 사용하면 거듭제곱에 $O(\log p)$가 소요되며, $C$는 중국인의 나머지 정리를 적용하는 데 소요되는 시간을 의미한다)
