---
layout: post
title:  "PyTorch 사용법 정리 - 기본구조(작성중)"
date:   2019-08-18 22:00:21
author: nyan101
categories: 자습
tags:	[전산, 개발]
use_math: true
---



요새는 뭘 찾아봐도 딥러닝이 나온다.. 태생이 continuous, gradient 같은 거랑은 안 맞아서 최대한 피해보려고 했지만 ~~시대의 흐름에 거스르지 않고~~ 어떻게 사용하는지 정도는 알아두는게 좋을 것 같아서 정리해봤다. tensorflow(+keras)와 pytorch 사이에서 고민하던 중, 내 기준으로 좀더 직관적인 pytorch를 기준으로 정리했다.

#### 요구사항(prerequisite)

* python에 대한 기초지식
  (ex: `ABC.xyz()`는 클래스/객체 `ABC` 안에 있는 `xyz` 라는 함수를 호출하는 것이다)
* 함수에 대한 개념(규칙에 따라 input → output으로 이어지는 블랙박스로 이해해도 된다)
* 머릿속 이미지화를 위한 약간의 상상력(?)




## tensor 클래스
tensor는 \\(n\_1 \\times n\_2 \\times \\cdots \\times n\_d \\) 개의 숫자를 \\(d\\)차원으로 정렬한 객체이다. 편의상 예시는 2차원 이하만을 다룰 예정이지만 임의의 차원을 가질 수 있다는 점은 알아두자.

#### 생성

```python
x = torch.tensor([[1,2,3],[4,5,6]]) # 1~6으로 채워진 2차원 텐서(크기 2x3)를 생성
y = torch.rand((3, 4)) # 0~1 사이의 임의의 수로 채워진 2차원 텐서(크기 3x4)를 생성
z = torch.zeros((1,2,3)) # 0으로 채워진 3차원 텐서(크기 1x2x3)를 생성. 1로 채우는 ones()도 있다

x.shape # 텐서 x의 크기. 위 예시에서는 torch.Size([2, 3])
```

#### 연산

numpy에서와 비슷하게 다양한 연산을 지원한다. ~~왠지 있을법한건 대충 다 있다고 보면 된다.~~

```python
z = x.mean() # x의 모든 원소들의 평균
z = x.sum()  # x의 모든 원소들의 합
z = x + y    # x,y의 각 원소들에 대한 element-wise 덧셈. + 대신 *를 쓰면 곱셈 연산이 된다
             # 예외적으로 y가 스칼라이거나 1x1 크기인 경우 x의 모든 원소에 대해 연산이 이루어진다
z = x @ y    # x,y의 행렬곱. x,y가 크기 제약조건(N x M 행렬과 M x R 행렬)을 만족해야 한다
             # 예외적으로 y가 1차원인 경우 상황에 맞는 행벡터or열벡터인 것처럼 처리된다
```



## Tensor와 Autograd

딥러닝은 결국 gradient descent 과정이다. 

#### 연산 그래프(Computational Graph)

이제 텐서들의 연산에 대한 머리속의 구조(Mental Model)를 살짝 바꾸는 작업이 필요하다. 다음 코드를 보자

```python
x = torch.tensor([3])
y = torch.tensor([4])
z = x + y
```

이 코드는 머리속에서 왼쪽과 같은 형태로 이해되기 쉽다. x와 y를 상수 3, 4에 붙은 다른 이름으로 생각하고 z에는 7이 저장된다고 상상하는 것이다. `int`나 `float` 같은 primitive 타입에서는 이렇게 생각해도 문제는 없다. 그러나 tensor라는 '객체'는 조금 다르게 동작한다.

<img src="/assets/images/2019/08/pytorch-01-add.png" width="400px">

왼쪽 그림에서와 달리 오른쪽에서 z는 연산의 결과값(7)뿐만이 아닌, 어떻게 그 값을 얻게 되었는지를 역추적할 수 있는 링크가 추가로 존재한다.[^1] z를 가지고 연산을 계속하면 마찬가지로 이어진 그래프(DAG)를 얻을 수 있고, 이를 연산 그래프(Computational Graph)라고 한다.

[^1]: 직관적인 그림을 위해 설명을 단순화했다. 실제로는 모든 텐서가 아닌 `requires_grad=True`로 설정된 텐서들만이 그래프의 유의미한 노드가 된다.

이러한 연산 그래프를 만들기 위해서는 `torch.tensor`를 정의할 때 `requires_grad=True`를 설정해야 하며, 선언 이후에 이를 변경해야 하는 경우 `.requires_grad_()` 함수에 True/False를 넘김으로써 온/오프가 가능하다.

```python
x = torch.tensor([3.0], requires_grad=True) # tensor([3.], requires_grad=True)
y = torch.tensor([4.0], requires_grad=True) # tensor([4.], requires_grad=True)
z = x + y                                   # tensor([7.], grad_fn=<AddBackward>)
y.requires_grad_(False) # 이제 y는 연산 그래프에서 gradient를 계산하지 않음
```

테스트

```python
x = torch.tensor([3.0], requires_grad=True)
y = torch.tensor([4.0], requires_grad=True)
z = x + y                                  
y.requires_grad_(False)
```



#### 그래디언트 계산

그럼 이제 다음과 같은 두 질문이 떠오른다.

* "required_grad에서 grad는 무엇을 의미하는가"
* "이렇게 연산 그래프를 만들어서 무엇을 얻는가"

먼저 첫 질문에 답해보자. 그래디언트(gradient, 이하 grad)는 간단히 말해 **변수가 '현재 시점'에서 목적함수를 변화시키는 정도**라고 할 수 있다. 예로 \\(y = -x^4 + 10x^3 + 10x^2 - 15x - 4\\)의 식에서 \\(y\\)를 목적함수라고 하면 아래와 같은 그래프를 얻을 수 있다.

<img src="/assets/images/2019/08/pytorch-01-gradient.png" width="600px">

아래 그래프에서 \\(x=5\\)인 순간에 x의 그래디언트 \\(\\frac{\\partial y}{\\partial x}\\)는 335이다. 이는 \\(x=5\\) 근처에서 x가 \\(d\\) 만큼 변하면 y는 \\(335d\\) 만큼 변하게 됨을 의미한다. 다변수 함수 \\(y=f(x\_1,x\_2)\\)에 대해서도 마찬가지로 \\(\\frac{\\partial y}{\\partial x\_1}, \\frac{\\partial y}{\\partial x\_2}\\) 를 정의할 수 있다.

이제 연산 그래프의 진가가 드러난다. 연산 그래프를 통해 최종 결과물(a.k.a. 목적함수)이 어떻게 계산된 것인지를 역추적함으로써 각 입력 변수들이 목적함수에 얼마나 영향을 끼치는지를 말해줄 수 있다.

```python
x = torch.tensor([5.0], requires_grad=True)

y = -1*(x**4) + 10*(x**3) + 10*(x**2) - 15*x - 4
y.backward()  # dy/dx를 구한다

print(x.grad) # tensor([335.])
```

조금 더 복잡한 연산의 경우에도 마찬가지 연산이 가능하다.

```python
x1 = torch.tensor([1.0], requires_grad=True)
x2 = torch.tensor([2.0], requires_grad=True)
x3 = torch.tensor([3.0], requires_grad=True)

y = x1*x2*x3*x3 + 7*x1*x2 - x2*x2 - 4*x1*x3 
y.backward()   # y의 계산과 관련된 모든 x들에 대해 dy/dx를 구한다

print(x1.grad) # tensor([20.])
print(x2.grad) # tensor([12.])
print(x3.grad) # tensor([8.])
```



## 모델 만들기

```python
class MyNet(nn.Module):
    def __init__(self):
        super(Net, self).__init__()
        # init parameters, usually layers

    def forward(self, x_input):
        # some calculation with x_input and parameters
        return y_predicted

# init model object
my_net = MyNet()

# target
my_input  = xxx # input data
y_target  = yyy # desired output

# run calculation on model
my_output = my_net(my_input)

# define criterion and loss
criterion = nn.MSELoss()
loss = criterion(my_output, y_target)
```

---

