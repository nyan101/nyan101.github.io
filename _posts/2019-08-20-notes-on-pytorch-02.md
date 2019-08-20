---
layout: post
title:  "[PyTorch] PyTorch 사용법 정리 - 추상화된 모델 만들기 (작성중)"
date:   2019-08-20 21:53:17
author: nyan101
categories: 자습
tags:	[전산, 개발]
use_math: true
---



## 학습의 각 단계를 추상화하기

앞서 그래디언트를 이용해 간단한 학습이 이루어지는 과정을 알아보았다. 이전 글의 마지막 코드를 다시 살펴보면 학습의 한 round를 크게 다음과 같은 단계들로 추상화시킬 수 있다.

```python
for i in range(num_adjust):
    # 1) 파라미터를 이용해 입력(xs)으로부터 예상 결과를 생성
    y_pred = a*xs + b
    # 2) 예상 결과(y_pred)와 실제 결과(ys)를 비교해 오차를 계산
    err = ((y_pred - ys)**2).mean()
    # 3) .backward()를 통해 각 파라미터가 오차에 관여하는 정도를 역산
    err.backward()
    # 4) 역산된 grad를 바탕으로 파라미터 수정 
    a.data.sub_(0.01 * a.grad)
    b.data.sub_(0.01 * b.grad)
    # 5) 파라미터들의 grad값을 0으로 초기화
    a.grad.zero_()
    b.grad.zero_()
```

그런데 이번과 같이 모델이 \\(y=ax+b\\) 처럼 간단한 형태인 경우 파라미터(`a`, `b`)들을 각자 관리할 수 있지만, 복잡한 모델의 경우 이는 상당히 번거로운 과정이 될 수 있다. 흩어진 파라미터들을 통합해 관리한다면 어떤 형태가 가능할지 생각해 보자.

```python
params = "통합된 파라미터들을 저장할 모음. list,dict,class,... 중 뭐가 좋을까?"

def init_params(params):
    params = "어떤 파라미터를 사용할 것인지 정의하고, 각 파라미터에 초기값 설정"
    pass

def predict(x, params):
    y_pred = "입력(=x)과 params으로부터 예측값 계산"
    return y_pred

def calculate_err(y_pred, y):
    err = "예측값(y_pred)과 실제값(y)간의 차이를 계산"
    return err

def update_params(params):
    "grad를 바탕으로 params를 조절한다"
    pass

def clear_grad(params):
    "params의 grad 값들을 전부 0으로 초기화한다"
    pass

# 추상화된 학습과정
init_params()
for i in range(num_adjust):
    # 1) 파라미터를 이용해 입력(xs)으로부터 예상 결과를 생성
    y_pred = predict(xs, params)
    # 2) 예상 결과(y_pred)와 실제 결과(ys)를 비교해 오차를 계산
    err = calculate_err(y_pres, ys)
    # 3) .backward()를 통해 각 파라미터가 오차에 관여하는 정도를 역산
    err.backward()
    # 4) 역산된 grad를 바탕으로 파라미터 수정 
    update_params(params)
    # 5) 파라미터들의 grad값을 0으로 초기화
    clear_grad(params)
```

대부분의 경우 학습과정은 이 형태를 크게 벗어나지 않을 것이다. 그런데 여기서 일부 함수들이 순수 함수(pure function)가 아닌, 내부 상태를 변화시키는 '동작' 을 하는 프로시저(procedure)라는 사실이 눈에 들어온다. 일관성 있는 관리를 위해 각 단계들을 다시 역할에 따라 분류해 클래스로 만들 수 있다.

* 예측값 계산 담당
  * `init_params()`, `predict()`
* 오차 계산 담당
  * `calculate_err()`
* 파라미터 조정 담당
  * `update_params()`, `clear_grad()`

pytorch 모델은 기본적으로 이러한 분류를 따라 설계된다. 각각은 흔히 model(혹은 module), criterion, optimizer라는 이름으로 불리며, 이들 용어는 특별한 언급이 없는 한 앞으로의 글에서도 동일한 의미를 가진다.



## Model 클래스 만들기

TODO