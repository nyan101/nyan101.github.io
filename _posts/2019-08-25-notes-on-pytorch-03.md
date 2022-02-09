---
layout: post
title:  "[PyTorch] 03. torch.nn 모듈 조립으로 CNN 만들기"
date:   2019-08-25 16:39:46 +0900
author: nyan101
categories: 자습
tags:	[전산, 개발]
use_math: true
---



## 예제 dataset 가져오기

지금까지는 \\(y=ax+b\\)나 \\(y=ax^2+bx+c\\) 처럼 간단한 형태의 숫자→숫자 함수만을 모델링했으니 이제 좀더 흥미로운 데이터를 살펴보자.

딥러닝, 특히 이미지 인식 관련 예제를 보면 MNIST나 CIFAR-10같은 이름이 많이 등장한다. 이 둘은 Image Classification 문제의 대표적인 예시로 각각 손글씨와 물체 사진 이미지셋에 해당하며, 흔히 모델의 벤치마크 용도로 활용되고 있다. 이번 글에서는 좀더 단순한 MNIST를 사용하기로 한다. MNIST 데이터는 아래와 같이 색이 없는 1채널(=gray scale) 28x28픽셀 이미지들의 모음으로 0에서 9까지 총 10개의 라벨을 가지고 있다.

<img src="/assets/images/2019/08/pytorch-03-MNIST-image.png" style="width:600px">

유명한 데이터셋인 만큼 인터넷에서 손쉽게 구할 수 있지만 ~~있을 건 다 있는 python답게~~  `torchvision` 모듈의 `datasets` 에서도 가져올 수 있다. `root`인자로 데이터가 저장된(혹은 저장하고자 하는) 경로를 넘겨주면 이를 읽어오며, `download=True`인 경우 해당 경로에 자동으로 다운로드까지 함께 이루어진다.

```python
import torchvision.datasets as datasets

train_data = datasets.MNIST(root='./data', train=True, download=True)
test_data = datasets.MNIST(root='./data', train=False, download=True)
```

`train_data`에 대한 정보를 살펴보면 각 데이터는 _(PIL 이미지, 라벨)_ 형식의 tuple로 이루어져 있음을 알 수 있다.

<img src="/assets/images/2019/08/pytorch-03-MNIST-jupyter.png">

이제 이를 인식하는 모델을 만들어야 한다.



## torch.nn 모듈 조립해서 CNN 만들기

이미지 인식이라는 주제로 찾아보면 어김없이 CNN이라는 단어가 등장한다. CNN(Convolutional Neural Network)은 이미지에 2d convolution 필터를 씌워 처리하는 네트워크로 크게 아래와 같은 구조를 가진다.

<img src="/assets/images/2019/08/pytorch-03-typical-CNN.png">

이전 글에서 모델 클래스를 만드는 법을 알아봤으니 convolution, sampling, activation에 필요한 설정을 생각해보자.

* 2D-convolution
  * convolution filter 하나당 필터 크기만큼의 2차원 텐서, 그 외 기타 설정값(ex: stride 등) 필요
  * \\(C\_{in}\\)개 입력, \\(C\_{out}\\)개 출력이면 \\(C\_{in} \\times C\_{out}\\) 개 필터를 관리해야 함
* Activation
  * 어떤 activation인지에 따라 다르지만 ReLU인 경우 일단은 `max` 함수로 구현 가능
* Sampling
  * 샘플링 함수 작성. 제일 간단한 max pooling의 경우 매 MxM 사각형에서 최대값 1개를 추출

....불가능한 건 아니지만 상당히 번거롭다. 어차피 알고리즘은 동일하고 세부 파라미터만 수정하면 되는데 누가 해놓지 않았을까? ~~왠지 노양심같지만 파이썬을 하다보면 이런 마인드가 자연스럽게 탑재된다~~

`pytorch.nn`에서 미리 구현된 모듈들을 가져올 수 있다. 간단히 2d-Convolution → activation → subsampling으로 이어지는 layer을 2개 만들고, 마지막에 Fully Connected layer를 덧붙였다.

```python
class MyModel(nn.Module):
    def __init__(self):
        super(MyModel, self).__init__()
        self.layer1_conv = nn.Conv2d(1, 6, 5, 1) # 입력 1개, 출력 6개, 필터 크기는 5x5, 1칸 단위로 이동하면서 필터를 씌운다
        self.layer1_relu = nn.ReLU()             # 활성화 함수. ReLU(x) 는 max(x, 0)과 같다
        self.layer1_pool = nn.MaxPool2d(2)       # 각 2x2 칸마다 최대값 하나씩만을 남긴다
        self.layer2_conv = nn.Conv2d(6, 16, 5, 1)
        self.layer2_relu = nn.ReLU()
        self.layer2_pool = nn.MaxPool2d(2)
        self.fc = nn.Linear(16*4*4, 10)
    
    def forward(self, x):
        x1 = self.layer1_conv(x)  # 1x28x28 형식의 데이터가 6x24x24 형식으로 변환된다
        x2 = self.layer1_relu(x1) # 
        x3 = self.layer1_pool(x2) # 6x24x24 형식의 데이터가 6x12x12 형식으로 변환된다
        x4 = self.layer2_conv(x3) # 6x12x12 형식의 데이터가 16x8x8 형식으로 변환된다
        x5 = self.layer2_relu(x4) # 
        x6 = self.layer2_pool(x5) # 16x8x8 형식의 데이터가 16x4x4 형식으로 변환된다
        x7 = x6.view(-1, 256)     # 16x4x4 형식의 데이터가 256-벡터로 변환된다
        x8 = self.fc(x7)          # 256-벡터가 10-벡터로 변환된다
        return x8
```

생각보다 꽤 단순하다. 그럼 동작하는지 확인해보자.

```python
net = MyModel()
criterion = nn.CrossEntropyLoss()
optimizer = optim.Adam(net.parameters())

# TypeError: conv2d(): argument 'input' (position 1) must be Tensor, not Image
net(train_data[0][0]) 
```

에러에서 볼 수 있듯이 PIL 이미지를 먼저 텐서로 변환해줄 필요가 있다. `torchvision.transforms` 에 있는`functional.to_tensor()` 함수를 통해 PIL이미지를 텐서로 변환하자. 혹은 앞서 데이터를 읽어들이는 시점에 다음과 같이 파라미터를 설정함으로써 PIL 이미지 대신 변환된 텐서를 가져올 수 있다. 

```python
# 이제 _data의 각 요소는 (PIL Image, Tensor) 대신 (Tensor, Tensor) 가 된다.
train_data = datasets.MNIST(root='./data', train=True, transform=transforms.ToTensor())
test_data = datasets.MNIST(root='./data', train=False, transform=transforms.ToTensor())
```

그런데 입력 데이터를 텐서 형식으로 넘겨줘도 또다른 에러가 발생한다. 이는 pytorch 모델이 기본적으로 단일 데이터가 아닌 데이터 batch에 대해 동작하도록 설계되었기 때문인데, 이를 위해 데이터에 축(axis)을 하나 추가해주자.

```python
# * transform=transforms.ToTensor()로 이미 변환된 데이터라고 가정
# 모델에 1x28x28 입력이 아닌 (batch_size)x1x28x28 입력을 전해줘야 한다.

x_input = train_data[0][0] # x_input은 1x28x28 크기의 텐서
net(x_input[None,:])       # [None,:] 으로 축을 추가해 텐서 크기를 1x1x28x28로 만든다
```

이제 다음과 같은 출력을 확인할 수 있다.

```
tensor([[ 0.0534,  0.0028, -0.0284, -0.0451, -0.0616,  0.0883,  0.0050, -0.0106,
          0.0624,  0.0225]], grad_fn=<ThAddmmBackward>)
```

출력 텐서가 크기 10인 1차원 텐서가 아니라 _1x10_ 크기의 텐서임에 유의하자. _(batch_size) x 10_ 크기의 텐서가 결과로 출력되는 것이다.

아직은 학습이 전혀 진행되지 않았으니 이는 무의미한 값들에 불과하다. 학습이 끝나면 이 무의미한 값이 어떤 의미를 가져야 할까? 머신러닝 관련 키워드에 관심이 많다면 원 핫 인코딩([One Hot Encoding](https://en.wikipedia.org/wiki/One-hot))이 떠오를 것이다. 핵심만 말하면 10-벡터에서 정답에 해당하는 인덱스에 1이, 나머지에는 0이 들어가도록, 혹은 기준을 조금 완화해 `argmax(prediction_tensor)`가 정답 라벨과 일치하도록 만드는 것이다.

말은 쉽지만 세부 사항을 정하기 위해서는 1)라벨을 one-hot 형식으로 바꾸고, 2)결과 벡터를 정규화하고, 3)두 벡터의 '차이'를 어떻게 정의할 것인지 결정하는 등 많은 과정이 필요하다. 물론 이 역시 ~~이젠 새삼스럽지도 않게~~ 다른 전처리 과정과 같이 pytorch에 구현되어 있다. 자세한 원리를 알고싶다면 [공식 문서](https://pytorch.org/docs/stable/nn.html#crossentropyloss)를 참조하자.


```python
criterion = nn.CrossEntropyLoss()
```

optimizer는 이전의 SGD 대신 Adam을 사용한다. 좀더 세련된(...) 방식의 파라미터 업데이트를 수행한다.



## 학습 진행하기

이제 학습을 진행해보자

```python
train_data = datasets.MNIST(root='./data', train=True, transform=transforms.ToTensor())
test_data = datasets.MNIST(root='./data', train=False, transform=transforms.ToTensor())


class MyModel(nn.Module):
    """MyModel 클래스 정의는 위와 동일"""
	pass

net = MyModel()
criterion = nn.CrossEntropyLoss()
optimizer = optim.Adam(net.parameters())

# training for 1 epoch
st = time.time()
print(f"training with {len(train_data)} data... ", end='')
for epoch in range(1):
    for x,y in train_data:
        y_pred = net(x[None,:]) # batch를 지정하지 않았으므로 이전과 같이 [None,:]으로 변환
        y = y[None]             # 라벨(y)도 마찬가지로 크기 1인 batch로 변환한다
        loss = criterion(y_pred, y)
        optimizer.zero_grad()
        loss.backward()
        optimizer.step()
print(f"done (elapsed {time.time() - st}s)")

# test accuracy
with torch.no_grad(): # 테스트 시에는 gradient를 계산할 필요가 없다
    acc, tot = 0, 0   # 맞은 개수, 전체 개수
    for x, y in test_data:
        y_pred = net(x[None,:]).argmax() # argmax를 이용해 가장 유력한 후보를 답으로 제시
        tot += 1
        acc += int(y_pred==y)
    print(f"test accuracy : {acc}/{tot} ({100*acc/tot}%)")
```

위 코드의 실행결과는 다음과 같다.

```
training with 60000 data... done (elapsed 70.17357993125916s)
test accuracy: 9766/10000 (97.66%)
```

1 epoch만 돌린 것 치고 생각보다 성능이 좋게 나온다(?) 실제로 MNIST는 깔끔한 데이터 특성으로 인해 모델에 따라 99% 선까지 정확도를 높일 수 있지만 일단은 여기서 만족하자.



## dataloader 사용하기

앞서 언급한 바와 같이 pytorch 모델은 단일 데이터가 아닌 데이터 batch에 대해 동작하도록 설계되었다. 이전 예시에서는 단일 데이터를 `x[None,:]`을 통해 강제로 크기 1인 batch로 바꿔줬지만 이번에는 제대로 batch 데이터를 다뤄보자.

data batch는 용어 그대로 데이터들을 묶어 세트로 만든 것이다. 예로 **[(x1, y1), (x2,y2), (x3,y3), ... ]** 로 저장된 데이터를 batch\_size=5로 정리하면 **[ [(x1,y1),...,(x5,y5)], [(x6,y6),...,(x10,y10)], [(x11,y11),...,(x15,y15)], ... ]** 와 같은 꼴이 된다. ~~이쯤 되면 당연하게도~~ pytorch에서는 이 일련의 작업을 `torch.utils.data.DataLoader`를 통해 간단히 수행할 수 있다.

```python
train_data = datasets.MNIST(root='./data', train=True, transform=transforms.ToTensor())
test_data = datasets.MNIST(root='./data', train=False, transform=transforms.ToTensor())

train_loader = torch.utils.data.DataLoader(train_data, shuffle=True, batch_size=50)
test_loader = torch.utils.data.DataLoader(test_data)
```

앞서 진행한 학습 과정은 dataloader를 이용해 아래와 같이 다시 작성할 수 있다.

```python
st = time.time()
print(f"training with {len(train_data)} data... ", end='')
for epoch in range(1):
    for x,y in train_loader:
        y_pred = net(x)      # 이젠 batch data이므로 입력에 특별한 처리가 필요하지 않다
        loss = criterion(y_pred, y)
        optimizer.zero_grad()
        loss.backward()
        optimizer.step()
print(f"done (elapsed {time.time() - st}s)")

# test accuracy
with torch.no_grad():
    acc, tot = 0, 0
    for x, y in test_loader:
        y_pred = net(x)
        # 이전과 달리 batch_size가 1이 아니므로 argmax(dim=1) 설정 필요
        # 자세한 설명은 https://pytorch.org/docs/stable/torch.html#torch.argmax 참조
        acc += (y==y_pred.argmax(1)).sum()
        tot += len(y)
    print(f"test accuracy : {acc}/{tot} ({100*acc/tot}%)")
```

위 코드의 실행결과는 다음과 같다.
```
training with 60000 data... done (elapsed 18.177398204803467s)
test accuracy : 9725/10000 (97.25%)
```

정확도 면에서는 큰 차이가 없지만 학습 시간이 급격하게(70초 → 18초) 줄어든 것을 확인할 수 있다. 



MNIST 데이터 특성상 이번에는 전체 training 데이터를사용한 1 epoch 학습으로도 상당한 정확도를 얻을 수 있었지만, 일반적으로 training 데이터를 전부 학습에 사용하면 과적합(overfitting) 문제가 발생하기 쉽다. 이를 피하기 위해 데이터를 training set / test set의 2종류 대신 training / validating set / test set의 3종류로 분리하는 방법이 잘 알려져 있으며, 이밖에 dropout layer나 data segmentation 등 다양한 기법이 존재한다.

---