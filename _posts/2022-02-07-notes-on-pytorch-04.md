---
layout: post
title:	"[PyTorch] PyTorch 사용법 정리 - train_model() 함수 제작"
date:	2022-02-07 20:38:11
author: nyan101
categories: 자습
tags:	[전산, 개발]
use_math: true
---



~~굉장히 오랜만에 이어지는 포스팅이다...~~

## Training & Validation

[이전 글](https://nyan101.github.io/blog/notes-on-pytorch-03)에서 작성했던 마지막 코드를 다시 살펴보자

```python
# 모델 생성 및 설정
net = MyModel()
criterion = nn.CrossEntropyLoss()
optimizer = optim.Adam(net.parameters())

# 데이터 로드
train_data = torchvision.datasets.MNIST(root='./data', train=True, transform=transforms.ToTensor())
test_data = torchvision.datasets.MNIST(root='./data', train=False, transform=transforms.ToTensor())

# dataloader에 적재
train_loader = torch.utils.data.DataLoader(train_data, shuffle=True, batch_size=50)
test_loader = torch.utils.data.DataLoader(test_data)

# 학습(training) 진행
st = time.time()
print(f"training with {len(train_data)} data... ", end='')
for epoch in range(1):
    for x,y in train_loader:
        y_pred = net(x)
        loss = criterion(y_pred, y)
        optimizer.zero_grad()
        loss.backward()
        optimizer.step()
print(f"done (elapsed {time.time() - st}s)")

# 검증(test) 진행
with torch.no_grad():
    acc, tot = 0, 0
    for x, y in test_loader:
        y_pred = net(x)
        acc += (y==y_pred.argmax(1)).sum()
        tot += len(y)
    print(f"test accuracy : {acc}/{tot} ({100*acc/tot}%)")
```

마지막 테스트 전 학습에서는 고정된 epoch의 학습을 무작정 진행했다. 그러나 모델을 본격적으로 학습시키기 위해서는 학습 과정에서 training loss를 계산하거나 주기적으로 validation을 진행하는 등, 학습의 진행도를 추적하기 위해 다양한 절차를 추가하는 경우가 많다. 여기서는 `학습 진행` 단계에 다음 두 작업을 추가하고자 한다.

* validation phase 추가
* train/val 단계마다 평균 손실(loss와)과 평균 정확도(acc) 계산



## `dataloaders_dict` 작성

이전에는 train용 dataloader와 test용 dataloader를 별도로 관리했다. 그러나 관리의 편의성을 위해 둘을 dict로 모아 관리하는 방법이 자주 사용된다. 이는 이후 다른 글에서 다룰 `torchvision.transforms`의 활용에 있어서도 동일하다. 다음 작업을 수행하자.

* `train_data`에서 일정 비율(80%)을 떼 train용으로, 나머지를 val용으로 분리한다
* 각 데이터셋을 `data.Dataloader`를 이용해 dataloader로 만든다
* 두 dataloader를 적절한 키(`'train'`, `'val'`)와 함께 dictionary에 등록한다

이를 코드로 작성하면 다음과 같다.

```python
import torch.utils.data as data
import torchvision
from torchvision import transforms

# 본 포스팅에서는 RGB채널이 모두 있는 CIFAR10 데이터셋을 사용한다
train_data = torchvision.datasets.CIFAR10(
  root='./data', download=True, train=True, transform=transforms.ToTensor()
)

train_size = int(len(train_data)*0.8) # 전체의 80%를 학습용으로 사용
val_size = len(train_data) - train_size
train_dataset, val_dataset = data.dataset.random_split(train_data, [train_size, val_size])

dataloaders_dict = {
  'train' : data.DataLoader(train_dataset, shuffle=True, batch_size=50),
  'val' : data.DataLoader(val_dataset, batch_size=50)
}
```

이제 `dataloaders_dict['train']`, `dataloaders_dict['val']`를 통해 각 phase용 dataloader에 접근할 수 있다.



## `train_model()` 함수 작성

이제 validation phase를 추가해 `train_model()` 함수를 작성하자. 수행할 작업은 다음과 같다

* 사용 가능한 device를 인식하고 모델을 변환
* 각 epoch마다 train, val 과정 수행
  * phase(`'train'`, `'val'`)에 따라 `model.train()`, `model.eval()` 모드 변경

* train phase에서는 파라미터 업데이트를 위해 gradient 계산 활성화
  * `loss.backward()`로 backpropagation 수행
  * `optimizer.zero_grad()`, `optimizer.step()` 수행
* val phase에서는 gradient 계산 비활성화(불필요한 계산 방지)
* 각 epoch, phase마다 loss, acc 출력

이를 코드로 작성하면 다음과 같다.

```python
def train_model(net, criterion, optimizer, dataloaders_dict, num_epochs):
    # 사용 가능한 device 인식(GPU가 있으면 GPU 사용)
    device = 'cuda' if torch.cuda.is_available() else 'cpu'
    net.to(device)
    print(f"Using device: {device}")
    
    # train & val 전체 진행루틴
    for epoch in range(num_epochs):
        print("-----------------")
        print(f"> Epoch {epoch+1}/{num_epochs}")
        # 각 epoch마다 'train', 'val'을 모두 진행
        for phase in ['train', 'val']:
            # 현재 phase에 따라 모델의 상태 변경
            if phase == 'train':
                net.train()
            else:
                net.eval()
            # 첫 epoch에서는 validation만 수행(초기 상태의 성능 측정 목적)
            if (epoch == 0) and (phase == 'train'):
                continue
            # 매 epoch마다 loss(손실), correct(맞은 개수)를 기록
            epoch_loss = 0.0
            epoch_corrects = 0
            # tqdm : 진행바(progress bar)를 표시하기 위한 라이브러리
            for x,y in tqdm(dataloaders_dict[phase]):
                x = x.to(device)
                y = y.to(device)
                # train phase일 때만 gradient 계산
                with torch.set_grad_enabled(phase == 'train'):
                    output =  net(x)
                    loss = criterion(output, y)
                    # train phase일 때만 loss값을 기반으로 파라미터 갱신
                    if phase == 'train':
                        optimizer.zero_grad()
                        loss.backward()
                        optimizer.step()
                    # loss, correct 계산
                    _, y_pred = torch.max(output, 1)
                    epoch_loss += loss.item() * x.size(0) # size(0): 해당 batch의 size
                    epoch_corrects += torch.sum(y_pred == y.data)
            # epoch이 끝난 후 해당 epoch에서의 평균 손실, 정확도 계산 및 출력
            epoch_loss = epoch_loss / len(dataloaders_dict[phase].dataset)
            epoch_acc = epoch_corrects.double() / len(dataloaders_dict[phase].dataset)
            print(f"{phase} Loss: {epoch_loss:.4f}  Acc: {epoch_acc:.4f} ({epoch_corrects}/{len(dataloaders_dict[phase].dataset)})")
```



## 모델 학습 진행

앞서 작성한 함수들을 이용해 모델 학습을 진행해보자. 편의상 별도 모델 클래스를 만드는 대신 `torchvision.models`의 `resnet18`을 사용했다.

```python
import torch
import torch.nn as nn
import torch.optim as optim
import torch.utils.data as data
import torchvision
from torchvision import models, transforms

"""
앞서 작성한 dataloaders_dict, train_model 코드 생략
"""

# resnet18 모델에서 마지막 output layer만 변경한다(총 10개의 label)
net = models.resnet18()
net.fc = nn.Linear(in_features=net.fc.in_features, out_features=10)

# criterion, optimizer 설정
criterion = nn.CrossEntropyLoss()
optimizer = optim.Adam(params = net.parameters())

# 학습 진행
train_model(net, criterion, optimizer, dataloaders_dict, num_epochs=5)
```

이를 실행하면 다음과 같은 출력을 볼 수 있다.(`tqdm`을 통해 학습이 진행되는 동안 진행상태를 볼 수 있다)

```
Using device: cuda
-----------------
> Epoch 1/5
100%|██████████| 200/200 [00:05<00:00, 34.14it/s]
val Loss: 2.3033  Acc: 0.1043 (1043/10000)
-----------------
> Epoch 2/5
100%|██████████| 800/800 [00:59<00:00, 13.52it/s]
train Loss: 1.4675  Acc: 0.4736 (18944/40000)
100%|██████████| 200/200 [00:04<00:00, 42.41it/s]
val Loss: 1.2823  Acc: 0.5465 (5465/10000)
-----------------
> Epoch 3/5
100%|██████████| 800/800 [00:59<00:00, 13.53it/s]
train Loss: 1.0625  Acc: 0.6243 (24970/40000)
100%|██████████| 200/200 [00:04<00:00, 42.35it/s]
val Loss: 1.1661  Acc: 0.5980 (5980/10000)
-----------------
> Epoch 4/5
100%|██████████| 800/800 [00:59<00:00, 13.52it/s]
train Loss: 0.8876  Acc: 0.6887 (27547/40000)
100%|██████████| 200/200 [00:04<00:00, 42.33it/s]
val Loss: 1.0737  Acc: 0.6208 (6208/10000)
-----------------
> Epoch 5/5
100%|██████████| 800/800 [00:59<00:00, 13.50it/s]
train Loss: 0.7564  Acc: 0.7349 (29394/40000)
100%|██████████| 200/200 [00:04<00:00, 42.28it/s]
val Loss: 0.9722  Acc: 0.6625 (6625/10000)
```



---
