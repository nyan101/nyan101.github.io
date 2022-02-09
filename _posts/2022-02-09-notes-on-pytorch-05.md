---
layout: post
title:	"[PyTorch] 05. data.Dataset으로 나만의 Dataset 클래스 만들기"
date:	2022-02-08 18:53:27
author: nyan101
categories: 자습
tags:	[전산, 개발]
use_math: true
---



## 자체 Dataset 클래스의 필요성

지금까지의 실습에서는 `torchvision.datasets`에서 제공하는 데이터셋을 사용했다. `torchvision` 라이브러리는 vision과 관련된 약 30여개의 데이터셋을 제공하며, 전체 목록은 [공식 홈페이지](https://pytorch.org/vision/stable/datasets.html)에서 확인할 수 있다.

그러나 실습이나 연구를 진행하다 보면, 기존에 잘 알려진 데이터셋 외에 자신만의 데이터로 학습을 진행해야 하는 상황이 자주 발생한다. 이를 위해 `torch.utils.data.dataloader`에 넘길 수 있는 나만의 `Dataset` 객체를 만드는 법을 알아보자.



### 방법 1. torchvision.datasets.ImageFolder() 이용

이미지 데이터의 경우 `torchvision.datasets.ImageFolder()` 함수를 이용해 간단히 처리 가능하다. 각 이미지 파일들이 다음과 같은 구조로 정리되어 있다고 가정하자.

```
data/dog/xxx.png
data/dog/xxy.png
data/dog/[...]/xxz.png

data/cat/123.png
data/cat/nsdf3.png
data/cat/[...]/asd932_.png
```

이렇게 이미지 파일들이 `..[공통경로]/[라벨명]/[파일명]`으로 정리된 구조를 가질 때, 다음과 같은 코드로 손쉽게 dataset 객체를 생성할 수 있다.

```python
import torchvision
from torchvision import transforms

# transforms.toTensor()보다 조금 더 세부적인 전처리 수행
data_transform = transforms.Compose([
    transforms.Resize(resize),
    transforms.CenterCrop(resize),
    transforms.ToTensor(),
    transforms.Normalize(mean, std)
])

# ./data 아래의 파일을 재귀적으로 읽어 폴더명(label)에 맞게 dataset 객체를 생성한다.
train_data = torchvision.datasets.ImageFolder(root='./data', transform=data_transform)

# 이후는 이전 포스팅에서의 코드와 동일하다
train_size = int(len(train_data)*0.8)
val_size = len(train_data) - train_size
train_dataset, val_dataset = data.dataset.random_split(train_data, [train_size, val_size])

dataloaders_dict = {
  'train': data.DataLoader(train_dataset, shuffle=True, batch_size=50),
  'val': data.DataLoader(val_dataset, batch_size=50)
}
```

이렇듯 일반적인 이미지 파일에 대한 실습은 `ImageFolder()` 함수로 충분하다. 그러나 train, val 과정에 서로 다른 전처리를 적용하거나 데이터파일의 폴더 구조가 복잡한 구성을 가지는 등, 좀더 세부적인 작업을 필요로 하는 경우 다음과 같이 `torch.data.Dataset` 클래스를 직접 구현해야 한다.



## 방법 2. torch.data.Dataset 클래스 작성

여기서는 torchvision이 아닌 torch에서 제공하는 클래스를 통해 `torch.data.Dataset` 클래스를 직접 작성해보기로 하자. Dataset 클래스는 크게 다음과 같은 메소드를 가진다

* `__init__(self)` : 초기화 함수
* `__len__(self)` : 전체 데이터셋의 개수를 리턴하는 함수
* `__getitem(self, idx)__` : idx번째 데이터를 (x, y) 형태의 tuple로 리턴하는 함수. 이때 x, y는 `torch.Tensor()`, 혹은 텐서로 변환될 수 있는 대상이어야 한다.

이를 구현해보자. 우리가 만들 Dataset 클래스는 다음 기능을 가진다.

* 데이터 파일 경로들의 리스트(path\_list)를 받아 관리
* 현재 데이터셋이 어떤 phase('train', 'val')에 사용되는지 관리
* 적용중인 phase에 따라 서로 다른 로직 사용

이를 코드로 작성하면 아래와 같다. `transforms_dict`가 사용되는 방식에 유의하자.

```python
import torch.utils.data as data
from torchvision import transforms
from PIL import Image

class MyDataset(data.Dataset):
    def __init__(self, path_list, phase='train'):
        self.path_list = path_list
        self.phase = phase

        # phase에 따라 서로 다른 전처리(transform) 적용
        img_size = 224
        img_mean = (0.485, 0.456, 0.406)
        img_std = (0.229, 0.224, 0.225)
        self.transforms_dict = {
            'train' : transforms.Compose([
                # data augmentation을 위한 random 변환을 추가
                transforms.RandomResizedCrop(img_size, scale=(1.0, 1.0)),
                transforms.RandomHorizontalFlip(),
                transforms.ToTensor(),
                transforms.Normalize(img_mean, img_std)
            ]),
            'val' : transforms.Compose([
                transforms.Resize(img_size),
                transforms.CenterCrop(img_size),
                transforms.ToTensor(),
                transforms.Normalize(img_mean, img_std)
            ])
        }
        
        # 문자열로 된 label들을 int로 바꾸기 위한 dict. 일관성을 위해 sorted 사용
        labels = sorted(list({ path.split('/')[-2] for path in path_list }))
        self.label_to_idx = { label : idx for idx,label in enumerate(labels) }
    
    def __len__(self):
        return len(self.path_list)
    
    def __getitem__(self, idx):
        img_path = self.path_list[idx] # idx번째 경로명을 가져오고
        img = Image.open(img_path) # 해당 경로에서 이미지 파일을 읽어들여
        img_transformed = self.transforms_dict[self.phase](img) # 적절한 전처리를 적용하고
        label_idx = self.label_to_idx[img_path.split('/')[-2]] # 라벨명을 식별한다
        
        return img_transformed, label_idx

```

이렇게 만들어진 MyDataset 클래스는 다음과 같이 사용할 수 있다.

```python
from glob import glob

# 해당 데이터는 https://download.pytorch.org/tutorial/hymenoptera_data.zip 에서 받을 수 있다
train_path_list = glob.glob("./data/hymenoptera_data/train/*/*")
train_dataset = MyDataset(path_list=train_path_list, phase='train')

val_path_list = glob.glob("./data/hymenoptera_data/val/*/*")
val_dataset = MyDataset(path_list=val_path_list, phase='val')

# DataLoader 설정
batch_size = 16
train_dataloader = torch.utils.data.DataLoader(train_dataset, batch_size=batch_size, shuffle=True)
val_dataloader = torch.utils.data.DataLoader(val_dataset, batch_size=batch_size, shuffle=False)

dataloaders_dict = {'train' : train_dataloader, 'val' : val_dataloader}
```

간단한 경우는 `torchvision.datasets.ImageFolder()`를, 데이터에 복잡한 전처리나 추가적인 작업이 필요한 경우 `torch.data.Dataset` 클래스를 직접 만들어 사용하는 것이 좋다.

 

---

