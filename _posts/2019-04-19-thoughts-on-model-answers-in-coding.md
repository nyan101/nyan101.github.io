---
layout: post
title:  "코딩에서 답지를 보는것에 대한 개인적인 생각"
date:   2019-04-19 12:34:51 +0900
author: nyan101
categories: 잡담
tags:	[잡담]
use_math: true
---



\* 개인 페이스북 타임라인에 썼던 내용을 다듬어 업로드한 글입니다.

### 알고리즘(PS)을 공부하는 법

인터넷을 보면 종종 "알고리즘 잘 하는 법(or알고리즘 문제 잘 푸는 법)"에 대한 질문글이 올라오고, 많은 경우 "모르겠다고 답지를 보지 말고 혼자서 끝까지 고민해봐야 한다"라는 답변이 주를 이룬다.

개인적으로 이 말에 동의하지 않는다. 연구를 진행하는 거라면 몰라도 문제풀이에 있어서는 모르면 풀이를 봐야 한다고 생각한다. 사람마다 "풀이를 본다"라는 말의 두 가지 해석이 있을 수 있다.

* 말로 된 알고리즘 풀이를 보고, 스스로의 힘으로 구현해본다 (1)

* 고수가 짠 정답 소스코드(a.k.a. '답지')를 본다 (2)

(1)에 대해서도 좋지 않게 보는 사람들이 있는데, 이에 대해서는 이미 많은 실력자 분들께서 좋은 글들을 작성한 바 있다. 한번쯤 읽어보면 좋은 글들을 아래에 첨부했다. ~~어째 나열하고 보니 사실상 PS계 이름쌓기~~

* bactree님의 ["알고리즘 공부, 어떻게 해야하나요?"](https://baactree.tistory.com/52)
* koosaga님의 ["내가 문제풀이를 연습하는 방법"](https://koosaga.com/217)
* subinium님의 ["PS를 공부하는 방법 (How to study Problem Solving?)"](https://subinium.github.io/how-to-study-problem-solving/)
* wookje님의 ["[잡담] 내가 알고리즘을 공부하는 방법"](http://wookje.dance/2019/04/16/how-to-study-algorithm/)



### 코딩에서 '답지'를 보는것에 대한 개인적인 생각

여기서는 (2)에 대해 말해보자. 많은 사람들이 (1)의 장점은 받아들이면서도 (2)는 치팅과 다를 바 없다고 여기는 것 같다. 하지만 개인적인 생각을 말하자면, 적어도 초급→중급 단계로 넘어가는 시점에 있어서는 (2)의 중요성을 무시할 수 없다. 학부 수업에서 다루는 기초적인 자료구조(스택, 큐, 힙)를 통해 알아보자.

아래에 max 힙에서 최대 원소를 삭제하는 pop함수의 두 가지 구현을 작성했다. 이진 힙의 구조나 각 연산의 알고리즘에 대해서는 크게 바뀔 여지가 없다. 가장 끝 원소를 루트(배열의 1번)로 옮기고, 옮겨진 1번 원소가 제자리를 찾아가도록 바꾸면 된다.

이진 힙의 제약은 "부모는 자식보다 커야 한다" 하나밖에 없고, 완전이진트리라는 특성상 자식 노드의 인덱스를 구하기도 쉽다. 하지만 막상 구현해보면 고려해야할 요소가 꽤 많다는 것을 알 수 있다. 구체적으로는 idx번 노드를 기준으로 다음과 같이 나뉜다.

0. 왼쪽 자식이 없는 경우
   : 이 경우 힙의 구조상 오른쪽 자식도 존재할 수 없고, 그대로 루프가 끝난다.

1. 오른쪽 자식이 존재하고, 오른쪽 자식이 왼쪽보다 큰 경우
   : 오른쪽 자식(idx\*2+1)과 현재 노드(idx)를 비교해 처리한다.

2. 오른쪽 자식이 존재하지만, 왼쪽 자식이 오른쪽보다 큰 경우
   : 왼쪽 자식(idx\*2)과 현재 노드(idx)를 비교해 처리한다.

3. 오른쪽 자식이 없이 왼쪽만 있는 경우
   : 왼쪽 자식(idx\*2)과 현재 노드(idx)를 비교해 처리한다.

각 경우를 '정직하게'(or 우직하게) 나눠서 구현하면 아래 코드가 나온다.  `heap[]` 배열은 힙의 정보를, `hsize`는 힙의 크기를 담고있는 변수이다.

```c++
void pop1()
{
    int idx = 1; heap[1] = heap[hsize--];
    while(idx*2 <= hsize)
    {
        if(idx*2 + 1 <= hsize)
        {
            if(heap[idx*2] < heap[idx*2+1])
            {
                if(heap[idx*2+1] > heap[idx])
                {
                    swap(heap[idx*2+1], heap[idx]);
                    idx = idx*2 + 1;
                }
                else
                    break;
            }
            else
            {
                if(heap[idx*2] > heap[idx])
                {
                    swap(heap[idx*2], heap[idx]);
                    idx = idx*2;
                }
                else
                    break;
            }
        }
        else
        {
            if(heap[idx*2] > heap[idx])
            {
                swap(heap[idx*2], heap[idx]);
                idx = idx*2;
            }
            else
                break;
        }
    }
}
```

코드의 동작이라는 측면에서 보면 이 코드에 문제는 없다. 연산 전후에 힙의 성질을 유지하고, 가능한 모든 경우를 빠짐없이 체크했으며, 시간복잡도 면에서도 낭비 없는 \\(O(\\log N)\\)이다.

이제 아래의 `pop2`를 보자. `pop1`과 동일한 알고리즘으로 매 루프에서 정확히 동일한 동작을 수행한다.

```c++
void pop2()
{
    int idx = 1; heap[1] = heap[hsize--];
    while(idx*2 <= hsize)
    {
        int child = idx*2;
        if(idx*2+1 <= hsize && heap[idx*2] < heap[idx*2+1])
            child = idx*2+1;

        if(heap[child] < heap[idx])
            break;

        swap(heap[child], heap[idx]);
        idx = child;
    }
}
```

이 둘 중 과연 어느 쪽이 '좋은' 코드일까? 개인적으로는 `pop2`가 `pop1`보다 좋은 코드라고 생각한다.

물론 혼자 많은 코드를 작성해보면서 점차 발전해가는 경우도 존재한다. 하지만 `pop1`에서 `pop2`로의 발전은 \\(O(N^2)\\)에서 \\(O(N\\log N)\\) 알고리즘으로 발전하는 과정과는 다르다. \\(O(N\\log N)\\)을 요구하는 문제에서 \\(O(N^2)\\) 알고리즘을 구현했다면 '틀린' 코드겠지만, 이 경우 양쪽 모두 '맞는' 코드이고 거의 모든 상황[^1]에서 `pop1`은 `pop2`와 동일한 수준의 결과물로 인정받을 것이다. '틀린 부분'이 없으므로 지적받을 일도 없고, 특별히 관심을 가지지 않는다면 자발적으로 개선될 가능성도 낮다. 실제로 학부에서 첫 프로그래밍을 접한 동기들이 작성한 코드는 대체로 `pop1`과 비슷했다.

[^1]: 코드를 직접 보고 평가하는 심층면접 등 극히 일부를 제외한

문법에 어느정도 익숙해졌다면 "말로 서술된 지시사항을 하나하나 코드로 옮기는" 것은 어려운 일이 아니다. 여기서 더 발전하기 위해서는 많은 알고리즘을 아는 것과 함께 '좋은 코드'에 대한 감각을 길러야 한다. 그런 의미에서 PS는 실무 개발에 비하면 비교적 짧은 분량에, 동일한 로직을 가지는 소위 '모범적인' 코드를 접할 수 있는 좋은 환경이다.

아직 'IT현업'이라고 하기엔 민망하고, 이렇다 할 경력도 없는 사람이 하기엔 부적절한 발언일 수 있다. 하지만 이런 "좋은 코드를 접하고, 그에 가까워질 수 있는 기회가 많다"라는 장점을 활용하지 않는 건, PS에서 얻을 수 있는 상당히 큰 소득을 포기하는 것이라고 생각한다. **같은 알고리즘이라고 같은 코드가 되는 건 아니다.** 모르면 답지를 보고, 알아도 미심쩍다 싶으면 답지를 보는 게 좋다(...)



### 답안지 족보는 어디에 있는가

이렇게까지 써뒀으면 "그럼 그 좋은 코드들은 어디서 볼 수 있는데?" 라는 질문에도 간단하게나마 답변을 하는 게 예의인 것 같다. 개인적으로는 다음과 같은 코드를 참조한다.


* [**Ries 마법의 슈퍼마리오(kks227님 블로그)**](https://blog.naver.com/PostList.nhn?blogId=kks227&categoryNo=299) 
  : **대회알고리즘** 카테고리에 들어가면 큐나 스택, BFS/DFS 등 기초 알고리즘에서 시작해 HLD나 BCC, 최대 유량과 같은 고급 기법들까지 상세하게 정리된 포스팅을 볼 수 있다. 각 알고리즘의 원리와 함께 kks227님 본인의 예제코드, 관련 연습문제들까지 잘 정리되어 있어 혼자서 PS를 공부하는 사람에게 강력히 추천한다.
* Codeforces의 Editorial
  : 매 라운드가 끝나고 제공되는 Editorial에서는 글로 된 알고리즘 풀이와 함께 공식 솔루션을 코드로 올려주는 경우가 많다. 비교적 낭비가 없고 간결한 코드가 대부분이다.
* 믿고 보는 OOO님 코드
  : 코드포스에서는 라운드에 참가한 다른 사람의 코드를 볼 수 있다. 스코어보드에서 몇 가지 코드를 훑어보고 본인 스타일에 가장 잘 맞는 한두 사람을 친구로 추가해, 같은 문제를 어떻게 코딩했는지 살펴보는 것도 도움이 된다. ~~TIP: 열어봤는데 코드에 #define이 5개 이상 있으면 일단 걸러라~~
* ICPC 팀노트 (애매함)
  : ICPC 팀노트를 인터넷에 공유하는 팀들이 있다. 충분히 성능이 검증된 코드이고, 팀노트 특성상 타이핑 수가 적고 간결한/깔끔한 코드들이 많다. 하지만 역으로 성능에 올인한 나머지 온갖 트릭들을 섞어놓는 경우도 있어 무조건적으로 본받는건 그다지 권장하지 않는다.

---

