---
layout: post
title:  "Google Code Jam 2019 후기"
date:   2019-06-11 20:55:07 +0900
author: nyan101
categories: 근황
tags:	대회
use_math: true
---



**TL;DR : 코드잼 티셔츠 받음**



2019년 [코드잼 본 대회](https://codingcompetitions.withgoogle.com/codejam)를 치렀다. 몇 번 글을 썼던 Kickstart와는 달리 1년에 1번밖에 열리지 않는 대회이고, 작년엔 훈련소에 있느라 참가를 못 해서인지 조금은 긴장된 마음이었다. 대학 시절 내내 코드잼, 해커컵을 통틀어 티셔츠와는 인연이 없었기에 이번에야말로 하나 받아내겠다는 생각을 했다.

<img src="/assets/images/2019/06/GCJ-main.png" width="800px">

구글 코드잼(Google Code Jam)은 이름에서처럼 구글에서 주최하는 코딩대회로 Qualification Round와 온사이트 World Final을 포함해 총 5단계로 이루어진다. World Final은 전 세계를 통틀어 상위 25명밖에 나갈 수 없어 기대조차 안했고(...) 그 이전 단계인 Round 3(세계 상위 1000명)까지를 목표로 삼았다.

<img src="/assets/images/2019/06/GCJ-result.png" width="800px">

결론부터 말하면 목표를 달성하는 데에는 성공했다. Round 3에서 395위로 티셔츠를 받을 수 있었고, World Final을 제외하면 실질적으로 인간계에서 올라갈 수 있는 마지막 라운드까지 올라간 셈이니 결과 자체로는 만족스럽다고 할 수 있다. 하지만 그와 별개로 매 라운드마다 조금씩 아쉬움이 남았는데, 특히 마지막 라운드에서는 쉽게 생각했던 문제에서 예외케이스 하나를 떠올리지 못해 대회 종료까지 수렁에서 빠져나오지 못했다. 대회가 끝나고 풀이를 들어보니 모든 문제들이 전문적인 지식을 요구하는 게 아닌, 대회 중 했던 고민들에서 조금씩 더 나아가는 풀이였기 때문에 이런 아쉬움이 더 크게 느껴졌다.

어차피 Qualification, Round 1A가 끝난지도 이제 2개월이 넘었고, 대회 사이트의 [Archive](https://codingcompetitions.withgoogle.com/codejam/archive/2019)에서 각 문제들의 풀이를 제공하고 있어 이를 다시 설명하는 건 큰 의미가 없을 것 같다. 여기서는 반성하는 의미에서 각 라운드마다 아쉬웠던 점을 요약해봤다.

### Qualification Round

* 30점 이상의 점수를 얻으면 Round 1로 진출하는 절대평가 방식. (85/100점)

[C. Cryptopangramss](https://codingcompetitions.withgoogle.com/codejam/round/0000000000051705/000000000008830b)는 간단한 수학 문제였다. 알고리즘 자체는 간단했지만 다루는 수의 범위가 커서(\\( N \leq 10^{100} \\)) 파이썬을 사용했는데, 파이썬3에서는 `/`으로 나눗셈을 하면 정수끼리의 연산에서도 실수가 반환된다는 사실을 고려하지 못해 Large 케이스에서 Runtime Error를 받았다. 대회가 끝나고 다시 코드에서 `/`를 `//`로 바꿔서 제출하니 정답이라는 판정이 나왔다(...)

### Round 1A

* 3개의 라운드(1A, 1B, 1C) 중 하나에서 1500위 이상을 달성하면 Round 2로 진출. (476위 in 1A)

다른 문제는 다 해결했는데 [A. Pylons](https://codingcompetitions.withgoogle.com/codejam/round/0000000000051635/0000000000104e03) 의 Large 케이스를 해결할 방법이 떠오르지 않았다. "내가 모르는 뭔가가 있나보다"라는 생각으로 대회 종료 후 공식 풀이를 읽어보니 다음 문구를 발견할 수 있었다.

> _we can rely on our occasional friend, randomness! (...) Many problems cannot be approached with random or brute-force solutions, but identifying the problems that can be (in Code Jam or the real world) is a useful skill!_

.....게임 형식의 문제에서 난수를 통해 확률적으로 해결하는 건 봤어도 공식 대회의 input/output이 명확한 문제에서 랜덤을 풀이로 제시하는 건 약간 놀라웠다. 풀지 못했던 문제의 해설을 보면서 새로운 걸 배울 수 있을거라 생각했기에 조금 실망스러웠다.

### Round 2

* Round 2 참가자들 중 상위 1000명이 Round 3에 진출. (724위)

무려 16번이나 제출을 시도한 [B. Pottery Lottery](https://codingcompetitions.withgoogle.com/codejam/round/0000000000051679/00000000001461c8) 문제이다. 인터렉티브 문제였는데 컴퓨터와 1:1 게임을 해서 90% 이상 승리하면 되는 확률적인 문제였다. 나름 그럴듯한 전략을 짰다고 생각했는데 막상 제출하니 Wrong Answer를 받았다. 이후 대전략은 그대로 두고 계속해서 세부 파라미터를 조금씩 수정하면서 제출했지만 결과는 끝까지 WA였다. 그런데 대회가 끝나고 공개된 풀이를 보니 생각했던 전략과 동일한 방식이었다. 어디에서 잘못됐는지 천천히 코드를 복기하던 중 Min Heap(루트가 최소 원소인 힙)을 써야 하는 자리에 C++의 `priority_queue` STL을 사용해 Max Heap(루트가 최대 원소인 힙)이 들어간 것을 깨닫고 이를 수정하니 정답 판정을 받았다(...)

### Round 3

* Round 3 참가자들 중 상위 25명이 World Final에 초청됨. (395위)

Qualification Round, Round 1A에서의 아쉬움이 <u>"다 맞게 풀어놓고 끝에 가서 멍청한 실수를 한 아쉬움"</u>이라면 Round 3에서의 아쉬움은 <u>"충분히 고민하지 못했던 것에 대한 아쉬움"</u>에 더 가깝다. 대회 중 B Small을 해결하고 다른 문제들을 읽어보니 [D. Napkin Folding](https://codingcompetitions.withgoogle.com/codejam/round/0000000000051707/0000000000159170)의 Small 케이스는 손쉽게 해결할 수 있어보였다. 그렇지만 자명해 보이는 알고리즘이 계속해서 Runtime Error를 발생시켰고, "뭔가 사소한 실수 하나만 고치면 될거같은데"라는 생각에 끝까지 손을 놓지 못했다. 결국 어떤 경우를 잘못 생각했는지 깨달았지만[^1] 이미 대회가 거의 끝나가는 시점이었고, 조급한 마음에서였는지 제대로 수정하지 못했다. 다른 문제들이 어려운 고급 알고리즘보다는 적절한 착안점을 발견하면 그 다음부터는 비교적 손쉽게 풀리는 것들이었기에 아쉬움이 느껴졌다.

물론 처음에 D가 아닌 다른 문제를 잡았다고 해서 대회 시간 내에 풀어냈을 것이란 보장은 없다. 그런 만큼 "만약 그랬다면 더 좋은 결과였을지도 모른다"라는 생각은 굳이 하지 않기로 했다. 다만 같은 문제를 고민하더라도 대회가 끝난 후 아무런 제약 없이 생각해보는 것과 대회 진행중에 긴장된 상태로 집중하는 건 큰 차이가 있고, 후자의 경험은 대회가 끝나면 다시 겪어보기 힘들다는 점이 약간은 미련으로 남았다.



---
[^1]: 한 직선 위에 셋 이상의 점이 존재해도 Simple Polygon이라는 조건을 만족시킬 수 있음

