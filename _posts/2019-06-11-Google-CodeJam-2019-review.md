---
layout: post
title:  "Google Code Jam 2019 후기"
date:   2019-06-11 20:55:07
author: nyan101
categories: 근황
tags:	대회
use_math: true
---

2019년 [코드잼 본 대회](https://codingcompetitions.withgoogle.com/codejam)를 치렀다. 몇 번 글을 썼던 Kickstart와는 달리 1년에 1번밖에 열리지 않는 대회이고, 작년엔 훈련소에 있느라 참가를 못 해서인지 조금은 긴장된 마음이었다. 대학 시절 내내 코드잼, 해커컵을 통틀어 티셔츠와는 인연이 없었기에 이번에야말로 하나 받아내겠다는 생각을 했다.

<img src="/assets/images/2019/06/GCJ-main.png" width="800px">

구글 코드잼(Google Code Jam)은 이름에서처럼 구글에서 주최하는 코딩대회로 Qualification Round와 온사이트 World Final을 포함해 총 5단계로 이루어진다. World Final은 전 세계를 통틀어 상위 25명밖에 나갈 수 없어 기대조차 하지 못했고(...) 그 이전 단계인 Round 3(세계 상위 1000명)까지를 목표로 삼았다.

<img src="/assets/images/2019/06/GCJ-result.png" width="800px">

결론부터 말하면 목표를 달성하는 데에는 성공했다. Round 3에서 395등으로 티셔츠를 받을 수 있었고, World Final을 제외하면 실질적으로 인간계에서 올라갈 수 있는 마지막 라운드까지 올라간 셈이니 결과 자체로는 만족스럽다고 할 수 있다. 하지만 그와 별개로 매 라운드마다 조금씩 아쉬움이 남았고, 특히 마지막 라운드에서는 쉽게 생각했던 문제에서 예외케이스 하나를 떠올리지 못해 대회 종료까지 수렁에서 빠져나오지 못했다. 대회가 끝나고 풀이를 들어보니 모든 문제들이 전문적인 지식을 요구하는 게 아닌, 대회 중 했던 고민들에서 조금씩 더 나아가는 풀이였기 때문에 이런 아쉬움이 더 크게 느껴졌다.

어차피 Qualification, Round 1A가 끝난지도 이제 2개월이 넘었고, 대회 사이트의 [Archive](https://codingcompetitions.withgoogle.com/codejam/archive/2019)에서 각 문제들의 풀이를 제공하고 있어 이를 다시 설명하는 건 큰 의미가 없을 것 같다. 여기서는 반성하는 의미에서 각 라운드마다 아쉬웠던 점을 요약해봤다.

### Qualification Round

[C. Cryptopangramss](https://codingcompetitions.withgoogle.com/codejam/round/0000000000051705/000000000008830b)는 간단한 수학 문제였다. 알고리즘 자체는 간단했지만 다루는 수의 범위가 커서(\\( N \leq 10^{100} \\)) 파이썬을 사용했는데, 파이썬3에서는 `/`으로 나눗셈을 하면 정수끼리의 연산에서도 실수가 반환된다는 사실을 고려하지 못해 Large 케이스에서 Runtime Error를 받았다. 대회가 끝나고 다시 코드에서 `/`를 `//`로 바꿔서 제출하니 정답이라는 판정이 나왔다(...)

### Round 1A

다른 문제는 다 해결했는데 [A. Pylons](https://codingcompetitions.withgoogle.com/codejam/round/0000000000051635/0000000000104e03) 의 Large 케이스를 해결할 방법이 떠오르지 않았다. "내가 모르는 뭔가가 있나보다"라는 생각으로 대회 종료 후 공식 풀이를 읽어보니 다음 문구를 발견할 수 있었다.

> _we can rely on our occasional friend, randomness! (...) Many problems cannot be approached with random or brute-force solutions, but identifying the problems that can be (in Code Jam or the real world) is a useful skill!_

.....랜덤 알고리즘을 낮춰서 보는 건 아니지만 저런 해설을 읽으니 조금 허탈했다.

### Round 2

무려 16번이나 제출을 시도한 [B. Pottery Lottery](https://codingcompetitions.withgoogle.com/codejam/round/0000000000051679/00000000001461c8) 문제이다. 인터렉티브 문제였는데 컴퓨터와 1:1 게임을 해서 90% 이상 승리하면 되는 확률적인 문제였다. 나름 그럴듯한 전략을 짰다고 생각했는데 막상 제출하니 Wrong Answer를 받았다. 이후 대전략은 그대로 두고 계속해서 세부 파라미터를 조금씩 수정하면서 제출했지만 결과는 끝까지 WA였다. 그런데 대회가 끝나고 공개된 풀이를 보니 생각했던 전략과 동일한 방식이었다. 천천히 코드를 복기하던 중 Min Heap(루트가 최소 원소인 힙)을 써야 하는 자리에 C++의 `priority_queue` STL을 사용해 Max Heap(루트가 최대 원소인 힙)이 들어간 것을 깨달았다. 다시 이를 수정하니 정답(...)

### Round 3

Qualification Round, Round 1A에서의 아쉬움이 "다 맞게 풀어놓고 끝에 가서 멍청한 실수를 한 아쉬움"이라면 Round 3에서의 아쉬움은 "충분히 고민하지 못했던 것에 대한 아쉬움"에 더 가깝다.