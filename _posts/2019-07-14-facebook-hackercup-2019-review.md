---
layout: post
title:  "Facebook Hacker Cup 2019 후기"
date:   2019-07-14 16:09:22
author: nyan101
categories: 근황
tags:	대회
use_math: true
---



**TL;DR : 아무래도 페이스북 티셔츠와는 연이 없는 모양이다(...)**



[2018년 해커컵](https://nyan101.github.io/blog/facebook-hackercup-2018-review)에 이어 2019년도 페이스북 해커컵 대회가 열렸다. 이번에는 지난번같은 실수 없이 티셔츠, 운이 좋다면 Round 3까지 진출하는 걸 목표로 삼았지만 결국 달성하지 못했다. 일요일 새벽 2시에 열리는 Round 2를 위해 토요일 저녁에 미리 잠들고, 알람까지 맞춰놨지만 눈을 뜨니 2시 23분이었고 급하게 노트북을 켰지만 이미 대회 시작에서 30분이 지난 상황이었다.

비몽사몽한 정신을 붙들고 문제를 풀어봤지만 2문제를 풀고나니 3,4번째 문제에서 아이디어를 구체화시키지 못했고, 결국 549등이라는 아쉬운 등수 - 500등까지 기념 티셔츠를 제공한다 - 로 대회를 끝마칠 수밖에 없었다. 30분 핸디캡이 없었다면 무난히 티셔츠를 받았을거라는 계산과~~(실제로 그렇다)~~ 왜 알람을 못 들었을까라는 자책(?) 등 다양한 생각이 들지만 막상 당시엔 다시 침대에 가 눕겠다는 생각이 주를 차지했던 것 같다..

각 라운드를 간단히 요약해봤다.

## Qualification Round

* 1문제 이상을 통과하면 Round 1로 진출. (55/100점)

<img src="/assets/images/2019/07/hackercup-Qual-scoreboard.png" width="800px">

문제 자체는 간단했다. 파이썬 라이브러리를 적절히 사용했다면 입력받는 부분을 제외하고 1,2줄 내로 작성 가능할 정도였지만 해커컵의 특징 - 구글 코드잼은 Small / Large로 나눠 Small의 정답 여부를 바로 알려주고 재시도가 가능하지만, 해커컵은 오직 1번만 제출 가능하고 제출한 후에도 대회 종료까지 정답/오답 여부를 알려주지 않는다 - 으로 인해 안전하게 3개 문제를 코딩해 제출했다. 결과는 3개 모두 정답으로 R1 진출.



## Round 1

* 30점 이상을 달성하면 Round 2로 진출 (65/100점)

<img src="/assets/images/2019/07/hackercup-R1-scoreboard.png" width="800px">

절대평가로 등수와 크게 관련은 없지만 D번 문제에서 저질렀던 실수가 아쉬운 라운드이다. 앞선 A,B,C 3개 문제를 해결하고 이어진 D에서 나름 깔끔한 풀이를 찾았는데, 다음 두 쿼리를 해결해야 했다.

1. 저장소에 정수 x를 추가
2. 저장소에서 k번째로 큰 수를 탐색

균형이진트리를 직접 구현할 경우 \\(O(\\log N)\\), 좌표압축과 펜윅트리를 조합하면 \\(O(\\log^2 N)\\) 복잡도로 해결 가능한 쿼리들이었지만 ~~코딩이 귀찮아서~~ 좀더 간단히 작성할 수 있는 방법을 찾았다.

> ...there are two new features — it is `find_by_order()` and `order_of_key()`. The first returns an iterator to the k-th largest element (counting from zero), the second — the number of items in a set that are strictly smaller than our item.
>
> (출처: [C++ STL: Policy based data structures](https://codeforces.com/blog/entry/11080))

GNU C++에서 제공하는 Policy-based data structure를 이용하면 [Order Statistic Tree](https://en.wikipedia.org/wiki/Order_statistic_tree) 라는 구조를 쉽게 작성할 수 있고, 문제에서 정확히 필요로 하는 연산(`find_by_order()`)을 \\(O(\\log N)\\)에 제공한다.

예제가 나오는 것을 확인하고 자체 테스트 결과 잘 동작하는 것처럼 보여 그대로 제출했지만, 대회가 끝나자 오답(!) 판정을 확인할 수 있었다. 몇 차례 테스트하면서 일부 데이터에서 실행할 때마다 결과가 바뀌는 현상을 발견했고, 원인을 찾던 중 중복 원소를 고려하지 않았다는 사실을 깨달았다. 구조는 order statistic tree지만 내부적으로 `STL set`을 사용했기에 중복 원소가 들어가면 하나로 카운트된다는 사실을 생각하지 못해 일어난 오류였다. 다시 이를 고려해 코드를 수정하자 Practice 모드에서 정답 판정을 확인할 수 있었다(...) 맞았다면 100점으로 꽤 기분좋은 결과였겠지만 어쨌든 Round 2에 진출했으므로 크게 개의치 않았다. 코드잼의 Small / Large 시스템이었으면 이런 오류는 바로 발견할 수 있었을텐데 이런 점에서는 해커컵의 No Feedback 정책이 약간은 아쉽다.



## Round 2

* Round 2 참가자들 중 상위 200명이 Round 3에 진출
* Round 2 참가자들 중 상위 500명에게는 기념 티셔츠가 제공됨 ~~(549위...)~~

<img src="/assets/images/2019/07/hackercup-R2-scoreboard.png" width="800px">

일요일(7.14) 새벽 2시부터 5시까지 진행되는 라운드였다. 새벽 2시까지 깨어있는건 크게 어려운 일이 아니지만 그 컨디션을 5시까지 유지하기엔 자신이 없어 아예 저녁에 미리 잠들기로 했다(...) 그렇게 1시 반에 알람을 맞춰두고 눈을 떴지만 핸드폰엔 **2:23**이라는 글자가 반쯤 덜 깬 몸을 반겼다..

그렇게 노트북을 켜고 접속을 마치니 이미 30분이 지난 상황이었고 문제당 시간 핸디캡을 30분씩[^1] 가지고 시작한다는 생각에 마음이 조급해졌다. A, B번 문제를 풀고 500위가 아슬아슬하다는 걸 깨달았지만 비몽사몽+조급함 디버프를 받아서인지 C,D번 문제는 아이디어만 떠오를 뿐 디테일을 구체화시키지 못했다. 그렇게 대회가 끝났고 549등이라는 순위를 확인할 수 있었다. 끝난 마당에 의미없다는 걸 알면서도 아쉬운 마음에 패널티를 역산하니[^2] 제 시간에 일어났더라면 무난히 400위 안쪽을 차지할 점수였기에 티셔츠에 대한 미련을 떨치기 힘들었다.

사실 실력이 좀더 높았다면 한문제를 더 해결해 시간 패널티가 아닌 총점으로 티셔츠(+Round 3 진출)를 노릴 수 있었겠지만 평소에 PS 연습도 잘 하지 않은 입장에서 거기까지 바라는 건 과욕이라고 생각한다. 학생 때에는 ICPC를 비롯한 각종 대회라는 동기부여가 있었지만 졸업한 지금은 그런 거 없이 순수한 취미생활이기에 이전처럼 많은 시간을 투자하긴 어려울 것 같다. 이젠 대학원이라는 문제도 있으니 어쩌다 흥미로운 문제를 발견하면 풀어보고, 가끔 있는 이런 온라인 대회에 참가하는 정도에 의의를 둘 계획이다.

---

[^1]: 동점자의 경우 "대회 시작부터 해당 문제에 대한 답안을 제출하기까지 걸린 시간"의 총합으로 순위를 결정한다.
[^2]: 총 2문제를 해결했으므로 패널티인 2:32:14에서 30분x2를 앞당긴 1:32:14로 예상했다.