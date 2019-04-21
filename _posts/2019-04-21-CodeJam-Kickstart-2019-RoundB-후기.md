---
layout: post
title:  "Code Jam Kickstart 2019 Round B 후기"
date:   2019-04-21 15:42:21
author: nyan101
categories: 근황
tags:	대회
use_math: true
---

지난 Round A에 이어 리뉴얼된 킥스타트에서 두번째로 치르는 대회였다. 다행히 지난번과 같은 서버 문제는 없었지만 생각처럼 문제가 잘 풀리지는 않았다. A번을 제출하고 나니 딱히 풀이가 떠오르는 문제가 없어 결국 B, C 모두 Small까지만 통과할 수 있었다. 결과는 최종 115등으로 전체 문제는 [여기](https://codingcompetitions.withgoogle.com/kickstart/round/0000000000050eda)에서 볼 수 있다.



<img src="/assets/images/2019/04/kickstart-B-dashboard.png" width="800px">




#### Problem A. Building Palindromes

문자열이 주어지면 주어진 문자열의 l...r 구간에 포함된 글자들로 팰린드롬을 만들 수 있는지 판단해야 한다. 구간 [l, r]에 속한 글자들만으로 팰린드롬을 만들기 위해서는 홀수 번 등장하는 알파벳이 최대 하나여야 한다는 사실에 유의하면, 각 알파벳 등장 횟수의 prefix sum을 이용해 각 쿼리를 \\(O(26)\\)에 처리할 수 있다. 첫 제출에서 초기화에 쓴 `fill` 함수의 범위를 잘못 잡았다는 걸 깨달아 대회 도중 다시 제출했다. [[source](https://github.com/nyan101/algorithm_snippet/blob/master/CodeJam/Kickstart 2019 Round B/A.cpp)]



#### Problem B. Energy Stones

Small에서는 **모든 \\(S\_i\\)가 동일하다** 라는 조건이 있으므로 **i번째 스톤을 먹기 시작하는 시점은 이전까지의 선택과 무관하게 \\(S\_1 \* (i-1)\\)로 고정된다.** 따라서 "스톤 i를 j번째로 먹을 때" 얻을 수 있는 에너지를 사전에 계산할 수 있고, 이를 가중치로 하는 이분그래프(스톤—순서)를 그릴 수 있다. 이제 만들어진 그래프에 대해 최대 가중치를 가지는 maximum matching[^1]을 구하면 Small을 통과할 수 있다. 최대 가중치 이분매칭은 예전 팀노트에 있던 MCMF 코드를 약간 수정했다. [[source](https://github.com/nyan101/algorithm_snippet/blob/master/CodeJam/Kickstart 2019 Round B/B.cpp)]

 정해는 먼저 각 스톤을 \\(S\_i / L\_i\\)를 기준으로 정렬한 후 Knapsack을 수행하는 것이다. 대회 도중  \\(S\_i / L\_i\\)까지는 떠올렸지만 _"The stone's energy stops decreasing once it hits zero."_ 라는 조건 때문에 그 이상 발전시키지 못했는데, 이를 Knapsack으로 해결할 수 있다고 한다.

[^1]: 그래프 구조상 항상 전체 N쌍이 매칭되는 것이 보장된다


#### Problem C. Diverse Subarray

먼저 왼쪽 지점(l)을 고정시킨 [l, r] 구간을 생각하자. 오른쪽 지점(r)을 한칸씩 이동시키면서 만나는 타입들의 개수 `cnt[]`를 관리하면, 각각의 r에 대해 [l,r] 구간을 선택했을 때 얻게 되는 trinket의 수 `get[r]`을 구할 수 있다. 고정된 l에 대해 `get[]`을 구하는 과정이 \\(O(N)\\)이므로, 이를 각 l에 대해 수행하면 전체 \\(O(N^2)\\)의 복잡도로 문제를 해결할 수 있다.

Large를 해결하기 위한 핵심은 **고정된 l에 대해 `get[]`을 구했으면 다음 l'=l+1에 대해서는 (처음부터 다시 계산하는 대신) 그 변화값만을 반영시킨다** 라는 아이디어로, 세그먼트 트리에 Lazy Propagation을 더해 해결할 수 있다. 대회 중에는 Small까지만 해결했고, 이후 공개된 풀이를 보고 다시 코드를 작성해봤다.[[source](https://github.com/nyan101/algorithm_snippet/blob/master/CodeJam/Kickstart 2019 Round B/C.cpp)]



<img src="/assets/images/2019/04/kickstart-B-ProblemC.png" width="800px">



세그먼트 트리에서의 Lazy Propagation은 이론적으로는 알아도 막상 문제를 보면 눈치채지 못하는, 다시 말해 "구현은 할 줄 알지만 익숙하지는 않은" 부류에 속해있었는데 이번을 계기로 좀더 익숙해질 수 있었으면 좋겠다. 그와 별개로 킥스타트가 리뉴얼되고 이전같은 성과가 잘 나오지 않고 있는데, 이게 졸업하고 PS연습을 덜 하게 되어서인지 아니면 다른 이유가 있는 건지는 아직 잘 모르겠다..



---