---
layout: post
title:  "Code Jam Kickstart 2019 Round B 후기"
date:   2019-04-21 15:42:21
author: nyan101
categories: 근황
tags:	대회
use_math: true
---

리뉴얼된 후 두 번째 치르는 코드잼이다. 지난번처럼 서버 문제는 없었지만 생각처럼 문제가 잘 풀리지 않아 A 빼고는 딱히 정해를 떠올릴 수 있는 문제가 없었다. 결국 B, C번 모두 Small만을 해결하고 최종 115등으로 대회가 끝났다. 전체 문제는 [여기](https://codingcompetitions.withgoogle.com/kickstart/round/0000000000050eda)에서 볼 수 있다.



<img src="/assets/images/2019/04/kickstart-B-dashboard.png" width="800px">




#### Problem A. Building Palindromes

문자열이 주어지면 주어진 문자열의 l...r 구간에 포함된 글자들로 팰린드롬을 만들 수 있는지 판단해야 한다. 구간 [l, r]에 속한 글자들만으로 팰린드롬을 만들기 위해서는 홀수 번 등장하는 알파벳이 최대 한 가지여야 한다는 사실에 유의하면, 각 알파벳 등장 횟수의 prefix sum을 이용해 각 쿼리를 \\(O(26)\\)에 처리할 수 있다. 첫 제출에서 초기화에 쓴 `fill` 함수의 범위를 잘못 잡았다는 걸 깨달아 대회 도중 다시 제출했다. [[source](https://github.com/nyan101/algorithm_snippet/blob/master/CodeJam/Kickstart 2019 Round B/A.cpp)]



#### Problem B. Energy Stones

Small에서는 **모든 \\(S\_i\\)가 동일하다** 라는 조건이 있으므로 **i번째 스톤을 먹기 시작하는 시점은 종류에 무관하게 \\(S\_1 \* (i-1)\\)로 고정된다.** 따라서 "스톤 i를 j번째로 먹을 때" 얻을 수 있는 에너지를 사전에 계산할 수 있고, 이를 가중치로 하는 이분그래프(스톤 vs 순서)를 그릴 수 있다. 만들어진 그래프에 대해 최대 가중치를 가지는 maximum matching(N쌍이 모두 매칭되는 것이 보장됨)을 구하면 Small을 통과할 수 있다. 최대 가중치 이분매칭은 예전 팀노트에 있던 MCMF 코드를 약간 수정했다. [[source](https://github.com/nyan101/algorithm_snippet/blob/master/CodeJam/Kickstart 2019 Round B/B.cpp)]

 정해는 먼저 각 스톤을 \\(S\_i / L\_i)\\)를 기준으로 정렬한 후 Knapsack을 수행하는 것이다. 대회 도중  \\(S\_i / L\_i)\\)까지는 떠올렸지만 _"The stone's energy stops decreasing once it hits zero."_ 라는 조건 때문에 그 이상 발전시키지 못했는데, 이를 Knapsack으로 해결할 수 있다고 한다.




#### Problem C. Diverse Subarray

[l, r] 구간을 생각하자. 먼저 왼쪽 지점(l)을 고정시키고, 오른쪽 지점(r)을 한칸씩 이동시키면서 만나는 타입들의 등장 횟수를 `cnt[]`로 관리할 수 있다. 이렇게 스캔이 끝나면 (고정된 l에 대해) 각각의 r에서 가져갈 수 있는 trinkets의 수를 \(O(N)\\)에 구할 수 있고, 이를 각 l에 대해 수행하면 전체 \\(O(N^2)\\)의 복잡도로 문제를 해결할 수 있다.

Large를 해결하기 위한 핵심은 "한번 고정된 l에 대해 해를 구하면 다음 l'=l+1에 대해서는 그 변화값만을 빠르게 반영할 수 있다" 라는 사실을 이용하는 것으로, 세그먼트 트리에 Lazy Propagation을 더해 해결할 수 있다. 대회 중에는 Small까지만 해결했고, 이후 공개된 풀이를 보고 다시 코드를 작성해봤다. [[source](https://github.com/nyan101/algorithm_snippet/blob/master/CodeJam/Kickstart 2019 Round B/C.cpp)]



<img src="/assets/images/2019/04/kickstart-B-ProblemC.png" width="800px">



세그먼트 트리에서의 Lazy Propagation은 이론적으로는 알아도 막상 문제를 보면 눈치채지 못하는, 다시 말해 "구현은 할 줄 알지만 익숙하지는 않은" 부류에 속해있었는데 이번을 계기로 좀더 익숙해질 수 있도록 해야겠다.