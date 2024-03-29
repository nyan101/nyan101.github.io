---
layout: post
title:  "Facebook Hacker Cup 2020 후기"
date:   2020-08-30 20:35:19 +0900
author: nyan101
categories: 근황
tags:	대회
use_math: true
---



**TL;DR : 이번엔 티셔츠 받음**



[2019년 해커컵](https://nyan101.github.io/blog/facebook-hackercup-2019-review)에 이어 올해도 2020년도 페이스북 해커컵 대회가 열렸다. 이번에도 Round 2에서 늦잠을 자면서 Round 3은 달성하지 못했지만[^1] 티셔츠까지는 받을 수 있었다. 구글 코드잼은 작년에 티셔츠를 받았지만 해커컵은 이번이 첫 티셔츠여서 그런지 나름 만족스럽다.

[^1]: 일찍 일어났어도 200등은 애매했을거같다.

그동안 해커컵에서의 제일 큰 불만은 **small / large가 없어서 조금이라도 실수하면 돌이킬 수가 없다**라는 점이었는데, 이번에는 validate step이 나와서 이런 점이 조금은 완화됐다. 코드포스의 pretest 느낌으로 `validate_input.txt`을 제공하고, `validate_output.txt`를 제출하면 이에 대한 채점결과를 알려주는 시스템이 추가되면서 "그래도 바보같은 코딩실수는 안했구나"라는 확인을 할 수 있었다.

<img src="/assets/images/2020/08/hackercup-tshirt.png" style="max-width:550px">

작년에는 Round 2 기준 상위 500명에게만 티셔츠를 제공했지만 올해 해커컵에서는 기준이 조금 바뀌었다. Round 2에서 1문제 이상을 해결한 경우 기념 티셔츠를,  Round 3(상위 200명)에 진출하는 경우 티셔츠에 "Top 200"이라는 뱃지가 추가되어 나온다는 모양이다. 이왕 받는거 Top 200이었다면 좋았겠지만 노말등급(?) 티셔츠도 전체 참가자 수 대비 5% 미만의 사람들만 받은 만큼 너무 아쉬워할 필요는 없을거같다.

각 라운드의 성적은 다음과 같다.

<img src="/assets/images/2020/08/hackercup-scoreboard.png">

### Qualification Round

Round 1 진출을 위해서는 1문제 이상만 정답이면 된다. 하지만 퀄라운드가 72시간이라는 긴 시간동안 진행되면서 "남는 시간동안 다른 문제들도 고민해보자"라는 생각을 했고, 결과적으로 모든 문제 정답이라는 나름 기분좋은 성적으로 진출할 수 있었다.

### Round 1

A번이 같은 상황에 데이터 조건만 다르게 해 A1, A2, A3으로 분리되어 나왔다. 보통 이렇게 분할된 문제들은 A3이 A1, A2의 상위호환[^2]인 경우가 많은데, 막상 문제를 보니 각 상황별로 다른 알고리즘을 사용해야 했다.

이번 Round 1에선 C번 문제를 제외한 나머지를 전부 제출했는데, 제출 후 얼마 지나지 않아 A3에서 세그트리로 처리해야할 최대 배열 사이즈를 잘못 설정했다는 것을 깨달았다. validate step에서는 걸러지지 않았던 문제라 눈치채지 못했고, 라운드 종료 후 확인해보니 예상대로(?) 오답 판정을 받았다. 배열 사이즈를 2배로 늘린 후 다시 제출하니 정답 판정이어서 조금 아쉬웠지만 어쨌든 Round 2로 진출했으니 "제대로 된 풀이를 떠올린 건 맞다"는 점에 의의를 두기로 했다.

[^2]: 각각의 데이터 조건이 subset 관계를 이뤄, A3을 풀었다면 같은 소스코드를 A1, A2에 제출하면 통과되는 경우.

### Round 2

올해도 Round 2는 일요일 새벽 2시부터 5시까지 진행됐다. 작년엔 자느라 30분 늦게 시작했던 아쉬움이 있었기에 이번엔 꼭 시간을 맞추겠다는 다짐을 했고, 편의점에서 미리 에너지드링크까지 사오면서 단단히 준비했다.

<img src="/assets/images/2020/08/hackercup-kakaotalk.jpg" style="width:60%">

하지만 1시에 "잠깐 눈좀 붙일까"라는 생각을 ~~해서는 안 됐음에도~~ 한 게 화근이었고, 그렇게 눈을 뜨니 2시 19분이었다(...) 다행히 바뀐 규정에 따라 1문제 이상만 해결해도 티셔츠는 받을 수 있었기에 부담을 조금 내려놓고 대회를 시작했다. A번은 Round 2인 걸 감안하면 간단한 난이도, B는 약간의 수식을 세우면 $$O(N^2)$$ DP로 풀리는 확률계산 문제였다. 이후 시간을 들여 C를 코딩했으나 예제가 나오지 않아 확인하던 중, 문제 접근을 살짝 엇나갔다는 사실을 깨달았다.

패널티를 확인해보니 C를 마저 풀어도 Round 3 진출(상위 200명)이 아슬아슬한 상황이었다. 어떻게 할지 고민했지만 어차피 결과에 큰 차이는 없다는 생각(과 자다 깨서 대회를 뛴 피곤함) 끝에 C를 더 잡지 않고 최종 629등으로 대회를 마무리했다.

---