---
layout: post
title:  "2022년도 대회 후기 - 해킹(CTF) 편"
date:   2022-12-31 19:58:31 +0900
author: nyan101
categories: 근황
tags:	대회
use_math: true
---

2022년에는 대회 하나씩 끝날 때마다 후기를 쓰겠다고 다짐했지만 이번에도 결국 연말에 몰아서 쓰게 됐다(...)

올해는 [작년](https://nyan101.github.io/blog/CTF-contests-in-2021-review)과는 달리 CTF에서도 나름의 성과가 있던 해였다. 아직 CVE를 찾거나 국방/공공분야라는 울타리를 벗어나지는 못했지만, 그래도 조금씩 경험이 쌓여가는 것 같아 나름 보람있게 보낸 느낌이다. ~~그런데 논문은 대체 언제 쓰지...~~


## 국방 사이버보안 경진대회

* 일시 : 9.15.(본선)
* 주관 : 군사안보지원사령부(現 국군방첩사령부)
* 결과 : 우수(2위)

<img src="/assets/images/2022/12/dssc-contest-award.jpg" style="width:45%">

군사안보지원사령부에서 주관하는 전군(육+해+공+국직) 대상 경진대회이다. 작년엔 코로나로 대회가 취소되는 탓에 출전하지 못했지만 다행히 작년 성적을 인정받아 올해 공군 대표단에 포함되어 나갈 수 있었다. 필기와 실기가 합쳐진 형식이었으며, 필기는 보안규정이나 정보보안 관련 지식을 묻는 지필고사 형식, 실기는 Jeopary 형식의 CTF로 진행되었다.

본선장에 가니 전부 학과 선배, 동기들이어서 "이정도면 사실상 집안싸움 아닌가"라는 생각이 자연스럽게 들었는데 ~~실제로도 순위표 까보니 1,2,3등이 전부 사이버국ㅂ...~~ 결과적으로 해군 대표로 나왔던 동기와 필기 & 실기 모두 동점으로 1위를 다투게 되었다. 모든 점수가 동점인 관계로 실기 CTF의 최종 제출시각을 기준으로 순위를 결정하기로 했고 우리 팀의 제출 시점이 조금 더 늦어 동기가 1위(국방부장관상), 우리 팀이 2위(안보지원사령관상)를 차지했다.

\+ 여담이지만 대회를 한달만 더 늦게 했어도 "군사안보지원사령관" 대신 "국군방첩사령관" 직인 찍힌 상장을 받았을 텐데 아슬아슬하게(?) 안보지원사령부 시절 마지막 상장을 가져가게 됐다.


## 화이트햇 콘테스트

* 일시 : 10.15.(예선), 11.19.(본선)
* 주최/주관 : 대한민국 국방부 / 사이버작전사령부
* 결과 : 국방트랙 우수(2위)

<img src="/assets/images/2022/12/whitehat-contest-main.jpg" style="width:85%">

사이버작전사령부에서 주관하는 CTF로, 일반 / 청소년 / 국방트랙이 별도로 분리되어 진행된다.

<div style="width:90%;min-width:320px;margin:0 auto;display:flex;justify-content:space-evenly">
<img src="/assets/images/2022/12/whitehat-contest-award-01.jpg" style="width:49%;display:inline-block">
<img src="/assets/images/2022/12/whitehat-contest-award-02.jpg" style="width:49%;display:inline-block">
</div>

작년에 아쉽게 5위를 했던 기억이 있어 다들 마음을 다잡고 대회에 임했다. ~~지금까지 모든 대회에서 그랬듯이~~ 본선 초반 빠르게 문제를 풀어 중간 1위를 달성했지만, 중반 이후 더 문제가 풀리지 않아 점차 추격해오는 다른 팀들을 긴장어린 눈으로 바라봤다. 막판에 추가된 문제들 중 암호학 관련 문제들이 포함되어있어 빠르게 추가 점수를 얻었고, 그 덕분인지 대회 마지막까지 최종 2위(합참의장상) 자리를 지켜낼 수 있었다.

<div style="width:90%;min-width:320px;margin:0 auto;display:flex;justify-content:center">
<img src="/assets/images/2022/12/whitehat-contest-award-03.jpg" style="width:49%;display:inline-block">
<img src="/assets/images/2022/12/whitehat-contest-award-04.jpg" style="width:49%;display:inline-block">
</div>

작년에는 결국 수상권 안에 들지 못해 아쉬움이 많이 남았던 대회였는데, 올해는 운이 따랐는지 스타포스(?) +4성에 시상식까지 참석하면서 나름 인상적인 경험을 할 수 있었다.


## CCE 사이버공격 방어대회

* 일시 : 9.24.(예선), 10.27.(본선)
* 주최/주관 : 국가정보원 / 국가보안기술연구소
* 결과 : 전체 15위, 공공기관 4위 [^1]

[^1]: 분야별 3위까지 상이 수여된다...

<img src="/assets/images/2022/12/cce-main.jpg" style="width:85%">

국가정보원에서 주관하는 CTF로 일반인들을 위한 일반분야와 공공기관 종사자들을 위한 공공분야로 나눠 진행된다. 예선은 일반적인 Jeopardy(문제풀이) 방식, 본선은 Jeopardy와 함께 공격받는 Live 서버를 실시간으로 방어하는 방식으로 진행되었다.

<div style="width:90%;min-width:320px;margin:0 auto;display:flex;justify-content:space-evenly">
<img src="/assets/images/2022/12/cce-contest-01.jpg" style="width:49%;display:inline-block">
<img src="/assets/images/2022/12/cce-contest-02.jpg" style="width:49%;display:inline-block">
</div>

온라인이었던 작년과 달리, 대구 EXCO에서 오프라인으로 본선을 진행했다.

작년 실시간 방어 분야에서 헤멨던 만큼 올해는 나름 준비를 해갔지만, 웹서버 패치 방식이었던 작년과 달리 바이너리 패치 방식이어서 거의 손을 대지 못했다. NodeJS서버에 바이너리 실행파일이 올라가있고 이를 패치해 업로드하는 형식이었는데, 바이너리라는 특성상 오류가 나면 디버깅을 하지 못한다는 생각에 팀원들끼리 상의 후에 "괜히 잘못 건드려서 SLA Fail 패널티 받느니 그냥 기본점수만 받고 들어가자" 라는 합의가 진행됐다.

여기에 Jeopary 방식은 역대급 난이도를 자랑했다(...) 우리 팀은 암호학 관련 문제를 겨우 풀었는데 그나마도 해당 주제에 대한 배경지식이 부족해 대회 시간 내내 인터넷에서 논문을 찾아가며 공부해야 풀리는 문제였다. 2020년대에 나온 논문을 참조해가며 Sage 코드를 작성했고, 몇 번의 시행착오 끝에 플래그를 획득할 수 있었다. 당시 중간 스코어보드를 확인해보니 공공분야 3위여서 혹시나 하는 마음으로 기도했지만 13시간 대회 중 종료 1시간 미만을 남겨두고 역전당해 최종 순위는 4위로 내려갔다.~~후임, "매년 아깝게 그럴거면 차라리 그냥 20등을 하세요..."~~

대회가 끝난 후 확인해보니 공공분야 본선에 진출했던 20개 팀들 중 과반이 넘는 12개 팀이 대회 시간동안 1문제도 해결하지 못했다는 것을 알 수 있었다. 조금이라도 풀었으니 그보다는 낫다고 위안삼을 수도 있지만 일반부 스코어보드의 ~~기러기목 오리과의 모 동물이름을 쓰는~~ 괴수집단들을 보면 아직 갈길이 멀다는 걸 새삼 깨닫게 된다.

<div style="width:90%;min-width:320px;margin:0 auto;display:flex;justify-content:space-evenly">
<img src="/assets/images/2022/12/cce-party-01.jpg" style="width:49%;display:inline-block">
<img src="/assets/images/2022/12/cce-party-02.jpg" style="width:49%;display:inline-block">
</div>

대회가 끝난 후 Theori 주관으로 참가자들 간 애프터파티가 열렸다. 오랜만에 보는 낮익은 얼굴들과 즐거운 시간을 보낼 수 있었다.


## DFC 디지털 포렌식 챌린지

* 일시 : 5.1. ~ 9.30.
* 주최/주관 : 한국정보보호학회
* 결과 : 장려상(7위)

<img src="/assets/images/2022/12/dfc-contest-main.jpg" style="width:85%">

한국정보보호학회에서 주관하는 대회로, 매달 다양한 주제의 포렌식 문제가 공개되고 이를 해결해 보고서를 제출하는 형식의 대회이다. 학과 선배, 동기들과 함께 6인 팀을 구성해 나갔으며, 주기적으로 온라인 회의를 통해 각자의 진행상황을 공유했다. 장장 5개월에 걸쳐 진행되는 만큼 페이스 조절이 어려운 대회였다.

<img src="/assets/images/2022/12/dfc-contest-award-01.jpg" style="width:85%">

그렇게 긴 여정이 끝나고 최종 7위라는 결과를 얻었다. 6위 팀까지 장려상이 수여된다고 알고있어 다들 낙심하던 중, 해외 팀들의 참여 부족으로 국내 수상팀 숫자에 TO가 하나 늘어나면서 아슬아슬하게 수상 막차를 탈 수 있었다.

<div style="width:90%;min-width:320px;margin:0 auto;display:flex;justify-content:center">
<img src="/assets/images/2022/12/dfc-contest-award-02.jpg" style="width:49%;display:inline-block">
<img src="/assets/images/2022/12/dfc-contest-award-03.jpg" style="width:49%;display:inline-block">
</div>

번외로, 상패에 영문 수상명이 "Participation Prize"로 되어있어 팀원들끼리 농담조로 "이거 참가상 아니야?" 라는 말을 했는데 구글검색 결과 장려상이 영어로 Participation Prize라는 사실을 알게 되었다.~~그냥 내가 영알못이었던 걸로~~

---

