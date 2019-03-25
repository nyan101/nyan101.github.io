---
layout: post
title:  "Code Jam Kickstart 2018 Round D 후기"
date:   2018-08-03 20:24:03
author: nyan101
categories: 근황
tags:	대회
---



공식적으로 전직(...)을 했지만 가능한 한 PS대회는 계속 나가보고 싶었다. SCPC나 UCPC는 이제 대학생이 아니라 참가를 못했지만, 지난 주말에 Code Jam Kickstart Round D가 있어 여기 참가해볼 수 있었다. 코드잼 킥스타트에 대한 설명은 [Round C 후기](https://nyan101.github.io/%EA%B7%BC%ED%99%A9/2018/05/27/CodeJam-KickstartC-%ED%9B%84%EA%B8%B0.html)에서 한번 작성한 바 있으니 이 글에서는 생략했다.



이날 대회는 오후 2시부터 열렸는데, 내가 3시부터 세미나가 있어 그전까지는 약속장소 근처 스타벅스, 이후엔 세미나실에서 틈틈히 코딩을 진행했다. 저번 Round C를 1시간 20분만에 올클했었기에 이번에도 비슷하게 걸리지 않을까라는 ~~근자감이 가득한~~ 예상을 했지만 A를 보는 순간 그런 기대는 깔끔하게 접혔다. 결국 C에 와서는 "그냥 small만 통과하자"라는 마음으로 small 전용 코드를 짜서 제출하고 다시 세미나에 합류했다.



쉬는시간에 최종 결과를 확인해보니 23등으로 나름 선방(?)한 걸 확인할 수 있었다. 

<img src="/assets/images/2018/08/kickstart-scoreboard.png" width="800px">



문제는 [여기](https://code.google.com/codejam/contest/6364486/dashboard) 에서 볼 수 있다. 이미 analysis까지 올라온 상황이니 풀이보다는 당시 심정을 중점으로 서술했다

#### Problem A. Candies 

문제를 읽고 "이거 A번 맞나"라는 생각이 들었다. odd 조건을 만족시킬 방법은 쉽게 떠올렸는데 max sweet 제한을 벗어나지 않으면서 가장 큰 값을 찾는 게 쉽지 않았다. BBST를 구현하면 금방 해결될 문제였지만 그러긴 싫었고, C++ STL multiset을 찾아봤다. 레퍼런스 설명을 잘못 읽으면서 헤멘 시간이 많아 40분이 지난 시점에서야 Correct를 띄울 수 있었다.



#### Problem B. Paragliding 

기둥들을 기준으로 양방향 45도 아래로 직각이등변삼각형을 그리면 그 영역에 포함된 풍선의 개수가 답이 된다. 문제를 보는 순간 데자뷰가 느껴졌다.



<img src="/assets/images/2018/08/kickstartB.png" width="500px">

<img src="/assets/images/2018/08/hackercup.png" width="650px">



위는 이번 문제에서 제공된 그림, 아래는 작년 Facebook에서 열렸던 Hackercup 2017 Round 2의 [Big Top](https://www.facebook.com/hackercup/problem/1612752199040515/)이라는 문제의 그림이다. 작년에 저 문제를 못 풀었고, 그때 정해가 BBST를 직접 구현하는 거였기에 "A에서 BBST 구현할걸"이라는 후회를 잠깐 했다. 이후 ~~BBST 코딩을 정말 하기 싫어서~~  천천히 다시 생각해보니 기둥을 실시간으로 세우는 게 아니기에 정렬만 하면 굳이 BBST 없이도 해결이 가능하다는 걸 깨달았고, 기쁜 마음으로(?) 코딩을 진행했다.



#### Problem C. Funniest Word Search 

뭔가 어렴풋이 떠오를 것 같았는데 구체화까지는 아직 멀어보였고, 이때 세미나가 진행중이어서 계속 문제만 붙들고 있기로 어려운 상황이었다. small은 prefix sum으로 금방 해결할 수 있어보여서 여기까지만 풀고 대회를 끝냈다. 나중에 analysis를 읽어보니 내 방식은 small에만 적용 가능하고 large를 위해서는 좀더 확장해야 한다고 하던데 한번 자세히 읽어봐야겠다.



최종 스코어보드는 [여기](https://code.google.com/codejam/contest/6364486/scoreboard?c=6364486#vt=1&vf=1)에서 볼 수 있다.