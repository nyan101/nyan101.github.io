---
layout: post
title:  "SW Foundations - Ch01. Functional Programming in Coq"
date:   2019-01-28 21:02:16
author: nyan101
categories: 자습
tags:	Coq
use_math: true
---

사실 예전 LaTeX을 익힐 때에도 이것저것 찾아보기만 하다가 결국 학교 과제를 LaTeX으로 작성해보고서야 익숙해졌는데, 이번에도 실 사용 없이 공부하는게 얼마나 갈지는 잘 모르겠다.. 자료 초반에 _"All the core chapters are suitable for both upper-level undergraduate and graduate students."_ 라는 말이 있던데, ~~물론 저런 말들이 다 그렇듯이 전부 거짓말이겠지만~~ 이젠 undergraduate 신분이라는 핑계도 사라졌으니 좀더 확실히 짚고 넘어가야겠다는 생각도 든다.


## Overview

_**\<Software Foundations\>**_ 라는 제목에서 짐작할 수 있듯이, 이런 것들을 하는 주된 목표는 "Building reliable software"라고 할 수 있다. 현대 사회에서 소프트웨어의 영향력이나 그만큼 커진 보안의 중요성에 대해서는 굳이 이 글이 아니어도 여러 곳에서 들었을 테니 생략하고, 다음 질문인 **"그럼 어떻게 하면 reliable한 소프트웨어를 만들 수 있는가"** 로 넘어가자. 다양한 시각에서 다양한 해결책이 제시되었다.

* 소프트웨어를 제작하는 사람을 중심으로 생각
  * 익스트림 프로그래밍, 애자일, 폭포수 모델,  ⋯
* SW 라이브러리를 디자인하는 방식 제안
  * MVC모델, publish-subcribe, ⋯
* 프로그래밍 언어 자체의 설계철학을 제시
  * OOP, aspect-oriented, functional, ⋯
* **소프트웨어의 성질을 수학적으로 논증(reasoning)**
  * SMT solver, Isabelle, Coq, ⋯

여기서 다루고자 하는 건 마지막 접근방식이다. 특히, \<Software Foundations\>에서는 크게 다음 3가지를 중점적으로 다룬다.

1. 프로그램의 성질을 정밀(precise)하게 묘사하기 위한 Logic
2. 엄밀한 논증을 위해 proof assistant를 사용하는 방법
3. 프로그래밍과 논리를 잇는 연결고리로서의 functional programming



### Proof Assistant

논리학이 CS에 제공하는 게 많아보이지만 의외로 CS가 논리학에 준 도움 또한 존재한다. CTF를 해봤거나 퍼즐 문제를 좋아한다면 한번쯤 들어봤을 SMT solver를 비롯해 다양한 툴이 있으며, 이는 크게 두 부류로 나뉘어진다

#### Automated Theorem Prover

명제를 입력하고 작동시키면 True 혹은 False를 리턴해주고, 필요한 경우 어떻게 그 결과가 나왔는지 근거를 제공한다. 예를 들어 \\( A \\land (B \\lor \\neg C)\\)라는 명제에 True와 함께 A:True, B:True, C:False를 출력하는 식이다. 다룰 수 있는 범위에 다소 제약이 있으며, 모든 경우를 해결해주지는 못한다(ex: _ran out of time_ 에러).  SAT solver나 SMT solver, model checker 등이 있다.

#### Proof Assistant

proof assistant는 사람의 개입을 가능하게 해 직관을 더하면서도 증명에서 논증의 단단함은 잃지 않도록 한 일종의 하이브리드 도구라고 할 수 있다. 툴과 사람이 상호작용을 통해 증명을 완성해가며, Isabelle이나 ACL2, Coq 등이 있다.



### Coq 활용 사례

Coq는 현재 전산학과 수학의 여러 분야에 폭넓게 활용되고 있다.

* 프로그래밍 언어의 모델링 플랫폼
  : JavaCard 플랫폼의 보안성을 증명해 CC인증을 받는 데 활용됨

* 증명된(formally certified) SW나 HW의 개발환경
  : CompCert(fully-verified C optimizing compiler), CertiKos(fully-verified hypervisor), CertiCrypt 등

* dependent type을 이용한 함수형 프로그래밍 환경 제공

* higher-order logic에서의 proof assistant
  : 4색 정리, Feit-Thompson 정리의 증명 및 검증