---
layout: post
title:  "Root Me: ELF x86 - Stack buffer overflow basic 1"
date:   2018-01-25 00:00:01
author: nyan101
categories: 자습
tags:	app/system
cover:  
---

이제 '약속의 그날'까지 70일쯤 남았는데 그전에 기본적인 건 알고 가야 하지 않을까 해서 간단한 내용부터 시작하기로 했다. 예전에 OverTheWire같은 데서 몇 번 깔짝거린 적은 있어도 끝까지 다 풀어본 건 아직 Lord of SQL Injection이 유일하고, 시스템이나 리버싱은 먼 나라 이야기여서 별 생각을 안하고 있었는데 어차피 하긴 해야하는거 남은 기간 동안 기초만이라도 알아가기로 했다. 누군가에게 설명을 위해서가 아니라 단순히 기록 목적으로 작성하는 글이라 다소 간략하게 정리했다.

사이트는 이렇게 생겼다.

![](/assets/images/2018/01/rootme-01-mainpage.png)



본론으로 들어가서, 첫 문제를 살펴보자. 

```c
#include <stdlib.h>
#include <stdio.h> 
/*
gcc -m32 -o ch13 ch13.c -fno-stack-protector
*/
int main()
{
 
  int var;
  int check = 0x04030201;
  char buf[40];
 
  fgets(buf,45,stdin);
 
  printf("\n[buf]: %s\n", buf);
  printf("[check] %p\n", check);
 
  if ((check != 0x04030201) && (check != 0xdeadbeef))
    printf ("\nYou are on the right way!\n");
 
  if (check == 0xdeadbeef)
   {
     printf("Yeah dude! You win!\nOpening your shell...\n");
     system("/bin/dash");
     printf("Shell closed! Bye.\n");
   }
   return 0;
}
```

~~다행히 처음엔 아는거다.~~ buf는 char[40]으로 선언되어있는데 45바이트를 입력받는다. 아래 그림에 나타난 스택 구조를 생각해보면 추가로 쓸 수 있는 바이트는 메모리의 check 영역을 침범함을 알 수 있다. 

![](/assets/images/2018/01/rootme-01-stack-memory.png)

따라서 아무 내용으로 40글자를 채운 후 뒤에 deadbeef를 붙이면 된다. ASCII 범위를 벗어나므로 python을 이용하자. `python -c `를 통해 한줄짜리 코드를 실행할 수 있다.

![](/assets/images/2018/01/rootme-01-endian.png)

check가 4byte int이므로 엔디안(리틀 엔디안)에 유의해야 한다. 순서에 유의해 다시 입력하면 쉘을 얻을 수 있고, `cat .passwd`를 통해 플래그를 구할 수 있다. (정답 공개를 방지하기 위해 본문에서는 생략)