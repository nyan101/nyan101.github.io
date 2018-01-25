---
layout: post
title:  "Root Me: ELF x86 - Stack buffer overflow basic 2"
date:   2018-01-25 00:00:02
author: nyan101
categories: 자습
tags:	app/system
cover:  
---



주어진 코드는 다음과 같다.

```c
/*
gcc -m32 -fno-stack-protector -o ch15 ch15.c
*/     
#include <stdio.h>
#include <stdlib.h>
     
void shell() {
    system("/bin/dash");
}
     
void sup() {
    printf("Hey dude ! Waaaaazzaaaaaaaa ?!\n");
}
     
main()
{ 
    int var;
    void (*func)()=sup;
    char buf[128];
    fgets(buf,133,stdin);
    func();
}
```

맨 마지막에 `func()`가 호출되므로 sup 대신 shell이 호출되게 만들면 된다. 함수의 주소는 GDB를 통해 확인할 수 있다. `gdb ./ch15`로 바이너리를 열고, `disas(dis)` 커맨드를 통해 `shell()` 함수의 주소를 확인하자

![](/assets/images/2018/01/rootme-02.png)

마지막으로, 얻어낸 주소값을 func에 덮어쓸 수 있도록 적절히 입력하면 쉘을 얻을 수 있다.