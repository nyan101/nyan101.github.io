---
layout: post
title:  "ELF x86 - Race condition"
date:   2018-01-25 00:00:05
author: nyan101
categories: 자습
tags:	app/system
cover:  
---



주어진 코드는 다음과 같다.

```c
#include <...>

#define PASSWORD "/challenge/app-systeme/ch12/.passwd"
#define TMP_FILE "/tmp/tmp_file.txt"
 
int main(void)
{
  int fd_tmp, fd_rd;
  char ch;
  
  if (ptrace(PTRACE_TRACEME, 0, 1, 0) < 0) 
  {
    printf("[-] Don't use a debugguer !\n");
    abort();
  }
  if((fd_tmp = open(TMP_FILE, O_WRONLY | O_CREAT, 0444)) == -1)
  {
    perror("[-] Can't create tmp file ");
    exit(0);
  }
 
  if((fd_rd = open(PASSWORD, O_RDONLY)) == -1)
  {
    perror("[-] Can't open file ");
    exit(0);
  }
 
  while(read(fd_rd, &ch, 1) == 1)
  {
    write(fd_tmp, &ch, 1);
  }
  close(fd_rd);
  close(fd_tmp);
  usleep(250000);
  unlink(TMP_FILE);
 
  return 0;
}
```

코드 내용은 단순하다. 먼저 디버거가 붙는 것을 감지해 차단한다. 이후 .passwd파일을 열어 그 내용을 TMP_FILE에 복사하고 약간의 시간이 지난 후 다시 unlink함수로 만들어진 TMP_FILE을 삭제한다. 따라서 usleep으로 생기는 잠깐의 틈 사이에 TMP_FILE을 열어 내용을 확인해야 한다. 몇 번의 시도 끝에 성공할 수 있었다.

![](/assets/images/2018/01/rootme-05.png)