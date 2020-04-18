#include "types.h"
#include "stat.h"
#include "user.h"
int
main(int argc, char *argv[])
{
    
    int pid = fork();
    int cnt = 0;
    if(pid == 0){
        while(cnt<10){
            printf(1, "Child\n");
            yield();
            cnt++;
        }
    }else{
        while(cnt<10){
            printf(1, "Parent\n");
            yield();
            cnt++;
        }
    }
    if(pid == 0){
        sleep(2);
    }else{
        wait();
        exit();
    }
    exit();
    return 0;
}


