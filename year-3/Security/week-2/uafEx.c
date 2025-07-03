#include <stdlib.h>
#include <unistd.h>
/* Based on one of the excellent Protostar execises
   https://exploit-exercises.lains.space/protostar/  */

#include <string.h>
#include <sys/types.h>
#include <stdio.h>

struct authStruct {
  char name[32];
  int isAuthed;
};

struct authStruct *auth;

char *service;

int main(int argc, char **argv)
{
  char line[128];
  while(1) {
    printf("[ Heap layout: auth is at address %p, service is at address %p ]\n", auth, service);
    if(fgets(line, sizeof(line), stdin) == NULL) break;
    
    if(strncmp(line, "addUser ", 5) == 0) {
      auth = malloc(sizeof(struct authStruct));
      memset(auth, 0, sizeof(struct authStruct));
      if(strlen(line + 5) < 31) {
        strcpy(auth->name, line + 5);
      }
    }

    if(strncmp(line, "reset", 5) == 0) {
      free(auth);
    }

    if(strncmp(line, "service", 6) == 0) {
      service = strdup(line + 7);
    }

    if(strncmp(line, "login", 5) == 0) {
      if(auth->isAuthed) {
        printf("you have logged in already!\n");
      } else {
        printf("please enter your password\n");
      }
    }

  }
}
