#include <stdio.h>
#include <string.h>
#include <stdlib.h>

char letter;

int main(void)
{
  char input[20];
  puts("Enter password:");
  fflush(stdout);
  fgets(input,sizeof(input),stdin);

 
  //Password must be 8 chars long
  if (strlen(input) == 9) {
  
    //It must start with lower case letter
    //from the first half of the alphabet
    if (input[0]>0x60 && input[0]<0x6F) {
  
      // first 8 chars must be assending ascii
      letter = input[0];
      letter++;
      if (input[1]==letter) {
        letter++;
        if (input[2]==letter) {
            letter++;
            if (input[3]==letter) {
                //second 8 chars must be "2016"
                char subst[5];
                strncpy(subst,input+4,4);
                subst[4] ='\0';
                int snd = atoi(subst);
                if (snd==2020) {
                    puts("Well done, that is the correct password\n");
                    fflush(stdout);
                    exit(0);
                }
            }
        }
      }       
    }
  }
  
  puts("Incorrect password"); 
  fflush(stdout);
  return 0;
}

