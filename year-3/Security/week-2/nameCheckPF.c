#include<stdio.h>

void function2(void) {
  printf("\nFUNCTION2!! \\o/\n");
  fflush(stdout);
}

void function1(void) {
    char buffer[62];

    int secretNumber = 65825582;
    char * password = "qytf-akgd-shgk-jskf";

    printf("Enter your username: ");
    fflush(stdout);

    fgets(buffer,999,stdin);

    printf("Enter password for ");
    printf(buffer);
    printf(": ");
    fflush(stdout);

    fgets(buffer,999,stdin);
    printf(buffer);
    fflush(stdout);

}



int main(void) {
    function1();
    return 0;
}
