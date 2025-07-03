#include<stdio.h>

void function1(void) {
    printf("Enter your name:\n");
    char buffer[64];
    gets(buffer);
    printf("No token for you %s!\n",buffer);
    printf("By the way buffer was at: %p\n",buffer);
}

void function2(void) {
    // Open file
    FILE *fptr;
    fptr = fopen("overflowToken1", "r");
    // Read contents from file
    char c = fgetc(fptr);
    while (c != EOF)
    {
        printf ("%c", c);
        c = fgetc(fptr);
    }
    fflush(stdout);
    fclose(fptr);
}

int main(void) {
    function1();
    return 0;
}
