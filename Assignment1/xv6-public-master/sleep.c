/*
    User Program Name: sleep
    Usage:  sleep NUMBER
            or:  sleep OPTION
        Pause for NUMBER ticks. 
        OPTION can be:
            -help        display help and exit
            -version     output version information and exit
    System Call Dependencies: Uses sleep system call    
*/

#include "types.h" // contains typedef for common data types
#include "user.h" // contains system call templates avalaible for use in user programs

// These are additional utility functions implemented below
void printHelpAndExit(void);
void printVersionAndExit(void);
void printErrorAndExit(int);
int isNumber(const char*);

int main(int argc, char *argv[]){
    // Checking number of arguments passed through Command Line, and raising appropriate errors if any discrepency found
    if(argc == 1 || argc > 2) printErrorAndExit(argc);

    // Checking if OPTION's are used
    if(!strcmp(argv[1], "-help")) printHelpAndExit();
    if(!strcmp(argv[1], "-version")) printVersionAndExit();

    // Checking if a number is passed as input (this error checking is not implemented in atoi)
    if(!isNumber(argv[1])) printErrorAndExit(0);

    // Sleeping for specified number of ticks
    int numTicksToSleep = atoi(argv[1]);
    sleep(numTicksToSleep);

    exit();
}

void printHelpAndExit(void){
    printf(0, "\nUsage: sleep NUMBER\n   or:  sleep OPTION\nPause for NUMBER ticks. \nOPTION can be:\n   -help        display this help and exit\n   -version     output version information and exit\n");
    exit();
}

void printVersionAndExit(void){
    printf(0, "Version 1.0\n (you really need another version of this?)\n");
    exit();
}

void printErrorAndExit(int argc){
    printf(1, "sleep: %s\nTry 'sleep -help' for more information.\n", argc == 1? "missing operand" : "incorrect usage");
    exit();
}

int isNumber(const char * s){
    // Iterates through the characters, and returns 0 if any character is not a digit
    while(*s != '\0'){
        if(!('0' <= *s && *s <= '9')) return 0;
        s++;
    }
    return 1;
}
