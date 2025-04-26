#include "types.h"
#include "stat.h"
#include "user.h"

#define function(i) i*i*i + 3*i*i - 29*i + 5

int
main(int argc, char* argv[]){
	for(int i = 0; i < 20; i++){
        int totalBytes = 0;
        int matchedBytes = 0;
        int differentBytes = 0;

		if(fork() == 0){
			for(int j = 0; j < 10; j++){
				int *arr = malloc(4096);
                totalBytes += 4096;

				for(int k = 0; k < 1024; k++){
					arr[k] = function(k);
				}

				for(int k = 0; k < 1024; k++){
					if(arr[k] == (function(k)))
						matchedBytes += 4;
                    else
                        differentBytes += 4;
				}
			}

            printf(1, "Child Number: %d\n\tTotal Bytes Allocated: %dB\n\tMatched Bytes: %dB\n\tDifferentBytes: %d\n\n", i+1, totalBytes, matchedBytes, differentBytes);
			exit();
		}
        wait();
	}

	while(wait()!=-1);
	exit();
}