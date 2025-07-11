#include <stdio.h>

unsigned sumarray(unsigned arr[], int len) {
    unsigned sum = 0;
    int i = 0;

    while (i < len) {
        sum += arr[i];
        i++;
    }

    return sum;
}

int main() {
    unsigned arr[] = {0, 1, 2, 3, 4};
    int len = sizeof(arr) / sizeof(arr[0]);

    int result = sumarray(arr, len);
    printf("Sum of array elements: %d\n", result);

    return 0;
}
