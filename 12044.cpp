#include <algorithm>
#include <bits/stdc++.h>
#include <csetjmp>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <queue>
#include <time.h>
#include <type_traits>
#include <vector>

#define ULL unsigned long long
#define LIMIT 2000

using namespace std;

ULL partialSumNumberOfDivisors(ULL x) {
    ULL res = 0;
    for (ULL n = 1; n * n <= x; n++) {
        res += (x / n);
    }
    res <<= 1;
    ULL root = (ULL)sqrt(x);
    res -= root * root;

    return res;
}

ULL partial_sum_sum_of_divisors(ULL x) {
    ULL res = 0;
    for (ULL n = 1; n * n <= x; n++) {
        ULL y = x / n;
        res += (2 * n + 1) * y + y * y;
    }
    ULL root = (ULL)sqrt(1.0 * x);
    res -= root * root * (root + 1);

    return res >> 1;
}

int main() {

    int tc;
    scanf("%d", &tc);

    while (tc--) {
        ULL a, b, k;
        scanf("%llu %llu %llu", &a, &b, &k);
        // cout << F(a, b, k) << endl;
        // cout << G(a, b, k) << endl;
    }

    return 0;
}
