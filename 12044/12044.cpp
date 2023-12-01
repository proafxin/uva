#include <algorithm>
#include <bits/stdc++.h>
#include <csetjmp>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <memory>
#include <mutex>
#include <queue>
#include <time.h>
#include <type_traits>
#include <vector>

#define ULL unsigned long long
#define LIMIT 2000
#define MAX 100000
#define MAX_PRIME_FACTORS 10

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

ULL partialSumSumOfDivisors(ULL x) {
    ULL res = 0;
    for (ULL n = 1; n * n <= x; n++) {
        ULL y = x / n;
        res += (2 * n + 1) * y + y * y;
    }
    ULL root = (ULL)sqrt(1.0 * x);
    res -= root * root * (root + 1);

    return res >> 1;
}

bool flag[MAX];
struct Factorization {
    ULL n;
    map<ULL, ULL> primePowers;
    map<ULL, ULL> sumOfDivisorContributions;
    map<ULL, ULL> numberOfDivisorContributions;
    ULL numberOfDivisors;
    ULL sumOfDivisors;

    int mobius;
    ULL radical;

    bool operator<(Factorization p) const { return n < p.n; }
    bool operator>(Factorization p) const { return n > p.n; }
    bool operator==(Factorization p) const { return n == p.n; }

    void reset() {
        primePowers.clear();
        sumOfDivisorContributions.clear();
        numberOfDivisorContributions.clear();
        numberOfDivisors = 1;
        sumOfDivisors = 1;
        mobius = 1;
        radical = 1;
    }

    void addSinglePrimeFactor(ULL prime, ULL exponent) {
        primePowers[prime] = exponent;
        if (exponent > 1) {
            mobius *= 0;
        }

        else {
            mobius *= -1;
        }
        if (radical % prime) {
            radical *= prime;
        }

        else {
            sumOfDivisors /= sumOfDivisorContributions[prime];
            numberOfDivisors /= numberOfDivisorContributions[prime];
        }

        ULL contribution = (pow(prime, exponent + 1) - 1);
        contribution /= (prime - 1);

        sumOfDivisorContributions[prime] = contribution;
        sumOfDivisors *= contribution;
        numberOfDivisorContributions[prime] = exponent + 1;
        numberOfDivisors *= (exponent + 1);
    }

    void print() {
        cout << n << " " << radical << " " << mobius << endl;
        for (auto primePower : primePowers) {
            cout << primePower.first << " " << primePower.second << endl;
        }
    }

} factorizations[MAX];

void sieve() {
    for (ULL i = 0; i < MAX; i++) {
        factorizations[i].reset();
        factorizations[i].n = i;
    }

    for (ULL i = 2; i < MAX; i++) {
        if (!flag[i]) {
            for (ULL j = i; j < MAX; j += i) {
                flag[j] = true;
                int exponent = 0;
                ULL n = j;
                while (!(n % i)) {
                    n /= i;
                    exponent++;
                }
                factorizations[j].addSinglePrimeFactor(i, exponent);
            }
        }
    }
}

vector<ULL> getSquareFreeDivisors(Factorization factorization) {
    vector<ULL> divisors;
    divisors.clear();

    vector<ULL> primes;
    primes.clear();
    for (auto primePower : factorization.primePowers) {
        primes.push_back(primePower.first);
    }
    int numPrimes = primes.size();
    for (int i = 0; i < (1 << numPrimes); i++) {
        ULL divisor = 1;
        for (int j = 0; j < numPrimes; j++) {
            if (i & (1 << j)) {
                divisor *= primes[j];
            }
        }
        divisors.push_back(divisor);
    }

    sort(divisors.begin(), divisors.end());

    return divisors;
}

vector<ULL> squareFreeDivisors[MAX];

vector<Factorization> generateSmoothNumbers(ULL n, ULL x) {
    vector<Factorization> smoothNumbers;
    smoothNumbers.clear();

    if (n == 1) {
        return smoothNumbers;
    }

    set<Factorization> queue;
    queue.clear();

    Factorization factorization = factorizations[n];
    queue.insert(factorization);

    while (!queue.empty()) {
        Factorization cur = *queue.begin();
        queue.erase(cur);

        smoothNumbers.push_back(cur);

        for (auto primePower : factorization.primePowers) {
            ULL m = cur.n * primePower.first;
            if (m > x) {
                break;
            }
            if (m < LIMIT) {
                queue.insert(factorizations[m]);
                continue;
            }
            Factorization tmp = cur;

            queue.insert(tmp);
        }
    }

    return smoothNumbers;
}

map<ULL, vector<Factorization>> generateAllSmoothNumbers(ULL k, ULL x) {
    map<ULL, vector<Factorization>> allSmoothNumbers;
    allSmoothNumbers.clear();

    for (int i = 0; i < squareFreeDivisors[k].size(); i++) {
        ULL divisor = squareFreeDivisors[k][i];
        if (divisor > x) {
            break;
        }
        allSmoothNumbers[divisor] = generateSmoothNumbers(divisor, x);
    }

    if (!factorizations[k].mobius) {
        allSmoothNumbers[k] = generateSmoothNumbers(k, x);
    }

    return allSmoothNumbers;
}

map<ULL, vector<Factorization>> allSmoothNumbers;

struct Pair {
    ULL a, b;
};

bool operator<(Pair p, Pair q) { return (p.a < q.a) || ((p.a == q.a) && (p.b < q.b)); }

bool operator==(Pair p, Pair q) { return p.a == q.a && p.b == q.b; }

map<Pair, ULL> tauValues, sigmaValues;

Pair U(ULL k, ULL x) {
    Pair res;
    res.a = 0;
    res.b = 0;
    if (x < k) {

        return res;
    }
    Pair pair;
    pair.a = k;
    pair.b = x;

    if (tauValues.find(pair) != tauValues.end()) {
        res.a = tauValues[pair];
        res.b = sigmaValues[pair];
        return res;
    }

    if (k == 1) {
        res.a = partialSumNumberOfDivisors(x);
        res.b = partialSumSumOfDivisors(x);
        tauValues[pair] = res.a;
        sigmaValues[pair] = res.b;
        return res;
    }

    vector<Factorization> smoothNumbers = allSmoothNumbers[k];

    if (x == k) {
        res.a = smoothNumbers[0].numberOfDivisors;
        res.b = smoothNumbers[0].sumOfDivisors;
        tauValues[pair] = res.a;
        sigmaValues[pair] = res.b;
        return res;
    }

    Pair internalSum;
    internalSum.a = 0;
    internalSum.b = 0;
    ULL runningY = 0;
    for (auto smoothNumber : smoothNumbers) {
        ULL n = smoothNumber.n;
        if (n > x) {
            break;
        }
        ULL y = x / n;
        if (y == runningY) {
            res.a += smoothNumber.numberOfDivisors * internalSum.a;
            res.b += smoothNumber.sumOfDivisors * internalSum.b;
            continue;
        }

        Pair ySum;
        ySum.a = 0;
        ySum.b = 0;

        Pair internalPair;
        internalPair.a = y;
        internalPair.b = k;

        int numSquareFreeDivisors = squareFreeDivisors[k].size();
        for (int i = 0; i < numSquareFreeDivisors && squareFreeDivisors[k][i] <= x; i++) {
            ULL divisor = squareFreeDivisors[k][i];
            Pair prev = U(divisor, y);
            ySum.a += factorizations[divisor].mobius * prev.a;
            ySum.b += factorizations[divisor].mobius * prev.b;
        }

        res.a += ySum.a * smoothNumber.numberOfDivisors;
        res.b += ySum.b * smoothNumber.sumOfDivisors;
        runningY = y;
    }

    tauValues[pair] = res.a;
    sigmaValues[pair] = res.b;

    return res;
}

int main() {
    // freopen("sample.txt", "r", stdin);
    sieve();
    for (ULL n = 2; n < MAX; n++) {
        squareFreeDivisors[n] = getSquareFreeDivisors(factorizations[n]);
    }

    for (int i = 1; i < 20; i++) {
        cout << i;
        for (auto divisor : squareFreeDivisors[i]) {
            cout << " " << divisor;
        }
        cout << endl;
        for (auto primePower : factorizations[i].sumOfDivisorContributions) {
            cout << primePower.first << " "
                 << factorizations[i].numberOfDivisorContributions[primePower.first] << " "
                 << primePower.second << endl;
        }
    }

    // for (ULL i = 2; i < LIMIT; i++) {
    //     generateSmoothNumbers(i, (ULL)1e12);
    // }

    // for (ULL n = 1; n < 20; n++) {
    //     // factorizations[n].print();
    //     cout << n << " " << factorizations[n].numberOfDivisors << " "
    //          << factorizations[n].sumOfDivisors << endl;
    //     for (int i = 0; i < factorizations[n].numPrimeFactors; i++) {
    //         cout << factorizations[n].primeFactors[i] << " " << factorizations[n].exponents[i]
    //              << " " << factorizations[n].sumOfDivisorContributions[i] << endl;
    //     }
    // }

    // for (ULL n = 1; n <= 20; n++) {
    //     cout << n;
    //     for (int i = 0; i < squareFreeDivisors[n].size(); i++) {
    //         cout << " " << squareFreeDivisors[n][i];
    //     }
    //     cout << endl;
    // }

    // ULL x = 200;
    // for (ULL i = 0; i < 5; i++) {
    //     ULL n = rand() % 20 + 1;
    //     vector<Factorization> smoothNumbers = generateSmoothNumbers(n, x);
    //     for (int j = 0; j < smoothNumbers.size(); j++) {
    //         cout << smoothNumbers[j].n << " " << smoothNumbers[j].radical << " "
    //              << smoothNumbers[j].mobius;
    //         for (int k = 0; k < smoothNumbers[j].numPrimeFactors; k++) {
    //             cout << " " << smoothNumbers[j].primeFactors[k] << "^"
    //                  << smoothNumbers[j].exponents[k];
    //         }
    //         cout << endl;
    //     }
    //     cout << endl;
    // }

    // allSmoothNumbers = generateAllSmoothNumbers(210, (ULL)3e3);

    // for (auto smoothNumbers : allSmoothNumbers) {
    //     cout << smoothNumbers.first << endl;
    //     for (auto smoothNumber : smoothNumbers.second) {
    //         cout << smoothNumber.n << " " << smoothNumber.numberOfDivisors << " "
    //              << smoothNumber.sumOfDivisors << endl;
    //         for (int i = 0; i < smoothNumber.numPrimeFactors; i++) {
    //             cout << smoothNumber.primeFactors[i] << " " << smoothNumber.exponents[i] << endl;
    //         }
    //         cout << smoothNumber.radical << " " << smoothNumber.mobius << endl;
    //     }
    // }

    int tc;
    scanf("%d", &tc);

    while (tc--) {
        ULL a, b, k;
        scanf("%llu %llu %llu", &a, &b, &k);
        allSmoothNumbers = generateAllSmoothNumbers(k, b);
        // for (auto smoothNumbers : allSmoothNumbers) {
        //     for (int j = 0; j < smoothNumbers.second.size(); j++) {
        //         cout << " " << smoothNumbers.second[j].n;
        //     }
        //     cout << endl;
        // }

        // cout << F(a, b, k) << " " << G(a, b, k) << endl;
        Pair res1 = U(k, b);
        Pair res2 = U(k, a - 1);
        printf("%llu %llu\n", res1.a - res2.a, res1.b - res2.b);
        // cout << res1.a - res2.a << " " << res1.b - res2.b << endl;
    }

    return 0;
}
