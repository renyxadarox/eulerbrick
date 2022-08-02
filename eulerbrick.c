#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <inttypes.h>
#include <string.h>
#include <time.h>
#include <libgen.h>
#include <gmp.h>

#ifdef BOINC
    #include "boinc_api.h"
#endif

#ifdef __linux__
	#include <sys/utsname.h>
#endif

#define PROGRAM_NAME "Euler brick"
#define VERSION "1.06"
#define YEARS "2022"
#define AUTHOR "Alexander Belogourov aka x3mEn"

#ifdef _WIN64
    const char* OS = "Windows 64-bit";
#elif _WIN32
    const char* OS = "Windows 32-bit";
#elif __APPLE__ || __MACH__
    const char* OS = "Mac OS X";
#elif __FreeBSD__
    const char* OS = "FreeBSD";
#elif __linux__
    const char* OS = "Linux";
#else
    const char* OS = "Other";
#endif

int almost = 0;            // search for almost perfect cuboids
int complex_num = 0;       // search for cuboids in Complex numbers
int derivative = 0;        // generate derivative cuboids
int body = 0;              // search for Body cuboids
int edge = 0;              // search for Edge cuboids
int face = 0;              // search for Face cuboids
int pcomplex = 0;          // search for Perfect Complex cuboids
int imaginary = 0;         // search for Imaginary cuboids
int twilight = 0;          // search for Twilight cuboids
int midnight = 0;          // search for Midnight cuboids
int progress = 0;          // display progress bar
int quiet = 0;             // suppress output to stdout
int output = 0;            // write results to output file out_%
int report = 0;            // write task stat to report file rep_%
int backward = 0;          // search on backward direction
int skip = 0;              // skip task if output file exists
int debug = 0;             // debug mode
uint32_t debug_step = 1;
int verbose = 0;           // verbose - verbose mode
uint32_t verbose_step = 1;

// check sum
uint64_t check_sum = 0;
//uint64_t loopCnt = 0;

uint64_t ini, fin, cur, task_ini, task_fin;
char repfname[256] = "rep", outfname[256] = "out", chkfname[256] = "chk";

#ifndef HAVE_BZERO
    #define bzero(ptr,n) \
    memset(ptr, 0, n)
#endif

#define max(a,b) ((a) > (b) ? a : b)

// 6542 primes less than 2^16 = 65536
#define SMALL_PRIMES_CNT 6542

uint32_t * Primes = NULL;
uint32_t primes_size = 0;

const uint64_t minA = 3;
// good to 18446744065119617025
const uint64_t maxA = (uint64_t)UINT32_MAX * (uint64_t)UINT32_MAX;

struct timespec starttime, endtime;
FILE * fout, * frep, * fchk;

uint32_t block_size = 100000;
typedef struct {uint64_t number; uint8_t primes;} TBlock;
TBlock * Block = NULL;
uint32_t bSize = 0;

// 614889782588491410 = 2*3*5*7*11*13*17*19*23*29*31*37*41*43*47
// the largest number of different prime factors among the numbers less than 2^64, is 15
#define MAX_FACTORS_CNT 15

typedef struct {uint64_t prime; uint8_t power;} TFactor;
TFactor * Factors[MAX_FACTORS_CNT], Divisors[MAX_FACTORS_CNT];

typedef struct {mpz_t a, b, c, aa, bb, cc, gcd;} TTriple;
TTriple Triple;
typedef struct {TTriple * array; uint32_t size, used;} TTriples;
TTriples Triples;

uint32_t
     pcCnt = 0 // Perfect cuboids
    ,bcCnt = 0 // Body cuboids
    ,ecCnt = 0 // Edge cuboids
    ,fcCnt = 0 // Face cuboids
    ,ccCnt = 0 // Perfect Gaussian cuboids
    ,icCnt = 0 // Imaginary cuboids
    ,tcCnt = 0 // Twilight cuboids
    ,mcCnt = 0 // Midnight cuboids
    ,toCnt = 0; // total amount of found cuboids

mpz_t ZERO, ONE, K, L;

static __inline__ uint64_t string_to_u64(const char * s) {
  uint64_t i;
  char c ;
  int scanned = sscanf(s, "%" SCNu64 "%c", &i, &c);
  if (scanned == 1) return i;
  if (scanned > 1) {
    // TBD about extra data found
    return i;
    }
  // TBD failed to scan;
  return 0;
}

void u128_to_string(const __uint128_t n, char * s)
{
    uint64_t d4, d3, d2, d1, d0, q;
	const int size = 40; // floor(log10(2^128-1))
    char u[40];
    char * t = u;

	// n = d3*2^96 + d2*2^64 + d1*2^32 + d0
	// n = d3*79228162514264337593543950336 + d2*18446744073709551616 + d1*4294967296 + d0

	// n = d3*79_228162514_264337593_543950336 + d2*18_446744073_709551616 + d1*4_294967296 + d0

	// n = d3*79*10^27 + d3*228162514*10^18 + d3*264337593*10^9 + d3*543950336
	//                 + d2*       18*10^18 + d2*446744073*10^9 + d2*709551616
	//                                      + d1*        4*10^9 + d1*294967296
	//                                                          + d0*000000001

	// define constants

	const uint32_t k3 = 79;
	const uint32_t k2 = 228162514;
	const uint32_t k1 = 264337593;
	const uint32_t k0 = 543950336;

	const uint32_t l2 = 18;
	const uint32_t l1 = 446744073;
	const uint32_t l0 = 709551616;

	const uint32_t m1 = 4;
	const uint32_t m0 = 294967296;

	const uint32_t dec_unit = 1000000000;

    d0 = (uint32_t)n;
    d1 = (uint32_t)(n >> 32);
    d2 = (uint32_t)(n >> 64);
    d3 = n >> 96;

    d0 = (k0 * d3) + (l0 * d2) + (m0 * d1) + d0;
    q  = d0 / dec_unit;
    d0 = d0 % dec_unit;

    d1 = q + (k1 * d3) + (l1 * d2) + (m1 * d1);
    q  = d1 / dec_unit;
    d1 = d1 % dec_unit;

    d2 = q + (k2 * d3) + (l2 * d2);
    q  = d2 / dec_unit;
    d2 = d2 % dec_unit;

    d3 = q + (k3 * d3);
    q  = d3 / dec_unit;
    d3 = d3 % dec_unit;

    d4 = q;

    bzero(t, size); // zero the buffer
	sprintf(t,"%u%.9u%.9u%.9u%.9u",(uint32_t)d4,(uint32_t)d3,(uint32_t)d2,(uint32_t)d1,(uint32_t)d0);

	// trim leading zeros
	while (*t && *t == '0') t++;
	if ( *t == 0x0 ) t--; // in case number = 0

    strcpy(s, t);
}

__uint128_t gcd(__uint128_t a, __uint128_t b)
{
    while (b)
    {
        a %= b;
        if (!a) return b;
        b %= a;
    }
    return a;
}

__uint128_t gcd3(__uint128_t a, __uint128_t b, __uint128_t c)
{
    return gcd(gcd(a, b), c);
}

void save_checkpoint(uint64_t pos)
{
    fchk = fopen(chkfname, "w");
    if(fchk == NULL) {
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }

    clockid_t clk = 0;
    struct timespec curtime;
    clock_gettime(clk, &curtime);
    uint64_t dif = (curtime.tv_sec - starttime.tv_sec) * 1000 + (curtime.tv_nsec - starttime.tv_nsec)/1000000;
    fprintf(fchk,  "%" PRIu64
                  ",%" PRIu64
                  ",%" PRIu64
                  ",%" PRIu64
                  ",%d,%" PRIu64
                  ",%" PRIu32
                  ",%" PRIu32
                  ",%" PRIu32
                  ",%" PRIu32
                  ",%" PRIu32
                  ",%" PRIu32
                  ",%" PRIu32
                  ",%" PRIu32
                ,ini
                ,fin
                ,pos
                ,check_sum
                ,backward
                ,dif
                ,pcCnt
                ,bcCnt
                ,ecCnt
                ,fcCnt
                ,ccCnt
                ,icCnt
                ,tcCnt
                ,mcCnt
           );
    fflush(fchk);
    fclose(fchk);
#if defined BOINC
	boinc_checkpoint_completed();
#endif
}

int read_checkpoint(void)
{
    fchk = fopen(chkfname, "r");
    if(fchk == NULL)
        return (EXIT_FAILURE);
    char c;
    uint64_t dif;
    int scanned = fscanf(fchk, "%" SCNu64
                              ",%" SCNu64
                              ",%" SCNu64
                              ",%" SCNu64
                              ",%d,%" SCNu64
                              ",%" PRIu32
                              ",%" PRIu32
                              ",%" PRIu32
                              ",%" PRIu32
                              ",%" PRIu32
                              ",%" PRIu32
                              ",%" PRIu32
                              ",%" PRIu32
                              ",%c"
                              , &ini
                              , &fin
                              , &cur
                              , &check_sum
                              , &backward
                              , &dif
                              , &pcCnt
                              , &bcCnt
                              , &ecCnt
                              , &fcCnt
                              , &ccCnt
                              , &icCnt
                              , &tcCnt
                              , &mcCnt
                              , &c);
    fclose(fchk);
    if (scanned != 14) {
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }
    if (!cur) return 1;
        else cur += 1;
    starttime.tv_sec -= dif / 1000;
	starttime.tv_nsec -= dif / 1000000;
    toCnt = pcCnt + bcCnt + ecCnt + fcCnt + ccCnt + icCnt + tcCnt + mcCnt;
    return 0;
}

void free_primes(void)
{
    free(Primes);
}

void init_primes(void)
{
    uint32_t sq = ceil(sqrtl(fin)), cb = ceil(sqrtl(sqrtf(fin)));
    uint32_t sSize = max(ceil((float)sq / 128), SMALL_PRIMES_CNT);
    uint32_t i, j;
    uint64_t * sieve;
    sieve = (uint64_t*) calloc (sSize, sizeof(uint64_t));
    if (sieve == NULL) {
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }
    sieve[0] = 1;
    for (i = 1; i < sSize; i++) sieve[i] = 0;
    for (i = 3; i <= cb; i += 2) {
        for (j = 3*i; j <= sq; j += 2*i) {
            sieve[j >> 7] |= ((uint64_t)1 << ((j >> 1)&63));
        }
    }
    primes_size = 1; // Primes[0] reserved for 2
    for (i = 3; i <= sq; i += 2) {
        if (!(sieve[i >> 7]&((uint64_t)1 << ((i >> 1)&63)))) {
            primes_size++;
        }
    }
    Primes = (uint32_t*) malloc (sizeof(uint32_t)*primes_size);
    if (Primes == NULL) {
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }
    Primes[0] = 2;
    primes_size = 1;
    for (i = 3; i <= sq; i += 2) {
        if (!(sieve[i >> 7]&((uint64_t)1 << ((i >> 1)&63)))) {
            Primes[primes_size++] = i;
        }
    }
    free(sieve);
}

void free_block(void)
{
    if (Block != NULL)
        for (uint8_t j = 0; j < MAX_FACTORS_CNT; j++)
            free(Factors[j]);
    free(Block);
}

void init_block(uint32_t size)
{
    free_block();
    bSize = size;
    Block = (TBlock *) calloc(size, sizeof(TBlock));
    if (Block == NULL) {
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }
    for (uint8_t j = 0; j < MAX_FACTORS_CNT; j++) {
        Factors[j] = (TFactor *) calloc(size, sizeof(TFactor));
        if (Factors[j] == NULL) {
#ifdef BOINC
            boinc_finish(EXIT_FAILURE);
#endif
            exit(EXIT_FAILURE);
        }
    }

    uint64_t n = cur;
    for (uint32_t i = 0; i < size; i++) {
        Block[i].number = n;
        n += 1;
    }
}

void factorize_range(void)
{
    uint32_t i, j, k, MaxFactor = rintl(sqrtl(Block[bSize-1].number));
    uint64_t d, n;
    uint8_t p;
    n = Block[0].number;
    for (j = 0; j < primes_size && Primes[j] <= MaxFactor; j++) {
        d = Primes[j];
        k = n % d;
        if (k) {
            if (n > d)
                k = d - (n - d) % d;
            else
                k = (d - n) % d;
        }
        for (i = k; i < bSize; i += d){
            if (!(Block[i].number % d)) {
                Factors[Block[i].primes][i].prime = d;
                do {
                    Block[i].number /= d;
                    Factors[Block[i].primes][i].power++;
                } while (!(Block[i].number % d));
                Block[i].primes++;
            }
        }
    }
    for (i = 0; i < bSize; i++) {
        k = Block[i].primes;
        if (Block[i].number > 1) {
            Factors[Block[i].primes][i].prime = Block[i].number;
            Factors[Block[i].primes++][i].power++;
        }
        for (j = 0; j < k; j++)
            for (p = 0; p < Factors[j][i].power; p++)
                Block[i].number *= Factors[j][i].prime;
    }
}

void init_divisors(uint32_t i)
{
    for (uint8_t j = 0; j < Block[i].primes; j++) {
        Divisors[j].prime = Factors[j][i].prime;
        Divisors[j].power = 0;
    }
}

void free_triples(void)
{
    for (uint32_t i = 0; i < Triples.size; i++) {
        mpz_clear(Triples.array[i].a);
        mpz_clear(Triples.array[i].b);
        mpz_clear(Triples.array[i].c);
        mpz_clear(Triples.array[i].aa);
        mpz_clear(Triples.array[i].bb);
        mpz_clear(Triples.array[i].cc);
        mpz_clear(Triples.array[i].gcd);
    }
    free(Triples.array);
    Triples.array = NULL;
    Triples.used = Triples.size = 0;
}

void reset_triples(void)
{
    Triples.used = 0;
}

void init_triples(void)
{
    Triples.array = malloc(0 * sizeof(TTriple));
    Triples.used = Triples.size = 0;
}

void add_triple(TTriple Triple)
{
    if (Triples.size == Triples.used) {
        Triples.size += 1;
        Triples.array = realloc(Triples.array, Triples.size * sizeof(TTriple));
        mpz_init(Triples.array[Triples.used].a);
        mpz_init(Triples.array[Triples.used].b);
        mpz_init(Triples.array[Triples.used].c);
        mpz_init(Triples.array[Triples.used].aa);
        mpz_init(Triples.array[Triples.used].bb);
        mpz_init(Triples.array[Triples.used].cc);
        mpz_init(Triples.array[Triples.used].gcd);
    }
    mpz_set(Triples.array[Triples.used].a, Triple.a);
    mpz_set(Triples.array[Triples.used].aa, Triple.aa);
    mpz_set(Triples.array[Triples.used].b, Triple.b);
    mpz_set(Triples.array[Triples.used].bb, Triple.bb);
    mpz_set(Triples.array[Triples.used].c, Triple.c);
    mpz_set(Triples.array[Triples.used].cc, Triple.cc);
    mpz_set(Triples.array[Triples.used].gcd, Triple.gcd);
    Triples.used++;
}

__uint128_t calc_divisor(uint32_t i)
{
    __uint128_t r = 1;
    for (uint8_t j = 0; j < Block[i].primes; j++)
        for (uint8_t p = 0; p < Divisors[j].power; p++)
            r *= (__uint128_t)Divisors[j].prime;
    return r;
}

void find_triples(uint32_t i)
{
    __uint128_t d, aa, a, b, c, g;
    a = (__uint128_t)Block[i].number;
    aa = a * a;
    mpz_import(Triple.a, 1, 1, sizeof(a), 0, 0, &a);
    mpz_mul(Triple.aa, Triple.a, Triple.a);
    int found = 1, even = 1 - (a & 1);
    if (even) aa >>= 2;
    uint8_t j;
    while (found) {
        d = calc_divisor(i);
        if (found && d < (a >> even)) {
            b = aa / d - d;
            if (!even) b >>= 1;
            mpz_import(Triple.b, 1, 1, sizeof(b), 0, 0, &b);
            mpz_mul(Triple.bb, Triple.b, Triple.b);
            c = b + d;
            if (even) c += d;
            mpz_import(Triple.c, 1, 1, sizeof(c), 0, 0, &c);
            mpz_mul(Triple.cc, Triple.c, Triple.c);
            g = gcd3(a, b, c);
            mpz_import(Triple.gcd, 1, 1, sizeof(g), 0, 0, &g);
            add_triple(Triple);
        }
        // generate a new divisor
        j = 0;
        found = 0;
        do {
            if (Divisors[j].power < (Factors[j][i].power - (j==0 ? even : 0)) * 2)
                found = ++Divisors[j].power;
            else
                Divisors[j++].power = 0;
        } while (j < Block[i].primes && !found);
    };
}

void sort_triples(TTriple * s, int32_t l, int32_t h)
{
    int32_t i, j, k;
    do {
        i = l;
        j = h;
        k = (l+h) >> 1;
        do {
            while (mpz_cmp(s[i].b, s[k].b) < 0) i++;
            while (mpz_cmp(s[j].b, s[k].b) > 0) j--;
            if (i <= j) {
                mpz_swap(s[i].a, s[j].a);
                mpz_swap(s[i].aa, s[j].aa);
                mpz_swap(s[i].b, s[j].b);
                mpz_swap(s[i].bb, s[j].bb);
                mpz_swap(s[i].c, s[j].c);
                mpz_swap(s[i].cc, s[j].cc);
                mpz_swap(s[i].gcd, s[j].gcd);
                if (k == i) k = j;
                else if (k == j) k = i;
                i++;
                j--;
            }
        } while (i <= j);
        if (l < j) sort_triples(s, l, j);
        l = i;
    } while (i < h);
}

void find_cuboids(void)
{
    char * A, * B, * C, * D, * E, * F, * G, s[280];
    int32_t i, j;
    for (i = 1; i < Triples.used; i++) {
        for (j = 0; j < i; j++) {
            mpz_gcd(K, Triples.array[i].gcd, Triples.array[j].gcd);
            if (!mpz_cmp(K, ONE)) {
                if (mpz_cmp(Triples.array[j].b, Triples.array[j].a) > 0) {
                    // two pairs of triples (X, Y, Z) and (X, V, W), such that (V, Y, ?) is a PT
                    // K = V*V + Y*Y
                    mpz_add(K, Triples.array[j].bb, Triples.array[i].bb);
                    if (mpz_perfect_square_p(K)) {
                        // K = (V*V + Y*Y)
                        mpz_sqrt(K, K);
                        A = mpz_get_str(NULL, 10, Triples.array[i].a); // X
                        B = mpz_get_str(NULL, 10, Triples.array[j].b); // V
                        C = mpz_get_str(NULL, 10, Triples.array[i].b); // Y
                        D = mpz_get_str(NULL, 10, Triples.array[j].c); // W
                        E = mpz_get_str(NULL, 10, Triples.array[i].c); // Z
                        F = mpz_get_str(NULL, 10, K);
                        // (Y, W, ?) is a PT
                        // L = Y*Y + W*W
                        mpz_add(L, Triples.array[i].bb, Triples.array[j].cc);
                        if (mpz_perfect_square_p(L)) {
                            // L = (Y*Y + W*W)
                            mpz_sqrt(L, L);
                            G = mpz_get_str(NULL, 10, L);
                            // Perfect cuboid
                            sprintf(s, "P,%s,%s,%s,%s,%s,%s,%s\n", A, B, C, D, E, F, G);
                            if (!quiet) fprintf(stderr, "%s", s);
                            if (output) fprintf(fout, "%s", s);
                            pcCnt++;
                            toCnt++;
                            if (complex_num && derivative) {
                                if (midnight) {
                                    sprintf(s, "M,%si,%si,%si,%si,%si,%si,%si\n", A, B, C, D, E, F, G);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    mcCnt++;
                                    toCnt++;
                                }
                                if (pcomplex) {
                                    sprintf(s, "C,%si,%si,%s,%si,%s,%s,%s\n", B, C, G, F, E, D, A);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    ccCnt++;
                                    toCnt++;
                                }
                                if (midnight) {
                                    sprintf(s, "M,%s,%s,%si,%s,%si,%si,%si\n", B, C, G, F, E, D, A);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    mcCnt++;
                                    toCnt++;
                                }
                                if (pcomplex) {
                                    sprintf(s, "C,%si,%si,%s,%si,%s,%s,%s\n", A, C, G, E, F, D, B);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    ccCnt++;
                                    toCnt++;
                                }
                                if (midnight) {
                                    sprintf(s, "M,%s,%s,%si,%s,%si,%si,%si\n", A, C, G, E, F, D, B);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    mcCnt++;
                                    toCnt++;
                                }
                                if (pcomplex) {
                                    sprintf(s, "C,%si,%si,%s,%si,%s,%s,%s\n", B, A, G, D, E, F, C);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    ccCnt++;
                                    toCnt++;
                                }
                                if (midnight) {
                                    sprintf(s, "M:%s,%s,%si,%s,%si,%si,%si\n", B, A, G, D, E, F, C);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    mcCnt++;
                                    toCnt++;
                                }
                            }
                            continue;
                        }
                        if (almost) {
                            G = mpz_get_str(NULL, 10, L);
                            if (body) {
                                sprintf(s, "B,%s,%s,%s,%s,%s,%s,(%s)\n", A, B, C, D, E, F, G);
                                if (!quiet) fprintf(stderr, "%s", s);
                                if (output) fprintf(fout, "%s", s);
                                bcCnt++;
                                toCnt++;
                            }
                            if (complex_num && derivative) {
                                if (midnight) {
                                    sprintf(s, "M,%si,%si,%si,%si,%si,%si,(-%s)\n", A, B, C, D, E, F, G);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    mcCnt++;
                                    toCnt++;
                                }
                                if (twilight) {
                                    sprintf(s, "T,%si,%si,(%s),%si,%s,%s,%s\n", C, B, G, F, D, E, A);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    tcCnt++;
                                    toCnt++;
                                }
                                if (midnight) {
                                    sprintf(s, "M,%s,%s,(-%s),%s,%si,%si,%si\n", C, B, G, F, D, E, A);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    mcCnt++;
                                    toCnt++;
                                }
                                if (twilight) {
                                    sprintf(s, "T,%si,%si,(%s),%si,%s,%s,%s\n", C, A, G, E, D, F, B);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    tcCnt++;
                                    toCnt++;
                                }
                                if (midnight) {
                                    sprintf(s, "M,%s,%s,(-%s),%s,%si,%si,%si\n", C, A, G, E, D, F, B);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    tcCnt++;
                                    toCnt++;
                                }
                                if (twilight) {
                                    sprintf(s, "T,%si,%si,(%s),%si,%s,%s,%s\n", B, A, G, D, E, F, C);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    tcCnt++;
                                    toCnt++;
                                }
                                if (midnight) {
                                    sprintf(s, "M,%s,%s,(-%s),%s,%si,%si,%si\n", B, A, G, D, E, F, C);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    mcCnt++;
                                    toCnt++;
                                }
                            }
                            continue;
                        }
                    }
                }
                if (almost) {
                    if (mpz_cmp(Triples.array[j].b, Triples.array[j].a) > 0) {
                        // two pairs of triples (X, Y, Z) and (X, V, W) such that (Y, W, ?) is a PT
                        // K = Y*Y + W*W
                        mpz_add(K, Triples.array[i].bb, Triples.array[j].cc);
                        if (mpz_perfect_square_p(K)) {
                            // K = (Y*Y + W*W)
                            mpz_sqrt(K, K);
                            // L = K*K - X*X
                            mpz_mul(L, K, K);
                            mpz_sub(L, L, Triples.array[i].aa);
                            A = mpz_get_str(NULL, 10, Triples.array[i].a); // X
                            B = mpz_get_str(NULL, 10, Triples.array[j].b); // V
                            C = mpz_get_str(NULL, 10, Triples.array[i].b); // Y
                            D = mpz_get_str(NULL, 10, Triples.array[j].c); // W
                            E = mpz_get_str(NULL, 10, Triples.array[i].c); // Z
                            F = mpz_get_str(NULL, 10, L);
                            G = mpz_get_str(NULL, 10, K);
                            if (face) {
                                sprintf(s, "F,%s,%s,%s,%s,%s,(%s),%s\n", A, B, C, D, E, F, G);
                                if (!quiet) fprintf(stderr, "%s", s);
                                if (output) fprintf(fout, "%s", s);
                                fcCnt++;
                                toCnt++;
                            }
                            if (complex_num && derivative) {
                                if (midnight) {
                                    sprintf(s, "M,%si,%si,%si,%si,%si,(-%s),%si\n", A, B, C, D, E, F, G);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    mcCnt++;
                                    toCnt++;
                                }
                                if (twilight) {
                                    sprintf(s, "T,%si,%si,%s,(-%s),%s,%s,%s\n", C, B, G, F, D, E, A);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    tcCnt++;
                                    toCnt++;
                                }
                                if (midnight) {
                                    sprintf(s, "M,%s,%s,%si,(%s),%si,%si,%si\n", C, B, G, F, D, E, A);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    mcCnt++;
                                    toCnt++;
                                }
                                if (twilight) {
                                    sprintf(s, "T,%si,%si,%s,%si,%s,(%s),%s\n", C, A, G, E, D, F, B);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    tcCnt++;
                                    toCnt++;
                                }
                                if (midnight) {
                                    sprintf(s, "M,%s,%s,%si,%s,%si,(-%s),%si\n", C, A, G, E, D, F, B);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    mcCnt++;
                                    toCnt++;
                                }
                                if (twilight) {
                                    sprintf(s, "T,%si,%si,%s,%si,%s,(%s),%s\n", B, A, G, D, E, F, C);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    tcCnt++;
                                    toCnt++;
                                }
                                if (midnight) {
                                    sprintf(s, "M,%s,%s,%si,%s,%si,(-%s),%si\n", B, A, G, D, E, F, C);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    mcCnt++;
                                    toCnt++;
                                }
                                // L = W*W + Z*Z
                                mpz_add(L, Triples.array[j].cc, Triples.array[i].cc);
                                if (mpz_perfect_square_p(L)) {
                                    // L = (W*W + Z*Z)
                                    mpz_sqrt(L, K);
                                    F = mpz_get_str(NULL, 10, L);
                                    if (pcomplex) {
                                        sprintf(s, "C,%si,%s,%s,%s,%s,%s,%s\n", A, D, E, B, C, F, G);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        ccCnt++;
                                        toCnt++;
                                    }
                                    if (midnight) {
                                        sprintf(s, "M,%s,%si,%si,%si,%si,%si,%si\n", A, D, E, B, C, F, G);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        mcCnt++;
                                        toCnt++;
                                    }
                                }
                                else {
                                    F = mpz_get_str(NULL, 10, L);
                                    if (imaginary) {
                                        sprintf(s, "I,%si,%s,%s,%s,%s,(%s),%s\n", A, D, E, B, C, F, G);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        icCnt++;
                                        toCnt++;
                                    }
                                    if (midnight) {
                                        sprintf(s, "M,%s,%si,%si,%si,%si,(-%s),%si\n", A, D, E, B, C, F, G);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        mcCnt++;
                                        toCnt++;
                                    }
                                    if (twilight) {
                                        sprintf(s, "T,%s,%s,%si,(%s),%si,%si,%s\n", E, D, G, F, B, C, A);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        tcCnt++;
                                        toCnt++;
                                    }
                                    if (midnight) {
                                        sprintf(s, "M,%si,%si,%s,(-%s),%s,%s,%si\n", E, D, G, F, B, C, A);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        mcCnt++;
                                        toCnt++;
                                    }
                                    if (twilight) {
                                        sprintf(s, "T,%s,%si,%s,%si,(%s),%s,%s\n", A, E, G, C, F, B, D);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        tcCnt++;
                                        toCnt++;
                                    }
                                    if (midnight) {
                                        sprintf(s, "M,%si,%s,%si,%s,(-%s),%si,%si\n", A, E, G, C, F, B, D);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        mcCnt++;
                                        toCnt++;
                                    }
                                    if (twilight) {
                                        sprintf(s, "T,%s,%si,%s,%si,(%s),%s,%s\n", A, D, G, B, F, C, E);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        tcCnt++;
                                        toCnt++;
                                    }
                                    if (midnight) {
                                        sprintf(s, "M,%si,%s,%si,%s,(-%s),%si,%si\n", A, E, G, C, F, B, D);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        mcCnt++;
                                        toCnt++;
                                    }
                                }
                                // L = Y*Y - V*V
                                mpz_sub(L, Triples.array[i].bb, Triples.array[j].bb);
                                if (mpz_perfect_square_p(L)) {
                                    // L = (Y*Y - V*V)
                                    mpz_sqrt(L, L);
                                    F = mpz_get_str(NULL, 10, L);
                                    if (pcomplex) {
                                        sprintf(s, "C,%si,%s,%s,%s,%s,%s,%s\n", B, D, C, A, F, G, E);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        ccCnt++;
                                        toCnt++;
                                    }
                                    if (midnight) {
                                        sprintf(s, "M,%s,%si,%si,%si,%si,%si,%si\n", B, D, C, A, F, G, E);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        mcCnt++;
                                        toCnt++;
                                    }
                                }
                                else {
                                    F = mpz_get_str(NULL, 10, L);
                                    if (imaginary) {
                                        sprintf(s, "I,%si,%s,%s,%s,(%s),%s,%s\n", B, D, C, A, F, G, E);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        icCnt++;
                                        toCnt++;
                                    }
                                    if (midnight) {
                                        sprintf(s, "M,%s,%si,%si,%si,(-%s),%si,%si\n", B, D, C, A, F, G, E);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        mcCnt++;
                                        toCnt++;
                                    }
                                    if (twilight) {
                                        sprintf(s, "T,%s,%s,%si,%s,(-%s),%si,%s\n", D, C, E, G, F, A, B);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        tcCnt++;
                                        toCnt++;
                                    }
                                    if (midnight) {
                                        sprintf(s, "M,%si,%si,%s,%si,(%s),%s,%si\n", D, C, E, G, F, A, B);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        mcCnt++;
                                        toCnt++;
                                    }
                                    if (twilight) {
                                        sprintf(s, "T,%s,%si,%s,(-%s),%s,%s,%s\n", B, C, E, F, G, A, D);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        tcCnt++;
                                        toCnt++;
                                    }
                                    if (midnight) {
                                        sprintf(s, "M,%si,%s,%si,(%s),%si,%si,%si\n", B, C, E, F, G, A, D);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        mcCnt++;
                                        toCnt++;
                                    }
                                    if (twilight) {
                                        sprintf(s, "T,%s,%si,%s,%si,%s,(%s),%s\n", B, D, E, A, G, F, C);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        tcCnt++;
                                        toCnt++;
                                    }
                                    if (midnight) {
                                        sprintf(s, "M,%si,%s,%si,%s,%si,(-%s),%si\n", B, D, E, A, G, F, C);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        mcCnt++;
                                        toCnt++;
                                    }
                                }
                            }
                            continue;
                        }
                    }
                    if (mpz_cmp(Triples.array[j].b, Triples.array[j].a) > 0  && mpz_cmp(Triples.array[i].b, Triples.array[j].c) > 0) {
                        // two pairs of triples (X, Y, Z) and (X, V, W) such that (W, ?, Z) is a PT
                        // K = Z*Z - W*W
                        mpz_sub(K, Triples.array[i].cc, Triples.array[j].cc);
                        if (mpz_perfect_square_p(K)) {
                            // K = (Ze*Z - W*W)
                            mpz_sqrt(K, K);
                            // L = K*K + X*X
                            mpz_mul(L, K, K);
                            mpz_add(L, L, Triples.array[i].aa);
                            A = mpz_get_str(NULL, 10, Triples.array[i].a); // X
                            B = mpz_get_str(NULL, 10, Triples.array[j].b); // V
                            C = mpz_get_str(NULL, 10, K);
                            D = mpz_get_str(NULL, 10, Triples.array[j].c); // W
                            E = mpz_get_str(NULL, 10, L);
                            F = mpz_get_str(NULL, 10, Triples.array[i].b); // Y
                            G = mpz_get_str(NULL, 10, Triples.array[i].c); // Z
                            if (face) {
                                sprintf(s, "F,%s,%s,%s,%s,(%s),%s,%s\n", A, B, C, D, E, F, G);
                                if (!quiet) fprintf(stderr, "%s", s);
                                if (output) fprintf(fout, "%s", s);
                                fcCnt++;
                                toCnt++;
                            }
                            if (complex_num && derivative) {
                                if (midnight) {
                                    sprintf(s, "M,%si,%si,%si,%si,(-%s),%si,%si\n", A, B, C, D, E, F, G);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    mcCnt++;
                                    toCnt++;
                                }
                                if (twilight) {
                                    sprintf(s, "T,%si,%si,%s,%si,%s,(%s),%s\n", C, B, G, F, D, E, A);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    tcCnt++;
                                    toCnt++;
                                }
                                if (midnight) {
                                    sprintf(s, "M,%s,%s,%si,%s,%si,(-%s),%si\n", C, B, G, F, D, E, A);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    mcCnt++;
                                    toCnt++;
                                }
                                if (twilight) {
                                    sprintf(s, "T,%si,%si,%s,(-%s),%s,%s,%s\n", C, A, G, E, D, F, B);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    tcCnt++;
                                    toCnt++;
                                }
                                if (midnight) {
                                    sprintf(s, "M,%s,%s,%si,(%s),%si,%si,%si\n", C, A, G, E, D, F, B);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    mcCnt++;
                                    toCnt++;
                                }
                                if (twilight) {
                                    sprintf(s, "T,%si,%si,%s,%si,(%s),%s,%s\n", B, A, G, D, E, F, C);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    tcCnt++;
                                    toCnt++;
                                }
                                if (midnight) {
                                    sprintf(s, "M,%s,%s,%si,%s,(-%s),%si,%si\n", B, A, G, D, E, F, C);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    mcCnt++;
                                    toCnt++;
                                }
                                // L = K*K - X*X
                                mpz_mul(L, K, K);
                                mpz_sub(L, L, Triples.array[i].aa);
                                if (mpz_perfect_square_p(L)) {
                                    // L = (K*K - X*X)
                                    mpz_sqrt(L, L);
                                    E = mpz_get_str(NULL, 10, L);
                                    if (pcomplex) {
                                        sprintf(s, "C,%si,%s,%s,%s,%s,%s,%s\n", A, D, C, B, E, G, F);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        ccCnt++;
                                        toCnt++;
                                    }
                                    if (midnight) {
                                        sprintf(s, "M,%s,%si,%si,%si,%si,%si,%si\n", A, D, C, B, E, G, F);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        mcCnt++;
                                        toCnt++;
                                    }
                                }
                                else {
                                    E = mpz_get_str(NULL, 10, L);
                                    if (imaginary) {
                                        sprintf(s, "I,%si,%s,%s,%s,(%s),%s,%s\n", A, D, C, B, E, G, F);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        icCnt++;
                                        toCnt++;
                                    }
                                    if (midnight) {
                                        sprintf(s, "M,%s,%si,%si,%si,(-%s),%si,%si\n", A, D, C, B, E, G, F);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        mcCnt++;
                                        toCnt++;
                                    }
                                    if (twilight) {
                                        sprintf(s, "T,%s,%s,%si,%s,(-%s),%si,%s\n", D, C, F, G, E, B, A);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        tcCnt++;
                                        toCnt++;
                                    }
                                    if (midnight) {
                                        sprintf(s, "M,%si,%si,%s,%si,(%s),%s,%si\n", D, C, F, G, E, B, A);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        mcCnt++;
                                        toCnt++;
                                    }
                                    if (twilight) {
                                        sprintf(s, "T,%s,%si,%s,(-%s),%s,%s,%s\n", A, C, F, E, G, B, D);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        tcCnt++;
                                        toCnt++;
                                    }
                                    if (midnight) {
                                        sprintf(s, "M,%si,%s,%si,(%s),%si,%si,%si\n", A, C, F, E, G, B, D);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        mcCnt++;
                                        toCnt++;
                                    }
                                    if (twilight) {
                                        sprintf(s, "T,%s,%si,%s,%si,%s,(%s),%s\n", A, D, F, B, G, E, C);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        tcCnt++;
                                        toCnt++;
                                    }
                                    if (midnight) {
                                        sprintf(s, "M,%si,%s,%si,%s,%si,(-%s),%si\n", A, D, F, B, G, E, C);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        mcCnt++;
                                        toCnt++;
                                    }
                                }

                                // L = Y*Y + W*W
                                mpz_add(L, Triples.array[i].bb, Triples.array[j].cc);
                                if (mpz_perfect_square_p(L)) {
                                    // L = (Y*Y + W*W)
                                    mpz_sqrt(L, L);
                                    E = mpz_get_str(NULL, 10, L);
                                    if (pcomplex) {
                                        sprintf(s, "C,%si,%s,%s,%s,%s,%s,%s\n", B, D, F, A, C, E, G);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        ccCnt++;
                                        toCnt++;
                                    }
                                    if (midnight) {
                                        sprintf(s, "M,%s,%si,%si,%si,%si,%si,%si\n", B, D, F, A, C, E, G);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        mcCnt++;
                                        toCnt++;
                                    }
                                }
                                else {
                                    E = mpz_get_str(NULL, 10, L);
                                    if (imaginary) {
                                        sprintf(s, "I,%si,%s,%s,%s,%s,(%s),%s\n", B, D, F, A, C, E, G);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        icCnt++;
                                        toCnt++;
                                    }
                                    if (midnight) {
                                        sprintf(s, "M,%s,%si,%si,%si,%si,(-%s),%si\n", B, D, F, A, C, E, G);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        mcCnt++;
                                        toCnt++;
                                    }
                                    if (twilight) {
                                        sprintf(s, "T,%s,%s,%si,(%s),%si,%si,%s\n", D, F, G, E, C, A, B);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        tcCnt++;
                                        toCnt++;
                                    }
                                    if (midnight) {
                                        sprintf(s, "M,%si,%si,%s,(-%s),%s,%s,%si\n", D, F, G, E, C, A, B);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        mcCnt++;
                                        toCnt++;
                                    }
                                    if (twilight) {
                                        sprintf(s, "T,%s,%si,%s,%si,(%s),%s,%s\n", B, F, G, C, E, A, D);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        tcCnt++;
                                        toCnt++;
                                    }
                                    if (midnight) {
                                        sprintf(s, "M,%si,%s,%si,%s,(-%s),%si,%si\n", B, F, G, C, E, A, D);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        mcCnt++;
                                        toCnt++;
                                    }
                                    if (twilight) {
                                        sprintf(s, "T,%s,%si,%s,%si,(%s),%s,%s\n", B, D, G, A, E, C, F);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        tcCnt++;
                                        toCnt++;
                                    }
                                    if (midnight) {
                                        sprintf(s, "M,%si,%s,%si,%s,(-%s),%si,%si\n", B, F, G, C, E, A, D);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        mcCnt++;
                                        toCnt++;
                                    }
                                }
                            }
                            continue;
                        }
                    }
                    if (mpz_cmp(Triples.array[j].b, Triples.array[j].a) > 0 && mpz_cmp(Triples.array[i].b, Triples.array[j].b) > 0) {
                        // two pairs of triples (X, Y, Z) and (X, V, W) such that (V, ?, Z) is a PT
                        // K = Z*Z - V*V
                        mpz_sub(K, Triples.array[i].cc, Triples.array[j].bb);
                        if (mpz_perfect_square_p(K)) {
                            // K = (Z*Z - V*V)
                            mpz_sqrt(K, K);
                            // L = K*K - X*X
                            mpz_mul(L, K, K);
                            mpz_sub(L, L, Triples.array[i].aa);
                            A = mpz_get_str(NULL, 10, Triples.array[i].a); // X
                            B = mpz_get_str(NULL, 10, Triples.array[j].b); // V
                            C = mpz_get_str(NULL, 10, L);
                            D = mpz_get_str(NULL, 10, Triples.array[j].c); // W
                            E = mpz_get_str(NULL, 10, K);
                            F = mpz_get_str(NULL, 10, Triples.array[i].b); // Y
                            G = mpz_get_str(NULL, 10, Triples.array[i].c); // Z
                            if (edge) {
                                sprintf(s, "E,%s,%s,(%s),%s,%s,%s,%s\n", A, B, C, D, E, F, G);
                                if (!quiet) fprintf(stderr, "%s", s);
                                if (output) fprintf(fout, "%s", s);
                                ecCnt++;
                                toCnt++;
                            }
                            if (complex_num && derivative) {
                                if (midnight) {
                                    sprintf(s, "M,%si,%si,(-%s),%si,%si,%si,%si\n", A, B, C, D, E, F, G);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    mcCnt++;
                                    toCnt++;
                                }
                                if (twilight) {
                                    sprintf(s, "T,(-%s),%si,%s,%si,%s,%s,%s\n", C, B, G, F, D, E, A);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    tcCnt++;
                                    toCnt++;
                                }
                                if (midnight) {
                                    sprintf(s, "M,(%s),%s,%si,%s,%si,%si,%si\n", C, B, G, F, D, E, A);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    mcCnt++;
                                    toCnt++;
                                }
                                if (twilight) {
                                    sprintf(s, "T,(-%s),%si,%s,%si,%s,%s,%s\n", C, A, G, E, D, F, B);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    tcCnt++;
                                    toCnt++;
                                }
                                if (midnight) {
                                    sprintf(s, "M,(%s),%s,%si,%s,%si,%si,%si\n", C, A, G, E, D, F, B);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    mcCnt++;
                                    toCnt++;
                                }
                                if (twilight) {
                                    sprintf(s, "T,%si,%si,%s,%si,%s,%s,(%s)\n", B, A, G, D, E, F, C);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    tcCnt++;
                                    toCnt++;
                                }
                                if (midnight) {
                                    sprintf(s, "M,%s,%s,%si,%s,%si,%si,(-%s)\n", B, A, G, D, E, F, C);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    mcCnt++;
                                    toCnt++;
                                }
                            }
                            continue;
                        }
                    }
                    if (complex_num) {
                        if (mpz_cmp(Triples.array[i].b, Triples.array[i].a) > 0 && mpz_cmp(Triples.array[j].c, Triples.array[i].b) > 0) {
                            // two pairs of triples (X, Y, Z) and (X, V, W) such that (Y, ?, W) is a PT and Y < W
                            // K = W*W - Y*Y
                            mpz_sub(K, Triples.array[j].cc, Triples.array[i].bb);
                            if (mpz_perfect_square_p(K)) {
                                // K = (W*W + Y*Y)
                                mpz_sqrt(K, K);
                                // L = X*X - K*K
                                mpz_set(L, Triples.array[i].aa);
                                mpz_submul(L, K, K);
                                A = mpz_get_str(NULL, 10, Triples.array[i].a); // X
                                B = mpz_get_str(NULL, 10, Triples.array[i].b); // Y
                                C = mpz_get_str(NULL, 10, L);
                                D = mpz_get_str(NULL, 10, Triples.array[i].c); // Z
                                E = mpz_get_str(NULL, 10, K);
                                F = mpz_get_str(NULL, 10, Triples.array[j].b); // V
                                G = mpz_get_str(NULL, 10, Triples.array[j].c); // W
                                if (imaginary) {
                                    sprintf(s, "I,%s,%s,(-%s),%s,%s,%s,%s\n", A, B, C, D, E, F, G);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    icCnt++;
                                    toCnt++;
                                }
                                if (derivative) {
                                    if (midnight) {
                                        sprintf(s, "M,%si,%si,(%s),%si,%si,%si,%si\n", A, B, C, D, E, F, G);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        mcCnt++;
                                        toCnt++;
                                    }
                                    if (twilight) {
                                        sprintf(s, "T,%si,(%s),%s,%si,%s,%s,%s\n", B, C, G, F, E, D, A);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        tcCnt++;
                                        toCnt++;
                                    }
                                    if (midnight) {
                                        sprintf(s, "M,%s,(-%s),%si,%s,%si,%si,%si\n", B, C, G, F, E, D, A);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        mcCnt++;
                                        toCnt++;
                                    }
                                    if (twilight) {
                                        sprintf(s, "T,%si,(%s),%s,%si,%s,%s,%s\n", A, C, G, E, F, D, B);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        tcCnt++;
                                        toCnt++;
                                    }
                                    if (midnight) {
                                        sprintf(s, "M,%s,(-%s),%si,%s,%si,%si,%si\n", A, C, G, E, F, D, B);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        mcCnt++;
                                        toCnt++;
                                    }
                                    if (twilight) {
                                        sprintf(s, "T,%s,%s,%si,%s,%si,%si,(%s)\n", A, B, G, D, F, E, C);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        tcCnt++;
                                        toCnt++;
                                    }
                                    if (midnight) {
                                        sprintf(s, "M,%si,%si,%s,%si,%s,%s,(-%s)\n", A, B, G, D, F, E, C);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        mcCnt++;
                                        toCnt++;
                                    }
                                }
                                continue;
                            }
                        }
                        if (mpz_cmp(Triples.array[i].b, Triples.array[i].a) > 0 && mpz_cmp(Triples.array[i].b, Triples.array[j].c) > 0) {
                            // two pairs of triples (X, Y, Z) and (X, V, W) such that (Y, ?, W) is a PT and Y > W
                            // K = Y*Y - W*W
                            mpz_sub(K, Triples.array[i].bb, Triples.array[j].cc);
                            if (mpz_perfect_square_p(K)) {
                                // K = (Y*Y - W*W)
                                mpz_sqrt(K, K);
                                // L = Z*Z - W*W
                                mpz_sub(L, Triples.array[i].cc, Triples.array[j].cc);
                                A = mpz_get_str(NULL, 10, Triples.array[i].a); // X
                                B = mpz_get_str(NULL, 10, Triples.array[i].b); // Y
                                C = mpz_get_str(NULL, 10, L);
                                D = mpz_get_str(NULL, 10, Triples.array[i].c); // Z
                                E = mpz_get_str(NULL, 10, K);
                                F = mpz_get_str(NULL, 10, Triples.array[j].b); // V
                                G = mpz_get_str(NULL, 10, Triples.array[j].c); // W
                                if (twilight) {
                                    sprintf(s, "T,%s,%s,(-%s),%s,%si,%s,%s\n", A, B, C, D, E, F, G);
                                    if (!quiet) fprintf(stderr, "%s", s);
                                    if (output) fprintf(fout, "%s", s);
                                    tcCnt++;
                                    toCnt++;
                                }
                                if (derivative) {
                                    if (midnight) {
                                        sprintf(s, "M,%si,%si,(%s),%si,%s,%si,%si\n", A, B, C, D, E, F, G);
                                        if (!quiet) fprintf(stderr, "%s", s);
                                        if (output) fprintf(fout, "%s", s);
                                        mcCnt++;
                                        toCnt++;
                                    }
                                }
                                continue;
                            }
                        }
                    }
                }
            }
        }
    }
}

int init_task(void)
{
    if (ini > fin) return 1;
    if (ini < minA) ini = minA;
    if (fin > maxA) fin = maxA;
    cur = ini;
    return 0;
}

static __inline__ int next_task(void)
{
    if (maxA - 1 >= cur) cur += 1;
    else return 6;
    if (cur > fin) return 7;
    return 0;
}

#define PBSTR "========================================================================"
#define PBWIDTH 35
#define SCRWIDTH 80
void do_progress( double percentage )
{
    int val = (int) (percentage);
    int lpad = (int) (percentage  * (val==100?SCRWIDTH:PBWIDTH) / 100);
    int rpad = (val==100?SCRWIDTH:PBWIDTH) - lpad;
    //fill progress bar with spaces
    fprintf(stderr, "\r%3d%% [%.*s%*s]", val, lpad, PBSTR, rpad, "");
    if (val!=100) {
        char midnight_str[40], complex_str[40];
        sprintf(midnight_str, ",%" PRIu32, mcCnt);
        sprintf(complex_str, ",%" PRIu32 ",%" PRIu32 ",%" PRIu32 "%s", ccCnt, icCnt, tcCnt, midnight ? midnight_str : "");
        fprintf(stderr, " (%" PRIu32 ",%" PRIu32 ",%" PRIu32 ",%" PRIu32 "%s)", pcCnt, bcCnt, ecCnt, fcCnt, complex_num ? complex_str : "");
    }
}

void print_factors(uint32_t i)
{
    uint64_t n = Block[i].number;
    char divisorsStr[256];
    bzero(divisorsStr, 256);
    for (int j=0; j < Block[i].primes; j++) {
        if (j > 0) sprintf(divisorsStr, "%s * ", divisorsStr);
        sprintf(divisorsStr, "%s%" PRIu64, divisorsStr, Factors[j][i].prime);
        if (Factors[j][i].power > 1) sprintf(divisorsStr, "%s^%i", divisorsStr, Factors[j][i].power);
    }
    fprintf(stderr, "%" PRIu64 " = %s\n",n,divisorsStr);
}

void print_triples(void)
{
    char * A, * B, * C;
    for (int j=0; j < Triples.used; j++) {
        A = mpz_get_str(NULL, 10, Triples.array[j].a);
        B = mpz_get_str(NULL, 10, Triples.array[j].b);
        C = mpz_get_str(NULL, 10, Triples.array[j].c);
        fprintf(stderr, "(%s,%s,%s)\n", A, B, C);
    }
}

void print_usage(char * name)
{
#ifdef _WIN32
	char pref[3] = "";
#elif __linux__ || unix || __unix__ || __unix
	char pref[3] = "./";
#endif // __linux__
    fprintf(stderr, "Usage: %s%s <low> <high> [switches]\n", pref, name);
    fprintf(stderr, "\t<low>\tlower border\n");
    fprintf(stderr, "\t<high>\thigher border\n");
    fprintf(stderr, "The following switches are accepted:\n");
    fprintf(stderr, "\t-a\tsearch for almost-perfect cuboids\n");
    fprintf(stderr, "\t-c\tsearch for cuboids in complex numbers\n");
    fprintf(stderr, "\t-f\tgenerate derivative cuboids\n");
    fprintf(stderr, "\t-t (BEFCITM)\n");
    fprintf(stderr, "\t   (P)erfect \t cuboid whose 3 edges, 3 face diagonals and the body diagonal are all integer\n");
    fprintf(stderr, "\t   (B)ody \t cuboid has 6 integer lengths and irrational body diagonal\n");
    fprintf(stderr, "\t   (E)dge \t cuboid has 6 integer lengths and one of the edges is irrational\n");
    fprintf(stderr, "\t   (F)ace \t cuboid has 6 integer lengths and one of the face diagonals is irrational\n");
    fprintf(stderr, "\t   (C)omplex \t Perfect cuboid whose all lengths are Gaussian integers\n");
    fprintf(stderr, "\t   (I)maginary \t cuboid has edge(s) in complex numbers, 6 Gaussian lengths out of 7\n");
    fprintf(stderr, "\t   (T)wilight \t cuboid has edge(s) and face diagonal(s) in complex numbers, 6 Gaussian lengths out of 7\n");
    fprintf(stderr, "\t   (M)idnight \t cuboid has the body diagonal in complex numbers, 6 Gaussian lengths out of 7\n");
    fprintf(stderr, "\t-q\tsuppress output to stdout\n");
    fprintf(stderr, "\t-p\tdisplay progress bar\n");
    fprintf(stderr, "\t-o\twrite results to output file\n");
    fprintf(stderr, "\t-r\twrite task stat to report file\n");
    fprintf(stderr, "\t-s\tskip task if output file exists\n");
    fprintf(stderr, "\t-b [s]\tblock size (default value: %" PRIu32 ")\n", block_size);
    fprintf(stderr, "\t-d [m]\tdebug mode\n\t\tdisplay (every [m]) factorizations\n");
    fprintf(stderr, "\t-v [n]\tverbose mode\n\t\tdisplay (every [n]) found results\n");
}

int main(int argc, char** argv)
{
#if defined BOINC
	boinc_init();
#endif

#ifdef _WIN32
#elif __linux__ || unix || __unix__ || __unix
	char OS[256];
	struct utsname name;
	if(uname(&name)) exit(EXIT_FAILURE);
	sprintf(OS, "%s %s", name.sysname, name.release);
#endif // __linux__
    char * exec_name = basename(argv[0]);
    fprintf(stderr, "%s %s (%s)\nCopyright %s, %s\n\n", PROGRAM_NAME, VERSION, OS, YEARS, AUTHOR);
    if (argc < 3) {
        print_usage(exec_name);
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }

    task_ini = ini = string_to_u64(argv[1]);
    task_fin = fin = string_to_u64(argv[2]);
    if (!ini || !fin) {
        print_usage(exec_name);
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }

    for (int i = 3; i < argc; i++) {
        if (!strcmp(argv[i],"-a")) {almost = 1; continue;}
        if (!strcmp(argv[i],"-t")) {continue;}
        if (!strcmp(argv[i-1],"-t")) {
            for (int j = 0; argv[i][j]; j++) {
                if (argv[i][j] == 'P') {continue;}
                if (argv[i][j] == 'B') {body = 1; continue;}
                if (argv[i][j] == 'E') {edge = 1; continue;}
                if (argv[i][j] == 'F') {face = 1; continue;}
                if (argv[i][j] == 'C') {pcomplex = 1; continue;}
                if (argv[i][j] == 'I') {imaginary = 1; continue;}
                if (argv[i][j] == 'T') {twilight = 1; continue;}
                if (argv[i][j] == 'M') {midnight = 1; continue;}
                print_usage(exec_name);
#ifdef BOINC
                boinc_finish(EXIT_FAILURE);
#endif
                exit(EXIT_FAILURE);
            }
            continue;
        }
        if (!strcmp(argv[i],"-c")) {complex_num = 1; continue;}
        if (!strcmp(argv[i],"-f")) {derivative = 1; continue;}
        if (!strcmp(argv[i],"-q")) {quiet = 1; continue;}
        if (!strcmp(argv[i],"-p")) {progress = 1; continue;}
        if (!strcmp(argv[i],"-o")) {output = 1; continue;}
        if (!strcmp(argv[i],"-r")) {report = 1; continue;}
        if (!strcmp(argv[i],"-s")) {skip = 1; continue;}
        if (!strcmp(argv[i],"-b")) {continue;}
        if (string_to_u64(argv[i]) && !strcmp(argv[i-1],"-b")) {block_size = string_to_u64(argv[i]); continue;}
        if (!strcmp(argv[i],"-d")) {debug = 1; continue;}
        if (string_to_u64(argv[i]) && !strcmp(argv[i-1],"-d")) {debug_step = string_to_u64(argv[i]); continue;}
        if (!strcmp(argv[i],"-v")) {verbose = 1; continue;}
        if (string_to_u64(argv[i]) && !strcmp(argv[i-1],"-v")) {verbose_step = string_to_u64(argv[i]); continue;}
        print_usage(exec_name);
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }

    clockid_t clk = 0;
    clock_gettime(clk, &starttime);

    time_t timer;
    char curdatetime[26];
    struct tm* tm_info;
    time(&timer);
    tm_info = localtime(&timer);
    strftime(curdatetime, 26, "%d.%m.%Y %H:%M:%S", tm_info);

#ifndef BOINC
    sprintf(repfname, "rep_%019" PRIu64 "_%019" PRIu64, task_ini, task_fin);
    sprintf(outfname, "out_%019" PRIu64 "_%019" PRIu64, task_ini, task_fin);
    sprintf(chkfname, "chk_%019" PRIu64 "_%019" PRIu64, task_ini, task_fin);
#endif

    int ErrorCode, CheckPointCode;
    ErrorCode = CheckPointCode = read_checkpoint();
    if (ErrorCode) ErrorCode = init_task();
    if (ErrorCode) return ErrorCode;

    uint64_t total = fin >= ini ? fin - ini + 1 : 0;

    uint64_t state = 0, cubCnt = 0, block_elem = block_size - 1;

    fout = fopen(outfname, "r");
    if (skip && fout != NULL && CheckPointCode) {
        fclose(fout);
#ifdef BOINC
	boinc_finish(EXIT_SUCCESS);
#endif
        exit (EXIT_SUCCESS);
    }
    if (output) {
        if (!CheckPointCode && fout == NULL) {
#ifdef BOINC
            boinc_finish(EXIT_FAILURE);
#endif
            exit(EXIT_FAILURE);
        }
        if (CheckPointCode) {
            fout = fopen(outfname, "w");
        } else {
            fout = fopen(outfname, "a");
        }
        if (fout == NULL) {
#ifdef BOINC
            boinc_finish(EXIT_FAILURE);
#endif
            exit(EXIT_FAILURE);
        }
    }

    fprintf(stderr, "Command line      :");
    for (int i = 1; i < argc; i++)
        fprintf(stderr, " %s", argv[i]);
    fprintf(stderr, "\n");
    fprintf(stderr, "Range bounds      : %" PRIu64 " %" PRIu64 "\n", ini, fin);
    fprintf(stderr, "Amount of numbers : %" PRIu64 "\n", total);
    fprintf(stderr, "Block size        : %" PRIu32 "\n", block_size);
    fprintf(stderr, "Start time        : %s\n", curdatetime);
#ifdef BOINC
    fprintf(stderr, "\n");
#endif

    init_primes();

    if (progress)
        fprintf(stderr, "%*s(P,B,E,F%s%s)\n",PBWIDTH+8,"", complex_num ? ",C,I,T" : "", midnight ? ",M" : "");

    int cpcnt, ctpcnt = 0;
    float cstep = 0.01;
    int fpcnt, ftpcnt = 0;
    float fstep = 0.0001;

    if (progress)
        do_progress(ctpcnt);
#ifdef BOINC
    boinc_fraction_done(0);
#endif

	mpz_init_set_str(ZERO,"0", 10);
	mpz_init_set_str(ONE, "1", 10);
    mpz_inits(K, L, Triple.a, Triple.b, Triple.c, Triple.aa, Triple.bb, Triple.cc, Triple.gcd, NULL);

    while (ini <= cur && cur <= fin) {
        uint32_t bs = (fin - cur < block_elem ? fin - cur : block_elem) + 1;
        init_block(bs);
        factorize_range();
        init_triples();
        for (uint32_t i = 0; i < bSize; i++) {
            init_divisors(i);
            find_triples(i);
            sort_triples(Triples.array, 0, Triples.used-1);
            find_cuboids();
            if (debug && !progress) {
                print_factors(i);
                print_triples();
            }
            reset_triples();
            state = Block[i].number - ini + 1;
            cpcnt = (int)((double)state / total / cstep);
            if (ctpcnt != cpcnt || cubCnt < toCnt) {
                ctpcnt = cpcnt;
                cubCnt = toCnt;
                if (progress)
                    do_progress((double)state / total * 100);
                save_checkpoint(Block[i].number + 1);
                if (output) fflush(fout);
                fflush(stdout);
            }
        }
        fpcnt = (int)((double)state / total / fstep);
        if (ftpcnt != fpcnt) {
            ftpcnt = fpcnt;
#ifdef BOINC
            boinc_fraction_done((double)state / total);
#endif
        }
        cur += bSize;
        free_triples();
    };

    mpz_clears(ZERO, ONE, K, L, Triple.a, Triple.b, Triple.c, Triple.aa, Triple.bb, Triple.cc, Triple.gcd, NULL);
    free_block();
    free_primes();

    if (output) fclose(fout);
    remove(chkfname);

    clock_gettime(clk, &endtime);
    uint64_t dif = (endtime.tv_sec - starttime.tv_sec) * 1000 + (endtime.tv_nsec - starttime.tv_nsec)/1000000;

#ifndef BOINC
    fprintf(stderr, "\n");
#endif
    fprintf(stderr, "Elapsed time      : %02d:%02d:%02d.%03d\n", (unsigned char)(dif/60/60/1000), (unsigned char)((dif/60/1000)%60), (unsigned char)((dif/1000)%60), (unsigned char)(dif%1000));
    fprintf(stderr, "Perfect cuboids   : %" PRIu32 "\n", pcCnt);
    fprintf(stderr, "Body cuboids      : %" PRIu32 "\n", bcCnt);
    fprintf(stderr, "Edge cuboids      : %" PRIu32 "\n", ecCnt);
    fprintf(stderr, "Face cuboids      : %" PRIu32 "\n", fcCnt);
    if (complex_num) {
        fprintf(stderr, "Complex cuboids   : %" PRIu32 "\n", ccCnt);
        fprintf(stderr, "Imaginary cuboids : %" PRIu32 "\n", icCnt);
        fprintf(stderr, "Twilight cuboids  : %" PRIu32 "\n", tcCnt);
        if (midnight) {
            fprintf(stderr, "Midnight cuboids  : %" PRIu32 "\n", mcCnt);
        }
    }
    fprintf(stderr, "Total cuboids     : %" PRIu32 "\n", toCnt);
    if (report) {
        frep = fopen(repfname, "w");
        if(frep == NULL) {
            perror("Failed to open rep file");
#ifdef BOINC
			boinc_finish(EXIT_FAILURE);
#endif
            exit(EXIT_FAILURE);
        }
        fprintf(frep,  "%" PRIu64
                      ",%" PRIu64
#ifdef BOINC
                      ",%" PRIu64
#endif
#ifndef BOINC
                      ",%s,%s,%02d:%02d:%02d.%03d"
#endif
                      ",%" PRIu64
                      ",%" PRIu32
                      ",%" PRIu32
                      ",%" PRIu32
                      ",%" PRIu32
                      ",%" PRIu32
                      ",%" PRIu32
                      ",%" PRIu32
                      ",%" PRIu32
                      "\n"
                    ,task_ini
                    ,task_fin
#ifdef BOINC
                    ,check_sum
#endif
#ifndef BOINC
                    ,VERSION
                    ,OS
                    ,(unsigned char)(dif/60/60/1000), (unsigned char)((dif/60/1000)%60), (unsigned char)((dif/1000)%60), (unsigned char)(dif%1000)
#endif
                    ,total
                    ,pcCnt
                    ,bcCnt
                    ,ecCnt
                    ,fcCnt
                    ,ccCnt
                    ,icCnt
                    ,tcCnt
                    ,mcCnt
               );
        fclose(frep);
    }
#ifdef BOINC
    boinc_finish(EXIT_SUCCESS);
#endif
    return (EXIT_SUCCESS);
}
