#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <inttypes.h>
#include <string.h>
#include <time.h>
#include <sys/timeb.h>

#ifdef BOINC
    #include "boinc_api.h"
#endif

#ifdef __linux__
	#include <sys/utsname.h>
#endif

#define PROGRAM_NAME "Euler brick"
#define VERSION "1.00"
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
#else
    const char* OS = "Other";
#endif

int almost = 0;
// progress - display progress bar
int progress = 0;
// quiet - suppress output to stdout
int quiet = 0;
// output - write results to output file out_%
int output = 0;
// report - write task stat to report file rep_%
int report = 0;
// backward - search on backward direction
int backward = 0;
// skip - skip task if output file exists
int skip = 0;
// debug - debug mode
int debug = 0;
uint32_t debug_step = 1;
// verbose - verbose mode
int verbose = 0;
uint32_t verbose_step = 1;

// check sum
uint64_t check_sum = 0;
//uint64_t loopCnt = 0;

#define max(a,b) ((a) > (b) ? a : b)
#define min(a,b) ((a) < (b) ? a : b)
#define sign(x) (x > 0 ? 1 : (x == 0 ? 0 : -1))

#ifndef HAVE_BZERO
    #define bzero(ptr,n) \
    memset(ptr, 0, n)
#endif //HAVE_BZERO

#define xchgu64(a,b) \
do {uint64_t c = *a; *a = *b; *b = c;} while (0)

#define xchgu128(a,b) \
do {__uint128_t c = *a; *a = *b; *b = c;} while (0)

// 6542 простих, менших за 2^16 = 65536
#define SMALL_PRIMES_CNT 6542
uint32_t SmallPrimes[SMALL_PRIMES_CNT];

uint32_t * Primes = NULL;
uint32_t primes_size = 0;

const int step = 2;
const uint64_t minA = 3;
const uint64_t maxA = (uint64_t)UINT32_MAX * (uint64_t)UINT32_MAX;

struct timeb starttime, endtime;
FILE * fout, * frep, * fchk;

uint32_t block_size = 100000;
typedef struct {uint64_t number; uint8_t primes;} TBlock;
TBlock * Block = NULL;
uint32_t bSize = 0;

// 16294579238595022365 = 3*5*7*11*13*17*19*23*29*31*37*41*43*47
// the largest number of different odd divisors among the numbers less than 2^64, is 14
#define MAX_FACTORS_CNT 14

typedef struct {uint64_t prime; uint8_t power;} TFactor;
TFactor * Factors[MAX_FACTORS_CNT], Divisors[MAX_FACTORS_CNT];

typedef struct {__uint128_t a, b, c, gcd;} TTriple;
typedef struct {TTriple * array; uint32_t size, used;} TTriples;
TTriples Triples;

uint32_t
     pcCnt = 0 // perfect cuboids
    ,bcCnt = 0 // body cuboids
    ,ecCnt = 0 // edge cuboids
    ,fcCnt = 0 // face cuboids
    ,icCnt = 0 // imaginary cuboids
    ,toCnt = 0; // total amount found cuboids

uint64_t ini, fin, cur, task_ini, task_fin;
char repfname[256] = "rep", outfname[256] = "out", chkfname[256] = "chk";

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
    if (!b) return a;
    __uint128_t c;
    while (a)
    {
        c = a;
        a = b%a;
        b = c;
    }
    return b;
}

__uint128_t gcd3(__uint128_t a, __uint128_t b, __uint128_t c)
{
    return gcd(gcd(a, b), c);
}

#define MOD48MASK ((1ULL << 48) - 1)
#define MOD56MASK ((1ULL << 56) - 1)
static __inline__ uint64_t is_square(__uint128_t p)
{
    if ((int64_t)(0xC840C04048404040ULL << (p & 63))>=0) return 0;
    uint64_t m48 = (uint64_t)(p >> 96) + ((uint64_t)(p >> 48) & MOD48MASK) + ((uint64_t)p & MOD48MASK);
    m48 = (m48 & MOD48MASK) + (m48 >> 48);
    m48 = (m48 & MOD48MASK) + (m48 >> 48); //important repetition
    uint64_t res, res1;
    // mod 63 & 65, try to cue the compiler to get out-of-order instructions to use two ALUs
    res = (m48 * 0x4104104104105ULL) & MOD56MASK;
    res1 = (m48 * 0x3F03F03F03F04ULL) & MOD56MASK;
    res = (res << 6) - res;
    res1 += (res1 << 6);
    res >>= 56;
    res1 >>= 56;
    if ((int64_t)(0xC940A2480C124020ULL << res) >= 0) return 0;
    if ((int64_t)(0xC862806619805184ULL << res1) > 0) return 0;
    // mod 17
    res = (m48 * 0xF0F0F0F0F0F10ULL) & MOD56MASK;
    res += (res << 4);
    res >>= 56;
    if ((int64_t)(0xE8C5800000000000ULL << res) >= 0) return 0;
    check_sum++;
    uint64_t c = rintl(sqrtl(p));
    return (p == (__uint128_t)c*(__uint128_t)c) ? c : 0;
}

static __inline__ uint64_t is_sub_of_squares_square_too(__uint128_t a, __uint128_t b)
{
    if (a == b) return 0;
    if ((a + 1) & b & 1) return 0;
    if (a < b) xchgu128(&a, &b);
    return is_square(a - b);
}

static __inline__ uint64_t is_sum_of_squares_square_too(__uint128_t a, __uint128_t b)
{
    if (a & b & 1) return 0;
    return is_square(a + b);
}

static __inline__ uint64_t is_square_hypot(uint64_t a, uint64_t b)
{
    return is_sum_of_squares_square_too((__uint128_t)a*a, (__uint128_t)b*b);
}

static __inline__ uint64_t is_square_leg(uint64_t a, uint64_t b)
{
    return is_sub_of_squares_square_too((__uint128_t)a*a, (__uint128_t)b*b);
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
                k = d - ((n - d)/step) % d;
            else
                k = ((d - n)/step) % d;
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

void save_checkpoint(uint64_t pos)
{
    fchk = fopen(chkfname, "w");
    if(fchk == NULL) {
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }

    struct timeb curtime;
    ftime(&curtime);
    uint64_t dif = (curtime.time - starttime.time) * 1000 + (curtime.millitm - starttime.millitm);
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
                ,icCnt
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
                              , &icCnt
                              , &c);
    fclose(fchk);
    if (scanned != 13) {
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }
    if (!cur) return 1;
        else cur = ((cur / step) + 1) * step + 1;
    starttime.time -= dif / 1000;
    long int millisec = (dif % 1000);
    if (starttime.millitm < millisec) {
        starttime.millitm += 1000 - millisec;
        starttime.time--;
    } else starttime.millitm -= millisec;
    toCnt = pcCnt + bcCnt + ecCnt + fcCnt + icCnt;
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
    SmallPrimes[0] = 2;
    j = 1;
    for (i = 3; j < SMALL_PRIMES_CNT ; i += 2) {
        if (!(sieve[i >> 7]&((uint64_t)1 << ((i >> 1)&63))))
            SmallPrimes[j++] = i;
    }
    primes_size = 0;
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
    primes_size = 0;
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
        n += step;
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
    }
    Triples.array[Triples.used++] = Triple;
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
    TTriple Triple;
    Triple.a = (__uint128_t)Block[i].number;
    __uint128_t x, aa = Triple.a * Triple.a;
    uint8_t j;
    int found = 1;
    while (found) {
        // generate a new divisor
        x = calc_divisor(i);
        if (found && x < Triple.a) {
            Triple.b = (aa / x - x) / 2;
            Triple.c = (aa / x + x) / 2;
            Triple.gcd = gcd3(Triple.a, Triple.b, Triple.c);
            add_triple(Triple);
        }
        j = 0;
        found = 0;
        do {
            if (Divisors[j].power < Factors[j][i].power * 2)
                found = ++Divisors[j].power;
            else
                Divisors[j++].power = 0;
        } while (j < Block[i].primes && !found);
    };
}

void sort_triples(TTriple * s, int32_t l, int32_t h)
{
    int32_t i, j, k;
    TTriple t;
    do {
        i = l;
        j = h;
        k = (l+h) >> 1;
        do {
            while (s[i].b < s[k].b) i++;
            while (s[j].b > s[k].b) j--;
            if (i <= j) {
                t = s[i];
                s[i] = s[j];
                s[j] = t;
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

void print_perfect_cuboid(__uint128_t A, __uint128_t B, __uint128_t C, __uint128_t D, __uint128_t E, __uint128_t F, __uint128_t G)
{
    char as128[40], bs128[40], cs128[40], ds128[40], es128[40], fs128[40], gs128[40];
    u128_to_string(A, as128);
    u128_to_string(B, bs128);
    u128_to_string(C, cs128);
    u128_to_string(D, ds128);
    u128_to_string(E, es128);
    u128_to_string(F, fs128);
    u128_to_string(G, gs128);
    if (!quiet) fprintf(stderr, "P:%s,%s,%s,%s,%s,%s,%s\n", as128, bs128, cs128, ds128, es128, fs128, gs128);
    if (output) fprintf(fout, "P,%s,%s,%s,%s,%s,%s,%s\n", as128, bs128, cs128, ds128, es128, fs128, gs128);
}

void print_body_cuboid(__uint128_t A, __uint128_t B, __uint128_t C, __uint128_t D, __uint128_t E, __uint128_t F, __uint128_t G)
{
    char as128[40], bs128[40], cs128[40], ds128[40], es128[40], fs128[40], gs128[40];
    u128_to_string(A, as128);
    u128_to_string(B, bs128);
    u128_to_string(C, cs128);
    u128_to_string(D, ds128);
    u128_to_string(E, es128);
    u128_to_string(F, fs128);
    u128_to_string(A*A + F*F, gs128);
    if (!quiet) fprintf(stderr, "B:%s,%s,%s,%s,%s,%s,(%s)\n", as128, bs128, cs128, ds128, es128, fs128, gs128);
    if (output) fprintf(fout, "B,%s,%s,%s,%s,%s,%s,(%s)\n", as128, bs128, cs128, ds128, es128, fs128, gs128);
}

void print_eface_cuboid(__uint128_t A, __uint128_t B, __uint128_t C, __uint128_t D, __uint128_t E, __uint128_t F, __uint128_t G)
{
    char as128[40], bs128[40], cs128[40], ds128[40], es128[40], fs128[40], gs128[40];
    u128_to_string(A, as128);
    u128_to_string(B, bs128);
    u128_to_string(C, cs128);
    u128_to_string(D, ds128);
    u128_to_string(A*A + C*C, es128);
    u128_to_string(F, fs128);
    u128_to_string(G, gs128);
    if (!quiet) fprintf(stderr, "F:%s,%s,%s,%s,(%s),%s,%s\n", as128, bs128, cs128, ds128, es128, fs128, gs128);
    if (output) fprintf(fout, "F,%s,%s,%s,%s,(%s),%s,%s\n", as128, bs128, cs128, ds128, es128, fs128, gs128);
}

void print_fface_cuboid(__uint128_t A, __uint128_t B, __uint128_t C, __uint128_t D, __uint128_t E, __uint128_t F, __uint128_t G)
{
    char as128[40], bs128[40], cs128[40], ds128[40], es128[40], fs128[40], gs128[40];
    u128_to_string(A, as128);
    u128_to_string(B, bs128);
    u128_to_string(C, cs128);
    u128_to_string(D, ds128);
    u128_to_string(E, es128);
    u128_to_string(B*B + C*C, fs128);
    u128_to_string(G, gs128);
    if (!quiet) fprintf(stderr, "F:%s,%s,%s,%s,%s,(%s),%s\n", as128, bs128, cs128, ds128, es128, fs128, gs128);
    if (output) fprintf(fout, "F,%s,%s,%s,%s,%s,(%s),%s\n", as128, bs128, cs128, ds128, es128, fs128, gs128);
}

void print_edge_cuboid(__uint128_t A, __uint128_t B, __uint128_t C, __uint128_t D, __uint128_t E, __uint128_t F, __uint128_t G)
{
    char as128[40], bs128[40], cs128[40], ds128[40], es128[40], fs128[40], gs128[40];
    u128_to_string(A, as128);
    u128_to_string(B, bs128);
    u128_to_string(E*E - A*A, cs128);
    u128_to_string(D, ds128);
    u128_to_string(E, es128);
    u128_to_string(F, fs128);
    u128_to_string(G, gs128);
    if (!quiet) fprintf(stderr, "E:%s,%s,(%s),%s,%s,%s,%s\n", as128, bs128, cs128, ds128, es128, fs128, gs128);
    if (output) fprintf(fout, "E,%s,%s,(%s),%s,%s,%s,%s\n", as128, bs128, cs128, ds128, es128, fs128, gs128);
}

void print_imaginary_cuboid(__uint128_t A, __uint128_t B, __uint128_t C, __uint128_t D, __uint128_t E, __uint128_t F, __uint128_t G)
{
    char as128[40], bs128[40], cs128[40], ds128[40], es128[40], fs128[40], gs128[40];
    u128_to_string(A, as128);
    u128_to_string(B, bs128);
    u128_to_string(A*A - E*E, cs128);
    u128_to_string(D, ds128);
    u128_to_string(E, es128);
    u128_to_string(F, fs128);
    u128_to_string(G, gs128);
    if (!quiet) fprintf(stderr, "I:%s,%s,(-%s),%s,%s,%s,%s\n", as128, bs128, cs128, ds128, es128, fs128, gs128);
    if (output) fprintf(fout, "I,%s,%s,(-%s),%s,%s,%s,%s\n", as128, bs128, cs128, ds128, es128, fs128, gs128);
}

void find_cuboids(void)
{
    int32_t i, j;
    __uint128_t k, l;
    for (i = 1; i < Triples.used; i++)
        for (j = 0; j < i; j++) {
            if (gcd(Triples.array[i].gcd, Triples.array[j].gcd) == 1) {
                if (Triples.array[i].b < UINT64_MAX && Triples.array[j].b < UINT64_MAX) {
                    k = (__uint128_t)is_square_hypot(Triples.array[i].b, Triples.array[j].b);
                    if (k) {
                        if (Triples.array[i].c < UINT64_MAX) {
                            l = (__uint128_t)is_square_hypot(Triples.array[i].b, Triples.array[j].c);
                            if (l) {
                                // (c, d, ?) is a PT (perfect cuboid)
                                print_perfect_cuboid(Triples.array[i].a, Triples.array[j].b, Triples.array[i].b, Triples.array[j].c, Triples.array[i].c, k, l);
                                pcCnt++;
                                continue;
                            }
                        }
                        if (almost) {
                            // two pairs of triples (a, c, e) and (a, b, d) such that (b, c, ?) is a PT (body cuboid)
                            print_body_cuboid(Triples.array[i].a, Triples.array[j].b, Triples.array[i].b, Triples.array[j].c, Triples.array[i].c, k, (__uint128_t)0);
                            bcCnt++;
                            continue;
                        }
                    }
                }
                if (almost) {
                    if (Triples.array[j].c < UINT64_MAX && Triples.array[i].b < UINT64_MAX) {
                        k = (__uint128_t)is_square_hypot(Triples.array[j].c, Triples.array[i].b);
                        if (k) {
                            // two pairs of triples (a, c, e) and (a, b, d) such that (c, d, ?) is a PT (face cuboid)
                            print_fface_cuboid(Triples.array[i].a, Triples.array[j].b, Triples.array[i].b, Triples.array[j].c, Triples.array[i].c, (__uint128_t)0, k);
                            fcCnt++;
                            continue;
                        }
                    }
                    if (Triples.array[i].c < UINT64_MAX && Triples.array[j].c < UINT64_MAX) {
                        k = (__uint128_t)is_square_leg(Triples.array[i].c, Triples.array[j].c);
                        if (k) {
                            // two pairs of triples (a, f, g) and (a, b, d) such that (d, ?, g) is a PT (face cuboid)
                            print_eface_cuboid(Triples.array[i].a, Triples.array[j].b, k, Triples.array[j].c, (__uint128_t)0, Triples.array[i].b, Triples.array[i].c);
                            fcCnt++;
                            continue;
                        }
                    }
                    if (Triples.array[i].c < UINT64_MAX && Triples.array[j].b < UINT64_MAX) {
                        k = (__uint128_t)is_square_leg(Triples.array[i].c, Triples.array[j].b);
                        if (k) {
                            // two pairs of triples (a, f, g) and (a, b, d) such that (b, ?, g) is a PT (edge cuboid)
                            print_edge_cuboid(Triples.array[i].a, Triples.array[j].b, (__uint128_t)0, Triples.array[j].c, k, Triples.array[i].b, Triples.array[i].c);
                            ecCnt++;
                            continue;
                        }
                    }
                    if (Triples.array[i].b < UINT64_MAX && Triples.array[j].c < UINT64_MAX && Triples.array[i].b < Triples.array[j].c) {
                        k = (__uint128_t)is_square_leg(Triples.array[j].c, Triples.array[i].b);
                        if (k) {
                            // two pairs of triples (a, b, d) and (a, f, g) such that (b, ?, g) is a PT (imaginary cuboid)
                            print_imaginary_cuboid(Triples.array[i].a, Triples.array[i].b, (__uint128_t)0, Triples.array[i].c, k, Triples.array[j].b, Triples.array[j].c);
                            icCnt++;
                            continue;
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
    ini = (uint64_t)((ini + step - 2) / step) * step + 1;
    fin = (uint64_t)((fin - 1) / step) * step + 1;
    cur = ini;
    return 0;
}

static __inline__ int next_task(void)
{
    if (maxA - step >= cur) cur += step;
    else return 6;
    if (cur > fin) return 7;
    return 0;
}

#define PBSTR "========================================================================"
#define PBWIDTH 45
#define SCRWIDTH 80
void do_progress( double percentage )
{
    int val = (int) (percentage);
    int lpad = (int) (percentage  * (val==100?SCRWIDTH:PBWIDTH) / 100);
    int rpad = (val==100?SCRWIDTH:PBWIDTH) - lpad;
    //fill progress bar with spaces
    fprintf(stderr, "\r%3d%% [%.*s%*s]", val, lpad, PBSTR, rpad, "");
    if (val!=100)
        fprintf(stderr, " (%" PRIu32 ",%" PRIu32 ",%" PRIu32 ",%" PRIu32 ",%" PRIu32 ")", pcCnt, bcCnt, ecCnt, fcCnt, icCnt);
}

void print_factors(uint32_t i)
{
    uint64_t n = Block[i].number;
    char divisorsStr[256], pclose[2], popen[2];
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
    char as128[40], bs128[40], cs128[40];
    for (int j=0; j < Triples.used; j++) {
        u128_to_string(Triples.array[j].a, as128);
        u128_to_string(Triples.array[j].b, bs128);
        u128_to_string(Triples.array[j].c, cs128);
        fprintf(stderr, "(%s,%s,%s)\n", as128, bs128, cs128);
    }
}

void print_usage(void)
{
#ifdef _WIN32
	char pref[3] = "";
#elif __linux__ || unix || __unix__ || __unix
	char pref[3] = "./";
#endif // __linux__
    fprintf(stderr, "Usage: %spcuboid <low> <high> [switches]\n", pref);
    fprintf(stderr, "\t<low>\t\tlower border\n");
    fprintf(stderr, "\t<high>\t\thigher border\n");
    fprintf(stderr, "The following switches are accepted:\n");
    fprintf(stderr, "\t-a\t\tsearch for almost-perfect cuboids\n");
    fprintf(stderr, "\t-q\t\tsuppress output to stdout\n");
    fprintf(stderr, "\t-p\t\tdisplay progress bar\n");
    fprintf(stderr, "\t-o\t\twrite results to output file\n");
    fprintf(stderr, "\t-r\t\twrite task stat to report file\n");
    fprintf(stderr, "\t-s\t\tskip task if output file exists\n");
    fprintf(stderr, "\t-f [s]\t\tfactoring block size (default value: %" PRIu32 ")\n", block_size);
    fprintf(stderr, "\t-d [m]\t\tdebug mode\n\t\t\tdisplay (every [m]) factorizations\n");
    fprintf(stderr, "\t-v [n]\t\tverbose mode\n\t\t\tdisplay (every [n]) found results\n");
    fprintf(stderr, "\nCuboids:\n");
    fprintf(stderr, "\t(P)erfect - cuboid with integer 3 edges, 3 face and 1 body diagonals\n");
    fprintf(stderr, "\t(B)ody - integer cuboid with only 1 irrational body diagonal\n");
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
    fprintf(stderr, "%s %s (%s)\nCopyright %s, %s\n\n", PROGRAM_NAME, VERSION, OS, YEARS, AUTHOR);
    if (argc < 3) {
        print_usage();
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }

    task_ini = ini = string_to_u64(argv[1]);
    task_fin = fin = string_to_u64(argv[2]);
    if (!ini || !fin) {
        print_usage();
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }

    for (int i = 3; i < argc; i++) {
        if (!strcmp(argv[i],"-a")) {almost = 1; continue;}
        if (!strcmp(argv[i],"-q")) {quiet = 1; continue;}
        if (!strcmp(argv[i],"-p")) {progress = 1; continue;}
        if (!strcmp(argv[i],"-o")) {output = 1; continue;}
        if (!strcmp(argv[i],"-r")) {report = 1; continue;}
        if (!strcmp(argv[i],"-s")) {skip = 1; continue;}
        if (!strcmp(argv[i],"-f")) {continue;}
        if (string_to_u64(argv[i]) && !strcmp(argv[i-1],"-f")) {block_size = string_to_u64(argv[i]); continue;}
        if (!strcmp(argv[i],"-d")) {debug = 1; continue;}
        if (string_to_u64(argv[i]) && !strcmp(argv[i-1],"-d")) {debug_step = string_to_u64(argv[i]); continue;}
        if (!strcmp(argv[i],"-v")) {verbose = 1; continue;}
        if (string_to_u64(argv[i]) && !strcmp(argv[i-1],"-v")) {verbose_step = string_to_u64(argv[i]); continue;}
        print_usage();
#ifdef BOINC
        boinc_finish(EXIT_FAILURE);
#endif
        exit(EXIT_FAILURE);
    }

    ftime(&starttime);

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

    uint64_t total = fin >= ini ? (uint64_t)((fin - ini) / step) + 1 : 0;

    uint64_t state = 0, cubCnt = 0, block_elem = (block_size - 1) * step;

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
    fprintf(stderr, "Range bounds      : from %" PRIu64 " to %" PRIu64 " step %i\n", ini, fin, step);
    fprintf(stderr, "Odd Numbers       : %" PRIu64 "\n", total);
    fprintf(stderr, "Block Size        : %" PRIu32 "\n", block_size);
    fprintf(stderr, "Start time        : %s\n", curdatetime);
#ifdef BOINC
    fprintf(stderr, "\n");
#endif

    init_primes();

    if (progress) {
        fprintf(stderr, "%*s(P,B,E,F,I)\n",PBWIDTH+8,"");
    }

    int cpcnt, ctpcnt = 0;
    float cstep = 0.01;
    int fpcnt, ftpcnt = 0;
    float fstep = 0.0001;

    if (progress)
        do_progress(ctpcnt);
#ifdef BOINC
    boinc_fraction_done(0);
#endif

    while (ini <= cur && cur <= fin) {
        uint32_t bs = (fin - cur < block_elem ? fin - cur : block_elem) / step + 1;
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
            state = (Block[i].number - ini) / step + 1;
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
        cur += bSize * step;
        free_triples();
    };

    if (output) fclose(fout);
    remove(chkfname);

    ftime(&endtime);
    uint64_t dif = (endtime.time - starttime.time) * 1000 + (endtime.millitm - starttime.millitm);

#ifndef BOINC
    fprintf(stderr, "\n");
#endif
    fprintf(stderr, "Elapsed time      : %02d:%02d:%02d.%03d\n", (unsigned char)(dif/60/60/1000), (unsigned char)((dif/60/1000)%60), (unsigned char)((dif/1000)%60), (unsigned char)(dif%1000));
//    fprintf(stderr, "Loop cnt                : %" PRIu64 "\n", loopCnt);
//    fprintf(stderr, "Check sum               : %" PRIu64 "\n", check_sum);
    fprintf(stderr, "Perfect Cuboids   : %" PRIu32 "\n", pcCnt);
    fprintf(stderr, "Body Cuboids      : %" PRIu32 "\n", bcCnt);
    fprintf(stderr, "Edge Cuboids      : %" PRIu32 "\n", ecCnt);
    fprintf(stderr, "Face Cuboids      : %" PRIu32 "\n", fcCnt);
    fprintf(stderr, "Imaginary Cuboids : %" PRIu32 "\n", icCnt);
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
                    ,icCnt
               );
        fclose(frep);
    }
    free_block();
    free_primes();
#ifdef BOINC
    boinc_finish(EXIT_SUCCESS);
#endif
    return (EXIT_SUCCESS);
}
