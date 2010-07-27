#include "parallel_symmetry_pthreads.h"

#if (NUM_THREADS<=0)
#error Compile with option -DNUM_THREADS=X where X is a positive number
#define NUM_THREADS 1
#endif

#define SLEEP 0
#define WORKING 1
#define STOPPED 2

typedef int thread_state_t;

typedef struct context_s
{
	int id;
	thread_state_t state;
	pthread_mutex_t mutex;
	pthread_cond_t cond;
} context_t;

context_t contexts[NUM_THREADS];
pthread_t ids[NUM_THREADS];

void wait_for_threads() {
	int i;
	for(i=0; i<NUM_THREADS; i++) {
		pthread_mutex_lock(&(contexts[i].mutex));
		if(contexts[i].state != SLEEP) {
			pthread_cond_wait(&(contexts[i].cond), &(contexts[i].mutex));
		}
		pthread_mutex_unlock(&(contexts[i].mutex));
	}
}

void wake_threads() {
	int i;
	for(i=0; i<NUM_THREADS; i++) {
		pthread_mutex_lock(&(contexts[i].mutex));
		contexts[i].state = WORKING;
		pthread_mutex_unlock(&(contexts[i].mutex));
		pthread_cond_signal(&(contexts[i].cond));
	}
}

void stop_threads() {
	int i;
	for(i=0; i<NUM_THREADS; i++) {
		pthread_mutex_lock(&(contexts[i].mutex));
		contexts[i].state = STOPPED;
		pthread_mutex_unlock(&(contexts[i].mutex));
		pthread_cond_signal(&(contexts[i].cond));
	}
}

void start_threads() {
	int i;
	for(i=0; i<NUM_THREADS; i++) {
		contexts[i].id = i;
		contexts[i].state = SLEEP;
		contexts[i].mutex = (pthread_mutex_t)PTHREAD_MUTEX_INITIALIZER;
		contexts[i].cond = (pthread_cond_t)PTHREAD_COND_INITIALIZER;
		pthread_create(&(ids[i]), NULL, thread_body, &(contexts[i].id));
	}
}

void join_threads() {
	int i;
	for(i=0; i<NUM_THREADS; i++) {
		void* exit_status;
		pthread_join(ids[0], &exit_status);
	}
}

int working(const int id) {
	pthread_mutex_lock(&(contexts[id].mutex));
	if(!((contexts[id].state==WORKING)||(contexts[id].state==STOPPED)))
	{
		pthread_cond_wait(&(contexts[id].cond), &(contexts[id].mutex));
	}
	pthread_mutex_unlock(&(contexts[id].mutex));

	return(!(contexts[id].state == STOPPED));
}

void topspin_thread_sleep(const int id) {
	pthread_mutex_lock(&(contexts[id].mutex));
	contexts[id].state = SLEEP;
	pthread_mutex_unlock(&(contexts[id].mutex));
	pthread_cond_signal(&(contexts[id].cond));
}

void get_data_section(int* start, int* end, const int id, const int data_size)
{
	*start = id*(data_size/NUM_THREADS);
	*end = (id==(NUM_THREADS-1)) ? data_size : *start + (data_size/NUM_THREADS);
}
