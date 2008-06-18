#include "parallel_symmetry_cell_ppu.h"

#include <libspe2.h>

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
	for(i=0; i<NUM_SPES; i++) {
		spu_event_wait();
	}

	pthread_mutex_lock(&(ppuWorkerContext.mutex));
	if(ppuWorkerContext.state != SLEEP) {
		pthread_cond_wait(&(ppuWorkerContext.cond), &(ppuWorkerContext.mutex));
	}
	pthread_mutex_unlock(&(ppuWorkerContext.mutex));
}

void wake_threads() {
	int i;

	for(i=0; i<NUM_SPES; i++) {
		write_mailbox(i, GO);
	}

	pthread_mutex_lock(&(ppuWorkerContext.mutex));
	ppuWorkerContext.state = WORKING;
	pthread_mutex_unlock(&(ppuWorkerContext.mutex));
	pthread_cond_signal(&(ppuWorkerContext.cond));
}

void stop_threads() {
	int i;

	for(i=0; i<NUM_SPES; i++) {
		write_mailbox(i, STOP);
	}

	pthread_mutex_lock(&(ppuWorkerContext.mutex));
	ppuWorkerContext.state = STOPPED;
	pthread_mutex_unlock(&(ppuWorkerContext.mutex));
	pthread_cond_signal(&(ppuWorkerContext.cond));

}


spe_event_unit_t spe_events[NUM_SPES];
spe_event_handler_ptr_t spe_handler;
pthread_t spe_threads[NUM_SPES];
spe_context_ptr_t spe_contexts[NUM_SPES];
thread_args_t spe_thread_args[NUM_SPES];

extern spe_program_handle_t spu_main;

void *spe_thread( void *voidarg ) {

  thread_args_t *arg = (thread_args_t *)voidarg;

  unsigned int runflags = 0;
  unsigned int entry = SPE_DEFAULT_ENTRY;

  spe_context_run( arg->spe_context, &entry, runflags, arg->argp, arg->envp, NULL );
  pthread_exit( NULL );

}

void start_threads() {
	int i;

	handler = spe_event_handler_create();

	for(i=0; i<NUM_SPES; i++) {

		spe_contexts[i] = spe_context_create( SPE_EVENTS_ENABLE, NULL );
		events[i].spe = spe_contexts[i];
		spe_events[i].events = SPE_EVENT_OUT_INTR_MBOX;
		spe_events[i].data.u32 = i;
		spe_event_handler_register(handler, &spe_events[i] );
		spe_program_load( spe_contexts[i], &spu_main );

		thread_args[i].spe_context = spe_contexts[i];
		thread_args[i].argp = buffer;
		thread_args[i].envp = buffer;

		pthread_create( &spe_threads[i], NULL, &spe_thread, &thread_args[i] );
	}

	ppuWorkerContext.id = i;
	ppuWorkerContext.state = SLEEP;
	ppuWorkerContext.mutex = PTHREAD_MUTEX_INITIALIZER;
	ppuWorkerContext.cond = PTHREAD_COND_INITIALIZER;
	pthread_create(&(ids[i]), NULL, thread_body, &(ppuWorkerContext.id));

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

void sleep(const int id) {
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
