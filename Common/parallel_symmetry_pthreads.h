#include <pthread.h>

void join_threads();
void start_threads();
void wait_for_threads();
void wake_threads();
void stop_threads();

int working(const int id);
void topspin_thread_sleep(const int id);

void get_data_section(int* start, int* end, const int id, const int data_size);

void* thread_body(void* arg);
