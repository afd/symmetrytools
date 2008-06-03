#ifdef TOPSPIN_VECTORS
#define STATE AugmentedState
#define MEMCPY augmented_memcpy
#define MEMCMP augmented_memcmp
#else
#define STATE State
#define MEMCPY memcpy
#define MEMCMP memcmp
#endif

typedef struct stabiliser_chain_s {
	char* key;
	int numberOfLevels;
	int* cosetsPerLevel;
	perm_t** cosets;
	int groupSize;
} stabiliser_chain_t;


#define CACHE_SIZE (NO_PROCS+NO_CHANS)*(NO_PROCS+NO_CHANS)

stabiliser_chain_t stabiliserTable[CACHE_SIZE];

int noStabilisers = 0;

int isKey(const char* s) {

	int i;

	for(i=0; i<noStabilisers; i++) {

		if(strcmp(s,stabiliserTable[i].key)==0) {

			return i;

		}

	}

	return -1;
}



stabiliser_chain_t getStabiliserChain(const STATE* s) {

	char *partitionString = constructPartition(
#ifdef TOPSPIN_VECTORS
		&(s->state)
#else
		s
#endif
		);

	int index = isKey(partitionString);

	if(index!=-1) {

		free(partitionString);

		return stabiliserTable[index];

	} else {

		printf("%s\n", partitionString);
		stabiliser_chain_t result;
		result.key = partitionString;
		char line[256];
		fgets(line,256,stdin);

		if(strncmp(line,"identity",8)==0) {

			result.numberOfLevels = 0;

		} else {

			sscanf( line, "%d", &(result.numberOfLevels) );

			result.cosetsPerLevel = (int*)malloc(result.numberOfLevels * sizeof(int));

			result.cosets = (perm_t**)malloc(result.numberOfLevels * sizeof(perm_t*));

			result.groupSize = 1;

			int i;
			for(i=0; i<result.numberOfLevels; i++) {

				fgets( line, 256, stdin );
				sscanf( line, "%d", &(result.cosetsPerLevel[i]) );

				result.groupSize *= result.cosetsPerLevel[i];

				result.cosets[i] = (perm_t*) malloc( result.cosetsPerLevel[i] * sizeof(perm_t) );
				result.cosets[i][0] = constructPerm( "" );

				int j;
				for( j = 1; j < result.cosetsPerLevel[i]; j++ ) {

					fgets(line,256,stdin);
					result.cosets[i][j] = constructPerm(line);

				}

			}

		}

		stabiliserTable[noStabilisers++] = result;

		return result;
	}

}

stabiliser_chain_t chain;

#define MAX_CHAIN_LENGTH 100


int getLevelToUpdate(int counters[MAX_CHAIN_LENGTH]) {

	int result;

	for(result = 0; result<chain.numberOfLevels; result++) {

		if(counters[result] < chain.cosetsPerLevel[result]-1) {

			counters[result]++;
			return result;

		} else {

			counters[result]=0;

		}
	}

	return -1;

}

#ifndef NUM_THREADS

int levelCounters[MAX_CHAIN_LENGTH];

inline void initialiseLevelCounters() {
	int i;
	for(i=0; i<chain.numberOfLevels; i++) {
		levelCounters[i] = 0;
	}
}

inline void minimise(STATE* s) {
	int i;

	initialiseLevelCounters();

	STATE partialImages[chain.numberOfLevels];

	for(i=0; i<chain.numberOfLevels; i++) {
		MEMCPY(&partialImages[i],s,vsize);
	}

	int count = 1;


	do {
		int levelToUpdate = getLevelToUpdate(levelCounters);

		for(i=levelToUpdate; i>=0; i--) {

			if(i==chain.numberOfLevels-1) {
				MEMCPY(&partialImages[i],s,vsize);
			} else {
				MEMCPY(&partialImages[i],&partialImages[i+1],vsize);
			}
			applyPermToState(&partialImages[i],&(chain.cosets[i][levelCounters[i]]));
		}

		count++;

		if(MEMCMP(&partialImages[0],s,vsize)<0) {
			MEMCPY(s,&partialImages[0],vsize);
		}
	} while(count < chain.groupSize);
}



void segment(STATE *s) {
	chain = getStabiliserChain(s);
	minimise(s);	
}

#else

void initialiseLevelCounters(int counters[MAX_CHAIN_LENGTH], const unsigned int start)
{
	int i;
	int divisor = 1;

	for(i=0; i<chain.numberOfLevels; i++) {
		counters[i] = (start/divisor)%chain.cosetsPerLevel[i];
		divisor *= chain.cosetsPerLevel[i];
	}
}


State state_before_segmentation;
State* result_state;

inline void* thread_body(void* arg) {
	int id, i;
	id = *(int*)arg;

	int levelCounters[MAX_CHAIN_LENGTH];


	while(working(id)) {

		int start, end, count;

		State partial_min;

		get_data_section(&start, &end, id, chain.groupSize);

		memcpy(&partial_min, &state_before_segmentation, vsize);

		initialiseLevelCounters(levelCounters, start);

		



		State partialImages[chain.numberOfLevels];

		memcpy(&partialImages[chain.numberOfLevels-1],&state_before_segmentation,vsize);
		applyPermToState(&partialImages[chain.numberOfLevels-1],&(chain.cosets[chain.numberOfLevels-1][levelCounters[chain.numberOfLevels-1]]));


		for(i=chain.numberOfLevels-2; i>=0; i--) {
			memcpy(&partialImages[i],&partialImages[i+1],vsize);
			applyPermToState(&partialImages[i],&(chain.cosets[i][levelCounters[i]]));
		}

		count = 1;

		if(memcmp(&partialImages[0],&partial_min,vsize)<0) {
			memcpy(&partial_min,&partialImages[0],vsize);
		}

		do {
			int levelToUpdate = getLevelToUpdate(levelCounters);

			for(i=levelToUpdate; i>=0; i--) {

				if(i==chain.numberOfLevels-1) {
					memcpy(&partialImages[i], &partial_min,vsize);
				} else {
					memcpy(&partialImages[i],&partialImages[i+1],vsize);
				}
				applyPermToState(&partialImages[i],&(chain.cosets[i][levelCounters[i]]));
			}

			count++;

			if(memcmp(&partialImages[0],&partial_min,vsize)<0) {
				memcpy(&partial_min,&partialImages[0],vsize);
			}


		} while(count<(end-start));

		pthread_mutex_lock(&min_mutex);
		if(memcmp(&partial_min, result_state, vsize)<0) {
			memcpy(result_state, &partial_min, vsize);
		}
		pthread_mutex_unlock(&min_mutex);
		sleep(id);

	}

	return 0;
}


void segment(State *s) {

	chain = getStabiliserChain(s);

	memcpy(&state_before_segmentation, s, vsize);

	result_state = s;

	wake_threads();

	wait_for_threads();

}

#endif

