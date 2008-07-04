#include <stdlib.h>

#include "state.h"

#include "group.h"
		
#define SEG(state,pid) (((uchar *)state)+proc_offset[pid])
#define QSEG(state,cid) (((uchar *)state)+q_offset[cid])
#define VAR(state,pid,var,type) ((type *)SEG(state,pid))->var
#define QVAR(state,cid,var,type) ((type *)QSEG(state,cid))->var

#define MAX_PROCS 256
#define MAX_QUEUES 256

int proc_offset[MAX_PROCS] __attribute__((aligned(16)));
int q_offset[MAX_QUEUES] __attribute__((aligned(16)));
int vsize;

typedef unsigned char uchar;

typedef struct SPU_context_s {
	State* source;
	State* dest;
	int start;
	int end;
} SPU_context_t;

SPU_context_t myContext __attribute__ ((aligned(16)));

State originalState __attribute__((aligned(16)));

State minimisedState __attribute__((aligned(16)));

#include "apply_permutation.h"

#include "symmetry_group.h"

#define STOP 0
#define READY 1

int main(unsigned long long speid,  unsigned long long argp, unsigned long long envp )
{
	int tag = 31, tag_mask = 1<<tag;

	mfc_get(&myContext, argp, sizeof(SPU_context_t), tag, 0, 0);	
	mfc_write_tag_mask(tag_mask);
	mfc_read_tag_status_any();

	initialiseGroup();

	for(;;)
	{

		int message = spu_read_in_mbox();

		if(STOP == message)
		{
			break;
		}

		mfc_get(&originalState, myContext.source, sizeof(State), tag, 0, 0);
		mfc_write_tag_mask(tag_mask);
		mfc_read_tag_status_any();

        minimiseState();

		mfc_put(myContext.dest, &minimisedState, sizeof(State), tag, 0, 0);
		mfc_write_tag_mask(tag_mask);
		mfc_read_tag_status_any();

		spu_write_out_intr_mbox(READY);

	}

}
