#ifndef SAUCY_H
#define SAUCY_H

#include <stdio.h>

struct saucy_graph {
	int n;
	int e;
	int digraph;
	union {
		struct {
			int *adj;
			int *edg;
		} u;
		struct {
			int *ain;
			int *ein;
			int *aout;
			int *eout;
		} d;
	} u;
	int *lab;
	int *ptn;
};

struct saucy_stats {
	double grpsize_base;
	int grpsize_exp;
	int nodes;
	int bads;
	int gens;
};

int saucy_alloc(int size, int size_saved);
int saucy_init(
	const struct saucy_graph *g,
	struct saucy_stats *stats,
	int *canon,
	int max_saved);
int *saucy_search(void);
void saucy_free(void);

int saucy_read_amorph(FILE *f, struct saucy_graph *g, int digraph_mode);
int saucy_read_gap(FILE *f, struct saucy_graph *g);
void saucy_print_automorphism(int *gamma, int gap_mode);

#endif
