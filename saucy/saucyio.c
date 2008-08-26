/*
 * saucyio.c
 * Input/output routines for saucy
 *
 * by Paul T. Darga <pdarga@umich.edu>
 * and Mark Liffiton <liffiton@umich.edu>
 *
 * Copyright (C) 2004, The Regents of the University of Michigan
 * See the LICENSE file for details.
 */

#include <stdlib.h>
#include <stdio.h>
#include "saucy.h"

static int
init_alloc(struct saucy_graph *g)
{
	/* Allocate the arrays */
	g->u.u.adj = (int *)calloc(g->n+1, sizeof(int));
	if (g->u.u.adj == NULL) goto a;
	g->u.u.edg = (int *)malloc(2 * g->e * sizeof(int));
	if (g->u.u.edg == NULL) goto b;
	g->lab = (int *)malloc((g->n+1) * sizeof(int));
	if (g->lab == NULL) goto c;
	g->ptn = (int *)malloc(g->n * sizeof(int));
	if (g->ptn == NULL) goto d;
	g->lab[g->n] = g->n;
	return 0;

	/* Error handling */
d:	free(g->lab);
c:	free(g->u.u.edg);
b:	free(g->u.u.adj);
a:	return -1;
}

static int
init_alloc_digraph(struct saucy_graph *g)
{
	/* Allocate the arrays */
	g->u.d.ain = (int *)calloc(g->n+1, sizeof(int));
	if (g->u.d.ain == NULL) goto a;
	g->u.d.ein = (int *)malloc(2 * g->e * sizeof(int));
	if (g->u.d.ein == NULL) goto b;
	g->u.d.aout = (int *)calloc(g->n+1, sizeof(int));
	if (g->u.d.aout == NULL) goto c;
	g->u.d.eout = (int *)malloc(2 * g->e * sizeof(int));
	if (g->u.d.eout == NULL) goto d;
	g->lab = (int *)malloc((g->n+1) * sizeof(int));
	if (g->lab == NULL) goto e;
	g->ptn = (int *)malloc(g->n * sizeof(int));
	if (g->ptn == NULL) goto f;
	g->lab[g->n] = g->n;
	return 0;

	/* Error handling */
f:	free(g->lab);
e:	free(g->u.d.eout);
d:	free(g->u.d.aout);
c:	free(g->u.d.ein);
b:	free(g->u.d.ain);
a:	return -1;
}

static int
do_free(struct saucy_graph *g)
{
	if (g->digraph) {
		free(g->u.u.adj);
		free(g->u.u.edg);
	}
	else {
		free(g->u.d.ain);
		free(g->u.d.ein);
		free(g->u.d.aout);
		free(g->u.d.eout);
	}
	free(g->lab);
	free(g->ptn);
	return -1;
}

static void
init_fixadj1(int n, int *adj)
{
	int val, sum, i;

	/* Translate adj values to real locations */
	val = adj[0]; sum = 0; adj[0] = 0;
	for (i = 1; i < n; ++i) {
		sum += val;
		val = adj[i];
		adj[i] = sum;
	}
}

static void
init_fixadj2(int n, int e, int *adj)
{
	int i;

	/* Translate again-broken sizes to adj values */
	for (i = n-1; i > 0; --i) {
		adj[i] = adj[i-1];
	}
	adj[0] = 0;
	adj[n] = e;
}

static int
saucy_read_amorph_digraph(FILE *f, struct saucy_graph *g)
{
	fpos_t fpos;
	int i, j, k, p;

	/* Read the sizes */
	if (fscanf(f, "%d %d %d", &g->n, &g->e, &p) != 3) return -1;
	if (init_alloc_digraph(g) == -1) return -1;

	/* Initialize the partition nest */
	for (i = 0; i < g->n; ++i) {
		g->lab[i] = i;
		g->ptn[i] = g->n+1;
	}
	g->ptn[g->n-1] = 0;

	/* Insert separators in partition nest */
	for (i = 1, j = 0; i < p; ++i, j = k) {
		if (fscanf(f, "%d", &k) != 1) return do_free(g);
		g->ptn[k-1] = 0;
	}

	/* Remember this spot in the file */
	if (fgetpos(f, &fpos) == -1) return do_free(g);

	/* Count the size of each adjacency list */
	for (i = 0; i < g->e; ++i) {
		if (fscanf(f, "%d %d", &j, &k) != 2) return do_free(g);
		++g->u.d.aout[j]; ++g->u.d.ain[k];
	}

	/* Fix that */
	init_fixadj1(g->n, g->u.d.aout);
	init_fixadj1(g->n, g->u.d.ain);

	/* Go back to the front of the edges */
	if (fsetpos(f, &fpos) == -1) return do_free(g);

	/* Insert adjacencies */
	for (i = 0; i < g->e; ++i) {
		if (fscanf(f, "%d %d", &j, &k) != 2) return do_free(g);
		g->u.d.eout[g->u.d.aout[j]++] = k; g->u.d.ein[g->u.d.ain[k]++] = j;
	}

	/* Fix that too */
	init_fixadj2(g->n, g->e, g->u.d.aout);
	init_fixadj2(g->n, g->e, g->u.d.ain);
	return 0;
}

int
saucy_read_amorph(FILE *f, struct saucy_graph *g, int digraph_mode)
{
	fpos_t fpos;
	int i, j, k, p;

	/* Handle digraph mode */
	g->digraph = digraph_mode;
	if (digraph_mode) return saucy_read_amorph_digraph(f, g);

	/* Read the sizes */
	if (fscanf(f, "%d %d %d", &g->n, &g->e, &p) != 3) return -1;
	if (init_alloc(g) == -1) return -1;

	/* Initialize the partition nest */
	for (i = 0; i < g->n; ++i) {
		g->lab[i] = i;
		g->ptn[i] = g->n+1;
	}
	g->ptn[g->n-1] = 0;

	/* Insert separators in partition nest */
	for (i = 1, j = 0; i < p; ++i, j = k) {
		if (fscanf(f, "%d", &k) != 1) return do_free(g);
		g->ptn[k-1] = 0;
	}

	/* Remember this spot in the file */
	if (fgetpos(f, &fpos) == -1) return do_free(g);

	/* Count the size of each adjacency list */
	for (i = 0; i < g->e; ++i) {
		if (fscanf(f, "%d %d", &j, &k) != 2) return do_free(g);
		++g->u.u.adj[j]; ++g->u.u.adj[k];
	}

	/* Fix that */
	init_fixadj1(g->n, g->u.u.adj);

	/* Go back to the front of the edges */
	if (fsetpos(f, &fpos) == -1) return do_free(g);

	/* Insert adjacencies */
	for (i = 0; i < g->e; ++i) {
		if (fscanf(f, "%d %d", &j, &k) != 2) return do_free(g);
		g->u.u.edg[g->u.u.adj[j]++] = k; g->u.u.edg[g->u.u.adj[k]++] = j;
	}

	/* Fix that too */
	init_fixadj2(g->n, 2 * g->e, g->u.u.adj);
	return 0;
}

int
saucy_read_gap(FILE *f, struct saucy_graph *g)
{
	fpos_t fpos;
	int i, j, k;
	char c;

	/* Skip leading chaff */
	do {
		while ((c = fgetc(f)) != '[' && c != EOF);
	} while ((c = fgetc(f)) != '[' && c != EOF);
	if (c == EOF) return -1;
	ungetc('[', f);

	/* Remember this spot in the file */
	if (fgetpos(f, &fpos) == -1) return -1;

	/* First pass: count the edges */
	g->e = 0; do {
		++g->e; if (fscanf(f, "[%d,%d]", &j, &k) != 2) return -1;
	} while ((c = fgetc(f)) == ',');
	if (c == EOF) return -1;

	/* Read the number of vertices */
	if (fscanf(f, ", %d)), [", &g->n) != 1) return -1;

	/* Do the allocation */
	if (init_alloc(g) == -1) return -1;

	/* Go back to the front of the edges */
	if (fsetpos(f, &fpos) == -1) return do_free(g);

	/* Second pass: count adjacencies for each vertex */
	do {
		if (fscanf(f, "[%d,%d]", &j, &k) != 2) return do_free(g);
		++g->u.u.adj[j-1]; ++g->u.u.adj[k-1];
	} while ((c = fgetc(f)) == ',');
	if (c == EOF) return do_free(g);

	/* Fix that */
	init_fixadj1(g->n, g->u.u.adj);

	/* Go back again */
	if (fsetpos(f, &fpos) == -1) return do_free(g);

	/* Third pass: actually insert the edges */
	do {
		if (fscanf(f, "[%d,%d]", &j, &k) != 2) return do_free(g);
		g->u.u.edg[g->u.u.adj[j-1]++] = k-1;
		g->u.u.edg[g->u.u.adj[k-1]++] = j-1;
	} while ((c = fgetc(f)) == ',');
	if (c == EOF) return do_free(g);

	/* Fix that too */
	init_fixadj2(g->n, 2 * g->e, g->u.u.adj);

	/* Read the number of vertices (again) */
	if (fscanf(f, ", %d)), [", &g->n) != 1) return do_free(g);

	/* We've read the edges; now read the coloring */
	i = -1; do {

		/* Eat a left bracket */
		if (fgetc(f) == EOF) return do_free(g);

		/* Try eating a right bracket; otherwise keep going */
		if ((c = fgetc(f)) == ']') continue;
		ungetc(c, f);

		/* Read in the entire color */
		do {
			if (fscanf(f, "%d", &j) != 1) return do_free(g);
			g->lab[++i] = j-1;
			g->ptn[i] = g->n+1;
		} while ((c = fgetc(f)) == ',');
		if (c == EOF) return do_free(g);

		/* Mark the end of the cell and add to alpha */
		g->ptn[i] = 0;
	} while ((c = fgetc(f)) == ',');
	if (c == EOF) return do_free(g);

	return 0;
}
