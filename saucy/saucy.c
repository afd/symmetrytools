/*
 * saucy.c
 * Searching for Automorphisms in Underlying CNF, yes?
 *
 * by Paul T. Darga <pdarga@umich.edu>
 * and Mark Liffiton <liffiton@umich.edu>
 *
 * Copyright (C) 2004, The Regents of the University of Michigan
 * See the LICENSE file for details.
 */

#include <limits.h> /* CHAR_BIT */
#include <stdlib.h> /* malloc, calloc, free, exit, EXIT_* */
#include <string.h> /* memset */
#include <stdio.h>  /* FILE, fopen, fscanf, printf, fclose */

#include "saucy.h"

static int digraph;  /* The graph is directed */
static int *adj;      /* Adjacency list sizes and positions */
static int *edg;      /* Connection info */
static int *ain;      /* Adjacencies for in edges */
static int *ein;      /* Conn info for in edges */
static int *aout;      /* Adjacencies for out edges */
static int *eout;      /* Conn info for out edges */
static int front;      /* Position of refining cell */
static int *alpha;     /* Nonsingletons that might induce refinement */
static int *beta;      /* Singletons that might induce refinement */
static int nalpha;     /* Size of alpha stack */
static int nbeta;      /* Size of beta stack */
static char *abmark;   /* Those things that are marked */
static int *bucket;    /* Workspace */
static int *count;     /* Num vertices with same adj count to ref cell */
static char *stuff;      /* bit_contents replacement (faster) */
static char *cmark;      /* Is this cell marked for refining? */
static int *ccount;      /* Number of connections to refining cell */
static int *clist;       /* List of cells marked for refining */
static int csize;        /* Number of cells in clist */
static int n;              /* Number of objects searched over */
static int cells;          /* Number of cells in partition */
static int *lab;           /* Labelling of objects (half of coloring) */
static int *ptn;           /* Where/what level cells split (other half) */
static int *nextnon;       /* Forward next-nonsingleton pointers */ 
static int *prevnon;       /* Backward next-nonsingleton pointers */
static int *cfront;        /* Pointer to front of cells */
static int *clen;          /* Length of cells (defined for cfront's) */
static int lev;            /* Current search tree level */
static int flag;           /* Was the last leaf node an automorphism? */
static int target;         /* Front of cell about to be split */
static int target_min;     /* Location of minimum element in target cell */
static int *gamma;         /* Container for permutations at leaf nodes */
static int *bit_contents;  /* Workspace bit vector */
static int anc;         /* Level of greatest common ancestor with zeta */
static int have_zeta;   /* Have we hit the first leaf node yet? */
static int saved;       /* Number of auto's saved */
static int *start;      /* Location of target at each level */
static int *fixed;      /* Label fixed at each level */
static int *zeta;       /* The first leaf node */
static int *theta;      /* Running approximation of orbit partition */
static int *bit_fixed;  /* Bit vector version of fixed */
static int *fix;        /* Labels left fixed by each saved auto */
static int *mcr;        /* Min cell representatives of each saved auto */
static int max_saved;   /* Saved auto's for backtracking from bads */
static struct saucy_stats *stats; /* Statistics structure */
static int size;        /* Array size */
static int size_saved;  /* fix/mcr array size */
static int indmin;      /* Used for group size computation */
static int init;        /* Search state */
static int desc;        /* Search state */
static int *canon;      /* Canonical labeling */

/* Bit manipulation routines */
#define BITS            ((int)(sizeof(int)*CHAR_BIT))
#define BSIZE(n)        (((n-1)/BITS)+1)
#define BWIPE(b,n)      (memset(b,0,BSIZE(n)*sizeof(int)))
#define BISSET(b,i)     (b[(i)/BITS]&(1<<((i)%BITS)))
#define BSET(b,i)       (b[(i)/BITS]|=(1<<((i)%BITS)))
#define BCLEAR(b,i)     (b[(i)/BITS]&=~(1<<((i)%BITS)))
#define BERASE(b,i)     (b[(i)/BITS]=0)

/* Array-of-bit-vectors manipulation routines */
#define BARR(b,i,k)        ((b)+((i)*BSIZE(k)))
#define FIX(i)             BARR(fix, i, n)
#define MCR(i)             BARR(mcr, i, n)

static void
min_target(void)
{
	int i, size, min, color, next, target_size = n+1;

	/* Start with a bogus value */
	target = n+1;

	/* Search for the smallest non-trivial cell */
	for (i = nextnon[-1]; i < n; i = next) {

		/* Find our size and the next thing in line */
		next = nextnon[i];
		size = clen[i] + 1;

		/* Skip singletons (in the front, anyway) */
		if (size == 1) continue;

		/* Skip anything that isn't an improvement */
		if (size >= target_size) continue;

		/* Find the minimum value in this cell */
		color = min = i;
		do { if (lab[++i] < lab[min]) min = i; } while (ptn[i] > lev);

		/* Update target */
		target_size = size;
		target_min = min;
		target = color;

		/* Shortcut length 2 */
		if (target_size == 2) break;
	}
}

static void
data_mark(int *adj, int *edg, int x)
{
	int i, cf;

	/* Mark connections */
	for (i = adj[x]; i < adj[x+1]; ++i) {
		stuff[edg[i]] = 1;
		cf = cfront[edg[i]];

		/* Add nonsingleton cell fronts to the list */
		if (clen[cf] && !cmark[cf]) {
			cmark[cf] = 1;
			clist[csize++] = cf;
		}
	}
}

static void
data_unmark(int *adj, int *edg, int x)
{
	int i;

	/* Clear the cell contents */
	for (i = adj[x]; i < adj[x+1]; ++i) {
		stuff[edg[i]] = 0;
	}
}

static void
data_count(int *adj, int *edg, int x)
{
	int i, cf;

	/* Count connections */
	for (i = adj[x]; i < adj[x+1]; ++i) {

		/* Find the cell front */
		cf = cfront[edg[i]];

		/* Skip singletons */
		if (!clen[cf]) continue;

		/* Increment the count for this vertex */
		++ccount[edg[i]];

		/* Add this cell to the refine list */
		if (!cmark[cf]) {
			cmark[cf] = 1;
			clist[csize++] = cf;
		}
	}
}

static void
target_cell(void)
{
	min_target();
}

static void
check_mapping(int *adj, int *edg, int i)
{
	int j;

	/* Construct bit vector for this adjacency list */
	for (j = adj[i]; j < adj[i+1]; ++j) {
		BSET(bit_contents, gamma[edg[j]]);
	}

	/* Check mapping */
	for (j = adj[gamma[i]]; j < adj[gamma[i]+1]; ++j) {
		if (!BISSET(bit_contents, edg[j])) {flag = 0; break;}
	}

	/* Clear the bit vector */
	for (j = adj[i]; j < adj[i+1]; ++j) {
		BERASE(bit_contents, gamma[edg[j]]);
	}
}

static void
is_undirected_automorphism(void)
{
	int i;

	/* Iterate through the vertices */
	for (i = 0, flag = 1; flag && (i < n); ++i) {
		if (i == gamma[i]) continue;
		check_mapping(adj, edg, i);
	}
}

static void
is_directed_automorphism(void)
{
	int i;

	/* Iterate through the vertices */
	for (i = 0, flag = 1; flag && (i < n); ++i) {
		if (i == gamma[i]) continue;
		check_mapping(aout, eout, i);
		if (!flag) break;
		check_mapping(ain, ein, i);
	}
}

static void
is_automorphism(void)
{
	if (digraph) {
		is_directed_automorphism();
	}
	else {
		is_undirected_automorphism();
	}
}

void
saucy_print_automorphism(int *gamma, int gap_mode)
{
	int i, j;

	/* Print the automorphism */
	for (i = 0; i < n; ++i) {

		/* Mark elements we've already seen */
		if (BISSET(bit_contents, i)) continue;
		BSET(bit_contents, i);

		/* Skip fixed elements */
		if (gamma[i] == i) continue;
		printf("(%d", gap_mode ? i+1 : i);

		/* Mark and print elements in this orbit */
		for (j = gamma[i]; j != i; j = gamma[j]) {
			BSET(bit_contents, j);
			putchar(gap_mode ? ',' : ' ');
			printf("%d", gap_mode ? j+1 : j);
		}

		/* Finish off the orbit */
		printf(")");
	}

	/* Clean up after ourselves */
	if (!gap_mode) printf("\n");
	BWIPE(bit_contents, n);
}

#define add_induce(single, who) do { \
	if (single) { \
		beta[nbeta++] = who; \
	} \
	else { \
		alpha[nalpha++] = who; \
	} \
	abmark[who] = 1; \
} while (0);

static void
init_refine(void)
{
	int i, j;

	nalpha = nbeta = 0;
	csize = 0;

	/* Update refinement stuff based on initial partition */
	for (i = j = cells = 0; i < n; j = i, ++cells) {
		do { cfront[lab[i]] = j; } while (ptn[i++]);
		clen[j] = i - j - 1;
		add_induce(!clen[j], j);
	}

	/* nextnon[-1] is the first nonnegative cell, prevnon[n] is last */
	++nextnon;

	/* Prepare lists based on cell lengths */
	for (i = 0, j = -1; i < n; i += clen[i] + 1) {
		if (!clen[i]) continue;
		prevnon[i] = j;
		nextnon[j] = i;
		j = i;
	}

	/* Fix the end */
	prevnon[n] = j;
	nextnon[j] = n;
}

static void
sort_clist(void)
{
	int h, i, j, k;

	/* Shell sort, as implemented in nauty, (C) Brendan McKay */
	j = csize / 3;
	h = 1;
	do { h = 3 * h + 1; } while (h < j);

	do {
		for (i = h; i < csize; ++i) {
			k = clist[i];
			for (j = i; clist[j-h] > k; ) {
				clist[j] = clist[j-h];
				if ((j -= h) < h) break;
			}
			clist[j] = k;
		}
		h /= 3;
	} while (h > 0);
}

static void
do_ref_singleton(void)
{
	int cf, cb, ff, fb, tmp;

	/* Sort connected list */
	sort_clist();

	/* Now iterate over the marked cells */
	while (csize) {

		/* Get the cell boundaries */
		cf = clist[--csize];
		cb = cf + clen[cf];
		ff = cf; fb = cb;

		/* Cheat: set stuff[lab[cb+1]] so we can tighten this loop */
		stuff[lab[cb+1]] = 1;

		/* Move from opposite ends, sorting notconn->conn */
		while (ff <= fb) {
			if (!stuff[lab[ff]]) {
				++ff;
				while (!stuff[lab[ff]]) ++ff;
			}
			else {
				tmp = lab[ff];
				lab[ff] = lab[fb];
				lab[fb] = tmp;
				--fb;
			}
		}

		/* Uncheat */
		stuff[lab[cb+1]] = 0;

		/* Check if we split */
		if ((fb >= cf) && (ff <= cb)) {

			/* We did, so mark the new level */
			ptn[fb] = lev; ++cells;

			/* Add the new guy if we were already in alpha */
			if (abmark[cf] || fb-cf >= cb-ff) {
				add_induce(ff == cb, ff);
			}
			/* Otherwise, add the smaller */
			else {
				add_induce(fb == cf, cf);
			}

			/* Update cell lengths */
			clen[cf] = fb - cf;
			clen[ff] = cb - ff;
			
			/* Update cell front pointers */
			while (cb >= ff) cfront[lab[cb--]] = ff;

			/* Update nonsingleton list */
			if (clen[ff]) {
				nextnon[ff] = nextnon[cf];
				prevnon[nextnon[cf]] = ff;
				prevnon[ff] = cf;
				nextnon[cf] = ff;
			}
			if (!clen[cf]) {
				nextnon[prevnon[cf]] = nextnon[cf];
				prevnon[nextnon[cf]] = prevnon[cf];
			}
		}

		/* Clear the mark */
		cmark[cf] = 0;
	}
}

static void
do_ref_nonsingle(void)
{
	int cnt, i, cf, cb, ff, fb, max_size, max_pos, bmin, bmax;
	int max_site, lastnon, endnon;

	/* Sort connected list */
	sort_clist();

	/* Iterate through all the cells we're connected to */
	while (csize) {

		/* Find the front and back */
		ff = cf = clist[--csize];
		cb = cf + clen[cf];

		/* Clear the mark */
		cmark[cf] = 0;

		/* Remember some stuff about the nonsingleton list */
		lastnon = prevnon[cf];
		endnon = nextnon[cf];

		/* Prepare the buckets */
		cnt = ccount[lab[ff]];
		ccount[lab[ff]] = 0;
		count[ff] = bmin = bmax = cnt;
		bucket[cnt] = 1;

		/* Iterate through the rest of the vertices */
		while (++ff <= cb) {
			cnt = ccount[lab[ff]];
			ccount[lab[ff]] = 0;

			/* Initialize intermediate buckets */
			while (bmin > cnt) bucket[--bmin] = 0;
			while (bmax < cnt) bucket[++bmax] = 0;

			/* Mark this count */
			++bucket[cnt];
			count[ff] = cnt;
		}

		/* If they all had the same count, bail */
		if (bmin == bmax) continue;
		ff = fb = cf; max_size = max_pos = max_site = -1;

		/* Calculate bucket locations, sizes */
		for (i = bmin; i <= bmax; ++i, ff = fb) {

			/* Skip empty buckets */
			if (!bucket[i]) continue;
			fb = ff + bucket[i];
			bucket[i] = ff;

			/* Fix max-sized bucket */
			if (fb - ff > max_size) {
				max_size = fb - ff;
				max_pos = ff;
			}

			/* Add everybody except first */
			if (ff != cf) {
				if (fb - ff == 1) {
					if (ff == max_pos) max_site = nbeta;
					beta[nbeta++] = ff;
				}
				else {
					if (ff == max_pos) max_site = nalpha;
					alpha[nalpha++] = ff;
				}
				abmark[ff] = 1;
			}

			/* Create new cell for everybody but last */
			if (fb <= cb) {
				ptn[fb-1] = lev; ++cells;
			}

			/* Fix cell lengths */
			clen[ff] = fb - ff - 1;

			/* Update nonsingleton list */
			if (clen[ff]) {
				nextnon[lastnon] = ff;
				prevnon[ff] = lastnon;
				lastnon = ff;
			}
		}

		/* Finish the nonsingleton list */
		nextnon[lastnon] = endnon;
		prevnon[endnon] = lastnon;

		/* Repair the partition nest */
		for (i = cf; i <= cb; ++i) gamma[bucket[count[i]]++] = lab[i];
		for (i = cf; i <= cb; ++i) lab[i] = gamma[i];

		/* Clear the counts */
		for (i = cf; i <= cb; ++i) ccount[lab[i]] = 0;

		/* Fix cell beginnings */
		for (i = ff = cf + clen[cf] + 1; i <= cb; ++i) {
			cfront[lab[i]] = ff;
			if (ptn[i] <= lev) ff = i + 1;
		}

		/* If the front isn't marked and it isn't the largest... */
		if (!abmark[cf] && (cf != max_pos)) {

			/* Remove the max from its stack */
			if (ptn[max_pos] <= lev) {
				abmark[beta[max_site]] = 0;
				beta[max_site] = beta[--nbeta];
			}
			else {
				abmark[alpha[max_site]] = 0;
				alpha[max_site] = alpha[--nalpha];
			}

			/* Add the front to its stack */
			add_induce(ptn[cf] <= lev, cf);
		}
	}
}

static void
ref_singleton(int k)
{
	if (digraph) {
		data_mark(aout, eout, k);
		do_ref_singleton();
		data_unmark(aout, eout, k);
		data_mark(ain, ein, k);
		do_ref_singleton();
		data_unmark(ain, ein, k);
	}
	else {
		data_mark(adj, edg, k);
		do_ref_singleton();
		data_unmark(adj, edg, k);
	}
}

static void
ref_nonsingle(int front, int back)
{
	int i;
	if (digraph) {
		for (i = front; i <= back; ++i) data_count(aout, eout, lab[i]);
		do_ref_nonsingle();
		for (i = front; i <= back; ++i) data_count(ain, ein, lab[i]);
		do_ref_nonsingle();
	}
	else {
		for (i = front; i <= back; ++i) data_count(adj, edg, lab[i]);
		do_ref_nonsingle();
	}
}

static void
refine(void)
{
	/* Add target to beta */
	beta[nbeta++] = target;
	abmark[target] = 1;

	/* Keep going until refinement stops */
	while (1) {

		/* If discrete, clear alpha and bail */
		if (cells == n) {
			while (nalpha) { abmark[alpha[--nalpha]] = 0; }
			while (nbeta) { abmark[beta[--nbeta]] = 0; }
			break;
		}

		/* Look for something else to refine on */
		if (nbeta) {
			front = beta[--nbeta];
		}
		else if (nalpha) {
			front = alpha[--nalpha];
		}
		else break;
		abmark[front] = 0;

		/* Perform the appropriate refinement operation */
		if (ptn[front] <= lev) {
			ref_singleton(lab[front]);
		}
		else {
			ref_nonsingle(front, front + clen[front]);
		}
	}
}

#define MULTIPLY(s1,s2,i) if ((s1 *= i) >= 1e10) {s1 /= 1e10; s2 += 10;}

static void
descend_left(void)
{
	int temp;

	/* Remember that this cell is the target at this level */
	start[lev] = target;

	/* Update greatest common ancestor with zeta */
	if (!have_zeta) ++anc;

	/* Move the minimum label to the front */
	temp = lab[target_min];
	lab[target_min] = lab[target];
	lab[target] = temp;

	/* Remember that we fixed this element at this level */
	fixed[lev] = temp;
	BSET(bit_fixed, temp);

	/* Split the cell */
	ptn[target] = ++lev; ++cells;

	/* Update cell fronts */
	for (temp = target+1; temp <= target + clen[target]; ++temp) {
		cfront[lab[temp]] = target + 1;
	}

	/* If |target| = 2, then skip target completely */
	if (clen[target] == 1) {
		nextnon[prevnon[target]] = nextnon[target];
		prevnon[nextnon[target]] = prevnon[target];
	}
	/* Otherwise, fix pointers to deal with nonsingle after target */
	else {
		nextnon[target+1] = nextnon[target];
		prevnon[target+1] = prevnon[target];
		nextnon[prevnon[target]] = target+1;
		prevnon[nextnon[target]] = target+1;
	}

	/* Update cell lengths */
	clen[target+1] = clen[target] - 1;
	clen[target] = 0;

	/* Now go and do some work */
	refine();
}

static void
update_theta(void)
{
	int i, j, x, y, z;

	/* Update all cell representatives */
	for (i = 0; i < n; ++i) {

		/* Look for the start of an orbit */
		if (i >= gamma[i]) continue;

		/* Find the cell rep for the two elements */
		for (x = i; x != theta[x]; x = theta[x]);
		for (y = gamma[i]; y != theta[y]; y = theta[y]);

		/* Pick the cell with the smaller representative */
		z = (x < y) ? x : y;

		/* Update the old root's cell representatives */
		theta[x] = theta[y] = z;
	}

	/* Clear out last automorphism if we've already saved max */
	if (saved == max_saved) {
		--saved;
		BWIPE(FIX(saved), n);
		BWIPE(MCR(saved), n);
	}

	/* Look for orbits in gamma and update fix and mcr */
	for (i = 0; i < n; ++i) {

		/* Find the start of an orbit, and save it as an mcr */
		if (BISSET(bit_contents, i)) continue;
		BSET(bit_contents, i);
		BSET(MCR(saved), i);

		/* If the element is fixed, save as fixed and continue */
		if (gamma[i] == i) {
			BSET(FIX(saved), i);
			continue;
		}

		/* Find all other elements in the orbit */
		for (j = gamma[i]; j != i; j = gamma[j]) {
			BSET(bit_contents, j);
		}
	}

	/* Clean up */
	BWIPE(bit_contents, n);
	++saved;
}

static void
theta_prune(void)
{
	int i = start[lev], j, k, t;

	/* Find the start of the target cell at this level */
	target = i;
	target_min = n+1;

	/* Find the next-biggest minimum cell representative */
	do {
		++i;

		/* If we have a new candidate for minimum... */
		if ((lab[i] > fixed[lev]) && (lab[i] < target_min)) {

			/* Find and update the minimum cell rep for this element */
			for (j = lab[i]; j != theta[j]; j = theta[j]);
			k = lab[i]; while (theta[k] != j) {
				t = theta[k]; theta[k] = j; k = t;
			}

			/* Update if we are in fact a min cell rep */
			if (theta[lab[i]] == lab[i]) {
				target = i; target_min = lab[i];
			}
		}
	}
	/* Keep going until the end of the cell */
	while (ptn[i] > lev);
}

static void
orbit_prune(void)
{
	int i, j, good;

	/* Start with a completely set bit vector */
	for (j = 0; j < BSIZE(n); ++j) {
		bit_contents[j] = ~0;
	}

	/* Find the mcr's of permutations that fix this node */
	for (i = 0; i < saved; ++i) {

		/* Make sure we're a superset */
		for (j = 0, good = 1; good && j < BSIZE(n); ++j) {
			if (bit_fixed[j] & ~FIX(i)[j]) good = 0;
		}
		if (!good) continue;

		/* The automorphism fixes this node, so update mcr */
		for (j = 0; j < BSIZE(n); ++j) {
			bit_contents[j] &= MCR(i)[j];
		}
	}

	/* Point to the start of the target cell */
	target = i = start[lev];
	target_min = n+1;

	/* Do some orbit pruning */
	do {
		++i;

		/* If we have a new candidate for minimum... */
		if ((lab[i] > fixed[lev]) && (lab[i] < target_min)) {

			/* Make it minimum if it is an mcr */
			if (BISSET(bit_contents, lab[i])) {
				target = i; target_min = lab[i];
			}
		}
	/* Keep going until the end of the cell */
	} while (ptn[i] > lev);

	/* Clear the bit vector */
	BWIPE(bit_contents, n);
}

static void
backtrack(struct saucy_stats *stats)
{
	int i, j, k, t, indx, lastnon;

	/* Keep backtracking for a while */
	do {
		/* Back up from this spot to our ancestor with zeta */
		for (--lev; lev > 0; --lev) {
			BCLEAR(bit_fixed, fixed[lev]);
			if (flag && (lev > anc)) continue;
			break;
		}

		/* If we're at the top, quit */
		if (!lev) return;

		/* Update ancestor with zeta if we've rewound more */
		if (anc > lev) {
			anc = lev;
			indmin = fixed[lev];
		}

		/* Recover the partition nest to this level */
		for (i = j = cells = 0, lastnon = -1; i < n; j = ++i) {

			/* Rewind ptn */
			while (ptn[i] > lev) {
				ptn[i] = n+1;
				cfront[lab[i++]] = j;
			}

			/* We're at the end of a cell */
			++cells;
			if (i == j) continue;

			/* Update lengths and fronts */
			clen[j] = i-j;
			cfront[lab[i]] = j;

			/* Update the nonsingleton list */
			prevnon[j] = lastnon;
			nextnon[lastnon] = j;
			lastnon = j;
		}

		/* Fix the end of the nonsingleton list */
		prevnon[n] = lastnon;
		nextnon[lastnon] = n;

		/* If we're at our gca with zeta, orbit prune with theta */
		if (lev == anc) theta_prune(); else orbit_prune();

		/* Compute |Aut(G)| found so far */
		if ((target_min == n+1) && (anc == lev)) {
			indx = 0; i = start[lev] - 1;

			/* Find factor */
			do {
				/* Find lab[i]'s minimum cell representative */
				for (j = lab[++i]; j != theta[j]; j = theta[j]);
				k = lab[i]; while (theta[k] != j) {
					t = theta[k]; theta[k] = j; k = t;
				}

				/* If it is the fixed value, then increment */
				if (j == indmin) ++indx;
			} while (ptn[i] > lev);

			/* Update size */
			MULTIPLY(stats->grpsize_base, stats->grpsize_exp, indx);
		}
	}
	/* Quit when there's something left in the target */
	while (target_min == n+1);
}

static void
descend(void)
{
	int temp;

	/* Put the new minimum value into the singleton cell */
	lab[start[lev]] = lab[target];
	lab[target] = fixed[lev];
	target = start[lev];

	/* Mark the new element as fixed */
	fixed[lev] = lab[target];
	BSET(bit_fixed, fixed[lev]);

	/* Split the singleton cell again, and refine */
	ptn[target] = lev + 1; ++lev; ++cells;

	/* Update cell fronts */
	for (temp = target+1; temp <= target + clen[target]; ++temp) {
		cfront[lab[temp]] = target + 1;
	}

	/* Update the nonsingleton list */
	if (clen[target] == 1) {
		nextnon[prevnon[target]] = nextnon[target];
		prevnon[nextnon[target]] = prevnon[target];
	}
	else {
		nextnon[target+1] = nextnon[target];
		prevnon[target+1] = prevnon[target];
		nextnon[prevnon[target]] = target+1;
		prevnon[nextnon[target]] = target+1;
	}

	/* Update cell lengths */
	clen[target+1] = clen[target] - 1;
	clen[target] = 0;

	/* Descend once again */
	refine();
}

static void
init_search(void)
{
	int i;

	/* Initialize scalars */
	lev = anc = 1;
	have_zeta = flag = saved = 0;
	target = target_min = 0;

	/* The initial orbit partition is discrete */
	for (i = 0; i < n; ++i) {
		theta[i] = i;
	}
}

int *
saucy_search(void)
{
	int i;

	/* Do initialization steps if necessary */
	if (!init) {
		init = 1;

		/* Initialize stats */
		stats->grpsize_base = 1.0;
		stats->grpsize_exp = stats->nodes = stats->bads = stats->gens = 0;

		/* Preprocessing after initial coloring */
		refine();
	}

	/* Keep going while there are tree nodes to expand */
	while (lev) {
		if (desc) { desc = 0; descend(); }

		/* Find a target cell */
		++stats->nodes; target_cell();
		if (target != n+1) { descend_left(); continue; }

		/* We don't have a target, so we're discrete */
		if (!have_zeta) {
			have_zeta = 1;
			for (i = 0; i < n; ++i) zeta[lab[i]] = i;
			if (canon != NULL) memcpy(canon, lab, n * sizeof(int));
		}
		else {
			/* Prepare permutation and check */
			for (i = 0; i < n; ++i) gamma[i] = lab[zeta[i]];
			is_automorphism();

			/* Do some stuff if we actually got an automorphism */
			if (flag) {
				++stats->gens;
				update_theta();
			}
			/* Keep track of leaf nodes that are not automorphisms */
			else {
				++stats->bads;
			}
		}

		/* Since we're discrete, we need to backtrack */
		backtrack(stats); desc = 1;
		if (flag) return gamma;
	}

	/* Normalize group size */
	while (stats->grpsize_base >= 10.0) {
		stats->grpsize_base /= 10;
		++stats->grpsize_exp;
	}

	/* All done */
	return NULL;
}

static int
cleanup(int x)
{
	switch (x) {
	case 22: free(mcr);
	case 21: free(fix);
	case 20: free(bit_contents);
	case 19: free(bit_fixed);
	case 18: free(theta);
	case 17: free(gamma);
	case 16: free(zeta);
	case 15: free(fixed);
	case 14: free(start);
	case 13: free(prevnon);
	case 12: free(--nextnon);
	case 11: free(clist);
	case 10: free(cmark);
	case 9: free(ccount);
	case 8: free(count);
	case 7: free(bucket);
	case 6: free(stuff);
	case 5: free(clen);
	case 4: free(cfront);
	case 3: free(abmark);
	case 2: free(beta);
	case 1: free(alpha);
	}
	return -1;
}

int
saucy_alloc(int n, int max_saved)
{
#define M(i,f,k,t) if (!(f=(t*)malloc((k)*sizeof(t)))) return cleanup(i);
#define C(i,f,k,t) if (!(f=(t*)calloc((k),sizeof(t)))) return cleanup(i);
	M(0, alpha, n, int)
	M(1, beta, n, int)
	C(2, abmark, n, char)
	C(3, cfront, n, int)
	M(4, clen, n, int)
	C(5, stuff, n+1, char)
	M(6, bucket, n+2, int)
	M(7, count, n+1, int)
	C(8, ccount, n, int)
	C(9, cmark, n, char)
	M(10, clist, n, int)
	M(11, nextnon, n+1, int)
	M(12, prevnon, n+1, int)
	M(13, start, n, int)
	M(14, fixed, n, int)
	M(15, zeta, n, int)
	M(16, gamma, n, int)
	M(17, theta, n, int)
	C(18, bit_fixed, BSIZE(n), int)
	C(19, bit_contents, BSIZE(n), int)
	C(20, fix, max_saved * BSIZE(n), int)
	C(21, mcr, max_saved * BSIZE(n), int)
#undef C
#undef M
	size = n;
	size_saved = max_saved;
	return 0;
}

int
saucy_init(
	const struct saucy_graph *g,
	struct saucy_stats *stats_,
	int *canon_,
	int max_saved_)
{
	if (g->n > size || max_saved_ > size_saved) return -1;
	n = g->n;
	digraph = g->digraph;
	if (!g->digraph) {
		adj = g->u.u.adj;
		edg = g->u.u.edg;
	}
	else {
		ain = g->u.d.ain;
		ein = g->u.d.ein;
		aout = g->u.d.aout;
		eout = g->u.d.eout;
	}
	lab = g->lab;
	ptn = g->ptn;
	stats = stats_;
	canon = canon_;
	max_saved = max_saved_;
	init = desc = indmin = 0;
	init_refine();
	init_search();
	return 0;
}

void
saucy_free(void)
{
	cleanup(22);
	size = size_saved = 0;
}
