/*
 * main.c
 * Program entry and option parsing
 *
 * by Paul T. Darga <pdarga@umich.edu>
 * and Mark Liffiton <liffiton@umich.edu>
 *
 * Copyright (C) 2004, The Regents of the University of Michigan
 * See the LICENSE file for details.
 */

#define _XOPEN_SOURCE 600
#include <unistd.h>
#include <stdlib.h>
#include <signal.h>
#include <time.h>
#include "saucy.h"

#define CPUTIME (((double)clock())/((double)CLOCKS_PER_SEC))

static char *prog_name;  /* Name we were invoked under */
static FILE *f;     /* File we're reading input from */
static int timeout = 0;      /* Seconds before quitting after refinement */
static int timeout_flag = 0; /* Has the alarm gone off yet? */
static int stats_mode;  /* Print out stats when we're done */
static int quiet_mode;  /* Don't output automorphisms */
static int gap_mode;    /* Do GAP I/O (interface with Shatter) */
static int max_saved = 60;   /* Saved auto's for backtracking from bads */
static int digraph_mode = 0; /* Input graph is directed */
static int canon_mode;  /* Get canonical labeling */

/*
 * pusage()
 * Print a usage statement to standard error and exit with error.
 * This function does not return.
 */

static void
pusage(void)
{
	fprintf(stderr, "usage: %s [-sqzg] [-t secs] [-p count]"
			" FILE\n", prog_name);
	exit(EXIT_FAILURE);
}

/*
 * opt_int(min)
 * Return the integer value sitting in optarg if it is greater than or
 * equal to min; otherwise, exit with an error status.
 */

static int
opt_int(int min)
{
	int val = atoi(optarg);
	if (val < min) {
		fprintf(stderr, "%s: invalid numeric argument\n", prog_name);
		pusage();
	}
	return val;
}

/*
 * parse_options(argc, argv)
 * Set option flags for the other modules
 */

static void
parse_options(int argc, char **argv)
{
	int c;

	/* Remember our name */
	prog_name = argv[0];

	/* Do some command line processing */
	while (1) {

		/* Get the next option */
		c = getopt(argc, argv, "csqgdt:p:");
		if (c == -1) break;

		/* Handle the option */
		switch (c) {
		case 'c': canon_mode = 1; break;
		case 's': stats_mode = 1; break;
		case 'q': quiet_mode = 1; break;
		case 'g': gap_mode = 1; break;
		case 'd': digraph_mode = 1; break;
		case 't': timeout = opt_int(1); break;
		case 'p': max_saved = opt_int(1); break;
		default:
			pusage();
		}
	}

	/* Gap and digraph are mutually exclusive */
	if (gap_mode && digraph_mode) {
		fprintf(stderr, "%s: gap and digraph mutually exclusive\n", prog_name);
		exit(EXIT_FAILURE);
	}

	/* There must be exactly one file */
	if (argc - optind != 1) {
		fprintf(stderr, "%s: must specify input file\n", prog_name);
		exit(EXIT_FAILURE);
	}

	/* Open the input file */
	if ((f = fopen(argv[optind], "r")) == NULL) {
		fprintf(stderr, "%s: unable to open file %s\n",
			prog_name, argv[optind]);
		exit(EXIT_FAILURE);
	}
}

static void
timeout_handler(int x)
{
	/* Do nothing but set a flag to be tested during the search */
	timeout_flag = 1;
}

/*
 * main(argc, argv)
 * Program entry, option parsing, and algorithm execution.
 */

int
main(int argc, char **argv)
{
	struct saucy_graph g;
	struct saucy_stats s;
	double cpu_time;
	int *perm, *canon, *pcanon, first = 1;

	/* Option handling */
	parse_options(argc, argv);
	
	/* Initialize graph structure */
	if (gap_mode) {
		if (saucy_read_gap(f, &g) == -1) {
			fprintf(stderr, "%s: error reading gap input\n", prog_name);
			return EXIT_FAILURE;
		}
		if (!quiet_mode) putchar('[');
	}
	else {
		if (saucy_read_amorph(f, &g, digraph_mode) == -1) {
			fprintf(stderr, "%s: error reading graph input\n", prog_name);
			return EXIT_FAILURE;
		}
	}
	fclose(f);

	/* Other initialization */
	if (canon_mode) {
		canon = (int *)malloc(g.n * sizeof(int));
		pcanon = (int *)malloc(g.n * sizeof(int));
		if (canon == NULL || pcanon == NULL) {
			fprintf(stderr, "%s: canon allocation error\n", prog_name);
			return EXIT_FAILURE;
		}
	}
	else {
		canon = pcanon = NULL;
	}
	if (saucy_alloc(g.n, max_saved) == -1) {
		fprintf(stderr, "%s: memory allocation failed\n", prog_name);
		return EXIT_FAILURE;
	}
	if (saucy_init(&g, &s, canon, max_saved) == -1) {
		fprintf(stderr, "%s: initialization failed\n", prog_name);
		return EXIT_FAILURE;
	}

	/* Set up the alarm for timeouts */
	if (timeout > 0) {
		signal(SIGALRM, timeout_handler);
		alarm(timeout);
	}

	/* Start timing */
	cpu_time = CPUTIME;

	/* Run the search */
	while (!timeout_flag && (perm = saucy_search()) != NULL) {
		if (quiet_mode) continue;
		if (gap_mode) { printf(first ? "\n" : ",\n"); first = 0; }
		saucy_print_automorphism(perm, gap_mode);
	}

	/* Warn if timeout */
	if (timeout_flag) fprintf(stderr, "%s: search timed out\n", prog_name);

	/* Finish timing */
	cpu_time = CPUTIME - cpu_time;

	/* Print out stats if requested */
	if (stats_mode) {
		fprintf(stderr, "%s: stats %fe%d %d %d %d %.2f\n",
			prog_name, s.grpsize_base, s.grpsize_exp,
			s.nodes, s.gens, s.bads, cpu_time);
	}

	/* Print last character in gap mode */
	if (gap_mode && !quiet_mode) printf("\n]\n");

	/* Print canonical labeling in canon mode */
	if (canon_mode) {
		if (s.bads > 0) {
			fprintf(stderr, "%s: can't do canonical labeling\n", prog_name);
		}
		else {
			int i;
			for (i = 0; i < g.n; ++i) pcanon[canon[i]] = i;
			for (i = 0; i < g.n; ++i) printf(" %d", pcanon[i]);
			putchar('\n');
		}
	}

	/* Cleanup */
	saucy_free();

	/* That's it, have a nice day */
	return EXIT_SUCCESS;
}
