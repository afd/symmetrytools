/*
 * Model of cell-phone handoff strategy in a mobile network.
 * A translation from the pi-calculus description of this
 * model presented in:
 * Fredrik Orava and Joachim Parrow, 'An algebraic verification
 * of a mobile network,' Formal aspects of computing, 4:497-543 (1992).
 * For more information on this model, email: joachim@it.kth.se
 *
 * See also the simplified version of this model in mobile2
 *
 * The ltl property definition for this version is in mobile1.ltl
 *
 * to perform the verification with xspin, simply use the ltl property
 * manager, which will load the above .ltl file by default.
 * to perform the verificaion from a Unix command line, type:
 * 	$ spin -a -N mobile1.ltl mobile1
 * 	$ cc -o pan pan.c
 * 	$ pan -a
 */

mtype = { data, ho_cmd, ho_com, ho_acc, ho_fail, ch_rel, white, red, blue };

chan in  = [1] of { mtype };
chan out = [1] of { mtype };

byte a_id, p_id;	/* ids of processes refered to in the property */

proctype CC(chan fa, fp, l)	/* communication controller */
{	chan  m_old, m_new, x;
	mtype v;

	do
	:: in?v ->
		printf("MSC: DATA\n");
		fa!data; fa!v
	:: l?m_new ->
		fa!ho_cmd; fa!m_new;
		printf("MSC: HAND-OFF\n");
		if
		:: fp?ho_com ->
			printf("MSC: CH_REL\n");
			fa!ch_rel; fa?m_old;
			l!m_old;
			x = fa; fa = fp; fp = x
		:: fa?ho_fail ->
			printf("MSC: FAIL\n");
			l!m_new
		fi
	od
}

proctype HC(chan l, m)			/* handover controller */
{
	do
	:: l!m; l?m
	od
}

proctype MSC(chan fa, fp, m)		/* mobile switching center */
{	chan l  = [0] of { chan };

	atomic {
		run HC(l, m);
		run CC(fa, fp, l)
	}
}

proctype BS(chan f, m; bit how)		/* base station */
{	chan v;

	if
	:: how -> goto Active
	:: else -> goto Passive
	fi;

Active:
	printf("MSC: ACTIVE\n");
	do
	:: f?data -> f?v; m!data; m!v
	:: f?ho_cmd ->			/* handover command */
progress:	f?v; m!ho_cmd; m!v;
		if
		:: f?ch_rel ->
			f!m;
			goto Passive
		:: m?ho_fail ->
			printf("MSC: FAILURE\n");
			f!ho_fail
		fi
	od;

Passive:
	printf("MSC: PASSIVE\n");
	m?ho_acc -> f!ho_com;
	goto Active
}

proctype MS(chan m)			/* mobile station */
{	chan m_new;
	mtype v;

	do
	:: m?data -> m?v; out!v
	:: m?ho_cmd; m?m_new;
		if
		:: m_new!ho_acc; m = m_new
		:: m!ho_fail
		fi
	od
}

proctype P(chan fa, fp)
{	chan m  = [0] of { mtype };

	atomic {
		run MSC(fa, fp, m);
		p_id = run BS(fp, m, 0)	/* passive base station */
	}
}

proctype Q(chan fa)
{	chan m  = [0] of { mtype }; /* mixed use as mtype/chan */

	atomic {
		a_id = run BS(fa, m, 1);	/* active base station */
		run MS(m)
	}
}

active proctype System()
{	chan fa = [0] of { mtype }; /* mixed use as mtype/chan */
	chan fp = [0] of { mtype }; /* mixed use as mtype/chan */

	atomic {
		run P(fa, fp);
		run Q(fa)
	}
}

active proctype top()
{
	do
	:: in!red; in!white; in!blue
	od
}
active proctype bot()
{
	do	/* deadlock on loss or duplication */
	:: out?red; out?white; out?blue
	od
}
