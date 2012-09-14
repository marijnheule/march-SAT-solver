/*
   MARCH Satisfiability Solver
   Copyright (C) 2001-2005 M.J.H. Heule, J.E. van Zwieten, and M. Dufour.
   Copyright (C) 2005-2011 M.J.H. Heule.
   [marijn@heule.nl, jevanzwieten@gmail.com, mark.dufour@gmail.com]
*/

#include <stdlib.h>
#include <math.h>
#include <time.h>

#include "march.h"
#include "cube.h"
#include "common.h"
#include "equivalence.h"
#include "lookahead.h"
#include "parser.h"
#include "preselect.h"
#include "progressBar.h"
#include "resolvent.h"
//#include "rootlook.h"
#include "solver.h"
#include "memory.h"
//#include "translator.h"

void handleUNSAT()
{
	printf( "c main():: nodeCount: %i\n", nodeCount );
	printf( "c main():: time=%f\n", ((float)(clock()))/CLOCKS_PER_SEC );
#ifdef TRELOS
	outputUnsat ();
#endif
#ifndef CUBE
       	printf( "s UNSATISFIABLE\n" );
#else
	printUNSAT();
#endif
	disposeFormula();

	exit( EXIT_CODE_UNSAT);
}

int main( int argc, char** argv )
{
	int i, result, exitcode;

	/* let's not be too optimistic... :) */
	result   = UNKNOWN;
	exitcode = EXIT_CODE_UNKNOWN;

        if( argc < 2 )
        {
                printf( "input file missing, usage: ./march_cc < DIMACS-file.cnf >\n" );
                return EXIT_CODE_ERROR;
        }
#ifdef CUBE
	if( argc > 2 )
	{
		// -a cube file 	  default = /tmp/cubes
		//lec learnt clauses file default = /tmp/earnt
	}
#endif
#ifdef PARALLEL
	if( argc == 4 )
	{
	    para_depth = atoi( argv[2] );
	    para_bin   = atoi( argv[3] );
	}
	else
	{
	    para_depth = 0;
	    para_bin   = 0;
	}
	printf("c running in parallel using %i processors with currently number %i\n", 1 << para_depth, para_bin );
#endif

	/*
		Parsing...
	*/
	runParser( argv[ 1 ] );
	/*
		Preprocessing...
	*/

#ifdef PRINT_FORMULA
	compactCNF();
	printFormula( Cv );
	exit(0);
#endif

//        if( structual_hashing()     == UNSAT )  handleUNSAT();
	if( equivalence_reasoning() == UNSAT )	handleUNSAT();

        for( i = 0; i < nrofclauses; i++ )
            if( Clength[ i ] > 3 )
	    { kSAT_flag = 1; break; }

	if( kSAT_flag )	printf("c using k-SAT heuristics (size based diff)\n");
	else		printf("c using 3-SAT heuristics (occurence based diff)\n");
	//check_integrety();


#ifndef TERNARYLOOK
#ifdef RESOLVENTLOOK
	if( resolvent_look() == UNSAT ) handleUNSAT();
#endif
#endif
        if( kSAT_flag )         allocate_big_clauses_datastructures();

	depth                 = 0;   // naar solver.c ?
        nodeCount             = 0;
        lookAheadCount        = 0;
        unitResolveCount      = 0;
	necessary_assignments = 0;

//	dispose_preprocessor_eq();

	if( initSolver() )			//dit staat wel heel gek...
	{
#ifdef TIMEOUT
		printf( "c timeout = %i seconds\n", TIMEOUT );
#endif
#ifdef PROGRESS_BAR
		pb_init( 6 );
#endif
#ifdef DISTRIBUTION
		result = distribution_branching();
#else
#ifdef SUPER_LINEAR
		result = super_linear_branching();
#else
		result = march_solve_rec();
#endif
#endif

#ifdef PROGRESS_BAR
		pb_dispose();
#endif
	}
	else
	{
		printf( "c main():: conflict caused by unary equivalence clause found.\n" );
		result = UNSAT;
	}
#ifdef CUBE
//	if( result != UNKNOWN )
//	printDecisionTree();

        printf( "c nodes vs cubes = %i vs %i\n", nodeCount + 1, nr_cubes );
//	printf( "c ratio assigned : freevars = %i %i\n", assigned_th, part_free ); 
	printf( "c final cutoff: %.4f * %i\n", factor_th, part_free ); 
#endif
	printf( "c main():: dead ends in main: %i\n", mainDead );
	printf( "c main():: lookAheadCount: %i\n", lookAheadCount );
      	printf( "c main():: unitResolveCount: %i\n", unitResolveCount );
        printf( "c time = %.2f seconds\n", ((float)(clock()))/CLOCKS_PER_SEC );
	printf( "c main():: necessary_assignments: %i\n", necessary_assignments );
	printf( "c main():: bin_sat: %i, bin_unsat %i\n", bin_sat, bin_unsat );
#ifdef DOUBLELOOK
	printf( "c main():: doublelook: #: %d, succes #: %d\n", (int) doublelook_count, (int) (doublelook_count - doublelook_failed) );
	printf( "c main():: doublelook: overall %.3f of all possible doublelooks executed\n", 
		100.0 * dl_actual_counter / (double) dl_possibility_counter );
 	printf( "c main():: doublelook: succesrate: %.3f, average DL_trigger: %.3f\n", 100.0 - 
		(100.0 * doublelook_failed / doublelook_count), DL_trigger_sum / doublelook_count );
#endif
#ifdef COUNT_SAT 
	printf( "c main():: found %i solutions\n", count_sat );
	if( count_sat > 0 ) result = SAT;
#endif

	switch( result )
	{
	    case SAT:
		printf( "c main():: SOLUTION VERIFIED :-)\n" );
		printf( "s SATISFIABLE\n" );
#ifndef COUNT_SAT
		printSolution( nrofvars );
#endif
		exitcode = EXIT_CODE_SAT;
		break;

	    case UNSAT:
#ifndef CUBE
                printf( "s UNSATISFIABLE\n" );
	        exitcode = EXIT_CODE_UNSAT;
#else
		printDecisionTree();
#endif
		break;

	    default:
		printf( "s UNKNOWN\n" );
		exitcode = EXIT_CODE_UNKNOWN;
        }

	disposeSolver();

	disposeFormula();

        return exitcode;
}

void runParser( char* fname )
{
	FILE* in;

	if( ( in = fopen( fname, "r" ) ) == NULL )
	{
		printf( "c runParser():: input file could not be opened!\n" );
		exit( EXIT_CODE_ERROR );
	}

	if( !initFormula( in ) )
	{
		printf( "c runParser():: p-line not found in input, but required by DIMACS format!\n" );
		fclose( in );
		exit( EXIT_CODE_ERROR );
	}
	
	if( !parseCNF( in ) )
        {
                printf( "c runParser():: parse error in input!\n" );
		fclose( in );
                exit( EXIT_CODE_ERROR );
        }

	fclose( in );

	init_equivalence();

	if( simplify_formula() == UNSAT )
	{
		printf( "c runParser():: conflicting unary clauses, so instance is unsatisfiable!\n" );
        	printf( "s UNSATISFIABLE\n" );

#ifdef TRELOS
		outputUnsat();
#endif
		disposeFormula();
		exit( EXIT_CODE_UNSAT );
	}
}
