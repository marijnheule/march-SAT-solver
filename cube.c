/* 
   MARCH Satisfiability Solver
   Copyright (C) 2001-2005 M.J.H. Heule, J.E. van Zwieten, and M. Dufour.
   Copyright (C) 2005-2011 M.J.H. Heule.
   [marijn@heule.nl, jevanzwieten@gmail.com, mark.dufour@gmail.com]
*/

#include <stdio.h>
#include <stdlib.h>
#include "cube.h"
#include "common.h"

#ifndef __APPLE__
  #include "malloc.h"
#endif

FILE *cubes;
FILE *learnt;

int *trail;
int nrofDnodes;
int Dnodes_size;
struct Dnode *Dnodes;
int _nr_cubes;

int Dnode_left( int index )
{        return Dnodes[ index ].left; }

int Dnode_right( int index )
{        return Dnodes[ index ].right; }

void Dnode_setType( int index, int type )
{        Dnodes[ index ].type = type; }

void Dnode_setDecision( int index, int decision )
{        Dnodes[ index ].decision = decision; }

void Dnode_close( int index )
{
	if( (Dnodes[ Dnodes[ index ].left ].type == REFUTED_DNODE) && (Dnodes[ Dnodes[ index ].right ].type == REFUTED_DNODE) )
		Dnodes[ index ].type = REFUTED_DNODE;
	else
		Dnodes[ index ].type = INTERNAL_DNODE;
}

int Dnode_new()
{        
	nrofDnodes++;
//	Dnodes[ nrofDnodes ].index = nrofDnodes;
	Dnodes[ nrofDnodes ].type  = REFUTED_DNODE;

	return nrofDnodes; 
}

void Dnode_init( int index )
{
	Dnodes[ index ].index = index;
        Dnodes[ index ].left  = Dnode_new();
        Dnodes[ index ].right = Dnode_new();
//	Dnodes[ index ].decision  = 0;
	Dnodes[ index ].type  = INTERNAL_DNODE;

	if( nrofDnodes + 3 > Dnodes_size )
	{
	    int i;
	    Dnodes = (struct Dnode*) realloc( Dnodes, sizeof(struct Dnode) * Dnodes_size * 2 );
	    for( i = Dnodes_size; i < 2*Dnodes_size; i++ )
	    {
	        Dnodes[ i ].index = 0;
	        Dnodes[ i ].left = 0;
	        Dnodes[ i ].right = 0;
	        Dnodes[ i ].decision = 0;
	        Dnodes[ i ].type = 0;
	    }
	    Dnodes_size *= 2;
	}

//	printf("c Dnodes %i\n", nrofDnodes );
}

void init_assumptions()
{
	int i;

	nrofDnodes = 1;	

	Dnodes_size = 100;
	Dnodes = (struct Dnode*) malloc( sizeof(struct Dnode) * Dnodes_size );
	for( i = 0; i < Dnodes_size; i++ )
	{
	    Dnodes[ i ].index = 0;
	    Dnodes[ i ].left = 0;
	    Dnodes[ i ].right = 0;
	    Dnodes[ i ].decision = 0;
	    Dnodes[ i ].type = 0;
	}
}

void printDecisionNode( struct Dnode Dnode, int depth, int discrepancies, int target )
{
	int i;

	if( Dnode.type == CUBE_DNODE )
	{
	    if( (target == -1) || (discrepancies == target) )
	    {
		_nr_cubes++;
	    	fprintf(cubes, "a ");
	    	for( i = 0; i < depth; i++ )
		    fprintf(cubes, "%d ", trail[ i ] );
	    	fprintf(cubes, "0\n" );
	    }
	    return;
	} 

	if( Dnodes[ Dnode.left ].type == REFUTED_DNODE )
	{
	    if( (target == -1) || (discrepancies == target) )
	    {
//		printf("c Dnode %i is REFUTED\n", Dnode.left );
	        for( i = 0; i < depth; i++ )
		    fprintf(learnt, "%d ", -trail[ i ] );
	        fprintf(learnt, "%d 0\n", -Dnodes[ Dnode.left ].decision );
	    }
		printDecisionNode( Dnodes[ Dnode.right ], depth, discrepancies, target );
		return;
	}

	if( Dnodes[ Dnode.right ].type == REFUTED_DNODE )
	{
	    if( (target == -1) || (discrepancies == target) )
	    {
//		printf("c Dnode %i is REFUTED\n", Dnode.right );
	        for( i = 0; i < depth; i++ )
		    fprintf(learnt, "%d ", -trail[ i ] );
	        fprintf(learnt, "%d 0\n", -Dnodes[ Dnode.right ].decision );
	    }
		printDecisionNode( Dnodes[ Dnode.left ], depth, discrepancies, target );
		return;
	}

#ifndef FLIP_ASSUMPTIONS
	trail[ depth ] = Dnodes[ Dnode.left ].decision;
	printDecisionNode( Dnodes[ Dnode.left ], depth + 1, discrepancies+1, target );
#endif
	trail[ depth ] = Dnodes[ Dnode.right ].decision;
	printDecisionNode( Dnodes[ Dnode.right ], depth + 1, discrepancies, target );
#ifdef FLIP_ASSUMPTIONS
	trail[ depth ] = Dnodes[ Dnode.left ].decision;
	printDecisionNode( Dnodes[ Dnode.left ], depth + 1, discrepancies+1, target );
#endif

}

void printUNSAT( )
{
	cubes  = fopen ("/tmp/cubes", "w");
	learnt = fopen ("/tmp/learnt",  "w");

	fprintf(learnt, "0\n");
	fprintf(cubes, "a 0\n");

	fclose(cubes);
	fclose(learnt);
}

void printFULL( )
{
	cubes  = fopen ("/tmp/cubes", "w");
	learnt = fopen ("/tmp/learnt",  "w");

	fprintf(cubes, "a 0\n");

	fclose(cubes);
	fclose(learnt);
}

void printDecisionTree( )
{
#ifdef CUBE
	int i;
	int discrepancy_search = 0;

#ifdef DISCREPANCY_SEARCH
	discrepancy_search = 1;
#endif
	if( (nr_cubes < 2000) || (nr_cubes > 200000) ) discrepancy_search = 1;

	if( Dnodes[1].type == REFUTED_DNODE )
	    return printUNSAT();

//	if( conflicts == 0 )
//	    return printFULL();

	trail = (int*) malloc(sizeof(int) * nrofvars );

	for( i = 0; i < nrofvars; i++ ) trail[ i ] = 0;

	cubes  = fopen ("/tmp/cubes", "w");
	learnt = fopen ("/tmp/learnt",  "w");

	printf("c print learnt clauses and cubes\n");

	_nr_cubes = 0;

	if( discrepancy_search )
	{
	    int target = 0;

	    do
	    {
	        printDecisionNode( Dnodes[1], 0, 0, target++);
	    }
	    while( _nr_cubes != nr_cubes );

	}
	else printDecisionNode( Dnodes[1], 0, 0, -1);

	fclose(cubes);
	fclose(learnt);

	free(trail);
#endif
}
