#include <stdio.h>
#include <stdlib.h>

#include "common.h"
#include "lookahead.h"
#include "transred.h"

#ifndef __APPLE__
  #include <malloc.h>
#endif

int* bin_db, *dsc, *fin, *rep;
int removed;
int *S;

int els_stamp_rec( int nrval, int stamp )
{
	int i;
	int *bImp, lit;
	int flag = 1;
	
	*S++ = nrval;
	dsc[ nrval ] = stamp++;

        bImp = BIMP_START(nrval);
	for( i = BIMP_ELEMENTS; --i; )
        {
	    lit = *bImp; // different than trd!
	    if( dsc[ lit ] == 0 )
		stamp = els_stamp_rec( lit, stamp );

	    if( fin[ lit ] == 0 && dsc[ lit ] < dsc[ nrval ] ) // lit is parent of nrval
	    {
		dsc[ nrval ] = dsc[ lit ];
		flag = 0;
	    }
		
	    bImp++;
	}


	if( flag )
	{
	    int size = 0;
	    stamp++;
	    do
	    {
		--S;
		lit = *S;
		size++;

		if( rep[ nrval ] == nrval && lit != nrval )
		{
		    rep[  lit ] =  nrval;
		    rep[ -lit ] = -nrval;
		}

		fin[ lit ] = stamp;
	    }
	    while( lit != nrval );
	
//	    if( size > 1 && rep[ nrval ] == nrval )
//	    printf("c size of SCC[ %i ] = %i\n", nrval, size );
	}

	return stamp;
}

int trd_stamp_rec( int nrval, int stamp )
{
	int i;
	int *bImp, lit;

	dsc[ nrval ] = stamp++;
/*
        bImp = BIMP_START(nrval);
	for( i = BIMP_ELEMENTS; --i; )
        {
	    int new = rand() % i;
	
	    if( new )
	    {
		lit = *bImp;
		*bImp = bImp[new];
		bImp[new] = lit;
	    }
	    bImp++;
	}
*/
        bImp = BIMP_START(nrval);
	for( i = BIMP_ELEMENTS; --i; )
        {
	    lit = bin_db[ *bImp ];
	    if( lit != 0 )
	    {
		if( dsc[lit ] > dsc[ nrval ] )
		{
		    bin_db[  *bImp    ] = 0;
		    bin_db[ (*bImp)^1 ] = 0;
		    removed++;
		}

		if( dsc[ lit ] == 0 )
		    stamp = trd_stamp_rec( lit, stamp );

		else if( fin[ lit ] != 0 )
		    dsc[ lit ] = stamp++ ;
	    }
	    bImp++;
	}

        bImp = BIMP_START(nrval);
	for( i = BIMP_ELEMENTS; --i; )
        {
	    lit = bin_db[ bImp[i-1] ];
	    if( lit != 0 )
	    {
		if( fin[lit ] > dsc[ nrval ] && dsc[lit] > fin[lit] )
		{
		    bin_db[  bImp[i-1]    ] = 0;
		    bin_db[ (bImp[i-1])^1 ] = 0;
		    removed++;
		}
	    }
	}

	fin[ nrval ] = stamp++;

	return stamp;
}




void trans_red()
{
	int i,j ;
	int lit, *bImp, *rts;
	int size = 0, nrofroots = 0;
	int stamp = 0;
	int root_dsc;
	int _removed = 0;

	removed = 0;

	for( i = -nrofvars; i <= nrofvars; i++ )
	{
	    size += BinaryImp[ i ][ 0 ] - 2;
	}

	bin_db = (int*) malloc( sizeof(int) * size );
	rts    = (int*) malloc( sizeof(int) * nrofvars );

//	printf("c bin size %i\n", size );

	size = 0;

        for( i = -nrofvars; i <= nrofvars; i++ )
        {
            bImp = BIMP_START( i);
            for( j = BIMP_ELEMENTS; --j; )
            {
                lit = *(bImp++);
                if( -i < lit ) continue;

		bin_db[ size++ ] = -i; 
		bin_db[ size++ ] = lit; 
            }

	    dsc[ i ] = 0;
	    fin[ i ] = 0;
	    BinaryImp[i][0] = 2;
        }

//	printf("c bin size %i\n", size );

	for( i = 0; i < size; i+=2 )
	{
	    int a = bin_db[ i   ];
	    int b = bin_db[ i+1 ];

	    BinaryImp[ -a ][ BinaryImp[ -a ][ 0 ]++ ] = i+1;
	    BinaryImp[ -b ][ BinaryImp[ -b ][ 0 ]++ ] = i;
	}

	start_trd:;

        for( i = -nrofvars; i <= nrofvars; i++ )
            if( (BinaryImp[ i ][0] > 2) && (BinaryImp[ -i ][0] == 2)  )
                rts[ nrofroots++ ] = i;

//	printf("c number of roots %i\n", nrofroots );

        while( nrofroots != 0 )
        {
            int idx = rand() % nrofroots;
            root_dsc = stamp + 1;
            stamp = trd_stamp_rec( rts[ idx ], stamp );
            rts[ idx ] = rts[ --nrofroots ];
        }

	if( removed > size/1000 )
	{
	    stamp = 0;

            for( i = -nrofvars; i <= nrofvars; i++ )
            {
	        dsc[ i ] = 0;
	        fin[ i ] = 0;
            }


	    _removed += removed;
	    removed = 0;
	    goto start_trd;
	}


        for( i = -nrofvars; i <= nrofvars; i++ )
	    BinaryImp[i][0] = 2;


	for( i = 0; i < size; i+=2 )
	{
	    int a = bin_db[ i   ];
	    int b = bin_db[ i+1 ];

	    if( a == 0 || b == 0 ) continue;

	    BinaryImp[ -a ][ BinaryImp[ -a ][ 0 ]++ ] = b;
	    BinaryImp[ -b ][ BinaryImp[ -b ][ 0 ]++ ] = a;
	}


	free( bin_db );
	free( rts );

	removed = _removed;

	printf("c removed %i of %i binaries\n", removed, size / 2 );
}

void els_red()
{
	int i, j;
	int stamp = 0;
	int lit, *bImp;
	int *fle, nroffailed = 0;

	fle = (int*) malloc ( sizeof(int) * 2 * nrofvars );

	S = (int*) malloc ( sizeof(int) * 2 * nrofvars );
	rep = (int*) malloc( sizeof(int) * (2*nrofvars+1) );
	rep += nrofvars;

	for( i = -nrofvars; i <= nrofvars; i++ )
	{
	    dsc[ i ] = 0; fin[ i ] = 0; rep[ i ] = i;
	
            if( IS_FORCED( i ) ) 
	    {
		dsc[ i ] = 1; 
		fin[ i ] = 1; 
	    }
	}

	dsc[ 0 ] = 1;

	for( i = -nrofvars; i <= nrofvars; i++ )
	   if( dsc[ i ] == 0 ) 
		stamp = els_stamp_rec( i, stamp );

        for( i = -nrofvars; i <= nrofvars; i++ )
        {
	    if( rep[ i ] == i )
	    {
                bImp = BIMP_START(i);
                for( j = BIMP_ELEMENTS; --j; )
                {
                  lit = *bImp;
		  if( rep[ lit ] == -i )
		  {
			printf("c found failed literal %i\n", i );
			fle[ nroffailed++ ] = -i;
		  }
		  else if( rep[ lit ] != i && rep[lit] != lit )
		  {
//		    printf("c lit %i equal to lit %i (%i)\n", lit, rep[ lit ], i );
		    *bImp = rep[ lit ];
		  }
		  bImp++;
                }
	    }
	    else
	    {
		int flag = 1;

//		printf("c moving implications from %i to %i\n", i, rep[ i ] );

                bImp = BIMP_START(i);
		CHECK_BIMP_UPPERBOUND( rep[ i ], BIMP_ELEMENTS +1 );
                for( j = BIMP_ELEMENTS; --j; )
                {
                  lit = *bImp++;
		  if( rep[ lit ] == -rep[ i ] )
		  {
		     printf("c found failed literal %i\n", rep[ i ] );
		     fle[ nroffailed++ ] = -rep[ i];
		  }		
		  else if( rep[ lit ] != rep[ i ] )
		  {  ADD_BINARY_IMPLICATION( -rep[ i ], rep[ lit ] ); 
//		     printf("c adding %i to %i\n", rep[ lit ], rep[ i ] );
	  	  }
		  else if( lit == rep[ i ] ) 
		    flag = 0;
                }

		BinaryImp[ i ][ 0 ] = 3;
		BinaryImp[ i ][ 2 ] = rep[ i ];
		if( flag )
		    ADD_BINARY_IMPLICATION( -rep[ i ], i );
	    }
        }

	for( i = 0; i < nroffailed; i++ )
	    look_fix_forced_literal( fle[i] );

	free(fle);

	rep -= nrofvars;
	free(rep);
	free(S);
}

void transitive_red ()
{ 
	dsc    = (int*) malloc( sizeof(int) * (2*nrofvars+1) );
	fin    = (int*) malloc( sizeof(int) * (2*nrofvars+1) );
	dsc += nrofvars;
	fin += nrofvars;

//	els_red();
	trans_red();

	dsc -= nrofvars;
	fin -= nrofvars;
	free(dsc);
	free(fin);
}
