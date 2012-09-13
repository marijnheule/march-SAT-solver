/* 
   MARCH Satisfiability Solver
   Copyright (C) 2001-2005 M.J.H. Heule, J.E. van Zwieten, and M. Dufour.
   Copyright (C) 2005-2011 M.J.H. Heule.
   [marijn@heule.nl, jevanzwieten@gmail.com, mark.dufour@gmail.com]
*/

void init_doublelook();
void reset_doublelook_pointers();

int doublelook( int nrval, int new_binaries );
inline int DL_fix_implications( const int nrval );
inline int DL_fix_binary_implications( const int nrval );

int DL_treelook( int nrval );
int DL_IFIUP( const int nrval );
int DL_fix_forced_literal( const int nrval );

inline int DL_fix_equivalences( const int nrval );
inline int DL_fix_3SAT_clauses( const int nrval );
inline int DL_fix_kSAT_clauses( const int nrval );

inline void DL_restore_big_clauses( int *local_stackp );

