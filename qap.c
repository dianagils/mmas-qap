/*****************************************************************************/
/*                                                                           */
/*      Version:  1.00   Date: 19/04/96   File: main-trial.c                 */
/* Last Version:                          File:                              */
/* Changes:                                                                  */
/* 19/04/96 Created                                                          */
/*                                                                           */
/* Purpose:                                                                  */
/*                                                                           */
/*                                                                           */
/* Author:  Thomas Stuetzle                                                  */
/*                                                                           */
/*****************************************************************************/
/*                                                                           */
/*===========================================================================*/

#include <stdio.h>
#include <math.h>
#include <limits.h>
#include <assert.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>
#include <getopt.h>

#include "timer.h"
#include "stat.h"

#define LINE_BUF_LEN  512
#define PROG_ID_STR "MAX-MIN Ant System for QAP, V0.99999\n"
#define CALL_SYNTAX_STR "mmasqap --help\n" 
#define VERBOSE(x)
#define VERYVERBOSE(x)
 
#define XOR(x,y) ((x && !y) || (!x && y))
#define MAX(x,y) ((x)>=(y)?(x):(y))

#define DEBUG( x ) x

#define FALSE 0
#define TRUE  1

/* --- variables for main program ---------------------------------------- */

/* constants for a pseudo-random number generator, details see Numerical Recipes in C book */

#define IA 16807
#define IM 2147483647
#define AM (1.0/IM)
#define IQ 127773
#define IR 2836

/* seed for the random number generator */

long int seed = -1; /* MAO: initialized to -1, meaning "uninitialized"... */

long int opt;

long int **d;             /* first matrix read from input file, typically distance matrix */
long int **f;             /* second matrix read from input file, typically flow matrix */

float **pheromone;        /* pheromone matrix for algorithm */

typedef struct {
  long int *s;     /* solution */
  long int *occupied;   /* auxiliary array for construction to keep track of occupied locations */
  long int value;
} ant_struct;

ant_struct *colony;


float tau_min;          /* minimum pheromone trail limit */
float tau_max;          /* maximum pheromone trail limit */ 

long int  n;              /* instance size of the QAP instance */
long int  best_known;     /* best objective function value of QAP instance */

long int null_diagonal_flag  = FALSE;  /* at least one matrix has zero diagonal: TRUE */
long int d_symmetric_flag    = FALSE;  /* if first (d) matrix is symmetric: TRUE */
long int f_symmetric_flag    = FALSE;  /* if second (f) matrix is symmetric: TRUE */
long int make_symmetric_flag = FALSE;  /* convert asymmetric instance into symmetric 
					  instance: TRUE
				       */

long int first_it_flag;         /* first iteration of local search: yes / no */

FILE    *output_file;           /* output file for developement of solution quality */
FILE    *output_summary_file;   /* output file for developement of solution quality */
char name_buf[LINE_BUF_LEN];    /* input file name */

long int   **move_values;       /* move values in best improvement local search */
long int   **tabu_values;       /* entries of matrix give iteration up to which an attribute is forbidden */

long int  *global_best;         /* global best solution in a trial */
long int  *restart_best;        /* best solution found since last pheromone initialization */

long int  *dlb;                 /* don't look bits, just one vector needed */
long int  dlb_flag;             /* set to one if don't look bits should be used */

long int  local_search_flag  = 0;  /* indicates which local search should be run
				      0: first improvement, don't look bits
				      1: first improvement, no don't look bits
				      2: best improvement 
                                      3: short tabu search runs of length 2n
				      4: short tabu search runs of length 6n
				   */

long int  global_best_value;    /* objective function value of global best solution */
long int  restart_best_value;   /* best solution since reinitialisation of pheromone trails */


long int  rchosen, schosen;     /* locations involved in move */
long int  tabu_search_length;   /* how many iterations the tabu search is run, is a multiple of the 
				   instance size */
long int  tabu_list_length;    
long int  iterations_before_aspiration;  /* robust tabu search specific, multiple of instance size */
long int  aspirating_iteration;
long int  max_trials;           /* max. number of repetitions of robust tabu search */
long int  trials;               /* Number trials */


double    rho;            /* parameter for pheromone trail evaporation */
long int  m;              /* number of ants in the colony */ 

long int  optimal;        /* Stop when hitting a solution with that or better value */

long int  iterations;     /* Number of iterations */
long int  max_iterations; /* Max. number of iterations */

long int  iteration_best_found;      /* iteration at which best solution is found */
long int  iterations_since_pheromone_reinit;  /* iterations passed since last reinitialization of pheromone trails */

long int  iteration_pheromone_reinit; /* iteration in which last time the pheromone was initialized */

long int  update_gb;      /* update with global-best solution every update_gb iterations */
long int  update_rb;      /* update with restart-best solution instead with gb up to update_rb 
			  iterations after a restart */

long int global_or_restart_update_flag; /* choose global (= 1) or restart best (= 0) for pheromone update */

long int  last_improvement;   /* last time an improved solution is found since restart */

long int  restart_iterations; /* restart from new initial solution after .. iterations */

double    time_limit;         /* time limit */
double    time_best_found = 0.0;     /* stores the time at which best solution is found 
					in each trial */

float     average_branching_factor;

long int  schedule_length = 20;  /* length during which the iteration
				    best / restart best schedule is
				    followed */ 


double ran01( long *idum ) {
/* 
      FUNCTION:      returns a pseudo-random number
      INPUT:         a pointer to the seed variable 
      OUTPUT:        a pseudo-random number uniformly distributed in [0,1]
      (SIDE)EFFECTS: changes the value of seed
*/
  long k;
  double ans;

  k =(*idum)/IQ;
  *idum = IA * (*idum - k * IQ) - IR * k;
  if (*idum < 0 ) *idum += IM;
  ans = AM * (*idum);
  return ans;
}



void read_problem_size( FILE *input ) {
/* 
      FUNCTION:      read the dimension of the QAP instance
      INPUT:         a pointer to the input file 
      OUTPUT:        none
      (SIDE)EFFECTS: assigns n the instance dimension (= number of locations / objects)
*/
  if( fscanf(input, "%ld", &n) <= 0) {
    fprintf(stderr, "error reading qap size value in data file\n");
    exit(1);	
  }
  VERYVERBOSE ( printf("QAP instance size %ld\n",n); )
}



void read_best_known_value( FILE *input ) {
/* 
      FUNCTION:      read the best known objective function value of the QAP instance
      INPUT:         a pointer to the input file 
      OUTPUT:        none
      (SIDE)EFFECTS: assigns best_known the read value
*/
  if( fscanf(input, "%ld ", &best_known) < 0 ) {
    fprintf(stderr, "error reading best known solution in data file\n");
    exit(1);	
  }
  VERYVERBOSE ( printf(" Best known solution %ld\n",best_known); )
}



long int ** read_matrix( FILE *input, long int size )
/*    
      FUNCTION:      read a QAP instance matrix from the input file
      INPUT:         Pointer to input file, size of QAP instance
      OUTPUT:        pointer to matrix, has to be freed before program stops
      (SIDE)EFFECTS: allocates a memory of appropriate size for the matrix
*/
{
  long int     i, j;
  long int     **matrix;

  if((matrix = malloc(sizeof(long int) * size * size +
		      sizeof(long int *) * size	 )) == NULL){
    fprintf(stderr,"Out of memory, exit.\n"); 
    exit(1);
  }
  for ( i = 0 ; i < size ; i++ ) {
    matrix[i] = (long int *)(matrix + size) + i*size;
    for ( j = 0  ; j < size ; j++ ) {
      if( fscanf(input, "%ld", &matrix[i][j]) < 0) {
	fprintf(stderr, "error reading (%ld, %ld) qap_distance in data file\n", i, j);
	exit(1);	
      }
    }
  }
  return matrix;
}



float ** generate_pheromone_matrix( long int size )
/*    
      FUNCTION:      generate pheromone matrix
      INPUT:         size of QAP instance
      OUTPUT:        pointer to matrix, has to be freed before program stops
      (SIDE)EFFECTS: allocates a memory of appropriate size for the pheromone matrix
*/
{
  long int     i, j;
  float        **matrix;

  if((matrix = malloc(sizeof(float) * size * size +
		      sizeof(float *) * size	 )) == NULL){
    fprintf(stderr,"Out of memory, exit.\n");
    exit(1);
  }
  for ( i = 0 ; i < size ; i++ ) {
    matrix[i] = (float *)(matrix + size) + i*size;
    for ( j = 0  ; j < size ; j++ ) {
      matrix[i][j] = 1.0; 
    }
  }
  return matrix;
}



long int check_null_diagonal ( long int **matrix, long int size ) {
/* 
      FUNCTION:      check whether the Matrix matrix has a zero diagonal
      INPUT:         pointer to the matrix
      OUTPUT:        TRUE if null diagonal, otherwise FALSE
*/
  long int   i;
  
  for ( i = 0 ; i < size ; i++ ) {
    if( matrix[i][i] != 0 ) {
      return FALSE;
    }
  }
  return TRUE;
}



long int check_symmetry ( long int **matrix, long int size ) {
/* 
      FUNCTION:      check whether the Matrix matrix is symmetric
      INPUT:         pointer to the matrix
      OUTPUT:        TRUE if symmetric, otherwise FALSE
*/
  long int   i, j;
  
  for ( i = 0 ; i < size - 1 ; i++ ) {
    for ( j = i + 1 ; j < size ; j++ ) {
      if( matrix[i][j] != matrix[j][i] )
	return FALSE;
    }
  }
  return TRUE;
}


       
void make_matrix_symmetric( long int **matrix, long int size ) {
/* 
      FUNCTION:      makes an asymmetric matrix symmetric (calculates M = M + M-transpose)
      INPUT:         pointer to the matrix
      OUTPUT:        none
      (SIDE)EFFECTS: makes the Matrix matrix symmetric 
      NOTES:         was described in the 1994 overview paper on QAP by Pardalos, Rendl, Wolkowicz 
*/
  long int  i, j;  /* index variables */
  long int  help;
  
  for ( i = 0 ; i < size ; i++ ) {
    for ( j = 0 ; j < i ; j++ ) {
      help = matrix[i][j] + matrix[j][i];
      matrix[i][j] = help;
      matrix[j][i] = help;
    }
  } 
}



void print_solution( long int *p ) {
/*    
      FUNCTION:      prints solution p
      INPUT:         pointer to the solution
      OUTPUT:        none
*/
    int i;

    printf("Assignment: \n");
    for ( i = 0 ; i < n ; i++ ) {
	printf(" %ld ",p[i]);
    }
    printf("\n");
}



void check_permutation( long int *p ) {
/*    
      FUNCTION:      does a very basic check whether p can be a permutation
      INPUT:         pointer to the permutation
      OUTPUT:        none
*/
    int i, j = 0;

    for ( i = 0 ; i < n ; i++ ) {
	j += p[i];
    }
    if ( j != (n * (n-1) / 2) ) {
	fprintf(stderr,"NOT A CORRECT PERMUTATION, ABORT:\n");
	print_solution(p);
	printf("sum = %d \n",j);
	exit(1);
    }
}



void print_integer_matrix ( long int **m ) {
/*    
      FUNCTION:      prints an integer matrix m
      INPUT:         pointer to the matrix 
      OUTPUT:        none
*/
  long int i, j;

  printf("\n");
  for ( i = 0 ; i < n ; i++ ) {
    for ( j = 0 ; j < n ; j++ ) {
      printf(" %ld ", m[i][j]);
    }
    printf("\n");
  }
}    



void print_matrix ( float **m ) {
/*    
      FUNCTION:      prints a float matrix m
      INPUT:         pointer to the matrix 
      OUTPUT:        none
*/
  long int i, j;

  printf("\n");
  for ( i = 0 ; i < n ; i++ ) {
    for ( j = 0 ; j < n ; j++ ) {
      printf(" %f ", m[i][j]);
    }
    printf("\n");
  }
}    



long int compute_evaluation_function( long int *p ) {
/*    
      FUNCTION:      computes the objective function value of a permutation
      INPUT:         pointer to a permutation
      OUTPUT:        none
      (SIDE)EFFECTS: none
      COMMENTS:      Division by 2 has to be done if we have an asymmetric instance that has 
                     been converted into a symmetric one (indicated by make_symmetric_flag). 
		     This is due to the particular way of doing this conversion.
*/
   long int  i, j;
   unsigned long  obj_f_value; /* unsigned, because with only "long int" we have an overflow
				  on some few instances, for example, tai100b. This is because 
				  of making this instance symmetric (see make_matrix_symmetric) 
			       */
   obj_f_value = 0;
   for ( i = 0 ; i < n ; i++ ) {
     for ( j = 0 ; j < n ; j++ ) {
       obj_f_value += d[i][j] * f[p[i]][p[j]];
     }
   }
   if ( make_symmetric_flag ) 
     obj_f_value /= 2;
   VERYVERBOSE ( printf("objective function value = %lu \n\n",obj_f_value); )
   return obj_f_value;
}



long int * generate_random_vector( long int size )
/*    
      FUNCTION:      generates a random vector, quick and dirty
      INPUT:         vector dimension
      OUTPUT:        returns pointer to vector, free memory when vector is not needed anymore 
      (SIDE)EFFECTS: none
*/
{
   long int  i, j, help;
   long int  *v;

   v = malloc( size * sizeof(long int) );

   for ( i = 0 ; i < size; i++ ) 
     v[i] = i;

   for ( i = 0 ; i < size-1 ; i++) {
     j = (long int) ( ran01( &seed ) * (size - i)); 
     assert( i + j < size );
     help = v[i];
     v[i] = v[i+j];
     v[i+j] = help;
   }
   VERYVERBOSE ( printf("Random vector:\n");
   for (i = 0 ; i < size ; i++ ) 
     printf(" %ld ",v[i]);
   printf("\n"); )

   return v;
}



void copy_from_to ( long int *v, long int *w )
/*    
      FUNCTION:      copies the content of a vector v to vector w
      INPUT:         the two vector v (from) and w (to)
      OUTPUT:        none
      (SIDE)EFFECTS: w has equal content as v; 
      NOTES:         it is assumed that the two vectors are of length n
*/
{
  int i;

  for ( i = 0 ; i < n ; i++ ) {
    w[i] = v[i];
  }
}



long int termination_condition( void )
/*    
      FUNCTION:      checks whether the termination condition is satisfied
      INPUT:         none
      OUTPUT:        TRUE if satisfied, FALSE otherwise
*/
{

  if ( !(iterations % 10) )
    printf("it %ld, maxit %ld, time %f tl %f, best %ld, opt %ld\n",iterations,max_iterations,elapsed_time( VIRTUAL ), time_limit, global_best_value, optimal);  

  return ( ((iterations >= max_iterations) && (elapsed_time( VIRTUAL ) > time_limit)) || 
	  (global_best_value <= optimal)); 

}

 

void swap( long int pos_1, long int pos_2, long int *q ) {   
/*    
      FUNCTION:      swap items at positions pos_1 and pos_2
      INPUT:         positions 1 and 2, pointer to a vector
      OUTPUT:        none
      (SIDE)EFFECTS: items at positions pos_1 and pos_2 are swapped (2-exchange move for QAP)
*/
  long int  help;
  
  help     = q[pos_1];
  q[pos_1] = q[pos_2];
  q[pos_2] = help;
}



void best_2_opt_asymmetric ( long int * q ) {
/*    
      FUNCTION:      best improvement 2-opt local search for asymmetric instances
      INPUT:         pointer to some initial assignment
      OUTPUT:        none
      (SIDE)EFFECTS: initial assignment is locally optimized
      COMMENTS:      fast evaluation of moves with additional matrix move_values
                     the first local search iteration is slow 
                     local search looks for best neighboring solution in each iteration
*/

  long int   improvement = TRUE;
  long int   u, v, k;
  long int   tmp;
  long int   **move_values;             /* matrix of move values in previous iteration
					   allows for fast evaluation of neighbourhood
					*/
  long int   first_it_flag = TRUE;      /* first iteration of local search: TRUE */
  long int   max_decrease;              /* largest decrease found so far in neighbourhood scan */
  long int   rchosen = n, schosen = n;  /* memorize which is best move in current iteration */
  long int   r, s;                      /* memorize which is best move in previous iteration */

  VERBOSE ( printf("best imp, asymmetric case\n"); )

  if((move_values = malloc(sizeof(long int) * n * n +
		      sizeof(long int *) * n )) == NULL){
    fprintf(stderr,"Out of memory, exit.\n");
    exit(1);
  }
  for ( k = 0 ; k < n ; k++ ) {
    move_values[k] = (long int *)(move_values + n) + k*n;
  }

  r = rchosen;
  s = schosen;

  while ( improvement ) {
    improvement = FALSE;
    max_decrease = LONG_MAX;
    /* in the first local search iteration the full neighborhood has to be evaluated */
    if (first_it_flag) {
      first_it_flag = FALSE;
      for ( u = 0 ; u < n-1 ; u++) {
	for ( v = u+1 ; v < n ; v++) {
	  tmp = 0;
	  for ( k = 0 ; k < n ; k++ ) {
	    if ( (k != u) && (k != v) ) {
	      tmp += d[k][u] * ( f[q[k]][q[v]] - f[q[k]][q[u]] ) + 
		d[k][v] * ( f[q[k]][q[u]] - f[q[k]][q[v]] ) + 
		d[u][k] * ( f[q[v]][q[k]] - f[q[u]][q[k]] ) + 
		d[v][k] * ( f[q[u]][q[k]] - f[q[v]][q[k]] );
	    }    
	  }
	  tmp += d[u][u] * ( f[q[v]][q[v]] - f[q[u]][q[u]] )+
	    d[u][v] * ( f[q[v]][q[u]] - f[q[u]][q[v]] )+
	    d[v][u] * ( f[q[u]][q[v]] - f[q[v]][q[u]] )+ 
	    d[v][v] * ( f[q[u]][q[u]] - f[q[v]][q[v]] );
	  move_values[u][v] = tmp;
	  if (tmp < max_decrease) {
	    max_decrease = tmp;
	    rchosen = u;
	    schosen = v;
	  }
	}
      }
    } else {
      for ( u = 0 ; u < n-1 ; u++) {
	for ( v = u+1 ; v < n ; v++) {
	  if (u == r || v == s || u == s || v == r) {
	    tmp = 0;
	    for ( k = 0 ; k < n ; k++ ) {
	      if ( (k != u) && (k != v) ) {
		tmp += d[k][u] * ( f[q[k]][q[v]] - f[q[k]][q[u]] ) + 
		  d[k][v] * ( f[q[k]][q[u]] - f[q[k]][q[v]] ) + 
		  d[u][k] * ( f[q[v]][q[k]] - f[q[u]][q[k]] ) + 
		  d[v][k] * ( f[q[u]][q[k]] - f[q[v]][q[k]] );
	      }    
	    }
	    tmp += d[u][u] * ( f[q[v]][q[v]] - f[q[u]][q[u]] )+
	      d[u][v] * ( f[q[v]][q[u]] - f[q[u]][q[v]] )+
	      d[v][u] * ( f[q[u]][q[v]] - f[q[v]][q[u]] )+ 
	      d[v][v] * ( f[q[u]][q[u]] - f[q[v]][q[v]] );
	    move_values[u][v] = tmp;
	    if (tmp < max_decrease) {
	      max_decrease = tmp;
	      rchosen = u;
	      schosen = v;
	      /*   	    printf(" max-decr = %ld\n",tmp); */
	    }
	  } else { /* change derived from move_values */
	    tmp = ( d[r][u] - d[r][v] + d[s][v] - d[s][u] ) *
	      ( f[q[s]][q[u]] - f[q[s]][q[v]] + f[q[r]][q[v]] - f[q[r]][q[u]] )
	      + ( d[u][r] - d[v][r] + d[v][s] - d[u][s] ) *
	      ( f[q[u]][q[s]] - f[q[v]][q[s]] + f[q[v]][q[r]] - f[q[u]][q[r]] );
 	    tmp += move_values[u][v];
	    move_values[u][v] = tmp;
	  }
	  if (tmp < max_decrease) {
	    max_decrease = tmp;
	    rchosen = u;
	    schosen = v;
	  }	   
	}
      }
    }
    if ( max_decrease < 0 ) {      /* Obj. function value can be improved */
      assert (rchosen < schosen);
      improvement = TRUE;
      swap(rchosen,schosen,q);    
      r = rchosen; /* memorize previously done move */
      s = schosen;/* memorize previously done move */
      VERYVERBOSE ( printf("improvement %ld, exchange %ld and %ld\n",max_decrease, rchosen, schosen); )
    }
  }
  free ( move_values );
}



void best_2_opt_symmetric ( long int * q ) {
/*    
      FUNCTION:      best improvement 2-opt local search for symmetric instances
      INPUT:         pointer to some initial assignment
      OUTPUT:        none
      (SIDE)EFFECTS: initial assignment is locally optimized
      COMMENTS:      faster evaluation of moves with additional matrix move_values
*/

  long int   improvement = TRUE;
  long int   u, v, k;
  long int   tmp;
  long int   original_symmetric_factor;
  long int   **move_values;
  long int   first_it_flag = TRUE;
  long int   max_decrease;
  long int   rchosen = n, schosen = n;
  long int   r, s;

  VERYVERBOSE ( printf("best imp, symmetric case\n"); )
  if ( make_symmetric_flag )
    original_symmetric_factor = 1;
  else
    original_symmetric_factor = 2;

  /* allocate and prepare matrix with move_values */
  if((move_values = malloc(sizeof(long int) * n * n +
		      sizeof(long int *) * n )) == NULL){
      printf("Out of memory, exit.");
    exit(1);
  }
  for ( k = 0 ; k < n ; k++ ) {
    move_values[k] = (long int *)(move_values + n) + k*n;
  }
  r = rchosen;
  s = schosen;

  while ( improvement ) {
    improvement = FALSE;
    max_decrease = LONG_MAX;
    /* in the first iteration the full neighborhood has to be evaluated */
    if (first_it_flag) {
      first_it_flag = FALSE;
      for ( u = 0 ; u < n-1 ; u++) {
	for ( v = u+1 ; v < n ; v++) {
	  tmp = 0;
	  for ( k = 0 ; k < n ; k++ ) {
	    if ( (k != u) && (k != v) ) {
	      tmp += ( d[k][u] - d[k][v] ) * ( f[q[k]][q[v]] - f[q[k]][q[u]] );
	    }    
	  }
	  tmp *= original_symmetric_factor;
	  move_values[u][v] = tmp;
	  if (tmp < max_decrease) {
	    max_decrease = tmp;
	    rchosen = u;
	    schosen = v;
/*    	    printf(" max-decr = %ld\n",tmp); */
	  }
	}
      }
    } else {
      for ( u = 0 ; u < n-1 ; u++) {
	for ( v = u+1 ; v < n ; v++) {
	  if (u == r || v == s || u == s || v == r) {
	    tmp = 0.;
	    for (k = 0 ; k < n ; k++) {
	      if ( (k != u) && (k != v) ) {
		tmp += ( d[k][u] - d[k][v] ) * ( f[q[k]][q[v]] - f[q[k]][q[u]] );
	      }    
	    }
	    tmp *= original_symmetric_factor;
	    move_values[u][v] = tmp;
	  } else { /* change derived from prev iteration, u and v differ from rchosen or schosen */
	    tmp = original_symmetric_factor * ( d[r][u] - d[r][v] + d[s][v] - d[s][u] ) *
	      ( f[q[s]][q[u]] - f[q[s]][q[v]] + f[q[r]][q[v]] - f[q[r]][q[u]] );
	    tmp += move_values[u][v];
	    move_values[u][v] = tmp;
	  }
	  if (tmp < max_decrease) {
	    max_decrease = tmp;
/*    	    printf(" max-decr = %ld\n",tmp); */
	    rchosen = u; /* memorize move */
	    schosen = v; /* memorize move */
	  }	   
	}
      }
    }
    if ( max_decrease < 0 ) {      /* Obj. function value can be improved */
      assert (rchosen < schosen);
      improvement = TRUE;
      swap(rchosen,schosen,q);    
/*        printf(" max-decr = %ld\n",max_decrease); */
      r = rchosen; /* memorize previously done move */
      s = schosen; /* memorize previously done move */

      VERYVERBOSE ( printf("improvement %ld, exchange %ld and %ld\n",max_decrease,rchosen, schosen); )
    }
  }
  VERYVERBOSE ( printf("best 2-opt, value after %ld\n",compute_evaluation_function(q)); )

  free ( move_values );
}



void best_2_opt_asymmetric_tabu ( long int * q ) {
/*    
      FUNCTION:      best improvement 2-opt local search for asymmetric instances
                     computes the move values for the tabu search
      INPUT:         pointer to some initial assignment
      OUTPUT:        none
      (SIDE)EFFECTS: initial assignment is locally optimized
      COMMENTS:      fast evaluation of moves with additional matrix move_values
                     the first local search iteration is slow 
                     local search looks for best neighboring solution in each iteration
      NOTES:         obviously, the code could overall be made a bit simpler if using this 
                     function also in the iterative improvement algorithm.
*/

  long int   u, v, k;
  long int   r, s;                      /* memorize which is best move in previous iteration */
  long int   tmp;
  long int   original_symmetric_factor; /* = 2: original symmetric instance
					   = 1: original asymmetric instance 
					*/

  VERYVERBOSE ( printf("best imp, asymmetric case\n"); )
  if ( make_symmetric_flag )
    original_symmetric_factor = 1;
  else
    original_symmetric_factor = 2;

  r = rchosen;
  s = schosen;

  /* in the first local search iteration the full neighborhood has to be evaluated */
  if (first_it_flag) {
    first_it_flag = FALSE;
    for ( u = 0 ; u < n-1 ; u++) {
      for ( v = u+1 ; v < n ; v++) {
	tmp = 0;
	for ( k = 0 ; k < n ; k++ ) {
	  if ( (k != u) && (k != v) ) {
	    tmp += d[k][u] * ( f[q[k]][q[v]] - f[q[k]][q[u]] ) + 
	      d[k][v] * ( f[q[k]][q[u]] - f[q[k]][q[v]] ) + 
	      d[u][k] * ( f[q[v]][q[k]] - f[q[u]][q[k]] ) + 
	      d[v][k] * ( f[q[u]][q[k]] - f[q[v]][q[k]] );
	  }    
	}
	tmp += d[u][u] * ( f[q[v]][q[v]] - f[q[u]][q[u]] )+
	  d[u][v] * ( f[q[v]][q[u]] - f[q[u]][q[v]] )+
	  d[v][u] * ( f[q[u]][q[v]] - f[q[v]][q[u]] )+ 
	  d[v][v] * ( f[q[u]][q[u]] - f[q[v]][q[v]] );
	move_values[u][v] = tmp;
      }
    }
  } else {
    for ( u = 0 ; u < n-1 ; u++) {
      for ( v = u+1 ; v < n ; v++) {
	if (u == r || v == s || u == s || v == r) {
	  tmp = 0;
	  for ( k = 0 ; k < n ; k++ ) {
	    if ( (k != u) && (k != v) ) {
	      tmp += d[k][u] * ( f[q[k]][q[v]] - f[q[k]][q[u]] ) + 
		d[k][v] * ( f[q[k]][q[u]] - f[q[k]][q[v]] ) + 
		d[u][k] * ( f[q[v]][q[k]] - f[q[u]][q[k]] ) + 
		d[v][k] * ( f[q[u]][q[k]] - f[q[v]][q[k]] );
	    }    
	  }
	  tmp += d[u][u] * ( f[q[v]][q[v]] - f[q[u]][q[u]] )+
	    d[u][v] * ( f[q[v]][q[u]] - f[q[u]][q[v]] )+
	    d[v][u] * ( f[q[u]][q[v]] - f[q[v]][q[u]] )+ 
	    d[v][v] * ( f[q[u]][q[u]] - f[q[v]][q[v]] );
	  move_values[u][v] = tmp;
	} else { /* change derived from move_values */
	  tmp = ( d[r][u] - d[r][v] + d[s][v] - d[s][u] ) *
	    ( f[q[s]][q[u]] - f[q[s]][q[v]] + f[q[r]][q[v]] - f[q[r]][q[u]] )
	      + ( d[u][r] - d[v][r] + d[v][s] - d[u][s] ) *
	    ( f[q[u]][q[s]] - f[q[v]][q[s]] + f[q[v]][q[r]] - f[q[u]][q[r]] );
	  tmp += move_values[u][v];
	  move_values[u][v] = tmp;
	}
      }
    }
  }
}



void best_2_opt_symmetric_tabu ( long int * q ) {
/*    
      FUNCTION:      best improvement 2-opt local search for symmetric instances
                     computes the move values for the tabu search
      INPUT:         pointer to some initial assignment
      OUTPUT:        none
      (SIDE)EFFECTS: initial assignment is locally optimized
      COMMENTS:      faster evaluation of moves with additional matrix move_values
      NOTES:         obviously, the code could overall be made a bit simpler if using this 
                     function also in the iterative improvement algorithm.
*/

  long int   u, v, k;
  long int   r, s;
  long int   tmp;
  long int   original_symmetric_factor;

  VERYVERBOSE ( printf("best imp, symmetric case\n"); )
  if ( make_symmetric_flag )
    original_symmetric_factor = 1;
  else
    original_symmetric_factor = 2;

  r = rchosen;
  s = schosen;

  /* in the first iteration the full neighborhood has to be evaluated */
  if (first_it_flag) {
    first_it_flag = FALSE;
    for ( u = 0 ; u < n-1 ; u++) {
      for ( v = u+1 ; v < n ; v++) {
	tmp = 0;
	for ( k = 0 ; k < n ; k++ ) {
	  if ( (k != u) && (k != v) ) {
	    tmp += ( d[k][u] - d[k][v] ) * ( f[q[k]][q[v]] - f[q[k]][q[u]] );
	  }    
	}
	move_values[u][v] = tmp * original_symmetric_factor;
      }
    }
  } else {
    for ( u = 0 ; u < n-1 ; u++) {
      for ( v = u+1 ; v < n ; v++) {
	if (u == r || v == s || u == s || v == r) {
	  tmp = 0.;
	  for (k = 0 ; k < n ; k++) {
	    if ( (k != u) && (k != v) ) {
	      tmp += ( d[k][u] - d[k][v] ) * ( f[q[k]][q[v]] - f[q[k]][q[u]] );
	    }    
	  }
	  move_values[u][v] = tmp * original_symmetric_factor;
	} else { /* change derived from prev iteration, u and v differ from rchosen or schosen */
	  tmp = original_symmetric_factor * ( d[r][u] - d[r][v] + d[s][v] - d[s][u] ) *
	    ( f[q[s]][q[u]] - f[q[s]][q[v]] + f[q[r]][q[v]] - f[q[r]][q[u]] );
	  tmp += move_values[u][v];
	  move_values[u][v] = tmp;
	}
      }
    }
  }
}



long int ** init_move_values( )
/*    
      FUNCTION:      allocate and initialize the move values of speed-up in tabu search
      INPUT:         instance size
      OUTPUT:        pointer to matrix, has to be freed before next tabu search run
      (SIDE)EFFECTS: current assignment is modified
*/
{
  long int i, j;
  long int **matrix;

  VERYVERBOSE ( printf("initialize matrix of move values for tabu search\n"); ) 

  if((matrix = malloc(sizeof(long int) * n * n +
		      sizeof(long int *) * n	 )) == NULL){
    fprintf(stderr,"Out of memory, exit.\n"); 
    exit(1);
  }

  for ( i = 0 ; i < n ; i++ ) {
    matrix[i] = (long int *)(matrix + n) + i*n;
    for (j = 0 ; j < n ; j++ ) {
      matrix[i][j] = 0;
    }
  }
  return matrix;
}



long int choose_tabu_length( )
/*    
      FUNCTION:      choose a new tabu list length
      INPUT:         instance size
      OUTPUT:        none
      (SIDE)EFFECTS: changes the value of variable tabu__list_length
*/
{
  double  help, min, max;

  min      = 0.9  * n;
  max      = 1.1  * n;
  help     = min + ran01( &seed ) * (max - min);
  if (help < 2 )
    help = 2;
  return   help;
}



long int ** init_tabu( )
/*    
      FUNCTION:      allocate and initialize the tabu values
      INPUT:         instance size
      OUTPUT:        pointer to matrix, has to be freed before next trial
      (SIDE)EFFECTS: current assignment is modified
*/
{
  long int i, j;
  long int     **matrix;

  VERYVERBOSE ( printf("initialze matrix of tabu values\n"); ) 

  if((matrix = malloc(sizeof(long int) * n * n +
		      sizeof(long int *) * n )) == NULL){
/*      printf("Out of memory, exit."); */
    exit(1);
  }

  for ( i = 0 ; i < n ; i++ ) {
    matrix[i] = (long int *)(matrix + n) + i*n;
    for (j = 0 ; j < n ; j++ ) {
      matrix[i][j] = 0;
    }
  }
  return matrix;
}



void  make_tabu( long int * q, long int iteration, long int r, long int s )
/*    
      FUNCTION:      make an invers move tabu (forbids a location for an item)
      INPUT:         pointer to some assignment, iteration number, two locations involved in move
      OUTPUT:        none
      (SIDE)EFFECTS: matrix of tabu_values is modified
*/
{
  tabu_values[r][q[r]] = iteration + tabu_list_length;
  tabu_values[s][q[s]] = iteration + tabu_list_length;
}



void select_move( long int *q, long int current, long int iteration, long int best_so_far )
/*    
      FUNCTION:      select the best move which is not tabu or is aspired
      INPUT:         pointer to some assignment, obj_f_val of current solution, iteration number
      OUTPUT:        none
      (SIDE)EFFECTS: global variables rchosen and schosen are assigned the locations involved in the move
*/
{
  long int   i, j;
  long int   max_decrease;
  long int   taboo, aspired;
  
  max_decrease = LONG_MAX;
  rchosen = n; schosen = n;
  for ( i = 0 ; i < n - 1 ; i++) {
    for (j = (i+1); j < n ; j++) {
      if ( (tabu_values[i][q[j]] > iteration ) && (tabu_values[j][q[i]] > iteration ) )
	taboo = TRUE;
      else 
	taboo = FALSE;
      if ( ((current + move_values[i][j]) < best_so_far ) && taboo )
	aspired = TRUE;
      else if ( tabu_values[i][q[j]] < aspirating_iteration && 
	      tabu_values[j][q[i]] < aspirating_iteration )
	aspired = TRUE;
      else 
	aspired = FALSE;
      if ( (move_values[i][j] < max_decrease && !taboo) || aspired ) {
	rchosen = i;
	schosen = j;
	if ( aspired && !taboo ) {
	  max_decrease = LONG_MIN;
	}
	else 
	  max_decrease = move_values[i][j];
      }
    }
  }
  assert ( rchosen >= 0 && rchosen < n);
  assert ( schosen >= 0 && schosen < n);
}



void tabu_search( long int *s )
/*    
      FUNCTION:      perform robust tabu search
      INPUT:         pointer to initial solution
      OUTPUT:        pointer to best solution
      (SIDE)EFFECTS: 
*/
{
  long int  i;
  long int  iterations, obj_f_value, *b, *q;
  long int  best_so_far = 0;

  VERYVERBOSE ( printf("tabu search\n"); )
  move_values = init_move_values( );
  tabu_values = init_tabu( );
  b = malloc( n * sizeof(long int) );
  q = malloc( n * sizeof(long int) );
  for ( i = 0 ; i < n ; i++ ) {
    q[i] = s[i];
    b[i] = s[i];
  }
  obj_f_value       = compute_evaluation_function( b );
  best_so_far       = obj_f_value;
  first_it_flag     = TRUE;  
  rchosen           = schosen      = 0;
  iterations        = 1;
  tabu_list_length  = choose_tabu_length();

/*    printf("tabu_search_length %ld\n",tabu_search_length); */

  while ( iterations < tabu_search_length ) {

    aspirating_iteration = iterations - iterations_before_aspiration;

    if ( d_symmetric_flag && f_symmetric_flag && null_diagonal_flag )
      best_2_opt_symmetric_tabu ( q );
    else if ( make_symmetric_flag )
      best_2_opt_symmetric_tabu ( q );
    else
      best_2_opt_asymmetric_tabu ( q );

    select_move( q , obj_f_value, iterations , best_so_far );

    make_tabu( q, iterations, rchosen, schosen ); /* make_tabu has to go before swap */

    swap( rchosen, schosen, q );

    obj_f_value += move_values[rchosen][schosen];

    if ( obj_f_value < best_so_far ) {
      best_so_far = obj_f_value;
/*        printf("best %ld\t time %f\n",best_so_far,elapsed_time( VIRTUAL )); */
      for ( i = 0 ; i < n ; i++ ) 
	b[i] = q[i];
    }

    if ( !(iterations % ( long int )(2.2 * n + 4))) {
      tabu_list_length = choose_tabu_length();
      VERYVERBOSE ( printf(" tabu_length = %ld, iteration %ld\n",tabu_list_length, iterations); )
    }
    iterations++;

  }

  DEBUG ( if ( compute_evaluation_function( b ) != best_so_far )
    fprintf(stderr,"Some error must have occurred in local search routine,\n values do not match\n");
        )
  for ( i = 0 ; i < n ; i++ ) 
    s[i] = b[i];
  free ( b );
  free ( q );
  free ( move_values );
  free ( tabu_values );

}




void first_2_opt_asymmetric ( long int * q ) {
/*    
      FUNCTION:      first improvement 2-opt local search for asymmetric instances
      INPUT:         pointer to initial assignment
      OUTPUT:        none
      (SIDE)EFFECTS: initial assignment is locally optimized
*/

      long int   improvement = TRUE;
      long int   improve_item = FALSE;
      long int   u, v, k;
      long int   tmp;

      VERBOSE ( printf("first imp, asymmetric case\n"); )
      for ( k = 0 ; k < n ; k++ ) {
	  dlb[k] = FALSE;
      }

      while ( improvement ) {
	  improvement = FALSE;
	  for ( u = 0 ; u < n ; u++) {
	      if ( dlb_flag && dlb[u] )
		  continue;
	      improve_item = FALSE;
	      for ( v = 0 ; v < n ; v++) {
		  if (u == v)
		      continue;
		  tmp = 0;
		  for ( k = 0 ; k < n ; k++ ) {
		      if ( (k != u) && (k != v) ) {
			  tmp += d[k][u] * ( f[q[k]][q[v]] - f[q[k]][q[u]] ) + 
			      d[k][v] * ( f[q[k]][q[u]] - f[q[k]][q[v]] ) + 
			      d[u][k] * ( f[q[v]][q[k]] - f[q[u]][q[k]] ) + 
			      d[v][k] * ( f[q[u]][q[k]] - f[q[v]][q[k]] );
		      }    
		  }
		  tmp += d[u][u] * ( f[q[v]][q[v]] - f[q[u]][q[u]] )+
		      d[u][v] * ( f[q[v]][q[u]] - f[q[u]][q[v]] )+
		      d[v][u] * ( f[q[u]][q[v]] - f[q[v]][q[u]] )+ 
		      d[v][v] * ( f[q[u]][q[u]] - f[q[v]][q[v]] );
		  if (tmp < 0) {
		      improvement = TRUE;
		      improve_item = TRUE;	  
		      dlb[u] = FALSE;
		      dlb[v] = FALSE;	  
		      swap( u, v, q);
		  }
	      }
	      if ( !improve_item )
		  dlb[u] = TRUE;
	  }
      }
  }



void first_2_opt_symmetric ( long int *q ) {
/*    
      FUNCTION:      first improvement 2-opt local search for symmetric instances
      INPUT:         pointer to some initial assignment
      OUTPUT:        none
      (SIDE)EFFECTS: initial assignment is locally optimized
*/

    long int   improvement = TRUE;
    long int   improve_item = FALSE;
    long int   u, v, k;
    long int   tmp;
    long int   original_symmetric_factor; /* = 2: original symmetric instance
					     = 1: original asymmetric instance 
					  */

    VERBOSE (  printf("first imp, symmetric case\n"); )
    for ( k = 0 ; k < n ; k++ ) {
	dlb[k] = FALSE;
    }
    if ( make_symmetric_flag )
	original_symmetric_factor = 1; /* compensation because of not dividing matrix by 2 */
    else
	original_symmetric_factor = 2;
    improvement   = TRUE;
    while ( improvement ) {
	improvement = FALSE;
	for ( u = 0 ; u < n ; u++ ) {
	    if ( dlb_flag && dlb[u] )
		continue;
	    improve_item = FALSE;
	    for ( v = 0 ; v < n ; v++ ) {
		if (u == v)
		    continue;
		tmp = 0;
		for ( k = 0 ; k < n ; k++ ) {
		    if ( (k != u) && (k != v) ) {
			tmp += ( d[k][u] - d[k][v] ) * ( f[q[k]][q[v]] - f[q[k]][q[u]] );
		    }    
		}
		tmp *= original_symmetric_factor;
		if (tmp < 0) {
		    improvement = TRUE;
		    improve_item = TRUE;	  
		    dlb[u] = FALSE;
		    dlb[v] = FALSE;	  
		    swap( u, v, q);
		    VERYVERBOSE ( printf("improvement %ld\n",tmp); )
	        }
	    }
	    if ( improve_item )
		dlb[u] = FALSE;
	    else
		dlb[u] = TRUE;	
	}
    }
}



void local_search( long int *s ) {
/*    
      FUNCTION:      this function calls the chosen local search routine in the MMAS algorithm
      INPUT:         pointer to some initial assignment
      OUTPUT:        none
      (SIDE)EFFECTS: initial assignment is locally optimized
*/

    if ( d_symmetric_flag && f_symmetric_flag && null_diagonal_flag ) {
	if ( local_search_flag == 2 )
	    best_2_opt_symmetric( s );
	else if ( local_search_flag == 3 )
	    tabu_search( s );
	else if ( local_search_flag == 4 )
	    tabu_search( s );
	else 
	    first_2_opt_symmetric ( s );
    }
    else if ( make_symmetric_flag ) {
	if ( local_search_flag == 2 )
	    best_2_opt_symmetric( s );
	else if ( local_search_flag == 3 )
	    tabu_search( s );
	else if ( local_search_flag == 4 )
	    tabu_search( s );
	else
	    first_2_opt_symmetric ( s );
    }
    else {
	if ( local_search_flag == 2 )
	    best_2_opt_asymmetric( s );
	else if ( local_search_flag == 3 )
	    tabu_search( s );
	else if ( local_search_flag == 4 )
	    tabu_search( s );
	else
	    first_2_opt_asymmetric ( s );
    }  
}



void usage()
/*    
      FUNCTION:      output usage of program
      INPUT:         none
      OUTPUT:        none
      (SIDE)EFFECTS: 
*/
{
    fprintf(stderr,"\nILS for QAP, Configuration, V0.99\n");
    fprintf(stderr,"usage: [- see below -] [-i dat_file] (given are long and short options)\n");
    fprintf(stderr,"--input        -i #\t input file\n");
    fprintf(stderr,"--trials       -r #\t number of trials to be run on one instance, default 1\n");
    fprintf(stderr,"--iterations   -j #\t maximum number of iterations, default 1\n");
    fprintf(stderr,"--time         -t #\t maximum time limit\n");
    fprintf(stderr,"--localsearch  -l #\t local search type to be run, default 2\n");
    fprintf(stderr,"                  #\t 0: first improvement, don't look bits\n");
    fprintf(stderr,"                  #\t 1: first improvement, no don't look bits\n");
    fprintf(stderr,"                  #\t 2: best improvement\n");
    fprintf(stderr,"                  #\t 3: short tabu search runs of length 4n\n");
    fprintf(stderr,"                  #\t 4: short tabu search runs of length 10n\n");
    fprintf(stderr,"--ants         -m #\t number of ants in the colony, default 5\n");
    fprintf(stderr,"--rho          -e #\t rho, factor in pheromone evaporation: tau = rho * tau ..\n");
    fprintf(stderr,"                  #\t default value is 0.8\n");
    fprintf(stderr,"--optimal      -o #\t stop when hitting a solution of that quality\n");
    fprintf(stderr,"--seed         -s #\t Seed for random number generator: if absent,\n");
    fprintf(stderr,"                  #\t a seed is somehow generated...\n");
    fprintf(stderr,"--help         -h \t\t help: prints this information\n");
}



void set_default_parameters()
/*    
      FUNCTION:      set default parameter values
      INPUT:         none
      OUTPUT:        none
      (SIDE)EFFECTS: assigns some values to global variables
*/
{
    max_trials         = 1;
    tabu_search_length = 4;
    time_limit         = 30.;
    max_iterations     = 1;
    m                  = 5;
    rho                = 0.6;
    optimal            = 1;
    local_search_flag  = 2; 
    tau_max            = 1.0;
    update_gb          = 3;
    update_rb          = 30;     
    restart_iterations = 5;
}



void print_header ( ) {
/*    
      FUNCTION:      prints the header of the output file
      INPUT:         none
      OUTPUT:        none
      (SIDE)EFFECTS: none
*/

/*   fprintf(output_file,"Celeron 2GHz, 256 kB Cache\n"); */
/*   fprintf(output_file,"Compiler gcc 3.3.5 (Debian 1:3.3.5-6) Flags -O3 -ansi -Wall\n"); */
/*   fprintf(output_file,"OS Debian Linux\n\n"); */
    fprintf(output_file,"MAX-MIN Ant System for QAP, V0.99\n\n");
    fprintf(output_file,"Parameter Settings\n\n");
    fprintf(output_file,"tries %ld\n", max_trials);
    fprintf(output_file,"local search %ld\n", local_search_flag);
    fprintf(output_file,"rho %f\n\n", rho);
    fprintf(output_file,"ants %ld\n\n", m);
    fprintf(output_file,"iterations %ld\n\n", max_iterations);
    fprintf(output_file,"time %f\n\n", time_limit);

    fprintf(output_file,"Initialization time %f\n\n", elapsed_time ( VIRTUAL ) );
    fprintf(output_file,"begin problem %s\n",name_buf);
}




void checkOutOfRange(int value, int MIN, int MAX, char *optionName){

    if ((value<MIN)||(value>MAX)){
	fprintf(stderr,"Error: Option `%s' out of range\n",optionName);
	exit(1);
    }

}



void check_options(int argc, char *argv[]) {
  
    while (1){
	int option_index = 0;

	static struct option long_options[] = {
	    {"input",       1, 0, 'i'},
	    {"localsearch", 1, 0, 'l'},
	    {"ants",        1, 0, 'm'},
	    {"rho",         1, 0, 'e'},
	    {"time",        1, 0, 't'},
	    {"iterations",  1, 0, 'j'},
	    {"trials",      1, 0, 'r'},
	    {"optimal",     1, 0, 'o'},
	    {"seed",        1, 0, 's'},
	    {"help",        0, 0, 'h'},
	    {0,             0, 0,  0 }
	};
    
	opt = getopt_long(argc, argv, "t:r:l:e:i:j:h:m:o:s:",
			  long_options, &option_index);
	if (opt == -1)
	    break;
    
	switch (opt){
	    case 0:
		fprintf(stderr,"Error: Confused by input on long option...\n"), exit(1);
		break;
      
	    case 't':
		time_limit = atof(optarg);
		break;
      
	    case 'j':
		max_iterations = atol(optarg);
		checkOutOfRange(max_iterations,1,100000,"j (iterations)");
		break;
      
	    case 'r':
		max_trials = atol(optarg);
		checkOutOfRange(max_trials,1,1000,"r (trials)");
		break;
      
	    case 'l':
		local_search_flag = atol(optarg);
		checkOutOfRange(local_search_flag,0,4,"l (local_search_flag)");
		break;

	    case 'm':
		m = atol(optarg);
		checkOutOfRange(m,0,151,"m (popsize)");
		break;

	    case 'e':
		rho = atof(optarg);
		checkOutOfRange(rho,0,1,"l (rho)");
		break;

	    case 'o':
		optimal = atol(optarg);
/*        checkOutOfRange(optimal,0,LONG_MAX/2,"o (optimal)"); */
		break;

	    case 's':
		seed = atol(optarg);
		/* I'm not checking if in range... I trust the user :-) */
		break;

	    case 'i':
		strncpy(name_buf,optarg,strlen(optarg));
		break;

	    case 'h':
		usage();
		fprintf(stderr,"No more help yet, sorry.\n"), exit(1);
		break;
      
	    default:
		fprintf(stderr,"Error: Confused by input... %ld\n",opt), exit(1);
      
	}
    }
}  



void init_program( long int argc, char *argv[] )
/*    
      FUNCTION:      all the stuff for starting the program: input, parameters, etc.
      INPUT:         argument list from program call
      OUTPUT:        none
*/
{
    FILE *qap_file;
    long int i;
    char buf[LINE_BUF_LEN], *c;    /* input file name */

    setbuf(stdout,NULL);
    printf(PROG_ID_STR);

    if (seed<0) 
	seed = (long int) time(NULL); /* initialize random number generator */

    printf("seed %ld\n", seed);

    if( (qap_file = fopen(name_buf, "r")) == NULL) {
	fprintf(stderr, "error opening input file %s\n",name_buf);
	exit(1);	
    }

    /* read instance data */
    read_problem_size( qap_file );
    read_best_known_value( qap_file );
    d = read_matrix( qap_file, n);
    d_symmetric_flag = check_symmetry ( d, n );
    null_diagonal_flag = check_null_diagonal ( d, n );   
    VERYVERBOSE ( print_matrix( d ); )  
	f = read_matrix( qap_file, n );

    /* check for null-diagonal; make symmetric if possible (at most one asymmetric matrix) */
    f_symmetric_flag = check_symmetry ( f, n );
    if ( null_diagonal_flag )
	; /* if one matrix has already null diagonal we need not check the other */
    else
	null_diagonal_flag = check_null_diagonal ( f, n );

    VERBOSE ( printf("d_symmetric_flag %ld, f_symmetric_flag %ld, null_diagonal_flag %ld\n",d_symmetric_flag, f_symmetric_flag, null_diagonal_flag); )

	make_symmetric_flag = XOR(d_symmetric_flag,f_symmetric_flag);
    if ( make_symmetric_flag && null_diagonal_flag ) {
	if ( !d_symmetric_flag )
	    make_matrix_symmetric ( d, n );
	else if ( !f_symmetric_flag )
	    make_matrix_symmetric ( f, n );
	else {
	    fprintf(stderr,"One matrix should have been symmetric\n");
	    exit(1);
	}
    }
     
    /* generate output file names and open them; I assume Lunix, Unix directory separators "/" */
    if ( ( c = strrchr(name_buf,'/') ) != NULL ) {
	c++;
	i = 0;
	while ((buf[i] = *c) != '\0') {
	    i++;
	    c++;
	}
	printf("%s\n",buf);
	strcpy(name_buf, buf);
    }
  
    sprintf(buf,"%s.MMAS.v.2.0.t%.2f.rep",name_buf,time_limit);
    if( (output_file = fopen(buf, "w")) == NULL) {
	fprintf(stderr, "error opening output file %s\n","qap.rep");
	exit(1);	
    }
  
    sprintf(buf,"%s.MMAS.v.2.0.t%.2f.sum",name_buf,time_limit);  
    if( (output_summary_file = fopen(buf, "w")) == NULL) {
	fprintf(stderr, "error opening output file %s\n","qap.sum");
	exit(1);	
    }
 
    /* dlb_flag = TRUE only reasonable for first-improvement */
    if ( ( local_search_flag == 0 ) )
	dlb_flag = TRUE;
    else
	dlb_flag = FALSE;
  
    if ( local_search_flag == 3 )
	tabu_search_length = 4;
    else if ( local_search_flag == 4 )
	tabu_search_length = 10;
    tabu_search_length *= n;
    /* the following was used in original Robust Tabu Search; probably never applies here */
    iterations_before_aspiration = (long int)(3. * n * n);

    /* allocate memory for colony and to keep track of some solutions */
    global_best = malloc( n * sizeof(long int) );
    restart_best = malloc( n * sizeof(long int) );
    colony = malloc( m * sizeof(ant_struct) );
    for ( i = 0 ; i < m ; i++ ) {
	colony[i].s = malloc( n * sizeof(long int) );
	colony[i].occupied = malloc( n * sizeof(long int) );
    }
    VERBOSE ( printf("end init program\n"); )

}



void start_trial( )
/*    
      FUNCTION:      initializes some stuff when starting a new independent trial
      INPUT:         none
      OUTPUT:        none
*/
{
    long int i;

    printf("start trial %ld .. \n", trials);
    start_timers();
    time_best_found = 0.0;
    iteration_best_found = 0;
    last_improvement = 0;
    iterations = 1;
    iterations_since_pheromone_reinit = 1;
    iteration_pheromone_reinit = 1;
    restart_iterations = 5;
    if ( restart_iterations < 5 )
	restart_iterations = 5;
    update_rb = n / 3; 
    if ( update_rb < 10 )
	update_rb = 10;

    global_best_value = LONG_MAX;
    restart_best_value = LONG_MAX;
    pheromone = generate_pheromone_matrix( n ); 

    fprintf(output_file,"begin try %li\n",trials);
    dlb = malloc( n * sizeof(long int) );
    for ( i = 0 ; i < n ; i++ ) {
	dlb[i] = FALSE;
    }
    VERYVERBOSE ( printf(".. done\n"); ) 
}



void end_trial( )
/*    
      FUNCTION:      does some final clean-up after a trial ends
      INPUT:         none
      OUTPUT:        none
*/
{

    fprintf(output_file,"end try %ld\t total-time %f\n",trials, elapsed_time( VIRTUAL ));
    fprintf(output_summary_file,"best %ld\titeration %ld\ttime-to-best %.2f\ttotal-time %.2f\n",global_best_value, iteration_best_found, time_best_found,elapsed_time( VIRTUAL ));
    fflush( output_file ); 
    fflush( output_summary_file ); 

    free( pheromone );
    free( dlb );

    printf("end try %li\n",trials);
}


float avg_node_branching ( void ) {
  /*    
	FUNCTION:      computes the average node branching factor
	INPUT:         none
	OUTPUT:        average node branching factor
	COMMENTS:      since here the average node branching factor is computed for MAX-MIN 
	Ant System, we do a simplified form that considers only how many 
	pheromone trails are larger than a fixed factor above tau_min, since the 
	minimum amount of pheromone is known a priori
  */

  long int i, j;
  float    lambda = 1.05;
  float    cutoff;
  float    avg;
  float    *num_branches;
    
  num_branches = malloc ( n * sizeof(float));

  cutoff = lambda * tau_min;

  for ( i = 0 ; i < n ; i++) {
    num_branches[i] = 0.;
  }

  for ( i = 0 ; i < n ; i++ ) {
     for ( j = 0 ; j < n ; j++) {
      if ( i == j )
	continue;
      if ( pheromone[i][j] > cutoff )
	num_branches[i] += 1;
    }
  }

  avg = 0.;
  for ( i = 0 ; i < n ; i++ ) {
    avg += num_branches[i];
  }
  return ( avg / (float) n);
}


void choose_location( long int individual, long int item)
/*    
      FUNCTION:      choose a location where to put the item 
      INPUT:         number indicating the ant and the item to be placed
      OUTPUT:        none
      (SIDE)EFFECTS: places the item on a location loc
*/
{ 
    long int  i;
    float     rnd, partial_sum = 0., sum_prob = 0.;
    float     *prob;
    long int  loc;

    prob = malloc ( n * sizeof(float));
  
    DEBUG( assert ( item >= 0 && item < n ); )

    for ( i = 0 ; i < n ; i++) {
	if ( colony[individual].occupied[i] ) 
	    prob[i] = 0.0;
	else {
	    prob[i] = pheromone[item][i];
	    sum_prob += prob[i];
	} 
    }

    /* now select to which location assign next an object */
    rnd = ran01(&seed);
    rnd *= sum_prob;
    i = 0;
    partial_sum = prob[i];
    while ((partial_sum < rnd) && ( i < n-1 )) {
	i++;
	partial_sum += prob[i]; 
    }
    loc = i;
    DEBUG( assert ( loc >= 0 && loc < n ); )
    colony[individual].occupied[loc] = TRUE;
    colony[individual].s[loc] = item;
    free(prob);
}



void evaporation( void )
/*    
      FUNCTION:      simulate the pheromone evaporation in each iteration 
      INPUT:         none
      OUTPUT:        none
      (SIDE)EFFECTS: all pheromone trails are reduced by a factor rho
*/
{ 
    long int i, j;
  
    for ( i = 0; i < n ; i++ ) {
	for ( j = 0 ; j < n ; j++ ) {
	    pheromone[i][j] = rho * pheromone[i][j];
	}
    }
}

    

void deposit_pheromone( long int *s, long int value )
/*    
      FUNCTION:      deposit pheromone on solution s  
      INPUT:         solution s and its objective function value
      OUTPUT:        none
      (SIDE)EFFECTS: increases pheromone on components of the solution s
*/
{  

    long int  i;
    float     d_tau;
  
    d_tau = 1. / (float) value;
/*      d_tau = 1.; */
    VERYVERBOSE ( printf(" value = %ld, d_tau = %.10f\n",value, d_tau); )
    for ( i = 0 ; i < n ; i++ ) {
	pheromone[s[i]][i] += d_tau;
    }
}



void init_pheromones( float value )
/*    
      FUNCTION:      sets all pheromone trails to a specific value  
      INPUT:         value to which pheromone trails are set
      OUTPUT:        none
      (SIDE)EFFECTS: see FUNCTION
*/
{
    long int i, j;

    for ( i = 0; i < n ; i++ ) {
	for ( j = 0; j < n ; j++ ) {
	    pheromone[i][j] = value;
	}
    }
}



void check_tau_min( void )
/*    
      FUNCTION:      controls lower pheromone trail limit  
      INPUT:         none
      OUTPUT:        none
      (SIDE)EFFECTS: sets all pheromone trails lower than tau_min to tau_min
*/
{
    long int i, j;

    for ( i = 0; i < n ; i++ ) {
	for ( j = 0; j < n ; j++ ) {
	    if ( pheromone[i][j] < tau_min) 
		pheromone[i][j] = tau_min;
	}
    }
}



void check_tau_max( void )
/*    
      FUNCTION:      controls upper pheromone trail limit  
      INPUT:         none
      OUTPUT:        none
      (SIDE)EFFECTS: sets all pheromone trails larger than tau_max to tau_max
*/
{
    long int i, j;

    for ( i = 0; i < n ; i++ ) {
	for ( j = 0; j < n ; j++ ) {
	    if ( pheromone[i][j] > tau_max) 
		pheromone[i][j] = tau_max;
	}
    }
}



void mmas_construct( void )
/*    
      FUNCTION:      main wrapper for the ants' solution construction
      INPUT:         none
      OUTPUT:        none
      (SIDE)EFFECTS: the ants solutions are constructed
      COMMENTS:      here one ant after another constructs a solutions since each ant 
                     is independent of any other ant (this is not the case in Ant Colony 
		     System!)
*/
{

    long int i, j;
    long int *objects; 

    VERYVERBOSE ( printf("begin mmas_construct\n"); )

    for ( i = 0 ; i < m ; i++ ) {
	objects = generate_random_vector( n );
	for ( j = 0 ; j < n ; j++ ) {
	    colony[i].occupied[j] = FALSE;
	}
	for ( j = 0 ; j < n ; j++ ) {
	    choose_location( i , objects[j] );
	}
	colony[i].value = compute_evaluation_function( colony[i].s );
	free(objects);
    }
    VERYVERBOSE ( printf("end mmas_construct\n"); )
}



void mmas_local_search()
/*    
      FUNCTION:      main wrapper for the ants' local search phase
      INPUT:         none
      OUTPUT:        none
      (SIDE)EFFECTS: the ants solutions are locally optimized
*/
{

    long int i;

    VERYVERBOSE ( printf("begin mmas_local_search\n"); )
    for ( i = 0 ; i < m ; i++ ) {
/*  	check_permutation( colony[i].s ); */
	local_search( colony[i].s );
/*     best_2_opt_symmetric( colony[i].s ); */
/*  	check_permutation( colony[i].s ); */
	colony[i].value = compute_evaluation_function( colony[i].s );
    }
    VERYVERBOSE ( printf("end mmas_local_search\n"); )

}



void mmas_update_statistics( )
/*   
      FUNCTION:      procedure to update some statistics (best found, etc)
      INPUT:         none
      OUTPUT:        none
      (SIDE)EFFECTS: possible update of global-best, restart-best, and pheromone trail limits
*/
{

    long int  i; 

    float     p_dec, help;


    for ( i = 0 ; i < m ; i++ ) {
	if ( colony[i].value < global_best_value ) {
	    time_best_found = elapsed_time( VIRTUAL ); 
	    global_best_value = colony[i].value;
	    p_dec = pow(0.005, 1. / n ); 
	    help = (1. - p_dec) / (p_dec * (double)(n / 2));
	    tau_max = (1. / (float) global_best_value) / (1. - rho) ;
/*  	    tau_max = 1. / (1. - rho) ; */
	    if ( (local_search_flag == 3) || (local_search_flag == 4) ) {
/*  		tau_min = tau_max / (2. * n); */
		tau_min = tau_max * help;
	    }
	    else {
/*  		tau_min = tau_max / (2. * n); */
		tau_min = tau_max * help;
	    }
  	    printf("tau_max %.14f, tau_min %.14f\n",tau_max,tau_min);
	    iteration_best_found = iterations;
	    last_improvement = iterations;
	    DEBUG ( if ( compute_evaluation_function( colony[i].s ) != global_best_value) {
		         printf(" ERROR, gb does not verify, global_best_value: %ld\n",global_best_value);
		         exit(0);
	              } else 
		         printf(" solution does verify \n"); 
		)
	    printf("best %ld\ttime %.2f\titerations %ld\n",global_best_value,time_best_found,iterations);
	    fprintf(output_file,"best %ld\tcycle %ld\tsteps %ld\ttime %.2f\n",global_best_value,iterations,iterations,time_best_found);
	    copy_from_to( colony[i].s, global_best);
	}
  
	if ( colony[i].value < restart_best_value ) {
	    restart_best_value = colony[i].value;
	    last_improvement = iterations;
	    copy_from_to( colony[i].s, restart_best);
	    printf("best since restart: %ld\tcycle %ld\ttime = %.2f\n",restart_best_value,iterations,elapsed_time( VIRTUAL ));
	}

    }
}



void mmas_pheromone_update()
/*    
      FUNCTION:      main wrapper for the ants' pheromone update
      INPUT:         none
      OUTPUT:        none
      (SIDE)EFFECTS: pheromone trails are updated 
*/
{
    long int iteration_best = LONG_MAX;
    long int i, tmp = LONG_MAX;


    evaporation();

    for ( i = 0 ; i < m ; i++ ) {
      if ( colony[i].value < tmp ) {
	tmp = colony[i].value;
	iteration_best = i;
      }
    }

    global_or_restart_update_flag = 1;

    if ( iterations_since_pheromone_reinit < 5 ) {
      printf("ITERATION BEST UPDATE\n");
      deposit_pheromone (colony[iteration_best].s , colony[iteration_best].value); 
    }
    else if ( iterations_since_pheromone_reinit < schedule_length ) {
      if (iterations_since_pheromone_reinit % update_gb) {
	printf("ITERATION BEST UPDATE\n");
	deposit_pheromone (colony[iteration_best].s , colony[iteration_best].value);
      }
      else {
	printf("RESTART BEST UPDATE\n");
	deposit_pheromone(restart_best, restart_best_value);
      }
    }
    else { 

      /*
      if ( tau_max / tau_min > 1. / pow ( rho,(double)(iterations - iteration_pheromone_reinit )) || (iterations - last_improvement < 3 ) ) {
	
	VERYVERBOSE ( printf("RESTART BEST UPDATE\n"); )printf("RESTART BEST UPDATE\n");
	deposit_pheromone(restart_best, restart_best_value);
      }
      else {
	VERYVERBOSE ( printf("GLOBAL BEST UPDATE\n"); )printf("GLOBAL BEST UPDATE\n");
	deposit_pheromone(global_best, global_best_value);
      }
    }
      */

      if (global_or_restart_update_flag) {
	  printf("GLOBAL BEST UPDATE\n");
	  deposit_pheromone(global_best, global_best_value);
	}
      else {
	printf("RESTART BEST UPDATE\n");
	deposit_pheromone(restart_best, restart_best_value);
	}
    }



    /*
    if ( !(iterations_since_pheromone_reinit % update_gb) && ( iterations - iteration_pheromone_reinit >= 3 ) ) {
	if ( tau_max / tau_min > 1. / pow ( rho,(double)(iterations - iteration_pheromone_reinit )) || (iterations - last_improvement < 3 ) ) {

	    VERYVERBOSE ( printf("RESTART BEST UPDATE\n"); )printf("RESTART BEST UPDATE\n");
	    deposit_pheromone(restart_best, restart_best_value);
	}
	else {
	    VERYVERBOSE ( printf("GLOBAL BEST UPDATE\n"); )printf("GLOBAL BEST UPDATE\n");
	    deposit_pheromone(global_best, global_best_value);
	}
    }
    else {
	for ( i = 0 ; i < m ; i++ ) {
	    if ( colony[i].value < tmp ) {
		tmp = colony[i].value;
		iteration_best = i;
	    }
	}
	VERYVERBOSE ( printf("ITERATION BEST UPDATE\n"); ) printf("ITERATION BEST UPDATE\n");
	DEBUG ( assert ( iteration_best <= m ); )
	deposit_pheromone( colony[iteration_best].s , tmp);
    }

    */

    /* now check pheromone trail limits; only lower ones need to be
       checked */ 
    check_tau_min();
    if ( iterations == 1 )
	check_tau_max();
  
    /* adjust parameters for pheromone update */
    if ( iterations_since_pheromone_reinit <= schedule_length / 2 )
	update_gb = 3; 
    if ( iterations_since_pheromone_reinit > schedule_length / 2 )
	update_gb = 2; 
    if ( iterations_since_pheromone_reinit > schedule_length )
	update_gb = 1; 
    if ( (local_search_flag == 3) || (local_search_flag == 4) ) {
	if ( iterations - iterations_since_pheromone_reinit < schedule_length )
	    update_gb = 2;
	else
	    update_gb = 1;
    }
}


void pheromone_reinit( void ) {
/*    
      FUNCTION:      determine whether the pheromone trails should be re-initialized
      INPUT:         none
      OUTPUT:        none
      (SIDE)EFFECTS: pheromone trails are re-initialized to tau_max
*/

  float avg_node_brnch;

    VERYVERBOSE ( printf("Pheromone reinitialization %ld\n",iterations); )


    avg_node_brnch = avg_node_branching();

    printf("avg_node_brnch %.3f\n",avg_node_brnch);

    if ( global_or_restart_update_flag )
      ;
    else if ( (avg_node_brnch < 1.3) && ( iterations - last_improvement > restart_iterations ) )
      global_or_restart_update_flag = 1;

    if ( ( avg_node_brnch < 1.1 ) && ( iterations - last_improvement > restart_iterations ) ) {

/*       print_pheromone(); */
      init_pheromones( tau_max );
      restart_best_value = LONG_MAX;
      last_improvement = iterations;
      iterations_since_pheromone_reinit = 0;
      iteration_pheromone_reinit = iterations;
      update_gb = 3; 
      global_or_restart_update_flag = 0; /* choose restart_best for pheromone update */
    }







}



int main(int argc, char *argv[]) {
  

  /* variables for main programs are declared above */
  

  start_timers();             /* start timing routines */

  set_default_parameters();  
  check_options(argc, argv);
  init_program(argc, argv);   /* initialize all important data */
  print_header ();
  assert ( seed < IM );

  for ( trials = 1 ; trials <= max_trials ; trials ++ ) {

    start_trial();
    last_improvement = 0;

    while ( !termination_condition() ) {
      
      mmas_construct();
      mmas_local_search();
      mmas_update_statistics();
      mmas_pheromone_update();
      
      iterations++;
      iterations_since_pheromone_reinit++; 

      pheromone_reinit();
	  
    }

    end_trial();
    fflush ( output_file );
    fflush ( output_summary_file );

  }
  printf("\n");
  printf("%ld\n",global_best_value);
  fprintf(output_file,"end problem %s\n",name_buf);  
  fflush ( output_file );
  fflush ( output_summary_file );
  free ( d );  /* first matrix */
  free ( f );  /* second matrix */

  return(0);
}


