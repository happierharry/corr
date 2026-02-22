/******************************************************************************/
/*                Searching for a maximum clique using MaxSAT reasoning       */
/*                Author: Chumin LI                                           */
/*                Copyright MIS, University of Picardie Jules Verne, France   */
/*                chu-min.li@u-picardie.fr                                    */
/*                Avril 2008                                                  */
/******************************************************************************/

/* The program is distributed for research purpose, but without any guarantee.
   For any other (commercial or industrial) use of the proram, please contact
   Chumin LI
*/

/* The program read a graph from a file in DIMACS format, a number of colors
   and the a heuristic
   Three heuristics for branching are available: dom, dom+degree, 
   dom+degree+UP
   Exploitation of symmetries between colors
*/

/* Based on color3.c, using parse parameters
 */

/* Based on color6, use node_state au lieu de nodeMark pour G_v
iMaxClique2 is working version in progress.
This is very different from iMaxClique1 which is a final version
 */

/* Based on iMaxClique2, simple lookahead after each backtracking
using matching (pair of nonneibor nodes)
*/

/* Based on iMaxClique3, lookahead after each backtracking
using isets using arrange_sets (insert nodes into an iset
in which a node is chosen as a candidate
Works well when the density is 90%
*/

/* Based on iMaxClique4, use iset_testable1 of iMaxClique1 to
control lookahead when choosing the next node to expand
Also use partitionIntoIsets() of iMaxClique1 when solving
a graph of low density
 */

/* Based on iMaxClique5, distinguish dense and sparse graphs
Works better for sparse graphs
 */

/* Based on iMaxClique7, compute node_nb_neibors after lookahead
also for dense graphs
 */

/* Based on iMaxClique8, when compute nb of neibors for dense graph
directly compute non neibors instead of from noneibors made passive
during expansion

The most efficient on the 22/09/09
 */

/* Based on iMaxClique14, use a new upper bound inspired from 
MaxSAT, limited to propagate unit isets in a partition for lookahead
*/

/* Based on ImaxClique18, propagate binary isets
 */

/* Based on ImaxClique19, apply more maxsatz
 */

/* Based on iMaxClique20, add a new node to every iset in an
inconsistent set.
 */

/* Based on iMaxClique21, test isets of size 2, 3, 4, 5 instead of 
only 2 in iMaxClique21
 */

/* Based on imaxClique22, when nb_extra_isets is one more than 
nb_conflicts, remove failed nodes and propagate unit iset
 */

/* Based on iMaxClique23, move lookahead from choose_candidate
to backtracking
*/

/* Based on iMaxClique23bis, when the graph is sparse, use
get_upper_bound_by_coloring
 */

/* Based on iMaxClique23bisbis, use adjacence matrice in 
patitionIntoIsetsTomita
*/

/* Based on iMaxClique31, expand clq according to adjacence matrice
instead of noneibors
*/

/* Based on iMaxClique32, compute degree information using adjacence
matrice for sparse graphs
 */

/* Based on iMaxClique33, use qsort in partitionIntoIsetTomita
 */

/* Based on iMaxClique35, simplify choose_candidate() function
 */

#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#include <sys/times.h>
#include <sys/types.h>
// #include <limits.h>

typedef signed char my_type;
typedef unsigned char my_unsigned_type;

#define CLK_TCK 100
#define WORD_LENGTH 100 
#define TRUE 1
#define FALSE 0
#define NONE -1
#define NONE2 -2

/* the tables of nodes and edges are statically allocated. Modify the 
   parameters tab_node_size and tab_edge_size before compilation if 
   necessary */
#define tab_node_size  12001
#define tab_edge_size 72000000
#define max_nb_value 100
#define pop(stack) stack[--stack ## _fill_pointer]
#define push(item, stack) stack[stack ## _fill_pointer++] = item
#define depth 1000
#define PASSIVE 0
#define ACTIVE 1

int *node_neibors[tab_node_size];
int node_value[tab_node_size];
int node_state[2*tab_node_size];
int *node_value_state[tab_node_size];
int node_nb_value[tab_node_size];
int node_nb_symmetric_value[tab_node_size];
int node_impact[tab_node_size];
int nb_neibors[tab_node_size];
int static_nb_neibors[tab_node_size];
int branching_node[tab_node_size];
int NODE_STACK[tab_node_size];
int NODE_STACK_fill_pointer=0;

int UNIT_ISET_STACK[tab_node_size];
int UNIT_ISET_STACK_fill_pointer=0;

int edge[tab_edge_size][2];
int symmetry[max_nb_value];

int NB_VALUE, NB_NODE, NB_EDGE, H;

int NB_UNIT=0, NB_BACK = 0, NB_BRANCHE=0;

int non_neibor[tab_node_size];
int *node_non_neibors[tab_node_size];
int nb_non_neibor[tab_node_size];

int matrice[tab_node_size][tab_node_size];

int FORMAT=1;

// const double CLK_TCK = 100.0;
int sPoint[tab_node_size];
int sN[tab_node_size];
int CANDIDATE_DEGREE_STACK[depth*tab_node_size];
int CANDIDATE_DEGREE_STACK_fill_pointer=0;
int nnb=0;
int degree_neibors[tab_node_size];
int degree_neibors_subgraph[tab_node_size];

my_type build_simple_graph_instance(char *input_file) {
  FILE* fp_in=fopen(input_file, "r");
  char ch, word2[WORD_LENGTH];
  int i, j, e, node1, node2, *neibors, neibor, redundant;
  if (fp_in == NULL) return FALSE;
  if (FORMAT==1) {
    fscanf(fp_in, "%c", &ch);
    while (ch!='p') {
      while (ch!='\n') fscanf(fp_in, "%c", &ch);  
      fscanf(fp_in, "%c", &ch);
    }
    fscanf(fp_in, "%s%d%d", word2, &NB_NODE, &NB_EDGE);
  }
  else    fscanf(fp_in, "%d%d",  &NB_NODE, &NB_EDGE);

  for(i=0; i<NB_EDGE; i++) {
    if (FORMAT==1)
      fscanf(fp_in, "%s%d%d", word2, &edge[i][0], &edge[i][1]);
    else fscanf(fp_in, "%d%d", &edge[i][0], &edge[i][1]);
    if (edge[i][0]==edge[i][1]) {
      printf("auto edge %d over %d\n", i--, NB_EDGE--);
    }
    else {
      if (edge[i][0]>edge[i][1]) {
	e=edge[i][1]; edge[i][1]=edge[i][0]; edge[i][0]=e;
      }
      nb_neibors[edge[i][0]]++;
      nb_neibors[edge[i][1]]++;
    }
  }
  fclose(fp_in);

  for(i=1; i<=NB_NODE; i++) 
    for(j=1; j<=NB_NODE; j++) {
      matrice[i][j]=FALSE;
      matrice[j][i]=FALSE;
    }

  for (i=1; i<=NB_NODE; i++) {
    static_nb_neibors[i]=nb_neibors[i];
    node_neibors[i]= (int *)malloc((nb_neibors[i]+1) * sizeof(int));
    node_neibors[i][nb_neibors[i]]=NONE;
    nb_neibors[i]=0;
    node_nb_value[i]=NB_VALUE;
    node_nb_symmetric_value[i]=NB_VALUE;
    node_state[i]=ACTIVE;
    node_value_state[i]= (int *)malloc(NB_VALUE * sizeof(int));
    for(j=0; j<NB_VALUE; j++)
      node_value_state[i][j]=ACTIVE;
  }
  for(i=0; i<NB_EDGE; i++) {
    node1=edge[i][0];    node2=edge[i][1]; 
    neibors=node_neibors[node1]; redundant=FALSE;
    for(j=0; j<nb_neibors[node1]; j++) 
      if (neibors[j]==node2) {
	printf("edge redundant %d \n", i);
	redundant=TRUE;
	break;
      }
    if (redundant==FALSE) {
      node_neibors[node1][nb_neibors[node1]++]=node2;
      node_neibors[node2][nb_neibors[node2]++]=node1;
      matrice[node1][node2]=TRUE;
      matrice[node2][node1]=TRUE;
    }
  }
  for (i=1; i<=NB_NODE; i++) {
    static_nb_neibors[i]=nb_neibors[i];
    node_neibors[i][nb_neibors[i]]=NONE;
  }
  return TRUE;
}

int CLIQUE_CANDIDATE_STACK_fill_pointer=0;
int CLIQUE_CANDIDATE_STACK[depth*tab_node_size];
int candidate_potentiel[depth*tab_node_size];
int candidate_nb_neibors[depth*tab_node_size];
int candidate_nb_noneibors[depth*tab_node_size];
int candidate_position[depth*tab_node_size];
int COLOR_STACK_fill_pointer=0;
int COLOR_STACK[max_nb_value];
int colorMark[max_nb_value];
int nodeMark[tab_node_size];
int candidate_state[tab_node_size];
int saved_candidate_color_nb[tab_node_size];
int node_nb_neibors[tab_node_size];
int ISET_CANDIDATE_STACK_fill_pointer=0;
int ISET_CANDIDATE_STACK[depth*tab_node_size];
int ISET_STACK_fill_pointer=0;
int ISET_STACK[depth*tab_node_size];
int ISETS_STACK_fill_pointer=0;
int ISETS_STACK[tab_node_size];
int nodeIsetMark[tab_node_size];
int iset_node_state[tab_node_size];

int node_nb_noneibors[tab_node_size];
int NONEIBOR_STACK[tab_node_size];
int NONEIBOR_STACK_fill_pointer=0;
int CLIQUE_STACK[tab_node_size];
int CLIQUE_STACK_fill_pointer=0;
int MAXCLIQUE_STACK[tab_node_size];
int MAXCLIQUE_STACK_fill_pointer=0;
int CLIQUES_STACK[3*tab_node_size];
int CLIQUES_STACK_fill_pointer=0;
int saved_node_value[tab_node_size];
int node_iset_no[tab_node_size];
int candidate_iset_no[depth*tab_node_size];
int candidate_ub[depth*tab_node_size];
int UB=-1, LB=-1, NB_COLOR=-1;

int saved_candidate_stack[tab_node_size];
int saved_noneibor_stack[tab_node_size];

int MAX_CLQ_SIZE=0;
int NB_BACK_CLIQUE=0;

int verifyClique(int debut) {
  int i, node, *neibors, neibor;

  for(node=1; node<=NB_NODE; node++)
    nodeMark[node]=0;

  for(i=debut; i<CLIQUE_STACK_fill_pointer; i++) {
    node=CLIQUE_STACK[i];
    if (nodeMark[node]!=i-debut) {
      printf("erreur clique in node %d\n", node);
      return FALSE;
    }
    neibors=node_neibors[node];
    for(neibor=*neibors; neibor!=NONE; neibor=*(++neibors))
      nodeMark[neibor]++;
  }
  return TRUE;
}

void sort_neibors_inc(int *neibors) {
  int *neibors1, *neibors2, neibor1, neibor2;
  neibors1=neibors;
  for(neibor1=*neibors1; neibor1!=NONE; neibor1=*(++neibors1)) {
    neibors2=neibors1+1;
    for(neibor2=*neibors2; neibor2!=NONE; neibor2=*(++neibors2)) {
      if (nb_neibors[neibor1]>nb_neibors[neibor2]) {
	*neibors1=neibor2;
	*neibors2=neibor1;
	neibor1=neibor2;
      }
    }
  }
}

void sort_neibors_dec(int *neibors) {
  int *neibors1, *neibors2, neibor1, neibor2;
  neibors1=neibors;
  for(neibor1=*neibors1; neibor1!=NONE; neibor1=*(++neibors1)) {
    neibors2=neibors1+1;
    for(neibor2=*neibors2; neibor2!=NONE; neibor2=*(++neibors2)) {
      if (nb_neibors[neibor1]<nb_neibors[neibor2]) {
	*neibors1=neibor2;
	*neibors2=neibor1;
	neibor1=neibor2;
      }
    }
  }
}

void sort_noneibors_dec(int *neibors) {
  int *neibors1, *neibors2, neibor1, neibor2;
  neibors1=neibors;
  for(neibor1=*neibors1; neibor1!=NONE; neibor1=*(++neibors1)) {
    neibors2=neibors1+1;
    for(neibor2=*neibors2; neibor2!=NONE; neibor2=*(++neibors2)) {
      if (nb_non_neibor[neibor1]<nb_non_neibor[neibor2]) {
	*neibors1=neibor2;
	*neibors2=neibor1;
	neibor1=neibor2;
      }
    }
  }
}

void sort_noneibors_inc(int *neibors) {
  int *neibors1, *neibors2, neibor1, neibor2;
  neibors1=neibors;
  for(neibor1=*neibors1; neibor1!=NONE; neibor1=*(++neibors1)) {
    neibors2=neibors1+1;
    for(neibor2=*neibors2; neibor2!=NONE; neibor2=*(++neibors2)) {
      if (nb_non_neibor[neibor1]>nb_non_neibor[neibor2]) {
	*neibors1=neibor2;
	*neibors2=neibor1;
	neibor1=neibor2;
      }
    }
  }
}

void build_complement_graph() {
  int node, node1, *neibors, neibor, nb;

  for (node=1; node<=NB_NODE; node++) 
    non_neibor[node]=TRUE;
  for (node=1; node<=NB_NODE; node++) {
    neibors=node_neibors[node]; nb=0;
    for(neibor=*neibors; neibor!=NONE; neibor=*(++neibors)) {
      non_neibor[neibor]=FALSE;
      nb++;
    }
    non_neibor[node]=FALSE;
    node_non_neibors[node]= (int *)malloc((NB_NODE-nb) * sizeof(int));
    nb=0;
    for (node1=1; node1<=NB_NODE; node1++) {
      if (non_neibor[node1]==TRUE) {
	node_non_neibors[node][nb++]=node1;
      }
      else non_neibor[node1]=TRUE;
    }
    node_non_neibors[node][nb]=NONE;
    nb_non_neibor[node]=nb;
    if (nb+static_nb_neibors[node] !=NB_NODE-1)
      printf("erreur graphe by complementation\n");
  }
  for (node=1; node<=NB_NODE; node++) {
    sort_noneibors_inc(node_non_neibors[node]);
    sort_neibors_dec(node_neibors[node]);
  }
}

void complement_graph() {
  int node, nb, *neibors;

  for (node=1; node<=NB_NODE; node++) {
    neibors=node_neibors[node];
    node_neibors[node]=node_non_neibors[node];
    node_non_neibors[node]=neibors;
    nb=nb_neibors[node];
    if (nb != static_nb_neibors[node])
      printf("erreur graphe nb neibor\n");
    nb_neibors[node]=nb_non_neibor[node];
    static_nb_neibors[node]=nb_non_neibor[node];
    nb_non_neibor[node]=nb;
  }
  
  for (node=1; node<=NB_NODE; node++) {
    sort_noneibors_inc(node_non_neibors[node]);
    sort_neibors_dec(node_neibors[node]);
    } 
}

void scanone(int argc, char *argv[], int i, int *varptr) {
  if (i>=argc || sscanf(argv[i],"%i",varptr)!=1){
    fprintf(stderr, "Bad argument %s\n", i<argc ? argv[i] : argv[argc-1]);
    exit(-1);
  }
}

int HELP_FLAG=FALSE;
char *INPUT_FILE;
int LBflag=TRUE, UBflag=TRUE;

void parse_parameters(int argc,char *argv[]) {
  int i, temp, j;
  if (argc<2)
    HELP_FLAG=TRUE;
  else 
    for (i=1;i < argc;i++) {
      if (strcmp(argv[i],"-nbColors") == 0) 
	scanone(argc,argv,++i,&NB_VALUE);
      else if (strcmp(argv[i],"-f") == 0)
	scanone(argc,argv,++i,&FORMAT);
      else if (strcmp(argv[i],"-lb") == 0)
	scanone(argc,argv,++i,&LBflag);
     else if (strcmp(argv[i],"-ub") == 0)
	scanone(argc,argv,++i,&UBflag);
      else if (strcmp(argv[i],"-help") == 0)
	HELP_FLAG=TRUE;
      else   
	  INPUT_FILE=argv[i];
    }
}

char* filename(char* input) {
  char c, *input1;
  int  nb, nb1;
  input1=input; nb=0;
  for(c=*input1; c!='\0'; c=*(input1+=1)) 
    if (c=='/') nb++;
  input1=input; nb1=0;
  for(c=*input1; c!='\0'; c=*(input1+=1)) {
    if (c=='/') nb1++;
    if (nb==nb1)
      return input1+1;
  }
  return input1;
}

void compute_candidate_nb_neibors() {
  int i,  *neibors, neibor, node;
  for(i=0; i<CLIQUE_CANDIDATE_STACK_fill_pointer; i++) {
    node=CLIQUE_CANDIDATE_STACK[i];
    neibors=node_neibors[node]; node_nb_neibors[node]=0;
    for(neibor=*neibors; neibor!=NONE; neibor=*(++neibors)) 
      if (node_state[neibor]==TRUE) {
	node_nb_neibors[node]++;
      }
  }
}

void compute_degree_neibors() {
  int i, *neibors, neibor, node;
  for(i=0; i<CLIQUE_CANDIDATE_STACK_fill_pointer; i++) {
	node=CLIQUE_CANDIDATE_STACK[i];
	neibors=node_neibors[node]; degree_neibors[node]=0;
    for(neibor=*neibors; neibor!=NONE; neibor=*(++neibors))
	  degree_neibors[node]=degree_neibors[node]+node_nb_neibors[neibor];
  }
} 

#define debutGraph() CLIQUE_CANDIDATE_STACK_fill_pointer-\
candidate_potentiel[CLIQUE_CANDIDATE_STACK_fill_pointer-1]
int ISET_NB=0;
int ISETS_SIZE[tab_node_size];
int isetCandidateStates[tab_node_size][tab_node_size];
int available_iset_nb[tab_node_size];
int iset_nb_candidates[tab_node_size];
int ISETS[tab_node_size][tab_node_size];
int DENSITY, NB_ISETS_TEST=0;
double RATIO;

#define NO_CONFLICT -2
int iset_state[tab_node_size];
int REDUCED_ISET_STACK[tab_node_size];
int REDUCED_ISET_STACK_fill_pointer=0;
int ENLARGED_ISET_STACK[tab_node_size];
int ENLARGED_ISET_STACK_fill_pointer=0;
int UNITISET_STACK[tab_node_size];
int UNITISET_STACK_fill_pointer=0;
int MY_UNITISET_STACK[tab_node_size];
int MY_UNITISET_STACK_fill_pointer=0;
int node_reason[tab_node_size];
#define NO_REASON -3
int iset_involved[tab_node_size];
int REASON_STACK[tab_node_size];
int REASON_STACK_fill_pointer=0;
int *CONFLICT_ISETS[5*tab_node_size];
int CONFLICT_ISET_STACK[tab_node_size];
int CONFLICT_ISET_STACK_fill_pointer=0;
int ADDED_NB_NODE;
//int conflict_iset[tab_node_size];
int PASSIVE_ISET_STACK[tab_node_size];
int PASSIVE_ISET_STACK_fill_pointer=0;

int TWOISET_STACK[tab_node_size];
int TWOISET_STACK_fill_pointer=0;
int MY_TWOISET_STACK[tab_node_size];
int MY_TWOISET_STACK_fill_pointer=0;
int FLAG=0;
int TWOREASON=0;
int STATIC_ISET_SIZE[tab_node_size];
int STATIC_ISET_SIZE_fill_pointer=0;

void assign_node_value(int node, int value, int reason) {
  node_value[node]=value;
  node_state[node]=PASSIVE;
  push(node, NODE_STACK);
  node_reason[node]=reason;
}

int fix_node_for_iset(int node, int iset) {
  int *noneibors, noneibor, my_iset;
  iset_state[iset]=PASSIVE;
  push(iset, PASSIVE_ISET_STACK);
  assign_node_value(node, TRUE, iset);
  noneibors=node_non_neibors[node]; 
  for(noneibor=*noneibors; noneibor!=NONE; noneibor=*(++noneibors)) 
    if (node_state[noneibor]==ACTIVE) {
      my_iset=node_iset_no[noneibor];
      assign_node_value(noneibor, FALSE, iset);
      if (iset_state[my_iset]==ACTIVE) {
	ISETS_SIZE[my_iset]--;
	push(my_iset, REDUCED_ISET_STACK);
	if (ISETS_SIZE[my_iset]==1)
	  push(my_iset, MY_UNITISET_STACK);
	else if (ISETS_SIZE[my_iset]==2)
	  push(my_iset, MY_TWOISET_STACK);
	else if (ISETS_SIZE[my_iset]==0)
	  return my_iset;
      }
    }
  return NO_CONFLICT;
}

int fix_addedNode_for_iset(int node, int iset) {
  int *isets, c_iset;
  iset_state[iset]=PASSIVE;
  push(iset, PASSIVE_ISET_STACK);
  assign_node_value(node, FALSE, iset);
  isets=CONFLICT_ISETS[node]; 
  for(c_iset=*isets; c_iset!=NONE; c_iset=*(++isets))
    if (iset_state[c_iset]==ACTIVE) {
      ISETS_SIZE[c_iset]--;
      push(c_iset, REDUCED_ISET_STACK);
      if (ISETS_SIZE[c_iset]==1)
	    push(c_iset, MY_UNITISET_STACK);
	  else if (ISETS_SIZE[c_iset]==1 && iset_state[c_iset]==PASSIVE)
	    printf("%d\n", c_iset);  
	  else if (ISETS_SIZE[c_iset]==2)
	    push(c_iset, MY_TWOISET_STACK);
      else if (ISETS_SIZE[c_iset]==0)
	    return c_iset;
    }
  return NO_CONFLICT;
}

int fix_unitIset(int iset) {
  int node, *nodes;

  nodes=ISETS[iset];
  for(node=*nodes; node!=NONE; node=*(++nodes)) 
    if (node_state[node]==ACTIVE) {
      if (node>NB_NODE)
	return fix_addedNode_for_iset(node, iset);
      else
	return fix_node_for_iset(node, iset);
    }
  printf("erreur unitIset qqn %d\n", FLAG);
  return NO_CONFLICT;
}

int TESTED_NODE_STACK[tab_node_size];
int TESTED_NODE_STACK_fill_pointer=0;
int node_tested_state[tab_node_size];
int UNITISET_IN_TWOISET_STACK[tab_node_size];
int UNITISET_IN_TWOISET_STACK_fill_pointer=0;

int unitForTwoIsetProcess() {
  int i, iset, j, my_iset;
  for(i=0; i<UNITISET_IN_TWOISET_STACK_fill_pointer; i++) {
    iset=UNITISET_IN_TWOISET_STACK[i];
    if (iset_state[iset]==ACTIVE && ISETS_SIZE[iset]==1) {
      MY_UNITISET_STACK_fill_pointer=0; FLAG=10;
      if ((my_iset=fix_unitIset(iset))!=NO_CONFLICT)
	    return my_iset;
      else 
	    for(j=0; j<MY_UNITISET_STACK_fill_pointer; j++) {
	      iset=MY_UNITISET_STACK[j]; FLAG=12;
	      if (iset_state[iset]==ACTIVE)
	        if ((my_iset=fix_unitIset(iset))!=NO_CONFLICT)
	          return my_iset;
	    }
    }
  }
  MY_UNITISET_STACK_fill_pointer=0;
  MY_TWOISET_STACK_fill_pointer=0;
  return NO_CONFLICT;
}

void lookback_for_maxsatz(int iset) {
  int i, *nodes, node, reason_iset;
  if(TWOREASON!=1)
    REASON_STACK_fill_pointer=0;
  push(iset, REASON_STACK); iset_involved[iset]=TRUE;
  for(i=0; i<REASON_STACK_fill_pointer; i++) {
    iset=REASON_STACK[i];
    nodes=ISETS[iset];
    for(node=*nodes; node!=NONE; node=*(++nodes))
      if (node_value[node]==FALSE && 
	  node_reason[node] !=NO_REASON && 
	  iset_involved[node_reason[node]]==FALSE) {
	reason_iset=node_reason[node];
	push(reason_iset, REASON_STACK);
	node_reason[node]=NO_REASON;
	iset_involved[reason_iset]=TRUE;
      }
  }
  for(i=0; i<REASON_STACK_fill_pointer; i++) 
    iset_involved[REASON_STACK[i]]=FALSE;
  TWOREASON=0;    
}

void reset_context_for_maxsatz(int saved_node_stack_fill_pointer,
			       int saved_passive_iset_stack_fill_pointer,
			       int saved_reduced_iset_stack_fill_pointer,
			       int saved_unitiset_stack_fill_pointer) {
  int i, node;

  for(i=saved_node_stack_fill_pointer; i<NODE_STACK_fill_pointer; i++) {
    node=NODE_STACK[i];
    node_state[node]=ACTIVE;
    node_reason[node]=NO_REASON;
  }
  NODE_STACK_fill_pointer=saved_node_stack_fill_pointer;
  for(i=saved_passive_iset_stack_fill_pointer; 
      i<PASSIVE_ISET_STACK_fill_pointer; i++)
    iset_state[PASSIVE_ISET_STACK[i]]=ACTIVE;
  PASSIVE_ISET_STACK_fill_pointer=saved_passive_iset_stack_fill_pointer;
  for(i=saved_reduced_iset_stack_fill_pointer; 
      i<REDUCED_ISET_STACK_fill_pointer; i++)
    ISETS_SIZE[REDUCED_ISET_STACK[i]]++;
  REDUCED_ISET_STACK_fill_pointer=saved_reduced_iset_stack_fill_pointer;
  UNITISET_STACK_fill_pointer=saved_unitiset_stack_fill_pointer;
  MY_UNITISET_STACK_fill_pointer=0;
  MY_TWOISET_STACK_fill_pointer=0;
}

int arrange_iset_stack() {
  int i;
  UNITISET_IN_TWOISET_STACK_fill_pointer=0;
  for(i=0; i<MY_UNITISET_STACK_fill_pointer; i++)
    push(MY_UNITISET_STACK[i], UNITISET_IN_TWOISET_STACK);
  MY_UNITISET_STACK_fill_pointer=0;
  if(UNITISET_IN_TWOISET_STACK_fill_pointer>0)
    return 1;
  else return 0;
}

int my_unitIsetProcess() {
  int iset, j, my_iset;
  for(j=0; j<MY_UNITISET_STACK_fill_pointer; j++) {
    iset=MY_UNITISET_STACK[j];
    if(ISETS_SIZE[iset]==1) {
      if (iset_state[iset] ==PASSIVE)
            printf("%d %d %d\n", iset, ISETS_SIZE[iset], iset_state[iset]);
        //~ printf("bizzar iset state %d %d\n", j, FLAG);
      if ((my_iset=fix_unitIset(iset))!=NO_CONFLICT)
        return my_iset;
	}   
  }   
  return NO_CONFLICT;
}

int fix_twoIset(int iset) {
  int node, *nodes, my_iset, nb_node,
    saved_unitiset_stack_fill_pointer,saved_twoiset_stack_fill_pointer,
    saved_node_stack_fill_pointer, saved_passive_iset_stack_fill_pointer,
    saved_reduced_iset_stack_fill_pointer;
  saved_passive_iset_stack_fill_pointer=PASSIVE_ISET_STACK_fill_pointer;
  saved_reduced_iset_stack_fill_pointer=REDUCED_ISET_STACK_fill_pointer;
  saved_node_stack_fill_pointer=NODE_STACK_fill_pointer;
  saved_unitiset_stack_fill_pointer=UNITISET_STACK_fill_pointer;  
  nodes=ISETS[iset]; nb_node=0;
  for(node=*nodes; node!=NONE; node=*(++nodes)) {
    if (node_state[node]==ACTIVE) { 
      MY_UNITISET_STACK_fill_pointer=0;
      MY_TWOISET_STACK_fill_pointer=0;
      if (node>NB_NODE) { FLAG=28;
        MY_UNITISET_STACK_fill_pointer=0;
	if((my_iset=fix_addedNode_for_iset(node, iset))!=NO_CONFLICT
	   || (my_iset=my_unitIsetProcess())!=NO_CONFLICT) {
	  if(nb_node==0) {
	    nb_node=1;
	    lookback_for_maxsatz(my_iset);   
	    reset_context_for_maxsatz(saved_node_stack_fill_pointer,
				      saved_passive_iset_stack_fill_pointer,
				      saved_reduced_iset_stack_fill_pointer,
				      saved_unitiset_stack_fill_pointer);
	  }
	  else if(nb_node==1) {
	    TWOREASON=1;  
	    return my_iset;
	  }
	}
	else {
	  reset_context_for_maxsatz(saved_node_stack_fill_pointer,
				    saved_passive_iset_stack_fill_pointer,
				    saved_reduced_iset_stack_fill_pointer,
				    saved_unitiset_stack_fill_pointer);	       	
	  return NO_CONFLICT;
	}
      }
      else { FLAG=23;
	if((my_iset=fix_node_for_iset(node, iset))!=NO_CONFLICT 
	   || (my_iset=my_unitIsetProcess())!=NO_CONFLICT) {
	  if(nb_node==0) {
	    nb_node=1;
	    lookback_for_maxsatz(my_iset);   
	    reset_context_for_maxsatz(saved_node_stack_fill_pointer,
				      saved_passive_iset_stack_fill_pointer,
				      saved_reduced_iset_stack_fill_pointer,
				      saved_unitiset_stack_fill_pointer);
	  }
	  else if(nb_node==1) {
	    TWOREASON=1;
	    return my_iset;
	  }
	}
	else {
	  reset_context_for_maxsatz(saved_node_stack_fill_pointer,
				    saved_passive_iset_stack_fill_pointer,
				    saved_reduced_iset_stack_fill_pointer,
				    saved_unitiset_stack_fill_pointer);	       		       
	  return NO_CONFLICT;
	}
      }
    }  
  }
  printf("erreur twoIset a\n");
  return NO_CONFLICT;
}

int unitIsetProcess_test() {
  int i, iset, j, my_iset;
  for(i=0; i<UNITISET_STACK_fill_pointer; i++) {
    iset=UNITISET_STACK[i];
    if (iset_state[iset]==ACTIVE && ISETS_SIZE[iset]==1) {
      MY_UNITISET_STACK_fill_pointer=0;
      MY_TWOISET_STACK_fill_pointer=0;
      if ((my_iset=fix_unitIset(iset))!=NO_CONFLICT)
	    return my_iset;
      else 
	    for(j=0; j<MY_UNITISET_STACK_fill_pointer; j++) {
	      iset=MY_UNITISET_STACK[j];
	        if (iset_state[iset]==ACTIVE) {
			  MY_TWOISET_STACK_fill_pointer=0; 
	          if ((my_iset=fix_unitIset(iset))!=NO_CONFLICT)
	            return my_iset;
	        }
	    }
	  //~ if(MY_TWOISET_STACK_fill_pointer>0)
        //~ if((my_iset=twoIsetProcess())!=NO_CONFLICT)
          //~ return my_iset; 
    }
  }
  MY_UNITISET_STACK_fill_pointer=0;
  //~ MY_TWOISET_STACK_fill_pointer=0;
  return NO_CONFLICT;
}


int unitIsetProcess() {
  int i, iset, j, my_iset;
  for(i=0; i<UNITISET_STACK_fill_pointer; i++) {
    iset=UNITISET_STACK[i];
    if (iset_state[iset]==ACTIVE && ISETS_SIZE[iset]==1) {
      MY_UNITISET_STACK_fill_pointer=0;
      MY_TWOISET_STACK_fill_pointer=0;
      if ((my_iset=fix_unitIset(iset))!=NO_CONFLICT)
	    return my_iset;
      else 
	    for(j=0; j<MY_UNITISET_STACK_fill_pointer; j++) {
	      iset=MY_UNITISET_STACK[j];
	        if (iset_state[iset]==ACTIVE) {
			  MY_TWOISET_STACK_fill_pointer=0; 
	          if ((my_iset=fix_unitIset(iset))!=NO_CONFLICT)
	            return my_iset;
	        }
	    }
	  if(MY_TWOISET_STACK_fill_pointer>0)
        if((my_iset=twoIsetProcess())!=NO_CONFLICT)
          return my_iset; 
    }
  }
  MY_UNITISET_STACK_fill_pointer=0;
  MY_TWOISET_STACK_fill_pointer=0;
  return NO_CONFLICT;
}
int DIVIDE=0;
int TOTAL=0;

int twoIsetProcess() {
  int i, iset, my_iset;
  TOTAL++;
  TWOISET_STACK_fill_pointer=0;
  for(i=0; i<MY_TWOISET_STACK_fill_pointer; i++)
    push(MY_TWOISET_STACK[i], TWOISET_STACK);
  for(i=0; i<TWOISET_STACK_fill_pointer; i++) {
    iset=TWOISET_STACK[i];
    if (iset_state[iset]==ACTIVE && ISETS_SIZE[iset]==2)
      if ((my_iset=fix_twoIset(iset))!=NO_CONFLICT) {
	    DIVIDE++;
	    return my_iset;
	  }
  }
  MY_UNITISET_STACK_fill_pointer=0;
  MY_TWOISET_STACK_fill_pointer=0;
  return NO_CONFLICT;
}

int INVOLVED_ISET_STACK[tab_node_size];
int INVOLVED_ISET_STACK_fill_pointer=0;

void enlarge_involved_iset() {
  int i, iset;  
  CONFLICT_ISETS[ADDED_NB_NODE]=
    &CONFLICT_ISET_STACK[CONFLICT_ISET_STACK_fill_pointer];
  node_state[ADDED_NB_NODE]=ACTIVE;
  for(i=0; i<REASON_STACK_fill_pointer; i++) {
    iset=REASON_STACK[i];
    if (iset_involved[iset]==FALSE) {
      iset_involved[iset]=TRUE;
      if (ISETS[iset][ISETS_SIZE[iset]] != NONE)
        printf("erreur conflict iset\n");
      ISETS[iset][ISETS_SIZE[iset]++]=ADDED_NB_NODE;
      ISETS[iset][ISETS_SIZE[iset]]=NONE;
      push(iset, CONFLICT_ISET_STACK);
      push(iset, ENLARGED_ISET_STACK);
    }
  }
  push(NONE, CONFLICT_ISET_STACK);
  ADDED_NB_NODE++;
  for(i=0; i<REASON_STACK_fill_pointer; i++)	
    iset_involved[REASON_STACK[i]]=FALSE;
} 

void enlarge_stored_involved_isets() {
  int i, iset;
  CONFLICT_ISETS[ADDED_NB_NODE]=
    &CONFLICT_ISET_STACK[CONFLICT_ISET_STACK_fill_pointer];
  node_state[ADDED_NB_NODE]=ACTIVE;
  for(i=0; i<INVOLVED_ISET_STACK_fill_pointer; i++) {
    iset=INVOLVED_ISET_STACK[i];
    if (iset_involved[iset]==FALSE) {
      iset_involved[iset]=TRUE;
      if (ISETS[iset][ISETS_SIZE[iset]] != NONE)
	    printf("erreur conflict iset\n");
      ISETS[iset][ISETS_SIZE[iset]++]=ADDED_NB_NODE;
      ISETS[iset][ISETS_SIZE[iset]]=NONE;
      push(iset, CONFLICT_ISET_STACK);
      push(iset, ENLARGED_ISET_STACK);
    }
  }
  push(NONE, CONFLICT_ISET_STACK);
  ADDED_NB_NODE++;
  for(i=0; i<INVOLVED_ISET_STACK_fill_pointer; i++)
    iset_involved[INVOLVED_ISET_STACK[i]]=FALSE;
  INVOLVED_ISET_STACK_fill_pointer=0;
}

void reset_context_for_maxsatz_no(int saved_node_stack_fill_pointer,
				  int saved_passive_iset_stack_fill_pointer,
				  int saved_reduced_iset_stack_fill_pointer,
				  int saved_unitiset_stack_fill_pointer) {
  int i, node;

  for(i=saved_node_stack_fill_pointer; i<NODE_STACK_fill_pointer; i++) {
    node=NODE_STACK[i];
    node_state[node]=ACTIVE;
    node_reason[node]=NO_REASON;
    if (node_value[node]==TRUE && node_tested_state[node]==FALSE) {
      node_tested_state[node]=TRUE; // no need to re-test at this point
      push(node, TESTED_NODE_STACK);
    }
  }
  NODE_STACK_fill_pointer=saved_node_stack_fill_pointer;
  for(i=saved_passive_iset_stack_fill_pointer; 
      i<PASSIVE_ISET_STACK_fill_pointer; i++)
    iset_state[PASSIVE_ISET_STACK[i]]=ACTIVE;
  PASSIVE_ISET_STACK_fill_pointer=saved_passive_iset_stack_fill_pointer;
  for(i=saved_reduced_iset_stack_fill_pointer; 
      i<REDUCED_ISET_STACK_fill_pointer; i++)
    ISETS_SIZE[REDUCED_ISET_STACK[i]]++;
  REDUCED_ISET_STACK_fill_pointer=saved_reduced_iset_stack_fill_pointer;
  UNITISET_STACK_fill_pointer=saved_unitiset_stack_fill_pointer;
  MY_UNITISET_STACK_fill_pointer=0;
  MY_TWOISET_STACK_fill_pointer=0;
}

void reset_enlarged_isets() {
  int i, iset;
  for(i=0; i<ENLARGED_ISET_STACK_fill_pointer; i++) {
    iset=ENLARGED_ISET_STACK[i];
    iset_state[iset]=ACTIVE;
    ISETS_SIZE[iset]--;
    ISETS[iset][ISETS_SIZE[iset]]=NONE;
  }
    
  ENLARGED_ISET_STACK_fill_pointer=0;

  for(i=0; i<TESTED_NODE_STACK_fill_pointer; i++)
    node_tested_state[TESTED_NODE_STACK[i]]=FALSE;
  TESTED_NODE_STACK_fill_pointer=0;
}

int LAST_NO_CONFLICT_STACK[tab_node_size];
int LAST_NO_CONFLICT_STACK_fill_pointer=0;

int test_node(int node, int iset, int flag) {
  int my_iset, saved_unitiset_stack_fill_pointer,
    saved_node_stack_fill_pointer, saved_passive_iset_stack_fill_pointer,
    saved_reduced_iset_stack_fill_pointer;
  saved_unitiset_stack_fill_pointer=UNITISET_STACK_fill_pointer;
  saved_node_stack_fill_pointer=NODE_STACK_fill_pointer;
  saved_passive_iset_stack_fill_pointer=PASSIVE_ISET_STACK_fill_pointer;
  saved_reduced_iset_stack_fill_pointer=REDUCED_ISET_STACK_fill_pointer;
  MY_UNITISET_STACK_fill_pointer=0;
  MY_TWOISET_STACK_fill_pointer=0; 
  if ((my_iset=unitIsetProcess_test())!=NO_CONFLICT)
    printf("bizzar.....\n");
  MY_TWOISET_STACK_fill_pointer=0; 
  if ((my_iset=fix_node_for_iset(node, iset)) != NO_CONFLICT ||
      (my_iset=my_unitIsetProcess()) !=  NO_CONFLICT 
      || ((flag == 1) && 
	  ((my_iset=twoIsetProcess()) != NO_CONFLICT))) {
    lookback_for_maxsatz(my_iset);
    reset_context_for_maxsatz(saved_node_stack_fill_pointer,
			      saved_passive_iset_stack_fill_pointer,
			      saved_reduced_iset_stack_fill_pointer,
			      saved_unitiset_stack_fill_pointer);
    return my_iset;
  }
  else {
    if(flag == 0) push(iset, LAST_NO_CONFLICT_STACK);
    reset_context_for_maxsatz_no(saved_node_stack_fill_pointer,
				 saved_passive_iset_stack_fill_pointer,
				 saved_reduced_iset_stack_fill_pointer,
				 saved_unitiset_stack_fill_pointer);
    return NO_CONFLICT;
  }
}

void store_involved_isets() {
  int i, iset;
  for(i=0; i<REASON_STACK_fill_pointer; i++) {
    iset=REASON_STACK[i];
    push(iset, INVOLVED_ISET_STACK);
  }
}

int test_last_node(int nb_conflict, int nb_extra_isets) {
  int iset, *nodes, node, no_conflict, test_flag, k, saved_size, last_node;
  for(k=0; k<LAST_NO_CONFLICT_STACK_fill_pointer; k++) {
    iset=LAST_NO_CONFLICT_STACK[k];
    if (iset_state[iset]==ACTIVE) {
      nodes=ISETS[iset]; test_flag=TRUE; 
      for(node=*nodes; node!=NONE; node=*(++nodes)) {
	if (node>NB_NODE || node_tested_state[node]==TRUE) {
	  test_flag=FALSE;
	  break;
	}
      }
      if (test_flag==TRUE) {
	nodes=ISETS[iset]; no_conflict=FALSE; 
	INVOLVED_ISET_STACK_fill_pointer=0;FLAG=18;
	for(node=*nodes; node!=NONE; node=*(++nodes)) {
	  if (node_tested_state[node]==TRUE ||
	      test_node(node, iset, 1)==NO_CONFLICT) {
	    no_conflict=TRUE;
	    break;
	  }
	  else store_involved_isets();
	}
	if (no_conflict==FALSE) { 
	  saved_size=ISETS_SIZE[iset];
	  enlarge_stored_involved_isets();
	  if (saved_size+1 != ISETS_SIZE[iset])
	    printf("erreur iset involved...%d %d\n", 
		   saved_size, ISETS_SIZE[iset]);
	  nb_conflict++;
	  if (nb_extra_isets<=nb_conflict) {
	    LAST_NO_CONFLICT_STACK_fill_pointer=0;  
	    return nb_conflict;
	  }
	}
      }
    }
  }
  LAST_NO_CONFLICT_STACK_fill_pointer=0;
  return nb_conflict;
}

int maxsatz_lookahead_by_fl(int nb_conflict, int nb_extra_isets) {
  int iset, *nodes, node, no_conflict, test_flag, k, saved_size, last_node, i;
  //  if (NB_BACK_CLIQUE==194)
  //   printf("sjdfh");
  for(k=2; k<=5; k++) 
    //for(i=0; i<=ISET_NB-nb_extra_isets+nb_conflict; i++) {
   for(iset=ISET_NB-1; iset>=nb_extra_isets-nb_conflict; iset--) {
     if (iset_state[iset]==ACTIVE && ISETS_SIZE[iset]==k) {
      nodes=ISETS[iset]; test_flag=TRUE; 
      for(node=*nodes; node!=NONE; node=*(++nodes)) {
	//	if(i==k-1) last_node=node;
	if (node>NB_NODE || node_tested_state[node]==TRUE) {
	  test_flag=FALSE;
	  break;
	}
      }
      if (test_flag==TRUE) {
 	nodes=ISETS[iset]; no_conflict=FALSE;
	INVOLVED_ISET_STACK_fill_pointer=0;
	for(node=*nodes; node!=NONE; node=*(++nodes)) {
	  if (node_tested_state[node]==TRUE ||
	      test_node(node, iset, 0)==NO_CONFLICT) {
	    no_conflict=TRUE;
	    break;
	  }
	  else store_involved_isets();
	}
	if (no_conflict==FALSE) { 
	  saved_size=ISETS_SIZE[iset];
	  enlarge_stored_involved_isets();
	  if (saved_size+1 != ISETS_SIZE[iset])
	    //printf("erreur iset involved...%d %d\n", DIVIDE, REASON_STACK_fill_pointer);
	    printf("erreur iset involved...%d %d\n", saved_size, ISETS_SIZE[iset]);
	  nb_conflict++;
	  if (nb_extra_isets<=nb_conflict) {
	    LAST_NO_CONFLICT_STACK_fill_pointer=0;
	    return nb_conflict;
	  }
	}
      }
    }
  }
  if(LAST_NO_CONFLICT_STACK_fill_pointer>0)
    nb_conflict=test_last_node(nb_conflict, nb_extra_isets);
  return nb_conflict;
}

int test_node_for_failed_nodes(int node, int iset) {
  int my_iset, saved_unitiset_stack_fill_pointer, 
    saved_node_stack_fill_pointer, saved_passive_iset_stack_fill_pointer,
    saved_reduced_iset_stack_fill_pointer;

  saved_unitiset_stack_fill_pointer=UNITISET_STACK_fill_pointer;
  saved_node_stack_fill_pointer=NODE_STACK_fill_pointer;
  saved_passive_iset_stack_fill_pointer=PASSIVE_ISET_STACK_fill_pointer;
  saved_reduced_iset_stack_fill_pointer=REDUCED_ISET_STACK_fill_pointer;
  MY_UNITISET_STACK_fill_pointer=0;
  MY_TWOISET_STACK_fill_pointer=0; FLAG=12;
  if ((my_iset=fix_node_for_iset(node, iset)) == NO_CONFLICT) 
    my_iset=my_unitIsetProcess();
  reset_context_for_maxsatz(saved_node_stack_fill_pointer,
			    saved_passive_iset_stack_fill_pointer,
			    saved_reduced_iset_stack_fill_pointer,
			    saved_unitiset_stack_fill_pointer);
  return my_iset;
}

void check_consistency() {
  int iset, node, *nodes, nb_a, nb_p, nb, nb_passive_nodes=0;

  nb_p=0;
  for(iset=0; iset<ISET_NB; iset++) {
    if (iset_involved[iset] !=FALSE)
      printf("erreur involved... ");
    if (iset_state[iset]==ACTIVE) {
      nodes=ISETS[iset]; nb_a=0; 
      for(node=*nodes; node!=NONE; node=*(++nodes)) {
	if (node_state[node]==ACTIVE) 
	  nb_a++;
	else if (node<=NB_NODE)
	  nb_passive_nodes++;
      }
      if (ISETS_SIZE[iset]!=nb_a)
	printf("erreur nb_a");
    }
    else {
      nb_p++;
      nodes=ISETS[iset]; nb_a=0; nb=0;
      for(node=*nodes; node!=NONE; node=*(++nodes)) {
	if (node_state[node]!=ACTIVE && node<=NB_NODE)
	  nb_passive_nodes++;
	if (node_state[node]==ACTIVE) 
	  printf("erreur active...");
	else if (node<=NB_NODE && node_value[node]==TRUE)
	  nb_a++;
	else if (node>NB_NODE)
	  nb++;
      }
      if (nb_a==0 && nb==0)
	printf("erreur SAT...");
    }
  }
  // if (nb_p != REDUCED_ISET_STACK_fill_pointer)
  //  printf("erreur nb_p %d %d\n", nb_p, REDUCED_ISET_STACK_fill_pointer);
  for(node=NB_NODE+1; node<ADDED_NB_NODE; node++)
    if (node_state[node]==PASSIVE)
      nb_passive_nodes++;
  if (nb_passive_nodes != NODE_STACK_fill_pointer)
    printf("erreur active node...");
  if (nb_p != PASSIVE_ISET_STACK_fill_pointer)
    printf("erreur nb_p %d %d\n", nb_p, PASSIVE_ISET_STACK_fill_pointer);
}

int test_by_eliminate_failed_nodes() {
  int node, my_iset, *nodes, saved_unitiset_stack_fill_pointer,
    saved_node_stack_fill_pointer, saved_passive_iset_stack_fill_pointer,
    saved_reduced_iset_stack_fill_pointer, conflict;
  // return TRUE;
  saved_unitiset_stack_fill_pointer=UNITISET_STACK_fill_pointer;
  saved_node_stack_fill_pointer=NODE_STACK_fill_pointer;
  saved_passive_iset_stack_fill_pointer=PASSIVE_ISET_STACK_fill_pointer;
  saved_reduced_iset_stack_fill_pointer=REDUCED_ISET_STACK_fill_pointer;
  //for(my_iset=ISET_NB-1; my_iset>=0; my_iset--) {
  for(my_iset=0; my_iset<ISET_NB; my_iset++) {
    if (iset_state[my_iset]==ACTIVE) {
      //  check_consistency();
      nodes=ISETS[my_iset]; conflict=FALSE; 	 
      MY_UNITISET_STACK_fill_pointer=0;
      MY_TWOISET_STACK_fill_pointer=0;
      for(node=*nodes; node!=NONE; node=*(++nodes)) {
	    if (node<=NB_NODE && node_state[node]==ACTIVE && 
	        test_node_for_failed_nodes(node, my_iset)!=NO_CONFLICT) {
	      MY_UNITISET_STACK_fill_pointer=0;
	      MY_TWOISET_STACK_fill_pointer=0;FLAG=6;
	      assign_node_value(node, FALSE, NO_REASON);
	      ISETS_SIZE[my_iset]--;
	      push(my_iset, REDUCED_ISET_STACK);
	      if (ISETS_SIZE[my_iset]==1) {
	        push(my_iset, MY_UNITISET_STACK);
	        break;
	      }
	      else if (ISETS_SIZE[my_iset]==0) {
	        conflict=TRUE;
	        break;
	      }
	      //~ else if (ISETS_SIZE[my_iset]==2) {
		    //~ push(my_iset, MY_TWOISET_STACK);
		    //~ break;
		  //~ }
	    }
      }
      if (conflict==TRUE) break;
      else if (MY_UNITISET_STACK_fill_pointer>0 &&
               //~ MY_TWOISET_STACK_fill_pointer>0 &&
	           my_unitIsetProcess() != NO_CONFLICT) {
	    conflict=TRUE;
	    break;
      }
    }
  }
  reset_context_for_maxsatz(saved_node_stack_fill_pointer,
			    saved_passive_iset_stack_fill_pointer,
			    saved_reduced_iset_stack_fill_pointer,
			    saved_unitiset_stack_fill_pointer);
  if (conflict==TRUE)
    return NONE;
  else
    return TRUE;
}

int NB1=0;

int maxsatz(int clq_size) {
  int i, nb_conflict=0, iset, nb=0, nb_node=0,
    saved_unitiset_stack_fill_pointer, nb_extra_isets, max_size,
    saved_node_stack_fill_pointer, saved_passive_iset_stack_fill_pointer,
    saved_reduced_iset_stack_fill_pointer;
  // return TRUE;
  if (clq_size <=0)
    return TRUE;
  UNITISET_STACK_fill_pointer=0; nb_extra_isets=ISET_NB-clq_size;
  max_size=0; STATIC_ISET_SIZE_fill_pointer=0;
  //~ for(i=ISET_NB-1; i>=0; i--) {
  for(i=0; i<ISET_NB; i++) {
	push(ISETS_SIZE[i], STATIC_ISET_SIZE);  	  
    if (max_size<ISETS_SIZE[i])
      max_size=ISETS_SIZE[i];
    iset_state[i]=ACTIVE;
    if (ISETS_SIZE[i]==1)
      push(i, UNITISET_STACK);
  }
      //~ else if  (ISETS_SIZE[i]==2)
      //~ push(i, MY_TWOISET_STACK);
  // if (nb_node != candidate_potentiel[CLIQUE_CANDIDATE_STACK_fill_pointer-1])
  // printf("erreur isets_size\n");
  // printf("%d %d %d %d\n", 
  //	  ISET_NB, clq_size, UNITISET_STACK_fill_pointer, nb);
  
  // if (UNITISET_STACK_fill_pointer/2+nb/5<nb_extra_isets)
  //  return TRUE;
  ADDED_NB_NODE=NB_NODE+1;
  CONFLICT_ISET_STACK_fill_pointer=0;
  saved_unitiset_stack_fill_pointer=UNITISET_STACK_fill_pointer;
  NODE_STACK_fill_pointer=0; saved_node_stack_fill_pointer=0;
  PASSIVE_ISET_STACK_fill_pointer=0;
  saved_passive_iset_stack_fill_pointer=0;
  REDUCED_ISET_STACK_fill_pointer=0;
  saved_reduced_iset_stack_fill_pointer=0;
  ENLARGED_ISET_STACK_fill_pointer=0;
  MY_UNITISET_STACK_fill_pointer=0;
  MY_TWOISET_STACK_fill_pointer=0;
  while ((iset=unitIsetProcess())!=NO_CONFLICT) { 
         //~ || (iset=twoIsetProcess())!=NO_CONFLICT) {
    lookback_for_maxsatz(iset);
    reset_context_for_maxsatz(saved_node_stack_fill_pointer,
			      saved_passive_iset_stack_fill_pointer,
			      saved_reduced_iset_stack_fill_pointer,
			      saved_unitiset_stack_fill_pointer);
    enlarge_involved_iset();
    nb_conflict++;
    if (nb_extra_isets<=nb_conflict)
      break;
  }
  reset_context_for_maxsatz_no(saved_node_stack_fill_pointer,
			       saved_passive_iset_stack_fill_pointer,
			       saved_reduced_iset_stack_fill_pointer,
			       saved_unitiset_stack_fill_pointer);
  if (nb_extra_isets>nb_conflict) 
    nb_conflict=maxsatz_lookahead_by_fl(nb_conflict, nb_extra_isets);
    
  // for(i=0; i<ISET_NB; i++) 
  //  nb_node -= ISETS_SIZE[i];
  // if (nb_node != 0)
  //  printf("erreur isets_size -\n");
  
  if (nb_conflict != ADDED_NB_NODE-NB_NODE-1)
    printf("erreur nb conflict %d %d...\n", nb_conflict,ADDED_NB_NODE-NB_NODE-1);
  if (nb_extra_isets<=nb_conflict) {
    reset_enlarged_isets();
    return NONE;
  }
  if (nb_extra_isets==nb_conflict+1 && 
      test_by_eliminate_failed_nodes()==NONE) {
    reset_enlarged_isets();
    return NONE;
  }
    // printf("#%d#", ++NB1);
  reset_enlarged_isets();
  return TRUE;
}

int expand_clq_from_node(int node) {
  int *neibors, neibor, saved_candidate_nb, i, nb, 
    *noneibors, noneibor, candidate, saved_noneibor_fp, debut;

  debut=debutGraph(); neibors=matrice[node];
  saved_candidate_nb=CLIQUE_CANDIDATE_STACK_fill_pointer; nb=0;
  for(i=debut; i<saved_candidate_nb; i++) {
    candidate=CLIQUE_CANDIDATE_STACK[i];
    if (neibors[candidate]==TRUE) {
      candidate_nb_neibors[CLIQUE_CANDIDATE_STACK_fill_pointer]=
	node_nb_neibors[candidate];
      nb++;
      candidate_potentiel[CLIQUE_CANDIDATE_STACK_fill_pointer]=nb;
      push(candidate, CLIQUE_CANDIDATE_STACK);
    }
    else {
      node_state[candidate]=PASSIVE;
      push(candidate, NONEIBOR_STACK);
    }
  }
  return nb;
}

void store_max_clique() {
  int i, node;
  MAXCLIQUE_STACK_fill_pointer=CLIQUE_STACK_fill_pointer;
  for(i=0; i<CLIQUE_STACK_fill_pointer; i++) 
    MAXCLIQUE_STACK[i]=CLIQUE_STACK[i];
  if (MAX_CLQ_SIZE != CLIQUE_STACK_fill_pointer)
    printf("erreur clique\n");
}

void printMaxClique() {
  int i;
  printf("Max Clique Size: %d\n", MAX_CLQ_SIZE);
  for(i=0; i<MAXCLIQUE_STACK_fill_pointer; i++)
    printf("%d ", MAXCLIQUE_STACK[i]);
  printf("\n");
}

int FILTER_STACK_fill_pointer=0;
int FILTER_STACK[tab_node_size];
int filter_state[tab_node_size];

void init_for_maxclique() {
  int node, i;
  DENSITY=NB_EDGE*100*2/(NB_NODE*(NB_NODE-1));
  RATIO=1.0*NB_NODE*(NB_NODE-1)/(2*NB_EDGE);
  CLIQUE_CANDIDATE_STACK_fill_pointer=0;
  for(node=0; node<=NB_NODE; node++) {
   if (node_state[node]==ACTIVE) {
      push(node, CLIQUE_CANDIDATE_STACK);
    }
    nodeMark[node]=0;
    nodeIsetMark[node]=0;
    iset_node_state[node]=PASSIVE;
    filter_state[node]=PASSIVE;
    iset_state[node]=ACTIVE;
    iset_involved[node]=FALSE;
    //~ conflict_iset[node]=FALSE;
    node_reason[node]=NO_REASON;
    node_tested_state[node]=FALSE;
  }
  NONEIBOR_STACK_fill_pointer=0;
  MAX_CLQ_SIZE=0; CLIQUE_STACK_fill_pointer=0;
  compute_candidate_nb_neibors();
  compute_degree_neibors();
  for(i=0; i<CLIQUE_CANDIDATE_STACK_fill_pointer; i++) {
    candidate_potentiel[i]=i+1;
    candidate_nb_neibors[i]=node_nb_neibors[CLIQUE_CANDIDATE_STACK[i]];
  }
}

int maxno;
int max_degree;
int pk, nk, nk_size;
double num_level=0.06;
int temp_iset_stack[tab_node_size];
int temp_iset_stack_fill_pointer=0;

int CUT(int node, int min) {
  int *neibors, neibor, i, *adjacences;
  adjacences=matrice[node];
  for(i=0; i<ISET_NB; i++) {
    neibors=ISETS[i];
    for(neibor=*neibors; neibor!=NONE; neibor=*(++neibors)) {
      if (adjacences[neibor]==TRUE)
	break;
    }
    if(neibor==NONE) {
	  ISETS[i][ISETS_SIZE[i]]=node;
      ISETS_SIZE[i]++;
      ISETS[i][ISETS_SIZE[i]]=NONE;
      if(i < min)
	    push(node, temp_iset_stack);
      node_iset_no[node]=i;
      return 1;
    }
  }
  ISETS_SIZE[ISET_NB]=1;
  ISETS[ISET_NB][0]=node;
  ISETS[ISET_NB][1]=NONE;
  node_iset_no[node]=ISET_NB;
  if(ISET_NB < min)
	push(node, temp_iset_stack);
  ISET_NB++;
  return 0;
}

int NUMBER_SORT() {
  int i, j, k, nb, position;
  int p, min_k, node, debut;
  
  //~ for(i=0; i<ISET_NB; i++) {
    //~ ISETS[i][0]=NONE;
    //~ ISETS_SIZE[i]=0;
  //~ }
  maxno = 1; debut=debutGraph(); position=debut;
  min_k = MAX_CLQ_SIZE - CLIQUE_STACK_fill_pointer;
  i = 0; j = 0; ISET_NB=0;
  temp_iset_stack_fill_pointer=0;
  while (position < CLIQUE_CANDIDATE_STACK_fill_pointer) {	  
    // node=CLIQUE_CANDIDATE_STACK[position];
   CUT(CLIQUE_CANDIDATE_STACK[position], min_k);
   // if (ISET_NB > maxno)
   //  maxno = ISET_NB;
   position++;
  }
  return ISET_NB;  
}

int TEMP_ISET_SIZE[tab_node_size];
int TEMP_ISET_SIZE_fill_pointer=0;

static int degreeisetsize(const void *pnode1, const void *pnode2) {
  int *node1, *node2, degree1, degree2;
  node1=(int *) pnode1; node2=(int *) pnode2;
  degree1=ISETS_SIZE[*node1]; degree2=ISETS_SIZE[*node2];
  if (degree1>degree2)
    return -1;
  else if (degree1==degree2)
    return 0;
  else return 1;
}

int ADD_NEW_UNITISET(int iset, int j, int nb_unit) {
  int i, node;
  node=ISETS[iset][ISETS[iset][j]];
  ISETS_SIZE[ISET_NB]=1;
  ISETS[ISET_NB][0]=node;
  ISETS[ISET_NB][1]=NONE;
  node_iset_no[node]=ISET_NB;
  ISET_NB++; nb_unit++;
  ISETS[iset][ISETS[iset][j]]=ISETS[iset][ISETS_SIZE[iset]-1];
  ISETS_SIZE[iset]--;
  if(ISETS_SIZE[iset]==1) nb_unit++;
  ISETS[iset][ISETS_SIZE[iset]]=NONE;
  return nb_unit;
}

void ARRANGE_ORDER_ISET() {
  int i, first_iset, iset, temp_iset;
  first_iset=TEMP_ISET_SIZE[0];
  for(i=1; i<TEMP_ISET_SIZE_fill_pointer; i++) {
	iset=TEMP_ISET_SIZE[i];
	if(ISETS_SIZE[first_iset] > ISETS_SIZE[iset]) {
	  temp_iset=TEMP_ISET_SIZE[i-1];
	  TEMP_ISET_SIZE[0]=TEMP_ISET_SIZE[i-1];
	  TEMP_ISET_SIZE[i-1]=temp_iset;
    }
  }
}

int ARRANGE_ISET() {
  int i, j, iset, nb_unit=0, max_size, min_noneibors, min_nb;
  min_noneibors=NB_NODE; max_size=0; min_nb=0;
  TEMP_ISET_SIZE_fill_pointer=0;
  for(i=0; i<ISET_NB; i++) {
	push(i, TEMP_ISET_SIZE); 	  
    if (ISETS_SIZE[i]==1)
      nb_unit++;
  }
  qsort(TEMP_ISET_SIZE, TEMP_ISET_SIZE_fill_pointer, 
        sizeof(int), degreeisetsize);
  while(nb_unit/ISET_NB < 1/10) {
    for(i=0; i<TEMP_ISET_SIZE_fill_pointer; i++) {
      iset=TEMP_ISET_SIZE[i];
      if(ISETS_SIZE[iset]>1) {
        for(j=0; j<ISETS_SIZE[iset]; j++) {
		  if(min_noneibors > node_nb_neibors[ISETS[iset][j]])
		    min_noneibors =  node_nb_neibors[ISETS[iset][j]];
		    min_nb = j;
		}
        nb_unit=ADD_NEW_UNITISET(iset, j, nb_unit);
        if(nb_unit/ISET_NB < 1/10) break;
        else ARRANGE_ORDER_ISET();
        i--;
	  }
    }
  }
  return 1;
}

int node_neibor_in_subgraph[tab_node_size];

static int degreesubgraph(const void *pnode1, const void *pnode2) {
  int *node1, *node2, degree1, degree2, degneib1, degneib2;
  //  node1=(*pnode1); node2=(*pnode2);
  node1=(int *) pnode1; node2=(int *) pnode2;
  degree1=node_neibor_in_subgraph[*node1]; 
  degree2=node_neibor_in_subgraph[*node2];
  // degneib1=degree_neibors_subgraph[*node1]; 
  // degneib2=degree_neibors_subgraph[*node2];
  if (degree1>degree2)
    return -1;
  else if (degree1==degree2) {
    // if(degneib1>degneib2)
    //  return -1;
    // else if(degneib1==degneib2)
      return 0;
      // else return 1;
  }
  else return 1;
}

void compute_nb_neibors_for_sparse_graph(int debut) {
  int i, j, *neibors, neibor, node, candidate, nb, node1;
  
  for(i=debut; i<CLIQUE_CANDIDATE_STACK_fill_pointer; i++) {
    node=CLIQUE_CANDIDATE_STACK[i]; nb=0; neibors=matrice[node];
    for(j=debut; j<CLIQUE_CANDIDATE_STACK_fill_pointer; j++)
      if (neibors[CLIQUE_CANDIDATE_STACK[j]]==TRUE)
	nb++;
    node_neibor_in_subgraph[node]=nb;
  }
}

void compute_nb_neibors_for_dense_graph(int debut) {
  int i,  *noneibors, noneibor, node, nb, nb_nodes;

  nb_nodes=CLIQUE_CANDIDATE_STACK_fill_pointer-debut;

  for(i=debut; i<CLIQUE_CANDIDATE_STACK_fill_pointer; i++) {
    node=CLIQUE_CANDIDATE_STACK[i];
    noneibors=node_non_neibors[node]; nb=0;
    for(noneibor=*noneibors; noneibor!=NONE; noneibor=*(++noneibors)) 
      if (node_state[noneibor]==ACTIVE) {
	nb++;
      }
    node_neibor_in_subgraph[node]=nb_nodes-nb;
  }
}

int DEGREES_SORT() {
  int i, j=0, k, node, node1, debut, tmp;

  debut=debutGraph();
  if (DENSITY>0.70)
    compute_nb_neibors_for_dense_graph(debut);
  else 
    compute_nb_neibors_for_sparse_graph(debut);
  
  /*
  for(i=0; i<=NB_NODE; i++) 
  	node_neibor_in_subgraph[i]=0;	
  for(i=debut; i<CLIQUE_CANDIDATE_STACK_fill_pointer; i++) {
    node=CLIQUE_CANDIDATE_STACK[i];
    for(k=i+1; k<CLIQUE_CANDIDATE_STACK_fill_pointer; k++) {
      node1=CLIQUE_CANDIDATE_STACK[k];
      if(matrice[node][node1]==TRUE) {
        node_neibor_in_subgraph[node]++;
        node_neibor_in_subgraph[node1]++;
      }
    }
  }
  */
  qsort(&CLIQUE_CANDIDATE_STACK[debut], 
	CLIQUE_CANDIDATE_STACK_fill_pointer-debut, 
        sizeof(int), degreesubgraph);
}

int CHOOSE_CANDIDATE() {
  int i, j, candidate, debut;
  debut=debutGraph();
  if (CLIQUE_CANDIDATE_STACK_fill_pointer-debut==1) {
    push(CLIQUE_CANDIDATE_STACK[debut], CLIQUE_STACK);
    if (CLIQUE_STACK_fill_pointer>MAX_CLQ_SIZE) {
      MAX_CLQ_SIZE=CLIQUE_STACK_fill_pointer;
      store_max_clique();
      printf("Current MaxClique Size=%d\n", MAX_CLQ_SIZE);
    }
    pop(CLIQUE_STACK);
    return NONE;
   }
   else {
     candidate=
      CLIQUE_CANDIDATE_STACK[CLIQUE_CANDIDATE_STACK_fill_pointer-1];
     CLIQUE_CANDIDATE_STACK_fill_pointer--;
     CANDIDATE_DEGREE_STACK_fill_pointer--;
   }
   return candidate;
}

int backtracking_for_maxclique() {
  int i, node, debut, clq_size;
  NB_BACK_CLIQUE++;
  while (CLIQUE_STACK_fill_pointer>0) {
    node=pop(CLIQUE_STACK);
    for(i=saved_noneibor_stack[node]; i<NONEIBOR_STACK_fill_pointer; i++) 
      node_state[NONEIBOR_STACK[i]]=ACTIVE;
    NONEIBOR_STACK_fill_pointer=saved_noneibor_stack[node];
    CLIQUE_CANDIDATE_STACK_fill_pointer=saved_candidate_stack[node];
    push(node, NONEIBOR_STACK);
    clq_size=MAX_CLQ_SIZE-CLIQUE_STACK_fill_pointer;
    if (CANDIDATE_DEGREE_STACK[CLIQUE_CANDIDATE_STACK_fill_pointer-1]-2>
        clq_size || lookahead_after_backtracking()!=NONE) {
	  CANDIDATE_DEGREE_STACK_fill_pointer=
	    CLIQUE_CANDIDATE_STACK_fill_pointer;
      return TRUE; 
    }
  }
  CLIQUE_CANDIDATE_STACK_fill_pointer=0;
  NONEIBOR_STACK_fill_pointer=0;
  return 0;
}

int by_filter(int debut, int rest_clq_size) {
  int nb, i, node, matching, *noneibors, noneibor, j;
  nb=CLIQUE_CANDIDATE_STACK_fill_pointer-debut;
  
  if (nb/2<rest_clq_size) {
    for(i=debut; i<CLIQUE_CANDIDATE_STACK_fill_pointer; i++) {
      filter_state[CLIQUE_CANDIDATE_STACK[i]]=ACTIVE;
    }
    matching=0;
    for(i=CLIQUE_CANDIDATE_STACK_fill_pointer-1; i>=debut; i--) {
      node=CLIQUE_CANDIDATE_STACK[i];
      if (filter_state[node]==ACTIVE) {
	noneibors=node_non_neibors[node];
	for(noneibor=*noneibors; noneibor!=NONE; noneibor=*(++noneibors)) {
	  if (filter_state[noneibor]==ACTIVE) {
	    filter_state[noneibor]=PASSIVE; nb--;
	    break;
	  }
	}
	filter_state[node]=PASSIVE; nb--;
	matching++;
	if (matching+nb<=rest_clq_size)
	  break;
	if (matching+nb/2>rest_clq_size) 
	  break;
      }
    }
    for(j=i-1; j>=debut; j--)
      filter_state[CLIQUE_CANDIDATE_STACK[j]]=PASSIVE;
    if (matching+nb<=rest_clq_size) 
      return NONE;
    else return TRUE;
  }
  else return TRUE;
}

int set_isets(int debut) {
  int i, node, iset_no;

  ISET_NB=candidate_iset_no[CLIQUE_CANDIDATE_STACK_fill_pointer-1]+1;
  for (i=0; i<ISET_NB; i++) {
    ISETS[i][0]=NONE;
    ISETS_SIZE[i]=0;
  }
  for(i=debut; i<CLIQUE_CANDIDATE_STACK_fill_pointer; i++) {
    node=CLIQUE_CANDIDATE_STACK[i];
    iset_no=candidate_iset_no[i];
    node_iset_no[node]=candidate_iset_no[i];
    ISETS[iset_no][ISETS_SIZE[iset_no]]=node;
    ISETS_SIZE[iset_no]++;
    ISETS[iset_no][ISETS_SIZE[iset_no]]=NONE;
  }
  return ISET_NB;
}


int lookahead_after_backtracking() {
  int debut, clq_size, i, node, *nodes, ub=0, saved;

  debut=debutGraph();
  clq_size=MAX_CLQ_SIZE-CLIQUE_STACK_fill_pointer;
  if (// by_filter(debut, clq_size)==NONE ||
      set_isets(debut)<=clq_size ||
      //~ (ARRANGE_ISET()==1 && maxsatz(clq_size)==NONE))
      (maxsatz(clq_size)==NONE))
    return NONE;
  else {
    return TRUE;
  }
}

int lookahead() {
  int debut, clq_size, i, node, *nodes, ub=0, saved;

  debut=debutGraph();
  clq_size=MAX_CLQ_SIZE-CLIQUE_STACK_fill_pointer;
  if (//by_filter(debut, clq_size)==NONE ||
      NUMBER_SORT()<=clq_size ||
      //~ (ARRANGE_ISET()==1 && maxsatz(clq_size)==NONE))
      (maxsatz(clq_size)==NONE))
    return NONE;
  else {
    saved=CLIQUE_CANDIDATE_STACK_fill_pointer;
    CLIQUE_CANDIDATE_STACK_fill_pointer=debut;
    CANDIDATE_DEGREE_STACK_fill_pointer=debut;
    for(i=0; i<temp_iset_stack_fill_pointer; i++) {
      node=temp_iset_stack[i];
      candidate_iset_no[CLIQUE_CANDIDATE_STACK_fill_pointer]=node_iset_no[node];
      push(node, CLIQUE_CANDIDATE_STACK);
      push(0, CANDIDATE_DEGREE_STACK);
    }
    if (clq_size < 0) clq_size = 0; 
    for (i = clq_size; i < ISET_NB; i++) {
      nodes=ISETS[i];
      for(node=*nodes; node!=NONE; node=*(++nodes)) {
	if (node <= NB_NODE) {
	  candidate_iset_no[CLIQUE_CANDIDATE_STACK_fill_pointer]=i;
	  push(i+1, CANDIDATE_DEGREE_STACK);
	  push(node, CLIQUE_CANDIDATE_STACK);
	}
	else {
	  printf("bizzar reset_enlarged_isets\n"); break;
	}
      }
    }
    if (saved!=CLIQUE_CANDIDATE_STACK_fill_pointer)
      printf("bizzar reorder by isets\n");
    return ISET_NB;
  }
}

void EXPAND() {
 int p, debut, candidate, expand, degree, clq_size;
 
 while (CLIQUE_CANDIDATE_STACK_fill_pointer>0) {
   nnb++; 
   sPoint[CLIQUE_STACK_fill_pointer+1]=sPoint[CLIQUE_STACK_fill_pointer+1]
   +sPoint[CLIQUE_STACK_fill_pointer]-sN[CLIQUE_STACK_fill_pointer+1];
   sN[CLIQUE_STACK_fill_pointer+1]=sPoint[CLIQUE_STACK_fill_pointer];
   candidate=CHOOSE_CANDIDATE();
   if (candidate!=NONE) {   
     saved_candidate_stack[candidate]=CLIQUE_CANDIDATE_STACK_fill_pointer;
     saved_noneibor_stack[candidate]=NONEIBOR_STACK_fill_pointer;
     push(candidate, CLIQUE_STACK);
     node_state[candidate]=PASSIVE;
     expand=expand_clq_from_node(candidate);
     if (expand != 0) {
       if ((double)sPoint[CLIQUE_STACK_fill_pointer]/pk < num_level) {
         nk++;  DEGREES_SORT();
       }
       sPoint[CLIQUE_STACK_fill_pointer]++; pk++;
       if(lookahead()==NONE)
         backtracking_for_maxclique();
     }
     else if (expand == 0) {
       if(CLIQUE_STACK_fill_pointer > MAX_CLQ_SIZE) { 
         MAX_CLQ_SIZE=CLIQUE_STACK_fill_pointer;
         store_max_clique();
         printf("Current MaxClique Size=%d\n", MAX_CLQ_SIZE);
       }
       backtracking_for_maxclique();
     }
   }
   else backtracking_for_maxclique();
 }
 return;
}

static int degreecmp(const void *pnode1, const void *pnode2) {
  int *node1, *node2, degree1, degree2, degneib1, degneib2;
  //  node1=(*pnode1); node2=(*pnode2);
  node1=(int *) pnode1; node2=(int *) pnode2;
  degree1=node_nb_neibors[*node1]; degree2=node_nb_neibors[*node2];
  degneib1=degree_neibors[*node1]; degneib2=degree_neibors[*node2];
  if (degree1>degree2)
    return -1;
  else if (degree1==degree2) {
    if(degneib1>degneib2)
      return -1;
    else if(degneib1==degneib2)
      return 0;
    else return 1;
  }
  else return 1;
}

int addIntoIsetTomitaBis(int node) {
  int *neibors, neibor, i, *adjacences;
  adjacences=matrice[node];
  for(i=0; i<ISET_NB; i++) {
    neibors=ISETS[i];
    for(neibor=*neibors; neibor!=NONE; neibor=*(++neibors)) {
      if (adjacences[neibor]==TRUE)
	break;
    }
    if (neibor==NONE) {
      ISETS[i][ISETS_SIZE[i]]=node;
      ISETS_SIZE[i]++;
      ISETS[i][ISETS_SIZE[i]]=NONE;
      node_iset_no[node]=i;
      return TRUE;
    }
  }
  ISETS_SIZE[ISET_NB]=1;
  ISETS[ISET_NB][0]=node;
  ISETS[ISET_NB][1]=NONE;
  node_iset_no[node]=ISET_NB;
  ISET_NB++;
  return FALSE;
}

int partitionIntoIsetsTomita() {
  int i, node, candidate, iset, iset_no;

  ISET_NB=0;
  for(i=0; i<CLIQUE_CANDIDATE_STACK_fill_pointer; i++) {
    candidate=CLIQUE_CANDIDATE_STACK[i];
    addIntoIsetTomitaBis(candidate);
  }
  return ISET_NB;
}

void MCQ() {
 int i, j, tmp, k, max_k, node, node1;
 qsort(CLIQUE_CANDIDATE_STACK, CLIQUE_CANDIDATE_STACK_fill_pointer, 
       sizeof(int), degreecmp);
 max_degree=lookahead();
 // max_degree = partitionIntoIsetsTomita();
 //~ max_degree = node_nb_neibors[CLIQUE_CANDIDATE_STACK[0]];
 printf("max_degree = %d \n", max_degree); 
 /*
 if (CLIQUE_CANDIDATE_STACK_fill_pointer!=CANDIDATE_DEGREE_STACK_fill_pointer)
   printf("azazaza...");
 for (i = 0; i < NB_NODE-max_degree; i++) {
   push(i+1, CANDIDATE_DEGREE_STACK);
 }
 for (i = NB_NODE-max_degree; i < NB_NODE; i++) {
   push(max_degree, CANDIDATE_DEGREE_STACK);
 }
 */
 for (i = 0; i < NB_NODE; i++) {
   sPoint[i] = 0;
   sN[i] = 0;
 }
 EXPAND();
}

main(int argc, char *argv[]) {
  int i, result;
  unsigned long long begintime, endtime, mess;
  struct tms *a_tms;
  FILE *fp_time;
  
  
  switch (build_simple_graph_instance(argv[1])) {
  case FALSE: printf("Input file error\n"); return FALSE;
  case TRUE:
    build_complement_graph();
    a_tms = ( struct tms *) malloc( sizeof (struct tms));
    mess=times(a_tms); begintime = a_tms->tms_utime;
    init_for_maxclique();
    printf("instance information: #node=%d, #edge=%d density= %5.4f\n\n", 
	   NB_NODE, NB_EDGE, ((float)NB_EDGE*2)/(NB_NODE*(NB_NODE-1)));
	pk = 0; nk = 0; nk_size = 0;
	MCQ();
    printMaxClique();
    mess=times(a_tms); endtime = a_tms->tms_utime;
    break;
  }
  
  
  printf ("Program terminated in %5.3f seconds.\n",
	  ((double)(endtime-begintime)/CLK_TCK));
  printf("iMCQ+MSZ5+TwoIset10 %s %d %d %5.4f %10.3f %d %d %d %d %d %d %d %d\n", 
	 argv[1], NB_NODE, NB_EDGE, 
	 ((float)NB_EDGE*2)/(NB_NODE*(NB_NODE-1)),
	 ((double)(endtime-begintime)/CLK_TCK), 
	 NB_BACK_CLIQUE, MAX_CLQ_SIZE, NB_ISETS_TEST, nk, pk, nnb, TOTAL, DIVIDE); 
  fp_time = fopen("resultsOfiMCQ+MSZ5+TwoIset17", "a");
  fprintf(fp_time, 
	  "iMCQ+MSZ5+TwoIset17 %s %d %d %5.4f %10.3f %d %d %d %d %d %d %d %d\n", 
	  argv[1], NB_NODE, NB_EDGE, 
	  ((float)NB_EDGE*2)/(NB_NODE*(NB_NODE-1)),
	  ((double)(endtime-begintime)/CLK_TCK), 
	  NB_BACK_CLIQUE, MAX_CLQ_SIZE, NB_ISETS_TEST, nk, pk, nnb, TOTAL, DIVIDE);
  fclose(fp_time);
  return TRUE;
}
