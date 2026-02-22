/******************************************************************************************/
/* Copyright 2016 (c) Chu-Min Li & Hua Jiang                                              */
/*                                                                                        */
/* This is a software for finding a maximum clique in an undirected graph                 */
/* or to prove the optimality of a maximum clique in an undirected graph                  */
/* It is provided for research purpose. For all other purposes, please contact Chu-Min LI */
/* To compile the software use command: gcc -O3 -mcmodel=medium IncMC2.c -o IncMC2        */
/* For solving a graph from scratch, please use command: ./IncMC2 fileInDIMACSformat      */
/* For solving a graph from a given lower bound lb, use command:                          */
/*                        ./IncMC2 fileInDIMACSformat -i lb                               */
/******************************************************************************************/


#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/times.h>
#include <sys/types.h>
#include <limits.h>
#include <unistd.h>
#include <sys/resource.h>
#include <math.h>
#include <assert.h>
#define SOMC
#define WORD_LENGTH 100
#define TRUE 1
#define FALSE 0
#define NONE -1
#define DELIMITER 0
#define PASSIVE 0
#define ACTIVE 1
#define P_TRUE 2
#define P_FALSE 0
#define NO_REASON -3
#define CONFLICT -1978
#define tab_node_size  10010
#define max_expand_depth 1200
#define pop(stack) stack[--stack ## _fill_pointer]
#define push(item, stack) stack[stack ## _fill_pointer++] = item
#define ptr(stack) stack ## _fill_pointer
#define is_neibor(i,j) matrice[i][j]
#define candidate_start branch_stack[branch_stack_fill_pointer][0]
#define candidate_end Candidate_Stack_fill_pointer
#define branching_node branch_stack[branch_stack_fill_pointer][1]
#define candidate_is_not_empty() (Candidate_Stack_fill_pointer-candidate_start>0)
#define candidate_is_empty() (Candidate_Stack_fill_pointer==candidate_start)
#define CUR_CLQ_SIZE Clique_Stack_fill_pointer
#define NOT_ROOT (ptr(Cursor_Stack)>1)
#define CURSOR Cursor_Stack[Cursor_Stack_fill_pointer-1]
#define SSINDEX SIndex_Stack[SIndex_Stack_fill_pointer-1]
#define MIN(a,b) a<=b?a:b
#define time_in_s(clock) (double)(clock)/clock_per_second
static int FORMAT = 1, DENSITY, NB_NODE, ADDED_NODE, NB_EDGE, MAX_CLQ_SIZE,
		MAX_ISET_SIZE, INIT_CLQ_SIZE, NB_BACK_CLIQUE;
static char node_state[2 * tab_node_size];
//static int node_value[2 * tab_node_size];
static int node_reason[2 * tab_node_size];
//static char static_matrix[tab_node_size][tab_node_size];
static char *static_matrix;
static char matrice[tab_node_size][tab_node_size];
static int iSET[tab_node_size][tab_node_size];
static int iSET_COUNT = 0;
static int iSET_Size[tab_node_size];
//static int iSET_OLD_Size[tab_node_size];
//static int iSET_ADD_Size[tab_node_size];
static char iSET_State[tab_node_size];
static char iSET_Used[tab_node_size];
static char iSET_Tested[tab_node_size];
static int iSET_Index[tab_node_size];
static int REDUCED_iSET_STACK[tab_node_size * 10];
static int REDUCED_iSET_STACK_fill_pointer = 0;
static int PASSIVE_iSET_STACK[tab_node_size];
static int PASSIVE_iSET_STACK_fill_pointer = 0;
static int FIXED_NODE_STACK[2 * tab_node_size];
static int FIXED_NODE_STACK_fill_pointer = 0;
static int UNIT_STACK[tab_node_size];
static int UNIT_STACK_fill_pointer = 0;
static int NEW_UNIT_STACK[tab_node_size];
static int NEW_UNIT_STACK_fill_pointer = 0;
static int *node_neibors[tab_node_size];
static int *none_neibors[tab_node_size];
static int static_degree[tab_node_size];
static int active_degree[tab_node_size];
//static int neibor_degree[tab_node_size];
static int none_degree[tab_node_size];
static int Clique_Stack[tab_node_size];
static int Clique_Stack_fill_pointer = 0;
static int MaxCLQ_Stack[tab_node_size];
static int Candidate_Stack[tab_node_size * max_expand_depth];
static int Candidate_Stack_fill_pointer = 0;
static int Cursor_Stack[max_expand_depth];
static int Cursor_Stack_fill_pointer = 0;
static int Vertex_UB[tab_node_size * max_expand_depth];
static int Rollback_Point;
static int Branching_Point;
static int Tmp_Stack[tab_node_size * 2];
static int Tmp_Stack_fill_pointer = 0;
static int NEW_OLD[tab_node_size];
static int OLD_NEW[tab_node_size];
static int NB_CANDIDATE = 0, FIRST_INDEX, REBUILD_MATRIX = FALSE;

static int Extra_Node_Stack[1000];
//static int Extra_Node_Stack_fill_pointer = 0;
//static int Extra_Node_Index[tab_node_size];
static int Last_Idx = 0;
static int cut_ver = 0, total_cut_ver = 0;
static int cut_inc = 0, total_cut_inc = 0;
static int cut_iset = 0, total_cut_iset = 0;
static int cut_satz = 0, total_cut_satz = 0;
static long long Branches_Nodes[6];
static int  STATIC_ORDERING = TRUE, LAST_IN, INIT_CLIQUE = 0;
static float Dynamic_Radio = 0.6;
static float Mean_Dynamic_Radio = 0.0;
static int Dynamic_Count = 0;
//static int INIT_SORTING = FALSE;
//static int CACHED_REASON_STACK[tab_node_size];
//static int CACHED_REASON_STACK_fill_pointer = 0;
static int Branches[1200];
static int none_degree_inc(const void * a, const void * b) {
	int node1 = *((int *) a), node2 = *((int *) b);
	if (none_degree[node1] < none_degree[node2])
		return -1;
	else if (none_degree[node1] == none_degree[node2]) {
		return 0;
	} else {
		return 1;
	}
}
static int static_degree_dec(const void * a, const void * b) {
	int node1 = *((int *) a), node2 = *((int *) b);
	if (static_degree[node1] > static_degree[node2])
		return -1;
	else if (static_degree[node1] == static_degree[node2]) {
		return 0;
	} else {
		return 1;
	}
}
static int build_simple_graph_instance(char *input_file) {
	FILE* fp_in = fopen(input_file, "r");
	char ch, words[WORD_LENGTH];
	int i, j, e, nb1, nb2, node, left_node, right_node, nb_edge = 0;
	if (fp_in == NULL )
		return FALSE;
	if (FORMAT == 1) {
		fscanf(fp_in, "%c", &ch);
		while (ch != 'p') {
			while (ch != '\n')
				fscanf(fp_in, "%c", &ch);
			fscanf(fp_in, "%c", &ch);
		}
		fscanf(fp_in, "%s%d%d", words, &NB_NODE, &NB_EDGE);
	} else
		fscanf(fp_in, "%d%d", &NB_NODE, &NB_EDGE);
	
	if(NB_NODE>=tab_node_size){
		printf("The number of vertices exceeds the limitation of (%d).\n", tab_node_size);
		exit(0);
	}

	for (i = 0; i < NB_EDGE; i++) {
		if (FORMAT == 1)
			fscanf(fp_in, "%s%d%d", words, &left_node, &right_node);
		else
			fscanf(fp_in, "%d%d", &left_node, &right_node);
		if (left_node == right_node) {
			i--, NB_EDGE--;
		} else {
			if (left_node > right_node) {
				e = right_node;
				right_node = left_node;
				left_node = e;
			}
			if (matrice[left_node][right_node] == FALSE) {
				matrice[left_node][right_node] = TRUE;
				matrice[right_node][left_node] = TRUE;
				static_degree[left_node]++;
				static_degree[right_node]++;
				nb_edge++;
			}
		}
	}
	fclose(fp_in);
	NB_EDGE = nb_edge;
	for (i = 1; i <= NB_NODE; i++) {
		node_state[i] = ACTIVE;
		active_degree[i] = static_degree[i];

	
		none_degree[i] = NB_NODE - static_degree[i] - 1;
		none_neibors[i] = (int *) malloc(
				(NB_NODE+2) * sizeof(int));

	        node_neibors[i] = none_neibors[i] + none_degree[i]+1;

		nb1 = 0;
		nb2 = 0;
		for (j = 1; j <= NB_NODE; j++) {
			if (matrice[i][j] == TRUE)
				node_neibors[i][nb1++] = j;
			else if (i != j) {
				none_neibors[i][nb2++] = j;
			}
		}
		node_neibors[i][nb1] = NONE;
		none_neibors[i][nb2] = NONE;
	}
//	for (i = 1; i <= NB_NODE; i++) {
//		memcpy(static_matrix[i], matrice[i], (NB_NODE + 1) * sizeof(char));
//	}
	static_matrix = (char *) malloc(
			(NB_NODE + 1) * (NB_NODE + 1) * sizeof(char));
	for (node = 1; node <= NB_NODE; node++) {
		qsort(none_neibors[node], none_degree[node], sizeof(int),
				none_degree_inc);
		qsort(node_neibors[node], static_degree[node], sizeof(int),
				static_degree_dec);
	}
	printf("c Instance Information: #node=%d, #edge=%d density= %5.4f \n",
			NB_NODE, NB_EDGE,
			((float) NB_EDGE * 2) / (NB_NODE * (NB_NODE - 1)));

	return TRUE;
}

static int choose_candidate_node() {
	int i, chosen_node = NONE, node, max_degree;
	max_degree = -1;
	for (i = 0; i < ptr(Candidate_Stack); i++) {
		node = Candidate_Stack[i];
		if (static_degree[node] > max_degree) {
			max_degree = static_degree[node];
			chosen_node = node;
		}
	}
	return chosen_node;
}

static void search_initial_maximum_clique() {
	int i = 0, j = 0, node = NONE;
	ptr(Clique_Stack) = 0;
	ptr(Candidate_Stack) = 0;
	for (node = 1; node <= NB_NODE; node++) {
		push(node, Candidate_Stack);
	}
	node = choose_candidate_node();
	while (node != NONE) {
		j = 0;
		push(node, Clique_Stack);
		for (i = 0; i < ptr(Candidate_Stack); i++) {
			if (is_neibor(node, Candidate_Stack[i])==TRUE) {
				Candidate_Stack[j++] = Candidate_Stack[i];
			}
		}
		ptr(Candidate_Stack) = j;
		node = choose_candidate_node();
	}
	INIT_CLQ_SIZE = ptr(Clique_Stack);
	printf("c Initial clique size: %d\n", INIT_CLQ_SIZE);
}

static void complement_graph() {
	int node, *neibors, i, j, t;
	for (node = 1; node <= NB_NODE; node++) {
		neibors = node_neibors[node];
		node_neibors[node] = none_neibors[node];
		none_neibors[node] = neibors;
		t = static_degree[node];
		static_degree[node] = none_degree[node];
		active_degree[node] = static_degree[node];
		none_degree[node] = t;
	}
	for (i = 1; i <= NB_NODE; i++)
		for (j = 1; j <= NB_NODE; j++) {
			if (i != j) {
				if (matrice[i][j] == TRUE)
					matrice[i][j] = FALSE;
				else
					matrice[i][j] = TRUE;
			}
		}
}
static void sort_by_active_degree() {
	int min = 0, i, node = NONE, neibor, *neibors, j;
	ptr(Candidate_Stack) = 0;
	for (i = 1; i <= NB_NODE; i++) {
		node_state[i] = ACTIVE;
		//	active_degree[i] = static_degree[i];
	}
	for (i = 1; i <= NB_NODE; i++) {
		min = NB_NODE;
		for (j = 1; j <= NB_NODE; j++) {
			if (node_state[j] == ACTIVE && active_degree[j] < min) {
				min = active_degree[j];
				node = j;
			}
		}
		push(node, Candidate_Stack);
		node_state[node] = PASSIVE;
		neibors = node_neibors[node];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors))
			if (node_state[neibor] == ACTIVE) {
				active_degree[neibor]--;
			}
	}
	push(DELIMITER, Candidate_Stack);
	for (i = 1; i <= NB_NODE; i++) {
		active_degree[i] = static_degree[i];
	}
}

static void my_sort_by_degree_dec() {
	int max, i, node, neibor, *neibors, j, node1, index;
	for (i = 0; i < ptr(Candidate_Stack); i++) {
		node = Candidate_Stack[i];
		max = active_degree[node];
		index = i;
		for (j = i + 1; j < ptr(Candidate_Stack); j++) {
			node1 = Candidate_Stack[j];
			if (active_degree[node1] > max) {
				node = node1;
				max = active_degree[node1];
				index = j;
			}
		}
		node1 = Candidate_Stack[i];
		Candidate_Stack[i] = node;
		Candidate_Stack[index] = node1;
		neibors = node_neibors[node];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors))
			active_degree[neibor]--;
	}
	for (node = 1; node <= NB_NODE; node++) {
		active_degree[node] = static_degree[node];
	}
}
static void my_sort_by_degree_inc() {
	int min, i, node, neibor, *neibors, j, node1, index;
	for (i = 0; i < ptr(Candidate_Stack); i++) {
		node = Candidate_Stack[i];
		min = active_degree[node];
		index = i;
		for (j = i + 1; j < ptr(Candidate_Stack); j++) {
			node1 = Candidate_Stack[j];
			if (active_degree[node1] < min) {
				node = node1;
				min = active_degree[node1];
				index = j;
			}
		}
		node1 = Candidate_Stack[i];
		Candidate_Stack[i] = node;
		Candidate_Stack[index] = node1;
		neibors = node_neibors[node];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors))
			active_degree[neibor]--;
	}
	for (node = 1; node <= NB_NODE; node++) {
		active_degree[node] = static_degree[node];
	}
}

static int iset_smaller_than(int iset1, int iset2) {
	int *neibors1, neibor1, *neibors2, neibor2;
	if (iSET_Size[iset1] < iSET_Size[iset2])
		return TRUE;
	else if (iSET_Size[iset1] > iSET_Size[iset2])
		return FALSE;
	neibors1 = iSET[iset1];
	neibors2 = iSET[iset2];
	for (neibor1 = *neibors1, neibor2 = *neibors2;
			neibor1 != NONE && neibor2 != NONE;
			neibor1 = *(++neibors1), neibor2 = *(++neibors2)) {
		if (static_degree[neibor1] < static_degree[neibor2])
			return TRUE;
		else if (static_degree[neibor1] > static_degree[neibor2])
			return FALSE;
	}
	if (neibor1 == NONE && neibor2 == NONE)
		return FALSE;
	else if (neibor1 == NONE)
		return TRUE;
	else
		return FALSE;
}



static void sort_isets_and_push_nodes() {
	int i, j, iset1, iset2, node, index;
	ptr(Tmp_Stack) = 0;
	ptr(Candidate_Stack) = 0;
	for (i = 0; i < iSET_COUNT; i++) {
		push(i, Tmp_Stack);
		qsort(iSET[i], iSET_Size[i], sizeof(int), static_degree_dec);
	}
	for (i = 0; i < ptr(Tmp_Stack); i++) {
		iset1 = Tmp_Stack[i];
		index = i;
		for (j = i + 1; j < ptr(Tmp_Stack); j++) {
			iset2 = Tmp_Stack[j];
			if (iset_smaller_than(iset2, iset1) == TRUE) {
				iset1 = iset2;
				index = j;
			}
		}
		iset2 = Tmp_Stack[i];
		Tmp_Stack[i] = iset1, Tmp_Stack[index] = iset2;
		for (j = iSET_Size[iset1] - 1; j >= 0; j--) {
			node = iSET[iset1][j];
			push(node, Candidate_Stack);
		}
		//printf("%d ", iSET_Size[iset1]);
	}
	//printf("\n");
	push(DELIMITER, Candidate_Stack);
}

static void print_isets(int i_set) {
	int *color_set, node;
//printf("\niset: \n");
//	printf("SET %d active=%d: c_size=%d  ", i_set + 1, iSET_State[i_set],
//			iSET_Size[i_set]);
	color_set = iSET[i_set];
	printf("{ ");
	for (node = *color_set; node != NONE; node = *(++color_set)) {
		if (node_state[node] == ACTIVE)
			printf("%d ", node);
		else if (node_state[node] == PASSIVE) {
			if (node_state[node] == P_TRUE)
				printf("%d ", node);
			else if (node_state[node] == P_FALSE)
				printf("%d ", node);
		} else {
			printf("%d ", node);
		}
	}
	printf("} ");
//printf("\n");
}
static void print_all_iset() {
	int i = 0;
	for (i = 0; i < iSET_COUNT; i++) {
		print_isets(i);
	}
}

static int re_number(int node) {
	int i, k, *neibors, *saved_neibors, neibor, one_neibor;
	char *adjacences = matrice[node], *adjacences1;
	for (i = 0; i < iSET_COUNT - 1; i++) {
		neibors = iSET[i];
		one_neibor = NONE;
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			if (adjacences[neibor] == TRUE) {
				if (one_neibor == NONE) {
					one_neibor = neibor;
					saved_neibors = neibors;
				} else if (one_neibor != NONE) {
					break;
				}
			}
		}
		if (one_neibor == NONE) {
		  iSET_Index[node] = i;
			iSET[i][iSET_Size[i]] = node;
			iSET_Size[i]++;
			iSET[i][iSET_Size[i]] = NONE;
			return TRUE;
		}
		if (neibor == NONE) {
			adjacences1 = matrice[one_neibor];
			for (k = i + 1; k < iSET_COUNT; k++) {
				neibors = iSET[k];
				for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
					if (adjacences1[neibor] == TRUE)
						break;
				}
				if (neibor == NONE) {
					iSET[k][iSET_Size[k]] = one_neibor;
					iSET_Size[k]++;
					iSET[k][iSET_Size[k]] = NONE;
					iSET_Index[one_neibor] = k;
					*saved_neibors = node;
					iSET_Index[node] = i;
					return TRUE;
				}
			}
		}
	}
	return FALSE;
}
static int addIntoIsetTomitaBis(int node) {
	int j, *current_set, iset_node;
	char *adjacent = matrice[node];
	for (j = 0; j < iSET_COUNT; j++) {
		current_set = iSET[j];
		for (iset_node = *current_set; iset_node != NONE; iset_node =
				*(++current_set)) {
			if (adjacent[iset_node] == TRUE)
				break;
		}
		if (iset_node == NONE) {
			iSET_Size[j]++;
			*(current_set) = node;
			*(++current_set) = NONE;
			iSET_Index[node] = j;
			return TRUE;
		}
	}
	if (iSET_COUNT < MAX_ISET_SIZE) {
		iSET_Size[j] = 1;
		iSET[j][0] = node;
		iSET[j][1] = NONE;
		iSET_Index[node] = j;
		iSET_COUNT++;
		return TRUE;
	} else {
		return FALSE;
	}
}

/* static int cut_by_iset_first() { */
/* 	int i = ptr(Candidate_Stack) - 2, node; */
/* 	FIRST_INDEX = NONE; */
/* 	iSET_COUNT = 0; */
/* 	MAX_ISET_SIZE = MAX_CLQ_SIZE - CUR_CLQ_SIZE - 1; */
/* 	for (node = Candidate_Stack[i]; node != DELIMITER; node = */
/* 			Candidate_Stack[--i]) { */
/* 		if (addIntoIsetTomitaBis(node) == FALSE) { */
/* 			FIRST_INDEX = i; */
/* 			do { */
/* 				Candidate_Stack[i] = -node; */
/* 			} while ((node = Candidate_Stack[--i]) != DELIMITER); */
/* 			break; */
/* 		} */
/* 	} */
/* 	if (FIRST_INDEX == NONE) { */
/* 		cut_iset++; */
/* 		Vertex_UB[CURSOR]=iSET_COUNT+1; */
/* 		return TRUE; */
/* 	} else { */
/* 		Branching_Point = FIRST_INDEX + 1; */
/* 		return FALSE; */
/* 	} */
/* } */

/* static int cut_by_iset_first_renumber() { */
/* 	int i = ptr(Candidate_Stack) - 2, node; */
/* 	FIRST_INDEX = NONE; */
/* 	iSET_COUNT = 0; */
/* 	MAX_ISET_SIZE = MAX_CLQ_SIZE - CUR_CLQ_SIZE - 1; */
/* 	for (node = Candidate_Stack[i]; node != DELIMITER; node = */
/* 			Candidate_Stack[--i]) { */
/* 		if (addIntoIsetTomitaBis(node) == FALSE && re_number(node) == FALSE) { */
/* 			FIRST_INDEX = i; */
/* 			do { */
/* 				Candidate_Stack[i] = -node; */
/* 			} while ((node = Candidate_Stack[--i]) != DELIMITER); */
/* 			break; */
/* 		} */
/* 	} */
/* 	if (FIRST_INDEX == NONE) { */
/* 		cut_iset++; */
/* 		Vertex_UB[CURSOR]=iSET_COUNT+1; */
/* 		return TRUE; */
/* 	} else { */
/* 		Branching_Point = FIRST_INDEX + 1; */
/* 		return FALSE; */
/* 	} */
/* } */

/* static int cut_by_iset_last() { */
/* 	int i = ptr(Candidate_Stack) - 2, node; */
/* 	FIRST_INDEX = NONE; */
/* 	iSET_COUNT = 0; */
/* 	MAX_ISET_SIZE = MAX_CLQ_SIZE - CUR_CLQ_SIZE - 1; */
/* 	for (node = Candidate_Stack[i]; node != DELIMITER; node = */
/* 			Candidate_Stack[--i]) { */
/* 		if (addIntoIsetTomitaBis(node) == FALSE) { */
/* 			if (FIRST_INDEX == NONE) */
/* 				FIRST_INDEX = i; */
/* 			Candidate_Stack[i] = -node; */
/* 			Vertex_UB[i] = MAX_ISET_SIZE + 1; */
/* 		} */
/* 	} */
/* 	if (FIRST_INDEX == NONE) { */
/* 		cut_iset++; */
/* 		Vertex_UB[CURSOR]=iSET_COUNT+1; */
/* 		return TRUE; */
/* 	} else { */
/* 		Branching_Point = FIRST_INDEX + 1; */
/* 		return FALSE; */
/* 	} */
/* } */

static int cut_by_iset_last_renumber() {
	int i = ptr(Candidate_Stack) - 2, node;
	LAST_IN = INT_MAX;
	FIRST_INDEX = NONE;
	iSET_COUNT = 0;
	MAX_ISET_SIZE = MAX_CLQ_SIZE - CUR_CLQ_SIZE - 1;
	for (node = Candidate_Stack[i]; node != DELIMITER; node =
			Candidate_Stack[--i]) {
		if (addIntoIsetTomitaBis(node) == FALSE && re_number(node) == FALSE) {
			if (FIRST_INDEX == NONE)
				FIRST_INDEX = i;
			Candidate_Stack[i] = -node;
			//Vertex_UB[i] = MAX_ISET_SIZE + 1;
		} else {
			LAST_IN = i;
		}
	}
	if (FIRST_INDEX == NONE) {
		cut_iset++;
		Vertex_UB[CURSOR]=iSET_COUNT+1;
		return TRUE;
	} else {
		Branching_Point = FIRST_INDEX + 1;
//		i = ptr(Candidate_Stack) - 2;
//		for (node = Candidate_Stack[i]; node != DELIMITER; node =
//				Candidate_Stack[--i]) {
//			if (node < 0 && i > LAST_IN) {
//				Vertex_UB[i] = MAX_CLQ_SIZE + 1 - CUR_CLQ_SIZE;
//			}
//		}
		return FALSE;
	}
}

//static int cut_by_iset_last_renumber() {
//	int i = ptr(Candidate_Stack) - 2, node;
//	LAST_IN = INT_MAX;
//	FIRST_INDEX = NONE;
//	iSET_COUNT = 0;
//	MAX_ISET_SIZE = MAX_CLQ_SIZE - CUR_CLQ_SIZE - 1;
//	for (node = Candidate_Stack[i]; node != DELIMITER; node =
//			Candidate_Stack[--i]) {
//		if (addIntoIsetTomitaBis(node) == FALSE && re_number(node) == FALSE) {
//			FIRST_INDEX = i;
//			for (node = Candidate_Stack[i]; node != DELIMITER; node =
//					Candidate_Stack[--i]) {
//				Candidate_Stack[i] = -node;
//			}
//			break;
//		}
//	}
//	if (FIRST_INDEX == NONE) {
//		cut_iset++;
//		Vertex_UB[CURSOR]=iSET_COUNT+1;
//		return TRUE;
//	} else {
////		i = ptr(Candidate_Stack) - 2;
////		for (node = Candidate_Stack[i]; node != DELIMITER; node =
////				Candidate_Stack[--i])
////			if (node > 0)
////				node_state[node] = ACTIVE;
////			else {
////				node_state[-node] = PASSIVE;
////				/*if (CUR_CLQ_SIZE > SWITCH_LEVEL && i > last_in)
////				 Vertex_UB[i] = MAX_ISET_SIZE + 1;*/
////			}
//		Branching_Point = FIRST_INDEX + 1;
//		return FALSE;
//	}
//}

/* static int cut_by_iset_last_renumber2() { */
/* 	int i = ptr(Candidate_Stack) - 2, node; */
/* 	FIRST_INDEX = NONE; */
/* 	iSET_COUNT = 0; */
/* 	MAX_ISET_SIZE = MAX_CLQ_SIZE - CUR_CLQ_SIZE - 1; */
/* 	for (node = Candidate_Stack[i]; node != DELIMITER; node = */
/* 			Candidate_Stack[--i]) { */
/* 		if (addIntoIsetTomitaBis(node) == FALSE) { */
/* 			Candidate_Stack[i] = -node; */
/* 			Vertex_UB[i] = MAX_ISET_SIZE + 1; */
/* 			if (FIRST_INDEX == NONE) */
/* 				FIRST_INDEX = i; */
/* 		} */
/* 	} */
/* 	if (FIRST_INDEX != NONE) { */
/* 		i = FIRST_INDEX; */
/* 		FIRST_INDEX = NONE; */
/* 		for (node = Candidate_Stack[i]; node != DELIMITER; node = */
/* 				Candidate_Stack[--i]) { */
/* 			if (node < 0) { */
/* 				if (re_number(-node) == TRUE) { */
/* 					Candidate_Stack[i] = -node; */
/* 					Vertex_UB[i] = MAX_ISET_SIZE; */
/* 				} else if (FIRST_INDEX == NONE) */
/* 					FIRST_INDEX = i; */
/* 			} */
/* 		} */
/* 	} */
/* 	if (FIRST_INDEX == NONE) { */
/* 		cut_iset++; */
/* 		Vertex_UB[CURSOR]=iSET_COUNT+1; */
/* 		return TRUE; */
/* 	} else { */
/* 		Branching_Point = FIRST_INDEX + 1; */
/* 		return FALSE; */
/* 	} */
/* } */
/* static int get_branches(int rollback) { */
/* 	int i = ptr(Candidate_Stack) - 2, node, nb = 0; */
/* 	for (node = Candidate_Stack[i]; node != DELIMITER; node = */
/* 			Candidate_Stack[--i]) { */
/* 		if (node < 0) { */
/* 			nb++; */
/* 			if (rollback == TRUE) */
/* 				Candidate_Stack[i] = -node; */
/* 		} */
/* 	} */
/* 	return nb; */
/* } */
/* static int compare_iset() { */
/* 	int result; */
/* 	cut_by_iset_first(); */
/* 	Branches_Nodes[1] += get_branches(1); */

/* 	cut_by_iset_last(); */
/* 	Branches_Nodes[3] += get_branches(1); */

/* 	cut_by_iset_last_renumber(); */
/* 	Branches_Nodes[4] += get_branches(1); */

/* 	cut_by_iset_last_renumber2(); */
/* 	Branches_Nodes[5] += get_branches(1); */

/* 	result = cut_by_iset_first_renumber(); */
/* 	Branches_Nodes[2] += get_branches(0); */

/* 	return result; */
/* } */

/* static int cut_by_iset_new() { */
/* 	int i = ptr(Candidate_Stack) - 2, node; */
/* 	FIRST_INDEX = NONE; */
/* 	iSET_COUNT = 0; */
/* 	MAX_ISET_SIZE = MAX_CLQ_SIZE - CUR_CLQ_SIZE - 1; */
/* 	for (node = Candidate_Stack[i]; node != DELIMITER; node = */
/* 			Candidate_Stack[--i]) { */
/* 		if (addIntoIsetTomitaBis(node) == TRUE || re_number(node) == TRUE) { */
/* 			node_state[node] = ACTIVE; */
/* 		} else { */
/* 			node_state[node] = PASSIVE; */
/* 			if (FIRST_INDEX == NONE) */
/* 				FIRST_INDEX = i; */
/* 		} */
/* 	} */
/* 	if (FIRST_INDEX == NONE) { */
/* 		cut_iset++; */
/* 		Vertex_UB[CURSOR]=iSET_COUNT+1; */
/* 		i = ptr(Candidate_Stack) - 2; */
/* 		for (node = Candidate_Stack[i]; node != DELIMITER; node = */
/* 				Candidate_Stack[--i]) */
/* 			node_state[node] = PASSIVE; */
/* 		return TRUE; */
/* 	} else { */
/* 		Branching_Point = FIRST_INDEX + 1; */
/* 		return FALSE; */
/* 	} */
/* } */

static int CONFLICT_ISET_STACK[tab_node_size * tab_node_size];
static int CONFLICT_ISET_STACK_fill_pointer;
static int ADDED_NODE_iSET[2 * tab_node_size];

#define assign_node(node, value, reason) {\
	node_state[node] = value;\
	node_reason[node] = reason;\
	push(node, FIXED_NODE_STACK);\
}
static int fix_newNode_for_iset(int fix_node, int fix_iset) {
	int idx, iset_idx;
	iSET_State[fix_iset] = PASSIVE;
	push(fix_iset, PASSIVE_iSET_STACK);
	assign_node(fix_node, P_FALSE, fix_iset);
//iSET_Potential[fix_iset] -= Node_Potential[fix_node];
	idx = ADDED_NODE_iSET[fix_node];
	while ((iset_idx = CONFLICT_ISET_STACK[idx++]) != NONE) {
		if (iSET_State[iset_idx] == ACTIVE) {
			iSET_Size[iset_idx]--;
			//iSET_ADD_Size[iset_idx]--;
			push(iset_idx, REDUCED_iSET_STACK);
			//iSET_Potential[iset_idx] -= Node_Potential[fix_node];
			if (iSET_Size[iset_idx] == 1)
				push(iset_idx, NEW_UNIT_STACK);
			else if (iSET_Size[iset_idx] == 0)
				return iset_idx;
		}
	}
	return NONE;
}

static int fix_oldNode_for_iset(int fix_node, int fix_iset) {
	int i, node, iset_idx, *noneibors;
	char *neibors;
	assign_node(fix_node, P_TRUE, fix_iset);
	iSET_State[fix_iset] = PASSIVE;
	push(fix_iset, PASSIVE_iSET_STACK);
	if (none_degree[fix_node] > (NB_CANDIDATE << 1)) {
		neibors = matrice[fix_node];
		i = ptr(Candidate_Stack) - 2;
		for (node = Candidate_Stack[i]; node != DELIMITER; node =
				Candidate_Stack[--i]) {
			if (node > 0 && neibors[node] == FALSE && node_state[node] == ACTIVE) {
				assign_node(node, P_FALSE, fix_iset);
				iset_idx = iSET_Index[node];
				if (iSET_State[iset_idx] == ACTIVE) {
					iSET_Size[iset_idx]--;
					push(iset_idx, REDUCED_iSET_STACK);
					if (iSET_Size[iset_idx] == 1) {
						push(iset_idx, NEW_UNIT_STACK);
					} else if (iSET_Size[iset_idx] == 0) {
						return iset_idx;
					}
				}
			}
		}
	} else {
		noneibors = none_neibors[fix_node];
		for (node = *noneibors; node != NONE; node = *(++noneibors)) {
			if (node_state[node] == ACTIVE) {
				assign_node(node, P_FALSE, fix_iset);
				iset_idx = iSET_Index[node];
				if (iSET_State[iset_idx] == ACTIVE) {
					iSET_Size[iset_idx]--;
					push(iset_idx, REDUCED_iSET_STACK);
					if (iSET_Size[iset_idx] == 1) {
						push(iset_idx, NEW_UNIT_STACK);
					} else if (iSET_Size[iset_idx] == 0) {
						return iset_idx;
					}
				}
			}
		}
	}
	return NONE;
}

#define fix_node(node,iset) ((node > NB_NODE)? fix_newNode_for_iset(node, iset):fix_oldNode_for_iset(node, iset))

static int fix_node_iset(int fix_iset) {
	int fix_node, *nodes = iSET[fix_iset];
	for (fix_node = *(nodes); fix_node != NONE; fix_node = *(++nodes)) {
		if (node_state[fix_node] == ACTIVE) {
			if (fix_node > NB_NODE)
				return fix_newNode_for_iset(fix_node, fix_iset);
			else
				return fix_oldNode_for_iset(fix_node, fix_iset);
		}
	}
	nodes = iSET[fix_iset];
	for (fix_node = *(nodes); fix_node != NONE; fix_node = *(++nodes)) {
		printf("iset=%d,node=%d,active=%d\n", fix_iset, fix_node,
				node_state[fix_node]);
	}
	printf("error in fix_node_iset\n");
	printf("iSET COUNT=%d\n", iSET_COUNT);
	print_all_iset();
	exit(0);
}

static int unit_iset_process() {
	int i = 0, j = 0, iset_idx, empty_iset;
	for (i = 0; i < ptr(UNIT_STACK); i++) {
		iset_idx = UNIT_STACK[i];
		if (iSET_State[iset_idx] == ACTIVE && iSET_Size[iset_idx] == 1) {
			ptr(NEW_UNIT_STACK) = 0;
			if ((empty_iset = fix_node_iset(iset_idx)) > NONE) {
				return empty_iset;
			} else {
				for (j = 0; j < ptr(NEW_UNIT_STACK); j++) {
					iset_idx = NEW_UNIT_STACK[j];
					if (iSET_State[iset_idx] == ACTIVE) {
						if ((empty_iset = fix_node_iset(iset_idx)) > NONE)
							return empty_iset;
					}
				}
			}
		}
	}
	ptr(NEW_UNIT_STACK) = 0;
	return NONE;
}

static int unit_iset_process_used_first() {
	int j, iset, iset_start = 0, used_iset_start = 0, my_iset;
	do {
		for (j = used_iset_start; j < ptr(NEW_UNIT_STACK); j++) {
			iset = NEW_UNIT_STACK[j];
			if (iSET_State[iset] == ACTIVE && iSET_Used[iset] == TRUE)
				if ((my_iset = fix_node_iset(iset)) != NONE)
					return my_iset;
		}
		used_iset_start = j;
		for (j = iset_start; j < ptr(NEW_UNIT_STACK); j++) {
			iset = NEW_UNIT_STACK[j];
			if (iSET_State[iset] == ACTIVE) {
				if ((my_iset = fix_node_iset(iset)) != NONE)
					return my_iset;
				iset_start = j + 1;
				break;
			}
		}
	} while (j < ptr(NEW_UNIT_STACK));
	return NONE;
}
//int unit_iset_process_used_first() {
//	int j, iset, my_iset;
//	for (j = 0; j < ptr(NEW_UNIT_STACK); j++) {
//		iset = NEW_UNIT_STACK[j];
//		if (iSET_State[iset] == ACTIVE) {
//			if ((my_iset = fix_node_iset(iset)) != NONE)
//				return my_iset;
//		}
//	}
//	return NONE;
//}
static int iSET_Involved[tab_node_size];
static int REASON_STACK[tab_node_size];
static int REASON_STACK_fill_pointer = 0;
static void identify_conflict_sets(int iset_idx) {
	int i, reason_start = ptr(REASON_STACK), iset, *nodes, node, reason_iset;
	push(iset_idx, REASON_STACK);
	iSET_Involved[iset_idx] = TRUE;
	for (i = reason_start; i < ptr(REASON_STACK); i++) {
		iset = REASON_STACK[i];
		nodes = iSET[iset];
		for (node = *nodes; node != NONE; node = *(++nodes))
			if (node_state[node] == P_FALSE && node_reason[node] != NO_REASON
					&& iSET_Involved[node_reason[node]] == FALSE) {
				reason_iset = node_reason[node];
				push(reason_iset, REASON_STACK);
				//node_reason[node] = NO_REASON;
				iSET_Involved[reason_iset] = TRUE;
			}
	}
	for (i = reason_start; i < ptr(REASON_STACK); i++) {
		iSET_Involved[REASON_STACK[i]] = FALSE;
		iSET_Used[REASON_STACK[i]] = TRUE;
	}
}
static void enlarge_conflict_sets() {
	int i, iset;
	node_state[ADDED_NODE] = ACTIVE;
	node_reason[ADDED_NODE] = NO_REASON;
//node_match_state[ADDED_NODE] = FALSE;
	ADDED_NODE_iSET[ADDED_NODE] = ptr(CONFLICT_ISET_STACK);
	for (i = 0; i < ptr(REASON_STACK); i++) {
		iset = REASON_STACK[i];
		if (iSET_Involved[iset] == FALSE) {
			iSET_Involved[iset] = TRUE;
			iSET[iset][iSET_Size[iset]++] = ADDED_NODE;
			iSET[iset][iSET_Size[iset]] = NONE;
			//assert(ptr(CONFLICT_ISET_STACK)<3*tab_node_size);
			push(iset, CONFLICT_ISET_STACK);
		}
	}
	push(NONE, CONFLICT_ISET_STACK);
	i = ADDED_NODE_iSET[ADDED_NODE];
//	while ((iset = CONFLICT_ISET_STACK[i++]) != NONE) {
//		iSET_Potential[iset] += Node_Potential[ADDED_NODE];
//	}
	for (i = 0; i < ptr(REASON_STACK); i++) {
		iSET_Involved[REASON_STACK[i]] = FALSE;
		iSET_Used[REASON_STACK[i]] = FALSE;
	}
	ptr(REASON_STACK) = 0;
	ADDED_NODE++;
}

static void rollback_context_for_maxsatz(int start_fixed, int start_passive,
		int start_reduced) {
	int i, node;
	for (i = start_fixed; i < ptr(FIXED_NODE_STACK); i++) {
		node = FIXED_NODE_STACK[i];
		node_state[node] = ACTIVE;
		node_reason[node] = NO_REASON;
	}
	ptr(FIXED_NODE_STACK) = start_fixed;
	for (i = start_passive; i < ptr(PASSIVE_iSET_STACK); i++) {
		iSET_State[PASSIVE_iSET_STACK[i]] = ACTIVE;
	}
	ptr(PASSIVE_iSET_STACK) = start_passive;
	for (i = start_reduced; i < ptr(REDUCED_iSET_STACK); i++) {
		iSET_Size[REDUCED_iSET_STACK[i]]++;
	}
	ptr(REDUCED_iSET_STACK) = start_reduced;
	ptr(NEW_UNIT_STACK) = 0;
}

static void reset_context_for_maxsatz() {
	int i, node;
	for (i = 0; i < ptr(FIXED_NODE_STACK); i++) {
		node = FIXED_NODE_STACK[i];
		node_state[node] = ACTIVE;
		node_reason[node] = NO_REASON;
	}
	ptr(FIXED_NODE_STACK) = 0;
	for (i = 0; i < ptr(PASSIVE_iSET_STACK); i++) {
		iSET_State[PASSIVE_iSET_STACK[i]] = ACTIVE;
	}
	ptr(PASSIVE_iSET_STACK) = 0;
	for (i = 0; i < ptr(REDUCED_iSET_STACK); i++) {
		iSET_Size[REDUCED_iSET_STACK[i]]++;
	}
	ptr(REDUCED_iSET_STACK) = 0;
	ptr(NEW_UNIT_STACK) = 0;
}
//static void identify_conflict_isets_for_matching(int iset_idx) {
//	int i, iset, *nodes, node, reason_iset, idx, reason_start =
//			ptr(REASON_STACK);
//	//ptr(REASON_STACK) = 0;
//	if (iset_idx != NONE) {
//		push(iset_idx, REASON_STACK);
//		iSET_Involved[iset_idx] = TRUE;
//	} else {
//		for (i = Matching_iSET_Point; i < ptr(Matched_iSET_Stack) - 1; i++) {
//			iset = Matched_iSET_Stack[i];
//			push(iset, REASON_STACK);
//			iSET_Involved[iset] = TRUE;
//		}
////		ptr(Matched_iSET_Stack) = Matching_iSET_Point;
////		for (i = Matching_Node_Point; i < ptr(Matched_Node_Stack) - 1; i++)
////			node_match_state[Matched_Node_Stack[i]] = FALSE;
////		ptr(Matched_Node_Stack) = Matching_Node_Point;
//	}
//	for (i = reason_start; i < ptr(REASON_STACK); i++) {
//		iset = REASON_STACK[i];
//		nodes = iSET[iset];
//		//printf("reason:%d \n", REASON_STACK[i]);
//		for (node = *nodes; node != NONE; node = *(++nodes)) {
//			if (node_state[node] == P_FALSE) {
//				if (node_reason[node] != NONE) {
//					if (node_reason[node] != NO_REASON
//							&& iSET_Involved[node_reason[node]] == FALSE) {
//						reason_iset = node_reason[node];
//						push(reason_iset, REASON_STACK);
//						node_reason[node] = NO_REASON;
//						iSET_Involved[reason_iset] = TRUE;
//					}
//				} else {
//					idx = node_matching_index[node];
//					while ((reason_iset = Matched_iSET_Stack[idx++]) != NONE)
//						if (iSET_Involved[reason_iset] == FALSE) {
//							push(reason_iset, REASON_STACK);
//							node_reason[node] = NO_REASON;
//							iSET_Involved[reason_iset] = TRUE;
//						}
//				}
//			}
//		}
//	}
//	for (i = reason_start; i < ptr(REASON_STACK); i++) {
//		iSET_Involved[REASON_STACK[i]] = FALSE;
//		iSET_Used[REASON_STACK[i]] = TRUE;
//	}
//}
static int further_test_reduced_iset(int start) {
	int i, chosen_iset, empty_iset, node, *nodes;
	int saved_fixed = ptr(FIXED_NODE_STACK);
	int start_passive = ptr(PASSIVE_iSET_STACK);
	int start_reduced = ptr(REDUCED_iSET_STACK);
	for (i = start; i < ptr(REDUCED_iSET_STACK); i++)
		iSET_Tested[REDUCED_iSET_STACK[i]] = FALSE;
	for (i = start; i < ptr(REDUCED_iSET_STACK); i++) {
		chosen_iset = REDUCED_iSET_STACK[i];
		if (iSET_Tested[chosen_iset] == FALSE
				&& iSET_State[chosen_iset] == ACTIVE
				&& iSET_Size[chosen_iset] == 2) {
			iSET_Tested[chosen_iset] = TRUE;
			nodes = iSET[chosen_iset];
			for (node = *nodes; node != NONE; node = *(++nodes)) {
				if (node_state[node] == ACTIVE && node > NB_NODE)
					break;
			}
			if (node == NONE) {
				nodes = iSET[chosen_iset];
				for (node = *nodes; node != NONE; node = *(++nodes)) {
					if (node_state[node] == ACTIVE) {
						ptr(NEW_UNIT_STACK) = 0;
						if ((empty_iset = fix_oldNode_for_iset(node,
								chosen_iset)) != NONE || (empty_iset =
								unit_iset_process_used_first()) != NONE) {
							iSET_Involved[chosen_iset] = TRUE;
							identify_conflict_sets(empty_iset);
							iSET_Involved[chosen_iset] = FALSE;
							rollback_context_for_maxsatz(saved_fixed,
									start_passive, start_reduced);
						} else {
							rollback_context_for_maxsatz(saved_fixed,
									start_passive, start_reduced);
							break;
						}
					}
				}
				if (node == NONE)
					return chosen_iset;
			}
		}
	}
	return NONE;
}

static int fix_anyNode_for_iset(int fix_node, int fix_iset) {
	if (fix_node > NB_NODE)
		return fix_newNode_for_iset(fix_node, fix_iset);
	else
		return fix_oldNode_for_iset(fix_node, fix_iset);
}
char tested[tab_node_size];
static int inc_maxsatz_lookahead_by_fl2() {
	int i, j, empty_iset, iset_idx, *nodes, node;
	int sn = FIXED_NODE_STACK_fill_pointer;
	int sp = PASSIVE_iSET_STACK_fill_pointer;
	int sr = REDUCED_iSET_STACK_fill_pointer;
	int rs = REASON_STACK_fill_pointer;
	for (i = 0; i < sr; i++) {
		tested[REDUCED_iSET_STACK[i]] = FALSE;
	}
	for (i = 0; i < sr; i++) {
		iset_idx = REDUCED_iSET_STACK[i];
		if (tested[iset_idx] == FALSE && iSET_State[iset_idx] == ACTIVE
				&& iSET_Size[iset_idx] == 2) {
			nodes = iSET[iset_idx];
			ptr(REASON_STACK) = rs;
			tested[iset_idx] = TRUE;
			for (node = *nodes; node != NONE; node = *(++nodes)) {
				if (node_state[node] == ACTIVE) {
					ptr(NEW_UNIT_STACK) = 0;
					if ((empty_iset = fix_anyNode_for_iset(node, iset_idx))
							!= NONE || (empty_iset =
							unit_iset_process_used_first()) != NONE
							|| (*(nodes + 1) == NONE && (empty_iset =
									further_test_reduced_iset(sr)) != NONE)) {
						identify_conflict_sets(empty_iset);
						rollback_context_for_maxsatz(sn, sp, sr);
					} else {
						rollback_context_for_maxsatz(sn, sp, sr);
						break;
					}
				}
			}
			if (node == NONE) {
				//reset_context_for_maxsatz();
				return TRUE;
			} else {
				for (j = rs; j < ptr(REASON_STACK); j++) {
					iSET_Involved[REASON_STACK[j]] = FALSE;
					iSET_Used[REASON_STACK[j]] = FALSE;
				}
				ptr(REASON_STACK) = rs;
			}
		}
	}
//reset_context_for_maxsatz();
	return FALSE;
}
/* static int maxsatz_by_remove_smaller_nodes(int end) { */
/* 	int i, node, *nodes, iset_idx, empty_iset, nb = 0; */
/* 	for (i = Rollback_Point; i < end; i++) { */
/* 		node = Candidate_Stack[i]; */
/* 		if (node_state[node] == ACTIVE) { */
/* 			iset_idx = iSET_Index[node]; */
/* 			nodes = iSET[iset_idx]; */
/* 			while (node != (*nodes)) */
/* 				++nodes; */
/* 			//assert((*nodes) == node); */
/* 			while (((*nodes) = (*(nodes + 1))) != NONE) */
/* 				++nodes; */
/* 			node_state[node] = PASSIVE; */
/* 			iSET_Size[iset_idx]--; */
/* 			//GUARD = node; */
/* 			if (iSET_Size[iset_idx] == 1) { */
/* 				push(iset_idx, NEW_UNIT_STACK); */
/* 				if ((empty_iset = unit_iset_process_used_first()) != NONE) { */
/* 					identify_conflict_sets(empty_iset); */
/* 					return TRUE; */
/* 				} */
/* 			} */
/* 			nb++; */
/* 		} */
/* 	} */
/* //	if (nb > 0) */
/* //		return inc_maxsatz_lookahead_by_fl2(); */
/* //	else */
/* 	return FALSE; */
/* } */
static int inc_maxsatz_on_last_iset(int end) {
	int empty_iset, node, *nodes, iset_idx = iSET_COUNT - 1;
	ptr(REASON_STACK) = 0;
	ptr(NEW_UNIT_STACK) = 0;
	ptr(FIXED_NODE_STACK) = 0;
	ptr(PASSIVE_iSET_STACK) = 0;
	ptr(REDUCED_iSET_STACK) = 0;
	nodes = iSET[iset_idx];
	for (node = *nodes; node != NONE; node = *(++nodes)) {
		if (node_state[node] == ACTIVE) {
			ptr(NEW_UNIT_STACK) = 0;
			if ((empty_iset = fix_oldNode_for_iset(node, iset_idx)) != NONE
					|| (empty_iset = unit_iset_process_used_first()) != NONE
					|| (empty_iset = unit_iset_process()) != NONE) {
				identify_conflict_sets(empty_iset);
				reset_context_for_maxsatz();
			} else if (inc_maxsatz_lookahead_by_fl2() == TRUE) {
				reset_context_for_maxsatz();
			}
//			else if (maxsatz_by_remove_smaller_nodes(end) == TRUE) {
//				reset_context_for_maxsatz();
//			}
			else {
				reset_context_for_maxsatz();
				break;
			}
		}
	}
	if (node == NONE) {
		enlarge_conflict_sets();
	}
	return node;
}

static int open_new_iset_old(int i) {
	int *current_set, node, iset_node, idx = 0;
	char *adjacent;
	iSET_Size[iSET_COUNT] = 0;
	iSET[iSET_COUNT][0] = NONE;
	
	iSET_Involved[iSET_COUNT]=FALSE;
	iSET_Used[iSET_COUNT] = FALSE;
	iSET_State[iSET_COUNT] = ACTIVE;

	while ((node = Candidate_Stack[i]) != DELIMITER) {
		if (node < 0) {
			node = -node;
			adjacent = matrice[node];
			current_set = iSET[iSET_COUNT];
			for (iset_node = *current_set; iset_node != NONE; iset_node =
					*(++current_set)) {
				if (adjacent[iset_node] == TRUE)
					break;
			}
			if (iset_node == NONE) {
				iSET_Size[iSET_COUNT]++;
				*(current_set) = node;
				*(++current_set) = NONE;
				iSET_Index[node] = iSET_COUNT;
				node_state[node] = ACTIVE;
				node_reason[node] = NO_REASON;
				Candidate_Stack[i] = node;
				Extra_Node_Stack[idx++] = node;
				Extra_Node_Stack[idx++] = i;
			} else {
				break;
			}
		}
		i--;
	}
	if (iSET_Size[iSET_COUNT] == 1) {
		push(UNIT_STACK[0], UNIT_STACK);
		UNIT_STACK[0] = iSET_COUNT;
	}
	iSET_COUNT++;
	Extra_Node_Stack[idx] = NONE;
	return i;
}

/* static int open_new_iset_new(int i, int *last_iset) { */
/* 	int *current_set, node, iset_node, last_idx = NONE; */
/* 	char *adjacent; */
/* 	iSET_Size[iSET_COUNT] = 0; */
/* 	iSET[iSET_COUNT][0] = NONE; */
/* 	iSET_Used[iSET_COUNT] = FALSE; */
/* 	iSET_State[iSET_COUNT] = ACTIVE; */

/* 	while ((node = Candidate_Stack[i]) != DELIMITER) { */
/* 		if (node_state[node] == PASSIVE) { */
/* 			adjacent = matrice[node]; */
/* 			current_set = iSET[iSET_COUNT]; */
/* 			for (iset_node = *current_set; iset_node != NONE; iset_node = */
/* 					*(++current_set)) { */
/* 				if (adjacent[iset_node] == TRUE) */
/* 					break; */
/* 			} */
/* 			if (iset_node == NONE) { */
/* 				iSET_Size[iSET_COUNT]++; */
/* 				*(current_set) = node; */
/* 				*(++current_set) = NONE; */
/* 				iSET_Index[node] = iSET_COUNT; */
/* 				node_state[node] = ACTIVE; */
/* 				node_reason[node] = NO_REASON; */
/* 				last_idx = i; */
/* 			} else { */
/* 				break; */
/* 			} */
/* 		} */
/* 		i--; */
/* 	} */

/* 	if (last_idx != NONE) { */

/* 		if (iSET_Size[iSET_COUNT] == 1) { */
/* 			push(UNIT_STACK[0], UNIT_STACK); */
/* 			UNIT_STACK[0] = iSET_COUNT; */
/* 		} */
/* 		if (node == DELIMITER) */
/* 			*last_iset = TRUE; */
/* 		else */
/* 			*last_iset = FALSE; */
/* 		iSET_COUNT++; */
/* 		return last_idx; */
/* 	} else { */
/* 		return NONE; */
/* 	} */
/* } */

int simple_further_test_node(int start) {
	int my_iset, saved_node_stack_fill_pointer,
			saved_passive_iset_stack_fill_pointer,
			saved_reduced_iset_stack_fill_pointer, chosen_iset, node, *nodes, i,
			j;
	int my_saved_node_stack_fill_pointer,
			my_saved_passive_iset_stack_fill_pointer,
			my_saved_reduced_iset_stack_fill_pointer, conflict = FALSE;

	saved_node_stack_fill_pointer = FIXED_NODE_STACK_fill_pointer;
	saved_passive_iset_stack_fill_pointer = PASSIVE_iSET_STACK_fill_pointer;
	saved_reduced_iset_stack_fill_pointer = REDUCED_iSET_STACK_fill_pointer;
	my_saved_node_stack_fill_pointer = FIXED_NODE_STACK_fill_pointer;
	my_saved_passive_iset_stack_fill_pointer = PASSIVE_iSET_STACK_fill_pointer;
	my_saved_reduced_iset_stack_fill_pointer = REDUCED_iSET_STACK_fill_pointer;

	for (i = start; i < ptr(REDUCED_iSET_STACK); i++)
		iSET_Tested[REDUCED_iSET_STACK[i]] = FALSE;
	for (i = start; i < ptr(REDUCED_iSET_STACK); i++) {
		chosen_iset = REDUCED_iSET_STACK[i];
		if (iSET_State[chosen_iset] == ACTIVE
				&& iSET_Tested[chosen_iset] == FALSE
				&& iSET_Size[chosen_iset] <= 2) {
			nodes = iSET[chosen_iset];
			iSET_Tested[chosen_iset] = TRUE;
			for (node = *nodes; node != NONE; node = *(++nodes)) {
				if (node <= NB_NODE && node_state[node] == ACTIVE) {
					ptr(NEW_UNIT_STACK) = 0;
					my_iset = fix_oldNode_for_iset(node, chosen_iset);
					if (my_iset == NONE)
						my_iset = unit_iset_process_used_first();
					rollback_context_for_maxsatz(
							my_saved_node_stack_fill_pointer,
							my_saved_passive_iset_stack_fill_pointer,
							my_saved_reduced_iset_stack_fill_pointer);
					if (my_iset != NONE) {
						assign_node(node, P_FALSE, NO_REASON);
						iSET_Size[chosen_iset]--;
						push(chosen_iset, REDUCED_iSET_STACK);
						if (iSET_Size[chosen_iset] == 1) {
							ptr(NEW_UNIT_STACK) = 0;
							push(chosen_iset, NEW_UNIT_STACK);
							if (unit_iset_process_used_first() != NONE) {
								conflict = TRUE;
								break;
							}
							for (j = my_saved_reduced_iset_stack_fill_pointer;
									j < ptr(REDUCED_iSET_STACK); j++)
								iSET_Tested[REDUCED_iSET_STACK[j]] = FALSE;
							my_saved_node_stack_fill_pointer =
									FIXED_NODE_STACK_fill_pointer;
							my_saved_passive_iset_stack_fill_pointer =
									PASSIVE_iSET_STACK_fill_pointer;
							my_saved_reduced_iset_stack_fill_pointer =
									REDUCED_iSET_STACK_fill_pointer;
						}
					}
				}
			}
			if (conflict == TRUE)
				break;
		}
	}
	rollback_context_for_maxsatz(saved_node_stack_fill_pointer,
			saved_passive_iset_stack_fill_pointer,
			saved_reduced_iset_stack_fill_pointer);
	if (conflict == TRUE)
		return chosen_iset;
	else
		return NONE;
}

int test_node_for_failed_nodes(int node, int iset) {
	int my_iset, saved_node_stack_fill_pointer,
			saved_passive_iset_stack_fill_pointer,
			saved_reduced_iset_stack_fill_pointer;

	saved_node_stack_fill_pointer = FIXED_NODE_STACK_fill_pointer;
	saved_passive_iset_stack_fill_pointer = PASSIVE_iSET_STACK_fill_pointer;
	saved_reduced_iset_stack_fill_pointer = REDUCED_iSET_STACK_fill_pointer;
	ptr(NEW_UNIT_STACK) = 0;
	if ((my_iset = fix_oldNode_for_iset(node, iset)) == NONE) {
		if ((my_iset = unit_iset_process_used_first()) == NONE) {
			my_iset = simple_further_test_node(
					saved_reduced_iset_stack_fill_pointer);
		}
	}
	rollback_context_for_maxsatz(saved_node_stack_fill_pointer,
			saved_passive_iset_stack_fill_pointer,
			saved_reduced_iset_stack_fill_pointer);
	return my_iset;
}
int test_by_eliminate_failed_nodes() {
	int node, my_iset, *nodes, conflict, false_flag;
	do {
		false_flag = 0;
		for (my_iset = iSET_COUNT - 1; my_iset >= 0; my_iset--) {
			if (iSET_State[my_iset] == ACTIVE) {
				nodes = iSET[my_iset];
				conflict = FALSE;
				ptr(NEW_UNIT_STACK) = 0;
				for (node = *nodes; node != NONE; node = *(++nodes)) {
					if (node <= NB_NODE&& node_state[node] == ACTIVE
					&& test_node_for_failed_nodes(node, my_iset)
					!= NONE) {ptr(NEW_UNIT_STACK) = 0;
					assign_node(node,P_FALSE, NO_REASON);
					false_flag++;
					iSET_Size[my_iset]--;
					push(my_iset, REDUCED_iSET_STACK);
					if (iSET_Size[my_iset] == 1) {
						push(my_iset, NEW_UNIT_STACK);
						break;
					} else if (iSET_Size[my_iset] == 0) {
						conflict = TRUE;
						break;
					}
				}
			}
				if (conflict == TRUE)
					break;
				else if (ptr(NEW_UNIT_STACK)
						> 0&& unit_iset_process_used_first() != NONE) {
					conflict = TRUE;
					break;
				}
			}
		}
	} while (false_flag > 1 && conflict == FALSE);
	reset_context_for_maxsatz();
	return conflict;
}

/* static int cut_by_inc_maxsat() { */
/* 	int i, j, node, flag = TRUE, last_iset; */
/* 	ADDED_NODE = NB_NODE + 1; */
/* 	ptr(CONFLICT_ISET_STACK) = 0; */
/* 	ptr(UNIT_STACK) = 0; */
/* 	cut_satz++; */
/* 	for (i = 0; i < iSET_COUNT; i++) { */
/* 		if (iSET_Size[i] == 1) */
/* 			push(i, UNIT_STACK); */
/* 	} */
/* 	while ((node = Candidate_Stack[FIRST_INDEX]) != DELIMITER) { */
/* 		if ((j = open_new_iset_new(FIRST_INDEX, &last_iset)) == NONE) { */
/* 			flag = TRUE; */
/* 			break; */
/* 		} */
/* 		if ((node = inc_maxsatz_on_last_iset(j)) == NONE) { */
/* 			FIRST_INDEX = j - 1; */
/* 		} else { */
/* 			if (last_iset == TRUE && test_by_eliminate_failed_nodes() == TRUE) { */
/* 				flag = TRUE; */
/* 			} else { */
/* 				while (Candidate_Stack[FIRST_INDEX] != node) */
/* 					FIRST_INDEX--; */
/* 				Branching_Point = FIRST_INDEX + 1; */
/* 				flag = FALSE; */
/* 				cut_satz--; */
/* 			} */
/* 			break; */
/* 		} */
/* 	} */

/* 	i = ptr(Candidate_Stack) - 2; */
/* 	while ((node = Candidate_Stack[i--]) != DELIMITER) { */
/* 		node_state[node] = PASSIVE; */
/* 	} */
/* 	if (flag == TRUE) { */
/* 		Vertex_UB[CURSOR]=MAX_CLQ_SIZE - CUR_CLQ_SIZE; */
/* 	} */
/* 	return flag; */
/* } */

static int cut_by_inc_maxsat_eliminate_first() {
	int i, j, k = 0, node;
	ADDED_NODE = NB_NODE + 1;
	ptr(CONFLICT_ISET_STACK) = 0;
	ptr(UNIT_STACK) = 0;
	cut_satz++;
	for (i = 0; i < iSET_COUNT; i++) {
	  iSET_State[i]=ACTIVE;
	  iSET_Involved[i]=FALSE;
	  iSET_Used[i]=FALSE;
        		if (iSET_Size[i] == 1)
			push(i, UNIT_STACK);
	}
	i = ptr(Candidate_Stack) - 2;
	for (node = Candidate_Stack[i]; node != DELIMITER; node =
			Candidate_Stack[--i]) {
		if (node > 0)
			node_state[node] = ACTIVE;
		else {
			node_state[-node] = PASSIVE;
		}
	}
	while ((node = Candidate_Stack[FIRST_INDEX]) != DELIMITER) {
		j = open_new_iset_old(FIRST_INDEX);
		if (Candidate_Stack[j] == DELIMITER
				&& test_by_eliminate_failed_nodes() == TRUE) {
			FIRST_INDEX = j;
			break;
		} else if ((node = inc_maxsatz_on_last_iset(-1)) == NONE) {
			FIRST_INDEX = j;
		} else {
			for (k = 0; Extra_Node_Stack[k] != node; k += 2)
				;
			FIRST_INDEX = Extra_Node_Stack[k + 1];
			Branching_Point = FIRST_INDEX + 1;

#ifdef SOMC
			for (k = FIRST_INDEX; Candidate_Stack[k] != DELIMITER; k--) {
				if (Candidate_Stack[k] > 0)
				Candidate_Stack[k] = -Candidate_Stack[k];
			}
#endif
#ifdef DOMC
			for (; Extra_Node_Stack[k] != NONE; k += 2)
			Candidate_Stack[Extra_Node_Stack[k + 1]] = -Extra_Node_Stack[k];

			for (k = FIRST_INDEX; Candidate_Stack[k] != DELIMITER; k--) {
				if (Candidate_Stack[k] < 0 && k > LAST_IN)
				Vertex_UB[k] = MAX_ISET_SIZE + 1;
			}
#endif
#ifdef MOMC
			int SoMC=0,DoMC=0;
			for (; Extra_Node_Stack[k] != NONE; k += 2)
			Candidate_Stack[Extra_Node_Stack[k + 1]] = -Extra_Node_Stack[k];

			if (STATIC_ORDERING == TRUE) {
				for (k = FIRST_INDEX; Candidate_Stack[k] != DELIMITER; k--) {
					SoMC++;
					if (Candidate_Stack[k] < 0) {
						DoMC++;
					}
				}
				if ((double) DoMC / (double) SoMC < Dynamic_Radio) {
					STATIC_ORDERING = FALSE;
				}
			}
			if (STATIC_ORDERING == TRUE) {
				for (k = FIRST_INDEX; Candidate_Stack[k] != DELIMITER; k--) {
					if (Candidate_Stack[k] > 0)
					Candidate_Stack[k] = -Candidate_Stack[k];
				}
			} else {
				for (k = FIRST_INDEX; Candidate_Stack[k] != DELIMITER; k--) {
					if (Candidate_Stack[k] < 0 && k > LAST_IN)
					Vertex_UB[k] = MAX_ISET_SIZE + 1;
				}
			}
#endif
			cut_satz--;
			break;
		}
	}

	i = ptr(Candidate_Stack) - 2;
	while ((node = Candidate_Stack[i--]) != DELIMITER) {
		if (node > 0)
			node_state[node] = PASSIVE;
		else
			node_state[-node] = PASSIVE;
	}

	if (Candidate_Stack[FIRST_INDEX] == DELIMITER) {
		Vertex_UB[CURSOR]=MAX_ISET_SIZE+1;
		return TRUE;
	}
	return FALSE;
}

//static int cut_by_inc_maxsat() {
//	int i, j, node, flag = TRUE, last_idx;
//	GUARD = DELIMITER;
//	ADDED_NODE = NB_NODE + 1;
//	ptr(CONFLICT_ISET_STACK) = 0;
//	ptr(UNIT_STACK) = 0;
//	cut_satz++;
//	for (i = 0; i < iSET_COUNT; i++) {
//		if (iSET_Size[i] == 1)
//			push(i, UNIT_STACK);
//	}
//	while ((node = Candidate_Stack[FIRST_INDEX]) != GUARD) {
//		j = open_new_iset_new(FIRST_INDEX);
//		if (Candidate_Stack[j] != GUARD) {
//			if ((node = inc_maxsatz_on_last_iset(j)) == NONE) {
//				FIRST_INDEX = j - 1;
//			} else {
//				if (Candidate_Stack[j] == DELIMITER
//						&& test_by_eliminate_failed_nodes() == TRUE) {
//					flag = TRUE;
//				} else {
//					while (Candidate_Stack[FIRST_INDEX] != node)
//						FIRST_INDEX--;
//					Branching_Point = FIRST_INDEX + 1;
//					flag = FALSE;
//					cut_satz--;
//				}
//				break;
//			}
//		} else {
//			break;
//		}
//	}
//
//	i = ptr(Candidate_Stack) - 2;
//	while ((node = Candidate_Stack[i--]) != DELIMITER) {
//		node_state[node] = PASSIVE;
//	}
//	if (Candidate_Stack[j] == GUARD && GUARD != DELIMITER) {
//		Branching_Point = j + 1;
//		flag = FALSE;
//		cut_satz--;
//	}
//	if (flag == TRUE) {
//		Vertex_UB[CURSOR]=MAX_CLQ_SIZE - CUR_CLQ_SIZE;
//	}
//	return flag;
//}

static void rebuild_matrix(int start) {
	int i = start, j = 1, node,  nb_non_neibors = 0;
	char * adj1;
	for (node = Candidate_Stack[i]; node != DELIMITER; node =
			Candidate_Stack[++i]) {
		Candidate_Stack[i] = j;
		memcpy(matrice[j], static_matrix + node * (NB_NODE + 1),
				(NB_NODE + 1) * sizeof(char));
		OLD_NEW[j++] = node;
	}
	for (i = 1; i <= NB_CANDIDATE; i++) {
		nb_non_neibors = 0;
		adj1 = matrice[i];
		for (j = 1; j <= NB_CANDIDATE; j++) {
			adj1[j] = adj1[OLD_NEW[j]];
			if (i != j && adj1[j] == FALSE)
				none_neibors[i][nb_non_neibors++] = j;

		}
		none_neibors[i][nb_non_neibors] = NONE;
		none_degree[i] = nb_non_neibors;
	}
	for (i = 1; i <= NB_CANDIDATE; i++) {
		qsort(none_neibors[i], none_degree[i], sizeof(int), none_degree_inc);
	}
}

static int cut_by_inc_ub() {
	int i = CURSOR, neibor, max = 0;
	int node=Candidate_Stack[CURSOR];
	int start=ptr(Candidate_Stack);
	char *neibors;
#ifndef SOMC
			if(CUR_CLQ_SIZE>0) {
				while(Candidate_Stack[i]!=DELIMITER)i--;
			}
#endif
			if(REBUILD_MATRIX==FALSE || CUR_CLQ_SIZE>0)
			neibors=matrice[node];
			else
			neibors=static_matrix+node*(NB_NODE+1);
			NB_CANDIDATE=0;
			for (neibor = Candidate_Stack[++i]; neibor != DELIMITER; neibor =
					Candidate_Stack[++i]) {
				if (neibor>0&&neibors[neibor] == TRUE) {
					if (max < Vertex_UB[i])
					max = Vertex_UB[i];
					Vertex_UB[ptr(Candidate_Stack)] = Vertex_UB[i];
					push(neibor, Candidate_Stack);
					NB_CANDIDATE++;
				}
			}
			push(DELIMITER, Candidate_Stack);
			if(NB_CANDIDATE<max)
			max=NB_CANDIDATE;
			if (Vertex_UB[CURSOR]-1 < max)
			max = Vertex_UB[CURSOR]-1;

			if (max < MAX_CLQ_SIZE - CUR_CLQ_SIZE) {
				Vertex_UB[CURSOR]=max+1;
				cut_inc++;
				return TRUE;
			} else if(REBUILD_MATRIX==TRUE&&CUR_CLQ_SIZE==0) {
				rebuild_matrix(start);
				return FALSE;
			} else {
				return FALSE;
			}

		}

//void print_candidate() {
//	int i = 0;
//	printf("\nC:");
//	for (i = 0; i < ptr(Candidate_Stack); i++)
//		if (i == CURSOR)
//		printf("(%d) ", Candidate_Stack[i]);
//		else
//		printf("%d ", Candidate_Stack[i]);
//	printf("\n");
//}
//void print_incub() {
//	int i = 0;
//	printf("B:");
//	for (i = 0; i < ptr(Candidate_Stack); i++)
//		if (i == CURSOR)
//		printf("(%d) ",Vertex_UB[i]);
//		else
//		printf("%d ",Vertex_UB[i]);
//	printf("\n");
//}
static int BRANCHING_COUNT = 0, LAST_BRANCHING_COUNT = 0;
struct rusage lasttime;
static void init_for_search(int using_init_clique) {
	int i;
	//char *adajecent;
	cut_ver = 0;
	cut_inc = 0;
	cut_iset = 0;
	cut_satz = 0;
	total_cut_ver = 0;
	total_cut_inc = 0;
	total_cut_iset = 0;
	total_cut_satz = 0;

	Branches_Nodes[0] = 0;
	Branches_Nodes[1] = 0;
	Branches_Nodes[2] = 0;
	Branches_Nodes[3] = 0;
	Branches_Nodes[4] = 0;
	Branches_Nodes[5] = 0;

	getrusage(RUSAGE_SELF, &lasttime);
	LAST_BRANCHING_COUNT=0;
	Last_Idx = NB_NODE;
	NB_BACK_CLIQUE = 0;
	MAX_CLQ_SIZE = 0;
	ptr(Clique_Stack) = 0;
	ptr(Cursor_Stack) = 0;
	Rollback_Point = 0;
	push(ptr(Candidate_Stack)-1, Cursor_Stack);
	if (using_init_clique == TRUE) {
		if (INIT_CLIQUE > 0)
			INIT_CLQ_SIZE = INIT_CLIQUE;
		MAX_CLQ_SIZE = INIT_CLQ_SIZE;
		memcpy(MaxCLQ_Stack, Clique_Stack, INIT_CLQ_SIZE * sizeof(int));
		printf("c the current maximal clique is %d\n", MAX_CLQ_SIZE);
	}
	for (i = 0; i < ptr(Candidate_Stack) - 1; i++) {
		Vertex_UB[i] = NB_NODE;
		node_state[Candidate_Stack[i]] = PASSIVE;
	}
//	if (MAX_CLQ_SIZE > 0) {
//		for (i = ptr(Candidate_Stack) - 2; i > 0; i--) {
//			max = 0;
//			adajecent = matrice[Candidate_Stack[i]];
//			for (j = ptr(Candidate_Stack) - 2; j > i; j--) {
//				if (adajecent[Candidate_Stack[j]] == TRUE && Vertex_UB[j] > max)
//					max = Vertex_UB[j];
//			}
//			if (max < MAX_CLQ_SIZE) {
//				Vertex_UB[i] = max + 1;
//			} else {
//				push(i + 1, Cursor_Stack);
//				//MAX_CLQ_SIZE=0;
//				break;
//			}
//		}
//		//MAX_CLQ_SIZE = 0;
//	}
}

static void store_maximum_clique(int node, int print_info) {
	if (REBUILD_MATRIX == TRUE && CUR_CLQ_SIZE > 0)
		push(OLD_NEW[node], Clique_Stack);
	else
		push(node, Clique_Stack);
	MAX_CLQ_SIZE = ptr(Clique_Stack);
	memcpy(MaxCLQ_Stack, Clique_Stack, MAX_CLQ_SIZE * sizeof(int));
	ptr(Candidate_Stack) = NB_NODE + 1;
	ptr(Cursor_Stack) = 1;
	ptr(Clique_Stack) = 0;
	Rollback_Point = 0;
	Vertex_UB[CURSOR]=MAX_CLQ_SIZE;
	if (print_info == TRUE)
		printf("c %4d |%5d |%8d %10d %10d %10d|%10d \n", MAX_CLQ_SIZE,
				Last_Idx - CURSOR,cut_ver,cut_inc, cut_iset, cut_satz,BRANCHING_COUNT);
	total_cut_ver += cut_ver;
	cut_ver = 0;
	total_cut_inc += cut_inc;
	cut_inc = 0;
	total_cut_iset += cut_iset;
	cut_iset = 0;
	total_cut_satz += cut_satz;
        cut_satz = 0;
	Last_Idx = CURSOR;
	getrusage(RUSAGE_SELF, &lasttime);
	LAST_BRANCHING_COUNT = BRANCHING_COUNT;
}

static void search_maxclique(int cutoff, int using_init_clique) {
	int node;
	init_for_search(using_init_clique);
	BRANCHING_COUNT = 0;
	if (using_init_clique == TRUE) {
		printf(
				"c  -----------------------------------------------------------------\n");
		printf(
				"c  Size| Index|NB_Vertex  NB_IncUB    NB_Iset  NB_MaxSat|  NB_Branch\n");
	}
	while (CURSOR> 0) {
		node=Candidate_Stack[--CURSOR];
		if(CUR_CLQ_SIZE>0 && node>0)
		continue;
		if(CUR_CLQ_SIZE==0) 
			STATIC_ORDERING=TRUE;
		if(node==DELIMITER) {
			ptr(Candidate_Stack)=CURSOR+1;
			ptr(Cursor_Stack)--;
			ptr(Clique_Stack)--;
			Vertex_UB[CURSOR]=MAX_CLQ_SIZE-CUR_CLQ_SIZE;
			if (cutoff>0 && ++NB_BACK_CLIQUE>cutoff)
			break;
		} else {
			BRANCHING_COUNT++;
			if(node<0) {
				node=-node;
				Candidate_Stack[CURSOR]=-Candidate_Stack[CURSOR];
			}
			if(MAX_CLQ_SIZE==CUR_CLQ_SIZE) {
				store_maximum_clique(node,using_init_clique);
			} else if(Vertex_UB[CURSOR] <= MAX_CLQ_SIZE - CUR_CLQ_SIZE) {
				cut_ver++;
			} else {
				Rollback_Point=ptr(Candidate_Stack);
				if(cut_by_inc_ub()==TRUE
				//||cut_by_iset_first()==TRUE
				//||cut_by_iset_first_renumber()==TRUE
				//||cut_by_iset_last()==TRUE
				||cut_by_iset_last_renumber()==TRUE
				//||cut_by_iset_last_renumber2()==TRUE
				//||compare_iset()==TRUE
				//|| cut_by_inc_maxsat()==TRUE
				|| cut_by_inc_maxsat_eliminate_first()==TRUE
				) {
					ptr(Candidate_Stack)=Rollback_Point;
				} else {
					if (REBUILD_MATRIX == TRUE && CUR_CLQ_SIZE > 0)
					push(OLD_NEW[node], Clique_Stack);
					else
					push(node, Clique_Stack);
					push(Branching_Point,Cursor_Stack);
				}
			}
		}
	}
	if (using_init_clique == TRUE) {
		printf("p %4d |%5d |%8d %10d %10d %10d|%10d \n", MAX_CLQ_SIZE,
				Last_Idx - CURSOR,cut_ver,cut_inc, cut_iset, cut_satz,BRANCHING_COUNT);
		total_cut_ver += cut_ver;
		total_cut_inc += cut_inc;
		total_cut_iset += cut_iset;
		total_cut_satz += cut_satz;
		printf(
				"c  ----------------------------------------------------------------\n");
		printf("c %4d |%5d |%8d %10d %10d %10d|%10d \n", MAX_CLQ_SIZE, CURSOR+1,total_cut_ver,total_cut_inc, total_cut_iset, total_cut_satz,BRANCHING_COUNT);
	}
}

static int sort_by_maxiset(int mandatory) {
	int i, node, nb_node, nb_isets = 0, ans = 0;
	int ordered_nodes[tab_node_size];
	complement_graph();
	ptr(Candidate_Stack) = 0;
	ptr(Tmp_Stack) = 0;
	for (node = 1; node <= NB_NODE; node++) {
		node_state[node] = ACTIVE;
		push(node, Candidate_Stack);
	}
	if (NB_NODE < 1000)
		my_sort_by_degree_dec();
	else
		my_sort_by_degree_inc();
	for (i = 0; i < ptr(Candidate_Stack); i++)
		ordered_nodes[i] = Candidate_Stack[i];
	nb_node = ptr(Candidate_Stack);
	push(DELIMITER, Candidate_Stack);
	while (ptr(Candidate_Stack) > 1) {
		MAX_CLQ_SIZE = 0;
		search_maxclique(50000, FALSE);
		for (i = 0; i < MAX_CLQ_SIZE; i++) {
			node = MaxCLQ_Stack[i];
			node_state[node] = NONE;
			push(node, Tmp_Stack);
		}
		push(NONE, Tmp_Stack);
		nb_isets++;
		ptr(Candidate_Stack) = 0;
		for (i = 0; i < nb_node; i++) {
			if (node_state[ordered_nodes[i]] != NONE)
				push(ordered_nodes[i], Candidate_Stack);
		}
		push(DELIMITER, Candidate_Stack);
		if (MAX_CLQ_SIZE == 1) {
			ans++;
		}
	}
	complement_graph();
	printf("c Iset size is %d\n", nb_isets);
	if (mandatory == FALSE && ans > 3
			&& ((double) nb_isets / (double) INIT_CLQ_SIZE) > 1.1) {
		return FALSE;
	}
	iSET_COUNT = 0;
	iSET_Size[iSET_COUNT] = 0;
	for (i = 0; i < ptr(Tmp_Stack); i++) {
		if (Tmp_Stack[i] != NONE) {
			iSET[iSET_COUNT][iSET_Size[iSET_COUNT]] = Tmp_Stack[i];
			iSET_Size[iSET_COUNT]++;
			iSET_Used[iSET_COUNT] += static_degree[Tmp_Stack[i]];
		} else {
			iSET[iSET_COUNT][iSET_Size[iSET_COUNT]] = NONE;
			iSET_COUNT++;
			iSET_Size[iSET_COUNT] = 0;
			iSET_Used[iSET_COUNT] = 0;
		}
	}
	sort_isets_and_push_nodes();
	//sort_isets_and_push_nodes2();
	//sort_isets_degreeSum_and_push_nodes();
	return TRUE;
}

static void init_for_maxclique(int ordering) {
	DENSITY = NB_EDGE * 100 * 2 / (NB_NODE * (NB_NODE - 1));
	int mandatory = FALSE;
	if (ordering > 0)
		mandatory = TRUE;

	if (ordering == 1) {
		printf("c Using the degeneracy ordering...\n");
	} else if (ordering == 2)
		printf("c Using the MaxIndSet ordering...\n");
	else if (ordering == -1) {
		if (DENSITY <= 60) {
			printf("c Using the degeneracy ordering...\n");
			ordering = 1;
		} else {
			printf("c Investigating the MaxIndSet ordering...\n");
			ordering = 2;
		}
	}
	Dynamic_Radio = 0.0;
	if (ordering == 1) {
		sort_by_active_degree();
		Dynamic_Radio = 0.6;
	} else if (sort_by_maxiset(mandatory) == FALSE) {
		printf(
				"c the MaxIndSet ordering disable, using the degeneracy ordering...\n");
		sort_by_active_degree();
		Dynamic_Radio = 0.6;
	} else {
		Dynamic_Radio = 0.1;
	}
	INIT_CLQ_SIZE = INIT_CLIQUE;
	MAX_CLQ_SIZE = INIT_CLIQUE;
	Mean_Dynamic_Radio = 0;
	Dynamic_Count = 0;
}

static void printMaxClique() {
	int i;
	printf("s ");
	if (REBUILD_MATRIX == TRUE) {
		for (i = 1; i < MAX_CLQ_SIZE; i++) {

		}
		for (i = 0; i < MAX_CLQ_SIZE; i++)
			printf("%d ", NEW_OLD[MaxCLQ_Stack[i]]);
	} else {
		for (i = 0; i < MAX_CLQ_SIZE; i++)
			printf("%d ", NEW_OLD[MaxCLQ_Stack[i]]);
	}
	printf("\n");
}
static void re_code() {
  int i, j, k, node, *noneibors, *address1, *address2;
	for (i = 1; i <= NB_NODE; i++) {
		for (j = 1; j <= NB_NODE; j++)
			matrice[i][j] = TRUE;
		matrice[i][i] = FALSE;

		node_state[i] = ACTIVE;
		NEW_OLD[i] = Candidate_Stack[i - 1];
		OLD_NEW[Candidate_Stack[i - 1]] = i;
	}
	for (i = 1; i <= NB_NODE; i++) {
		if (node_state[i] == ACTIVE) {
			k = i;
			address1 = none_neibors[k];
			do {
				node_state[k] = PASSIVE;
				k = OLD_NEW[k];
				address2 = none_neibors[k];
				none_neibors[k] = address1;
				address1 = address2;
			} while (node_state[k] == ACTIVE);
		}
	}
	for (i = 1; i <= NB_NODE; i++) {
		none_degree[i] = 0;
		noneibors = none_neibors[i];
		for (node = *noneibors; node != NONE; node = *(++noneibors)) {
			*noneibors = OLD_NEW[node];
			matrice[i][OLD_NEW[node]] = FALSE;
			none_degree[i]++;
		}
	}
	for (i = 0; i < NB_NODE; i++) {
		node_state[i + 1] = PASSIVE;
		Candidate_Stack[i] = i + 1;
	}
	if (DENSITY >= 49) {
		REBUILD_MATRIX = TRUE;
		for (i = 1; i <= NB_NODE; i++) {
			memcpy(static_matrix + i * (NB_NODE + 1), matrice[i],
					(NB_NODE + 1) * sizeof(char));
		}
	}
//	for (i = 0; i < NB_NODE; i++) {
//		printf("%d ", Candidate_Stack[i]);
//	}
//	printf("\n");
//	for (i = 1; i <= NB_NODE; i++) {
//		neibors = node_neibors[i];
//		printf("node %2d degree %2d neibors:", i, static_degree[i]);
//		for (node = *neibors; node != NONE; node = *(++neibors)) {
//			printf("%d ", node);
//		}
//		printf("\n");
//	}
}
/* static void print_sorted_nodes() { */
/* 	int i; */
/* 	for (i = 0; i < NB_NODE; i++) */
/* 		printf("%d ", Candidate_Stack[i]); */
/* 	printf("\n"); */
/* } */
void print_branches() {
	int i = 0;
	for (i = 0; i <= NB_NODE; i++) {
		printf("%d ", Branches[i]);
	}
	printf("\n");
}

void print_version() {
	printf("c Hello! I am IncMC2 built at %s %s.\n",__TIME__,__DATE__);
	return;
}

int main(int argc, char *argv[]) {
	struct rusage starttime, endtime;
	long sec, usec, sec_p, usec_p;
	int i, ordering = -1;
	INIT_CLIQUE = 0;
	print_version();
	if (argc > 3) {
		for (i = 2; i < argc; i++) {
			if (strcmp(argv[i], "-o") == 0) {
				sscanf(argv[++i], "%d", &ordering);
				printf("c the specified vertex ordering is %d\n", ordering);
			} else if (strcmp(argv[i], "-d") == 0) {
				sscanf(argv[++i], "%f", &Dynamic_Radio);
				printf("c the specified dynamic radio is %f\n", Dynamic_Radio);
			} else if (strcmp(argv[i], "-i") == 0) {
				sscanf(argv[++i], "%d", &INIT_CLIQUE);
				printf("c the specified init clique size is %d\n", INIT_CLIQUE);
			}
		}
	}
	printf("c reading %s ...\n", argv[1]);
	getrusage(RUSAGE_SELF, &starttime);
	if (build_simple_graph_instance(argv[1])) {
		search_initial_maximum_clique();
		init_for_maxclique(ordering);
		
		re_code();
		
		search_maxclique(0, TRUE);
		printMaxClique();
	}
	getrusage(RUSAGE_SELF, &endtime);
	sec = (int) endtime.ru_utime.tv_sec;
	usec = (int) endtime.ru_utime.tv_usec;
	sec_p = (int) lasttime.ru_utime.tv_sec;
	usec_p = (int) lasttime.ru_utime.tv_usec;


	
	printf(
			"s Instance %s Max_CLQ %d Branching %d Time %4.2lf ProveBranching %d ProveTime %4.2lf\n",
			argv[1], MAX_CLQ_SIZE, BRANCHING_COUNT,
			(double) (sec + (double) usec / 1000000),
			BRANCHING_COUNT - LAST_BRANCHING_COUNT,
			(double) (sec - sec_p + (double) (usec - usec_p) / (double) 1000000));
//	printf("ISET%s\t&%0.2lf\t&%0.2lf\t&%0.2lf\t&%0.2lf\t&%0.2lf\\\\\n", argv[1],
//			(double) Branches_Nodes[1] / (double) BRANCHING_COUNT,
//			(double) Branches_Nodes[2] / (double) BRANCHING_COUNT,
//			(double) Branches_Nodes[3] / (double) BRANCHING_COUNT,
//			(double) Branches_Nodes[4] / (double) BRANCHING_COUNT,
//			(double) Branches_Nodes[5] / (double) BRANCHING_COUNT);
//	print_branches();
	return TRUE;
}

