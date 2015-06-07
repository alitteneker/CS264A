#include "sat_api.h"

/******************************************************************************
 * We explain here the functions you need to implement
 *
 * Rules:
 * --You cannot change any parts of the function signatures
 * --You can/should define auxiliary functions to help implementation
 * --You can implement the functions in different files if you wish
 * --That is, you do not need to put everything in a single file
 * --You should carefully read the descriptions and must follow each requirement
 ******************************************************************************/

/******************************************************************************
 * Variables
 ******************************************************************************/

//returns a variable structure for the corresponding index
Var* sat_index2var(c2dSize i, const SatState* sat_state) {
    
    if( sat_state != NULL && i > 0 && i <= sat_state->variables_size )
        return sat_state->variables[ i - 1 ];
    return NULL;
}

//returns the index of a variable
c2dSize sat_var_index(const Var* var) {
    
    if(var != NULL)
        return var->index;
    return 0;
}

//returns the variable of a literal
Var* sat_literal_var(const Lit* lit) {
    
    if( lit != NULL )
        return lit->var_ptr;
    return NULL;
}

//returns 1 if the variable is instantiated, 0 otherwise
//a variable is instantiated either by decision or implication (by unit resolution)
BOOLEAN sat_instantiated_var(const Var* var) {
    
    if( var != NULL )
        return var->is_set;
    return 0;
}

//returns 1 if all the clauses mentioning the variable are subsumed, 0 otherwise
BOOLEAN sat_irrelevant_var(const Var* var) {
    long index;
    
    if( var == NULL )
        return 0;
    
    for(index = 0; index < var->used_clauses_size; ++index) {
        if( !var->used_clauses[index]->is_subsumed && !var->used_clauses[index]->was_generated )
            return 0;
    }
    return 1;
}

//returns the number of variables in the cnf of sat state
c2dSize sat_var_count(const SatState* sat_state) {
    
    if( sat_state != NULL ) {
        return sat_state->variables_size;
    }
    return 0;
}

//returns the number of clauses mentioning a variable
//a variable is mentioned by a clause if one of its literals appears in the clause
c2dSize sat_var_occurences(const Var* var) {
    
    if( var != NULL ) {
        unsigned long count = 0;
        for( unsigned long i = 0; i < var->used_clauses_size; ++i )
            if( !var->used_clauses[i]->was_generated )
                ++count;
        return count;
    }
    return 0;
}

//returns the index^th clause that mentions a variable
//index starts from 0, and is less than the number of clauses mentioning the variable
//this cannot be called on a variable that is not mentioned by any clause
Clause* sat_clause_of_var(c2dSize index, const Var* var) {
    
    if( var != NULL && index < var->used_clauses_size )
        return var->used_clauses[index];
    return NULL;
}

/******************************************************************************
 * Literals
 ******************************************************************************/

//returns a literal structure for the corresponding index
Lit* sat_index2literal(c2dLiteral index, const SatState* sat_state) {
    unsigned long u_index = labs(index);
    Var* var = sat_index2var(u_index, sat_state);
    if( var != NULL )
        return ( index < 0 ) ? var->neg_literal : var->pos_literal;
    return NULL;
}

//returns the index of a literal
c2dLiteral sat_literal_index(const Lit* lit) {
    
    if( lit != NULL )
        return lit->index;
    return 0;
}

//returns the positive literal of a variable
Lit* sat_pos_literal(const Var* var) {
    
    if( var != NULL )
        return var->pos_literal;
    return NULL;
}

//returns the negative literal of a variable
Lit* sat_neg_literal(const Var* var) {
    
    if( var != NULL )
        return var->neg_literal;
    return NULL;
}

//returns the opposite of the passed literal (pos if passed neg, neg if passed pos)
Lit* sat_opposite_literal(const Lit* lit) {
    if(lit == NULL)
        return NULL;
    return ( ( lit->index < 0 ) ? lit->var_ptr->pos_literal : lit->var_ptr->pos_literal );
}

//returns the asserted literal pertaining to this one, so this one if it is asserted, and it's negation if it is resolved
Lit* sat_asserted_iteral( const Lit* lit ) {
    if( lit == NULL || !lit->var_ptr->is_set )
        return NULL;
    return ( ( lit->var_ptr->set_sign == 1 ) ? lit->var_ptr->pos_literal : lit->var_ptr->neg_literal );
}
Lit* sat_resolved_iteral( const Lit* lit ) {
    if( lit == NULL || !lit->var_ptr->is_set )
        return NULL;
    return ( ( lit->var_ptr->set_sign == 0 ) ? lit->var_ptr->pos_literal : lit->var_ptr->neg_literal );
}

//returns 1 if the literal is implied, 0 otherwise
//a literal is implied by deciding its variable, or by inference using unit resolution
BOOLEAN sat_implied_literal(const Lit* lit) {
    
    if( lit != NULL )
        return lit->var_ptr->is_set && ( ( lit->index > 0 ) == ( lit->var_ptr->set_sign == 1 ) );
    return 0;
}

BOOLEAN set_literal(const Lit* lit) {
    
    if( lit != NULL )
        return lit->var_ptr->is_set;
    return 0;
}

BOOLEAN asserted_literal(const Lit* lit) {
    
    if( lit != NULL && lit->var_ptr->is_set && ( lit->var_ptr->set_sign == 1 ) == ( lit->index > 0 ) )
        return 1;
    return 0;
}

BOOLEAN resolved_literal(const Lit* lit) {
    
    if( lit != NULL && lit->var_ptr->is_set && ( lit->var_ptr->set_sign == 0 ) == ( lit->index > 0 ) )
        return 1;
    return 0;
}

//calculate the maximum level in the clause
unsigned long calc_decision_level(const Clause *clause) {
    unsigned long decision_level = 1;
    for( unsigned long index = 0; index < clause->elements_size; ++index ) {
        if( clause->elements[index]->var_ptr->is_set && clause->elements[index]->var_ptr->decision_level > decision_level )
            decision_level = clause->elements[index]->var_ptr->decision_level;
    }
    return decision_level;
}

//mark this clause as needing to be checked, and add it to the circular queue of
BOOLEAN mark_check_clause(Clause* clause, SatState *sat_state) {
    if( clause == NULL || sat_state == NULL || clause->needs_checking || clause->is_subsumed
       || ( !clause->watch_1->var_ptr->is_set && !clause->watch_2->var_ptr->is_set && clause->watch_1 != clause->watch_2 ) )
        return 0;

    clause->needs_checking = 1;
    if( sat_state->clauses_to_check_end == sat_state->clauses_capacity )
        sat_state->clauses_to_check_end = 0;
    sat_state->clauses_to_check[sat_state->clauses_to_check_end] = clause;
    ++sat_state->clauses_to_check_end;
    
    return 1;
}

BOOLEAN check_clause( Clause* clause, SatState *sat_state );

// return the decision level found
c2dSize apply_literal(Lit* lit, Clause* clause, SatState* sat_state) {
    
    if( lit == NULL || set_literal(lit) )
        return 0;
    
    Var *var = lit->var_ptr;
    var->set_sign = lit->index > 0;
    var->implication_clause = clause;
    var->decision_level =
        ( clause != NULL ) ? calc_decision_level(clause) : ( sat_state->decisions_size + 2 );
    lit->var_ptr->is_set = 1;
    
    // flag all the clauses that use this new setting
    unsigned long index;
    for( index = 0; index < var->pos_literal->used_clauses_size; ++index ) {
        if( var->pos_literal->used_clauses[index]->is_subsumed )
            continue;
        if( var->set_sign == 1 )
            var->pos_literal->used_clauses[index]->is_subsumed = 1;
        else
            mark_check_clause(var->pos_literal->used_clauses[index], sat_state);
    }
    for( index = 0; index < var->neg_literal->used_clauses_size; ++index ) {
        if( var->neg_literal->used_clauses[index]->is_subsumed )
            continue;
        if( var->set_sign == 0 )
            var->neg_literal->used_clauses[index]->is_subsumed = 1;
        else
            mark_check_clause(var->neg_literal->used_clauses[index], sat_state);
    }
    
    return lit->var_ptr->decision_level;
}

BOOLEAN unapply_literal(Lit *lit, SatState* sat_state) {
    
    if( lit == NULL || !asserted_literal(lit) )
        return 0;
    
    unsigned long index, vi;
    Var *var = lit->var_ptr;
    var->is_set = 0;
    
    if( var->set_sign == 1 ) {
        for( index = 0; index < var->pos_literal->used_clauses_size; ++index ) {
            if( var->pos_literal->used_clauses[index]->is_subsumed ) {
                var->pos_literal->used_clauses[index]->is_subsumed = 0;
                for( vi = 0; vi < var->pos_literal->used_clauses[index]->elements_size; ++vi )
                    if( asserted_literal(var->pos_literal->used_clauses[index]->elements[vi]) )
                        var->pos_literal->used_clauses[index]->is_subsumed = 1;
                mark_check_clause(var->pos_literal->used_clauses[index], sat_state);
            }
        }
    }
    else {
        for( index = 0; index < var->neg_literal->used_clauses_size; ++index ) {
            if( var->neg_literal->used_clauses[index]->is_subsumed ) {
                var->neg_literal->used_clauses[index]->is_subsumed = 0;
                for( vi = 0; vi < var->neg_literal->used_clauses[index]->elements_size; ++vi )
                    if( asserted_literal(var->neg_literal->used_clauses[index]->elements[vi]) )
                        var->neg_literal->used_clauses[index]->is_subsumed = 1;
                mark_check_clause(var->neg_literal->used_clauses[index], sat_state);
            }
        }
    }

    return 1;
}

//sets the literal to true, and then runs unit resolution
//returns a learned clause if unit resolution detected a contradiction, NULL otherwise
//
//if the current decision level is L in the beginning of the call, it should be updated
//to L+1 so that the decision level of lit and all other literals implied by unit resolution is L+1
Clause* sat_decide_literal(Lit* lit, SatState* sat_state) {
    
    if( sat_state == NULL || lit == NULL || lit->var_ptr->is_set || sat_state->decisions_size == sat_state->variables_size )
        return NULL;

    apply_literal(lit, NULL, sat_state);
    sat_state->decisions[ sat_state->decisions_size++ ] = lit;
    return sat_unit_resolution(sat_state) ? NULL : sat_state->assertion_clause;
}

BOOLEAN imply_literal(Lit *lit, Clause *clause, SatState *sat_state) {
    
    if( sat_state == NULL || lit == NULL || set_literal(lit) )
        return 0;

    unsigned long decision_level = apply_literal(lit, clause, sat_state);
    if( decision_level > 1 ) {
        Var* dec = sat_state->decisions[ decision_level-2 ]->var_ptr;
        dec->implications[ dec->implications_size++ ] = lit;
    }
    
    return 1;
}

//undoes the last literal decision and the corresponding implications obtained by unit resolution
//
//if the current decision level is L in the beginning of the call, it should be updated
//to L-1 before the call ends
void sat_undo_decide_literal(SatState* sat_state) {
    
    if( sat_state == NULL || sat_state->decisions_size == 0 )
        return;
    
    Lit* decision = sat_state->decisions[ sat_state->decisions_size-1 ];
    for( unsigned long index = 0; index < decision->var_ptr->implications_size; ++index ) {
        unapply_literal(decision->var_ptr->implications[index], sat_state);
    }
    decision->var_ptr->implications_size = 0;
    unapply_literal(decision, sat_state);
    
    --sat_state->decisions_size;
}

/******************************************************************************
 * Clauses
 ******************************************************************************/

//returns a clause structure for the corresponding index
Clause* sat_index2clause(c2dSize index, const SatState* sat_state) {
    
    if( sat_state != NULL && index > 0 && index <= sat_state->clauses_size )
        return sat_state->clauses[index-1];
    return NULL;
}

//returns the index of a clause
c2dSize sat_clause_index(const Clause* clause) {
    
    if( clause != NULL )
        return clause->index;
    return 0;
}

//returns the literals of a clause
Lit** sat_clause_literals(const Clause* clause) {
    
    if( clause != NULL )
        return clause->elements;
    return NULL;
}

//returns the number of literals in a clause
c2dSize sat_clause_size(const Clause* clause) {
    
    if( clause != NULL )
        return clause->elements_size;
    return 0;
}

//returns 1 if the clause is subsumed, 0 otherwise
BOOLEAN sat_subsumed_clause(const Clause* clause) {
    
    if( clause != NULL )
        return clause->is_subsumed;
    return 0;
}

//returns the number of clauses in the cnf of sat state
c2dSize sat_clause_count(const SatState* sat_state) {
    
    if( sat_state != NULL )
        return sat_state->clauses_size - sat_state->assertion_clause_count;
    return 0;
}

//returns the number of learned clauses in a sat state (0 when the sat state is constructed)
c2dSize sat_learned_clause_count(const SatState* sat_state) {
    
    if( sat_state != NULL )
        return sat_state->assertion_clause_count;
    return 0;
}

// resize the list of clauses for something when we run out of room
Clause** resize_clause_list(Clause** original, c2dSize original_start, c2dSize original_end, c2dSize original_capacity, c2dSize new_capacity) {
    
    Clause **expand = malloc(new_capacity * sizeof(Clause*));
    
    // copy over the memory into the new block, making sure to make the new version is contiguous
    unsigned long index = 0, j;
    if( original_start < original_end ) {
        for( j = original_start; j < original_end; ++j )
            expand[index++] = original[j];
    }
    else if( original_start != original_end ) {
        for( j = original_start; j < original_capacity; ++j )
            expand[index++] = original[j];
        for( j = 0; j < original_end; ++j )
            expand[index++] = original[j];
    }
    
    free(original);
    return expand;
}

//adds clause to the set of learned clauses, and runs unit resolution
//returns a learned clause if unit resolution finds a contradiction, NULL otherwise
//
//this function is called on a clause returned by sat_decide_literal() or sat_assert_clause()
//moreover, it should be called only if sat_at_assertion_level() succeeds
Clause* sat_assert_clause(Clause* clause, SatState* sat_state) {
    unsigned long index;
    Var* var;
    Lit* lit;
    
    if( sat_state == NULL || clause == NULL ) {
        return 0;
    }
    
    clause->index = sat_state->clauses_size;
    clause->watch_1 = clause->elements[0];
    clause->watch_2 = clause->elements[0];
    clause->needs_checking = 0;
    clause->is_subsumed = 0;
    
    for( index = 0; index < clause->elements_size; ++index ) {
        
        lit = clause->elements[index];
        var = lit->var_ptr;
        
        if( lit->used_clauses_capacity == lit->used_clauses_size ) {
            lit->used_clauses = resize_clause_list( lit->used_clauses, 0, lit->used_clauses_size, lit->used_clauses_capacity, lit->used_clauses_capacity * 2 );
            lit->used_clauses_capacity *= 2;
        }
        lit->used_clauses[ lit->used_clauses_size++ ] = clause;
        
        if( var->used_clauses_capacity == var->used_clauses_size ) {
            var->used_clauses = resize_clause_list( var->used_clauses, 0, var->used_clauses_size, var->used_clauses_capacity, var->used_clauses_capacity * 2 );
            var->used_clauses_capacity *= 2;
        }
        var->used_clauses[ var->used_clauses_size++ ] = clause;
    }
    
    if( sat_state->clauses_capacity == sat_state->clauses_size ) {
        sat_state->clauses = resize_clause_list( sat_state->clauses, 0, sat_state->clauses_size, sat_state->clauses_capacity, sat_state->clauses_capacity * 2 );
        
        sat_state->clauses_to_check = resize_clause_list( sat_state->clauses_to_check, sat_state->clauses_to_check_start, sat_state->clauses_to_check_end, sat_state->clauses_capacity, sat_state->clauses_capacity * 2 );
        
        sat_state->clauses_to_check_end =
            ( sat_state->clauses_to_check_start < sat_state->clauses_to_check_end )
            ? ( sat_state->clauses_to_check_end - sat_state->clauses_to_check_start )
            : ( sat_state->clauses_to_check_end + ( sat_state->clauses_capacity - sat_state->clauses_to_check_start ) );
        sat_state->clauses_to_check_start = 0;
        sat_state->clauses_capacity *= 2;
    }
    sat_state->clauses[ sat_state->clauses_size ] = clause;
    ++sat_state->clauses_size;

    ++sat_state->assertion_clause_count;
    if( clause == sat_state->assertion_clause )
        sat_state->assertion_clause = NULL;
    else
        printf("Trying to assert a clause we did not generate.");
    
    if( !check_clause(clause, sat_state) || !sat_unit_resolution(sat_state) )
        return sat_state->assertion_clause;

    return  NULL;
}

/******************************************************************************
 * A SatState should keep track of pretty much everything you will need to
 * condition/uncondition variables, perform unit resolution, and do clause learning
 *
 * Given an input cnf file you should construct a SatState
 *
 * This construction will depend on how you define a SatState
 * Still, you should at least do the following:
 * --read a cnf (in DIMACS format, possible with weights) from the file
 * --initialize variables (n of them)
 * --initialize literals  (2n of them)
 * --initialize clauses   (m of them)
 *
 * Once a SatState is constructed, all of the functions that work on a SatState
 * should be ready to use
 *
 * You should also write a function that frees the memory allocated by a
 * SatState (sat_state_free)
 ******************************************************************************/

BOOLEAN in_used_clause(Clause** used_clauses, c2dSize clause_index, c2dSize cls_size) {
    for( unsigned long i = 0; i < cls_size; i++ ) {
        if( used_clauses[i]->index == clause_index )
            return 1;
    }
    return 0;
}
long get_numbers(const char *line, long **vars, size_t num_vars) {
    long i, x;
    long *tmp;
    const char *p, *q;
    
    if(vars == NULL)
        return 0;
    
    tmp = (long*)malloc(num_vars * sizeof(long));
    
    p = line;
    q = NULL;
    
    for(i=0; i < num_vars; i++){
        while(*p!=0 && isspace(*p)) p++;
        q = p;
        while(*q!=0 && !isspace(*q)) q++;
        while(*q!=0 && isspace(*q)) q++;
        
        if(p==q)
            break;
        
        if(sscanf(p, "%ld", &x) != 1) {
            free(tmp);
            tmp = NULL;
            return 0;
        }
        
        if(x == 0)
            break;
        tmp[i] = x;
        p = q;
    }
    *vars = tmp;
    return i;
}

SatState* sat_state_new(const char* cnf_fname) {
    SatState *ret;
    FILE *fp;
    
    int num_clause;
    size_t n;
    char *buffer;
    unsigned long i;
    
    // testing the file
    if((fp=fopen(cnf_fname, "r")) == NULL)
        return NULL;
    
    num_clause = 0;
    n = 80;
    ret = (SatState *) malloc( sizeof(SatState) );
    memset(ret, 0x00, sizeof(SatState));
    
    buffer = (char *)malloc(n * sizeof(char));
    
    while(getline(&buffer, &n, fp) != -1) {
        
        char fst_char = buffer[0];
        i = 0;
        while( fst_char == ' ' )
            fst_char = buffer[++i];

        if( fst_char == '0' || fst_char == '\n' || fst_char == 'c' )
            continue;
        
        else if(fst_char== 'p') {
            
            if(sscanf(buffer, "p cnf %lu %lu", &ret->variables_size, &ret->clauses_size) != 2)
                exit(EXIT_FAILURE);
            ret->literals_size = ret->variables_size * 2;
            
            //allocating memories for attributes for sat_state
            ret->variables = (Var**)malloc(ret->variables_size *sizeof(Var *));
            for(int i = 0; i < ret->variables_size; i++) {
                ret->variables[i] = (Var*)malloc(sizeof(Var));
            }
            
            ret->literals = (Lit**)malloc(ret->literals_size * sizeof(Lit *));
            for(unsigned long i = 0; i < ret->literals_size ; i++) {
                ret->literals[i] = (Lit*)malloc(sizeof(Lit));
            }
            
            ret->clauses_capacity = ret->clauses_size * 4;
            ret->clauses          = (Clause**) malloc( ret->clauses_capacity * sizeof(Clause*) );
            ret->clauses_to_check = (Clause**) malloc( ret->clauses_capacity * sizeof(Clause*) );
            ret->clauses_to_check_start = 0;
            ret->clauses_to_check_end   = 0;
            for(int i = 0; i < ret->clauses_size ; i++) {
                ret->clauses[i] = (Clause*)malloc(sizeof(Clause));
                ret->clauses[i]->is_subsumed   = 0;
                ret->clauses[i]->was_generated = 0;
            }
            
            ret->decisions    = (Lit**) malloc( ret->variables_size * sizeof(Lit*) );
            ret->decisions_size    = 0;
            
            
            //initialize variables
            for( int i = 0 ; i < ret-> variables_size; i++){
                ret->variables[i]->index = i + 1;
                ret->variables[i]->mark  = 0;
                ret->variables[i]->assertion_list = ret->variables[i]->assertion_use = 0;
                
                ret->variables[i]->used_clauses = (Clause **)malloc( 2 * ret->clauses_size * sizeof(Clause*) );
                ret->variables[i]->used_clauses_capacity = 2*ret->clauses_size;
                ret->variables[i]->used_clauses_size = 0;
                
                ret->variables[i]->implications = (Lit**)malloc( ret->variables_size * sizeof(Lit*) );
                ret->variables[i]->implications_size = 0;
            }
            
            //initialize literals
            long k = 1, j;
            for(i=0, j = 0; j < ret->literals_size; j+=2,i++ ) {
                ret->literals[j]->index   = k;                 ret->literals[j+1]->index   = -(k);
                ret->literals[j]->var_ptr = ret->variables[i]; ret->literals[j+1]->var_ptr = ret->variables[i];
                
                ret->literals[ j ]->used_clauses_size = 0;
                ret->literals[ j ]->used_clauses_capacity = 2 * ret->clauses_size;
                ret->literals[ j ]->used_clauses = (Clause **)malloc( ret->literals[j]->used_clauses_capacity * sizeof(Clause*) );
                ret->variables[i]->pos_literal = ret->literals[j];
                
                ret->literals[j+1]->used_clauses_size = 0;
                ret->literals[j+1]->used_clauses_capacity = 2 * ret->clauses_size;
                ret->literals[j+1]->used_clauses = (Clause **)malloc( ret->literals[j+1]->used_clauses_capacity * sizeof(Clause*) );
                ret->variables[i]->neg_literal = ret->literals[j+1];
                
                k++;
            }
            ret->literals_size = ret->variables_size*2;
            continue;
        }
        //else it's the clauses
        else if( !(fst_char >= 'a' && fst_char <= 'z') && num_clause < ret->clauses_size) {
            
            //initialize clauses
            long *vals;
            Lit** element_array = NULL;
            long n = get_numbers(buffer, &vals, ret->variables_size);
            
            element_array = (Lit**) malloc( n * sizeof(Lit*) );
            ret->clauses[num_clause]->mark           = 0;
            ret->clauses[num_clause]->is_subsumed    = 0;
            ret->clauses[num_clause]->was_generated  = 0;
            ret->clauses[num_clause]->needs_checking = 0;
            ret->clauses[num_clause]->elements       = element_array;
            ret->clauses[num_clause]->elements_size  = n;
            ret->clauses[num_clause]->index          = num_clause + 1;
            
            for( i = 0; i < n; ++i ) {
                // assignment for literals in this clause cls[num_clause]
                element_array[i] = vals[i] > 0 ? ret->variables[ vals[i]-1 ]->pos_literal : ret->variables[ -vals[i] - 1 ]->neg_literal;
                
                //setting the used_clauses for variables that appear in the clause
                if( !in_used_clause(element_array[i]->var_ptr->used_clauses, num_clause+1, element_array[i]->var_ptr->used_clauses_size) ) {
                    element_array[i]->var_ptr->used_clauses[element_array[i]->var_ptr->used_clauses_size] = ret->clauses[num_clause];
                    ++element_array[i]->var_ptr->used_clauses_size;
                }
                if( !in_used_clause(element_array[i]->used_clauses, num_clause+1, element_array[i]->used_clauses_size) ) {
                    element_array[i]->used_clauses[element_array[i]->used_clauses_size] = ret->clauses[num_clause];
                    ++element_array[i]->used_clauses_size;
                }
            }
            
            // initialize the watches with a usable value
            ret->clauses[num_clause]->watch_1 = ret->clauses[num_clause]->watch_2 = element_array[0];
            ++num_clause;
        }
        else {
            continue;
        }
        
    }
    fclose(fp);
    
    for( i= 0; i < ret->clauses_size; ++i ) {
        mark_check_clause(ret->clauses[i], ret);
    }
    return ret;
}
//frees the SatState
void sat_state_free(SatState* sat_state) {
    c2dSize index;
    
    if( sat_state == NULL )
        return;
    
    for( index = 0; index < sat_state->clauses_size; ++index ) {
        free(sat_state->clauses[index]->elements);
        free(sat_state->clauses[index]);
    }
    free(sat_state->clauses);
    free(sat_state->clauses_to_check);
    
    for( index = 0; index < sat_state->variables_size; ++index ) {
        free(sat_state->variables[index]->pos_literal->used_clauses);
        free(sat_state->variables[index]->pos_literal);
        free(sat_state->variables[index]->neg_literal->used_clauses);
        free(sat_state->variables[index]->neg_literal);
        free(sat_state->variables[index]->implications);
        free(sat_state->variables[index]->used_clauses);
        free(sat_state->variables[index]);
    }
    free(sat_state->literals);
    free(sat_state->variables);
    free(sat_state->decisions);
    
    free(sat_state);
}

/******************************************************************************
 * Given a SatState, which should contain data related to the current setting
 * (i.e., decided literals, subsumed clauses, decision level, etc.), this function
 * should perform unit resolution at the current decision level
 *
 * It returns 1 if succeeds, 0 otherwise (after constructing an asserting
 * clause)
 *
 * There are three possible places where you should perform unit resolution:
 * (1) after deciding on a new literal (i.e., in sat_decide_literal())
 * (2) after adding an asserting clause (i.e., in sat_assert_clause(...))
 * (3) neither the above, which would imply literals appearing in unit clauses
 *
 * (3) would typically happen only once and before the other two cases
 * It may be useful to distinguish between the above three cases
 *
 * Note if the current decision level is L, then the literals implied by unit
 * resolution must have decision level L
 *
 * This implies that there must be a start level S, which will be the level
 * where the decision sequence would be empty
 *
 * We require you to choose S as 1, then literals implied by (3) would have 1 as
 * their decision level (this level will also be the assertion level of unit
 * clauses)
 *
 * Yet, the first decided literal must have 2 as its decision level
 ******************************************************************************/

// this will actually build the new clause
void generate_assertion_clause(Clause *conflict_clause, SatState *sat_state) {
    unsigned long index, i, list_size, real_list_size, count, decision_level, last_remove;
    long assertion_level;
    Lit **list;
    Clause *clause;
    
    // this would indicate we have a truly unsat result (conflict through only unit clause implications)
    decision_level = calc_decision_level(conflict_clause);
    if( decision_level == 1 ) {
        printf("------Found base contradiction.------\n");
        conflict_clause->assertion_level = 0;
        sat_state->assertion_clause = conflict_clause;
        return;
    }
    
    list = malloc( sat_state->variables_size * sizeof(Lit*) );
    list_size = 0;
    real_list_size = 0;
    count = 0;
    
    // seed the list with the literals from the conflict clause
    for( index = 0; index < conflict_clause->elements_size; ++index ) {
        if( conflict_clause->elements[index]->var_ptr->assertion_list )
            continue;
        list[list_size] = sat_resolved_iteral( conflict_clause->elements[index] );
        list[list_size]->var_ptr->assertion_use = 1;
        list[list_size]->var_ptr->assertion_list = 1;
        if( list[list_size]->var_ptr->decision_level == decision_level )
            ++count;
        ++list_size;
    }
    real_list_size = list_size;
    
    // main loop here: find the fuip and generate the list of literals at the same time
    last_remove = 0;
    while( 1 ) {
        
        if( count == 1 ) {
            // we're done!
            break;
        }
        else {
            for( index = 0; index < list_size; ++index ) {
                // we have more than one thing at the current decision level: therefore we have not yet found the uip
                // find the first list item which is not a decision, and add the literals which implied it to our list
                if(   list[index]->var_ptr->decision_level == decision_level
                   && list[index]->var_ptr->assertion_use
                   && list[index]->var_ptr->implication_clause != NULL
                   ) {
                    
                    last_remove = index;
                    list[index]->var_ptr->assertion_use = 0;
                    --real_list_size;
                    --count;
                    for( i = 0; i < list[index]->var_ptr->implication_clause->elements_size; ++i ) {
                        if( list[index]->var_ptr->implication_clause->elements[i]->var_ptr->assertion_list )
                            continue;
                        
                        list[list_size] = sat_resolved_iteral( list[index]->var_ptr->implication_clause->elements[i] );
                        list[list_size]->var_ptr->assertion_use = 1;
                        list[list_size]->var_ptr->assertion_list = 1;
                        if( list[list_size]->var_ptr->decision_level == decision_level )
                            ++count;
                        ++list_size;
                        ++real_list_size;
                    }

                    break;
                }
            }
        }
    }

    // build the assertion clause itself, while simultaneously calculating the assertion level
    clause = malloc(sizeof(Clause));
    clause->elements = malloc( real_list_size * sizeof(Lit*) );
    clause->elements_size = real_list_size;
    
    i = 0;
    assertion_level = 1;
    for( index = 0; index < list_size; ++index ) {
        if( list[index]->var_ptr->assertion_use ) {
            clause->elements[i++] = list[index];
            if( list[index]->var_ptr->decision_level < decision_level && list[index]->var_ptr->decision_level > assertion_level )
                assertion_level = list[index]->var_ptr->decision_level;
        }
        list[index]->var_ptr->assertion_use  = 0;
        list[index]->var_ptr->assertion_list = 0;
    }
    
    free(list);
    
    clause->assertion_level = assertion_level;
    clause->was_generated = 1;
    sat_state->assertion_clause = clause;
}

BOOLEAN check_clause( Clause* clause, SatState *sat_state ) {
    long index;
    Lit *lit_1 = NULL, *lit_2 = NULL;
    BOOLEAN found_lit_1, found_lit_2;
    
    // if both watches are still free, then just return
    clause->needs_checking = 0;
    if( clause->is_subsumed )
        return 1;
    if( !clause->watch_1->var_ptr->is_set && !clause->watch_2->var_ptr->is_set && clause->watch_1 != clause->watch_2 ) {
        clause->is_subsumed = 0;
        return 1;
    }
    
    // Now we know that one of our watches has changed, search for two free watch statements
    found_lit_1 = 0;
    found_lit_2 = 0;
    for( index = 0; index < clause->elements_size && !( found_lit_1 && found_lit_2 ); ++index ) {
        if( asserted_literal(clause->elements[index]) ) {
            clause->is_subsumed = 1;
            return 1;
        }
        if( !set_literal(clause->elements[index]) ) {
            if( !found_lit_1 ) {
                lit_1 = clause->elements[index];
                found_lit_1 = 1;
            }
            else {
                lit_2 = clause->elements[index];
                found_lit_2 = 1;
            }
        }
    }
    
    if( !found_lit_1 ) {
        // if we have found a contradiction
        clause->is_subsumed = 0;
        generate_assertion_clause(clause, sat_state);
        mark_check_clause(clause, sat_state);
        return 0;
    }
    else if( found_lit_1 && !found_lit_2 ) {
        // if we have a new implication
        clause->is_subsumed = 1;
        imply_literal(lit_1, clause, sat_state);
    }
    else {
        // if the clause still has more than one free variable
        clause->watch_1 = lit_1;
        clause->watch_2 = lit_2;
        clause->is_subsumed = 0;
    }
    
    return 1;
}

//applies unit resolution to the cnf of sat state
//returns 1 if unit resolution succeeds, 0 if it finds a contradiction
BOOLEAN sat_unit_resolution(SatState* sat_state) {
    while( sat_state->clauses_to_check_start != sat_state->clauses_to_check_end ) {
        if( sat_state->clauses_to_check_start == sat_state->clauses_capacity ) {
            sat_state->clauses_to_check_start = 0;
        }
        if( !check_clause( sat_state->clauses_to_check[sat_state->clauses_to_check_start], sat_state ) ) {
            return 0;
        }
        ++sat_state->clauses_to_check_start;
    }
    return 1;
}


//undoes sat_unit_resolution(), leading to un-instantiating variables that have been instantiated
//after sat_unit_resolution()
void sat_undo_unit_resolution(SatState* sat_state) {
    while( sat_state->decisions_size > 0 )
        sat_undo_decide_literal(sat_state);
}

//returns 1 if the decision level of the sat state equals to the assertion level of clause, 0 otherwise
//
//this function is called after sat_decide_literal() or sat_assert_clause() returns clause.
//it is used to decide whether the sat state is at the right decision level for adding clause.
BOOLEAN sat_at_assertion_level(const Clause* clause, const SatState* sat_state) {
    
    if( sat_state != NULL && clause != NULL && clause->was_generated ) {
        return clause->assertion_level == sat_state->decisions_size + 1;
    }
    return 0;
}

/******************************************************************************
 * The functions below are already implemented for you and MUST STAY AS IS
 ******************************************************************************/

//returns the weight of a literal (which is 1 for our purposes)
c2dWmc sat_literal_weight(const Lit* lit) {
    return 1;
}

//returns 1 if a variable is marked, 0 otherwise
BOOLEAN sat_marked_var(const Var* var) {
    return var->mark;
}

//marks a variable (which is not marked already)
void sat_mark_var(Var* var) {
    var->mark = 1;
}

//unmarks a variable (which is marked already)
void sat_unmark_var(Var* var) {
    var->mark = 0;
}

//returns 1 if a clause is marked, 0 otherwise
BOOLEAN sat_marked_clause(const Clause* clause) {
    return clause->mark;
}

//marks a clause (which is not marked already)
void sat_mark_clause(Clause* clause) {
    clause->mark = 1;
}
//unmarks a clause (which is marked already)
void sat_unmark_clause(Clause* clause) {
    clause->mark = 0;
}

/******************************************************************************
 * end
 ******************************************************************************/
