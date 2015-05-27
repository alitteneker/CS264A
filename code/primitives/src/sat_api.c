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

  if( var != NULL ) {
    for(index = 0; index < var->used_clauses_size; ++index) {
      if( var->used_clauses[index]->is_subsumed == 0 )
        return 0;
    }
    return 1;
  }

  return 0;
}

//returns the number of variables in the cnf of sat state
c2dSize sat_var_count(const SatState* sat_state) {

  if( sat_state != NULL )
    return sat_state->variables_size;
  return 0;
}

//returns the number of clauses mentioning a variable
//a variable is mentioned by a clause if one of its literals appears in the clause
c2dSize sat_var_occurences(const Var* var) {

  if( var != NULL )
    return var->used_clauses_size;
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
  Var* var;

  if( sat_state != NULL && u_index < sat_state->variables_size ) {
    var = sat_index2var(u_index, sat_state);
    return ( index < 0 ) ? var->neg_literal : var->pos_literal;
  }
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

Lit* sat_opposite_literal(const Lit* lit) {
  if(lit == NULL)
    return NULL;
  return ( lit->index < 0 ) ? lit->var_ptr->pos_literal : lit->var_ptr->pos_literal;
}

//returns 1 if the literal is implied, 0 otherwise
//a literal is implied by deciding its variable, or by inference using unit resolution
BOOLEAN sat_implied_literal(const Lit* lit) {

  if( lit != NULL )
    return lit->var_ptr->is_set;
  return 0;
}

BOOLEAN set_literal(Lit* lit) {

  if( lit != NULL )
    return lit->var_ptr->is_set;
  return 0;
}

BOOLEAN asserted_literal(Lit* lit) {

  if( lit != NULL && lit->var_ptr->is_set == 1 && lit->var_ptr->set_sign == ( lit->index > 0 ) )
    return 1;
  return 0;
}

BOOLEAN resolved_literal(Lit* lit) {

  if( lit != NULL && lit->var_ptr->is_set == 1 && lit->var_ptr->set_sign == ( lit->index < 0 ) )
    return 1;
  return 0;
}

BOOLEAN unapply_literal(Lit *lit, SatState* sat_state) {
  unsigned long index;

  if( lit == NULL || !set_literal(lit) )
    return 0;

  lit->var_ptr->is_set = 1;
  for( index = 0; index < lit->var_ptr->used_clauses_size; ++index ) {
    lit->var_ptr->used_clauses[index]->needs_checking = 1;
  }

  return 1;
}

// return the decision level found
long apply_literal(Lit* lit, Clause* clause, SatState* sat_state) {

  long index, max_depth, max_level;

  if( lit == NULL || set_literal(lit) )
    return -1;

  lit->var_ptr->is_set = 1;
  lit->var_ptr->set_sign = lit->index > 0;
  lit->var_ptr->implication_clause = clause;

  // determine and set the depth and level of this new variable setting variable
  if( clause != NULL ) {
    max_level = 1;
    max_depth = -1;
    for( index = 0; index < clause->elements_size; ++index ) {
      if( clause->elements[index]->var_ptr->is_set == 0 || clause->elements[index] == lit )
        continue;
      if( clause->elements[index]->var_ptr->decision_level > max_level )
        max_level = clause->elements[index]->var_ptr->decision_level;
      if( clause->elements[index]->var_ptr->set_depth > max_depth )
        max_depth = clause->elements[index]->var_ptr->set_depth;
    }
    lit->var_ptr->decision_level = max_level;
    lit->var_ptr->set_depth = max_depth + 1;
  }
  else {
    max_level = lit->var_ptr->decision_level = sat_state->decisions_size + 1;
    max_depth = lit->var_ptr->set_depth = 0;
  }

  // flag all the clauses that use this new setting
  for( index = 0; index < lit->var_ptr->used_clauses_size; ++index )
    if( lit->var_ptr->used_clauses[index]->is_subsumed == 0 )
      lit->var_ptr->used_clauses[index]->needs_checking = 1;

  return max_level;
}

//sets the literal to true, and then runs unit resolution
//returns a learned clause if unit resolution detected a contradiction, NULL otherwise
//
//if the current decision level is L in the beginning of the call, it should be updated
//to L+1 so that the decision level of lit and all other literals implied by unit resolution is L+1
Clause* sat_decide_literal(Lit* lit, SatState* sat_state) {

  if( sat_state == NULL || lit == NULL
    || set_literal(lit) || sat_state->decisions_size == sat_state->variables_size )
      return NULL;

  sat_state->decisions[ sat_state->decisions_size++ ] = lit;
  apply_literal(lit, NULL, sat_state);
  return sat_unit_resolution(sat_state) ? NULL : sat_state->assertion_clause;
}

BOOLEAN imply_literal(Lit *lit, Clause *clause, SatState *sat_state) {
  long level, i, index;

  if( sat_state == NULL || lit == NULL
    || set_literal(lit) || sat_state->implications_size == sat_state->implications_size )
      return 0;

  level = apply_literal(lit, clause, sat_state);
  if( sat_state->implications_size == 0
    || level >= sat_state->implications[sat_state->implications_size]->var_ptr->decision_level ) {
      sat_state->implications[ sat_state->implications_size++ ] = lit;
  }
  else {
    // in this case, we have at least one out of sequence implication
    // (need to have implication list sorted by decision level)
    // find appropriate insertion point, and shift after that point along
    for( i = sat_state->implications_size-1; i >= 0; ++i ) {
      index = i;
      if( sat_state->implications[i]->var_ptr->decision_level <= level ) {
        ++index;
        break;
      }
      else {
        sat_state->implications[i+1] = sat_state->implications[i];
      }
    }
    sat_state->implications[index] = lit;
  }

  return 1;
}

//undoes the last literal decision and the corresponding implications obtained by unit resolution
//
//if the current decision level is L in the beginning of the call, it should be updated
//to L-1 before the call ends
void sat_undo_decide_literal(SatState* sat_state) {
  sat_undo_unit_resolution(sat_state);
}

/******************************************************************************
 * Clauses
 ******************************************************************************/

//returns a clause structure for the corresponding index
Clause* sat_index2clause(c2dSize index, const SatState* sat_state) {

  if( sat_state != NULL && index < sat_state->clauses_size )
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
    return sat_state->clauses_size;
  return 0;
}

//returns the number of learned clauses in a sat state (0 when the sat state is constructed)
c2dSize sat_learned_clause_count(const SatState* sat_state) {

  if( sat_state != NULL )
    return sat_state->assertion_clause_count;
  return 0;
}

// resize the list of clauses for something when we run out of room
Clause** resize_clause_list(Clause** original, unsigned long original_size, unsigned long new_capacity) {
  unsigned long j;

  // allocate some new memory, expand size by 10 each time: is this too much?
  Clause **expand = malloc(new_capacity * sizeof(Clause*));

  // copy over the memory into the new block
  for( j = 0; j < original_size; ++j )
    expand[j] = original[j];

  // write the newly expanded version
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

  if( sat_state == NULL || clause == NULL )
    return 0;

  clause->index = sat_state->clauses_size;
  clause->watch_1 = clause->watch_2 = clause->elements[0];
  clause->needs_checking = 1;
  clause->is_subsumed = 0;

  for( index = 0; index < clause->elements_size; ++index ) {
    var = clause->elements[index]->var_ptr;
    if( var->used_clauses_capacity == var->used_clauses_size ) {
      var->used_clauses = resize_clause_list(
        var->used_clauses, var->used_clauses_size, var->used_clauses_capacity+=10
      );
    }
    var->used_clauses[ var->used_clauses_size++ ] = sat_state->assertion_clause;
  }

  if( sat_state->clauses_capacity == sat_state->clauses_size ) {
    sat_state->clauses = resize_clause_list(
      sat_state->clauses, sat_state->clauses_size, sat_state->clauses_capacity+=10
    );
  }
  sat_state->clauses[ sat_state->clauses_size++ ] = clause;
  sat_state->assertion_clause_count++;
  sat_state->assertion_clause = NULL;
  sat_state->assertion_clause_level = 0;

  return sat_unit_resolution(sat_state) ? NULL : sat_state->assertion_clause;
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

int get_index(SatState* sat, c2dLiteral val){
    int i;
    for(i = 0; i < sat -> literals_size; i++){
        if((*sat->literals)[i].index == val)
            return i;
    }
    return i;
}

int if_in_usedClauseAlready(Clause** used_clauses, c2dSize clause_index, c2dSize cls_size)
{
    for(int i = 0; i < cls_size; i++){
        if(used_clauses[i]->index == clause_index)
            return 1;
    }
    return 0;
}
int get_numbers(const char *line, int **vars, size_t num_vars, Lit *lit)
{
    int i, x;
    int *tmp;
    const char *p, *q;
    
    if(vars == NULL)
        return 0;

    tmp = (int *)malloc(num_vars * sizeof(int));
    
    p = line;
    q = NULL;

    for(i=0; i < num_vars; i++){
        while(*p!=0 && isspace(*p)) p++;
        q = p;
        while(*q!=0 && !isspace(*q)) q++;
        while(*q!=0 && isspace(*q)) q++;
        
        if(p==q)
            break;
        
        if(sscanf(p, "%d", &x) != 1)
        {
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

SatState* construct_sat_state(char* cnf_fname) {
    SatState *ret;
    FILE *fp;
    Clause *cls = NULL;
    Lit *decision = NULL;
    Lit *implication = NULL;
    Lit *lit = NULL;
    Var *var = NULL;
    
    int num_clause;
    size_t n;
    char *buffer;
    
    // testing the file
    if((fp=fopen(cnf_fname, "r")) == NULL)
        return NULL;
    
    num_clause = 0;
    n = 80;
    ret = (SatState *) malloc( sizeof(SatState) );
    memset(ret, 0x00, sizeof(SatState));
    
    buffer = (char *)malloc(n * sizeof(char));
    
    while(getline(&buffer, &n, fp) != -1)
    {

        char fst_char = buffer[0];
        
        if( fst_char == 'c')
            continue;
        
        else if(fst_char== 'p')
        {

            if(sscanf(buffer, "p cnf %lu %lu", &ret->variables_size, &ret->clauses_size) != 2)
                exit(EXIT_FAILURE);
            
            //allocating memories for attributes for sat_state
            ret->variables = (Var**)malloc(sizeof(Var *));
            var = (Var *) malloc(ret -> variables_size * sizeof(Var));
            *ret->variables = var;
            
            ret->literals = (Lit**)malloc(sizeof(Lit *));
            lit = (Lit *) malloc(ret -> variables_size * 2 * sizeof(Lit));
            *ret->literals = lit;
            
            ret ->clauses = (Clause**) malloc(sizeof(Clause*));
            cls = (Clause *) malloc(ret-> clauses_size * sizeof(Clause));
            *ret -> clauses = cls;
            
            ret ->decisions =(Lit**) malloc(sizeof(Lit*));
            decision = (Lit*) malloc(ret->variables_size * sizeof(Lit));
            *ret -> decisions = decision;
            
            ret ->implications =(Lit**) malloc(sizeof(Lit*));
            implication = (Lit*) malloc(ret->variables_size * sizeof(Lit));
            *ret -> implications = implication;
            
            
            //initialize variable
            for( int i = 0 ; i < ret-> variables_size; i++){
                Clause **cls_arr;
                
                cls_arr = (Clause **)malloc(ret->clauses_size * sizeof(Clause*));
                var[i].index = i+1;
                var[i].used_clauses = cls_arr;
                var[i].used_clauses_size = 0;
                var[i].used_clauses_capacity = ret->clauses_size;
            }
            
            //initialize literals
            long k = 1;
            int i, j;
            for(i=0, j = 0; j < ret->variables_size*2; j+=2,i++ )
            {
                lit[j].index = k;
                lit[j+1].index = -(k);
                lit[j].var_ptr = ret->variables[i];
                lit[j+1].var_ptr = ret->variables[i];
                var[i].pos_literal = &lit[j];
                var[i].neg_literal = &lit[j+1];
                k++;
            }
            for(i = 0; i < ret->literals_size; i++){
                printf("%lu ", ret->literals[i]->index);
            }
            ret->literals_size = ret->variables_size*2;
            continue;
        }
        //else it's the clauses
        else if( !(fst_char >= 'a' && fst_char <= 'z') && num_clause < ret-> clauses_size)
        {

            //initialize clauses
            int *vals;
            int var_val;
            Lit** element_array = NULL;
            int n = get_numbers(buffer, &vals, ret->variables_size, lit);

            element_array = (Lit**)malloc(n*sizeof(Lit*));
            cls[num_clause].elements = element_array;
            
            for(int i = 0; i < n ; i++)
            {
                // assignment for literals in this clause cls[num_clause]
                int x;
                x = get_index(ret, vals[i]);
                element_array[i] = (lit+x);
                
                var_val = (vals[i]<0) ? -vals[i]: vals[i];
                var_val = var_val-1;
                
                //setting the used_clauses for varables that appear in the clause
                unsigned long j = var[var_val].used_clauses_size;
                if(if_in_usedClauseAlready(var[var_val].used_clauses, num_clause+1, j) == 0)
                {
                    //copy over all the information.
                    var[var_val].used_clauses[j] = &cls[num_clause];
                    var[var_val].used_clauses_size++;
                }
                
            }

            cls[num_clause].elements_size = n;
            cls[num_clause].index = num_clause+1;

            num_clause++;
        }
        else
        {
            continue;
        }        

    }
    fclose(fp);
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

  for( index = 0; index < sat_state->variables_size; ++index ) {
    free(sat_state->variables[index]->pos_literal);
    free(sat_state->variables[index]->neg_literal);
    free(sat_state->variables[index]->used_clauses);
    free(sat_state->variables[index]);
  }
  free(sat_state->variables);
  free(sat_state->implications);
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
unsigned long recurse_paths(Lit *lit, unsigned long level) {
  unsigned long paths, index;

  if( lit->var_ptr->implication_clause == NULL ) {
    paths = 1;
  }
  else {
    if( lit->var_ptr->implication_clause->elements_size == 1 )
      paths = 1;
    else {
      paths = 0;
      for( index = 0; index < lit->var_ptr->implication_clause->elements_size; ++index ) {
        if( lit->var_ptr->implication_clause->elements[index] == lit )
          continue;
        paths += recurse_paths( lit->var_ptr->implication_clause->elements[index], level );
        if( lit->var_ptr->set_depth > lit->var_ptr->implication_clause->elements[index]->var_ptr->used_depth )
          lit->var_ptr->implication_clause->elements[index]->var_ptr->used_depth = lit->var_ptr->set_depth;
      }
    }
  }
  lit->var_ptr->path_count += paths;

  if( lit->var_ptr->decision_level == level )
    return paths;
  return 0;
}

unsigned long calc_decision_level(Clause *clause) {
  unsigned long decision_level, index;

  // calculate the maximum level in the conflict clause
  decision_level = 0;
  for( index = 0; index < clause->elements_size; ++index ) {
    if( decision_level < clause->elements[index]->var_ptr->decision_level )
      decision_level = clause->elements[index]->var_ptr->decision_level;
  }

  return decision_level;
}

unsigned long calc_total_paths(Clause *clause, unsigned long decision_level, SatState *sat_state) {
  unsigned long total_paths, index;

  // clear out any old data in any of the implications and decisions
  for( index = 0; index < sat_state->implications_size; ++index ) {
    sat_state->implications[index]->var_ptr->path_count = 0;
    sat_state->implications[index]->var_ptr->used_depth = 0;
  }
  for( index = 0; index < sat_state->decisions_size; ++index ) {
    sat_state->decisions[index]->var_ptr->path_count = 0;
    sat_state->decisions[index]->var_ptr->used_depth = 0;
  }

  // calculate the total number of same-level paths from the conflict clause to the end
  total_paths = 0;
  for( index = 0; index < clause->elements_size; ++index ) {
    total_paths += recurse_paths( clause->elements[index], decision_level );
  }

  return total_paths;
}

Lit* find_UIP(SatState* sat_state, unsigned long decision_level, unsigned long total_paths) {
  long index;

  for(index = sat_state->implications_size-1; index >= 0; --index ) {
    if( sat_state->implications[index]->var_ptr->decision_level < decision_level ) {
      index = -1;
      break;
    }
    if( sat_state->implications[index]->var_ptr->path_count == total_paths )
      break;
  }

  if( index < 0 ) {
    // if our current decision level is 0, then generating
    if( decision_level > 1 )
      return sat_state->decisions[ decision_level - 2 ];
    return NULL;
  }
  return sat_state->implications[index];
}

// this will actually build the new clause
Clause* build_assertion_clause(Lit *uip, SatState *sat_state) {
  unsigned long index, cut_size;
  long assertion_level;
  Lit **cut;
  Clause *clause;

  // this would indicate we have no uip (conflict through only unit clause implications)
  if( uip == NULL )
    return NULL;

  cut = malloc( sat_state->variables_size * sizeof(Lit*) );
  cut_size = 0;
  for( index = 0; index < sat_state->implications_size; ++index ) {
    if( sat_state->implications[index]->var_ptr->path_count > 0 ) {
      if( sat_state->implications[index]->var_ptr->decision_level < uip->var_ptr->decision_level
        && sat_state->implications[index]->var_ptr->decision_level > assertion_level ) {
        assertion_level = sat_state->implications[index]->var_ptr->decision_level;
      }
      if( sat_state->implications[index]->var_ptr->set_depth <= uip->var_ptr->set_depth
        && sat_state->implications[index]->var_ptr->used_depth >= uip->var_ptr->set_depth + 1 ) {
          cut[cut_size++] = sat_opposite_literal(sat_state->implications[index]);
        }
    }
  }
  for( index = 0; index < sat_state->decisions_size; ++index ) {
    if( sat_state->decisions[index]->var_ptr->path_count > 0 ) {
      if( sat_state->decisions[index]->var_ptr->decision_level < uip->var_ptr->decision_level
        && sat_state->decisions[index]->var_ptr->decision_level > assertion_level ) {
        assertion_level = sat_state->decisions[index]->var_ptr->decision_level;
      }
      if( sat_state->decisions[index]->var_ptr->set_depth <= uip->var_ptr->set_depth
        && sat_state->decisions[index]->var_ptr->used_depth >= uip->var_ptr->set_depth + 1 ) {
          cut[cut_size++] = sat_opposite_literal(sat_state->decisions[index]);
        }
    }
  }

  clause = malloc(sizeof(Clause));
  clause->elements = malloc( cut_size * sizeof(Lit*) );
  clause->elements_size = cut_size;
  for( index = 0; index < cut_size; ++index ) {
    clause->elements[index] = cut[index];
  }
  free(cut);

  sat_state->assertion_clause = clause;
  sat_state->assertion_clause_level = assertion_level;

  return clause;
}

// this method runs all relevant calculations for assertion clause generation
// THIS METHOD CALLS THE METHOD ABOVE, only cal this method directly
void generate_assertion_clause(Clause *clause, SatState* sat_state) {
  unsigned long total_paths, decision_level;
  Lit *uip;

  decision_level = calc_decision_level(clause);
  total_paths = calc_total_paths(clause, decision_level, sat_state);
  uip = find_UIP(sat_state, decision_level, total_paths);
  build_assertion_clause(uip, sat_state);

  return;
}

BOOLEAN check_clause( Clause* clause, SatState *sat_state ) {
  long index;
  Lit *lit_1, *lit_2;
  BOOLEAN found_lit_1, found_lit_2;

  // if both watches are still free, then just return
  if( !set_literal( clause->watch_1 ) && !set_literal( clause->watch_2 ) && clause->watch_1 != clause->watch_2 )
    return 1;

  // Now we know that one of our watches has changed, search for two free watch statements
  found_lit_1 = 0;
  found_lit_2 = 0;
  for( index = 0; index < clause->elements_size && !( found_lit_1 && found_lit_2 ); ++index ) {
    if( asserted_literal(clause->elements[index]) ) {
      clause->is_subsumed = 1;
      return 1;
    }
    if( set_literal(clause->elements[index]) == 0 ) {
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

  if( !found_lit_1 && !found_lit_2 ) {
    // if we have found a contradiction
    clause->is_subsumed = 0;
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

BOOLEAN check_literal(Lit *lit, SatState* sat_state) {
  long index;

  for( index = 0; index < lit->var_ptr->used_clauses_size; ++index ) {
    if( lit->var_ptr->used_clauses[index]->needs_checking == 1 ) {
      lit->var_ptr->used_clauses[index]->needs_checking = 1;
      if( check_clause( lit->var_ptr->used_clauses[index], sat_state ) == 0 ) {
        generate_assertion_clause(lit->var_ptr->used_clauses[index], sat_state);
        return 0;
      }
    }
  }
  return 1;
}

//applies unit resolution to the cnf of sat state
//returns 1 if unit resolution succeeds, 0 if it finds a contradiction
BOOLEAN sat_unit_resolution(SatState* sat_state) {

  while( sat_state->decisions_applied < sat_state->decisions_size ) {
    if( !check_literal( sat_state->decisions[ sat_state->decisions_applied++ ], sat_state ) )
      return 0;
  }
  while( sat_state->implications_applied < sat_state->implications_size ) {
    if( !check_literal( sat_state->implications[ sat_state->implications_applied++ ], sat_state ) )
      return 0;
  }
  return 1;
}


//undoes sat_unit_resolution(), leading to un-instantiating variables that have been instantiated
//after sat_unit_resolution()
void sat_undo_unit_resolution(SatState* sat_state) {
  long index;
  Lit *decision;

  if( sat_state == NULL || sat_state->decisions_size == 0 )
    return;

  decision = sat_state->decisions[ --sat_state->decisions_size ];
  for( index = sat_state->implications_size-1;
    index >= 0 && sat_state->implications[index]->var_ptr->decision_level >= decision->var_ptr->decision_level;
    --index ) {
      unapply_literal(sat_state->implications[index], sat_state);
  }
  for( index = 0; index < sat_state->clauses_size; ++index ) {
    if( sat_state->clauses[index]->needs_checking ) {
      check_clause( sat_state->clauses[index], sat_state );
    }
  }
  return;
}

//returns 1 if the decision level of the sat state equals to the assertion level of clause,
//0 otherwise
//
//this function is called after sat_decide_literal() or sat_assert_clause() returns clause.
//it is used to decide whether the sat state is at the right decision level for adding clause.
BOOLEAN sat_at_assertion_level(const Clause* clause, const SatState* sat_state) {

  if( sat_state != NULL )
    return sat_state->assertion_clause_level == sat_state->decisions_size + 1;
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
