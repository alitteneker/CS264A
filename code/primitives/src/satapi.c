#include "satapi.h"


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
 * Given a variable index i, you should return the corresponding variable
 * structure (notice you must return a pointer to the structure)
 *
 * Note variable indices range from 1 to n where n is the number of variables
 ******************************************************************************/
Var* index2varp(unsigned long i, SatState* sat_state) {

  if( sat_state != NULL && i > 0 && i <= sat_state->variables_length )
    return sat_state->variables[ i - 1 ];
  return NULL;
}


/******************************************************************************
 * Given a variable var, you should return
 * --its positive literal (pos_literal)
 * --its negative literal (neg_literal)
 *
 *
 * Given a literal lit, set_literal(lit) should return
 * --1 if lit is set in the current setting
 * --0 if lit is free
 *
 * Note a literal is set either by a decision or implication
 * Do not forget to update the status of literals when you run unit resolution
 ******************************************************************************/
Lit* pos_literal(Var* var) {

  if( var != NULL )
    return var->pos_literal;
  return NULL;
}

Lit* neg_literal(Var* var) {

  if( var != NULL )
    return var->neg_literal;
  return NULL;
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

/******************************************************************************
 * Given a clause index i, you should return the corresponding clause
 * structure (notice you must return a pointer to the structure)
 *
 * Note clause indices range from 1 to m where m is the number of clauses
 ******************************************************************************/
Clause* index2clausep(unsigned long i, SatState* sat_state) {

  if( sat_state != NULL && i > 0 && i <= sat_state->clauses_size )
    return sat_state->clauses[ i - 1 ];
  return NULL;
}


/******************************************************************************
 * Given a clause, you should return
 * --1 if the clause is subsumed in the current setting
 * --0 otherwise
 *
 * Note a clause is subsumed if at least one of its literals is implied
 * Do not forget to update the status of clauses when you run unit resolution
 ******************************************************************************/
BOOLEAN subsumed_clause(Clause* clause) {

  int i;

  if( clause == NULL )
    return 0;

  if( clause->is_subsumed == 0 ) {

    // is this necessary? I can't tell from the above description.
    for( i = 0; i < clause->elements_size; ++i ) {
      if( asserted_literal(clause->elements[i]) ) {
        clause->is_subsumed = 1;
        break;
      }
    }
  }
  return clause->is_subsumed;
}


/******************************************************************************
 * A SatState should keep track of pretty much everything you will need to
 * condition/uncondition, perform unit resolution, and do clause learning
 *
 * Given a string cnf_fname, which is a file name of the input CNF, you should
 * construct a SatState
 *
 * This construction will depend on how you define a SatState
 * Still, you should at least do the following:
 * --read a CNF (in DIMACS format) from the file
 * --initialize variables (n of them)
 * --initialize literals  (2n of them)
 *
 * Once a SatState is constructed, all of the functions that work on a SatState
 * should be ready to use
 *
 * You should also write a function that frees the memory allocated by a
 * SatState (free_sat_state)
 ******************************************************************************/
SatState* construct_sat_state(char* cnf_fname) {

  // TODO
  return NULL; // dummy value
}

void free_sat_state(SatState* sat_state) {

  // TODO
  return; // dummy value
}


/******************************************************************************
 * This function should set literal lit to true and then perform unit resolution
 * It returns 1 if unit resolution succeeds, 0 otherwise
 *
 * Note if the current decision level is L in the beginning of the call, it
 * should be updated to L+1 so that the decision level of lit and all other
 * literals implied by unit resolution is L+1
 ******************************************************************************/
BOOLEAN decide_literal(Lit* lit, SatState* sat_state) {

  // TODO: need to deal with over capacity issue
  sat_state->decisions[ sat_state->decisions_size++ ];
  return unit_resolution(sat_state);
}

BOOLEAN imply_literal(Lit* lit, long level, long clause_index, SatState* sat_state) {

  unsigned long index;
  int i;

  if( sat_state == NULL || lit == NULL || set_literal(lit) )
    return 0;

  // make sure that the passed implication is not already in the implication list
  index = lit->var_ptr->index;
  for( i = 0; i < sat_state->implications_size; ++i ) {
    if( sat_state->implications[i]->var_ptr->index == index )
      return 0;
  }

  // TODO: need to deal with over capacity issue
  sat_state->implications[sat_state->implications_size] = lit;
  sat_state->implications_levels[sat_state->implications_size]     = level;
  sat_state->implications_clauses[sat_state->implications_size]    = clause_index; // make it a pointer to the clause itself?
  ++sat_state->implications_size;

  return 1;
}


/******************************************************************************
 * Given a SatState, which should contain data related to the current setting
 * (i.e., decided literals, asserted literals, subsumed clauses, decision
 * level, etc.), this function should perform unit resolution at the current
 * decision level
 *
 * It returns 1 if succeeds, 0 otherwise (after constructing an asserting
 * clause)
 *
 * There are three possible places where you should perform unit resolution:
 * (1) after deciding on a new literal (i.e., decide_literal(SatState*))
 * (2) after adding an asserting clause (i.e., add_asserting_clause(SatState*))
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
BOOLEAN unit_resolution(SatState* sat_state) {

  // TODO
  return 0; // dummy value
}


/******************************************************************************
 * This function should simply undo all set literals at the current decision
 * level
 ******************************************************************************/
void undo_unit_resolution(SatState* sat_state) {

  // TODO:
  // remove last element in decision list
  // remove all implications which are at the highest decision level\
  return;
}


/******************************************************************************
 * This function should undo all set literals at the current decision level (you
 * can in fact call undo_unit_resolution(SatState*))
 *
 * Note if the current decision level is L in the beginning of the call, it
 * should be updated to L-1 before the call ends
 ******************************************************************************/
void undo_decide_literal(SatState* sat_state) {
  return undo_unit_resolution(sat_state);
}


/******************************************************************************
 * This function must be called after a contradiction has been found (by unit
 * resolution), an asserting clause constructed, and backtracking took place to
 * the assertion level (i.e., the current decision level is the same as the
 * assertion level of the asserting clause)
 *
 * This function should add the asserting clause into the set of learned clauses
 * (so that unit resolution from there on would also take into account the
 * asserting clause), and then perform unit resolution
 *
 * It returns 1 if unit resolution succeeds, which means the conflict is
 * cleared, and 0 otherwise (that is, we have a new asserting clause with a new
 * assertion level)
 *
 * Note since the learned clause is asserting and we are at the assertion level
 * of the clause, it will become a unit clause under the current setting
 *
 * Also, if the learned clause itself is a unit clause, its assertion level must
 * be the same as the start level S, which is 1 (i.e., the level in
 * which no decision is made)
 ******************************************************************************/
BOOLEAN add_asserting_clause(SatState* sat_state) {

  if( sat_state == NULL )
    return;
  // TODO: have to deal with over-capacity issue
  sat_state->clauses[ sat_state->clauses_size++ ] = sat_state->asserting_clause;
  return unit_resolution(sat_state);
}


/******************************************************************************
 * This function can be called after a contradiction has been found (by unit
 * resolution), an asserting clause constructed, and the conflict is not cleared
 * yet (that is, conflict_exists(SatState*) must return 1 at the time of call)
 *
 * It returns 1 if the current decision level is the same as the assertion level
 * of the asserting clause, 0 otherwise
 ******************************************************************************/
BOOLEAN at_assertion_level(SatState* sat_state) {

  if( sat_state != NULL )
    return sat_state->conflict_clausse_level == sat_state->decisions_size + 1;
  return 0;
}


/******************************************************************************
 * It returns 1 if the current decision level is the same as the start level,
 * which is 1 (i.e., the level in which no decision is made), 0 otherwise
 ******************************************************************************/
BOOLEAN at_start_level(SatState* sat_state) {

  if( sat_state != NULL )
    return sat_state->decisions_size == 0;
  return 0;
}


/******************************************************************************
 * It returns 1 if there is a conflict in the current setting, 0 otherwise
 *
 * --Initially there is no conflict
 * --If unit resolution finds a contradiction, then we have a conflict
 * --A conflict is cleared when we backtrack to the assertion level, add the
 * asserting clause into the set of learned clauses, and successfully perform
 * unit resolution (i.e., the call add_asserting_clause(SatState*) returns 1)
 ******************************************************************************/
BOOLEAN conflict_exists(SatState* sat_state) {

  // Is this enough here, or do we ned to actually test: unit_resolution(sat_state);
  if( sat_state != NULL )
    return sat_state->conflict_clause_level == sat_state->decisions_size;
  return 0;
}

/******************************************************************************
 * end
 ******************************************************************************/
