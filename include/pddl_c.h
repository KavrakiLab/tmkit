#ifndef AMINO_RX_PDDL_C_H
#define AMINO_RX_PDDL_C_H

#include <stddef.h>
#include <stdbool.h>

/** Data structure for grounded PDDL domain */

typedef bool aa_rx_action_precon(const unsigned * vars, size_t vars_n);

typedef void aa_rx_action_effect(const unsigned * vars_pre, unsigned * vars_post, size_t vars_n);

struct aa_rx_pddl_struct
{
  size_t type_n; // Number of types
  unsigned * type; // Array containing the number of elements of each type

  // Array containing the domain of the grounded functions,
  // represented by the index of the domain type 
  size_t func_n;
  unsigned * func;

  // Action precondition and action effect
  size_t action_n;
  aa_rx_action_precon * action_precon;
  aa_rx_action_effect * action_effect;


};
  
#endif
