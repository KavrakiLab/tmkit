#ifndef AMINO_RX_PDDL_C_H
#define AMINO_RX_PDDL_C_H

#include <stddef.h>
#include <stdbool.h>

/** Data structure for grounded PDDL domain */

typedef int tmp_pd_action_pre(const unsigned * vars);

typedef void tmp_pd_action_eff(unsigned * vars);

struct tmp_pd_pddl_struct
{
  size_t n_type; // Number of types
  const unsigned * type; // Array containing the number of elements of each type

  // Array containing the domain of the grounded functions,
  // represented by the index of the domain type
  size_t n_func;
  const unsigned * func;
  const char ** func_name;

  // Action precondition and action effect
  size_t n_action;
  tmp_pd_action_pre ** action_precon;
  tmp_pd_action_eff ** action_effect;
  const char ** action_name;


};

#endif
