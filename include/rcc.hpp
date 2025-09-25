#ifndef RCC_H
#define RCC_H

// #include "libgqr.h"
#include "cadical.hpp"

#include <map>

namespace Qualitative {
  enum rcc_bitwise { SUB = 1, SUPER = 2, EQ = 4, DISJ = 8, OVLP = 16, RCC_U = 31 };
  enum rcc_additive { sub, sup, eq, disj, ovlp };
  
  struct RCC {
    int empty_start {-1}, empty_end {-1};
  
    bool quick_composition (std::map<int, std::map<int, int>> &orig_rules);
    bool update (std::map<int, std::map<int, int>> &rules,
		 int var_1, int var_2, int var3, int conn_1, int conn_2);
    int composition_with_variables (std::map<int, std::map<int, int>> &orig_rules,
				    std::map<int, std::map<int, int>> &vars,
				    CaDiCaL::Solver *solver, int next_var);
    int compose_with_vars (const int start_conn_1, const int start_conn_2, const int start_conn_3,
			   int s1_empty, int s2_empty, int s3_empty, CaDiCaL::Solver *solver,
			   int next_var);
  };
}

#endif
