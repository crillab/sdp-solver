#include "rcc.hpp"
#include "sat.hpp"

#include <set>
#include <vector>

namespace Qualitative {
  // bool quick_composition (std::map<int, std::map<int, int>> &orig_rules) {
  //   // In orig_rules, {x, {y, V}} means that some value in V must hold between x and y.
  //   for (auto &[first_var, comparisons] : orig_rules) {
  //     for (auto &[second_var, first_conn] : comparisons) {
  // 	if (orig_rules.contains (second_var)) {
  // 	  for (auto &[third_var, second_conn] : orig_rules[second_var]) {
  // 	    if (!update (orig_rules, first_var, second_var, third_var, first_conn, second_conn))
  // 	      { return false; }
  // 	  }
  // 	}
  //     }
  //   }
  // }

  // bool update (std::map<int, std::map<int, int>> &rules,
  // 	       int var_1, int var_2, int var3, int conn_1, int conn_2) {
  //   int conn_3 {};
    
  //   if (conn_1 & EQ)
  //     { conn_3 &= conn_2; }
  //   if (conn_2 & EQ)
  //     { conn_3 &= conn_2; }
  //   if (conn_1 & DISJ)
  //     {

  int RCC::composition_with_variables (std::map<int, std::map<int, int>> &orig_rules,
				       std::map<int, std::map<int, int>> &vars,
				       CaDiCaL::Solver *solver,
				       int next_var) {
    std::set<int> flat_vars;
    for (auto &[first, body] : orig_rules) {
      flat_vars.insert (first); 
      for (auto &[second, comp] : body)
	{ flat_vars.insert (second); }
    }

    empty_start = next_var;
    empty_end = next_var + flat_vars.size ();
    next_var = empty_end + 1;

    int i {};
    for (auto first_iter {flat_vars.cbegin ()}; first_iter != flat_vars.cend (); ++first_iter, ++i) {
      if (!orig_rules.contains (*first_iter))
	{ orig_rules[*first_iter] = vars[*first_iter] = {}; }
      int j {i + 1};
      for (auto second_iter {std::next (first_iter)}; second_iter != flat_vars.cend (); ++second_iter, ++j) {
	if (!orig_rules[*first_iter].contains (*second_iter)) {
	  orig_rules[*first_iter][*second_iter] = RCC_U;
	  vars[*first_iter][*second_iter] = next_var;
	  next_var += 5;
	}
	int k {j + 1};
	for (auto third_iter {std::next (second_iter)}; second_iter != flat_vars.cend (); ++third_iter, ++k) {
	  for (int early : {*first_iter, *second_iter}) {
	    if (!orig_rules[early].contains (*third_iter)) {
	      orig_rules[early][*third_iter] = RCC_U;
	      vars[early][*third_iter] = next_var;
	      next_var += 5;
	    }
	  }
	  next_var = compose_with_vars (vars[*first_iter][*second_iter], vars[*second_iter][*third_iter], vars[*first_iter][*third_iter],
					empty_start + i, empty_start + j, empty_start + j,
					solver, next_var);
	}
      }
    }

    return next_var;
  }

  int RCC::compose_with_vars (const int start_conn_1, const int start_conn_2, const int start_conn_3,
			      int s1_empty, int s2_empty, int s3_empty, CaDiCaL::Solver *solver,
			      int next_var) {
    int ij {start_conn_1}, jk {start_conn_2}, ik {start_conn_3};
    auto s { [] (int start, int rel) { return start + rel; } };

    // 5, 6
    for (int rel {sub}; rel <= ovlp; ++rel) {
      solver->add (-s (ij, eq)), solver->add (-s (jk, rel)), solver->add (s (ik, rel)), solver->add (0); 
      solver->add  (-s (jk, eq)), solver->add (-s (ij, rel)), solver->add (s (ik, rel)), solver->add (0);
    }

    // 7
    for (int rel : {sub, ovlp})  {
      solver->add (-s (ij, disj)), solver->add (-s (jk, rel));
      for (int sec_rel : {disj, ovlp, sub})
	{ solver->add (s (ik, sec_rel)); }
      solver->add (0);
    }

    // 8
    for (int rel : {sup, ovlp}) {
      solver->add (-s (jk, disj)), solver->add (-s (ij, rel));
      for (int sec_rel : {disj, ovlp, sup})
	{ solver->add (s (ik, sec_rel)); }
      solver->add (0);
    }

    // 9, 10
    for (int rel : {sup, sub}) {
      solver->add (-s (ij, rel)),
	solver->add (-s (jk, rel)),
	solver->add (s (ik, rel)),
	solver->add (0);
    }

    // 11
    solver->add (-s (ij, sup)), solver->add (-s (jk, sub)), solver->add (-s (ik, disj)), solver->add (s2_empty), solver->add (0);
    // solver->add (-s (ij, sup)), solver->add (-s (jk, sub)), solver->add (next_var), solver->add (-s (ik, disj)), solver->add (0);
    // next_var = SAT::bind_clause (next_var, {-s (jk, disj), s2_empty}, solver);

    // 12
    solver->add (-s (ij, disj)), solver->add (-s (jk, sup)), solver->add (s (jk, disj)), solver->add (s3_empty), solver->add (0);

    // 13
    solver->add (-s (ij, sub)), solver->add (-s (jk, disj)), solver->add (s (jk, disj)), solver->add (-s1_empty), solver->add (0);

    // 14
    solver->add (-s (ij, ovlp)), solver->add (-s (jk, sub));
    for (int rel : {sub, ovlp})
      { solver->add (s (ik, rel)); }
    solver->add (0);

    // 15
    solver->add (-s (ij, sup)), solver->add (-s (jk, ovlp));
    for (int rel : {sup, ovlp})
      { solver->add (s (ik, rel)); }
    solver->add (0);

    // 16
    solver->add (-s (ij, ovlp)), solver->add (-s (jk, sup));
    for (int rel : {sup, eq})
      { solver->add (-s (ik, rel)); }
    solver->add (0);

    // 17
    solver->add (-s (ij, sub)), solver->add (-s (jk, ovlp));
    for (int rel : {sub, eq})
      { solver->add (-s (ik, rel)); }
    solver->add (0);

    return next_var;
  }
}
