#include "sat.hpp"

namespace SAT {

  int inverse (int orig) {
    return RCC_U & (~orig);
  }
  
  int converse (int orig) {
    int out {orig & ~(SUB | SUPER)};
    for (int i {}; i <= SUPER; ++i) {
      if (orig & i)
	{ out |= i % SUPER + 1; }
    }
    return out;
  }

  bool single (int comparison) {
    for (int i {RCC_U + 1}; i > 0; i >>= 1) {
      if ((comparison & i) == comparison)
	{ return true; }
    }
    return false;
  }

  void iff (int lit_1, int lit_2, CaDiCaL::Solver *solver) {
    solver->add (-lit_1), solver->add (lit_2), solver->add (0);
    solver->add (-lit_2), solver->add (lit_1), solver->add (0);
  }
  
  int bind (int next_var, std::vector<int> &literals, CaDiCaL::Solver *solver, bool phase) {
    for (int &lit : literals) {
      solver->add (phase ? -lit : lit), solver->add (phase ? next_var : -next_var), solver->add (0);
      if (!phase)
	{ lit = -lit; }
    }
    literals.push_back (phase ? -next_var : next_var);
    solver->clause (literals);
    return ++next_var;
  }
  
  int bind_clause (int next_var, std::vector<int> &&literals, CaDiCaL::Solver *solver) {
    // return bind (next_var, literals, solver, true);
    
    for (int lit : literals)
      { solver->add (-lit), solver->add (next_var), solver->add (0); }
    for (int lit : literals)
      { solver->add (lit); }
    solver->add (-next_var), solver->add (0);
    return ++next_var;
  }

  int bind_term (int next_var, std::vector<int> &&literals, CaDiCaL::Solver *solver) {
    return bind (next_var, literals, solver, false);
    
    for (int lit : literals)
      { solver->add (-next_var), solver->add (lit), solver->add (0); }
    for (int lit : literals)
      { solver->add (-lit); }
    solver->add (next_var), solver->add (0);
    return ++next_var;
  }

  void at_most_one (int begin, int end, CaDiCaL::Solver *solver) {
    for (int i {begin}; i < end; ++i) {
      for (int j {i + 1}; j < end; ++j) 
	{ solver->add (-i), solver->add (-j), solver->add (0); }
    }
  }

  void at_least_one (int begin, int end, CaDiCaL::Solver *solver) {
    for (int i {begin}; i < end; ++i)
      { solver->add (i); }
    solver->add (0);
  }

  void exactly_one (int begin, int end, CaDiCaL::Solver *solver) {
    at_most_one (begin, end, solver);
    at_least_one (begin, end, solver);
  }
  
  void bottom (const std::string &reason, CaDiCaL::Solver *solver) {
    solver->add (1), solver->add (0);
    solver->add (-1), solver->add (0);
  }

  SeqEncoding::SeqEncoding (int &next_var, int width)
    : before_s_start {next_var - 1}, width {width} {
    next_var += width * width;
  }

  int SeqEncoding::s_idx (int i, int j) {
    return before_s_start + (i - 1) * width + j;
  }
  
  void SeqEncoding::first_determines_first (CaDiCaL::Solver *solver, int el_begin) {
    iff (el_begin, s_idx (1, 1), solver);
  }

  void SeqEncoding::first_counts_for_at_most_one (CaDiCaL::Solver *solver) {
    for (int k {2}; k < width; ++k)
      { solver->add (-s_idx (1, k)), solver->add (0); }
  }

  int SeqEncoding::one_iff (CaDiCaL::Solver *solver, int j, int q, int next_var) {
    iff (next_var, s_idx (j, 1), solver);
    return bind_clause (next_var, {q, s_idx (j - 1, 1)}, solver);
  }

  int SeqEncoding::k_iff (CaDiCaL::Solver *solver, int j, int q, int next_var) {
    for (int k {2}; k <= width; ++k) {
      int inner {next_var};
      int outer {bind_term (inner, {q, s_idx (j - 1, k - 1)}, solver)};
      next_var = bind_clause (outer, {inner, s_idx (j - 1, k)}, solver);
      iff (outer, s_idx (j, k), solver);
    }
    return next_var;
  }

  int SeqEncoding::operator () (CaDiCaL::Solver *solver, int el_begin, int el_end, int next_var) {
    first_determines_first (solver, el_begin);
    first_counts_for_at_most_one (solver);
    for (int q {el_begin + 1}, j {2}; q <= el_end; ++q, ++j) {
      next_var = one_iff (solver, j, q, next_var);
      next_var = k_iff (solver, j, q, next_var);
    }
    return next_var;
  }
	 
  PureBooleans::PureBooleans (Graphs::BooleanGraph *bg, int next_var) {
    for (Variables::Variable *gvar : bg->variables)
      { vars[gvar->name] = next_var++; }
  }

  void PureBooleans::read_rules (const std::set<Constraints::Bridi> &rules) {
    for (const Constraints::Bridi &bridi : rules) {
      if (bridi.functor == "=") {
	int coeff {bridi.negation ? 1 : -1};
	clauses.insert ({coeff * vars[bridi.arguments[0]->name], vars[bridi.arguments[1]->name]});
	clauses.insert ({coeff * vars[bridi.arguments[1]->name], vars[bridi.arguments[0]->name]});
      }
      else
	{ std::cout << bridi << " to SAT::PureBooleans.\n"; }
    }
  }
  
  void PureBooleans::to_solver (CaDiCaL::Solver *solver) {
    if (vars.contains ("TRUE"))
      { solver->add (vars["TRUE"]), solver->add (0); }
    if (vars.contains ("FALSE"))
      { solver->add (-vars["FALSE"]), solver->add (0); }

    for (const std::vector<int> &clause : clauses)
      { solver->clause (clause); }
  }

  void PureBooleans::decode (CaDiCaL::Solver *solver, std::ostream &out) {
    for (auto &[name, var] : vars) 
      { out << name << " = " << (solver->val (var) > 0 ? "⊤\n" : "⊥\n"); }
  }
  
  BoolPool::BoolPool (int next_var)
    : t {next_var}, f {next_var + 1} {}

  void BoolPool::to_solver (CaDiCaL::Solver *solver) {
    for (int el : elements) {
      if (el > 0)
	{ iff (el, t, solver); }
      else
	{ iff (-el, f, solver); }
    }
  }

  void BoolPool::decode (CaDiCaL::Solver *solver, std::ostream &out) {
    int truth {solver->val (t)};
    int falsity {solver->val (f)};

    if (truth > 0 && falsity > 0)
      { out << "⊤,⊥"; }
    else if (truth > 0)
      { out << "⊤"; }
    else if (falsity > 0)
      { out << "⊥"; }
  }
   
  Extension::Extension (int size, int start)
    : el_begin {start}, el_end {start + size} {}
    
  int Extension::variable (int pos, int base) const {
    int var {pos + el_begin - base};
    return var >= el_end ? -1 : var;
  }
  
  EnumeratedType::EnumeratedType (const Graphs::EnumeratedType &graph, std::string name, int var_start, CaDiCaL::Solver *solver)
    : rules {graph.rules}, name {name}, dom_size {(int) graph.tokens.size ()}, var_start {var_start} {
    
    int running_count {};
    for (auto var : graph.tokens)
      { tokens[var->name] = running_count++; }

    int running_var {var_start};
    for (auto var : graph.elements) {
      int start;
      start = elements[var->name] = running_var;
      running_var += dom_size;
      exactly_one (start, running_var, solver);
    }

    for (auto &[n, i] : tokens)
      { token_names[i] = n; }

    var_end = running_var;
  }
  
  void EnumeratedType::apply_rule (const Constraints::Bridi &rule, CaDiCaL::Solver *solver) {
    std::string arg1 {rule.arguments[0]->name};
    std::string arg2 {rule.arguments[1]->name};
    int as_int_1 {groundp (arg1) ? get_shift (arg1) : get_start (arg1)};
    int as_int_2 {groundp (arg2) ? get_shift (arg2) : get_start (arg2)};
    if (as_int_1 < 0 || as_int_2 < 0)
      { return; }

    if (rule.functor == "=") {
      if (groundp (arg1)) {
	if (groundp (arg2)) {
	  if (rule.negation ^ (as_int_1 == as_int_2))
	    { return; }
	  else {
	    std::stringstream reason;
	    reason << "Bad rule for enumerated elements: " << rule;
	    bottom (reason.str (), solver);
	  }
	}
	else
	  { solver->add (rule.negation ? -(as_int_1 + as_int_2) : as_int_1 + as_int_2), solver->add (0); }
      }
      else {
	if (groundp (arg2))
	  { solver->add (rule.negation ? -(as_int_1 + as_int_2) : as_int_1 + as_int_2), solver->add (0); }
	else
	  if (rule.negation) {
	    for (int i {}; i < dom_size; ++i) 
	      { solver->add (-i - as_int_1), solver->add (-i - as_int_2), solver->add (0); }
	  }
	  else {
	    for (int i {}; i < dom_size; ++i) {
	      solver->add (-i - as_int_1), solver->add (i + as_int_2), solver->add (0);
	      solver->add (-i - as_int_2), solver->add (i + as_int_1), solver->add (0);
	    }
	  }
      }
    }
    
    else
      { std::cerr << "Unhandled functor, " << rule.functor << ", for enum.\n"; }
  }

  bool EnumeratedType::groundp (const std::string &title) const {
    return tokens.contains (title);
  }

  int EnumeratedType::find_in_map (const std::string &title, const std::map<std::string, int> &map) const {
    auto iter {map.find (title)};
    if (iter != map.cend ())
      { return iter->second; }
    return -1;
  }
  
  int EnumeratedType::get_start (const std::string &title) const {
    int st {find_in_map (title, elements)};
    if (st < 0)
      { std::cerr << "EnumeratedType: " << title << " is not element of " << name << ".\n"; }
    return st;
  }

  int EnumeratedType::get_shift (const std::string &title) const {
    int sh {find_in_map (title, tokens)};
    if (sh < 0)
      { std::cerr << "EnumeratedType: " << title << " is not ground in " << name << ".\n"; }
    return sh;
  }

  std::string EnumeratedType::get_name (int i) const {
    return token_names.at (i);
  }
  
  std::string EnumeratedType::val (const std::string &to_check, CaDiCaL::Solver *solver) const {
    int i {};
    int start {elements.at (to_check)};
    for ( ; i < dom_size; ++i) {
      int val {solver->val (i + start)};
      if (val > 0)
	{ break; }
    }
    
    auto iter {tokens.cbegin ()};
    for ( ; i > 0; --i, ++iter) {}
    return iter->first;
  }

  void EnumeratedType::decode (CaDiCaL::Solver *solver, std::ostream &out) const {
    for (auto &[name, start] : elements) 
      { out << name << " = " << val (name, solver) << '\n'; }
  }

  PowEnum::PowEnum (const Graphs::EnumSubset &subset, const std::map<std::string, EnumeratedType *> &enums, int var_start)
    : name {subset.name}, var_start {var_start} {
    home = enums.at (subset.type->name);
    var_end = var_start + (int) home->tokens.size ();

    auto loc {subset.as_set_var->canonical && subset.as_set_var->canonical->name.substr (0, 5) != "group"
	      ? subset.as_set_var->canonical : subset.as_set_var};
    Variables::Set *as_canon_set {(Variables::Set *) loc};

    if (as_canon_set && as_canon_set->name.substr (0, 5) != "group") {
      for (auto var : as_canon_set->canonical_elements)
	{ definite_elements.insert (home->tokens[var->canonical->name] + var_start); }
      if (as_canon_set->canonical) {
	for (int i {var_start}; i < var_end; ++i) {
	  if (!definite_elements.contains (i))
	    { definite_elements.insert (-i); }
	}
      }
      
      for (auto var : as_canon_set->elements)
	{ other_elements.insert (var->name); }
      for (auto var : as_canon_set->nogoods)
	{ other_nogoods.insert (var->name); }
    }
  }

  void PowEnum::to_solver (CaDiCaL::Solver *solver) {
    for (int def : definite_elements)
      { solver->add (def), solver->add (0); }
    if (!other_elements.empty () || !other_nogoods.empty ()) {
      std::cerr << "PowEnum " << name << " has unground (un)elements: ";
      for (const std::string &str : other_elements)
	{ std::cerr << str << ' '; }
      for (const std::string &str : other_nogoods)
	{ std::cerr << str << ' '; }
      std::cerr << '\n';
    }
  }

  void PowEnum::decode (CaDiCaL::Solver *solver, std::ostream &out) {
    bool already {false};
    out << name << " = {";
    for (int i {var_start}, j {}; i < var_end; ++i, ++j) {
      if (solver->val (i) > 0) {
	out << (already ? "," : "") << home->get_name (j);
	already = true;
      }
    }
    out << "}\n";
  }

  int get_index (auto &&loc, auto goal, auto &&collisions) {
    if (goal->canonical)
      { goal = goal->canonical; }
    auto iter (loc.find (goal));
    if (iter == loc.cend ()) {
      if (collisions.contains (goal)) {
	goal = collisions.at (goal);
	iter = loc.find (goal);
      }
      return -1;
    }
    return (int) std::distance (loc.cbegin (), loc.find (goal));
  }

  Type::Type (int own_size, int known_dom_size, int total_dom_size, int start)
    : extensions (own_size), known_dom_size {known_dom_size}, total_dom_size {total_dom_size} {
    for (int i {}; i < own_size; ++i) {
      extensions[i] = new Extension {total_dom_size, start};
      start += total_dom_size;
    }
    var_end = start;
  }

  Type::~Type () {
    for (Extension *ex : extensions)
      { delete ex; }
  }

  int Type::get_own_size () const {
    return extensions.size ();
  }

  int Type::get_known_dom_size () const {
    return known_dom_size;
  }

  int Type::get_total_dom_size () const {
    return total_dom_size;
  }

  int Type::element_var (int set, int el, int base) const {
    return extensions.at (set)->variable (el < 0 ? -el : el, base);
  }

  void PowInt::get_rules (const std::set<Constraints::Bridi> &rules) {
    for (const Constraints::Bridi &bridi : rules) {
      if (bridi.functor == ":") {
	int el {get_index (graph->dom->variables, bridi.arguments[0], graph->dom->collisions) + 1};
	if (!el)
	  { return; }
	int set {get_index (graph->variables, bridi.arguments[1], graph->collisions)};
	get_element_rule (bridi, el, set);
      }
      else {
	int region_1 {get_index (graph->variables, bridi.arguments[0], graph->collisions)};
	int region_2 {get_index (graph->variables, bridi.arguments[1], graph->collisions)};
	get_rcc_rule (bridi, region_1, region_2);
      }
    }
  }

  void Type::no_double_counting (int set, CaDiCaL::Solver *solver, const std::set<Variables::Variable *, Variables::VarPtrComp> &dom_var_location) {
    int total_idx_i {};
    int non_canon_idx {};
    for (auto dom_iter : dom_var_location) {
      if (dom_iter->canonical)
	{ ++total_idx_i; continue; }
      int canonical {};
      int own_var {element_var (set, total_idx_i, 0)};
      int total_idx_j {};
      for (auto other_iter : dom_var_location) {
	if (dom_iter == other_iter)
	  { ++total_idx_j; continue; }
	std::vector<int> clause (3);
	clause[0] = -own_var;
	if (other_iter->canonical) 
	  { clause[1] = -get_eq_var (total_idx_i, canonical++, true); } // CHECK
	else {
	  if (total_idx_i < total_idx_j) {
	    if (total_idx_j > canonical_in_dom)
	      { goto big_break; }
	    else
	      { ++total_idx_j; continue; }
	  }
	  else
	    { clause[1] = -get_eq_var (total_idx_i, total_idx_j - canonical, false); }
	}
	clause[2] = -element_var (set, total_idx_j, 0);

	solver->clause (clause);
	++non_canon_idx;
	++total_idx_j;
      }
    big_break:
	
      ++total_idx_i;
    }
  }

  int Type::eq_el_array (int var_start, CaDiCaL::Solver *solver, const std::set<Variables::Variable *, Variables::VarPtrComp> &dom_variables) {
    // 1 | canon |
    // 2 | canon | 1
    // 3 | canon | 1 2
    int pos {-1};
    for (Variables::Variable *v : dom_variables) {
      ++pos;
      if (!v->canonical)
	{ eq_el_vars[pos] = {-1, -1}; }
    }
    for (++pos; pos < get_total_dom_size (); ++pos)
      { eq_el_vars[pos] = {-1, -1}; }
    
    canonical_in_dom = get_total_dom_size () - eq_el_vars.size ();

    auto set_array
      { [this] (int var_start, int dist, std::array<int, 2> &pair) {
	pair[0] = var_start;
	pair[1] = var_start = var_start + canonical_in_dom + dist;
	return var_start;
      }};

    int i {-1};
    for (auto &[pos, limits] : eq_el_vars)
      { var_start = set_array (var_start, ++i, limits); }

    for (int i {}; i < get_own_size (); ++i)
      { no_double_counting (i, solver, dom_variables); }
    
    return var_start;
  }
  
  int Type::get_eq_var (int non_canon, int comparison, bool canon_comp) const {
    if (canon_comp)
      { return eq_el_vars.at (non_canon)[0] + comparison; }

    int check {eq_el_vars.at (non_canon)[0] + canonical_in_dom + comparison};
    if (check >= eq_el_vars.at (non_canon)[1]) {
      int i {}, both {};
      int new_non_canon {-1}, new_comparison {-1};
      for (auto &[k, v] : eq_el_vars) {
	if (k == non_canon)
	  { new_comparison = i; ++both; }
	if (i == comparison)
	  { new_non_canon = k; ++both; }
	if (both)
	  { break; }
	++i;
      }
      if (new_non_canon < 0) {
	std::cerr << "Element " << non_canon // get_name (non_canon, true)
		  << '[' << comparison << "] not there.\n";
	return -1;
      }
      else 
	{ check = eq_el_vars.at (new_non_canon)[0] + canonical_in_dom + comparison; }
    }
    return check;
  }

  int Type::get_non_canonical_pos (int non_canon) const {
    int i {};
    for (auto &[p, l] : eq_el_vars) {
      if (p == non_canon)
	{ return i; }
      ++i;
    }
    return -1;
  }

  int Type::get_canonical_pos (int canon) const {
    int i {};
    for (auto &[non_canon, l] : eq_el_vars) {
      if (non_canon > canon)
	{ break; }
      ++i;
    }
    return canon - i;
  }

  int Type::get_element_idx (Variables::Variable *el,
			     const std::set<Variables::Variable *, Variables::VarPtrComp> &dom_variables) const {
    auto iter {dom_variables.find (el)};
    if (iter == dom_variables.cend ())
      { return -1; }
    return std::distance (dom_variables.cbegin (), iter) + 1;
  }
	 
  void Type::definite_elements (CaDiCaL::Solver *solver,
				const std::set<Variables::Variable *, Variables::VarPtrComp> &own_variables,
				const std::set<Variables::Variable *, Variables::VarPtrComp> &own_new_variables,
				const std::set<Variables::Variable *, Variables::VarPtrComp> &dom_variables) {
    int i {};
    for (Variables::Variable *var : own_variables) {
      if (own_new_variables.contains (var))
	{ ++i; continue; }
      
      std::set<int> canonical_el;
      Variables::Set *as_set {(Variables::Set *) var};
      for (Variables::Variable *el : as_set->canonical_elements)
	{ canonical_el.insert (get_element_idx (el, dom_variables)); }
      
      if (var->canonical) {
	if (var->name == "INT" || var->name == "NAT" || as_set->type == 'I')
	  { ++i; continue; }
	for (int j {1}; j <= get_total_dom_size (); ++j)
	  { solver->add (canonical_el.contains (j) ? element_var (i, j, 1) : -element_var (i, j, 1)), solver->add (0); }
      }
      else {
	for (int j : canonical_el)
	  { solver->add (element_var (i, j, 1)), solver->add (0); }
	for (Variables::Variable *non_var : as_set->canonical_nogoods)
	  { solver->add (-element_var (i, get_element_idx (non_var, dom_variables), 1)), solver->add (0); }
      }
      ++i;
    }

    for (auto &[set, el] : canonical_element_rules) {
      if (set > 0) {
	int unit {element_var (set, el, 1)};
	solver->clause (el < 0 ? -unit : unit);
      }
    }
  }

  int Type::possible_elements (CaDiCaL::Solver *solver, int next_var,
			       const std::set<Variables::Variable *, Variables::VarPtrComp> &dom_variables) {
    for (auto &[set, el] : other_element_rules) {
      std::vector<int> clause (get_total_dom_size ());
      int coefficient {el < 0 ? -1 : 1}; int coeff_el {coefficient * el};
      int non_canon_idx {get_non_canonical_pos (coeff_el-1)};

      auto handle_non_canonical
	{ [this, non_canon_idx, solver, coefficient, coeff_el, el, set, &clause] (int i, int j, int next_var) {
	  if (i+1 == coeff_el)
	    { clause[i] = coefficient * element_var (set, coeff_el, 1); }
	  else {
	    std::vector<int> affected (2);
	    affected[0] = element_var (set, i, 0);
	    if (j < non_canon_idx)
	      { affected[1] = get_eq_var (coeff_el-1, j, false); }
	    else
	      { affected[1] = get_eq_var (i, non_canon_idx, false); }
	    next_var = bind_term (next_var, std::move (affected), solver);
	    clause[i] = coefficient * (next_var - 1);
	  }
	  return next_var;
	}};

      auto dom_iter {dom_variables.cbegin ()};
      int j {};
      for (int i {}, canonical {eq_el_vars[coeff_el-1][0]}; dom_iter != dom_variables.cend (); ++dom_iter, ++i) {
	if ((*dom_iter)->canonical) {
	  next_var = bind_term (next_var, {element_var (set, i, 0), canonical++}, solver);
	  clause[i] = coefficient * (next_var - 1);
	}
	else
	  { next_var = handle_non_canonical (i, j, next_var); ++j; }
      }

      for (int i {get_known_dom_size ()}; i < get_total_dom_size (); ++i, ++j) 
	{ next_var = handle_non_canonical (i, j, next_var); }

      if (el > 0)
	{ solver->clause (clause); }
      else {
	for (int lit : clause)
	  { solver->add (lit), solver->add (0); }
      }
    }
    return next_var;
  }

  void Type::impossible_el_equalities (CaDiCaL::Solver *solver,
				       const std::set<Constraints::Bridi> &element_rules,
				       const std::set<Variables::Variable *, Variables::VarPtrComp> &dom_variables,
				       const std::map<Variables::Variable *, Variables::Variable *, Variables::VarPtrComp> &dom_collisions) {
    for (const Constraints::Bridi &bridi : element_rules) {
      if (bridi.negation && bridi.functor == "=") {
	auto var1 {bridi.arguments[0]}, var2 {bridi.arguments[1]};
	int arg1 {get_index (dom_variables, var1, dom_collisions) + 1},
	  arg2 {get_index (dom_variables, var2, dom_collisions) + 1};
	if (!arg1 || !arg2)
	  { return; }
	if (arg1 == arg2) {
	  std::stringstream reason;
	  reason << "Tried to declare " << var1->name << " and " << var2->name << " unequal.";
	  { bottom (reason.str (), solver); }
	}
	if (var1->canonical) {
	  if (var2->canonical) { return; }
	  
	  solver->add (get_eq_var (arg2, get_canonical_pos (arg1), true)), solver->add (0);
	}
	else if (var2->canonical)
	  { solver->add (get_eq_var (arg1, get_canonical_pos (arg2), true)), solver->add (0); }
	else
	  { solver->add (get_eq_var (arg1, get_non_canonical_pos (arg2), false)), solver->add (0); }
      }
      else
	{ std::cout << "INTEGER ELEMENTS: " << bridi << '\n'; }
    }
  }
   
  int Type::get_rcc_start (int first, int second, int &start, int next_var) {
    if (rcc_vars.contains (first)) {
      if (rcc_vars[first].contains (second)) {
	start = rcc_vars[first][second];
	return next_var;
      }
      else 
	{ rcc_vars[first][second] = next_var; }
    }
    else
      { rcc_vars[first] = {{second, next_var}}; }

    start = next_var;
    return next_var + 5;
  }

  int Type::rcc_inclusion_sat (int first, int second, int start, int next_var, bool left_in_right, CaDiCaL::Solver *solver) {
    int inner {extensions[first]->el_begin}, outer {extensions[second]->el_begin};
    if (!left_in_right)
      { std::swap (inner, outer); ++start; }

    if (start <= 0) {
      std::vector<int> aux (get_total_dom_size ());
      for (int i {}; i < get_total_dom_size (); ++i, ++inner, ++outer) {
	solver->add (-inner), solver->add (outer), solver->add (0);
	next_var = aux[i] = bind_term (next_var, {-inner, outer}, solver);
      }
      solver->clause (aux);
    }
    else {
      std::vector<int> aux (get_total_dom_size () + 1);
      for (int i {1}; i <= get_total_dom_size (); ++i, ++inner, ++outer) {
	solver->add (-start), solver->add (-inner), solver->add (outer), solver->add (0);
	next_var = aux[i] = bind_term (next_var, {-inner, outer}, solver);
      }
      aux[0] = -start;
      solver->clause (aux);
    }
    return next_var;
  }

  int Type::rcc_eq_sat (int first, int second, int start, int next_var, CaDiCaL::Solver *solver) {
    if (start <= 0) {
      for (int i {}, left {extensions[first]->el_begin}, right {extensions[second]->el_begin}; i < get_total_dom_size (); ++i, ++left, ++right) {
	solver->add (-left), solver->add (right), solver->add (0);
	solver->add (-right), solver->add (left), solver->add (0);
      }
    }
    else {
      start += 2;
      std::vector<int> aux (get_total_dom_size ());
      for (int i {}, left {extensions[first]->el_begin}, right {extensions[second]->el_begin}; i < get_total_dom_size (); ++i, ++left, ++right) {
	solver->add (-next_var), solver->add (-left), solver->add (right), solver->add (0);
	solver->add (next_var), solver->add (left), solver->add (0);
	solver->add (next_var), solver->add (-right), solver->add (0);
	aux[i] = next_var++;
      }
      bind_term (start, std::move (aux), solver);
    }
    return next_var;
  }

  int Type::rcc_disj_sat (int first, int second, int start, int next_var, CaDiCaL::Solver *solver) {
    if (start <= 0) {
      std::vector<int> left_non_empty (get_total_dom_size ());
      std::vector<int> right_non_empty (get_total_dom_size ());
      for (int i {}, left {extensions[first]->el_begin}, right {extensions[second]->el_begin};
	   i < get_total_dom_size (); ++i, ++left, ++right) {
	solver->add (-left), solver->add (-right), solver->add (0);
	left_non_empty[i] = left;
	right_non_empty[i] = right;
      }
      solver->clause (left_non_empty);
      solver->clause (right_non_empty);
    }
    
    else {
      start += 3;
      std::vector<int> no_ovlp (get_total_dom_size ());
      std::vector<int> left_non_empty (get_total_dom_size ());
      std::vector<int> right_non_empty (get_total_dom_size ());
      for (int i {}, left {extensions[first]->el_begin}, right {extensions[second]->el_begin};
	   i < get_total_dom_size (); ++i, ++left, ++right) {
	left_non_empty[i] = left; right_non_empty[i] = right;
	next_var = bind_clause (next_var, {-left, -right}, solver);
	no_ovlp[i] = next_var - 1;
      }
      int lne {next_var++}, rne {next_var++}, dc {next_var++};
      bind_clause (lne, std::move (left_non_empty), solver);
      bind_clause (rne, std::move (right_non_empty), solver);
      bind_clause (dc, std::move (no_ovlp), solver);
      bind_term (start, {lne, rne, dc}, solver);
    }
    
    return next_var;
  }

  int Type::rcc_ovlp_sat (int first, int second, int start, int next_var, CaDiCaL::Solver *solver) {
    std::vector<int> both (get_total_dom_size ());
    std::vector<int> left_on (get_total_dom_size ());
    std::vector<int> right_on (get_total_dom_size ());
    for (int i {}, left {extensions[first]->el_begin}, right {extensions[second]->el_begin};
	 i < get_total_dom_size (); ++i, ++left, ++right) {
      next_var = bind_term (next_var, {left, right}, solver);
      both[i] = next_var - 1;

      next_var = bind_term (next_var, {left, -right}, solver);
      left_on[i] = next_var - 1;
	
      next_var = bind_term (next_var, {-left, right}, solver);
      right_on[i] = next_var - 1;
    }

    if (start <= 0) {
      solver->clause (both);
      solver->clause (left_on);
      solver->clause (right_on);
    }
    else {
      start += 4;
      int bo {next_var++}, lo {next_var++}, ro {next_var++};
      bind_clause (bo, std::move (both), solver);
      bind_clause (lo, std::move (left_on), solver);
      bind_clause (ro, std::move (right_on), solver);

      bind_term (start, {bo, lo, ro}, solver);
    }

    return next_var;
  }
      
  int Type::encode_rcc_rule (int first, int second, int val, int next_var, CaDiCaL::Solver *solver) {
    if (first > second) {
      std::swap (first, second);
      val = converse (val);
    }

    int start {-1};
    if (!single (val)) 
      { next_var = get_rcc_start (first, second, start, next_var); }

    if (val & SUB)
      { next_var = rcc_inclusion_sat (first, second, start, next_var, true, solver); }
    if (val & SUPER)
      { next_var = rcc_inclusion_sat (first, second, start, next_var, false, solver); }
    if (val & EQ)
      { next_var = rcc_eq_sat (first, second, start, next_var, solver); }
    if (val & DISJ)
      { next_var = rcc_disj_sat (first, second, start, next_var, solver); }
    if (val & OVLP)
      { next_var = rcc_ovlp_sat (first, second, start, next_var, solver); }

    return next_var;
  }
  
  int Type::rcc_in_sat (CaDiCaL::Solver *solver, bool composition, bool eager, int next_var) {
    if (!composition) {
      if (eager) {
	for (int i {}; i < get_own_size (); ++i) {
	  for (int j {i + 1}; j < get_own_size (); ++j) {
	    if (rcc_rules.contains (i) && rcc_rules[i].contains (j))
	      { next_var = encode_rcc_rule (i, j, rcc_rules[i][j], next_var, solver); }
	    else
	      { next_var = encode_rcc_rule (i, j, RCC_U, next_var, solver); }
	  }
	}
      }
      else {
	for (auto &[first, body] : rcc_rules) {
	  for (auto &[second, val] : body) 
	    { next_var = encode_rcc_rule (first, second, val, next_var, solver); }
	}
      }
    }
    
    return next_var;
  }

  int Extension::initialize_seq (CaDiCaL::Solver *solver, int next_var) {
    int width {el_end - el_begin};
    SeqEncoding seq_encoding {next_var, width};
    next_var = seq_encoding (solver, el_begin, el_end, next_var);
    seq_start = seq_encoding.s_idx (width, 1);
    seq_end = seq_encoding.s_idx (width, width);
    return next_var;
  }
    
  int Extension::get_nth_size_var (int n) {
    if (!seq_start || n <= 0)
      { return 0; }
    --n;
    n += seq_start;
    return n >= seq_end ? 0 : n;
  }
    
  SetType::SetType (int own_size, int known_size, int total_size, int start)
    : Type {own_size, known_size, total_size, start} {}

  int SetType::to_solver (CaDiCaL::Solver *solver, int next_var) {
    definite_elements (solver, graph->variables, graph->new_variables, graph->dom->variables);
    // Use RCC = by negating
    next_var = eq_el_array (next_var, solver, graph->dom->variables);
    next_var = possible_elements (solver, next_var, graph->dom->variables);
    if (graph->dom)
      { impossible_el_equalities (solver, graph->element_rules, graph->dom->variables, graph->dom->collisions); }
    return next_var;
  }

  void SetType::decode (CaDiCaL::Solver *solver, std::ostream &out) {
    if (!extensions.empty ()) {
      auto ext_iter {extensions.cbegin ()};
      auto var_iter {graph->variables.cbegin ()};
      for ( ; ext_iter != extensions.cend (); ++ext_iter, ++var_iter) {
	bool already {false};
	out << (*var_iter)->name << " = {";
	auto dom_iter {graph->dom->variables.cbegin ()};
	int el {(*ext_iter)->el_begin};
	for ( ; dom_iter != graph->dom->variables.cend () && el != (*ext_iter)->el_end; ++dom_iter, ++el) {
	  if (solver->val (el) > 0) {
	    out << (already ? "," : "") << (*dom_iter)->name;
	    already = true;
	  }
	}
	for (int i {} ; el != (*ext_iter)->el_end; ++el, ++i) {
	  if (solver->val (el) > 0) {
	    out << (already ? "," : "") << '_' << i;
	    already = true;
	  }
	}
	out << "}\n";
      }
    }
  }
      
  PowInt::PowInt (Graphs::PowIntGraph *graph, int k, int start)
    : Type {(int) graph->variables.size (), graph->dom_size, graph->dom_size + k, start}, graph {graph} {
    get_rules (graph->rules);
  }

  std::string PowInt::get_name (int i, bool el) const {
    auto iter {el ? graph->dom->variables.cbegin () : graph->variables.cbegin ()};
    if (i < 0)
      { i *= -1; }
    if (i >= graph->dom->variables.size ()) {
      std::stringstream gensym;
      gensym << '_' << i - graph->dom->variables.size ();
      return gensym.str ();
    }
    while (i > 0)
      { --i; ++iter; }
    return (*iter)->name;
  }
    
  void Type::get_element_rule (const Constraints::Bridi &bridi, int el, int set) {
    if (bridi.negation)
      { el *= -1; }
    if (bridi.arguments[0]->canonical)
      { canonical_element_rules.push_back ({set, el}); }
    else
      { std::cout << "BR " << bridi << ' ' << set << ' ' << el << std::endl; other_element_rules.push_back ({set, el}); }
  }
    
  void Type::get_rcc_rule (const Constraints::Bridi &bridi, int region_1, int region_2) {
    int functor {RCC_U};

    if (bridi.functor == "=")
      { functor = EQ; }
    else if (bridi.functor == "<:")
      { functor = SUB | EQ; }
    else if (bridi.functor == "<<:")
      { functor = SUB; }
    else
      { std::cerr << "Missed " << bridi.functor << '\n'; }

    if (bridi.negation)
      { functor = inverse (functor); }

    if (region_2 < region_1) {
      std::swap (region_2, region_1);
      functor = converse (functor);
    }

    if (!rcc_rules.contains (region_1)) 
      { rcc_rules[region_1] = {{region_2, functor}}; }
    else if (!rcc_rules[region_1].contains (region_2))
      { rcc_rules[region_1][region_2] = functor; }
    else
      { rcc_rules[region_1][region_2] = rcc_rules[region_1][region_2] & functor; }
  }
    
  void PowInt::mark_constant (CaDiCaL::Solver *solver, const std::string &compare, bool on) {
    int i {};
    for (auto iter {graph->variables.cbegin ()}; iter != graph->variables.cend (); ++iter, ++i) {
      std::string name {(*iter)->name};
      if (name > compare)
	{ break; }
      if (name == compare) {
	for (int j {extensions[i]->el_begin}; j < extensions[i]->el_end; ++j)
	  { solver->add (on ? j : -j), solver->add (0); }
      }
    }
  }
    
  void PowInt::empty_set_is_empty (CaDiCaL::Solver *solver) {
    mark_constant (solver, "{}", false);
  }
  
  void PowInt::all_ints_are_int (CaDiCaL::Solver *solver) {
    mark_constant (solver, "INT", true);
  }

  int PowInt::to_solver (CaDiCaL::Solver *solver, int next_var) {
    all_ints_are_int (solver);
    definite_elements (solver, graph->variables, graph->new_variables, graph->dom->variables);
    next_var = eq_el_array (next_var, solver, graph->dom->variables);
    next_var = possible_elements (solver, next_var, graph->dom->variables);
    impossible_el_equalities (solver, graph->element_rules, graph->dom->variables, graph->dom->collisions);
    return next_var;
  }
    
  void PowInt::decode (int set, CaDiCaL::Solver *solver, std::ostream &out) {
    int start {extensions[set]->el_begin};

    std::set<std::string> constants {"INT", "INTEGER", "NAT", "NAT1", "NATURAL", "NATURAL1"};
    std::string name {get_name (set, false)};
    if (constants.find (name) == constants.cend ()) {
      out << name << " = {";
      bool already {false};
      for (int i {}; i < get_total_dom_size (); ++i) {
	if (solver->val (start + i) > 0) {
	  out << (already ? "," : "") << get_name (i, true);
	  already = true;
	}
      }
      out << "}\n";
    }
  }
    
  void PowInt::decode (CaDiCaL::Solver *solver, std::ostream &out) {
    for (int i {}; i < get_own_size (); ++i) 
      { decode (i, solver, out); }
  }
  
  Instance::Instance (Graphs::Multigraph *multigraph, int k) {
    if (multigraph->b_graph) {
      prop_vars = new PureBooleans {multigraph->b_graph, next_var};
      prop_vars->read_rules (multigraph->b_graph->rules);
      next_var += (int) prop_vars->vars.size ();
    }
    if (multigraph->pb_graph) {
      for (Variables::Variable *var : multigraph->pb_graph->variables) {
	bool_sets[var->name] = BoolPool {next_var};
	next_var += 2;
      }
      for (const Constraints::Bridi &rule : multigraph->pb_graph->rules) {
	if (rule.functor == "=") {
	  int coeff {rule.negation ? 1 : -1};
	  int t1 {bool_sets[rule.arguments[0]->name].t}, f1 {bool_sets[rule.arguments[0]->name].f},
	    t2 {bool_sets[rule.arguments[1]->name].t}, f2 {bool_sets[rule.arguments[1]->name].f};
	  if (rule.negation) {
	    int true_in_both {next_var};
	    next_var = bind_term (true_in_both, {t1, t2}, solver);
	    int false_in_both {next_var};
	    next_var = bind_term (false_in_both, {f1, f2}, solver);
	    solver->add (-true_in_both), solver->add (-false_in_both), solver->add (0);
	  }
	  else {
	    iff (t1, t2, solver);
	    iff (f1, f2, solver);
	  }
	}
	else if (rule.functor == ":") 
	  { bool_sets[rule.arguments[1]->name].elements.insert (rule.negation ? -prop_vars->vars[rule.arguments[0]->name] : prop_vars->vars[rule.arguments[0]->name]); }
	else
	  { std::cout << "Missed Rule: " << rule << '\n'; }
      }
    }

    for (auto &[v, gr] : multigraph->enums) {
      EnumeratedType *et {new EnumeratedType {gr, v->name, next_var, solver}};
      enums[et->name] = et;
      next_var = et->var_end;
    }
    for (auto &[v, s_e_ss] : multigraph->enum_subsets) {
      for (const Graphs::EnumSubset &subset : s_e_ss) {
	PowEnum *pow_enum {new PowEnum {subset, enums, next_var}};
	enum_subsets[pow_enum->name] = pow_enum;
	next_var = pow_enum->var_end;
      }
    }
    if (multigraph->pi_graph) {      
      pow_int = new PowInt {multigraph->pi_graph, k, next_var};
      next_var = pow_int->var_end;
    }

    for (auto &[tr, sg] : multigraph->set_graphs) {
      int known_type {(int) sg->dom->variables.size ()};
      SetType *type {new SetType {(int) sg->variables.size (), known_type, known_type + k, next_var}};
      type->graph = sg;
      sets[tr] = type;
      next_var = type->var_end;
    }
  }

  Instance::~Instance () {
    for (auto &[name, et] : enums)
      { delete et; }
    for (auto &[name, es] : enum_subsets)
      { delete es; }
    for (auto &[tr, set] : sets)
      { delete set; }
    delete prop_vars;
    delete pow_int;
    delete solver;
  }

  void Instance::to_solver () {
    prop_vars->to_solver (solver);
    for (auto &[set, pool] : bool_sets)
      { pool.to_solver (solver); }

    for (auto &[enum_name, et] : enums) {
      for (const Constraints::Bridi &bridi : et->rules)
	{ et->apply_rule (bridi, solver);  }
    }
    for (auto &[enum_name, es] : enum_subsets) 
      { es->to_solver (solver); }

    if (pow_int) {
      next_var = pow_int->to_solver (solver, next_var);
      next_var = pow_int->rcc_in_sat (solver, false, false, next_var);
    }

    for (auto &[tr, sg] : sets) {
      next_var = sg->to_solver (solver, next_var);
      next_var = sg->rcc_in_sat (solver, false, false, next_var);
    }
  }

  int Instance::decode (std::ostream &out) {
    int status {solver->solve ()};
    
    if (status == CaDiCaL::SATISFIABLE) {
      std::cout << "SATISFIABLE\n";
      if (prop_vars) { prop_vars->decode (solver, out); }
      for (auto &[name, bp] : bool_sets)
	{ out << name << " = {"; bp.decode (solver, out); out << "}\n"; }
      for (auto &[name, et] : enums)
	{ et->decode (solver, out); }
      for (auto &[name, es] : enum_subsets) 
	{ es->decode (solver, out); }
      if (pow_int && pow_int->get_own_size () > 2)
	{ pow_int->decode (solver, out); }
      for (auto &[tr, st] : sets)
	{ st->decode (solver, out); }
    }
    else
      { out << "UNSATISFIABLE\n"; }
    
    return status;
  }
}
