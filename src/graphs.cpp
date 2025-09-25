#include "graphs.hpp"

#include <algorithm>

namespace Graphs {
  void gather_synonyms (std::map<Variables::Variable *, int, Variables::VarPtrComp> &buffer,
			std::set<Variables::Variable *, Variables::VarPtrComp> &variables,
			std::set<Variables::Variable *, Variables::VarPtrComp> &new_vars,
			std::map<Variables::Variable *, Variables::Variable *, Variables::VarPtrComp> &collisions,
			int typref) {

    std::map<int, std::set<Variables::Variable *, Variables::VarPtrComp>> groups;
    for (auto &[v, i] : buffer) {
      if (groups.contains (i))
	{ groups[i]. insert (v); }
      else
	{ groups[i] = {v}; }
    }

    for (auto &[i, set] : groups) {
      std::stringstream name;
      name << "group" << typref << "::" << i;
      Variables::VarGroup *var_group {new Variables::VarGroup {name.str (), set}};

      if (variables.contains ((Variables::Variable *) var_group))
	{ delete var_group; }
      else {
	var_group->take_ownership (set);
	variables.insert ((Variables::Variable *) var_group);
	new_vars.insert ((Variables::Variable *) var_group);
	for (Variables::Variable *gr : set)
	  { collisions[gr] = (Variables::Variable *) var_group; }
      }
    }
  }
  
  EnumeratedType::EnumeratedType (const std::string &name,
				  std::set<Variables::EnumInt *> tokens,
				  std::set<Variables::Variable *> elements)
    : name {name} {
    for (Variables::EnumInt *tok : tokens)
      { this->tokens.insert (tok); }
    for (Variables::Variable *var : elements)
      { this->elements.insert (var); }
  }
	
  EnumeratedType::~EnumeratedType () {
    for (Variables::Variable *vg : new_variables)
      { delete vg; }
  }

  EnumSubset::EnumSubset (EnumeratedType &type, Variables::Variable *var)
    : type {&type}, as_set_var {(Variables::Set *) (var->canonical ? var->canonical : var)}, name {as_set_var->name} {}
  
  bool EnumSubset::operator < (const EnumSubset &other) const {
    return name < other.name;
  }
  
  void TyprefGraph::add_alias (std::map<Variables::Variable *, int, Variables::VarPtrComp> &collisions, Variables::Variable *var, int &i, bool add) const {
    if (!collisions.contains (var)) {
      collisions[var] = add ? ++i : i; 
      for (Variables::Variable *al : var->alias) {
	if (al != var)
	  { add_alias (collisions, al, i, false); }
      }
    }
  }

  bool TyprefGraph::thin_doubles (const std::map<int, std::set<Variables::Variable *, Variables::VarPtrComp>> &source, int &msf) {

    if (!source.contains (typref))
      { return false; }

    bool something {false};
    std::map<Variables::Variable *, int, Variables::VarPtrComp> buffer;
    int i {};

    for (Variables::Variable *var : source.at (typref)) {
      if (var->canonical) {
	this->insert_canonical (var, msf); 
	variables.insert (var->canonical);
      }
      else if (var->alias.empty ()) {
	this->insert_loose_var (var, msf);
	variables.insert (var);
      }
      else 
	{ add_alias (buffer, var, i, true); }
      something = true;
    }

    gather_synonyms (buffer, variables, new_variables, collisions, typref);

    return something;
  }

  void TyprefGraph::insert_canonical (Variables::Variable *var, int &msf) {}
  void TyprefGraph::insert_loose_var (Variables::Variable *var, int &msf) {}
  
  void TyprefGraph::print (std::ostream &out) {
    for (const Constraints::Bridi &bridi : rules)
      { out << bridi << '\n'; }
  }

  int TyprefGraph::get_prim_typref (const Constraints::Constraints &constraints, const std::string &type) const {
    for (auto &[k, v] : constraints.prim_types)
      { if (v == type) { return k; } }
    return -1;
  }
  
  BooleanGraph::BooleanGraph (const Constraints::Constraints &constraints) {
    typref = get_prim_typref (constraints, "BOOL");
    int ignore {-1};
    thin_doubles (constraints.variables->prim_vars, ignore);
    relevant_constraints (constraints);
  }

  BooleanGraph::~BooleanGraph () {
    for (Variables::Variable *var : new_variables)
      { delete var; }
  }

  void BooleanGraph::relevant_constraints (const Constraints::Constraints &constraints) {
    for (auto &[p, con] : constraints.constraint_graph.constraints) {
      for (const Constraints::Bridi &bridi : con) {
	std::vector<Variables::Variable *> arguments;
	bool save {true};

	for (Variables::Variable *arg : bridi.arguments) {
	  if (arg->typref == typref) 
	    { arguments.push_back (arg->canonical ? arg->canonical : arg); }
	  else { save = false; break; }
	}

	if (save)
	  { rules.insert (Constraints::Bridi {arguments, bridi.functor, bridi.negation}); }
      }
    }
  }
    
  IntegerGraph::IntegerGraph (const Constraints::Constraints &constraints) {
    typref = get_prim_typref (constraints, "INTEGER");
  }

  IntegerGraph::~IntegerGraph () {
    for (Variables::Variable *var : new_variables)
      { delete var; }
  }
    
  void IntegerGraph::thin_doubles (const std::map<int, std::set<Variables::Variable *, Variables::VarPtrComp>> &source, int typref, std::map<Variables::Variable *, EnumeratedType, Variables::VarPtrComp> &enums, bool validity_check) {
    if (!source.contains (typref))
      { return; }

    std::map<Variables::Variable *, std::map<Variables::Variable *, int, Variables::VarPtrComp>, Variables::VarPtrComp> buffers;
    Variables::Variable pure_int {"NULL", typref};
    buffers[&pure_int] = {};
    int i {};

    for (Variables::Variable *var : source.at (typref)) {
      Variables::Primitive *as_prim {(Variables::Primitive *) var};
      if (as_prim->type == 'E') {
	if (var->canonical == var) {
	  Variables::EnumInt *token {(Variables::EnumInt *) var};
	  if (enums.contains (token->home))
	    { enums[token->home].tokens.insert (token); }
	  else
	    { enums[token->home] = EnumeratedType {token->home->name, {token}, {}}; }
	}
	else {
	  Variables::Integer *el {(Variables::Integer *) var};
	  if (var->alias.empty ()) {
	    if (enums.contains (el->enumerated))
	      { enums[el->enumerated].elements.insert (var); }
	    else
	      { enums[el->enumerated] = EnumeratedType {el->enumerated->name, {}, {var}}; }
	  }
	  else {
	    if (buffers.contains (el->enumerated))
	      { add_alias (buffers[el->enumerated], var, i, true); }
	    else {
	      buffers[el->enumerated] = {};
	      add_alias (buffers[el->enumerated], var, i, true);
	    }
	  }
	}
      }
      else if (var->canonical) 
	{ variables.insert (var->canonical); }
      else if (var->alias.empty ()) {
	if (validity_check)
	  { skip.insert (var); }
	else
	  { variables.insert (var); }
      }
      else {
	if (validity_check)
	  { skip.insert (var); }
	else
	  { add_alias (buffers[&pure_int], var, i, true); }
      }
    }

    gather_synonyms (buffers[&pure_int], variables, new_variables, collisions, typref);
    buffers.erase (&pure_int);
    for (auto &[e, meration] : buffers)
      { gather_synonyms (meration, enums[e].elements, enums[e].new_variables, enums[e].collisions, typref); }
  }
	  
  void IntegerGraph::relevant_constraints (const Constraints::Constraints &constraints, std::map<Variables::Variable *, EnumeratedType, Variables::VarPtrComp> &enums) {
    
    for (auto &[p, con] : constraints.constraint_graph.constraints) {
      for (const Constraints::Bridi &bridi : con) {
	std::vector<Variables::Variable *> arguments;
	bool save {true};
	Variables::Variable *enumeration {nullptr};

	for (Variables::Variable *arg : bridi.arguments) {
	  if (arg->typref == typref) {
	    if (variables.contains (arg->canonical ? arg->canonical : arg)) {
	      arguments.push_back (arg->alias.empty () ? arg : collisions[arg]);
	      continue;
	    }
	    else if (skip.contains (arg))
	      { save = false; break; }
	    
	    else {
	      auto to_push_back
		{ [enums] (Variables::Variable *arg, Variables::Variable *enumeration) {
		  if (enums.at (enumeration).tokens.contains ((Variables::EnumInt *) arg)
		      || enums.at (enumeration).elements.contains (arg))
		    { return arg; }
		  else
		    { return enums.at (enumeration).collisions.at (arg); }
		}};
	      
	      Variables::Variable *new_enum {arg->canonical == arg ? ((Variables::EnumInt *) arg)->home
					     : ((Variables::Integer *) arg)->enumerated};

	      if (enumeration) {
		if (enumeration != new_enum)
		  { std::cerr << "Unmatched enums: " << enumeration->name << ' ' << new_enum->name << '\n'; }
		else {
		  arguments.push_back (to_push_back (arg, enumeration));  
		  continue;
		}
	      }
	      else {
		enumeration = new_enum;
		arguments.push_back (to_push_back (arg, enumeration));
		continue;
	      }
	    }
	  }
	  save = false;
	  break;
	}

	if (save) {
	  if (bridi.negation || bridi.functor != "=" || arguments[0] != arguments[1]) {
	    std::set<Constraints::Bridi> &loc {enumeration == nullptr
					       ? rules
					       : enums[enumeration].rules};
	    loc.insert (Constraints::Bridi {arguments, bridi.functor, bridi.negation});
	  }
	}
      }
    }
  }

  void IntegerGraph::group_synonyms () {
    auto new_const
      { [this] (long long value) {
	Variables::Variable not_ptr {std::to_string (value), typref};
	Variables::Variable *ptr;
	auto iter {variables.find (&not_ptr)};
	if (iter == variables.end ()) {
	  iter = new_variables.find (&not_ptr);
	  if (iter == new_variables.end ()) {
	    ptr = (Variables::Variable *) new Variables::Integer {not_ptr.name, typref};
	    new_variables.insert (ptr);
	  }
	  else 
	    { ptr = *iter; }
	}
	else
	  { ptr = *iter; }
	return ptr;
      }};

    auto get_int
      { [] (Variables::Variable *v, int bound) {
	Variables::Integer *as_int {(Variables::Integer *) v};
	return as_int->bounds[bound];
      }};
    auto get_group
      { [] (Variables::Variable *v, int bound) {
	Variables::VarGroup *group {(Variables::VarGroup *) v};
	long long limit {bound ? LLONG_MAX : LLONG_MIN};
	for (Variables::Variable *a : group->class_vars) {
	  Variables::Integer *as_int {(Variables::Integer *) a};
	  if (bound)
	    { limit = limit <= as_int->bounds[bound] ? limit : as_int->bounds[bound]; }
	  else
	    { limit = limit >= as_int->bounds[bound] ? limit : as_int->bounds[bound]; }
	}
	return limit;
      }};
      
    for (Variables::Variable *var : variables) {
      if (!var->canonical) {
	bool group {!var->alias.empty ()};

	if (group) {
	  Variables::VarGroup *as_vg {(Variables::VarGroup *) var};
	  for (Variables::Variable *version : as_vg->class_vars) {
	    Variables::Integer *as_int {(Variables::Integer *) version};
	    if (as_int->enumerated) {
	      as_vg->enumerated = as_int->enumerated;
	      break;
	    }
	  }
	}
	
	for (int i {}; i < 2; ++i) {
	  long long bound {group ? get_group (var, i) : get_int (var, i)};
	  if (bound != (i ? LLONG_MAX : LLONG_MIN)) {
	    rules.insert (Constraints::Bridi {{var, new_const (bound)}, i ? "<=" : ">=", false});
	  }
	}
      }
    }
  }
  
  void IntegerGraph::print (std::ostream &out) {
    std::cout << "#vars:" << variables.size () << '\n';
    for (const Constraints::Bridi &bridi : rules) {
      out << bridi << ' ';
      for (Variables::Variable *arg : bridi.arguments) {
	if (!arg->alias.empty ()) {
	  { out << arg->name << "enumerated"; break; }
	}
      }
      out << '\n';
    }
  }

  PowIntGraph::PowIntGraph (const Constraints::Constraints &constraints, IntegerGraph *dom, int typref)
    : dom {dom} {
    dom_size = (int) dom->variables.size ();
    this->typref = typref;
  }
  
  PowIntGraph::~PowIntGraph () {
    for (Variables::Variable *var : new_variables)
      { delete var; }
  }

  void PowIntGraph::nats_are_non_neg (const std::string &nat_name, int comparison) {
    auto iter {std::find_if (variables.cbegin (), variables.cend (), [&nat_name] (Variables::Variable *v) { return v->name == nat_name; })};
    if (iter != variables.cend ()) {
      for (Variables::Variable *var : dom->variables) {
	if (var->canonical) {
	  Variables::ConstInt *as_int {(Variables::ConstInt *) var->canonical};
	  rules.insert (Constraints::Bridi {{var, *iter}, ":", as_int->value < comparison});
	}
      }
    }
  }
  
  bool PowIntGraph::thin_doubles (const std::map<int, std::set<Variables::Variable *, Variables::VarPtrComp>> &source,
				  std::map<Variables::Variable *, EnumeratedType, Variables::VarPtrComp> &enums,
				  std::map<Variables::Variable *, std::set<EnumSubset>, Variables::VarPtrComp> &enum_subsets, int &msf) {
    if (!source.contains (typref))
      { return false; }

    bool something {false};

    auto handle_enum
      { [&enums, &enum_subsets] (Variables::Variable *var) mutable {
	Variables::Set *as_set {(Variables::Set *) var};
	if (as_set->enumerated) {
	  if (as_set->enumerated != as_set && as_set->enumerated != as_set->canonical) {
	    EnumSubset es {enums.at (as_set->enumerated), as_set};
	    if (enum_subsets[as_set->enumerated].contains (es))
	      { return true; }
	    enum_subsets[as_set->enumerated].insert (es);
	  }
	  return true;
	}
	else
	  { return false; }
      }};

    std::map<Variables::Variable *, int, Variables::VarPtrComp> buffer;
    int i {};
    for (Variables::Variable *var : source.at (typref)) {
      if (handle_enum (var)) { continue; }
      else {
	if (var->canonical) {
	  if (handle_enum (var->canonical))
	    { continue; }
	  else {
	    msf += ((Variables::Set *) var->canonical)->canonical_elements.size ();
	    variables.insert (var->canonical);
	  }
	}
	else if (var->alias.empty ())
	  { ++msf; variables.insert (var); }
	else
	  { add_alias (buffer, var, i, true); }
	something = true;
      }
    }

    gather_synonyms (buffer, variables, new_variables, collisions, typref);

    return something;
  }
  
  void PowIntGraph::relevant_constraints (const Constraints::Constraints &constraints,
					  std::map<Variables::Variable *, EnumeratedType, Variables::VarPtrComp> &enums,
					  std::map<Variables::Variable *, std::set<EnumSubset>, Variables::VarPtrComp> &enum_subsets) {
    for (auto &[p, con] : constraints.constraint_graph.constraints) {
      for (const Constraints::Bridi &bridi : con) {
	std::vector<Variables::Variable *> arguments;
	Variables::Variable *enumerated {nullptr};
	bool save {true};
	int num_el {};
	for (Variables::Variable *arg : bridi.arguments) {
	  if (arg->typref != typref && arg->typref != dom->typref)
	    { save = false; break; }
	  
	  else {
	    auto handle_enum
	      { [this, &num_el, &arguments] (Variables::Variable *arg) {
		Variables::Variable *enumerated {nullptr};
		if (arg->typref == typref) {
		  Variables::Set *as_set {(Variables::Set *) arg};
		  enumerated = as_set->enumerated;
		}
		else {
		  ++num_el;
		  if (arg->canonical)
		    { enumerated = ((Variables::EnumInt *) arg->canonical)->home; }
		  else 
		    { enumerated = ((Variables::Integer *) arg)->enumerated; }
		}
		arguments.push_back (arg);
		return enumerated;
	      }};

	    auto handle_int
	      { [this, &arguments, &num_el] (Variables::Variable *arg) {
		if (arg->typref == dom->typref)
		  { ++num_el; }
		arguments.push_back (arg);
	      }};

	    if (arg->canonical)
	      { arg = arg->canonical; }

	    if (variables.contains (arg) || dom->variables.contains (arg))
	      { handle_int (arg); }
	    else
	      { enumerated = handle_enum (arg); }
	  }
	}

	if (save) {
	  if (bridi.negation || bridi.functor != "=" || arguments[0] != arguments[1]) {
	    if (enumerated) {
	      if (num_el < 2) {
		for (const EnumSubset &es : enum_subsets.at (enumerated)) {
		  if (es.name == arguments[1]->name)
		    { const_cast<EnumSubset &> (es).rules.insert (Constraints::Bridi {arguments, bridi.functor, bridi.negation}); break; }
		}
	      }
	      else { continue; }
	    }
	    
	    if (num_el >= 2)
	      { element_rules.insert (Constraints::Bridi {arguments, bridi.functor, bridi.negation}); }
	    else
	      { rules.insert (Constraints::Bridi {arguments, bridi.functor, bridi.negation}); }
	  }
	}
      }
    }

    nats_are_non_neg ("NAT", 0);
    nats_are_non_neg ("NATURAL", 0);
    nats_are_non_neg ("NAT1", 1);
    nats_are_non_neg ("NATURAL1", 1);
  }

  PowBoolGraph::PowBoolGraph (const Constraints::Constraints &constraints, BooleanGraph *dom, int typref)
    : dom {dom} {
    dom_size = 2;
    this->typref = typref;
  }

  PowBoolGraph::~PowBoolGraph () {
    for (Variables::Variable *var : new_variables)
      { delete var; }
  }
  
  void PowBoolGraph::relevant_constraints (const Constraints::Constraints &constraints) {
    for (auto &[p, con] : constraints.constraint_graph.constraints) {
      for (const Constraints::Bridi &bridi : con) {
	std::vector<Variables::Variable *> arguments;
	bool save {true};
	int num_el {};
	
	for (Variables::Variable *arg : bridi.arguments) {
	  if (arg->typref != typref && arg->typref != dom->typref)
	    { save = false; break; }
	  else {
	    if (arg->typref == dom->typref)
	      { ++num_el; }
	    TyprefGraph *search_loc {arg->typref == typref ? (TyprefGraph *) this : (TyprefGraph *) dom};
	    arguments.push_back (arg->alias.empty () ? arg : search_loc->collisions[arg]);
	  }
	}
	if (save && num_el < 2) {
	  if (bridi.negation || bridi.functor != "=" || arguments[0] != arguments[1])
	    { rules.insert (Constraints::Bridi {arguments, bridi.functor, bridi.negation}); }
	}
      }
    }
  }
  
  SetGraph::SetGraph (int typref, int dom)
    : dom_typref {dom} {
    this->typref = typref;
  }

  SetGraph::SetGraph (const Constraints::Constraints &constraints, int typref, int dom)
    : dom_typref {dom} {
    this->typref = typref;
  }
    
  SetGraph::~SetGraph () {
    for (Variables::Variable *var : new_variables)
      { delete var; }
  }
  
  void SetGraph::setup (const Constraints::Constraints &constraints, TyprefGraph *dom) {
    this->dom = dom;
    if (dom)
      { dom_size = (int) ((SetGraph *) dom)->variables.size (); }
    if (thin_doubles (constraints.variables->set_vars, typref) || thin_doubles (constraints.variables->rel_vars, typref))
      { relevant_constraints (constraints); }
  }
	    
  void SetGraph::relevant_constraints (const Constraints::Constraints &constraints) {
    for (auto &[p, con] : constraints.constraint_graph.constraints) {
      for (const Constraints::Bridi &bridi : con) {
	std::vector<Variables::Variable *> arguments;
	bool save {true};
	for (Variables::Variable *arg : bridi.arguments) {
	  if (arg->typref != typref && arg->typref != dom_typref)
	    { save = false; break; }
	  else {
	    TyprefGraph *search_loc {arg->typref == typref ? (TyprefGraph *) this : dom};
	    arguments.push_back (arg->alias.empty () ? arg : search_loc->collisions[arg]);
	  }
	}
	if (save) {
	  if (bridi.negation || bridi.functor != "=" || arguments[0] != arguments[1])
	    { rules.insert (Constraints::Bridi {arguments, bridi.functor, bridi.negation}); }
	}
      }
    }

    // Cardinalities
  }

  void SetGraph::insert_canonical (Variables::Variable *var, int &msf) {
    msf += ((Variables::Set *) var->canonical)->canonical_elements.size ();
  }

  void SetGraph::insert_loose_var (Variables::Variable *var, int &msf) {
    ++msf;
  }

  RelGraph::RelGraph (int typref, int dom_typref, int ran_typref)
    : dom_typref {dom_typref}, ran_typref {ran_typref} {
    this->typref = typref;
  }

  RelGraph::~RelGraph () {
    for (Variables::Variable *var : new_variables)
      { delete var; }
  }

  void RelGraph::setup (const Constraints::Constraints &constraints, TyprefGraph *from, TyprefGraph *to) {
    this->from = from; this->to = to;
    if (from)
      { dom_size = (int) from->variables.size (); }
    if (to)
      { cod_size = (int) to->variables.size (); }
    if (thin_doubles (constraints.variables->mapping_vars, typref))
      { relevant_constraints (constraints); }
  }

  void RelGraph::relevant_constraints (const Constraints::Constraints &constraints) {
    for (auto &[p, con] : constraints.constraint_graph.constraints) {
      for (const Constraints::Bridi &bridi : con) {
	std::vector<Variables::Variable *> arguments;
	bool save {true};
	for (Variables::Variable *arg : bridi.arguments) {
	  if (arg->typref != typref && arg->typref != dom_typref && arg->typref != ran_typref)
	    { save = false; break; }
	  else {
	    TyprefGraph *search_loc {arg->typref == typref ? (TyprefGraph *) this : arg->typref == dom_typref ? from : to};
	    arguments.push_back (arg->alias.empty () ? arg : search_loc->collisions[arg]);
	  }
	}
	if (save) {
	  if (bridi.negation || bridi.functor != "=" || arguments[0] != arguments[1])
	    { rules.insert (Constraints::Bridi {arguments, bridi.functor, bridi.negation}); }
	}
      }
    }
  }

  Multigraph::Multigraph (const Constraints::Constraints &constraints, bool validity_check) 
    : i_graph {new IntegerGraph {constraints}}, b_graph {new BooleanGraph {constraints}}, validity_check {validity_check} {
    sort_integers (constraints.variables->prim_vars, constraints, i_graph->typref, validity_check);

    for (auto s : constraints.type_infos->sets) {
      if (s.body == i_graph->typref) {
	pi_graph = new PowIntGraph {constraints, i_graph, s.id};
	sort_pow_int (constraints, s.id, validity_check);
      }
      else if (s.body == b_graph->typref) {
	pb_graph = new PowBoolGraph {constraints, b_graph, s.id};
	pb_graph->thin_doubles (constraints.variables->set_vars, msf);
	pb_graph->relevant_constraints (constraints);
      }
      else 
	{ set_graphs[s.id] = new SetGraph {s.id, s.body}; }
    }
    for (auto r : constraints.type_infos->relations) 
      { set_graphs[r.id] = new SetGraph {r.id, r.body}; }
    for (auto m : constraints.type_infos->mappings)
      { rel_graphs[m.id] = new RelGraph {m.id, m.body[0], m.body[1]}; }
    
    for (auto &[tr, gr] : set_graphs) {
      auto find_for_setup
	{ [this, &constraints, gr] (auto &&map) {
	  auto iter {map.find (gr->dom_typref)};
	  if (iter != map.cend ())
	    { gr->setup (constraints, (TyprefGraph *) iter->second); }
	  else
	    { gr->setup (constraints, nullptr); }
	}};
    
      if (Variables::MAPS == constraints.get_concept (gr->dom_typref))
	{ find_for_setup (rel_graphs); }
      else {
	if (pi_graph && gr->dom_typref == pi_graph->typref) 
	  { gr->dom = pi_graph; }
	else if (pb_graph && gr->dom_typref == pb_graph->typref)
	  { gr->dom = pb_graph; }
	else
	  { find_for_setup (set_graphs); }
      }
    }
    for (auto &[tr, gr] : rel_graphs) {
      auto find_for_setup
	{ [this, &constraints] (int typref) {
	  auto search_graph
	    { [typref] (auto &&map) {
	      auto iter {map.find (typref)};
	      return iter != map.cend () ? (TyprefGraph *) iter->second : nullptr;
	    }};
	      
	  if (typref == i_graph->typref)
	    { return (TyprefGraph *) i_graph; }
	  else if (typref == b_graph->typref)
	    { return (TyprefGraph *) b_graph; }
	  else if (typref == pi_graph->typref)
	    { return (TyprefGraph *) pi_graph; }
	  else if (typref == pb_graph->typref)
	    { return (TyprefGraph *) pb_graph; }
	  else if (Variables::MAPS == constraints.get_concept (typref))
	    { return search_graph (rel_graphs); }
	  else
	    { return search_graph (set_graphs); }
	}};
      
      TyprefGraph *from {find_for_setup (gr->dom_typref)}, *to {find_for_setup (gr->ran_typref)};
      if (from && to)
	{ gr->setup (constraints, from, to); }
      else
	{ std::cerr << "Error in setting up rel_graph.\n"; }
    }
  }
  
  Multigraph::~Multigraph () {
    for (auto &[tr, gr] : rel_graphs)
      { delete gr; }
    for (auto &[tr, gr] : set_graphs)
      { delete gr; }
    delete pb_graph;
    delete pi_graph;
    delete b_graph;
    delete i_graph;
  }

  void Multigraph::sort_integers (const std::map<int, std::set<Variables::Variable *, Variables::VarPtrComp>> &source, const Constraints::Constraints &constraints, int typref, bool validity_check) {
    i_graph->thin_doubles (source, typref, enums, validity_check);
    i_graph->relevant_constraints (constraints, enums);
    for (auto &[type, token] : enums)
      { enum_subsets[type] = {}; }
    i_graph->group_synonyms ();
  }

  void Multigraph::sort_pow_int (const Constraints::Constraints &constraints, int typref, bool validity_check) {
    bool thinned {pi_graph->thin_doubles (constraints.variables->set_vars, enums, enum_subsets, msf)};
    if (thinned)
      { pi_graph->relevant_constraints (constraints, enums, enum_subsets); }
  }

  bool Multigraph::to_gqr () { return true; }
  
  TyprefGraph *Multigraph::get_graph_by_typref (int typref, bool prims) {
    auto search_map
      { [typref] (auto &&loc) -> TyprefGraph * {
	for (auto &[tr, gr] : loc) {
	  if (typref > tr)
	    { break; }
	  if (typref == tr)
	    { return gr; }
	}
	return nullptr;
      }};

    TyprefGraph *graph {search_map (set_graphs)};
    if (graph)
      { return graph; }
    graph = search_map (rel_graphs);
    return graph;
  }
    
  void Multigraph::print (std::ostream &out) {
    out << "Z, " << i_graph->typref << ' ';
    i_graph->print (out);
    
    if (pi_graph && !pi_graph->variables.empty ()) {
      out << "\nPow(Z), " << pi_graph->typref << " #vars:" << pi_graph->variables.size () << " |dom|:" << pi_graph->dom_size << '\n';
      pi_graph->print (out);
    }
    
    for (auto &[type, en] : enums) {
      out << '\n' << type->name << ": ";
      for (Variables::EnumInt *type : en.tokens)
	{ out << type->name << ' '; }
      out << '\n';
      for (Variables::Variable *token : en.elements)
	{ out << token->name << ' '; }
      out << '\n';
    }
    
    for (auto &[ty, s] : set_graphs) {
      if (!s->rules.empty ()) {
	out << "\nSet " << ty << ", P(" << s->dom_typref << ") "
	    << "#vars:" << s->variables.size ()
	    << " |dom|:" << s->dom_size << '\n';
	s->print (out);
      }
    }
    out << '\n';
  }
}
