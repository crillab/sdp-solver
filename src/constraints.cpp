#include "constraints.hpp"

#include <numeric>
#include <sstream>

namespace Constraints {

  bool Bridi::operator < (const Bridi &other) const {
    float this_ground {}, other_ground {};
    int signature_diff {};

    auto iter {arguments.cbegin ()}, other_iter {other.arguments.cbegin ()};

    if (functor == other.functor) {
      for ( ; other_iter != other.arguments.cend (); ++iter, ++other_iter) {
	if (iter == arguments.cend ())
	  { signature_diff == -1; break; }

	this_ground += (*iter)->ground;
	other_ground += (*other_iter)->ground;
	
	std::string name {(*iter)->name}, other_name {(*other_iter)->name};
	if (name == other_name) {
	  this_ground += (*iter)->ground;
	  other_ground += (*other_iter)->ground;
	}
	else {
	  signature_diff = name < other_name ? -1 : 1;
	  break;
	}
      }
      if (signature_diff == 0 && iter != arguments.cend ())
	{ signature_diff = 1; }
    }
    else
      { signature_diff = functor < other.functor ? -1 : 1; }

    if (signature_diff == 0)
      { return false; }

    this_ground += acc_grounds (iter, arguments.cend ());
    this_ground /= get_arity () ? get_arity () : 0;
    other_ground += acc_grounds (other_iter, other.arguments.cend ());
    other_ground /= other.get_arity () ? other.get_arity () : 0;

    if (this_ground == other_ground)
      { return signature_diff == -1; }

    return this_ground > other_ground;
  }

  int Bridi::get_arity () const {
    return arguments.size ();
  }

  float Bridi::get_groundness () const {
    if (!get_arity ())
      { return 0.0; }
    return (acc_grounds (arguments.cbegin (), arguments.cend ()) / get_arity ());
  }

  float Bridi::acc_grounds (std::vector<Variables::Variable *>::const_iterator cbegin,
			    std::vector<Variables::Variable *>::const_iterator cend) const {
    return std::accumulate (cbegin, cend, 0.0f,
			    [] (float running, Variables::Variable *current)
			    { return running + current->ground; });
  }

  bool Bridi::consistent_equality (std::set<Bridi> &output, Constraints &constraints) const {
    Variables::Variable *arg1 {arguments[0]}, *arg2 {arguments[1]};

    auto catch_up
      { [&constraints] (Variables::Variable *lead, Variables::Variable *other) {
	switch (lead->super_type) {
	case Variables::PRIM: {
	  Variables::PrimConst *prim {(Variables::PrimConst *) lead->canonical};
	  switch (prim->type) {
	  case 'E':
	  case 'Z': {
	    Variables::Integer *as_int {(Variables::Integer *) other};
	    as_int->update_ground (lead);
	    return;
	  }
	  case 'B':
	    other->update_ground (lead);
	  }
	  return;
	}
	case Variables::SETS: {
	  Variables::Set *as_set {(Variables::Set *) other};
	  as_set->update_ground ((Variables::Set *) lead, constraints.variables);
	  return;
	}}
      }};

    if (!negation) {
      if (arg1->canonical) {
	if (arg2->canonical) {
	  if (!arg1->compare (arg2)) {
	    output.insert (*this);
	    return false;
	  }
	  else
	    { return true; }
	}
	catch_up (arg1, arg2);
	arg2->alias.clear ();
	return true;
      }
      else if (arg2->canonical) {
	catch_up (arg2, arg1);
	arg1->alias.clear ();
	return true;
      }
      else if (constraints.get_concept (arg2->typref) == Variables::SETS && ((Variables::Set *) arg2)->type == 'I') {
	if (constraints.variables->set_to_interval (arg1, arg2))
	  { return true; }
      }
      else
	{ arg1->bind_names (arg2); }
    }
    else { // /=
      if (arg2->name == "{}") {
	Variables::Set *as_set {(Variables::Set *) arg1};
	as_set->set_card (1, true);
	return true;
      }
    }
    
    output.insert (*this);
    return true;
  }

  bool Bridi::consistent_elementhood (std::set<Bridi> &output, Constraints &constraints) const {
    int concept_1 {constraints.get_concept (arguments[0]->typref)};
    if (concept_1 == Variables::PRIM || concept_1 == Variables::SETS)
      { return simple_set_element (output, constraints); }
    else
      { return relation_as_set_element (output, constraints); }
  }

  bool Bridi::relation_as_set_element (std::set<Bridi> &output, Constraints &constraints) const {
    int concept_1 {constraints.get_concept (arguments[0]->typref)};
    int concept_2 {constraints.get_concept (arguments[1]->typref)};

   if (concept_1 == Variables::MAPS && concept_2 == Variables::RELS) {
      Variables::Pair *as_pair {arguments[0]->canonical ? (Variables::Pair *) arguments[0]->canonical : (Variables::Pair *) arguments[0]};
      Variables::SetOfRelations *as_sor {arguments[1]->canonical ? (Variables::SetOfRelations *) arguments[1]->canonical : (Variables::SetOfRelations *) arguments[1]};

      auto get_half
	{ [this, &output, &constraints] (Variables::Pair *el, Variables::SetOfRelations *set, bool left, int set_cod) {
	  int inner_typref {constraints.type_infos->get_home (left ? el->dom_typref : el->cod_typref)}; 
	  Variables::Variable *inner {el->canonical ? left ? el->from : el->to : constraints.surround_var (arguments[0], left ? "dom" : "ran", constraints.get_concept (inner_typref), inner_typref, constraints.constraint_graph)};
	  Variables::Variable *outer {set->canonical ? left ? set->from : set->to : constraints.surround_var (arguments[1], left ? "dom" : "ran", constraints.get_concept (left ? set->dom_typref : set_cod), left ? set->dom_typref : set_cod, constraints.constraint_graph)};
	  output.emplace (Bridi {{inner, outer}, ":", false});
	}};

      auto [_, set_cod] {constraints.type_infos->get_body (as_sor->dom_typref, constraints.type_infos->mappings)};
      get_half (as_pair, as_sor, true, set_cod);                                          get_half (as_pair, as_sor, false, set_cod);
    }

    else {
      Variables::SetOfRelations *element {(Variables::SetOfRelations *) (arguments[0]->canonical ? arguments[0]->canonical : arguments[0])};
      Variables::Set *set {(Variables::Set *) (arguments[1]->canonical ? arguments[1]->canonical : arguments[1])};

      int hash_rels {14};
      std::string rels[hash_rels] {"*s", "+->", "+->>", "-->", "-->>", "<+", "<->", "<<|", "<|", ">+>", ">->", ">->>", "|>", "|>>"};
    
      auto is_included
	{ [&rels, hash_rels] (const std::string &op) {
	  if (op < rels[0] || op > rels[hash_rels - 1])
	    { return -1; }
	  int start {}, end {hash_rels};
	  while (start <= end) {
	    int mid {start + (end - start) / 2};
	    if (op == rels[mid])
	      { return mid; }
	    if (op < rels[mid])
	      { end = --mid; }
	    else
	      { start = ++mid; }
	  }
	  return -1;
	}};

      int rel_idx {is_included (set->name.substr (0, set->name.find ('(')))};
      Variables::Variable *dom {element->from ? element->from : constraints.surround_var ((Variables::Variable *) element, "dom", constraints.get_concept (element->dom_typref), element->dom_typref, constraints.constraint_graph)};
      Variables::Variable *cod {element->to ? element->to : constraints.surround_var ((Variables::Variable *) element, "ran", constraints.get_concept (constraints.get_home (element->to_typref)), constraints.get_home (element->typref), constraints.constraint_graph)};
    }

    output.insert (*this);
    return true;
  }
    
  bool Bridi::simple_set_element (std::set<Bridi> &output, Constraints &constraints) const {
    Variables::Variable *element {arguments[0]};
    Variables::Set *set {(Variables::Set *) arguments[1]};
    
    if (set->canonical && set->canonical != set) {
      Bridi simplification {{element, set->canonical}, functor, negation};
      return simplification.consistent_elementhood (output, constraints);
    }

    if (!negation) {
      if (set->canonical && set->canonical->name == "INT")
	{ return true; }
      if (element->canonical) {
	if (set->canonical) {
	  auto geq_than
	    { [] (Variables::Variable *element, int comparison) {
	      Variables::Integer *as_int {(Variables::Integer *) element};
	      Variables::ConstInt *canon {(Variables::ConstInt *) element->canonical};
	      return as_int->get_value (canon) > comparison; }};
	  
	  if (set->canonical->name == "NAT" || set->canonical->name == "NATURAL") 
	    { geq_than (element, 0); }
	  else if (set->canonical->name == "NAT1" || set->canonical->name == "NATURAL1")
	    { geq_than (element, 1); }
	  return set->definitely_includes (element);
	}
	set->add_element (element, true);
      }
      else {
	auto update_non_canon_el
	  { [] (Variables::Variable *el, int comparison) {
	    Variables::Integer *as_int {(Variables::Integer *) el};
	    as_int->update_bounds (comparison, true);
	  }};
	if (set->canonical) {
	  if (set->canonical->name == "NAT" || set->canonical->name == "NATURAL")
	    { update_non_canon_el (element, 0); }
	  else if (set->canonical->name == "NAT1" || set->canonical->name == "NATURAL1")
	    { update_non_canon_el (element, 1); }
	  return true;
	}
	else if (element->typref == constraints.get_prim_type ("INTEGER") && set->enumerated) {
	  Variables::Integer *as_int {(Variables::Integer *) element};
	  as_int->give_home (set->enumerated);
	  return true;
	}
	else
	  { set->add_element (element, false); }
      }
    }
    else {
      if (set->name == "INT")
	{ return false; }
      if (element->canonical) {
	if (set->canonical) {
	  auto const_less_than
	    { [] (Variables::Variable *el, int comp) {
	      return ((Variables::ConstInt *) el->canonical)->value < comp;
	    }};
	  if (set->canonical->name == "NAT" || set->canonical->name == "NATURAL")
	    { return const_less_than (element, 0); }
	  else if (set->canonical->name == "NAT1" || set->canonical->name == "NATURAL1")
	    { return const_less_than (element, 1); }
	  return set->definitely_discludes (element);
	}
	set->block_element (element, true);
      }
      else
	{ set->block_element (element, false); }
    }
    
    output.insert (*this);
    return true;
  }

  bool Bridi::consistent_subset (std::set<Bridi> &output, Constraints &constraints) const {
    Variables::Set *sub {(Variables::Set *) arguments[0]}, *super {(Variables::Set *) arguments[1]};
    
    if (!negation) {
      if (super->name == "INT")
	{ return true; }
      if (super->name == "NAT") {} // !el . el : set (el >= 0)
      else if (super->canonical) {
	if (sub->canonical) {
	  for (Variables::Variable *el : sub->canonical_elements) {
	    if (!super->canonical_elements.contains (el->canonical))
	      { return false; }
	  }
	  return true;
	}
	else {
	  if (super->enumerated) {
	    sub->enumerated = super->enumerated;
	    if (super->enumerated == super)
	      return true;
	  }
	}
      }
      else if (sub->canonical) {
	for (Variables::Variable *el : sub->canonical_elements) 
	  { super->add_element (el, true); }
	return true;
      }
      else {
	for (Variables::Variable *el : sub->canonical_elements)
	  { super->add_element (el, true); }
	for (Variables::Variable *el : sub->elements)
	  { super->add_element (el, false); }
      }
    }
    else { // /<:
      if (super->name == "NAT") {}
      else if (super->canonical) {
	if (sub->canonical) {
	  for (Variables::Variable *el : sub->canonical_elements) {
	    if (!super->canonical_elements.contains (el->canonical))
	      { return true; }
	  }
	  return false;
	}
      }
      else if (sub->canonical) {
	for (Variables::Variable *el : sub->canonical_elements)
	  { super->block_element (el, true); }
	return true;
      }
      else {
	for (Variables::Variable *el : sub->canonical_elements)
	  { super->block_element (el, true); }
	for (Variables::Variable *el : sub->elements)
	  { super->block_element (el, false); }
      }
    }	
    
    output.insert (*this);
    return true;
  }
  
  bool Bridi::forward_check (std::set<Bridi> &output, Constraints &constraints) const {
    if (functor == "=")
      { consistent_equality (output, constraints); }
    else if (functor == ":") 
      { consistent_elementhood (output, constraints); }
    else if (functor == "<:")
      { consistent_subset (output, constraints); }
    else
      { output.insert (*this); }
    return true;
  }
  
  std::ostream &operator << (std::ostream &out, const Bridi &bridi) {
    bool pipes {bridi.functor.find (' ') != bridi.functor.npos};

    out << (bridi.negation ? "¬" : "") << (pipes ? "|" : "")
	<< bridi.functor << (pipes ? "|" : "") << '(';
    auto iter {bridi.arguments.cbegin ()};
    for ( ; iter != std::prev (bridi.arguments.cend ()); ++iter)
      { out << (*iter)->name << ','; }
    out << (*iter)->name << ')';

    // out << ' ' << bridi.get_groundness ();
    return out;
  }
  
  Variables::Variable *ConstraintGraph::find_var (const std::string &name) const {
    Variables::Variable var {name};
    auto iter {context_vars.find (&var)};
    if (iter != context_vars.cend ())
      { return *iter; }
    return nullptr;
  }

  void ConstraintGraph::add_constraint (const std::string &functor, std::vector<Variables::Variable *> arguments, bool negation) {    
    if (constraints.contains (purpose))
      { constraints[purpose].emplace (Bridi {arguments, functor, negation}); }
    else
      { constraints[purpose] = {Bridi {arguments, functor, negation}}; }
  }

  void ConstraintGraph::merge_graph (const ConstraintGraph &other) {
    for (auto &[status, set] : other.constraints) {
      set_purpose (status);
      for (const Bridi &bridi : set) 
	{ add_constraint (bridi.functor, bridi.arguments, bridi.negation); }
    }
  }
  
  void ConstraintGraph::relinquish_ownership () {
    context_vars.clear ();
  }

  void ConstraintGraph::set_purpose (int status) {
    purpose = status;
  }
  
  void ConstraintGraph::print (std::ostream &out) const {
    std::map<int, std::string> purposes {{GOAL, "Goal"}, {LOC_AUX, "Local Hyp."}, {AUX, "Hyp."}, {CTX, "Context"}};

    for (auto &[status, set] : constraints) {
      if (!set.empty ()) {
	out << '\n' << purposes[status] << ":\n";
	for (const Bridi &bridi : set)
	  { out << "  " << bridi << '\n'; }
      }
    }
  }

  int Constraints::get_body (int typref) const {
    const int conc {get_concept (typref)};
    switch (conc) {
    case Variables::SETS:
      return type_infos->get_body (typref, type_infos->sets);
    case Variables::RELS:
      return type_infos->get_body (typref, type_infos->relations);
    default:
      return -1;
    }
  }

  std::array<int, 2> Constraints::get_body (int typref, bool mappings) const {
    return type_infos->get_body (typref, type_infos->mappings);
  }
    
  int Constraints::get_concept (int typref) const {
    return type_infos->get_concept (typref);
  }

  int Constraints::get_home (int typref) const {
    return type_infos->get_home (typref);
  }
  
  void Constraints::recuperate_var (Variables::Variable *var) {
    auto recuperate
      { [this, var] (std::map<int, std::set<Variables::Variable *, Variables::VarPtrComp>> &map) {
	variables->add_instance_of_typref (map, var);
      }};

    switch (get_concept (var->typref)) {
    case Variables::PRIM:
      recuperate (variables->prim_vars);
      break;
    case Variables::SETS:
      recuperate (variables->set_vars);
      break;
    case Variables::MAPS:
      recuperate (variables->mapping_vars);
      break;
    case Variables::RELS:
      recuperate (variables->rel_vars);
      break;
    default:
      std::cerr << "Wrong concept at merge, " << var->name << ' ' << var->super_type << ".\n";
    }
  }
  void Constraints::merge_graph () {
    for (Variables::Variable *var : constraint_graph.context_vars) 
      { recuperate_var (var); }
    constraint_graph.relinquish_ownership ();
  }
  
  void Constraints::merge_graph (ConstraintGraph &tmp_cg) {
    for (Variables::Variable *var : tmp_cg.context_vars) 
      { recuperate_var (var); }
    constraint_graph.merge_graph (tmp_cg);
    tmp_cg.relinquish_ownership ();
  }

  void Constraints::recognize_set (pugi::xml_node set, int typref_self, int typref_inside) {
    pugi::xml_node id {set.first_child ()};
    if (!set.child ("Enumerated_Values")) {
      Variables::Variable *var {variables->new_variable (Variables::Set {id.attribute ("value").value (),
									 typref_self, typref_inside, 'S'},
	                        false, Variables::SETS)};
      Variables::Set *set {(Variables::Set *) var};
      set->card_bounds[0] = 1;
    }
    else {
      Variables::Variable *var {variables->new_variable (Variables::Set {id.attribute ("value").value (),
									 typref_self, typref_inside, true, 'S'},
	                        true, Variables::SETS)};
      ((Variables::Set *) var)->enumerated = var;
      recognize_enum (id.next_sibling (), (Variables::Set *) var);
    }
  }

  void Constraints::show_enum (std::ostream &out) {
    for (auto &[type, set] : constraint_graph.enum_sets) {
      out << type->name << " = {";
      auto iter {set.cbegin ()};
      for ( ; iter != std::prev (set.cend ()); ++iter)
	{ out << (*iter)->name << ','; }
      out << (*iter)->name << "}\n";
    }
  }

  void Constraints::recognize_enum (pugi::xml_node enumeration, Variables::Set *var) {
    int typref {var->dom_typref};
    int size {};
    std::set<Variables::Variable *, Variables::VarPtrComp> elements;
    for (pugi::xml_node id : enumeration.children ()) {
      ++size;
      elements.insert (variables->new_variable (Variables::EnumInt {id.attribute ("value").value (), typref, var}, true, Variables::PRIM));
    }
    constraint_graph.enum_sets[var] = elements;
    var->card_bounds[0] = var->card_bounds[1] = size;
  }

  bool Constraints::handle_exp_comparison (pugi::xml_node exp_comparison, int purpose, bool negation) {
    auto known_op
      { [] (const std::string &op) {
	for (const std::string &comp : {":", "<:", "="}) {
	  if (op < comp)
	    { return false; }
	  if (op == comp)
	    { return true; }
	}
	return false;
      }};

    std::string op {exp_comparison.attribute ("op").value ()};
    if (!known_op (op))
      { std::cerr << "Unknown Exp_Comparison op=\"" << op << "\"\n"; return false; }

    ConstraintGraph tmp_constraint_graph;
    constraint_graph.set_purpose (purpose);
    tmp_constraint_graph.set_purpose (purpose);

    Variables::Variable *arg1 {as_variable (exp_comparison.first_child (), tmp_constraint_graph)};
    if (!arg1)
      { return false; }
    Variables::Variable *arg2 {as_variable (exp_comparison.first_child ().next_sibling (), tmp_constraint_graph)};
    if (!arg2)
      { return false; }

    merge_graph (tmp_constraint_graph);
    if (!exceptional_constraint (op, {arg1, arg2}, negation, constraint_graph))
      { constraint_graph.add_constraint (op, {arg1, arg2}, negation); }

    merge_graph ();
    
    return true;
  }

  bool Constraints::exceptional_constraint (const std::string &functor, std::vector<Variables::Variable *> args, bool negation, ConstraintGraph &cg) {
    if (!negation && functor == "<:" && args[1]->name == "NAT") {
      Variables::Set *as_set {(Variables::Set *) args[0]};
      std::stringstream max_name;
      max_name << "imax(" << as_set->name << ')';
      args[0] = new_var_if (max_name.str (), Variables::PRIM, as_set->dom_typref, cg);
      cg.add_constraint (":", {args[0], args[1]}, false);
      
      return true;
    }
    return false;
  }
    
  int Constraints::get_prim_type (const std::string &type) const {
    for (auto &[ref, name] : prim_types) {
      if (type == name)
	{ return ref; }
    }
    return -1;
  }
  
  Variables::Variable *Constraints::find_var (const std::string &name, int super_type, int typref, const ConstraintGraph &tmp) const {
    Variables::Variable *var {variables->find_var (name, get_concept (typref), typref)};
    if (var)
      { return var; }

    var = constraint_graph.find_var (name);
    if (var)
      { return var; }

    var = tmp.find_var (name);
    return var;
  }

  Variables::Variable *Constraints::new_var_if (const std::string &name, int super_type, int typref, ConstraintGraph &tmp, float ground) const {
    super_type = get_concept (typref);
    Variables::Variable *var {find_var (name, get_concept (typref), typref, tmp)};
    if (var)
      { return var; }

    var = variables->make_constant (name, typref, type_infos->get_body (typref, type_infos->sets));
    if (var)
      { return var; }

    switch (super_type) {
    case Variables::PRIM: {
      switch (prim_types.at (typref)[0]) {
      case 'I':
	var = new Variables::Integer {name, typref};
	break;
      case 'B':
	var = new Variables::Boolean {name, typref};
	break;
      default:
	var = nullptr;
      }}
      break;
    case Variables::SETS: {
      int int_typ {type_infos->get_body (typref, type_infos->sets)};
      if (int_typ < 0)
	{ return nullptr; }
      if (name.find ("..") != name.npos)
	{ var = new Variables::Interval {name, typref, int_typ, nullptr, nullptr}; }
      else
	{ var = new Variables::Set {name, typref, int_typ, 'S'}; }
    }
      break;
    case Variables::MAPS: {
      std::array<int, 2> domains {type_infos->get_body (typref, type_infos->mappings)};
      if (domains[0] < 0 || domains[1] < 0)
	{ return nullptr; }
      var = new Variables::Relation {name, typref, domains[0], domains[1]};
    }
      break;
    case Variables::RELS: {
      int int_typ {type_infos->get_body (typref, type_infos->relations)};
      if (int_typ < 0)
	{ return nullptr; }
      auto [from, to] {type_infos->get_body (int_typ, type_infos->mappings)};
      var = new Variables::SetOfRelations {name, typref, int_typ, from, to};
    }
      break;
    }

    if (var) {
      if (ground) {
	var->update_ground (ground);
	if (ground >= 1.0)
	  { var->canonical = var; }
      }
      tmp.context_vars.insert (var);
    }
    
    return var;
  }

  Variables::Variable *Constraints::surround_var (Variables::Variable *sumti, const std::string &selbri, int super_type, int typref, ConstraintGraph &tmp_cg, float ground) {
    std::stringstream new_name;
    new_name << selbri << '(' << sumti->name << ')';
    return new_var_if (new_name.str (), super_type, typref, tmp_cg, ground);
  }
   
  Variables::Variable *Constraints::unary_exp (pugi::xml_node unary_exp, ConstraintGraph &tmp_cg) {
    Variables::Variable *inside {as_variable (unary_exp.first_child (), tmp_cg)};
    if (!inside)
      { return nullptr; }

    int typref {unary_exp.attribute ("typref").as_int ()};
    std::string op {unary_exp.attribute ("op").value ()};

    Variables::Variable *current {surround_var (inside, op, get_concept (typref), typref, tmp_cg, inside->ground)};
    if (!current)
      { return nullptr; }

    if (op == "imin" || op == "imax") 
      { tmp_cg.add_constraint (":", {current, inside}, false); }
    else if (op == "dom" || op == "ran")
      {}
    else {
      std::cerr << "Skipped " << current->name << '\n';
      return nullptr;
    }
    return current;
  }

  Variables::Variable *Constraints::maplet_var (pugi::xml_node maplet, ConstraintGraph &tmp_cg) {
    Variables::Variable *arg1 {as_variable (maplet.first_child (), tmp_cg)};
    if (!arg1)
      { return nullptr; }
    Variables::Variable *arg2 {as_variable (maplet.first_child ().next_sibling (), tmp_cg)};
    if (!arg2)
      { return nullptr; }
    return maplet_var (arg1, arg2, maplet.attribute ("typref").as_int (), tmp_cg);
  }
  
  Variables::Variable *Constraints::maplet_var (Variables::Variable *arg1, Variables::Variable *arg2, int typref, ConstraintGraph &tmp_cg) {
    std::stringstream name;
    name << '<' << arg1->name << ',' << arg2->name << '>';
    Variables::Pair *maplet {new Variables::Pair {name.str (), typref, arg1, arg2}};
    Variables::Variable *maybe {find_var (name.str (), Variables::MAPS, typref, tmp_cg)};
    if (maybe)
      { delete maplet; return maybe; }

    auto get_singleton
      { [this, &tmp_cg] (Variables::Variable *arg, int over_type) {
	std::stringstream dom_name;
	dom_name << '{' << (arg->canonical ? arg->canonical->name : arg->name) << '}';
	Variables::Variable *singleton {new_var_if (dom_name.str (), get_concept (over_type), over_type, tmp_cg)};
	if (arg->canonical)
	  { singleton->canonical = singleton; }
	Variables::Set *as_set {(Variables::Set *) singleton};
	as_set->add_element (arg, true);
	return singleton;
      }};
    
    Variables::Variable *dom {get_singleton (arg1, type_infos->get_home (arg1->typref))};
    Variables::Variable *ran {get_singleton (arg2, type_infos->get_home (arg2->typref))};

    tmp_cg.add_constraint ("=", {surround_var (maplet, "dom", get_concept (dom->typref), dom->typref, tmp_cg), dom}, false);
    tmp_cg.add_constraint ("=", {surround_var (maplet, "ran", get_concept (ran->typref), ran->typref, tmp_cg), ran}, false);
    if (dom->canonical && ran->canonical)
      { maplet->canonical = maplet; }

    maplet->ground = (dom->ground + ran->ground) / 2;
    tmp_cg.context_vars.insert (maplet);
    return maplet;
  }

  Variables::Variable *Constraints::boolean_exp (pugi::xml_node exp, ConstraintGraph &tmp_cg) {
    std::stringstream name;
    switch (exp.first_child ().name ()[0]) {
    case 'B': {
      Variables::Variable *arg1 {as_variable (exp.first_child ().first_child (), tmp_cg)};
      if (!arg1)
	{ return nullptr; }
      Variables::Variable *arg2 {as_variable (exp.first_child ().first_child ().next_sibling (), tmp_cg)};
      if (!arg2)
	{ return nullptr; }
      name << exp.first_child ().attribute ("op").value () << '(' << arg1->name << ',' << arg2->name << ')';
    }
      break;
      
    case 'U': {
      Variables::Variable *arg {as_variable (exp.first_child ().first_child (), tmp_cg)};
      if (!arg)
	{ return nullptr; }
      name << "¬" << arg->name;
    }
      break;
      
    case 'N': {
      name << '(';
      std::string op {exp.first_child ().attribute ("op").value ()[0] == '&' ? " ^ " : " v "};
      for (pugi::xml_node child : exp.first_child ().children ()) {
	Variables::Variable *var {as_variable (child, tmp_cg)};
	if (!var)
	  { return nullptr; }
	name << var->name << (child.next_sibling () ? op : "");
      }
      name << ')';
    }
      break;
      
    case 'E': {
      Variables::Variable *arg1 {as_variable (exp.first_child ().first_child (), tmp_cg)};
      if (!arg1)
	{ return nullptr; }
      Variables::Variable *arg2 {as_variable (exp.first_child ().first_child ().next_sibling (), tmp_cg)};
      if (!arg2)
	{ return nullptr; }

      name << exp.first_child ().attribute ("op").value () << '(' << arg1->name << ',' << arg2->name << ')';
    }
      break;
      
    default:
      return nullptr;
    }

    return new_var_if (name.str (), Variables::PRIM, exp.attribute ("typref").as_int (), tmp_cg);
  }

  void Constraints::equicardinality (Variables::Variable *first, Variables::Variable *second, ConstraintGraph &tmp_cg) {
    Variables::Variable *card_o_first {surround_var (first, "card", Variables::PRIM, get_prim_type ("INTEGER"), tmp_cg)};
    Variables::Variable *card_o_second {surround_var (second, "card", Variables::PRIM, get_prim_type ("INTEGER"), tmp_cg)};
    tmp_cg.add_constraint ("=", {card_o_first, card_o_second}, false);
  }
  
  Variables::Variable *Constraints::binary_exp (pugi::xml_node binary_exp, ConstraintGraph &tmp_cg) {
    Variables::Variable *arg1 {as_variable (binary_exp.first_child (), tmp_cg)};
    if (!arg1)
      { return nullptr; }
    Variables::Variable *arg2 {as_variable (binary_exp.first_child ().next_sibling (), tmp_cg)};
    if (!arg2)
      { return nullptr; }

    int typref {binary_exp.attribute ("typref").as_int ()};
    std::string op {binary_exp.attribute ("op").value ()};

    if (op == "..") 
      { return nullptr; } // plain_interval (typref, arg1, arg2, tmp_cg); }
    if (op == "|->") 
      { return maplet_var (arg1, arg2, typref, tmp_cg); }

    int hash_rels {14};
    std::string rels[hash_rels] {"*s", "+->", "+->>", "-->", "-->>", "<+", "<->", "<<|", "<|", ">+>", ">->", ">->>", "|>", "|>>"};
    
    auto is_included
      { [&op] (std::string *comps, int length) {
	if (op < comps[0] || op > comps[length - 1])
	  { return -1; }
	int start {}, end {length};
	while (start <= end) {
	  int mid {start + (end - start) / 2};
	  if (op == comps[mid])
	    { return mid; }
	  if (op < comps[mid])
	    { end = --mid; }
	  else
	    { start = ++mid; }
	}
	return -1;
      }};

    int rel_idx {is_included (rels, hash_rels)};
    if (rel_idx >= 0) {
      std::stringstream name;
      name << op << '(' << arg1->name << ',' << arg2->name << ')';
      int super_type {get_concept (binary_exp.attribute ("typref").as_int ())};
      Variables::Variable *main_rel {new_var_if (name.str (), super_type, typref, tmp_cg)};
      Variables::Set *as_set {(Variables::Set *) main_rel};

      if (super_type == Variables::RELS) {
	Variables::SetOfRelations *as_sor {(Variables::SetOfRelations *) main_rel};
	as_sor->from = arg1; as_sor->to = arg2;
      }

      Variables::Variable *dom {surround_var (main_rel, "dom", get_concept (arg1->typref), arg1->typref, tmp_cg)};
      Variables::Variable *ran {surround_var (main_rel, "ran", get_concept (arg2->typref), arg2->typref, tmp_cg)};
      tmp_cg.add_constraint ("=", {arg1, dom}, false);
      tmp_cg.add_constraint ("=", {arg2, ran}, false);

      return main_rel;
    }
    // std::vector<std::string> numeric {

    return nullptr;
  }
  
  Variables::Variable *Constraints::nary_exp (pugi::xml_node nary_exp, ConstraintGraph &tmp_cg) {
    if (nary_exp.attribute ("op").value ()[0] != '{')
      { return nullptr; }
    
    int card {};
    for (pugi::xml_node child : nary_exp.children ()) { ++card; }
    std::vector<Variables::Variable *> elements (card);

    int i {};
    float ground {};
    Variables::Variable *enumeration {nullptr};
    
    for (pugi::xml_node child : nary_exp.children ()) {
      Variables::Variable *var {as_variable (child, tmp_cg)};
      if (!var)
	{ return nullptr; }
      
      if (var->typref == get_prim_type ("INTEGER")) {
	Variables::Primitive *as_prim {(Variables::Primitive *) var};
	if (as_prim->type == 'E') {
	  if (as_prim->canonical) {
	    Variables::EnumInt *as_enum_int {(Variables::EnumInt *) as_prim->canonical};
	    enumeration = as_enum_int->home;
	  }
	  else {
	    Variables::Integer *as_int {(Variables::Integer *) as_prim};
	    enumeration = as_int->enumerated;
	  }
	}
      }
	    
      ground += var->ground;
      elements[i++] = var;
    }

    std::stringstream name;
    name << '{';
    if (!elements.empty ()) {
      auto iter {elements.cbegin ()};
      for ( ; iter != std::prev (elements.cend ()); ++iter)
	{ name << (*iter)->name << ','; }
      name << (*iter)->name;
    }
    name << '}';

    int typref {nary_exp.attribute ("typref").as_int ()};

    int super_type {get_concept (typref)};
    Variables::Variable *to_return {nullptr};
    switch (super_type) {
    case Variables::SETS:
    case Variables::RELS: {
      Variables::Set *set {(Variables::Set *) new_var_if (name.str (), super_type, typref, tmp_cg)};
      if (!set)
	{ return nullptr; }
      if (set->type == 'R') {
	Variables::SetOfRelations *as_sor {(Variables::SetOfRelations *) set};
	if (!as_sor->from)
	  { as_sor->from = surround_var ((Variables::Variable *) as_sor, "dom", get_concept (as_sor->dom_typref), as_sor->dom_typref, tmp_cg); }
        if (!as_sor->to)
	  { as_sor->to = surround_var ((Variables::Variable *) as_sor, "ran", get_concept (get_home (as_sor->to_typref)), get_home (as_sor->to_typref), tmp_cg); }
	Variables::Set *as_set {(Variables::Set *) as_sor->to};
      }
      
      bool own_canonical {true}, from_canonical {true}, to_canonical {true};
      Variables::Set *from_as_set, *to_as_set;
      if (set->type == 'R') {
	Variables::SetOfRelations *as_sor {(Variables::SetOfRelations *) set};
	from_as_set = (Variables::Set *) as_sor->from;
	to_as_set = (Variables::Set *) as_sor->to;
      }
      
      for (Variables::Variable *var : elements) {
	if (set->type == 'R') {
	  auto add_var_to_set
	    { [this, &own_canonical] (Variables::Variable *var, Variables::Set *set, bool &boolean) {
	      if (get_concept (var->typref) == Variables::PRIM) {
		Variables::Primitive *as_prim {(Variables::Primitive *) var};
		if (var->canonical) {
		  as_prim = (Variables::Primitive *) var->canonical;
		  if (as_prim->type == 'E') 
		    { set->enumerated = ((Variables::EnumInt *) as_prim)->home; }
		}
		else {
		  if (as_prim->type != 'B') 
		    { set->enumerated = ((Variables::Integer *) as_prim)->enumerated; }
		}
	      }
		
	      if (var->canonical) 
		{ set->add_element (var->canonical, true); }
	      else {
		set->add_element (var, false);
		boolean = false;
		own_canonical = false;
	      }
	    }};

	  Variables::Pair *as_pair {(Variables::Pair *) var};

	  add_var_to_set (as_pair->from, from_as_set, from_canonical);
	  add_var_to_set (as_pair->to, to_as_set, to_canonical);
	}
	if (var->canonical)
	  { tmp_cg.add_constraint (":", {var->canonical, set}, false); }
	else
	  { tmp_cg.add_constraint (":", {var, set}, false); }
      }
      set->card_bounds[1] = set->card_bounds[0] = card;
      set->ground = ground / card;

      if (own_canonical) 
	{ set->canonical = set; }
      set->enumerated = enumeration;
      to_return = (Variables::Variable *) set;
    }
      break;
    }
    
    return to_return;
  }

  Variables::Variable *Constraints::plain_interval (int typref, Variables::Variable *begin, Variables::Variable *end, ConstraintGraph &tmp_cg) {
    std::stringstream name;
    name << '[' << begin->name << ',' << end->name << ']';
    Variables::Interval *interval {(Variables::Interval *) new_var_if (name.str (), get_concept (typref), typref,
								       tmp_cg, (begin->ground + end->ground) / 2)};
    if (interval) {
      interval->var_bounds[0] = begin->canonical ? (Variables::Integer *) begin->canonical : (Variables::Integer *) begin;
      interval->var_bounds[1] = end->canonical ? (Variables::Integer *) end->canonical : (Variables::Integer *) end;
      interval->type = 'I';
      return (Variables::Variable *) interval;
    }
    return nullptr;
  }

  Variables::Variable *Constraints::make_ground_set (const std::vector<Variables::Variable *> &elements, int typref, int gov, int super_type, ConstraintGraph &tmp_cg) {
    if (elements.empty ())
      { return variables->make_empty_set (typref, gov); }

    std::set<Variables::Variable *, Variables::VarPtrComp> grounds;
    for (Variables::Variable *derived : elements)
      { grounds.insert (derived->canonical); }

    auto name_with_comma_fail
      { [] (Variables::Variable *v) {
	return v->canonical ? v->canonical->name : ",";
      }};
    
    auto iter {grounds.cbegin ()};
    std::stringstream new_name;
    new_name << '{' << name_with_comma_fail (*iter);
    for (++iter; iter != grounds.cend (); ++iter)
      { new_name << ',' << name_with_comma_fail (*iter); }
    new_name << '}';

    std::string as_str {new_name.str ()};
    if (as_str.find (",,") != as_str.npos)
      { return nullptr; }

    super_type = get_concept (typref);
    Variables::Variable *as_var {new_var_if (new_name.str (), super_type,
					     typref, tmp_cg, 1.0)};
    Variables::Set *as_set {(Variables::Set *) as_var};
    
    as_set->set_card (grounds.size ());
    for (Variables::Variable *gr : grounds)
      { as_set->canonical_elements.insert (gr); }
    as_set->canonical = as_set;
    
    return as_var;
  }

  Variables::Variable *Constraints::as_variable (pugi::xml_node node, ConstraintGraph &tmp_constraint_graph) {
    std::string node_type {node.name ()};
    if (node_type[0] == 'Q')
      { return nullptr; }
    int typref {node.attribute ("typref").as_int ()};
    int super_type {get_concept (typref)};

    auto pass_through
      { [] (const std::string &name) {
	for (const std::string &comp : {"Boolean_Literal", "Id", "Integer_Literal"}) {
	  if (name < comp)
	    { return false; }
	  if (name == comp)
	    { return true; }
	}
	return false;
      }};

    if (pass_through (node_type)) {
      if (node_type[1] == 'd')
	{ return new_var_if (node.attribute ("value").value (), super_type, typref, tmp_constraint_graph, 0.0); }
      else if (node_type[0] == 'I')
	{ return variables->make_int_lit (node.attribute ("value").as_llong (), typref); }

      // TRUE or FALSE
      return new_var_if (node.attribute ("value").value (), super_type, typref, tmp_constraint_graph, 1.0);
    }
    else if (node_type == "EmptySet")
      { return variables->make_empty_set (typref, type_infos->get_body (typref, type_infos->sets)); }
    else if (node_type == "Unary_Exp")
      { return unary_exp (node, tmp_constraint_graph); }
    else if (node_type == "Binary_Exp")
      { return binary_exp (node, tmp_constraint_graph); }
    else if (node_type == "Nary_Exp") 
      { return nary_exp (node, tmp_constraint_graph); }
    else if (node_type == "Boolean_Exp")
      { return boolean_exp (node, tmp_constraint_graph); }
      
    node.print (std::cout);
    return nullptr;
  }

  void Constraints::get_variables_from_node (pugi::xml_node node) {
    std::string name {node.name ()};
    if ("EmptySet" == name || name.find ("Literal") != name.npos)
      { return; }
    else if ("Id" == name) {
      int typref {node.attribute ("typref").as_int ()};
      new_var_if (node.attribute ("value").value (),
		  get_concept (typref), typref,
		  constraint_graph, 0.0);
    }
    else if (name.find ("Unary") != name.npos)
      { get_variables_from_node (node.first_child ()); }
    else if (name == "Exp_Comparison" || name.find ("ary") != name.npos) {
      for (pugi::xml_node child : node.children ())
	{ get_variables_from_node (child); }
    }
    else if (name[0] == 'Q')
      {}
    else
      { node.print (std::cerr); }
  }
  
  void Constraints::make_variables (pugi::xml_node predicate) {
    switch (predicate.name ()[0]) {
    case 'S': {
      int typref {predicate.attribute ("typref").as_int ()};
      recognize_set (predicate, typref, type_infos->get_body (typref, type_infos->sets));
      break;
    }
    case 'E':
      get_variables_from_node (predicate);
      break;
    }
  }

  bool ConstraintGraph::forward_check (Constraints &host_constraints) {
    bool response {true};
    for (auto &[status, set_of_constraints] : constraints) {
      std::set<Bridi> tmp;
      for (const Bridi &bridi : set_of_constraints) {
	if (!bridi.forward_check (tmp, host_constraints))
	  { response = false; }
      }
      constraints[status] = tmp;
    }
    return response;
  }

  bool Constraints::forward_check (int times) {
    for (int i {}; i < times; ++i) {
      if (!constraint_graph.forward_check (*this))
	{ return false; }
    }
    return true;
  }
}
