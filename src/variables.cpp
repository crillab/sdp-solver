#include "types.hpp"
#include "variables.hpp"

namespace Variables {
  Variable::Variable (std::string name, int typref, int super_type)
    : ground {}, name {name}, typref {typref}, super_type {super_type} {}

  void Variable::bind_names (Variable *other) {
    for (Variable *var : {this, other}) {
      for (Variable *moniker : var->alias) {
	this->alias.insert (moniker);
	other->alias.insert (moniker);
      }
    }
    this->alias.insert (other);
    other->alias.insert (this);
  }
   
  void Variable::update_ground () {
    ground = 1;
  }

  void Variable::update_ground (float new_ground) {
    ground = new_ground;
  }

  Variable *Variable::update_ground (Variable *gr_form) {
    if (canonical)
      { return canonical; }

    canonical = gr_form;
    ground = 1.0;

    for (Variable *other : alias) {
      if (other->update_ground (gr_form) != gr_form) {
	std::cerr << "Different canonical forms for ";
	print (std::cerr);
	std::cerr << " and ";
	other->print (std::cerr);
      }
    }

    return gr_form;
  }

  bool Variable::compare (const Variable *other) const {
    if (typref != other->typref || ground < 1.0 || other->ground < 1.0)
      { return false; }

    switch (super_type) {
    case PRIM:
      return get_value () == other->get_value ();
    case SETS:
      return ((Set *) this)->compare ((Set *) other);
    case RELS:
      return ((SetOfRelations *)this)->compare ((SetOfRelations *) other);
    }
    return false;
  }
  
  void Variable::print (std::ostream &out) const {
    out << "(Name . " << name << ") (Typref . " << typref << ") *unspecified-variable*";
  }

  Primitive::Primitive (std::string name, int typref, char type)
    : Variable {name, typref, PRIM}, type {type} {}

  void Primitive::print (std::ostream &out) const {
    out << "(Name . " << name << ") (Type . " << type << ") *unspecified-primitive-variable*";
  }
  
  Integer::Integer (std::string name, int typref)
    : Primitive {name, typref, 'Z'} {}
  
  Integer::Integer (std::string name, int typref, long long glb, long long lub)
    : Primitive {name, typref, 'Z'}, bounds {glb, lub} {}

  bool Integer::compare (const Integer *other) const {
    Integer *canon {(Integer *) canonical}, *other_canon {(Integer *) other->canonical};
    return canon->bounds[0] == other_canon->bounds[0];
  }
    
  bool Integer::empty () {
    return bounds[0] > bounds[1];
  }

  bool Integer::update_values (Variables *variables) {
    if (ground >= 1.0)
      { return true; }
    
    for (Variable *other : alias) {
      Integer *as_int {(Integer *) other};
      
      if (as_int->enumerated) {
	update_ground (as_int->canonical);
	for (Variable *again_other : alias)
	  { update_ground (canonical); }
	alias.clear ();
	return true;
      }
      
      update_bounds (as_int->bounds[0], as_int->bounds[1]);
      
      if (bounds[0] > bounds[1])
	{ return false; }
      if (bounds[0] == bounds[1]) {
	update_ground (variables->make_int_lit<long long> (bounds[0], typref));
	for (Variable *again_other : alias)
	  { update_ground (canonical); }
	alias.clear ();
	return true;
      }
    }

    return true;
  }

  void Integer::give_home (Variable *enumeration) {
    enumerated = enumeration;
    type = 'E';
    for (Variable *other : alias) {
      Integer *as_int {(Integer *) other};
      as_int->enumerated = enumeration;
    }
  }
  
  Variable *Integer::update_ground (Variable *gr_form) {
    if (canonical)
      { return canonical; }

    PrimConst *prim_const {(PrimConst *) gr_form};
    if (type == 'E') {
      EnumInt *prim_enum {(EnumInt *) gr_form};
      enumerated = prim_enum->home;
    }
    
    canonical = gr_form;
    ground = 1.0;

    for (Variable *other : alias) {
      if (other->update_ground (gr_form) != gr_form) {
	std::cerr << "Different canonical forms for ";
	print (std::cerr);
	std::cerr << " and ";
	other->print (std::cerr);
      }
    }

    return gr_form;
  }

  void Integer::update_domain (const std::string &str) {
    update_bounds (std::stoll (str));
  }

  void Integer::update_bounds (long long bound, bool lower) {
    long long glb, lub;
    if (lower) {
      glb = bound;
      lub = bounds[1];
    }
    else {
      glb = bounds[0];
      lub = bound;
    }
    update_bounds (glb, lub);
  }
  
  void Integer::update_bounds (long long glb, long long lub) {
    bounds[0] = bounds[0] >= glb ? bounds[0] : glb;
    bounds[1] = bounds[1] >= lub ? bounds[1] : lub;
  }
  
  void Integer::update_bounds (long long bound) {
    update_bounds (bound, bound);
  }

  long long Integer::get_value (ConstInt *canon) const {
    return canon->value;
  }

  std::string Integer::get_value (EnumInt *canon) const {
    return canon->name;
  }
  
  long long Integer::get_value (long long) const {
    ConstInt *canon {(ConstInt *) canonical};
    return canon->value;
  }

  std::string Integer::get_value (const std::string &) const {
    return canonical ? canonical->name : "";
  }
  
  void Integer::print (std::ostream &out) const {
    out << "(Name . " << name << ") (Type . ";
    if (enumerated)
      { out << enumerated->name; }
    else
      { out << type; }
    out << ')';
    if (LLONG_MIN != bounds[0])
      { out << " (GLB . " << bounds[0] << ')'; }
    if (LLONG_MAX != bounds[1])
      { out << " (LUB . " << bounds[1] << ')'; }
  }
  
  ConstInt::ConstInt (long long value, int typref)
    : PrimConst {std::to_string (value), typref, 'Z'}, value {value} {}
  ConstInt::ConstInt (const std::string &name, int typref)
    : PrimConst {name, typref, 'Z'}, value {name[1] == 'A' ? LLONG_MAX : LLONG_MIN} {}
  void ConstInt::print (std::ostream &out) const {
    out << "(Name . " << name << ") *const*";
  }
  
  EnumInt::EnumInt (std::string name, int typref, Variable *home)
    : PrimConst {name, typref, 'E'}, home {home} {}
  void EnumInt::print (std::ostream &out) const {
    out << "(Name . " << name << ") (Type . " << home->name << ')';
  }

  Boolean::Boolean (std::string name, int typref)
    : Primitive {name, typref, 'B'} {}

  bool Boolean::empty () {
    return !domain[0] && !domain[1];
  }
  
  void Boolean::determine_val (bool phase) {
    domain[phase ? 0 : 1] = false;
  }
  
  void Boolean::update_domain (const std::string &str) {
    determine_val (str[0] == 'T');
  }
  
  void Boolean::print (std::ostream &out) const {
    out << "(Name . " << name << ") (Type . " << type << ") (Domain . {";
    if (domain[0] && domain[1])
      { out << "⊤,⊥"; }
    else if (domain[0])
      { out << "⊤"; }
    else if (domain[1])
      { out << "⊥"; }
    out << "})";
  }

  ConstBool::ConstBool (bool val, int typref)
    : PrimConst {val ? "TRUE" : "FALSE", typref, 'B'}, phase {val} {}
  ConstBool::ConstBool (const std::string &name, int typref)
    : PrimConst {name, typref, 'B'}, phase {name[0] == 'T'} {}
  void ConstBool::print (std::ostream &out) const {
    out << "(Name . " << name << ") " << (phase ? "⊤" : "⊥");
  }

  Set::Set (std::string name, int own_typref, int dom_typref, char type)
    : Variable {name, own_typref, SETS}, dom_typref {dom_typref}, type {type} {}
  Set::Set (std::string name, int own_typref, int dom_typref, bool enumerated, char type)
    : Variable {name, own_typref, SETS}, dom_typref {dom_typref}, type {type} {
    if (enumerated) {
      ground = 1.0;
      this->enumerated == this;
    }
  }
  Set::Set (std::string name, int super_type, int own_typref, int dom_typref, char type)
    : Variable {name, own_typref, super_type}, dom_typref {dom_typref}, type {type} {}
  
  bool Set::definitely_includes (Variable *var) {
    return var->canonical && canonical_elements.contains (var->canonical);
  }

  bool Set::definitely_discludes (Variable *var) {
    return var->canonical && !canonical_elements.contains (var->canonical);
  }
  
  unsigned long long Set::get_card (bool &ungrounded) {
    if (ground < 1.0)
      { ungrounded = true; return 0; }
    ungrounded = false;
    return card_bounds[0];
  }

  void Set::set_card (long long inf, long long sup) {
    card_bounds[0] = card_bounds[0] >= inf ? card_bounds[0] : inf;
    card_bounds[1] = card_bounds[1] <= sup ? card_bounds[1] : sup;
  }
  
  void Set::set_card (long long bound, bool lower) {
    long long inf, sup;
    if (lower) {
      inf = bound;
      sup = card_bounds[1];
    }
    else {
      inf = card_bounds[0];
      sup = bound;
    }
    set_card (inf, sup);
  }

  void Set::set_card (long long cardinality) {
    set_card (cardinality, cardinality);
  }

  void Set::determine_element (Variable *var, bool ground, bool in) {
    if (!ground) {}
    // { elements.insert (var); }
    else {
      if (var->canonical) {
	Variable *canon {var->canonical};
	std::set<Variable *, VarPtrComp> &destination {in ? canonical_elements : canonical_nogoods};
	std::set<Variable *, VarPtrComp> &maybe_remove {in ? elements : nogoods};
	destination.insert (canon);
	std::erase_if (maybe_remove, [canon] (Variable *other) { return other->canonical == canon; });
      }
    }
  }
  
  void Set::add_element (Variable *var, bool ground) {
    determine_element (var, ground, true);
  }

  void Set::block_element (Variable *var, bool ground) {
    determine_element (var, ground, false);
  }
  
  bool Set::compare (const Set *other) const {
    if (!other || !other->canonical)
      { return false; }
    if (type == 'I') {
      Set *canon1 {(Set *) canonical}, *canon2 {(Set *) other->canonical};
      return canon1->var_bounds[0] == canon2->var_bounds[0] && canon1->var_bounds[1] == canon2->var_bounds[1];
    }
    return canonical == other->canonical;
  }

  Variable *Set::update_ground (const Variable *other, Variables *variables) {
    Set *as_set {(Set *) other};
    if (as_set->type == 'I') {
      type = 'I';

      auto update
	{ [] (Integer *lead, Integer *follow) {
	  if (!lead)
	    { return; }
	  follow->canonical = lead->canonical;
	  follow->ground = 1.0;
	  follow->update_bounds (((Integer *) lead->canonical)->bounds[0]);
	}};

      for (int i {}; i < 2; ++i) {
	if (var_bounds[i]) {
	  if (var_bounds[i]->canonical)
	    { continue; }
	  else
	    { update ((Integer *) as_set->var_bounds[i], (Integer *) var_bounds[i]); }
	}
	else {
	  std::stringstream name1;
	  name1 << (i ? "imax(" : "imin(") << name << ')';
	  Variable *limit1 {variables->new_variable (Integer {name1.str (), dom_typref}, false, PRIM)};

	  update ((Integer *) as_set->var_bounds[i], (Integer *) limit1); }
      }
      return this;
    }
	  
    //UPDATE
    for (Variable *var : as_set->canonical_elements) 
      { add_element (var, true); }
    ground = 1.0;
    canonical = as_set->canonical;

    return canonical;
  }
    
  void Set::print (std::ostream &out) const {
    out << "(Name . " << name << ") (Type . ";
    if (enumerated)
      { out << "enum)"; }
    else
      { out << "P("<< dom_typref << "))"; }
    if (card_bounds[0] != 0 || card_bounds[1] != LLONG_MAX) {
      out << " (Cardinality . ";
      if (card_bounds[0] != card_bounds[1])
	{ out << '[' << card_bounds[0] << ',' << card_bounds[1] << ']'; }
      else
	{ out << card_bounds[0]; }
      out << ')';
    }
  }

  void Interval::ground_bounds (int int_typref) {
    if (dom_typref == int_typref) {
      for (int i {}; i < 2; ++i) {
	if (var_bounds[i]) {
	  if (!var_bounds[i]->enumerated && var_bounds[i]->ground >= 1.0) {
	    ConstInt *as_const_int {(ConstInt *) var_bounds[i]->canonical};
	    card_bounds[i] = var_bounds[i]->get_value (as_const_int);
	  }
	}
      }
    }
  }

  unsigned long long Interval::get_card (bool &fail) {
    if (ground < 1.0)
      { fail = true; return 0; }
    fail = false;
    return (unsigned long long) (card_bounds[1] - card_bounds[0]);
  }

  bool Interval::compare (const Interval *other) const {
    return var_bounds[0]->compare (other->var_bounds[0]) && var_bounds[1]->compare (other->var_bounds[1]);
  }

  Relation::Relation (std::string name, int own_typref, int dom_typref, int cod_typref)
    : Set {name, true, own_typref, dom_typref, 'M'}, cod_typref {cod_typref} {}

  void Relation::print (std::ostream &out) const {
    out << "(Name . " << name << ") (Type . " << dom_typref << 'x' << cod_typref << ')';
  }

  void VarGroup::take_ownership (std::set<Variable *, VarPtrComp> vars) {
    for (const Variable *v : vars) {
      Variable *var {const_cast<Variable *> (v)};
      var->canonical = this;
    }
  }

  bool Variables::is_known_constant (Variable *var) {
    for (auto iter {known_constants.begin ()}; iter != known_constants.end (); ++iter) {
      if (var->name < *iter)
	{ break; }
      if (var->name == *iter) {
	known_constants.erase (iter);
	if (var->name[0] == 'M') {
	  ConstInt *as_int {(ConstInt *) var};
	  as_int->value = var->name[1] == 'A' ? LLONG_MAX : LLONG_MIN;
	}
	var->canonical = var;
	return true;
      }
    }
    return false;
  }
  
  void Variables::add_instance_of_typref (std::map<int, std::set<Variable *, VarPtrComp>> &collection, Variable *var) {
    if (collection.contains (var->typref))
      { collection[var->typref].insert (var); }
    else
      { collection[var->typref] = {var}; }
    all_vars.insert (var);
  }

  Variable *Variables::make_constant (const std::string &name, int typref, int gov) {
    for (auto iter {known_constants.begin ()}; iter != known_constants.end (); ++iter) {
      if (name < *iter)
	{ return nullptr; }
      if (name == *iter) {
	if (name[0] == '[') {
	  std::string new_name {name[1] == '0' ? "NAT" : "INT"};
	  Variable *v {find_var (new_name, SETS, typref)};
	  if (!v)
	    { v = make_constant (new_name, typref, gov); }
	  return v;
	}
	
	known_constants.erase (iter);

	switch (name[0]) {
	case 'B':
	  return make_bool_domain (typref, gov);
	case 'M':
	  return make_int_limit (name[1], typref);
	case 'F':
	case 'T':
	  return new_variable (ConstBool {name, typref}, true, PRIM);
	case '{':
	  return make_empty_set (typref, gov);
	default:
	  return make_int_interval (name[0], typref, gov);
	}
      }
    }
    return nullptr;
  }

  Variable *Variables::make_empty_set (int typref, int gov) {
    Set empty_set {"{}", typref, gov, 'S'};
    return new_variable (empty_set, true, SETS);
  }
  
  Variable *Variables::make_bool_domain (int typref, int gov) {
    Set *bool_domain {(Set *) new_variable (Set {"BOOL", typref, gov, 'S'}, true, SETS)};
    bool polarities[] {true, false};
    std::string names[2] {"TRUE", "FALSE"};
    for (int i {}; i < 2; ++i)
      { bool_domain->canonical_elements.insert (new_variable (ConstBool {names[i], gov}, true, PRIM)); }
    
    bool_domain->set_card (2);
    bool_domain->ground = 1.0;

    add_instance_of_typref (set_vars, bool_domain);

    return (Variable *) bool_domain;
  }

  Variable *Variables::make_int_lit (int typref, ConstInt *lit) {
    add_instance_of_typref (prim_vars, lit);
    return (Variable *) lit;
  }
  
  Variable *Variables::make_int_limit (char second_letter, int typref) {
    long long bound {second_letter == 'a' ? LLONG_MAX : LLONG_MIN};
    return make_int_lit<const std::string &> (second_letter == 'a' ? "MAXINT" : "MININT", typref);
  }
   
  Variable *Variables::make_int_interval (char first_letter, int typref, int gov) {
    Variable *begin {first_letter == 'I' ? make_int_limit ('i', gov) : make_int_lit<long long> (0, gov)},
      *end {make_int_limit ('a', gov)};
    Interval *interval {new_interval (Interval {first_letter == 'I' ? "INT" : "NAT",
						typref, gov, (Integer *) begin, (Integer *) end},
	true, (Integer *) begin, (Integer *) end)};
    
    interval->ground = 1.0;
    add_instance_of_typref (set_vars, interval);
    interval->canonical = interval;
    
    return (Variable *) interval;
  }

  bool Variables::set_to_interval (Variable *arg1, Variable *arg2) {
    Set *as_set {(Set *) arg1};
    Interval *as_interval {(Interval *) arg2};

    as_set->type = 'I';

    auto bind
      { [] (Integer *one, Integer *two) {
	for (Variable *other : one->alias)
	  { two->alias.insert (other); }
      }};

    std::stringstream min_name, max_name;
    min_name << "imin(" << as_set->name << ')';
    max_name << "imax(" << as_set->name << ')';
    Integer *min {(Integer *) new_variable (Integer {min_name.str (), as_set->dom_typref}, false, PRIM)},
      *max {(Integer *) new_variable (Integer {max_name.str (), as_set->dom_typref}, false, PRIM)};

    
    int match {}, integerp {}, natp {};
    float groundedness {};
    for (int i {}; i < 2; ++i) {
      Integer *limit {i ? max : min};

      if (as_interval->var_bounds[i]) {
	if (as_interval->var_bounds[i]->name == limit->name) {
	  ++match;
	  groundedness += 1.0;
	  limit->ground = 1.0;
	  limit->canonical = as_interval->var_bounds[i]->canonical;
	  as_set->var_bounds[i] = (Integer *) limit->canonical;
	  as_set->add_element (limit, true);
	  ++match;
	}
	else 
	  { as_set->add_element (limit, false); }
      }
      else {
	std::stringstream interval_name;
	interval_name << (i ? "imax(" : "imin(") << as_interval->name << ')';
	Integer *extremity {(Integer *) new_variable (Integer {interval_name.str (), as_set->dom_typref},
						      false, PRIM)};
	if (limit->canonical) {
	  extremity->canonical = limit->canonical;
	  extremity->ground = 1.0;
	}
	else {
	  bind (extremity, limit);
	  bind (limit, extremity);
	}
	as_set->add_element (limit, false);
      }
      if (i && limit->canonical && limit->canonical->name == "MAXINT")
	{ ++integerp; ++natp; }
      if (i == 0 && limit->canonical) {
	if (limit->canonical->name == "MININT")
	  { ++integerp; }
	else if (limit->canonical->name == "0")
	  { ++natp; }
      }
    }

    if (integerp == 2)
      { as_set->canonical = new_variable (Integer {"INT", as_set->dom_typref}, true, PRIM); }
    else if (natp == 2)
      { as_set->canonical = new_variable (Integer {"NAT", as_set->dom_typref}, true, PRIM); }
    groundedness /= 2.0;
    as_set->ground = groundedness;
    return match == 2;
  }
    
  Variable *Variables::new_variable (Variable *var) {
    auto iter {all_vars.find (var)};
    if (iter != all_vars.cend ())
      { delete var; return *iter; }
    
    if (is_known_constant (var))
      { var->update_ground (1); }
    all_vars.insert (var);
    return var;
  }

  Interval *Variables::new_interval (Interval var, bool canonical, Integer *begin, Integer *end) {
    Interval *ptr {(Interval *) new_variable (Set {var.name, var.typref, var.dom_typref, 'I'}, canonical, SETS)};
    
    Integer *edges[2] {begin, end};
    for (int i {}; i < 2; ++i) {
      if (!ptr->var_bounds[i]) {
	if (!edges[i]) {
	  std::stringstream name;
	  name << (i ? "imax(" : "imin(") << ptr->name << ')';
	  ptr->var_bounds[i] = (Integer *) new_variable (Integer {name.str (), ptr->dom_typref}, false, PRIM);
	  ptr->add_element (ptr->var_bounds[i], ptr->var_bounds[i]->ground >= 1.0);
	}
	else
	  { ptr->var_bounds[i] = edges[i]; }
      }
    }
    return ptr;
  }

  Variable *Variables::new_variable (std::string name, int typref, const Types::TypeInfos *type_infos) {
    Variable *var {nullptr};
    switch (type_infos->get_concept (typref)) {
    case PRIM: {
      std::string type_name {type_infos->get_body (typref, type_infos->primitives)};
      if (type_name == "INTEGER")
	{ var = new_variable (Integer {name, typref}, false, PRIM); }
      else if (type_name == "BOOL")
	{ var = new_variable (Boolean {name, typref}, false, PRIM); }
      else
	{ std::cerr << name << " ∈ " << type_name << '\n'; }
    }
      break;
    case SETS:
      var = new_variable (Set {name, typref, type_infos->get_body (typref, type_infos->sets), 'S'}, false, SETS);
      break;
    case MAPS: {
      std::array<int, 2> domains {type_infos->get_body (typref, type_infos->mappings)};
      var = new_variable (Relation {name, typref, domains[0], domains[1]}, false, MAPS);
    }
    case RELS: {
      int dom_typref {type_infos->get_body (typref, type_infos->relations)};
      auto [from, to] {type_infos->get_body (dom_typref, type_infos->mappings)};
      var = new_variable (SetOfRelations {name, typref, dom_typref, from, to}, false, RELS);
      }
      break;
    default:
      std::cerr << "Unhandled concept for TypeInfo " << typref << '\n';
    }
    return var;
  }      

  const std::map<int, std::set<Variable *, VarPtrComp>> *Variables::pick_concept_container (int super_type) const {
    switch (super_type) {
    case PRIM:
      return &prim_vars;
    case SETS:
      return &set_vars;
    case MAPS:
      return &mapping_vars;
    case RELS:
      return &rel_vars;
    default:
      return nullptr;
    }
  }

  bool Variables::contains (const std::map<int, std::set<Variable *, VarPtrComp>> &container, const std::string &name, int typref) const {
    Variable var {name, typref};
    return container.at (typref).contains (&var);
  }

  bool Variables::contains (const std::string &name, int super_type, int typref) const {
    const std::map<int, std::set<Variable *, VarPtrComp>> *container {pick_concept_container (super_type)};
    if (container->contains (typref))
      { return contains (*container, name, typref); }
    return false;
  }
  
  Variable *Variables::find_var (const std::string &name, int super_type, int typref) const {
    const std::map<int, std::set<Variable *, VarPtrComp>> *container {pick_concept_container (super_type)};
    if (container->contains (typref)) {
      Variable var {name, typref};
      auto iter {container->at (typref).find (&var)};
      if (iter != container->at (typref).cend ())
	{ return *iter; }
    }
    return nullptr;
  }

  void Variables::relinquish_ownership () {
    all_vars.clear ();
  }
  
  void Variables::print_vars (const std::map<int, std::set<Variable *, VarPtrComp>> &coll, std::ostream &out) const {
    for (auto &[key, body] : coll) {
      std::cout << key << ":\n";
      for (Variable *var : body) 
	{ out << ' '; var->print (out); out << '\n'; }
    }
  }

  void Variables::print_all_vars (std::ostream &out) const {
    out << "Primitives:\n";
    print_vars (prim_vars, out);
    out << "\nSets:\n";
    print_vars (set_vars, out);
    out << "\nMappings:\n";
    print_vars (mapping_vars, out);
    out << "\nRelations:\n";
    print_vars (rel_vars, out);
  }
}
