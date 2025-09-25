#ifndef VARS_H
#define VARS_H

#include "pugixml.hpp"

#include <climits>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <vector>

namespace Variables {
  enum super_types
    { PRIM, SETS, MAPS, RELS, UNKNOWN };

  struct Variables;

  struct Variable {
    float ground;
    const std::string name;
    const int typref;
    const int super_type;

    struct ByName {
      bool operator () (Variable *var1, Variable *var2) const {
	return var1->name < var2->name;
      }
    };
    
    Variable *canonical {nullptr};
    std::set<Variable *, ByName> alias;

    Variable (std::string name, int typref = -1, int super_type = -1);
    virtual ~Variable () = default;

    bool operator < (const Variable &other) const {
      return name < other.name;
    }

    Variable *get_value () const {
      return canonical;
    }
    
    virtual bool update_values (Variables *variables) { return true; }
    virtual void bind_names (Variable *other);
    virtual void update_ground ();
    virtual void update_ground (float new_ground);
    virtual Variable *update_ground (Variable *gr_form);
    virtual bool compare (const Variable *other) const;
    virtual void print (std::ostream &out = std::cout) const;
  };
  
  struct VarPtrComp {
    bool operator () (Variable *var1, Variable *var2) const {
      return var1->name < var2->name;
    }
  };

  struct Primitive : public Variable {
    char type;
    
    Primitive (std::string name, int typref, char type);
    virtual ~Primitive () = default;

    virtual bool empty () = 0;
    virtual void update_domain (const std::string &str) = 0;
    
    virtual void print (std::ostream &out = std::cout) const;
  };

  struct PrimConst : public Primitive {
    PrimConst (std::string name, int typref, char type)
      : Primitive {name, typref, type} {
      ground = 1.0;
      canonical = this;
    }
    virtual ~PrimConst () = default; 
    bool empty () { return false; }
    void update_domain (const std::string &str) {}
  };

  struct ConstInt : public PrimConst {
    long long value;
    
    ConstInt (long long val, int typref);
    ConstInt (const std::string &name, int typref);
    ~ConstInt () = default;

    void print (std::ostream &out = std::cout) const;
  };

  struct EnumInt : public PrimConst {
    Variable *home;
    EnumInt (std::string name, int typref, Variable *home);
    ~EnumInt () = default;
    void print (std::ostream &out = std::cout) const;
  };
        
  struct Integer : public Primitive {
    long long bounds[2] {LLONG_MIN, LLONG_MAX};
    Variable *enumerated {nullptr};

    Integer (std::string name, int typref);
    Integer (std::string name, int typref, long long glb, long long  lub);
    ~Integer () = default;

    bool compare (const Integer *other) const;
    bool empty ();
    bool update_values (Variables *variables);
    void give_home (Variable *enumeration);
    Variable *update_ground (Variable *gr);
    void update_domain (const std::string &str);
    void update_bounds (long long bound, bool lower);
    void update_bounds (long long glb, long long lub);
    void update_bounds (long long bound);

    std::string get_value (EnumInt *canon) const;
    long long get_value (ConstInt *canon) const;
    std::string get_value (const std::string &) const;
    long long get_value (long long) const;
    
    void print (std::ostream &out = std::cout) const;
  };

  struct Boolean : public Primitive {
    bool domain[2] {true, true}; // {can be false, can be true}

    Boolean (std::string name, int typref);
    ~Boolean () = default;

    bool empty ();
    void determine_val (bool phase);
    void update_domain (const std::string &str);

    bool get_value () const;
    
    void print (std::ostream &out = std::cout) const;
  };

  struct ConstBool : public PrimConst {
    bool phase;

    ConstBool (bool val, int typref);
    ConstBool (const std::string &name, int typref);
    ~ConstBool () = default;

    void print (std::ostream &out) const;
  };
  
  struct Set : public Variable {
    long long card_bounds[2] {0, LLONG_MAX};
    Integer *var_bounds[2] {nullptr, nullptr}; // Only known use so far - for intervals.
    const int dom_typref; // Typref of elements
    Variable *enumerated {nullptr};
    char type {};
    std::set<Variable *, VarPtrComp> canonical_elements;
    std::set<Variable *, VarPtrComp> elements;
    std::set<Variable *, VarPtrComp> canonical_nogoods;
    std::set<Variable *, VarPtrComp> nogoods;
    
    Set (std::string name, int own_typref, int dom_typref, char type);
    Set (std::string name, int own_typref, int dom_typref, bool enumerated, char type);
    explicit Set (std::string name, int super_type, int own_typref, int dom_typref, char type);
    virtual ~Set () = default;

    virtual bool definitely_includes (Variable *var);
    virtual bool definitely_discludes (Variable *var);
    virtual unsigned long long get_card (bool &unground);
    void set_card (long long inf, long long sup);
    void set_card (long long bound, bool lower);
    void set_card (long long cardinality);
    void determine_element (Variable *var, bool ground, bool in);
    void add_element (Variable *var, bool ground);
    void block_element (Variable *var, bool ground);
    virtual bool compare (const Set *other) const;
    Variable *update_ground (const Variable *other, Variables *variables);
    void print (std::ostream &out = std::cout) const;
  };

  struct Interval : public Set {
    Interval (std::string name, int own_typref, int dom_typref)
      : Set {name, own_typref, dom_typref, 'I'} {}
    Interval (std::string name, int own_typref, int dom_typref, Integer *min_el, Integer *max_el)
      : Set {name, own_typref, dom_typref, 'I'} {
      var_bounds[0] = min_el;
      var_bounds[1] = max_el;
    }
    void ground_bounds (int int_typref);
    unsigned long long get_card (bool &fail);
    bool compare (const Interval *other) const;
  };
  
  struct Relation : public Set {
    const int cod_typref; // Typref of codomain elements
    
    Relation (std::string name, int own_typref, int dom_typref, int cod_typref);
    virtual ~Relation () = default;

    void print (std::ostream &out = std::cout) const;
  };

  struct SetOfRelations : public Set {
    int from_typref {-1}, to_typref {-1};
    Variable *from {}, *to {};
    Variables *enumerated_from {}, *enumerated_to {};
    SetOfRelations (std::string name, int own_typref, int dom_typref, int from_typref, int to_typref)
      : Set {name, own_typref, dom_typref, 'R'}, from_typref {from_typref}, to_typref {to_typref} {}
    ~SetOfRelations () = default;
  };
    
  struct Pair : public Relation {
    Variable *from, *to;
    Pair (std::string name, int typref, Variable *from, Variable *to)
      : Relation {name, typref, from->typref, to->typref}, from {from}, to {to} {}
  };

  struct VarGroup : public Variable {
    std::set<Variable *, VarPtrComp> class_vars;
    Variable *enumerated {nullptr};

    VarGroup (std::string name, std::set<Variable *, VarPtrComp> vars)
      : Variable {name, (*vars.begin ())->typref, ((*vars.begin ())->super_type)} {
      class_vars = vars;
      alias.insert ((Variable *) this);
    }

    void take_ownership (std::set<Variable *, VarPtrComp> vars);
  };

  struct Variables {
    
    std::set<Variable *, VarPtrComp> all_vars;
    std::map<int, std::set<Variable *, VarPtrComp>> prim_vars;
    std::map<int, std::set<Variable *, VarPtrComp>> set_vars;
    std::map<int, std::set<Variable *, VarPtrComp>> mapping_vars;
    std::map<int, std::set<Variable *, VarPtrComp>> rel_vars;
    std::set<std::string> known_constants {"[0,MAXINT]", "[MININT,MAXINT]", "BOOL", "FALSE", "INT", "INTEGER", "MAXINT", "MININT", "NAT", "NAT1", "NATURAL", "NATURAL1", "TRUE", "{}"};

    ~Variables () {
      for (Variable *var : all_vars)
	{ delete var; }
    }

    bool is_known_constant (Variable *var);
    void add_instance_of_typref (std::map<int, std::set<Variable *, VarPtrComp>> &collection, Variable *var);

    Variable *make_constant (const std::string &name, int typref, int gov = 0);
    Variable *make_empty_set (int typref, int gov);
    Variable *make_bool_domain (int typref, int gov);
    Variable *make_int_lit (int typref, ConstInt *lit);

    template<typename T>
    Variable *make_int_lit (T val, int typref) {
      return make_int_lit (typref, (ConstInt *) new_variable (ConstInt {val, typref}, true, PRIM));
    }
      
    Variable *make_int_limit (char second_letter, int typref);
    Variable *make_int_interval (char first_letter, int typref, int gov);
    bool set_to_interval (Variable *not_yet_interval, Variable *interval);

    template<typename T>
    Variable *new_variable (T var, bool canonical, int super_type) {
      Variable *ptr {(Variable *) new T {var}};
      ptr = new_variable (ptr);
      switch (super_type) {
      case PRIM:
	add_instance_of_typref (prim_vars, ptr);
	break;
      case SETS:
	add_instance_of_typref (set_vars, ptr);
	break;
      case MAPS:
	add_instance_of_typref (mapping_vars, ptr);
	break;
      case RELS:
	add_instance_of_typref (rel_vars, ptr);
	break;
      default:
	std::cerr << "Bad concept: " << super_type << '\n';
      }
      if (canonical)
	{ ptr->canonical = ptr; }
      return ptr;
    }

    Variable *new_variable (Variable *var);
    Variable *new_variable (std::string name, int typref, const Types::TypeInfos *type_infos);
    Interval *new_interval (Interval var, bool canonical, Integer *begin = nullptr, Integer *end = nullptr);

    const std::map<int, std::set<Variable *, VarPtrComp>> *pick_concept_container (int super_type) const;
    bool contains (const std::map<int, std::set<Variable *, VarPtrComp>> &container, const std::string &name, int typref) const;
    bool contains (const std::string &name, int super_type, int typref) const;
    Variable *find_var (const std::string &name, int super_type, int typref) const;

    void relinquish_ownership ();
    
    void print_vars (const std::map<int, std::set<Variable *, VarPtrComp>> &coll, std::ostream &out = std::cout) const;
    void print_all_vars (std::ostream &out) const;
  };
}

#endif
