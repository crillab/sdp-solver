#ifndef GRAPHS_H
#define GRAPHS_H

#include "constraints.hpp"
#include "variables.hpp"

#include <iostream>
#include <map>
#include <set>

namespace Graphs {

  struct EnumeratedType {
    std::set<Variables::EnumInt *> tokens;
    std::set<Variables::Variable *, Variables::VarPtrComp> elements;
    std::set<Variables::Variable *, Variables::VarPtrComp> new_variables;
    std::map<Variables::Variable *, Variables::Variable *, Variables::VarPtrComp> collisions;
    std::set<Constraints::Bridi> rules;
    std::string name;

    EnumeratedType () = default;
    EnumeratedType (const std::string &name, std::set<Variables::EnumInt *> tokens, std::set<Variables::Variable *> elements);
    ~EnumeratedType ();
  };

  struct EnumSubset {
    std::set<std::string> potential_elements;
    std::set<Constraints::Bridi> rules;
    Variables::Set *as_set_var;
    std::string name;
    EnumeratedType *type;

    EnumSubset (EnumeratedType &type, Variables::Variable *var);
    ~EnumSubset () = default;

    bool operator < (const EnumSubset &other) const;
  };
  
  struct TyprefGraph {
    std::map<Variables::Variable *, Variables::Variable *, Variables::VarPtrComp> collisions;
    std::set<Variables::Variable *, Variables::VarPtrComp> variables;
    std::set<Variables::Variable *, Variables::VarPtrComp> new_variables;
    std::set<Constraints::Bridi> rules;
    int typref {-1};

    void add_alias (std::map<Variables::Variable *, int, Variables::VarPtrComp> &collisions,
		    Variables::Variable *var, int &counter, bool whether_to_increment) const;
    virtual bool thin_doubles (const std::map<int, std::set<Variables::Variable *, Variables::VarPtrComp>> &source, int &msf);
    virtual void print (std::ostream &out = std::cout);

    virtual void insert_canonical (Variables::Variable *var, int &msf);
    virtual void insert_loose_var (Variables::Variable *var, int &msf);
    int get_prim_typref (const Constraints::Constraints &constraints, const std::string &type) const;
  };

  struct BooleanGraph : public TyprefGraph {
    BooleanGraph (const Constraints::Constraints &constraints);
    virtual ~BooleanGraph ();

    void relevant_constraints (const Constraints::Constraints &constraints);
  };

  struct IntegerGraph : public TyprefGraph {
    std::set<Variables::Variable *> skip;
    
    IntegerGraph (const Constraints::Constraints &constraints);
    virtual ~IntegerGraph ();

    void thin_doubles (const std::map<int, std::set<Variables::Variable *, Variables::VarPtrComp>> &source, int typref, std::map<Variables::Variable *, EnumeratedType, Variables::VarPtrComp> &enums, bool validity_check);
    void relevant_constraints (const Constraints::Constraints &constraints, std::map<Variables::Variable *, EnumeratedType, Variables::VarPtrComp> &enums);
    void group_synonyms ();

    void print (std::ostream &out = std::cout);
  };

  struct SetlikeTyprefGraph : public TyprefGraph {
    std::set<Constraints::Bridi> element_rules;
    int dom_size {};
  };
    
  struct PowIntGraph : public SetlikeTyprefGraph {
    IntegerGraph *dom;

    PowIntGraph (const Constraints::Constraints &constraints, IntegerGraph *dom, int typref);
    virtual ~PowIntGraph ();

    void nats_are_non_neg (const std::string &nat_name, int comp);
    bool thin_doubles (const std::map<int, std::set<Variables::Variable *, Variables::VarPtrComp>> &source,
		       std::map<Variables::Variable *, EnumeratedType, Variables::VarPtrComp> &enums,
		       std::map<Variables::Variable *, std::set<EnumSubset>, Variables::VarPtrComp> &enum_subsets, int &msf);
    void relevant_constraints (const Constraints::Constraints &constraints,
			       std::map<Variables::Variable *, EnumeratedType, Variables::VarPtrComp> &enums,
			       std::map<Variables::Variable *, std::set<EnumSubset>, Variables::VarPtrComp> &enum_subsets);
  };

  struct PowBoolGraph : public SetlikeTyprefGraph {
    BooleanGraph *dom;

    PowBoolGraph (const Constraints::Constraints &constraints, BooleanGraph *dom, int typref);
    virtual ~PowBoolGraph ();

    void relevant_constraints (const Constraints::Constraints &constraints);
  };
    
  struct SetGraph : public SetlikeTyprefGraph {
    int dom_typref {-1};
    TyprefGraph *dom {nullptr};

    SetGraph (int typref, int dom);
    SetGraph (const Constraints::Constraints &constraints, int typref, int dom);
    virtual ~SetGraph ();

    void setup (const Constraints::Constraints &constraints, TyprefGraph *dom);
    void relevant_constraints (const Constraints::Constraints &constraints);
    void insert_canonical (Variables::Variable *var, int &msf);
    void insert_loose_var (Variables::Variable *var, int &msf);
  };

  struct RelGraph : public TyprefGraph {
    TyprefGraph *from, *to;
    int dom_typref {-1}, ran_typref {-1};
    int dom_size {}, cod_size {};

    RelGraph (int typref, int dom_typref, int ran_typref);
    virtual ~RelGraph ();

    void setup (const Constraints::Constraints &constraints, TyprefGraph *from, TyprefGraph *to);
    void relevant_constraints (const Constraints::Constraints &constraints);
  };
  
  struct Multigraph {
    IntegerGraph *i_graph {nullptr};
    BooleanGraph *b_graph {nullptr};
    PowIntGraph *pi_graph {nullptr};
    PowBoolGraph *pb_graph {nullptr};
    std::map<int, SetGraph *> set_graphs;
    std::map<int, RelGraph *> rel_graphs;
    std::map<Variables::Variable *, EnumeratedType, Variables::VarPtrComp> enums;
    std::map<Variables::Variable *, std::set<EnumSubset>, Variables::VarPtrComp> enum_subsets;

    int msf {};
    bool validity_check;

    Multigraph (const Constraints::Constraints &constraints, bool validity_check = false);
    ~Multigraph ();

    bool to_gqr ();
    TyprefGraph *get_graph_by_typref (int typref, bool prims = false);
    void sort_integers (const std::map<int, std::set<Variables::Variable *, Variables::VarPtrComp>> &source, const Constraints::Constraints &constraints, int typref, bool validity_check);
    void sort_pow_int (const Constraints::Constraints &constraints, int typref, bool validity_check);
    void print (std::ostream &out = std::cout);
  };
}

#endif
