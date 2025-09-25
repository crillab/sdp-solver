#ifndef CONSTRAINTS_H
#define CONSTRAINTS_H

#include "pugixml.hpp"

#include "types.hpp"
#include "variables.hpp"

#include <map>
#include <vector>

namespace Constraints {
  enum status
    { GOAL, LOC_AUX, AUX, CTX };

  struct Constraints;
  
  struct Bridi {
    std::vector<Variables::Variable *> arguments;
    std::string functor;
    bool negation;

    // Compares functors, then argument lists
    bool operator < (const Bridi &other) const;
    int get_arity () const;
    float get_groundness () const;
    float acc_grounds (std::vector<Variables::Variable *>::const_iterator cbegin,
		       std::vector<Variables::Variable *>::const_iterator cend) const;

    bool relation_as_set_element (std::set<Bridi> &output, Constraints &constraints) const;
    bool simple_set_element (std::set<Bridi> &output, Constraints &constraints) const;
    
    bool consistent_equality (std::set<Bridi> &output, Constraints &constraints) const;
    bool consistent_elementhood (std::set<Bridi> &output, Constraints &constraints) const;
    bool consistent_subset (std::set<Bridi> &output, Constraints &constraints) const;
    bool forward_check (std::set<Bridi> &output, Constraints &constraints) const;
  };

  std::ostream &operator << (std::ostream &out, const Bridi &bridi);
  
  struct ConstraintGraph {
    std::map<Variables::Variable *, std::set<Variables::Variable *, Variables::VarPtrComp>> enum_sets;
    std::set<Variables::Variable *, Variables::VarPtrComp> context_vars;
    int purpose;
    
    std::map<int, std::set<Bridi>> constraints;
    
    ConstraintGraph () = default;
    virtual ~ConstraintGraph () {
      for (Variables::Variable *var : context_vars)
	{ delete var; }
    }

    Variables::Variable *find_var (const std::string &name) const;
    void add_constraint (const std::string &functor, std::vector<Variables::Variable *> arguments, bool negation = false);
    void merge_graph (const ConstraintGraph &other);
    void relinquish_ownership ();
    void set_purpose (int status);
    bool forward_check (Constraints &host_constraints);

    void print (std::ostream &out = std::cout) const;
  };
  
  struct Constraints {
    ConstraintGraph constraint_graph;
    std::map<int, std::string> prim_types;
    Variables::Variables *variables;
    const Types::TypeInfos *type_infos;

    Constraints (Types::TypeInfos *type_infos) : variables {new Variables::Variables}, type_infos {type_infos} {
      for (const Types::Type<std::string> &type : type_infos->primitives)
	{ prim_types[type.id] = type.body; }
    }
    virtual ~Constraints () { delete variables; prim_types.clear (); }

    int get_body (int typref) const;
    std::array<int, 2> get_body (int typref, bool mappings) const;
    int get_concept (int typref) const;
    int get_home (int typref) const;
    void recuperate_var (Variables::Variable *var);
    void merge_graph ();
    void merge_graph (ConstraintGraph &other);
    void recognize_set (pugi::xml_node set, int typref_self, int typref_inside);
    void show_enum (std::ostream &out = std::cout);
    void recognize_enum (pugi::xml_node enumeration, Variables::Set *var);
    bool handle_exp_comparison (pugi::xml_node exp_comparison, int purpose, bool negation = false);

    bool exceptional_constraint (const std::string &functor, std::vector<Variables::Variable *> args, bool negation, ConstraintGraph &constraint_graph);
    int get_prim_type (const std::string &typ) const;

    Variables::Variable *find_var (const std::string &name, int super_type, int typref, const ConstraintGraph &tmp_constraint_graph) const;
    Variables::Variable *new_var_if (const std::string &name, int super_type, int typref, ConstraintGraph &tmp_constraint_graph, float ground = 0) const;
    Variables::Variable *surround_var (Variables::Variable *sumti, const std::string &selbri, int super_type, int typref, ConstraintGraph &tmp_cg, float ground = 0);
    Variables::Variable *unary_exp (pugi::xml_node unary_exp, ConstraintGraph &tmp_constraint_graph);
    Variables::Variable *maplet_var (pugi::xml_node mapley, ConstraintGraph &tmp_constraint_graph);
    Variables::Variable *maplet_var (Variables::Variable *arg1, Variables::Variable *arg2, int typref, ConstraintGraph &tmp_constraint_graph);
    Variables::Variable *boolean_exp (pugi::xml_node exp, ConstraintGraph &tmp_constraint_graph);
    void equicardinality (Variables::Variable *first, Variables::Variable *second, ConstraintGraph &tmp_cg);
    Variables::Variable *binary_exp (pugi::xml_node binary_exp, ConstraintGraph &tmp_constraint_graph);
    Variables::Variable *nary_exp (pugi::xml_node nary_exp, ConstraintGraph &tmp_constraint_graph);
    Variables::Variable *plain_interval (int typref, Variables::Variable *begin, Variables::Variable *end, ConstraintGraph &tmp_constraint_graph);
    Variables::Variable *make_ground_set (const std::vector<Variables::Variable *> &elements, int typref, int gov, int super_type, ConstraintGraph &tmp_constraint_graph);
    Variables::Variable *as_variable (pugi::xml_node node);
    Variables::Variable *as_variable (pugi::xml_node node, ConstraintGraph &tmp_constraint_graph);
    void get_variables_from_node (pugi::xml_node node);
    void make_variables (pugi::xml_node predicate);

    bool forward_check (int times);
  };
}
    
#endif
