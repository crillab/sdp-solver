#ifndef SAT_H
#define SAT_H

#include "cadical.hpp"
#include "constraints.hpp"
#include "graphs.hpp"
#include "rcc.hpp"
#include "variables.hpp"

#include <array>
#include <map>
#include <set>
#include <vector>

namespace SAT {
  enum kind { INT, BOOL, SET, REL };
  enum rcc { SUB = 1, SUPER = 2, EQ = 4, DISJ = 8, OVLP = 16, RCC_U = 31 };

  int inverse (int orig);
  int converse (int orig);
  bool single (int comparison);

  void iff (int lit_1, int lit_2, CaDiCaL::Solver *solver);
  int bind (int aux, std::vector<int> &&literals, CaDiCaL::Solver *solver, bool phase);
  int bind_clause (int aux, std::vector<int> &&literals, CaDiCaL::Solver *solver);
  int bind_term (int aux, std::vector<int> &&literals, CaDiCaL::Solver *solver);

  void at_most_one (int begin, int end, CaDiCaL::Solver *solver);
  void at_least_one (int begin, int end, CaDiCaL::Solver *solver);
  void exactly_one (int begin, int end, CaDiCaL::Solver *solver);
  
  void bottom (const char *reason, CaDiCaL::Solver *solver);

  struct SeqEncoding {
    int before_s_start;
    int width;

    SeqEncoding (int &next_var, int width);

    int s_idx (int i, int j);
    void first_determines_first (CaDiCaL::Solver *solver, int el_begin);
    void first_counts_for_at_most_one (CaDiCaL::Solver *solver);
    int one_iff (CaDiCaL::Solver *solver, int j, int q, int next_var);
    int k_iff (CaDiCaL::Solver *solver, int j, int q, int next_var);
    int operator () (CaDiCaL::Solver *solver, int el_begin, int el_end, int next_var);
  };
  
  struct PureBooleans {
    std::map<std::string, int> vars;
    std::set<std::vector<int>> clauses;

    PureBooleans (Graphs::BooleanGraph *bg, int next_var);
    ~PureBooleans () = default;

    void read_rules (const std::set<Constraints::Bridi> &rules);
    void to_solver (CaDiCaL::Solver *solver);
    void decode (CaDiCaL::Solver *solver, std::ostream &out = std::cout);
  };

  struct BoolPool {
    int t, f;
    std::set<int> elements;

    BoolPool () = default;
    BoolPool (int next_var);
    virtual ~BoolPool () = default;

    void to_solver (CaDiCaL::Solver *solver);
    void decode (CaDiCaL::Solver *solver, std::ostream &out = std::cout);
  };

  struct Extension {
    int el_begin {}, el_end {};
    int seq_start {}, seq_end {};

    Extension (int size, int start);
    virtual ~Extension () = default;

    int variable (int pos, int base) const;
    int initialize_seq (CaDiCaL::Solver *solver, int next_var);
    int get_nth_size_var (int n); // base 1
  };

  struct EnumeratedType {
    std::map<std::string, int> tokens;
    std::map<int, std::string> token_names;
    std::map<std::string, int> elements;
    const std::set<Constraints::Bridi> &rules;
    std::string name;
    int dom_size;
    int var_start, var_end;

    EnumeratedType () = default;
    EnumeratedType (const Graphs::EnumeratedType &graph, std::string name, int var_start, CaDiCaL::Solver *solver);
    EnumeratedType (const EnumeratedType &other) = default;
    ~EnumeratedType () = default;

    void apply_rule (const Constraints::Bridi &rule, CaDiCaL::Solver *solver);
    bool groundp (const std::string &title) const;
    int find_in_map (const std::string &title, const std::map<std::string, int> &map) const;
    int get_start (const std::string &title) const;
    int get_shift (const std::string &title) const;
    std::string get_name (int i) const;
    std::string val (const std::string &el, CaDiCaL::Solver *solver) const;
    void decode (CaDiCaL::Solver *solver, std::ostream &out = std::cout) const;
  };

  struct PowEnum {
    std::string name;
    EnumeratedType *home;
    int var_start, var_end;
    int size_first, size_last;

    std::set<int> definite_elements;
    std::set<std::string> other_elements;
    std::set<std::string> other_nogoods;

    PowEnum (const Graphs::EnumSubset &subset, const std::map<std::string, EnumeratedType *> &enums, int var_start);
    ~PowEnum () = default;

    void to_solver (CaDiCaL::Solver *solver);
    void decode (CaDiCaL::Solver *solver, std::ostream &out);
  };
  
  struct Type {
    std::vector<Extension *> extensions;
    int known_dom_size;
    int total_dom_size;
    int canonical_in_dom;
    int var_end;

    // {set, el} means el : set. {set, -el} means el /: set
    std::vector<std::array<int, 2>> canonical_element_rules;
    std::vector<std::array<int, 2>> other_element_rules;
    std::map<int, std::map<int, int>> rcc_rules;

    std::map<int, std::array<int, 2>> eq_el_vars; // (pos-of-var . (start . end))
    std::map<int, std::map<int, int>> rcc_vars;

    Type (int own_size, int known_dom_size, int total_dom_size, int start);
    virtual ~Type ();

    int get_own_size () const;
    int get_known_dom_size () const;
    int get_total_dom_size () const;
    int element_var (int set, int el, int base) const;

    void get_element_rule (const Constraints::Bridi &bridi, int el, int set);
    void get_rcc_rule (const Constraints::Bridi &bridi, int region_1, int region_2);
    void no_double_counting (int set, CaDiCaL::Solver *solver, const std::set<Variables::Variable *, Variables::VarPtrComp> &dom_var_location);
    int eq_el_array (int var_end, CaDiCaL::Solver *solver, const std::set<Variables::Variable *, Variables::VarPtrComp> &dom_variables);    
    int get_eq_var (int non_canon, int comparison, bool canon_comp) const;
    int get_non_canonical_pos (int non_canon) const;
    int get_canonical_pos (int canon) const;
    int get_element_idx (Variables::Variable *el, const std::set<Variables::Variable *, Variables::VarPtrComp> &dom_variables) const;

    void definite_elements (CaDiCaL::Solver *solver,
			    const std::set<Variables::Variable *, Variables::VarPtrComp> &own_variables,
			    const std::set<Variables::Variable *, Variables::VarPtrComp> &own_new_variables,
			    const std::set<Variables::Variable *, Variables::VarPtrComp> &dom_variables);
    int possible_elements (CaDiCaL::Solver *solver, int next_var,
			   const std::set<Variables::Variable *, Variables::VarPtrComp> &dom_variables);
    void impossible_el_equalities (CaDiCaL::Solver *solver,
				   const std::set<Constraints::Bridi> &element_rules,
				   const std::set<Variables::Variable *, Variables::VarPtrComp> &dom_variables,
				   const std::map<Variables::Variable *, Variables::Variable *, Variables::VarPtrComp> &dom_collisions);    

    int get_rcc_start (int first, int second, int &start, int next_var);
    int encode_rcc_rule (int first, int second, int val, int next_var, CaDiCaL::Solver *solver);
    int rcc_inclusion_sat (int first, int second, int rcc_start, int next_var, bool left_in_right, CaDiCaL::Solver *solver);
    int rcc_eq_sat (int first, int second, int start, int next_var, CaDiCaL::Solver *solver);
    int rcc_disj_sat (int first, int second, int start, int next_var, CaDiCaL::Solver *solver);
    int rcc_ovlp_sat (int first, int second, int start, int next_var, CaDiCaL::Solver *solver);
    int rcc_in_sat (CaDiCaL::Solver *solver, bool composition, bool eager, int next_var);
  };

  struct SetType : public Type {
    Graphs::SetGraph *graph;

    SetType () = default;
    SetType (int own_size, int known_size, int total_size, int start);

    void get_rules (const std::set<Constraints::Bridi> &rules);
    int to_solver (CaDiCaL::Solver *solver, int next_var);

    void decode (CaDiCaL::Solver *solver, std::ostream &out);
  };

  struct PowInt : public Type {
    Graphs::PowIntGraph *graph;

    PowInt () = default;
    PowInt (Graphs::PowIntGraph *graph, int k, int start);

    // get name of i^th member (of elements if el, of sets if not)
    std::string get_name (int i, bool el) const;
    void get_rules (const std::set<Constraints::Bridi> &rules);
    void mark_constant (CaDiCaL::Solver *solver, const std::string &compare, bool on);
    
    void empty_set_is_empty (CaDiCaL::Solver *solver);
    void all_ints_are_int (CaDiCaL::Solver *solver);
        
    int to_solver (CaDiCaL::Solver *solver, int next_var);

    void decode (int set, CaDiCaL::Solver *solver, std::ostream &out = std::cout);
    void decode (CaDiCaL::Solver *solver, std::ostream &out = std::cout);
  };

  struct Instance {
    CaDiCaL::Solver *solver {new CaDiCaL::Solver {}};
    std::map<std::string, EnumeratedType *> enums;
    std::map<std::string, PowEnum *> enum_subsets;
    std::map<std::string, BoolPool> bool_sets;
    PowInt *pow_int {nullptr};
    PureBooleans *prop_vars {nullptr};
    std::map<int, SetType *> sets;
    int next_var {1};

    Instance () = default;
    Instance (Graphs::Multigraph *multigraph, int k);
    ~Instance ();

    void to_solver ();
    int decode (std::ostream &out = std::cout);
  };
}

#endif
