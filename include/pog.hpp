#ifndef POG_H
#define POG_H


#include "pugixml.hpp"

#include "constraints.hpp"
#include "graphs.hpp"
#include "sat.hpp"
#include "types.hpp"
#include "variables.hpp"

namespace POG {
  struct POG {
    Types::TypeInfos *type_infos;
    Constraints::Constraints *constraints;
    Graphs::Multigraph *multigraph {nullptr};
    SAT::Instance *sat_instance {nullptr};

    POG (const char *filename);
    ~POG ();

    int get_concept (int type);
    
    std::string get_primitive_var (int type);
    int get_set_var (int type);
    std::array<int, 2> get_mapping_var (int type);
    int get_rel_var (int type);

    bool handle_exp_comparison (pugi::xml_node comparison, int purpose, bool negation = false);
    bool handle_pred (pugi::xml_node predicate, int purpose, bool negation = false);
    bool read_auxiliaries_for_vars (pugi::xml_node inner, pugi::xml_node outer, const char *name);
    bool read_auxiliaries (pugi::xml_node inner, pugi::xml_node outer, const char *name,
			   int &succ, int &all, bool get_vars = false);
    bool read_goal (pugi::xml_node simple_goal, bool get_vars = false);
    bool locate_goal (int po, int goal, pugi::xml_node pog,
		      pugi::xml_node &proof_obligation,
		      pugi::xml_node &principal);
      
    bool read_variables (const char *filename, int po, int goal);
    bool read_variables (int po, int goal);
    bool read_constraints (const char *filename, int po, int goal, bool validity_check, std::ostream &succ_stream = std::cout);

    void graphs (bool validity_check);
    bool to_gqr ();
    void to_sat (int k);
    
    template<typename T>
    void print (const std::set<Types::Type<T>> &location, std::ostream &out = std::cout) {
      for (const Types::Type<T> &t : location)
	{ std::cout << t << ' '; }
      std::cout << '\n';
    }
    void print (std::ostream &out = std::cout);
  };
}

#endif
