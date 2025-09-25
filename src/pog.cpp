#include "pog.hpp"

#include <array>
#include <iostream>
#include <set>

namespace POG {
  enum purpose
    { GOAL, LOC_AUX, AUX, CTX };
  
  POG::POG (const char *filename)
    : type_infos {new Types::TypeInfos {filename}},
      constraints {new Constraints::Constraints {type_infos}} {}
  POG::~POG () {
    delete sat_instance;
    delete multigraph;
    delete constraints;
    delete type_infos;
  }
  
  int POG::get_concept (int type) {
    return type_infos->get_concept (type);
  }

  std::string POG::get_primitive_var (int type) {
    return type_infos->get_body (type, type_infos->primitives);
  }
  int POG::get_set_var (int type) {
    return type_infos->get_body (type, type_infos->sets);
  }
  std::array<int, 2> POG::get_mapping_var (int type) {
    return type_infos->get_body (type, type_infos->mappings);
  }
  
  bool POG::handle_exp_comparison (pugi::xml_node comparison, int purpose, bool negation) {
    return constraints->handle_exp_comparison (comparison, purpose, negation);
  }
  
  bool POG::handle_pred (pugi::xml_node predicate, int purpose, bool negation) {
    constraints->constraint_graph.set_purpose (purpose);
    switch (predicate.name ()[0]) {
    case 'E':
      if (!handle_exp_comparison (predicate, purpose, negation))
	{ return false; }
      break;
    case 'U':
      if (!handle_pred (predicate.first_child (), purpose, !negation))
	{ return false; }
      break;
    default:
      predicate.print (std::cerr);
      return false;
    }
    return true;
  }

  bool POG::read_auxiliaries_for_vars (pugi::xml_node inner, pugi::xml_node outer, const char *name) {
    int ign, ore;
    return read_auxiliaries (inner, outer, name, ign, ore, true);
  }
  
  bool POG::read_auxiliaries (pugi::xml_node inner, pugi::xml_node outer, const char *name,
			      int &succ, int &all, bool get_vars) {
    std::string reference {name[0] == 'D' ? "Definition" : "Ref_Hyp"},
      source {name[0] == 'D' ? "Define" : "Local_Hyp"};
    int purpose {name[0] == 'D' ? AUX : LOC_AUX};
    const char *nm {name[0] == 'D' ? "name" : "num"};

    for (pugi::xml_node ref : inner.children (reference.c_str ())) {
      std::string name {ref.attribute (nm).value ()};
      for (pugi::xml_node val : outer.children (source.c_str ())) {
	if (name == val.attribute (nm).value () && name != "B definitions") {
	  for (pugi::xml_node pred : val.children ()) {
	    if (get_vars) 
	      { constraints->make_variables (pred); }
	    else {
	      if (std::string {"Set"} == pred.name ())
		{}
	      else {
		++all;
		succ += handle_pred (pred, purpose) ? 1 : 0;
	      }
	    }
	  }
	  break;
	}
      }
    }

    return true;
  }

  bool POG::read_goal (pugi::xml_node simple_goal, bool get_vars) {
    if (get_vars)
      { constraints->make_variables (simple_goal.child ("Goal")); }
    else
      { return handle_pred (simple_goal.child ("Goal").first_child (), GOAL, true); }
    return true;
  }

  bool POG::locate_goal (int po, int goal, pugi::xml_node pog,
			 pugi::xml_node &proof_obligation, pugi::xml_node &principal) {
    auto find
      { [] (pugi::xml_node &node, int idx, const char *type) {
	for (int i {}; i < idx; ++i)
	  { node = node.next_sibling (type); }
	return !node ? false : true;
      }};

    proof_obligation = pog.child ("Proof_Obligation");
    if (po < 0 || goal < 0 || !find (proof_obligation, po, "Proof_Obligation")
	|| (principal = proof_obligation.child ("Simple_Goal")), !find (principal, goal, "Simple_Goal")) {
      std::cerr << "No proof obligation " << po << ':' << goal << '\n';
      return false;
    }
    return true;
  }

  bool POG::read_variables (const char *filename, int po, int goal) {
    pugi::xml_document doc;
    doc.load_file (filename);
    pugi::xml_node pog {doc.first_child ()};
    
    pugi::xml_node proof_obligation;
    pugi::xml_node principal;
    if (!locate_goal (po, goal, pog, proof_obligation, principal))
      { return false; }
    read_auxiliaries_for_vars (proof_obligation, pog, "Def");
    read_auxiliaries_for_vars (principal, proof_obligation, "Hyp");
    read_goal (principal, true);
    return true;
  }

  bool POG::read_constraints (const char *filename, int po, int goal, bool validity_check, std::ostream &succ_stream) {
    pugi::xml_document doc;
    doc.load_file (filename);
    pugi::xml_node pog {doc.first_child ()};
    
    pugi::xml_node proof_obligation;
    pugi::xml_node principal;
    if (!locate_goal (po, goal, pog, proof_obligation, principal))
      { return false; }

    int succ {}, all {};
    read_auxiliaries (proof_obligation, pog, "Def", succ, all);
    read_auxiliaries (principal, proof_obligation, "Hyp", succ, all);
    succ_stream << "Handling rate: " << succ << '/' << all << '\n';
    return read_goal (principal, validity_check); // True if goal handled
  }

  void POG::graphs (bool validity_check) {
    multigraph = new Graphs::Multigraph (*constraints, validity_check);
  }

  bool POG::to_gqr () {
    if (multigraph)
      { return multigraph->to_gqr (); }
    return true;
  }
  
  void POG::to_sat (int k) {
    if (multigraph)
      { sat_instance = new SAT::Instance {multigraph, k}; }
  }
  
  void POG::print (std::ostream &out) {
    out << "Primitives:\n  ";
    print (type_infos->primitives);
    out << "Sets:\n  ";
    print (type_infos->sets);
    out << "Mappings:\n  ";
    print (type_infos->mappings);
    out << "Relations:\n  ";
    print (type_infos->relations);
  }
}
