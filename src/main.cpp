#include "pog.hpp"

#include <algorithm>
#include <array>
#include <filesystem>
#include <iostream>
#include <sstream>
#include <string>

std::string filename;
int po {-1}, goal {-1}, k {16}, times {2};

bool read_options (int argc, char **argv) {
  auto update
  { [argc, argv] (int &to_update, int i) {
    ++i;
    if (i >= argc)
      { return -1; }
    else
      { to_update = std::stoi (argv[i]); }
    return i;
  }};

  auto check_string
  { [argc, argv, &update] (int i) {
    std::string as_str {argv[i]};
    
    if (as_str == "--input") {
      ++i;
      if (i >= argc)
	{ return -1; }
      filename = argv[i];
      return i;
    }
    
    const int length {3};
    std::array<std::string, length> options {"--goal", "--proof-obligation", "--times"};
    for (int j {}; j < length; ++i) {
      if (as_str < options[j])
	{ return -1; }
      else if (as_str == options[j]) {
	switch (j) {
	case 0:
	  return update (goal, i);
	case 1:
	  return update (po, i);
	case 2:
	  return update (times, i);
	}
      }
    }
    return -1;
  }};
    
  for (int i {1}; i < argc; ++i) {
    if (argv[i][0] == '-') {
      switch (argv[i][1]) {
      case '-':
	i = check_string (i);
	break;
      case 'g':
	i = update (goal, i);
	break;
      case 'i':
	++i;
	if (i >= argc)
	  { return false; }
	else
	  { filename = argv[i]; }
	break;
      case 'k':
	i = update (k, i);
      case 'p':
	i = update (po, i);
	break;
      case 't':
	i = update (times, i);
	break;
      }
      if (i < 0)
	{ return false; }
    }
  }
  return !filename.empty ();
}

int loop (std::string filename, int po, int goal, bool validity_check, int times, int k, int &msf) {
  std::cout << (validity_check ? "UNSATISFIABLE\nTo verify:\n" : "For counterexample:\n");

  POG::POG pog {filename.c_str ()};
  if (!pog.read_variables (filename.c_str (), po, goal))
    { return 1; }

  // pog.print (std::cout);
  
  if (!pog.read_constraints (filename.c_str (), po, goal, validity_check)) {
    std::cout << "Goal unhandled.\n";
    return 20;
  }

  // pog.constraints->variables->print_all_vars (std::cout);
  // pog.constraints->constraint_graph.print (std::cout);

  if (!pog.constraints->forward_check (times)) {
    std::cout << "False after forward checking.\n";
    return 20;
  }

  // pog.constraints->constraint_graph.print (std::cout);

  pog.graphs (validity_check);
  // pog.multigraph->print ();

  pog.to_gqr ();

  pog.to_sat (validity_check ? msf ? msf : 1 : k);
  std::cout << "MSF: " << pog.multigraph->msf << '\n';
  pog.sat_instance->to_solver ();
  msf = pog.multigraph->msf;
  return pog.sat_instance->decode ();
}

std::string non_negated_path (const std::string &negated) {
  std::filesystem::path path {filename};
  std::string str {path.stem ().c_str ()};
  std::replace (str.begin (), str.end (), '-', ' ');
  std::stringstream sstream {str};
  std::string dir, rest;
  sstream >> dir >> rest;
  return "/home/evaluation/evaluation/pub/blasst/zenodo-dataset-pog-20220905/" + dir + "/" + rest.substr (0, rest.find ("_neg")) + ".pog";
}
  
int main (int argc, char **argv) {

  if (!read_options (argc, argv)) {
    std::cerr << "Usage: " << argv[0] << " <pog name> [--proof-obligation | -po <PO>] [--goal | -g <goal>] [-k <bound for SAT>] [--times | -t <times to forward check>]\n";
    return 1;
  }

  // int msf {k};
  // if (loop (filename, po, goal, false, times, k, msf) != 10)
  //   { loop (non_negated_path (filename), po, goal, true, times, k, msf); }
  int status {loop (filename, po, goal, false, times, k, k)};

  return 0;
}
