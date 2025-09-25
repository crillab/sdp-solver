#include "types.hpp"

#include "pugixml.hpp"

#include <array>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <string>

namespace Types {
  enum concepts
    { PRIM, SETS, MAPS, RELS, UNKNOWN };
  
  struct TypeReader {
    std::map<std::string, int> known_types;
    int counter {};

    void associate_id (std::string description, int id) {
      known_types[description] = id;
    }

    int new_type (std::string description) {
      int output {++counter};
      known_types[description] = output;
      
      pugi::xml_document doc;
      doc.load_string (description.c_str ());
      pugi::xml_node outer {doc.first_child ()};
      
      switch (outer.name ()[0]) {
      case 'B': {
	std::stringstream first, second;
	outer.first_child ().print (first);
	outer.first_child ().next_sibling ().print (second);
	mappings.insert (Type<std::array<std::string, 2>> {output, {first.str (), second.str ()}});
      }
	break;
      case 'U': {
	  std::stringstream body;
	  outer.first_child ().print (body);
	  sets.insert (Type<std::string> {output, body.str ()});
	}
      }
      return output;
    }
      
    int query_id (std::string description) {
      if (known_types.contains (description))
	{ return known_types[description]; }
      return new_type (description);
    }

    std::set<Type<std::string>> sets;
    std::set<Type<std::string>> relations;
    std::set<Type<std::array<std::string, 2>>> mappings;
  };

  bool read_type_node (const pugi::xml_node &node, TypeReader *type_reader, TypeInfos *type_infos) {
    int id {node.attribute ("id").as_int ()};
    type_reader->counter = type_reader->counter >= id ? type_reader->counter : id;
    std::stringstream sstream;
    pugi::xml_node body {node.first_child ()};
    body.print (sstream);
    type_reader->associate_id (sstream.str (), id);

    if (body.first_child ()) {
      std::stringstream first_child;
      body.first_child ().print (first_child);

      switch (body.name ()[0]) {
      case 'B': {
	std::stringstream codomain;
	body.first_child ().next_sibling ().print (codomain);
	type_reader->mappings.insert (Type<std::array<std::string, 2>> {id, {first_child.str (), codomain.str ()}});
      }
	break;
      case 'U':
	if (body.first_child ().name ()[0] == 'B')
	  { type_reader->relations.insert (Type<std::string> {id, first_child.str ()}); }
	else
	  { type_reader->sets.insert (Type<std::string> {id, first_child.str ()}); }
	break;
      default:
	std::cerr << "Bad name in\n";
	body.print (std::cerr);
	return false;
      }
    }
    else
      { type_infos->primitives.insert (Type<std::string> {id, body.attribute ("value").value ()}); }

    return true;
  }

  std::ostream &operator << (std::ostream &out, const Type<std::string> &type) {
    out << type.id << '=' << type.body;
    return out;
  }

  std::ostream &operator << (std::ostream &out, const Type<int> &type) {
    out << type.id << "=P(" << type.body << ')';
    return out;
  }

  std::ostream &operator << (std::ostream &out, const Type<std::array<int, 2>> &type) {
    out << type.id << '=' << type.body[0] << 'x' << type.body[1];
    return out;
  }

  TypeInfos::TypeInfos (const char *filename) {
    pugi::xml_document doc;
    doc.load_file (filename);
    pugi::xml_node infos {doc.first_child ().child ("TypeInfos")};

    TypeReader *type_reader {new TypeReader};
    for (const pugi::xml_node &node : infos.children ())
      { read_type_node (node, type_reader, this); }

    int hash_map, hash_set, hash_rels;
    do {
      hash_rels = (int) type_reader->relations.size ();
      hash_map = (int) type_reader->mappings.size ();
      hash_set = (int) type_reader->sets.size ();
      for (const Type<std::array<std::string, 2>> &type : type_reader->mappings) 
	{ mappings.insert (Type<std::array<int, 2>> {type.id, {type_reader->query_id (type.body[0]), type_reader->query_id (type.body[1])}}); }
      for (const Type<std::string> &type : type_reader->sets) 
	{ sets.insert (Type<int> {type.id, {type_reader->query_id (type.body)}}); }
      for (const Type<std::string> &type : type_reader->relations)
	{ relations.insert (Type<int> {type.id, {type_reader->query_id (type.body)}}); }
    } while (hash_map < type_reader->mappings.size ()
	     || hash_set < type_reader->sets.size ()
	     || hash_rels < type_reader->relations.size ());
    delete type_reader;
  }

  int TypeInfos::get_concept (int type) const {
    {
      std::set<Type<std::string>>::iterator ignore;
      if (find (type, primitives, ignore))
	{ return PRIM; }
    }
    {
      std::set<Type<int>>::iterator ignore;
      if (find (type, sets, ignore))
	{ return SETS; }
    }
    {
      std::set<Type<std::array<int, 2>>>::iterator ignore;
      if (find (type, mappings, ignore))
	{ return MAPS; }
    }
    {
      std::set<Type<int>>::iterator ignore;
      if (find (type, relations, ignore))
	{ return RELS; }
    }
    return UNKNOWN;
  }

  int TypeInfos::get_home (int target) const {
    for (const Type<int> &s : sets)
      { if (s.body == target) { return s.id; } }
    for (const Type<int> &r : relations)
      { if (r.body == target) { return r.id; } }
    return -1;
  }
}
