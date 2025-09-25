#ifndef TYPES_H
#define TYPES_H

#include <array>
#include <iostream>
#include <set>
#include <string>

namespace Types {

  template<typename T>
  struct Type {
    int id;
    T body;

    bool operator < (const Type &other) const {
      return id < other.id;
    }
  };    

  std::ostream &operator << (std::ostream &out, const Type<std::string> &type);
  std::ostream &operator << (std::ostream &out, const Type<int> &type);
  std::ostream &operator << (std::ostream &out, const Type<std::array<int, 2>> &type);
  
  struct TypeInfos {
    std::set<Type<std::string>> primitives;
    std::set<Type<int>> sets;
    std::set<Type<std::array<int, 2>>> mappings;
    std::set<Type<int>> relations;

    TypeInfos (const char *filename);
    ~TypeInfos () = default;

    template<typename T>
    bool find (const int type, const std::set<Type<T>> &loc, auto &iter) const {
      auto bottom {loc.cbegin ()}, top {std::prev (loc.cend ())};
      if (bottom->id > type || top->id < type)
	{ return false; }
      while (bottom->id <= top->id) {
	auto mid {std::next (bottom, std::distance (bottom, top) / 2)};
	if (mid->id == type) {
	  iter = mid;
	  return true;
	}
	else if (mid->id < type)
	  { bottom = std::next (mid); }
	else
	  { top = std::prev (mid); }
      }
      return false;
    }

    int get_concept (int type) const;
    template<typename T>
    T get_body (int target, const std::set<Type<T>> &loc) const {
      auto iter {loc.cbegin ()};
      return find (target, loc, iter) ? iter->body : T {-1};
    }
    int get_home (int target) const;
  };
}

#endif
