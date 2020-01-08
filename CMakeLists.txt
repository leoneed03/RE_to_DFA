cmake_minimum_required(VERSION 3.12)
project(RE_to_DFA_Sasha)

set(CMAKE_CXX_STANDARD 11)

add_executable(RE_to_DFA_Sasha main.cpp AUTOMATA.h AUTOMATA.cpp RE_to_AUTOMATA.h RE_to_AUTOMATA.cpp AUTOMATA.cpp AUTOMATA.h RE_to_AUTOMATA.cpp RE_to_AUTOMATA.h)