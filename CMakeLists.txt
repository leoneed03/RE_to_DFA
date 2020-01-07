cmake_minimum_required(VERSION 3.12)
project(RE_to_DFA_Sasha)

set(CMAKE_CXX_STANDARD 11)

add_executable(RE_to_DFA_Sasha main.cpp dfa.h dfa.cpp regex_to_dfa.h regex_to_dfa.cpp dfa.cpp dfa.h regex_to_dfa.cpp regex_to_dfa.h)