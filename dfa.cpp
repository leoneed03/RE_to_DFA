#include "dfa.h"
using namespace std;

int DFA::size() const {return (int)nodes_.size();}
void DFA::add_node(int node) {nodes_.insert(node);}

void DFA::set_initial(int node) {add_node(node); initial_ = node;}
void DFA::add_final(int node) {add_node(node); final_nodes_.insert(node);}

void DFA::add_transition(int from, char letter, int to) {
    add_node(from);
    add_node(to);
    transitions_[make_pair(from, letter)] = to;
}

ostream& operator << (ostream &out, const DFA &dfa) {
    //output states
    /*out << dfa.size() << '\n';
    for (int node : dfa.nodes_)
        out << node << " ";
    out << '\n';*/
    //output letters

    //output number of transitions
    out << dfa.transitions_.size() << '\n';

    unordered_set<char> letters;
    for (auto it : dfa.transitions_)
        letters.insert(it.first.second);
    /////out << letters.size() << '\n';
    /*for (char letter : letters)
        out << letter << " ";
    out << '\n';*/
    //output initial state
    ///////out << dfa.initial_ << '\n';

    for (auto it : dfa.transitions_) {
        if (it.first.first == dfa.initial_)
            out << it.first.first << ' ' << it.first.second << ' ' << it.second << '\n';
    }

    for (auto it : dfa.transitions_) {
        if (it.first.first != dfa.initial_)
            out << it.first.first << ' ' << it.first.second << ' ' << it.second << '\n';
    }
    //output final states
    ////////out << dfa.final_nodes_.size() << '\n';
    for (int node : dfa.final_nodes_)
        out << node << "\n";
    out << "#";
    return out;
}