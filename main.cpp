
#include <cstring>
#include "RE_to_AUTOMATA.h"
#include <algorithm>
#include <iostream>
#include <fstream>
#include <map>
#include <string>
#include <set>
#include <utility>

using namespace std;

string path = "DFA.txt";

vector<vector<string>> table;
vector<vector<string>> table_before_Aho;
vector<string> rows;
vector<string> col;
vector<vector<string>> min_table_before_Mart;
vector<vector<string>> min_table_before_Aho;

vector<string> aho_rows;
vector<string> aho_col;

set<int> deleted_states;
vector<string> min_rows;
map<string, int> min_masks;
vector<string> min_col;
vector<vector<string>> min_table;

class  Automata
{
    typedef std::map<std::string, std::string>  T_real_states_names;
    //-----------------------------------------------------------------------------------
    std::map   <std::pair  <std::string,  char>,   std::string>              rules_;
    std::map   <std::pair  <std::string,  char>,   std::string>              rules_with_first_start_state_;
    const std::string   DEFAULT_STATE_NAME_;
    T_real_states_names  real_states_names_;
    std::set   <std::string>       accept_states_names_;
    //-----------------------------------------------------------------------------------
public:
    Automata
            (
                    const std::map   <std::pair  <std::string,  char>,   std::string>&  rules,
                    const std::map   <std::pair  <std::string,  char>,   std::string>&  rules_with_first_start_state
            )
            : rules_                         (rules),
              rules_with_first_start_state_  (rules_with_first_start_state),
              DEFAULT_STATE_NAME_            ()
    {
        delete_unreachable();
        std::set   <std::string>  states_names = get_old_states_names_with_default_name();

        for( std::set   <std::string>::const_iterator  state_name_it = states_names.begin();
            state_name_it != states_names.end(); ++state_name_it)
        {
            real_states_names_[*state_name_it] = *state_name_it;
        }
    }
    //-----------------------------------------------------------------------------------
    void  set_accept_states_names(const std::set   <std::string>&  accept_states_names)
    {
        accept_states_names_ = accept_states_names;
    }
    //-----------------------------------------------------------------------------------
    void  to_minimize()
    {
        typedef std::map   <std::pair  <std::string,         std::string>,  bool        >  T_states_pair_are_not_eq;
        T_states_pair_are_not_eq  states_pair_are_not_eq;
        std::set   <std::string>  states_names = get_old_states_names_with_default_name();
        for( std::set   <std::string>::const_iterator  L_state_name_it = states_names.begin();
            L_state_name_it != states_names.end(); ++L_state_name_it) {
            for( std::set   <std::string>::const_iterator  R_state_name_it = L_state_name_it;
                R_state_name_it != states_names.end(); ++R_state_name_it) {
                states_pair_are_not_eq[std::make_pair(*L_state_name_it, *R_state_name_it)]
                        =    accept_states_names_.count(*L_state_name_it)
                             != accept_states_names_.count(*R_state_name_it);
            }
        }
        bool  repeat = false;
        do {
            repeat = false;
            for( T_states_pair_are_not_eq::iterator
                         st_pair_ar_not_eq_it  =   states_pair_are_not_eq.begin();
                 st_pair_ar_not_eq_it  !=  states_pair_are_not_eq.end();
                 ++st_pair_ar_not_eq_it ) {
                if( !st_pair_ar_not_eq_it->second )
                {
                    std::string  L = st_pair_ar_not_eq_it->first.first;
                    std::string  R = st_pair_ar_not_eq_it->first.second;

                    std::set   <char>  symbols = get_symbols();

                    for(std::set   <char>::const_iterator  symb_it = symbols.begin();
                        symb_it != symbols.end(); ++symb_it) {
                        std::string  new_L = rules_[std::make_pair(L, *symb_it)];
                        std::string  new_R = rules_[std::make_pair(R, *symb_it)];

                        if(new_L > new_R) {
                            std::swap(new_L, new_R);
                        }
                        if(states_pair_are_not_eq.find( std::make_pair(new_L, new_R) )->second)
                        {
                            st_pair_ar_not_eq_it->second = true;
                            repeat = true;
                            break;
                        }
                    }
                }
                if (repeat)
                    break;
            }
        } while (repeat);
        for (T_states_pair_are_not_eq::iterator
                     st_pair_ar_not_eq_it  =   states_pair_are_not_eq.begin();
             st_pair_ar_not_eq_it  !=  states_pair_are_not_eq.end();
             ++st_pair_ar_not_eq_it ) {
            if(!st_pair_ar_not_eq_it->second)
            {
                std::string  L = st_pair_ar_not_eq_it->first.first;
                std::string  R = st_pair_ar_not_eq_it->first.second;
                if(L != R)
                {
                    for( T_real_states_names::iterator
                                 real_states_names_it  =  real_states_names_.begin();
                         real_states_names_it  != real_states_names_.end();
                         ++real_states_names_it )
                    {
                        if(real_states_names_it->second == R)
                        {
                            real_states_names_it->second = L;
                        }
                    }
                }
            }
        }
    }
    std::set   <char>  get_symbols() const
    {
        std::set   <char>  symbols;

        for(std::map   <std::pair  <std::string,  char>,   std::string>::const_iterator  rule_it = rules_.begin(); rule_it != rules_.end(); ++rule_it) {
            symbols.insert( rule_it->first.second );
        }

        return  symbols;
    }
    std::string  get_start_state_name() const {
        return  get_real_state_name( rules_with_first_start_state_.begin()->first.first );
    }
    std::set   <std::string>  get_states_names() const {
        std::set   <std::string>  states_names;
        for(std::map   <std::pair  <std::string,  char>,   std::string>::const_iterator  rule_it = rules_.begin();
            rule_it != rules_.end(); ++rule_it) {
            states_names.insert( get_real_state_name( rule_it->first.first ) );
            states_names.insert( get_real_state_name( rule_it->second      ) );
        }
        states_names.erase(DEFAULT_STATE_NAME_);
        return  states_names;
    }
    std::set   <std::string>  get_accept_states_names() const
    {
        std::set   <std::string>  real_accept_states_names;
        for( std::set   <std::string>::const_iterator accept_state_name_it  =   accept_states_names_.begin();
             accept_state_name_it  !=  accept_states_names_.end(); ++accept_state_name_it ) {
            real_accept_states_names
                    .insert( get_real_state_name( *accept_state_name_it ) );
        }
        return  real_accept_states_names;
    }
    std::map   <std::pair  <std::string,  char>,   std::string>  get_rules() const {
        std::map   <std::pair  <std::string,  char>,   std::string>  res_rules;
        for(std::map   <std::pair  <std::string,  char>,   std::string>::const_iterator  rule_it = rules_.begin();
            rule_it != rules_.end(); ++rule_it) {
            std::string  begin_state_name  = rule_it->first.first;
            char      symbol            = rule_it->first.second;
            std::string  end_state_name    = rule_it->second;

            std::string  real_begin_state_name
                    = get_real_state_name(begin_state_name);

            std::string  real_end_state_name
                    = get_real_state_name(end_state_name);

            if(    real_begin_state_name  != DEFAULT_STATE_NAME_
                   && real_end_state_name    != DEFAULT_STATE_NAME_ ) {
                res_rules.insert
                        (std::make_pair(std::make_pair(real_begin_state_name, symbol), real_end_state_name));
            }
        }
        return  res_rules;
    }
private:
    void  delete_unreachable()
    {
        std::set   <std::string>  res_states_names;
        res_states_names.insert(rules_with_first_start_state_.begin()->first.first);
        bool  repeate = false;
        do
        {
            repeate = false;
            for(std::map   <std::pair  <std::string,  char>,   std::string>::const_iterator  rule_it = rules_.begin();
                rule_it != rules_.end(); ++rule_it)
            {
                std::string  begin_name  = rule_it->first.first;
                std::string  end_name    = rule_it->second;

                if(     res_states_names.count(begin_name)
                        && !res_states_names.count(end_name)   )
                {
                    res_states_names.insert(end_name);
                    repeate = true;
                }
            }
        }while(repeate);
        for(std::map   <std::pair  <std::string,  char>,   std::string>::iterator  rule_it = rules_.begin();
            rule_it != rules_.end(); )
        {
            if( !res_states_names.count(rule_it->first.first) )
            {
                std::map   <std::pair  <std::string,  char>,   std::string>::const_iterator  rule_it_for_erase = rule_it;
                ++rule_it;
                rules_.erase(rule_it_for_erase);
            }
            else
            {
                ++rule_it;
            }
        }
    }
    std::set   <std::string>  get_old_states_names_with_default_name() const
    {
        std::set   <std::string>  res_states_names;
        for(std::map   <std::pair  <std::string,  char>,   std::string>::const_iterator  rule_it = rules_.begin();
            rule_it != rules_.end(); ++rule_it)
        {
            res_states_names.insert( rule_it->first.first );
            res_states_names.insert( rule_it->second      );
        }
        res_states_names.insert(DEFAULT_STATE_NAME_);
        return  res_states_names;
    }
    std::string  get_real_state_name(const std::string&  state_name) const
    {
        return  real_states_names_.find(state_name)->second;
    }
};
void  input_rules_and_rules_with_first_start_state( std::map   <std::pair  <std::string,  char>,   std::string>&  rules, std::map   <std::pair  <std::string,  char>,   std::string>&  rules_with_first_start_state,std::string& path)
{
    std::ifstream input(path);
    int num = 0, s = 0;
    int  rules_total = 0;
    input >> rules_total;
    for(int  i = 0; i < rules_total; ++i) {
        std::string  state_begin_name;
        input >> state_begin_name;
        char  symbol = 0;
        input >> symbol;
        std::string  state_end_name;
        input >> state_end_name;
        std::pair  <std::string,  char>          rule_head  = std::make_pair( state_begin_name,  symbol         );
        std::map   <std::pair  <std::string,  char>,   std::string>::value_type  rule       = std::make_pair( rule_head,         state_end_name );
        rules.insert(rule);
        if(i == 0) {
            rules_with_first_start_state.insert(rule);
        }
    }
}


void  accept_states_names_input(
        const std::set<std::string> &states_names, std::set<std::string> &accept_states_names, std::string &path) {
    std::ifstream input(path);
    int num = 0;
    std::string s;
    input >> num;
    for (int i = 0; i < num * 3; ++i) {
        input >> s;
    }
    for(int i = 0;;) {
        std::string   accept_state_name;
        input >> accept_state_name;
        if (accept_state_name == "#")
            break;
            accept_states_names.insert(accept_state_name);
    }
}


std::vector<vector<string>>  get_table(const Automata &fsm) {
    std::vector<vector<string>> res(4);
    res[0].push_back(fsm.get_start_state_name());

    std::set   <std::string>  states_names = fsm.get_states_names();

    for (const auto& e: states_names)
        res[1].push_back(e);

    std::set   <std::string>  accept_states_names = fsm.get_accept_states_names();
    for (const auto& e: accept_states_names)
        res[2].push_back(e);

    std::set   <char>  symbols = fsm.get_symbols();
    for (const auto& e: symbols)
        res[3].push_back("" + string(1,e) + "");

    std::map   <std::pair  <std::string,  char>,   std::string>  rules = fsm.get_rules();

    for(std::map   <std::pair  <std::string,  char>,   std::string>::const_iterator  rule_it = rules.begin();
        rule_it != rules.end(); ++rule_it)
    {
        res.push_back({});
        res[res.size() - 1].push_back(rule_it->first.first);
        res[res.size() - 1].push_back(string(1,rule_it->first.second));
        res[res.size() - 1].push_back(rule_it->second);
    }
    return res;
}

vector<vector<string>> get_Mart(vector<vector<string>>& new_table, bool f) {
    vector<vector<string>> transitions(new_table[1].size(), vector<string>(new_table[3].size() + 1, "_"));

    map<string, int> rows;
    for (const auto &e: new_table[1]) {
        rows.insert({e, rows.size()});
        if (f)
            min_rows.push_back(e);
    }
    map<string, int> col;
    for (const auto &e: new_table[3]) {
        col.insert({e, col.size()});
        if (f)
            min_col.push_back(e);
    }
    col.insert({"&", col.size()});
    if (f)
        min_col.push_back("&");
    for (const auto &e: new_table[2])
        transitions[rows[e]][col["&"]] = "+";

    for (int i = 4; i < new_table.size(); ++i) {
        transitions[rows[new_table[i][0]]][col[new_table[i][1]]] = new_table[i][2];
    }
    return transitions;
}

int  do_stuff()
{
    std::locale::global( std::locale("") );

    std::map   <std::pair  <std::string,  char>,   std::string>  rules;
    std::map   <std::pair  <std::string,  char>,   std::string>  rules_with_first_start_state;

    input_rules_and_rules_with_first_start_state
            (
                    rules,
                    rules_with_first_start_state,
                    path
            );

    Automata           fsm(rules, rules_with_first_start_state);
    std::set   <std::string>  states_names = fsm.get_states_names();
    std::set   <std::string>  accept_states_names;
    accept_states_names_input(states_names, accept_states_names, path);
    fsm.set_accept_states_names(accept_states_names);
    table_before_Aho = get_table(fsm);
    for (const auto& e: table_before_Aho[1]) {
        aho_rows.push_back(e);
    }
    for (const auto& e: table_before_Aho[3]) {
        aho_col.push_back(e);
    }
    aho_col.push_back("&");
    min_table_before_Aho = get_Mart(table_before_Aho, false);


    {
        cout << "Автомат, построенный по регулярному выражению\n";
        cout << "  ";

        for (const auto &e: aho_col)
            cout << e << " ";
        cout << endl;
        int iq2 = 0;
        for (const auto &e: min_table_before_Aho) {
            cout << aho_rows[iq2] << " ";
            for (const auto &c: e) {
                cout << c << " ";
            }
            cout << endl;
            iq2++;
        }
    }

    fsm.to_minimize();
    table = get_table(fsm);
}
void change_s(std::string& s, int pos) {
    if (pos == 0) {
        s = s.substr(1, s.length() - 1);
        return;
    }
    if (pos == s.length() - 1) {
        s = s.substr(0, s.length() - 1);
        return;
    }
    int l = pos;
    int r = pos;
    int lc = 0;
    int rc = 0;
    string s1;
    string s2;
    string s3;
    string s4;
   if (s[pos - 1] == ')' && s[pos + 1] == '(') {
        --l;
        while (!(s[l] == '(' && lc == 1)) {
            if (s[l] == '(')
                --lc;
            if (s[l] == ')')
                ++lc;
            --l;
        }

        ++r;
        while (!(s[r] == ')' && rc == 1)) {
            if (s[r] == ')')
                --rc;
            if (s[r] == '(')
                ++rc;
            ++r;
        }
        s1 = s.substr(0, l);
        s4 = s.substr(r + 1, s.length() - r - 1);
        s2 = s.substr(l, pos - 1 - l + 1);
        s3 = s.substr(pos + 1, r - pos - 1 + 1);
        s = s1 + s2 + "(" + s3 + s2 + ")*" + s4;
        return;
    }
    if (s[pos - 1] != ')' && s[pos + 1] == '(') {
        l = pos - 1;
        ++r;
        while (!(s[r] == ')' && rc == 1)) {
            if (s[r] == ')')
                --rc;
            if (s[r] == '(')
                ++rc;
            ++r;
        }
        s1 = s.substr(0, l);
        s4 = s.substr(r + 1, s.length() - r - 1);

        s2 = s.substr(l, pos - 1 - l + 1);

        s3 = s.substr(pos + 1, r - pos - 1 + 1);

        s = s1 + s2 + "(" + s3 + s2 + ")*" + s4;
        return;
    }if (s[pos - 1] == ')' && s[pos + 1] != '(') {
        --l;
        while (!(s[l] == '(' && lc == 1)) {
            if (s[l] == '(')
                --lc;
            if (s[l] == ')')
                ++lc;
            --l;
        }
        r = pos + 1;
        s1 = s.substr(0, l);
        s4 = s.substr(r + 1, s.length() - r - 1);
        s2 = s.substr(l, pos - 1 - l + 1);
        s3 = s.substr(pos + 1, r - pos - 1 + 1);
        s = s1 + s2 + "(" + s3 + s2 + ")*" + s4;
        return;
    }
    if (s[pos - 1] != ')' && s[pos + 1] != '(') {
        l = pos - 1;
        r = pos + 1;
        s1 = s.substr(0, l);
        s4 = s.substr(r + 1, s.length() - r - 1);
        s2 = s.substr(l, pos - 1 - l + 1);
        s3 = s.substr(pos + 1, r - pos - 1 + 1);

        s = s1 + s2 + "(" + s3 + s2 + ")*" + s4;
        return;
    }
}
void change(std::string& s) {
    string st = "";
    for (int i = 0; i < s.length(); ++i) {
        if (s[i] == ',')
            continue;
        if (s[i] == ';') {
            st += "|";
            continue;
        }
        st += s[i];
    }
    s = st;
    while (true) {
        bool flag = false;
        for (int i = 0; i < s.length(); ++i) {
            if (s[i] == '#') {
                change_s(s, i);
                flag = true;
                break;
            }
        }
        if (!flag)
            break;
    }
}



pair<string, string> check_table() {

}
int join_sets(vector<int>& deleted) {
    for (int i = 0; i < min_table_before_Mart.size(); ++i) {
        for (int j = 0; j < min_table_before_Mart[0].size(); ++j) {
            bool flag = true;
            if (i == j)
                continue;
            if (deleted[i] != i || deleted[j] != j)
                continue;
            for (int k = 0; k < min_table_before_Mart[0].size(); ++k) {
                if ((min_table_before_Mart[i][k] == "_" && min_table_before_Mart[j][k] == "_")
                    || (min_table_before_Mart[i][k] == "_" && min_table_before_Mart[j][k] != "_")
                    || (min_table_before_Mart[i][k] != "_" && min_table_before_Mart[j][k] == "_")
                    || (min_table_before_Mart[i][k] == min_table_before_Mart[j][k] && min_table_before_Mart[i][k] != "_")
                        )
                {} else {
                    flag = false;
                    break;
                }
            }
            if (!flag)
                continue;
            int min_a = std::min(i, j);
            int max_a = std::max(i, j);
            deleted[max_a] = min_a;

            for (int i1 = 0; i1 < min_table_before_Mart[min_a].size(); ++i1) {
                if (min_table_before_Mart[min_a][i1] == "_")
                    min_table_before_Mart[min_a][i1] = min_table_before_Mart[max_a][i1];
            }

            for (int p1 = 0; p1 < min_table_before_Mart.size(); ++p1) {
                for (int p2 = 0; p2 < min_table_before_Mart[0].size(); ++p2) {
                    if (min_table_before_Mart[p1][p2] == min_rows[max_a])
                        min_table_before_Mart[p1][p2] = min_rows[min_a];
                }

            }
            return 0;
        }
    }
    return 1;
}
set<int> min_Mart() {
    set<int> new_deleted_states;
    for (int i = 0; i < min_rows.size(); ++i) {
        min_masks.insert({min_rows[i], i});
    }
    vector<int> masks(min_table_before_Mart.size());
    for (int i = 0; i < masks.size(); ++i)
        masks[i] = i;
    //cout << "\n\nDoing final steps!!!!\n\n";
    while (true) {
        int res = join_sets(masks);

        if (res == 1)
            break;
    }
    for (int i = 0; i < masks.size(); ++i) {
        if (masks[i] != i)
            new_deleted_states.insert(i);
    }
    deleted_states = new_deleted_states;

    return new_deleted_states;
}
/*
void min_Mart2() {
    vector<int> colors(table[1].size(), -1);
    for (int i = 0; i < colors.size(); ++i)
        colors[i] = i;
    int pointer_color = 0;
    vector<set<int>> classes(table[1].size());
    for (int i = 0; i < classes.size(); ++i)
        classes[i].insert(i);
    for (int i = 0; i < min_table.size(); ++i) {
        for (int j = 0; j < min_table.size(); ++j) {
            bool flag = true;
            if (i == j)
                continue;
            for (int k = 0; k < min_table[0].size(); ++k) {
                if ((min_table[i][k] == "_" && min_table[j][k] == "_")
                     || (min_table[i][k] == "_" && min_table[j][k] != "_")
                     || (min_table[i][k] != "_" && min_table[j][k] == "_")
                     || (min_table[i][k] == min_table[j][k] && min_table[i][k] != "_")
                )
                {} else {
                    flag = false;
                    break;
                }
            }
            if (!flag)
                continue;
            int min_a = std::min(i, j);
            int max_a = std::max(i, j);
            if (colors[min_a] == colors[max_a])
                continue;
            for (const auto& e: classes[max_a]) {
                colors[e] = min_a;
                classes[min_a].insert(e);
            }

        }
    }
    for (const auto& e: colors)
        cout << e << " ";
    cout << endl;
    for (const auto& e: classes) {
        cout << "class No ";
        for (const auto& c: e)
            cout << c << " ";
        cout << endl;
    }
    cout << endl;

}*/
int main() {
    //ifstream cin("data.in");
    ofstream fcout("DFA.txt");

    RE_to_Automata_converter converter;

    string large_regex = "((((a,fd)|(a#d))#q)#(d#w))#((qq#v)#(a#b))";
    string regex1 = "0*(11)*1(00)*01*";
    string regex2 = "ab((bc)|da)*aa|d";
    string regex3 = "0*1*10*0";
    string regex = "(01(1)*)((01(1)*1))*1";
    //cin >> regex;
    change(regex);
    fcout << converter.convert(regex);
    fcout.close();
    ifstream f("DFA.txt");
    if (f.is_open()) {
        std::string s;
        while (getline(f, s))
        {
            //std::cout << s << std::endl;
        }
    }
    do_stuff();
    string r1 = "W,E;LL(a,lo(ABRA),#(CADABRA)ha)#fHI";
    string r2 = "((a#q)#(d#w))#((qq#v)#(a#b))";
    string r3 = "a#b";
    string r4 = "ab*(ab|(bc*))vdb*a";
    string r = "((((a,fd)|(a#d))#q)#(d#w))#((qq#v)#(a#b))";
    change(r);

    min_table_before_Mart = get_Mart(table, true);

    cout << "Минимизированный по Ахо автомат" << endl;
    cout << "  ";
    int ip = 0;
    for (const auto& e: min_col)
        cout << e << " ";
    cout << endl;
    int iq = 0;
    for (const auto& e: min_table_before_Mart) {
        cout << min_rows[iq++] << " ";
        for (const auto& c: e) {
            cout << c << " ";
        }
        cout << endl;
    }
    set<int> deleted_states = min_Mart();
/*
    cout << "\nMINIM 2" << endl;
    cout << "  ";
    {
        for (const auto &e: min_col)
            cout << e << " ";
        cout << endl;
        int iq1 = 0;
        for (const auto &e: min_table_before_Mart) {
            cout << min_rows[iq1++] << " ";
            for (const auto &c: e) {
                cout << c << " ";
            }
            cout << endl;
        }
    }*/
    {
        cout << "Минимизированный по Ахо-Мартыненко автомат\n";
        cout << "  ";
        for (const auto &e: min_col)
            cout << e << " ";
        cout << endl;
        int iq2 = 0;
        for (const auto &e: min_table_before_Mart) {
            if (deleted_states.find(iq2) == deleted_states.end()) {
                cout << min_rows[iq2] << " ";
                for (const auto &c: e) {
                    cout << c << " ";
                }
                cout << endl;
            }
            iq2++;
        }
    }
    return 0;
}