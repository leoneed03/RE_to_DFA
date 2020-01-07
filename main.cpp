//#include <iostream>
//#include <fstream>
#include <cstring>
#include "regex_to_dfa.h"
using namespace std;

/*int main() {
    //ifstream cin("data.in");
    ofstream fcout("DFA.txt");

    RegexToDFAConverter converter;

    string regex;
    cin >> regex;
    fcout << converter.convert(regex);
    fcout.close();
    ifstream f("DFA.txt");
    if (f.is_open()) {
        std::string s;
        while (getline(f, s))
        {
            std::cout << s << std::endl;
        }
    }
    return 0;
}
*/



#include <algorithm>
#include <iostream>
#include <fstream>
#include <map>
#include <string>
#include <set>
#include <utility>

///Users/leonardbee/CLionProjects/old_version_min/DFA.txt

/////////////////////////////////////////////////////////////////////////////////////////
typedef std::string                               T_str;
typedef T_str                                     T_state_name;
typedef char                                      T_symbol;
typedef std::set   <T_symbol>                     T_symbols;
typedef std::pair  <T_state_name,  T_symbol>      T_rule_head;
typedef std::map   <T_rule_head,   T_state_name>  T_rules;
typedef std::set   <T_state_name>                 T_states_names;
/////////////////////////////////////////////////////////////////////////////////////////
std::string path = "DFA.txt";

class  T_FSM
{
    typedef std::map<T_state_name, T_state_name>  T_real_states_names;
    //-----------------------------------------------------------------------------------
    T_rules              rules_;
    T_rules              rules_with_first_start_state_;
    const T_state_name   DEFAULT_STATE_NAME_;
    T_real_states_names  real_states_names_;
    T_states_names       accept_states_names_;
    //-----------------------------------------------------------------------------------
public:
    T_FSM
            (
                    const T_rules&  rules,
                    const T_rules&  rules_with_first_start_state
            )
            : rules_                         (rules),
              rules_with_first_start_state_  (rules_with_first_start_state),
              DEFAULT_STATE_NAME_            ()
    {
        remove_unachievable_rules();
        T_states_names  states_names = get_old_states_names_with_default_name();

        for(T_states_names::const_iterator  state_name_it = states_names.begin();
            state_name_it != states_names.end(); ++state_name_it)
        {
            real_states_names_[*state_name_it] = *state_name_it;
        }
    }
    //-----------------------------------------------------------------------------------
    void  set_accept_states_names(const T_states_names&  accept_states_names)
    {
        accept_states_names_ = accept_states_names;
    }
    //-----------------------------------------------------------------------------------
    void  to_minimize()
    {
        //Составляем всевозможные пары состояний автомата.
        typedef std::pair  <T_state_name,         T_state_name>  T_states_names_pair;
        typedef std::map   <T_states_names_pair,  bool        >  T_states_pair_are_not_eq;
        T_states_pair_are_not_eq  states_pair_are_not_eq;
        //Заполняем  states_pair_are_not_eq.
        T_states_names  states_names = get_old_states_names_with_default_name();
        for(T_states_names::const_iterator  L_state_name_it = states_names.begin();
            L_state_name_it != states_names.end(); ++L_state_name_it)
        {
            for(T_states_names::const_iterator  R_state_name_it = L_state_name_it;
                R_state_name_it != states_names.end(); ++R_state_name_it)
            {
                states_pair_are_not_eq[std::make_pair(*L_state_name_it, *R_state_name_it)]
                        =    accept_states_names_.count(*L_state_name_it)
                             != accept_states_names_.count(*R_state_name_it);
            }
        }

        //Пробегаемся по states_pair_are_not_eq. Если находим пару со значением false,
        //т.е. с подозрением на эквивалентность, то пробегаемся по всем символам
        //и если находим такой символ, по которому эта пара переходит в отмеченную,
        //то отметить эту пару и повторить весь цикл.
        bool  repeat = false;
        do
        {
            repeat = false;
            for( T_states_pair_are_not_eq::iterator
                         st_pair_ar_not_eq_it  =   states_pair_are_not_eq.begin();
                 st_pair_ar_not_eq_it  !=  states_pair_are_not_eq.end();
                 ++st_pair_ar_not_eq_it )
            {
                //Если подозрение на эквивалентность:
                if( !st_pair_ar_not_eq_it->second )
                {
                    T_state_name  L = st_pair_ar_not_eq_it->first.first;
                    T_state_name  R = st_pair_ar_not_eq_it->first.second;

                    T_symbols  symbols = get_symbols();

                    for(T_symbols::const_iterator  symb_it = symbols.begin();
                        symb_it != symbols.end(); ++symb_it)
                    {
                        //Если правила с головой, указанной в квадратных скобках,
                        //не существует, то оно создается с пустым конечным состонием,
                        //т.е. равным дефолтному DEFAULT_STATE_NAME_.
                        T_state_name  new_L = rules_[std::make_pair(L, *symb_it)];
                        T_state_name  new_R = rules_[std::make_pair(R, *symb_it)];

                        if(new_L > new_R)
                        {
                            std::swap(new_L, new_R);
                        }

                        //Если существует отмеченная пара состояний, в которые можно перейти
                        //по этому символу, то:
                        if(states_pair_are_not_eq.find( std::make_pair(new_L, new_R) )->second)
                        {
                            st_pair_ar_not_eq_it->second = true;
                            repeat = true;
                            break;
                        }//if
                    }//for
                }//if
                if(repeat) break;
            }//for
        }while(repeat);

        //Находим в states_pair_are_not_eq классы эквивалентности состояний.

        //Выявляем классы эквивалентности на основе states_pair_are_not_eq.
        for( T_states_pair_are_not_eq::iterator
                     st_pair_ar_not_eq_it  =   states_pair_are_not_eq.begin();
             st_pair_ar_not_eq_it  !=  states_pair_are_not_eq.end();
             ++st_pair_ar_not_eq_it )
        {
            //Если состояния эквивалентны, то:
            if(!st_pair_ar_not_eq_it->second)
            {
                T_state_name  L = st_pair_ar_not_eq_it->first.first;
                T_state_name  R = st_pair_ar_not_eq_it->first.second;
                if(L != R)
                {
                    //Пробегаемся по real_states_names_ и все имена классов R заменяем на L.
                    for( T_real_states_names::iterator
                                 real_states_names_it  =  real_states_names_.begin();
                         real_states_names_it  != real_states_names_.end();
                         ++real_states_names_it )
                    {
                        if(real_states_names_it->second == R)
                        {
                            real_states_names_it->second = L;
                        }
                    }//for
                }//if
            }//if
        }//for
    }
    //-----------------------------------------------------------------------------------
    T_symbols  get_symbols() const
    {
        T_symbols  symbols;

        for(T_rules::const_iterator  rule_it = rules_.begin();
            rule_it != rules_.end(); ++rule_it)
        {
            symbols.insert( rule_it->first.second );
        }

        return  symbols;
    }
    //-----------------------------------------------------------------------------------
    T_state_name  get_start_state_name() const
    {
        return  get_real_state_name( rules_with_first_start_state_.begin()->first.first );
    }
    //-----------------------------------------------------------------------------------
    T_states_names  get_states_names() const
    {
        T_states_names  states_names;

        for(T_rules::const_iterator  rule_it = rules_.begin();
            rule_it != rules_.end(); ++rule_it)
        {
            states_names.insert( get_real_state_name( rule_it->first.first ) );
            states_names.insert( get_real_state_name( rule_it->second      ) );
        }
        states_names.erase(DEFAULT_STATE_NAME_);
        return  states_names;
    }
    //-----------------------------------------------------------------------------------
    T_states_names  get_accept_states_names() const
    {
        T_states_names  real_accept_states_names;

        for( T_states_names::const_iterator
                     accept_state_name_it  =   accept_states_names_.begin();
             accept_state_name_it  !=  accept_states_names_.end();
             ++accept_state_name_it )
        {
            real_accept_states_names
                    .insert( get_real_state_name( *accept_state_name_it ) );
        }
        return  real_accept_states_names;
    }
    //-----------------------------------------------------------------------------------
    T_rules  get_rules() const
    {
        T_rules  res_rules;
        for(T_rules::const_iterator  rule_it = rules_.begin();
            rule_it != rules_.end(); ++rule_it)
        {
            T_state_name  begin_state_name  = rule_it->first.first;
            T_symbol      symbol            = rule_it->first.second;
            T_state_name  end_state_name    = rule_it->second;

            T_state_name  real_begin_state_name
                    = get_real_state_name(begin_state_name);

            T_state_name  real_end_state_name
                    = get_real_state_name(end_state_name);

            if(    real_begin_state_name  != DEFAULT_STATE_NAME_
                   && real_end_state_name    != DEFAULT_STATE_NAME_ )
            {
                res_rules.insert
                        (
                                std::make_pair
                                        (
                                                std::make_pair
                                                        (
                                                                real_begin_state_name,
                                                                symbol
                                                        ),
                                                real_end_state_name
                                        )
                        );
            }//if
        }//for
        return  res_rules;
    }
    //-----------------------------------------------------------------------------------
private:
    //-----------------------------------------------------------------------------------
    void  remove_unachievable_rules()
    {
        T_states_names  res_states_names;

        //Вставляем в res_states_names имя стартового состояния.
        res_states_names.insert(rules_with_first_start_state_.begin()->first.first);

        //В цикле пробегаемся по всем правилам, и, если у какого-то правила
        //начальное состояние есть в res_states_names, а конечное отстутствует,
        //то поместить его туда и повторить цикл.
        bool  repeate = false;
        do
        {
            repeate = false;
            for(T_rules::const_iterator  rule_it = rules_.begin();
                rule_it != rules_.end(); ++rule_it)
            {
                T_state_name  begin_name  = rule_it->first.first;
                T_state_name  end_name    = rule_it->second;

                if(     res_states_names.count(begin_name)
                        && !res_states_names.count(end_name)   )
                {
                    res_states_names.insert(end_name);
                    repeate = true;
                }
            }
        }while(repeate);

        //Утверждение: имена всех достижимых состояний содержатся в res_states_names.
        //Удаляем из rules_ все правила, имен начальных состояний которых нет
        //в res_states_names.
        for(T_rules::iterator  rule_it = rules_.begin();
            rule_it != rules_.end(); )
        {
            if( !res_states_names.count(rule_it->first.first) )
            {
                T_rules::const_iterator  rule_it_for_erase = rule_it;
                ++rule_it;
                rules_.erase(rule_it_for_erase);
            }
            else
            {
                ++rule_it;
            }
        }//for
    }
    //-----------------------------------------------------------------------------------
    T_states_names  get_old_states_names_with_default_name() const
    {
        T_states_names  res_states_names;

        for(T_rules::const_iterator  rule_it = rules_.begin();
            rule_it != rules_.end(); ++rule_it)
        {
            res_states_names.insert( rule_it->first.first );
            res_states_names.insert( rule_it->second      );
        }
        res_states_names.insert(DEFAULT_STATE_NAME_);
        return  res_states_names;
    }
    //-----------------------------------------------------------------------------------
    T_state_name  get_real_state_name(const T_state_name&  state_name) const
    {
        return  real_states_names_.find(state_name)->second;
    }
    //-----------------------------------------------------------------------------------
};
/////////////////////////////////////////////////////////////////////////////////////////
void  input_rules_and_rules_with_first_start_state
        (
                T_rules&  rules,
                T_rules&  rules_with_first_start_state,
                std::string& path
        )
{
    std::ifstream input(path);
    int num = 0, s = 0;
    std::cout << "Введите количество правил автомата: ";
    int  rules_total = 0;
    input >> rules_total;

    std::cout << "Введите "
              << rules_total
              << " правил перехода автомата. "
              << std::endl
              << "Первым введите правило перехода из стартового состояния:"
              << std::endl;

    for(int  i = 0; i < rules_total; ++i)
    {
        std::cout << std::endl
                  << "#"
                  << i + 1;
        if(i == 0)
        {
            std::cout << " (правило перехода из стартового состояния)";
        }

        std::cout << ":"
                  << std::endl
                  << '\t'
                  << (i == 0 ? "стартовое состояние:" : "исходное состояние:")
                  << '\t'
                  << '\t';
        T_state_name  state_begin_name;
        input >> state_begin_name;

        std::cout << '\t'
                  << "символ:"
                  << '\t'
                  << '\t'
                  << '\t'
                  << '\t';
        T_symbol  symbol = 0;
        input >> symbol;

        std::cout << '\t'
                  << "результирующее состояние:"
                  << '\t';
        T_state_name  state_end_name;
        input >> state_end_name;
        std::cout << std::endl
                  << std::endl;

        T_rule_head          rule_head  = std::make_pair( state_begin_name,  symbol         );
        T_rules::value_type  rule       = std::make_pair( rule_head,         state_end_name );

        rules.insert(rule);
        if(i == 0)
        {
            rules_with_first_start_state.insert(rule);
        }
    }//for
}
/////////////////////////////////////////////////////////////////////////////////////////
void  input_accept_states_names(
        const T_states_names&  states_names, T_states_names&        accept_states_names, std::string& path)
{
    std::ifstream input(path);
    int num = 0;
    std::string s;
    input >> num;
    for (int i = 0; i < num * 3; ++i) {
        input >> s;
        std::cout << s << "\n";
    }
    std::cout << std::endl
              << std::endl
              << "Введите допускающие состояния автомата из нижеследующего списка"
              << std::endl
              << "(для завершения ввода введите пустую строку):"
              << std::endl;

    std::copy
            (
                    states_names.begin(),
                    states_names.end(),
                    std::ostream_iterator<T_state_name>(std::cout, "\t")
            );

    std::cout << std::endl;

    bool  name_is_good  = true;
    for(int i = 0;;)
    {
        if(name_is_good)
        {
            std::cout << std::endl
                      << "#"
                      << ++i
                      << ": "
                      << std::endl;
        }

        T_state_name   accept_state_name;
        input >> accept_state_name;
        std::cout << "WHY? " << accept_state_name << std::endl;
        if (accept_state_name == "#")
            break;

        /*
        if( accept_state_name.empty() ) break;

        name_is_good =     states_names         .count(accept_state_name)
                           && !accept_states_names  .count(accept_state_name);
*/

        if(name_is_good)
        {
            accept_states_names.insert(accept_state_name);
            //if( accept_states_names.size() == states_names.size() ) break;
        }
    }
}
/////////////////////////////////////////////////////////////////////////////////////////
void  print_FSM(const T_FSM&  fsm)
{
    std::cout << '\t'
              << "стартовое состояние:"
              << '\t'
              << fsm.get_start_state_name()
              << std::endl;

    std::cout << '\t'
              << "состояния автомата:"
              << '\t';
    T_states_names  states_names = fsm.get_states_names();
    std::copy
            (
                    states_names.begin(),
                    states_names.end(),
                    std::ostream_iterator<T_states_names::value_type>(std::cout, "\t")
            );

    std::cout << std::endl
              << '\t'
              << "допускающие состояния автомата:"
              << '\t';
    T_states_names  accept_states_names = fsm.get_accept_states_names();
    std::copy
            (
                    accept_states_names.begin(),
                    accept_states_names.end(),
                    std::ostream_iterator<T_states_names::value_type>(std::cout, "\t")
            );

    std::cout << std::endl
              << '\t'
              << "символы входной строки:"
              << '\t';

    T_symbols  symbols = fsm.get_symbols();
    std::copy
            (
                    symbols.begin(),
                    symbols.end(),
                    std::ostream_iterator<T_symbols::value_type>(std::cout, "\t")
            );

    std::cout << std::endl
              << '\t'
              << "правила перехода:"
              << std::endl;

    T_rules  rules = fsm.get_rules();

    for(T_rules::const_iterator  rule_it = rules.begin();
        rule_it != rules.end(); ++rule_it)
    {
        std::cout << '\t'
                  << '\t'
                  << rule_it->first.first
                  << '\t'
                  << rule_it->first.second
                  << '\t'
                  << rule_it->second
                  << std::endl;
    }
    std::cout << std::endl;
}
/////////////////////////////////////////////////////////////////////////////////////////
int  do_stuff()
{
    std::locale::global( std::locale("") );

    T_rules  rules;
    T_rules  rules_with_first_start_state;

    input_rules_and_rules_with_first_start_state
            (
                    rules,
                    rules_with_first_start_state,
                    path
            );

    T_FSM           fsm(rules, rules_with_first_start_state);
    T_states_names  states_names = fsm.get_states_names();
    T_states_names  accept_states_names;
    input_accept_states_names(states_names, accept_states_names, path);
    fsm.set_accept_states_names(accept_states_names);

    std::cout << std::endl
              << std::endl
              << std::endl
              << std::endl
              << "Исходный автомат с удаленными недостижимыми состояниями:"
              << std::endl;
    print_FSM(fsm);
    fsm.to_minimize();

    std::cout << std::endl
              << std::endl
              << "Минимизированный автомат, эквивалентный исходному:"
              << std::endl;
    print_FSM(fsm);
    std::cout << std::endl;
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
    cout << "starting" << endl;
    cout << s[pos-1] << s[pos] << s[pos+1] << endl;
    if (s[pos - 1] == ')' && s[pos + 1] == '(') {
        --l;
        while (!(s[l] == '(' && lc == 1)) {
            cout << s[l] <<  " " << lc << endl;
            if (s[l] == '(')
                --lc;
            if (s[l] == ')')
                ++lc;
            --l;
        }

        ++r;
        while (!(s[r] == ')' && rc == 1)) {
            cout << s[r] <<  " " << rc << endl;
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
            cout << s[l] <<  " " << lc << endl;
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
int main() {
    //ifstream cin("data.in");
    ofstream fcout("DFA.txt");

    RegexToDFAConverter converter;

    string regex;
    regex = "ab*(ab|(bc*))vdb*a";
    //cin >> regex;
    //////////change(regex);
    fcout << converter.convert(regex);
    fcout.close();
    ifstream f("DFA.txt");
    if (f.is_open()) {
        std::string s;
        while (getline(f, s))
        {
            std::cout << s << std::endl;
        }
    }
    do_stuff();
    string r1 = "W,E;LL(a,lo(ABRA),#(CADABRA)ha)#fHI";
    string r = "(a#d)#(v#a)";
    change(r);
    cout << r;
    return 0;
}