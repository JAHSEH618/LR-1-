//
//  main.cpp
//  LR(1)
//
//  Created by Friedhelm Liu on 2021/6/1.
//

#include <iostream>
#include <string>
#include <map>
#include <vector>
#include <stack>
#include <set>
#include <cstring>
#include <queue>

using namespace std;

map <char, int> getnum;
char getChar[100];
vector <string> proce;               //产生式
int table[30][30];                   //预测分析表
int tb_s_r[30][30];                  //移入or归约
int num = 0;
int numvt = 0;                       //终结符集合

void readin()
{
    memset(table, -1, sizeof(table));
    getnum['#'] = 0;
    getChar[0] = '#';
    cout << "Please input all the terminals:" << endl;
    char x;
    do
    {
        cin >> x;
        getnum[x] = ++num;
        getChar[num] = x;
    }while(cin.peek() != '\n');
    numvt = ++num;
    getnum['@'] = numvt;              //∊
    getChar[num] = ('@');
    
    cout <<"Please input all the nonterminals:" << endl;
    do
    {
        cin >> x;
        getnum[x] = ++num;
        getChar[num] = x;
    }while(cin.peek() != '\n');
    
    cout << "Enter all the productions(replace ∊ with '@', end with 'end'):" << endl;
    string prod;
    while(cin >> prod && prod != "end")
    {
        string ss;
        ss += prod[0];
        for(int i = 3; i < prod.size(); i++)
        {
            if(prod[i] == '|')
            {
                proce.push_back(ss);
                ss.clear();
                ss += prod[0];
            }
            else
            {
                ss += prod[i];
            }
        }
        proce.push_back(ss);
    }
}

struct project
{
    int nump;                 //产生式编号
    int id;                   //.的位置
    string fst;               //集合
};

string getp[100];             //获得终结符在左边的产生式集合

void getpp()
{
    for(int i = 0; i < proce.size(); i++)
    {
        int temp = getnum[proce[i][0]];
        getp[temp] += char('0' + i);
    }
}

string first[100];        //每个符号的first set
bool gotfirst[100];       //是否完成first set获取

void dfsgetfirst(int nv, int nump)          //当前符号和对应产生式的编号
{
    int temp = getnum[proce[nump][1]];      //产生式推出第一个字符
    gotfirst[nump] = 1;                     //tag
    if(temp <= numvt)
    {
        first[nv] += char('0' + temp);      //是终结符
    }
    else
    {
        for(int i = 0; i < getp[temp].size(); i++)    //所有temp可以退出来的符号的产生式
        {
            if(proce[nump][0] == proce[nump][1])      //左递归不影响
                continue;
            dfsgetfirst(temp, getp[temp][i] - '0');
        }
        first[nv] += first[temp];                     //回溯保存
    }
}

void getfirst()
{
    for(int i = 1; i <= numvt; i++)
    {
        first[i] = char('0' + i);                     //终结符first set是他本身
    }
    for(int i = 0; i < proce.size(); i++)
    {
        if(proce[i][0] == proce[i][1])                //左递归不影响
            continue;
        if(gotfirst[i])
            continue;
        int temp = getnum[proce[i][0]];
        dfsgetfirst(temp, i);
    }
}

vector <vector<project>> v;
int e[100][3];
int head[100];
int nume = 0;

void addegde(int from, int to, int w)
{
    e[nume][0] = to;
    e[nume][1] = head[from];
    head[from] = nume;
    e[nume++][2] = w;
}

void clear()                                         //初始化
{
    for(int i = 0; i < 100; i++)
        head[i] = -1;
    for(int i = 0; i < 30; i++)
    {
        for(int j = 0; j < 30; j++)
            tb_s_r[i][j] = table[i][j] = -1;
    }
    nume = 0;
}

inline bool projeq(project a, project b)
{
    if(a.fst == b.fst && a.id == b.id && a.nump == b.nump)
        return 1;
    return 0;
}

bool isin(project a, vector<project> b)
{
    for(int i = 0; i < b.size(); i++)
    {
        if(projeq(a, b[i]))
            return 1;
    }
    return 0;
}

vector<project> combine(vector<project> a, vector<project> b)
{
    for(int i = 0; i < b.size(); i++)
    {
        if(isin(b[i], a))
            continue;
        else
            a.push_back(b[i]);
    }
    return a;
}

bool projseq(vector<project> a, vector<project> b)
{
    if(a.size() != b.size())
        return 0;
    for(int i = 0; i < a.size(); i++)
    {
        if(!isin(a[i], b))
            return 0;
    }
    return 1;
}

int projs_isin(vector<project> a, vector<vector<project>> b)
{
    for(int i = 0; i < b.size(); i++)
    {
        if(projseq(a, b[i]))
            return i;
    }
    return -1;
}

vector<project> get_closure(project t)
{
    vector<project> temp;
    temp.push_back(t);
    queue<project> q;
    q.push(t);
    while(!q.empty())
    {
        project cur = q.front();
        q.pop();
        if(cur.id == proce[cur.nump].size())
            continue;
        int tt = getnum[proce[cur.nump][cur.id]];
        if(tt <= numvt)
            continue;
        for(int i = 0; i < getp[tt].size(); i++)
        {
            project c;
            c.id = 1;
            c.nump = getp[tt][i] - '0';
            if(proce[cur.nump].size() - cur.id == 1)
                c.fst += cur.fst;
            else
            {
                int tttnum = getnum[proce[cur.nump][cur.id + 1]];
                c.fst += first[tttnum];
            }
            if(!isin(c, temp))
            {
                q.push(c);
                temp.push_back(c);
            }
        }
    }
    return temp;
}

void get_projsets()
{
    vector<project> temp;
    project t;
    t.nump = 0;
    t.id = 1;
    t.fst += '0';
    temp = get_closure(t);
    queue<vector<project>> q;
    q.push(temp);
    v.push_back(temp);
    while(!q.empty())
    {
        vector<project> cur = q.front();
        q.pop();
        for(int i = 1; i <= num; i++)
        {
            if(i == numvt)
                continue;
            vector<project> temp;
            for(int j = 0; j < cur.size(); j++)
            {
                if(cur[j].id == proce[cur[j].nump].size())
                    continue;
                int tt = getnum[proce[cur[j].nump][cur[j].id]];
                if(tt == i)
                {
                    project tempt;
                    tempt.fst = cur[j].fst;
                    tempt.id = cur[j].id + 1;
                    tempt.nump = cur[j].nump;
                    temp = combine(temp, get_closure(tempt));
                }
            }
            if(temp.size() == 0)
                continue;
            int numcur = projs_isin(cur, v);
            int tttnum = projs_isin(temp, v);
            if(tttnum == -1)
            {
                v.push_back(temp);
                q.push(temp);
                addegde(numcur, v.size()-1, i);
            }
            else
            {
                addegde(numcur, tttnum, i);
            }
        }
    }
}

void print_projsets()
{
    for(int i = 0; i < v.size(); i++)
    {
        cout << "Project sets " << i << ":" << endl;
        for(int j = 0; j < v[i].size(); j++)
        {
            cout << proce[v[i][j].nump] << " " << v[i][j].id << " " << v[i][j].fst << endl;
        }
        cout << endl;
    }
    for(int i = 0; i < v.size(); i++)
    {
        for(int j = head[i]; j != -1; j = e[j][1])
        {
            cout << "    " << getChar[e[j][2]] << endl;
            cout << i << "--->" << e[j][0] << endl;
        }
    }
}

bool get_table()
{
    for(int i = 0; i < v.size(); i++)
    {
        for(int j = head[i]; j != -1; j = e[j][1])
        {
            if(table[i][e[j][2]] != -1)
                return 0;
            table[i][e[j][2]] = e[j][0];
            tb_s_r[i][e[j][2]] = -1;
        }
    }
    for(int i = 0; i < v.size(); i++)
    {
        for(int j = 0; j < v[i].size(); j++)
        {
            if(v[i][j].id == proce[v[i][j].nump].size())
            {
                for(int k = 0; k < v[i][j].fst.size(); k++)
                {
                    if(table[i][(v[i][j].fst)[k] - '0'] != -1)
                        return 0;
                    if((v[i][j].fst)[k] == '0' && v[i][j].nump == 0)
                    {
                        table[i][(v[i][j].fst)[k] - '0'] = -3;
                    }
                    else
                    {
                        table[i][(v[i][j].fst)[k] - '0'] = v[i][j].nump;
                        tb_s_r[i][(v[i][j].fst)[k] - '0'] = -2;
                    }
                }
            }
        }
    }
    return 1;
}

void print_table()
{
    cout << "LR(1): " << endl;
    cout << "state" << "\t" << "\t" << "\t" << "action" << "\t" << "\t" << endl;
    for(int j = 0; j <= num; j++)
    {
        if(j == numvt)
            continue;
        cout << "\t" << getChar[j];
    }
    cout << endl;
    for(int i = 0; i < v.size(); i++)
    {
        cout << i << "\t";
        for(int j = 0; j <= num; j++)
        {
            if(j == numvt)
                continue;
            if(table[i][j] == -3)
                cout << "acc" << "\t";
            else if (table[i][j] == -1)
                cout << "\t\t";
            else if (tb_s_r[i][j] == -1)
                cout << "s" << table[i][j] << "\t\t";
            else if (tb_s_r[i][j] == -2)
                cout << "r" << table[i][j] << "\t\t";
        }
        cout << endl;
    }
}

string word;

void print_cur_state(int count, stack<int>state, stack<int>wd, int i)
{
    cout << count << "\t\t";
    stack<int>temp;
    while(!state.empty())
    {
        temp.push(state.top());
        state.pop();
    }
    while(!temp.empty())
    {
        cout << temp.top();
        temp.pop();
    }
    cout << "\t\t";
    while(!wd.empty())
    {
        temp.push(wd.top());
        wd.pop();
    }
    while(!temp.empty())
    {
        cout << getChar[temp.top()];
        temp.pop();
    }
    cout << "\t\t";
    for(int j = i; j < word.size(); j++)
    {
        cout << word[j];
    }
    cout << "\t\t";
}

bool analyze()
{
    cout << "\t\t" << word << "'s analyzing process:" << endl;
    cout << "Step\t\t" << "StatesStack\t\t" << "CharacterStack\t\t" << "InputStringStack\t\t" << "Action" << endl;
    stack<int>state;
    stack<int>wd;
    int count = 0;
    state.push(0);
    wd.push(0);
    for(int i = 0;;)
    {
        int cur = state.top();
        if(table[cur][getnum[word[i]]] == -1)
            return 0;
        if(table[cur][getnum[word[i]]] == -3)
        {
            print_cur_state(count++, state, wd, i);
            cout << "\t\tacc!" << endl;
            return 1;
        }
        if(tb_s_r[cur][getnum[word[i]]] == -1)
        {
            print_cur_state(count++ , state, wd, i);
            int newstate = table[cur][getnum[word[i]]];
            cout << "action[" << cur << "," << getnum[word[i]] << "]=" << newstate;
            cout << ", state" << newstate << "in stack" << endl;
            wd.push(getnum[word[i]]);
            state.push(newstate);
            i++;
        }
        else if (tb_s_r[cur][getnum[word[i]]] == -2)
        {
            print_cur_state(count++, state, wd, i);
            int numpro = table[cur][getnum[word[i]]];
            int len = proce[numpro].size() - 1;
            for(int ii = 0; ii < len; ii++)
            {
                wd.pop();
                state.pop();
            }
            wd.push(getnum[proce[numpro][0]]);
            int cur = state.top();
            cout << "Use " << proce[numpro][0] << "->";
            for(int ii = 1; ii <=len ; ii++)
                cout << proce[numpro][ii];
            cout << "Reduction, goto[" << cur << ", " << getnum[word[i]] << "] = " << table[cur][getnum[proce[numpro][0]]];
            cout << "In Stack" << endl;
            state.push(table[cur][getnum[proce[numpro][0]]]);
        }
    }
    return 1;
}

int main()
{
    clear();
    readin();
    getpp();
    getfirst();
    get_projsets();
    if(!get_table())
    {
        cout << "This Grammar has multiple accesses, isn't a LR(1) grammar" << endl;
        return 0;
    }
    print_table();
    cout << "Enter a word: " << endl;
    cin >> word;
    word += '#';
    if(!analyze())
        cout << "Error!" << endl;
    else
        return 0;
}
