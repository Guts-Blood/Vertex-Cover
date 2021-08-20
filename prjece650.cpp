// defined std::unique_ptr
#include <memory>
// defines Var and Lit
#include "minisat/core/SolverTypes.h"
// defines Solver
#include "minisat/core/Solver.h"

// defined std::cout
#include <iostream>
// Compile with c++ ece650-a2cpp -std=c++11 -o ece650-a2
#include <vector>
#include <string>
#include <cstdlib>
#include <queue>
#include <list>
#include <sstream>
#include <unistd.h>
#include <pthread.h>
#include <time.h>

using namespace std;

#define handle_error(msg)   \
    do                      \
    {                       \
        perror(msg);        \
        exit(EXIT_FAILURE); \
    } while (0)

#define handle_error_en(en, msg) \
    do                           \
    {                            \
        errno = en;              \
        perror(msg);             \
        exit(EXIT_FAILURE);      \
    } while (0)
//Define the Vertice type as GraphNode
class GraphNode
{
public:
    //initiali some attribute
    int degree_freedom;
    vector<int> adj_list;
};
//Define the Graph class
class Graph
{
public:
    void setVertice(int);
    int getVertice() const;
    void addEdge(int, int);
    void initialize();
    vector<GraphNode> Vertice;

private:
    int vertice;
};
//reset the Graph
void Graph::initialize()
{
    Vertice.clear();
}

int Graph::getVertice() const
{
    return vertice;
}

void Graph::addEdge(int a, int b)
{
    Vertice[a].adj_list.push_back(b);
    Vertice[b].adj_list.push_back(a);
    Vertice[a].degree_freedom++;
    Vertice[b].degree_freedom++;
}

//setVertice
void Graph::setVertice(int v)
{
    vertice = v;
    for (int count = 0; count < v; count++)
    {
        GraphNode temp;
        temp.degree_freedom = 0;
        Vertice.push_back(temp);
    }
}

void *SAT_Vertexcover(void *arg);

void *Approx_vc_1(void *arg);

void *Approx_vc_2(void *arg);

static void pclock(char *msg, clockid_t cid)
{
    struct timespec ts;

    printf("%s", msg);
    if (clock_gettime(cid, &ts) == -1)
        handle_error("clock_gettime");
    printf("%4jd.%03ld\n", (intmax_t)ts.tv_sec, ts.tv_nsec / 1000000);
}

//main function begins here
int main()
{
    pthread_t sat_thread;
    pthread_t vc1_thread;
    pthread_t vc2_thread;

    clockid_t sat_cid;
    clockid_t vc1_cid;
    clockid_t vc2_cid;

    int s;

    int v;
    string input_commands;
    Graph newGraph;

    do
    {

        getline(cin, input_commands);
        //V command

        if (input_commands[0] == 'V')
        {
            //Initialize the graph and vertice whenever V commands detected
            newGraph.initialize();
            v = atoi(input_commands.substr(1).c_str());
            newGraph.setVertice(v);
        }
        //E command
        else if (input_commands[0] == 'E')
        {
            int has_edge = 0;
            int begin;
            int middle;
            int end;
            for (int count = 0; count < input_commands.length(); count++)
            {
                if (input_commands[count] == '<')
                {
                    begin = count + 1;
                }
                if (input_commands[count] == ',')
                {
                    middle = count;
                }
                //A point is generated
                if (input_commands[count] == '>')
                {
                    end = count;
                    int vertice1;
                    int vertice2;
                    vertice1 = atoi(input_commands.substr(begin, middle).c_str());
                    vertice2 = atoi(input_commands.substr(middle + 1, end).c_str());
                    //detect if vertice is exist in our graph, if not, print out error
                    if (vertice1 < newGraph.Vertice.size() && vertice2 < newGraph.Vertice.size())
                    {
                        newGraph.addEdge(vertice1, vertice2);
                        has_edge = 1;
                    }
                    else
                    {
                        cout << "Error: Input edge excess the graph vertice size" << endl;
                        break;
                    }
                }
            }
            if (has_edge == 0)
            {
                cout << " " << endl;
            }
            else
            {
                s = pthread_create(&sat_thread, NULL, SAT_Vertexcover, &newGraph);
                if (s != 0)
                    handle_error_en(s, "pthread_create");

                s = pthread_join(sat_thread, NULL);
                if (s != 0)
                    handle_error_en(s, "pthread_join");

                s = pthread_create(&vc1_thread, NULL, Approx_vc_1, &newGraph);
                if (s != 0)
                    handle_error_en(s, "pthread_create");                
                s = pthread_join(vc1_thread, NULL);
                if (s != 0)
                    handle_error_en(s, "pthread_join");

                s = pthread_create(&vc2_thread, NULL, Approx_vc_2, &newGraph);
                if (s != 0)
                    handle_error_en(s, "pthread_create");                
                s = pthread_join(vc2_thread, NULL);
                if (s != 0)
                    handle_error_en(s, "pthread_join");
            }
        }
        //check if the input is eof, if not then print out error
        else
        {
            if (!cin.eof())
            {
                cout << "Error: no such command exisit" << endl;
            }
        }
    } while (!cin.eof());

    exit(EXIT_SUCCESS); /* Terminates both threads */
}

void *SAT_Vertexcover(void *arg)
{
    Graph newGraph(*(Graph *)arg);
    //Vertex Cover problem starts from there
    std::unique_ptr<Minisat::Solver> solver(new Minisat::Solver());

    int k = 1;
    bool res;
    int n = newGraph.getVertice();
    vector<vector<Minisat::Lit>> x(n, vector<Minisat::Lit>(n));
    while (k < n)
    {
        //k=(lower_bound+upper_bound)/2;
        solver.reset(new Minisat::Solver());

        // Minisat::Lit x=new Minisat::Lit* [n];
        // for(int i=0;i<n;i++){
        //     x[i]=new Minisat::Lit[k]
        // }
        x.clear();
        x.resize(n, vector<Minisat::Lit>(n));
        //Step1: We need to create a n*k matrix
        for (int counter1 = 0; counter1 < n; counter1++)
        {
            for (int counter2 = 0; counter2 < k; counter2++)
            {
                x[counter1][counter2] = Minisat::mkLit(solver->newVar());
            }
        }
        //Step 2: At least one vertex is the ith vertex in the vertex cover:
        //for all i in 1~k x[1][i]||x[2][i]...x[n][i]
        Minisat::vec<Minisat::Lit> clause;
        for (int counter1 = 0; counter1 < k; counter1++)
        {
            for (int counter2 = 0; counter2 < n; counter2++)
            {
                clause.push(x[counter2][counter1]);
            }
            //use another attribute for list vec type add Clause
            solver->addClause_(clause);
            clause.clear();
        }
        //Step3: No one vertex can appear twice in a vertex cover.
        for (int m = 0; m < n; m++)
        {
            for (int q = 1; q < k; q++)
            {
                for (int p = 0; p < q; p++)
                {
                    // clause.push_back(~x[m][p],~x[m][q]);
                    solver->addClause(~x[m][p], ~x[m][q]);
                    // clause.clear();
                }
            }
        }
        //Step4: No more than one vertex appears in the mth position of the vertex cover.
        for (int m = 0; m < k; m++)
        {
            for (int q = 1; q < n; q++)
            {
                for (int p = 0; p < q; p++)
                {
                    //clause.push_back(~x[p][m],~x[q][m]);
                    solver->addClause(~x[p][m], ~x[q][m]);
                    //clause.clear();
                }
            }
        }
        //Step 5: Every edge is incident to at least one vertex in the vertex cover.
        for (int i = 0; i < n; i++)
        {
            int adj_size = newGraph.Vertice[i].adj_list.size();

            for (int j = 0; j < adj_size; j++)
            {
                for (int counter = 0; counter < k; counter++)
                {
                    clause.push(x[i][counter]);
                }

                for (int counter = 0; counter < k; counter++)
                {
                    clause.push(x[newGraph.Vertice[i].adj_list[j]][counter]);
                }
                solver->addClause_(clause);
                clause.clear();
            }
        }

        res = solver->solve();
        // std::cout << "The result is: " << res << "\n";
        if (res == 1)
        {

            break;
        }
        k++;
    }
    if (res == 1)
    {
        cout << "CNF-SAT-VC: ";
        //print out the result:
        int counter = 0;
        for (int counter1 = 0; counter1 < n; counter1++)
        {
            for (int counter2 = 0; counter2 < k; counter2++)
            {
                if (Minisat::toInt(solver->modelValue(x[counter1][counter2])) == 0)
                {
                    if (counter == 0)
                    {
                        cout << counter1;
                    }
                    else
                    {
                        cout << "," << counter1;
                    }
                    ++counter;
                }
                //cout<<"x"<<counter1<<" "<<counter2<<"is "<<Minisat::toInt(solver->modelValue(x[counter1][counter2]))<<endl;
                //if (Minisat::toInt(solver->modelValue(x[counter1][counter2]))==1){
            }
        }
        cout << endl;
    }
    else
    {
        cout << " " << endl;
    }

    return ((void *)0);
}

void *Approx_vc_1(void *arg)
{
    Graph newGraph(*(Graph *)arg);
    list<int> V_C_set;
    int degree_f;
    do
    {
        //Step1: Find the Vertex with the highest degree of freedom:
        int pos = 0;
        degree_f = 0;
        for (int counter = 0; counter < newGraph.Vertice.size(); counter++)
        {
            if (newGraph.Vertice[counter].degree_freedom > degree_f)
            {
                degree_f = newGraph.Vertice[counter].degree_freedom;
                pos = counter;
            }
        }
        //Step2: add it to our vertex cover:
        if (degree_f > 0)
        {
            V_C_set.push_back(pos);
            //and throw away all edge:
            for (int counter = 0; counter < degree_f; counter++)
            {

                int adj_vertex = newGraph.Vertice[pos].adj_list[counter];
                newGraph.Vertice[adj_vertex].degree_freedom--;
                newGraph.Vertice[pos].degree_freedom--;
            }
        }
    } while (degree_f > 0);
    //Print out the result
    V_C_set.sort();
    
    stringstream rtn;
    rtn << "APPROX-VC-1: ";
    for (auto iter = V_C_set.begin(); iter != V_C_set.end(); ++iter)
    {
        if (iter == V_C_set.begin())
        {
            rtn << *iter;
        }
        else
        {
            rtn << "," << *iter;
        }
    }

    // cout << rtn.str() << endl;
    // cout << "APPROX-VC-1: ";
    // for (int counter = 0; counter < V_C_set.size() - 1; counter++)
    // {
    //     cout << V_C_set[counter] << ",";
    // }
    // cout << V_C_set[V_C_set.size() - 1] << endl;
    cout << rtn.str() << endl;
    return ((void *)0);
}

void *Approx_vc_2(void *arg)
{
    Graph g(*(Graph *)arg);
    list<int> all_nodes;
    vector<list<int>> adj_list;

    list<int> VC;

    int id = 0;
    for (auto iter = g.Vertice.begin(); iter != g.Vertice.end(); ++iter, ++id)
    {
        all_nodes.push_back(id);
        GraphNode node = *iter;
        list<int> _tmp(node.adj_list.begin(), node.adj_list.end());
        adj_list.push_back(_tmp);
    }

    for (auto iter = all_nodes.begin(); iter != all_nodes.end(); ++iter)
    {
        int a = *iter;
        if (adj_list[a].empty())
        {
            continue;
        }

        int b = adj_list[a].front();

        while (!adj_list[a].empty())
        {
            int a1 = adj_list[a].front();
            adj_list[a].remove(a1);
            adj_list[a1].remove(a);
        }
        VC.push_back(a);

        if (adj_list[b].empty())
        {
            continue;
        }

        while (!adj_list[b].empty())
        {
            int b1 = adj_list[b].front();
            adj_list[b].remove(b1);
            adj_list[b1].remove(b);
        }
        VC.push_back(b);
    }
    VC.sort();

    stringstream rtn;
    rtn << "APPROX-VC-2: ";
    for (auto iter = VC.begin(); iter != VC.end(); ++iter)
    {
        if (iter == VC.begin())
        {
            rtn << *iter;
        }
        else
        {
            rtn << "," << *iter;
        }
    }

    cout << rtn.str() << endl;

    return ((void *)0);
}