//============================================================================
// Name        : Main.cpp
// Author      : Ying Xian Wu
// Version     :
// Copyright   :
// Description : Naive algorithm for linearising a domain given problem in .sas file
//============================================================================

#include <climits>
#include <string>
#include <vector>
#include <set>
#include <map>
#include <istream>
#include <stdlib.h>
#include <iostream>
#include <fstream>
#include <sstream>
#include <chrono>
#include <iomanip>
#include <math.h>
#include <filesystem>

#include "directed_graph.h"
#include "util.h"
#include "PrecsEffs.h"

using namespace std;

progression::Model *setup_model(string fileName)
{
       bool trackTasksInTN = false;
       progression::eMaintainTaskReachability maintainTaskReachability = mtrNO; // enum eMaintainTaskReachability {mtrNO, mtrACTIONS, mtrALL};
       bool progressEffectLess = false;
       bool progressOneModActions = false;
       progression::Model *m = new Model(trackTasksInTN, maintainTaskReachability, progressEffectLess, progressOneModActions);
       m->isHtnModel = true;

       std::ifstream fileStream;
       fileStream.open(fileName);
       if (fileStream.is_open())
       {
              printf("The problem file %s was opened successfully.", fileName.c_str());
              m->read(&fileStream);
       }
       else
       {
              printf("Could not open the specified file, %s", fileName.c_str());
       }

       return m;
}

void get_t_pre_eff_(int collect_to_task, int task_to_explore, bool *visited, bool ***all_pre_eff, Model *m, ofstream &o)
{
       if (!(visited[task_to_explore]))
       {
              visited[task_to_explore] = true;
              // add prec/eff of primitive
              if ((*m).isPrimitive[task_to_explore])
              {
                     // yes/no for integer variable that they act on
                     for (int j = 0; j < (*m).numPrecs[task_to_explore]; j++)
                     {
                            int prec = (*m).precLists[task_to_explore][j];
                            all_pre_eff[0][collect_to_task][prec] = true;
                     }
                     for (int j = 0; j < (*m).numAdds[task_to_explore]; j++) // adds
                     {
                            int add = (*m).addLists[task_to_explore][j];
                            all_pre_eff[1][collect_to_task][add] = true;
                     }
                     for (int j = 0; j < (*m).numDels[task_to_explore]; j++) // deletes
                     {
                            int del = (*m).delLists[task_to_explore][j];
                            all_pre_eff[2][collect_to_task][del] = true;
                     }
              }
              // investigate every other subtask it can decompose to
              else
              {
                     int *more_methods = (*m).taskToMethods[task_to_explore];
                     for (int j = 0; j < (*m).numMethodsForTask[task_to_explore]; j++)
                     {
                            int mm = more_methods[j];
                            for (int k = 0; k < (*m).numSubTasks[mm]; k++)
                            {
                                   int next_task = (*m).subTasks[mm][k];
                                   get_t_pre_eff_(collect_to_task, next_task, visited, all_pre_eff, m, o); // passes ptr, all_pre_eff changes kept
                            }
                     }
              }
       } // return all_pre_eff
}

bool ***get_task_pre_eff(Model *m, bool ***all_pre_eff, ofstream &o)
{
       // collect pre_eff for all tasks
       for (int t = 0; t < (*m).numTasks; t++)
       {
              int task_to_explore = t;
              bool *visited = new bool[(*m).numTasks];
              get_t_pre_eff_(t, task_to_explore, visited, all_pre_eff, m, o);
       }
       return all_pre_eff;
}



// this could be bool **,  adjacency graph for a methods subtasks
void find_orderings_(Model *m, int method, bool ***tasks_pre_eff, bool ***orderings, ofstream &o)
{
       // consider one subtasks
       for (int i = 0; i < (*m).numSubTasks[method]; i++)
       {
              int subtask_pos = i; // its position among subtasks
              int subtask = (*m).subTasks[method][i];
              // compared to other subtasks in that method
              for (int j = 0; j < (*m).numSubTasks[method]; j++)
              {
                     if (i != j) // not against yourself
                     {
                            int other_subtask_pos = j;
                            int other_subtask = (*m).subTasks[method][j];

                            for (int v = 0; v < (*m).numStateBits; v++)
                            {
                                   //// * For each add effect a of c
                                   bool add_effect = tasks_pre_eff[1][subtask][v];
                                   if (add_effect)
                                   {
                                          // move all other subtasks with precondition a behind c
                                          bool prec = tasks_pre_eff[0][other_subtask][v];
                                          if (prec)
                                          {
                                                 orderings[method][subtask_pos][other_subtask_pos] = true; // edge e1 = edge(subtask_pos, other_subtask_pos);   orderings[method].insert
                                          }
                                          //  and all other sub tasks with a delete effect in front of it.
                                          bool del_effect_ = tasks_pre_eff[2][other_subtask][v];
                                          if (del_effect_)
                                          {
                                                 orderings[method][other_subtask_pos][subtask_pos] = true;
                                          }
                                   }

                                   //// * For each delete effect d of c
                                   bool del_effect = tasks_pre_eff[2][subtask][v];
                                   if (del_effect)
                                   {
                                          // move all tasks with precondition d before c
                                          bool prec_ = tasks_pre_eff[0][other_subtask][v];
                                          if (prec_)
                                          {
                                                 orderings[method][other_subtask_pos][subtask_pos] = true;
                                          }

                                          // and all tasks with an add effect behind it.
                                          bool add_ = tasks_pre_eff[1][other_subtask][v];
                                          if (add_)
                                          {
                                                 orderings[method][subtask_pos][other_subtask_pos] = true;
                                          }
                                   }
                            }
                     }
              }
       } // return orderings;
}

void find_orderings(Model *m, bool ***tasks_pre_eff, bool ***orderings_per_method, ofstream &o)
{
       // get orderings for each method
       for (int method = 0; method < (*m).numMethods; method++)
       {
              find_orderings_(m, method, tasks_pre_eff, orderings_per_method, o);
       }
}


// search for and break cycles in the set of orderings
// adds new ordering to linearised_orderings
// returns bool whether it needed to cycle break or not
bool generate_total_ordering_(Model *m, int method, bool ***old_orderings, bool ***linearised_orderings, ofstream &o)
{
       std::set<edge> edges;
       bool needed_cycle_break = false;
       //  first priority to respect: (*m).orderings
       // (can't be overwritten later)
       for (int i = 0; i < (*m).numOrderings[method] - 1; i += 2)
       {
              int o1 = (*m).ordering[method][i];
              int o2 = (*m).ordering[method][i + 1]; // subtask ids
              edge edge(o1, o2, 0);
              edges.insert(edge);
       }

       //  second priority to respect: output of find_orderings
       // (cannot overwrite previous edges (i.e. already assigned a higher priority) )
       for (int i = 0; i < (*m).numSubTasks[method]; i++)
       {
              for (int j = 0; j < (*m).numSubTasks[method]; j++)
              {
                     if (old_orderings[method][i][j] && edges.find(edge(i, j, 0)) == edges.end())
                     {
                            // we take the subtask ids in the method - just want small subgraph
                            edge edge(i, j, 1);
                            edges.insert(edge);
                     }
              }
       }

       // find and break cycles in proposed orderings (without affecting required orderings)
       int V = (*m).numSubTasks[method];
       std::set<edge> new_orderings = break_cycle(edges, V);
       if (new_orderings != edges)
       {
              needed_cycle_break = true;
       }

       // make new orderings totally ordered
       Graph g2((*m).numSubTasks[method]);
       for (auto e : new_orderings)
              g2.addEdge(e.start, e.end, 0);
       stack<int> Stack = g2.topologicalSort();

       // return topological ordering in adj matrix format
       int first = Stack.top();
       Stack.pop();
       while (Stack.empty() == false)
       {
              int second = Stack.top();
              linearised_orderings[method][first][second] = true;
              first = second;
              Stack.pop();
       }
       return needed_cycle_break;
}
 
int generate_total_ordering(Model *m, bool ***old_orderings, bool ***linearised_orderings, ofstream &o)
{
       int i = 0;
       // get orderings for each method
       for (int method = 0; method < (*m).numMethods; method++)
       {
              if (generate_total_ordering_(m, method, old_orderings, linearised_orderings, o))
              {
                     i++;
              }
       }
       return i;
} 
// only linearisees methods that didn't need cycle breaking, otherwise leaves it alone
int generate_total_ordering_where_possible(Model *m, bool ***old_orderings, bool ***linearised_orderings, bool *needs_breaking, ofstream &o)
{
       int i = 0;
       // get orderings for each method
       for (int method = 0; method < (*m).numMethods; method++)
       {
              needs_breaking[method] = generate_total_ordering_(m, method, old_orderings, linearised_orderings, o);
              if (needs_breaking[method])
              {
                     i++;
              }
       }
       return i;
}


void make_linearized_model(Model *m, bool ***linearised_orderings, ofstream &o)
{
       // delete the old orderings of the methods
       delete[](*m).ordering;
       (*m).ordering = new int *[(*m).numMethods];

       // insert the new orderings of the methods
       for (int method = 0; method < (*m).numMethods; method++)
       {
              std::vector<int> orderings_vec; // for this method
              for (int i = 0; i < (*m).numSubTasks[method]; i++)
              {
                     for (int j = 0; j < (*m).numSubTasks[method]; j++)
                     {
                            if (linearised_orderings[method][i][j])
                            {
                                   orderings_vec.push_back(i);
                                   orderings_vec.push_back(j); // orderings relative to subtask ids
                            }
                     }
              }
              (*m).numOrderings[method] = orderings_vec.size();           // new size of ordering
              (*m).ordering[method] = new int[(*m).numOrderings[method]]; // new ordering array
              for (unsigned long int i = 0; i < orderings_vec.size(); i++)
              {
                     (*m).ordering[method][i] = orderings_vec[i];
              }
       } // return m;
}

void make_linearized_model_where_possible(Model *m, bool ***linearised_orderings, bool *needs_breaking, ofstream &o)
{

       // re-assign the old orderings of the methods
       int **old_ordering = (*m).ordering;
       (*m).ordering = new int *[(*m).numMethods];
       

       for (int method = 0; method < (*m).numMethods; method++)
       {
              // insert the new orderings of the methods (only if cycle breaking was not needed)
              if (needs_breaking[method])
              {              
                     (*m).ordering[method] = old_ordering[method];                    
              } 
              else 
              {
                     std::vector<int> orderings_vec; // for this method
                     for (int i = 0; i < (*m).numSubTasks[method]; i++)
                     {
                            for (int j = 0; j < (*m).numSubTasks[method]; j++)
                            {
                                   if (linearised_orderings[method][i][j])
                                   {
                                          orderings_vec.push_back(i);
                                          orderings_vec.push_back(j); // orderings relative to subtask ids
                                   }
                            }
                     }
                     (*m).numOrderings[method] = orderings_vec.size();           // new size of ordering
                     (*m).ordering[method] = new int[(*m).numOrderings[method]]; // new ordering array
                     for (unsigned long int i = 0; i < orderings_vec.size(); i++)
                     {
                            (*m).ordering[method][i] = orderings_vec[i];
                            
                     }
              }

       }

       // delete the old orderings of the methods
       delete[] old_ordering;
}


void test(Model *m, int start, int end)
{
       for (int method = start; method < end; method++)
       {
              printf("method %i: ", method);
              for (int i = 0; i < (*m).numOrderings[method]; i++)
              {
                     printf("%i ", (*m).ordering[method][i]);
              }
              printf("\n");
       }
}

void collect_statistics_(Model *m, float * timings,  ofstream& o, bool init_needed_break, int methods_broken) {
       if (o.is_open())
       {
              // methods  information 
              int max = 0;
              int min = INT_MAX;
              int sum = 0;
              for (int method = 1; method < (*m).numMethods; method++)
              {
                     // if ((*m).decomposedTask[method] != (*m).initialTask)
                     //{
                     if (max < (*m).numSubTasks[method])
                     {
                            max = (*m).numSubTasks[method];
                     }
                     if (min > (*m).numSubTasks[method])
                     {
                            min = (*m).numSubTasks[method];
                     }
                     sum += (*m).numSubTasks[method];
                     //}
              }
              if (min >= INT_MAX)
                     min = 0;

              float avg;
              if ((*m).numMethods > 1)
              {
                     avg = static_cast<float>(sum) / (static_cast<float>((*m).numMethods) - 1);
              }
              else
              {
                     avg = min;
              }

              int init_tn_size = (*m).numSubTasks[0];

              o << (*m).numStateBits << ",";
              o << (*m).numTasks << ",";
              o << init_tn_size << ",";
              o << ((init_needed_break) ? "true" : "false") << ",";
              o << min << "," << max << "," << avg << ",";
              o << (*m).numMethods << ",";
              o << methods_broken << ",";

              int big_method_num = 0;
              for (int method = 0; method < (*m).numMethods; method++)
              {
                     if ((*m).numSubTasks[method] > 1)
                     {
                            big_method_num++; // number of methods with more than one subtask
                     }
              }
              o << big_method_num << ",";
              o << (((*m).numMethods - static_cast<float>(methods_broken)) / (*m).numMethods) * 100 << ",";
              o << ((big_method_num - static_cast<float>(methods_broken)) / (big_method_num)) * 100 << ",";

              Graph g((*m).numTasks);
              for (int method = 0; method < (*m).numMethods; method++)
              {
                     int parent = (*m).decomposedTask[method];
                     for (int child_pos = 0; child_pos < (*m).numSubTasks[method]; child_pos++)
                     {
                            int child = (*m).subTasks[method][child_pos];
                            g.addEdge(parent, child, 0);
                     }
              }
              std::vector<edge> back_edges = g.findAllCycles((*m).initialTask);
              o << back_edges.size() << ","; // ((back_edges.size() > 0) ? "true" : "false") << ","; // if it has back edges, it is recursive, => "true"

              int height = g.findGraphHeight((*m).initialTask);
              o << (height - 1) << ",";

              o << timings[0] << "," << timings[1] << "," << timings[2] << "," << timings[4] << ","; // "," << timings[3] <<

              // read the solved file
              // o << Status: TO_Solved
              o.close();

              cout << "Preprocessing time: " << timings[4] << "\n";
       }
}

// transform Conny's preconditions and effects to the format for find_orderings
void transform(int num_compound_tasks, vector<int> *poss_eff_positive, vector<int> *poss_eff_negative, vector<int> *eff_positive,
               vector<int> *eff_negative, vector<int> *preconditions, bool ***all_pre_eff)
{
       for (int t = 0; t < num_compound_tasks; t++)
       {
              for (unsigned long int i = 0; i < preconditions[t].size(); i++)      // prec
              {
                     int prec = preconditions[t][i];
                     all_pre_eff[0][t][prec] = true;
              }   
              for (unsigned long int i = 0; i < poss_eff_positive[t].size(); i++)  // add
              {
                     int prec = poss_eff_positive[t][i];
                     all_pre_eff[1][t][prec] = true;
              }
              for (unsigned long int i = 0; i < poss_eff_negative[t].size(); i++) // you mean a delete???
              {
                     int prec = poss_eff_negative[t][i];
                     all_pre_eff[2][t][prec] = true;
              }                         
       }
}


void ComplexTopLevelLinearization(Model * m, string domain_out_name, string problem_out_name, bool collect_statistics, ofstream& o) {
    //   bool ***linearised_orderings, bool * needed_break) {
       auto start_all = std::chrono::high_resolution_clock::now();
       float timings[10];

       /*************************** CONNY's (was in Model.cpp) *******************************/
       // BEGIN: Compute possible effects. Just for dev reason i am using var = 0 (first state variable)
       cout << "Calculating preconditions and effects of compound tasks... " << endl;
       (*m).buildOrderingDatastructures();
       int amount_compound_tasks = 0;
       // for (size_t index = 0; index < m->numTasks; index++)
       // {
       //        if (!m->isPrimitive[index])
       //               amount_compound_tasks++;
       // }

       m->poss_eff_positive = new vector<int>[amount_compound_tasks];
       m->poss_eff_negative = new vector<int>[amount_compound_tasks];
       m->eff_positive = new vector<int>[amount_compound_tasks];
       m->eff_negative = new vector<int>[amount_compound_tasks];
       m->preconditions = new vector<int>[amount_compound_tasks];

       m->poss_pos_m = new vector<int>[m->numMethods];
       m->poss_neg_m = new vector<int>[m->numMethods];
       m->eff_pos_m = new vector<int>[m->numMethods];
       m->eff_neg_m = new vector<int>[m->numMethods];
       m->prec_m = new vector<int>[m->numMethods];

       progression::computeEffectsAndPreconditions(m, m->poss_eff_positive, m->poss_eff_negative, m->eff_positive, m->eff_negative, m->preconditions, amount_compound_tasks);
       // END: Compute effects
       printf("Conn'y's Effects computed\n");

       // transform prec/eff format
       // set up storage
       int T = (*m).numTasks;
       int V = (*m).numStateBits;
       bool ***all_pre_eff = new bool **[3]; // [3][numTasks][numStateBits]
       for (int i = 0; i < 3; i++)
       {
              all_pre_eff[i] = new bool *[T];
              for (int t = 0; t < (*m).numTasks; t++)
              {
                     all_pre_eff[i][t] = new bool[V]{false};
              }
       }
       transform(amount_compound_tasks, m->poss_eff_positive, m->poss_eff_negative, m->eff_positive,
              m->eff_negative, m->preconditions, all_pre_eff);

       ///////////////////////////////////// start linearizing the top-level method //////////////////////////////////
       ///////////////////////////////////// get orderings
       auto start = std::chrono::high_resolution_clock::now();
       // set up storage
       bool ***orderings_per_method = new bool **[(*m).numMethods];
       for (int method = 0; method < (*m).numMethods; method++)
       {
              orderings_per_method[method] = new bool *[(*m).numSubTasks[method]];
              for (int i = 0; i < (*m).numSubTasks[method]; i++)
              {
                     orderings_per_method[method][i] = new bool[(*m).numSubTasks[method]]{0};
              }
       }
              
       auto stop = std::chrono::high_resolution_clock::now();
       auto duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start_all);
       float d = static_cast<float>(duration.count()) / 1000000.0;
       timings[0] = d; // time taken for complex inference of variables
       
       // printf("Before linearization of top method\n");
       // test(m, 0, 20);

       //find_orderings(m, all_pre_eff, orderings_per_method, o); 
       int method = 0;       
       find_orderings_(m, method, all_pre_eff, orderings_per_method, o);
       
       // delete storage
       T = (*m).numTasks;
       V = (*m).numStateBits;
       for (int i = 0; i < 3; i++)
       {
              for (int t = 0; t < (*m).numTasks; t++)
              {
                     delete all_pre_eff[i][t];
              }
              delete[] all_pre_eff[i];
       }
       delete[] all_pre_eff;

       stop = std::chrono::high_resolution_clock::now();
       duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
       d = static_cast<float>(duration.count()) / 1000000.0;
       timings[1] = d;

       //////////////////////////////////////// get linearised orderings  (ONLY FOR THE TOP-LEVEL task)
       // set up storage
       bool ***linearised_orderings = new bool **[(*m).numMethods];
       for (int method = 0; method < (*m).numMethods; method++)
       {
              // container for linearised_orderings -> initialise
              linearised_orderings[method] = new bool *[(*m).numSubTasks[method]];
              for (int i = 0; i < (*m).numSubTasks[method]; i++)
              {
                     linearised_orderings[method][i] = new bool[(*m).numSubTasks[method]]{0};
              }
       }
       bool init_needed_break = generate_total_ordering_(m, method, orderings_per_method, linearised_orderings, o);

       /////////////////////////////////////// make_linearised_model_where_toplevel_method     
       delete (*m).ordering[method];
       std::vector<int> orderings_vec; // for this method
       for (int i = 0; i < (*m).numSubTasks[method]; i++)
       {
              for (int j = 0; j < (*m).numSubTasks[method]; j++)
              {
                     if (linearised_orderings[method][i][j])
                     {
                            orderings_vec.push_back(i);
                            orderings_vec.push_back(j); // orderings relative to subtask ids
                     }
              }
       }
       
       (*m).numOrderings[method] = orderings_vec.size();           // new size of ordering
       (*m).ordering[method] = new int[(*m).numOrderings[method]]; // new ordering array
       for (unsigned long int i = 0; i < orderings_vec.size(); i++)
       {
              (*m).ordering[method][i] = orderings_vec[i];
       }

       // delete (orderings stoarge) storage
       for (int method = 0; method < (*m).numMethods; method++)
       {
              for (int i = 0; i < (*m).numSubTasks[method]; i++)
              {
                     delete orderings_per_method[method][i];
              }
              delete[] orderings_per_method[method];
       }
       delete[] orderings_per_method;


       /* test after */
       // printf("\nAfter linearizing top level method\n");
       // test(m, 0, 20);
       printf("Top-level needed breaking %i \n", init_needed_break);
       // delete storage
       for (int method = 0; method < (*m).numMethods; method++)
       {
              for (int i = 0; i < (*m).numSubTasks[method]; i++)
              {
                     delete linearised_orderings[method][i];
              }
              delete[] linearised_orderings[method];
       }
       delete[] linearised_orderings;

       stop = std::chrono::high_resolution_clock::now();
       duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
       d = static_cast<float>(duration.count()) / 1000000.0;
       timings[2] = d;

       auto stop_all = std::chrono::high_resolution_clock::now();
       duration = std::chrono::duration_cast<std::chrono::microseconds>(stop_all - start_all);
       d = static_cast<float>(duration.count()) / 1000000.0;
       timings[4] = d;

       // m->writeToPDDL(domain_out_name, problem_out_name);

       //////////////////////////////////////// metrics for top level change ///////////////////////////////////////
       if (o.is_open())
       {
              // methods  information
              int max = 0;
              int min = INT_MAX;
              int sum = 0;
              for (int method = 1; method < (*m).numMethods; method++)
              {
                     // if ((*m).decomposedTask[method] != (*m).initialTask)
                     //{
                     if (max < (*m).numSubTasks[method])
                     {
                            max = (*m).numSubTasks[method];
                     }
                     if (min > (*m).numSubTasks[method])
                     {
                            min = (*m).numSubTasks[method];
                     }
                     sum += (*m).numSubTasks[method];
                     //}
              }
              if (min >= INT_MAX)
                     min = 0;

              float avg;
              if ((*m).numMethods > 1)
              {
                     avg = static_cast<float>(sum) / (static_cast<float>((*m).numMethods) - 1);
              }
              else
              {
                     avg = min;
              }

              int init_tn_size = (*m).numSubTasks[0];

              o << (*m).numStateBits << ",";
              o << (*m).numTasks << ",";
              o << init_tn_size << ",";
              o << ((init_needed_break) ? "true" : "false") << ",";
              o << min << "," << max << "," << avg << ",";
              o << (*m).numMethods << ",";
              o << "Unknown" << ",";

              int big_method_num = 0;
              for (int method = 0; method < (*m).numMethods; method++)
              {
                     if ((*m).numSubTasks[method] > 1)
                     {
                            big_method_num++; // number of methods with more than one subtask
                     }
              }
              o << big_method_num << ",";
              o << "Unknown" << ","; //(((*m).numMethods - static_cast<float>(methods_broken)) / (*m).numMethods) * 100 << ",";
              o << "Unknown" << ","; //((big_method_num - static_cast<float>(methods_broken)) / (big_method_num)) * 100 << ",";

              Graph g((*m).numTasks);
              for (int method = 0; method < (*m).numMethods; method++)
              {
                     int parent = (*m).decomposedTask[method];
                     for (int child_pos = 0; child_pos < (*m).numSubTasks[method]; child_pos++)
                     {
                            int child = (*m).subTasks[method][child_pos];
                            g.addEdge(parent, child, 0);
                     }
              }
              std::vector<edge> back_edges = g.findAllCycles((*m).initialTask);
              o << back_edges.size() << ","; // ((back_edges.size() > 0) ? "true" : "false") << ","; // if it has back edges, it is recursive, => "true"

              int height = g.findGraphHeight((*m).initialTask);
              o << (height - 1) << ",";

              o << timings[0] << "," << timings[1] << "," << timings[2] << "," << timings[4] << ","; // "," << timings[3] <<

              // read the solved file
              // o << Status: TO_Solved
              o.close();

              cout << "Preprocessing time: " << timings[4] << "\n";
       }
}



void ComplexInference(Model * m, bool collect_statistics, ofstream& o,  bool linearize_all=true) {
    //   bool ***linearised_orderings, bool * needed_break) {
       auto start_all = std::chrono::high_resolution_clock::now();
       auto start = std::chrono::high_resolution_clock::now();
       float timings[10];

       /*************************** CONNY's (was in Model.cpp) *******************************/
       // BEGIN: Compute possible effects. Just for dev reason i am using var = 0 (first state variable)
       cout << "Calculating preconditions and effects of compound tasks... " << endl;
       (*m).buildOrderingDatastructures();
       int amount_compound_tasks = 0;
       for (int index = 0; index < m->numTasks; index++)
       {
              if (!m->isPrimitive[index])
                     amount_compound_tasks++;
       }

       m->poss_eff_positive = new vector<int>[amount_compound_tasks];
       m->poss_eff_negative = new vector<int>[amount_compound_tasks];
       m->eff_positive = new vector<int>[amount_compound_tasks];
       m->eff_negative = new vector<int>[amount_compound_tasks];
       m->preconditions = new vector<int>[amount_compound_tasks];

       m->poss_pos_m = new vector<int>[m->numMethods];
       m->poss_neg_m = new vector<int>[m->numMethods];
       m->eff_pos_m = new vector<int>[m->numMethods];
       m->eff_neg_m = new vector<int>[m->numMethods];
       m->prec_m = new vector<int>[m->numMethods];

       progression::computeEffectsAndPreconditions(m, m->poss_eff_positive, m->poss_eff_negative, m->eff_positive, m->eff_negative, m->preconditions, amount_compound_tasks);
       // END: Compute effects

       // transform prec/eff format
       // set up storage
       int T = (*m).numTasks;
       int V = (*m).numStateBits;
       bool ***all_pre_eff = new bool **[3]; // [3][numTasks][numStateBits]
       for (int i = 0; i < 3; i++)
       {
              all_pre_eff[i] = new bool *[T];
              for (int t = 0; t < (*m).numTasks; t++)
              {
                     all_pre_eff[i][t] = new bool[V]{false};
              }
       }
       transform(amount_compound_tasks, m->poss_eff_positive, m->poss_eff_negative, m->eff_positive,
              m->eff_negative, m->preconditions, all_pre_eff);
       auto stop = std::chrono::high_resolution_clock::now();
       auto duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
       float d = static_cast<float>(duration.count()) / 1000000.0;
       timings[0] = d;

       // get orderings
       start = std::chrono::high_resolution_clock::now();
       // set up storage
       bool ***orderings_per_method = new bool **[(*m).numMethods];
       for (int method = 0; method < (*m).numMethods; method++)
       {
              orderings_per_method[method] = new bool *[(*m).numSubTasks[method]];
              for (int i = 0; i < (*m).numSubTasks[method]; i++)
              {
                     orderings_per_method[method][i] = new bool[(*m).numSubTasks[method]]{0};
              }
       }
       find_orderings(m, all_pre_eff, orderings_per_method, o); // get
       // delete storage
       T = (*m).numTasks;
       V = (*m).numStateBits;
       for (int i = 0; i < 3; i++)
       {
              for (int t = 0; t < (*m).numTasks; t++)
              {
                     delete all_pre_eff[i][t];
              }
              delete[] all_pre_eff[i];
       }
       delete[] all_pre_eff;

       stop = std::chrono::high_resolution_clock::now();
       duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
       d = static_cast<float>(duration.count()) / 1000000.0;
       timings[1] = d;


       // // get linearised orderings
       // set up storage
       bool ***linearised_orderings = new bool **[(*m).numMethods];
       for (int method = 0; method < (*m).numMethods; method++)
       {
              linearised_orderings[method] = new bool *[(*m).numSubTasks[method]];
              for (int i = 0; i < (*m).numSubTasks[method]; i++)
              {
                     linearised_orderings[method][i] = new bool[(*m).numSubTasks[method]]{0};
              }
       }
       bool *needed_break = new bool[(*m).numMethods];
       
       bool init_needed_break;
       if (o.is_open())
              init_needed_break = generate_total_ordering_(m, 0, orderings_per_method, linearised_orderings, o);

       start = std::chrono::high_resolution_clock::now();
       int methods_broken;
       if (linearize_all) {
              methods_broken = generate_total_ordering(m, orderings_per_method, linearised_orderings, o); // get
       } else {
              methods_broken = generate_total_ordering_where_possible(m, orderings_per_method, linearised_orderings, needed_break, o); // get
       }

       // delete storage
       for (int method = 0; method < (*m).numMethods; method++)
       {
              for (int i = 0; i < (*m).numSubTasks[method]; i++)
              {
                     delete orderings_per_method[method][i];
              }
              delete[] orderings_per_method[method];
       }
       delete[] orderings_per_method;

       // return (linearised_orderings, needed_break);
       if (linearize_all) {
              make_linearized_model(m, linearised_orderings, o);
       } else {    
              make_linearized_model_where_possible(m, linearised_orderings, needed_break, o);
       }
       /* test after */
       // printf("Conny's algorithm 1");
       //  printf("\nAfter\n");
       // test(m, 0, 20);
       printf("Methods broken %i \n", methods_broken);
       printf("Number of Actions %i \n", (*m).numActions);

       // delete storage
       for (int method = 0; method < (*m).numMethods; method++)
       {
              for (int i = 0; i < (*m).numSubTasks[method]; i++)
              {
                     delete linearised_orderings[method][i];
              }
              delete[] linearised_orderings[method];
       }
       delete[] linearised_orderings;

       stop = std::chrono::high_resolution_clock::now();
       duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
       d = static_cast<float>(duration.count()) / 1000000.0;
       timings[2] = d;
       
       auto stop_all = std::chrono::high_resolution_clock::now();
       duration = std::chrono::duration_cast<std::chrono::microseconds>(stop_all - start_all);
       d = static_cast<float>(duration.count()) / 1000000.0;
       timings[4] = d;
        
       // m->writeToPDDL(domain_out_name, problem_out_name);

       // collect statistics
       if (collect_statistics) {
              collect_statistics_(m, timings, o, init_needed_break, methods_broken);
       }
}


/************************************** GREGORS **********************************/
void SimpleInference(Model * m, string domain_out_name, string problem_out_name, bool collect_statistics, ofstream& o, bool linearize_all=true) {
       // get preconditions and effects
       auto start_all = std::chrono::high_resolution_clock::now();
       auto start = std::chrono::high_resolution_clock::now();
       float timings[10];
       // set up storage
       int T = (*m).numTasks;
       int V = (*m).numStateBits;
       bool ***all_pre_eff = new bool **[3]; // [3][numTasks][numStateBits]
       for (int i = 0; i < 3; i++)
       {
              all_pre_eff[i] = new bool *[T];
              for (int t = 0; t < (*m).numTasks; t++)
              {
                     all_pre_eff[i][t] = new bool[V]{false};
              }
       }

       /* test before */
       // printf("\nBefore: \n");
       // test(m, 0, 20);

       get_task_pre_eff(m, all_pre_eff, o); // get
       auto stop = std::chrono::high_resolution_clock::now();
       auto duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
       float d = static_cast<float>(duration.count()) / 1000000.0;
       timings[0] = d;

       // //test output
       // int task = 52;
       // printf("Collected preconditions and effects of Task %i\n", task);
       // for (int i = 0; i < 3; i++)
       // {
       //        for (int k = 0; k < (*m).numStateBits; k++)
       //        {
       //               if (all_pre_eff[i][task][k])
       //               {
       //                      printf("%i ", k);
       //               }
       //        }
       //        printf("\n");
       // }
       // //test output

       // get orderings
       start = std::chrono::high_resolution_clock::now();
       // set up storage
       bool ***orderings_per_method = new bool **[(*m).numMethods];
       for (int method = 0; method < (*m).numMethods; method++)
       {
              orderings_per_method[method] = new bool *[(*m).numSubTasks[method]];
              for (int i = 0; i < (*m).numSubTasks[method]; i++)
              {
                     orderings_per_method[method][i] = new bool[(*m).numSubTasks[method]]{0};
              }
       }
       start = std::chrono::high_resolution_clock::now();
       find_orderings(m, all_pre_eff, orderings_per_method, o); // get
       // delete storage
       T = (*m).numTasks;
       V = (*m).numStateBits;
       for (int i = 0; i < 3; i++)
       {
              for (int t = 0; t < (*m).numTasks; t++)
              {
                     delete all_pre_eff[i][t];
              }
              delete[] all_pre_eff[i];
       }
       delete[] all_pre_eff;

       stop = std::chrono::high_resolution_clock::now();
       duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
       d = static_cast<float>(duration.count()) / 1000000.0;
       timings[1] = d;

       // // get linearised orderings
       // set up storage
       bool ***linearised_orderings = new bool **[(*m).numMethods]; 
       for (int method = 0; method < (*m).numMethods; method++)
       {
              linearised_orderings[method] = new bool *[(*m).numSubTasks[method]];
              for (int i = 0; i < (*m).numSubTasks[method]; i++)
              {
                     linearised_orderings[method][i] = new bool[(*m).numSubTasks[method]]{0};
              }
       }
       bool * needed_break = new bool[(*m).numMethods];

       bool init_needed_break;
       if (o.is_open())
              init_needed_break = generate_total_ordering_(m, 0, orderings_per_method, linearised_orderings, o);

       start = std::chrono::high_resolution_clock::now();
       int methods_broken;
       if (linearize_all) {        
              methods_broken = generate_total_ordering(m, orderings_per_method, linearised_orderings, o); // get
       } else {
              methods_broken = generate_total_ordering_where_possible(m, orderings_per_method, linearised_orderings, needed_break, o); // get
       }

       // delete storage
       for (int method = 0; method < (*m).numMethods; method++)
       {
              for (int i = 0; i < (*m).numSubTasks[method]; i++)
              {
                     delete orderings_per_method[method][i];
              }
              delete[] orderings_per_method[method];
       }
       delete[] orderings_per_method;

       // return (linearised_orderings, needed_break)
       if (linearize_all) {
              make_linearized_model(m, linearised_orderings, o);
       } else {
              make_linearized_model_where_possible(m, linearised_orderings, needed_break, o);
       }

       /* test after */
       // printf("\nAfter\n");
       // test(m, 0, 20);
       printf("Methods broken %i \n", methods_broken);
       printf("Number of Actions %i \n", (*m).numActions);

       // delete storage
       for (int method = 0; method < (*m).numMethods; method++)
       {
              for (int i = 0; i < (*m).numSubTasks[method]; i++)
              {
                     delete linearised_orderings[method][i];
              }
              delete[] linearised_orderings[method];
       }
       delete[] linearised_orderings;

       stop = std::chrono::high_resolution_clock::now();
       duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
       d = static_cast<float>(duration.count()) / 1000000.0;
       timings[2] = d;

       auto stop_all = std::chrono::high_resolution_clock::now();
       duration = std::chrono::duration_cast<std::chrono::microseconds>(stop_all - start_all);
       d = static_cast<float>(duration.count()) / 1000000.0;
       timings[4] = d;
 
       // m->writeToPDDL(domain_out_name, problem_out_name);

       // collect statistics
       if (collect_statistics) {
              collect_statistics_(m, timings, o, init_needed_break, methods_broken);
       }
}


// int main(int argc, char *argv[])
// {
//        char *problem_sas;
//        string domain_out_name;
//        string problem_out_name;
//        char *timing_file;
//        string processing_method;
//        bool collect_statistics = true;

//        if (argc > 4)
//        {
//               problem_sas = argv[1];
//               domain_out_name = argv[2]; 
//               problem_out_name = argv[3];
//               timing_file = argv[4];
//               processing_method = argv[5];  
//        }
//        else
//        {
//               printf("You need to pass in:\n 1) a sas problem file, name of new domain file, name of new problem file, name of the timings file, and algorithm to use");
//               return 1;
//        }

//        Model *m = setup_model(problem_sas); 
//        ofstream o; // ofstream is the class for fstream package
//        if (collect_statistics)
//        {
//               o.open(timing_file, std::ios_base::app);
//               if (!(o.is_open()))
//               {
//                      printf("Could not open timings file\n");
//                      return 0;
//               }
//        }
  
//        // inference here changes Model * m
//        printf("Processing_method %s\n", processing_method.c_str());
//        if (processing_method.compare("CS") == 0) {
//               ofstream o_empty;
//               ComplexInference(m, domain_out_name, problem_out_name, false, o_empty, false);  
//               SimpleInference(m, domain_out_name, problem_out_name, collect_statistics, o, false);
//        }
//        else if (processing_method.compare("CPossible") == 0) {            
//               ComplexInference(m, domain_out_name, problem_out_name, collect_statistics, o, false);}  
//        else if (processing_method.compare("SPossible") == 0) { 
//               SimpleInference(m, domain_out_name, problem_out_name, collect_statistics, o, false);} 
//        else if (processing_method.compare("C") == 0) {            
//               ComplexInference(m, domain_out_name, problem_out_name, collect_statistics, o, true);}  
//        else if (processing_method.compare("S") == 0) {
//              SimpleInference(m, domain_out_name, problem_out_name, collect_statistics, o, true);} 
//        else if (processing_method.compare("CT") == 0) {
//               ComplexTopLevelLinearization(m, domain_out_name, problem_out_name, collect_statistics, o);}
//        else {
//               printf("Error: This algorithm (%s) is unkonwn", processing_method.c_str());
//        }       
// }
