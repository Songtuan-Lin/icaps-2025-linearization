// A C++ Program to detect cycle in a graph (from https://www.geeksforgeeks.org/detect-cycle-in-a-graph/)
#include "directed_graph.h"


using namespace std;

// iPair ==> Integer Pair
// distance/priority, node_id
typedef pair<int, int> iPair;


edge::edge(int s, int e, int w = 0)
{
    start = s;
    end = e;
    weight = w;
}

bool edge::operator<(const edge &rhs) const
{
    if (start < rhs.start || (start == rhs.start && end < rhs.end))
    {
        return true;
    }
    return false;
}

bool edge::operator==(const edge &rhs) const
{
    if (start == rhs.start && end == rhs.end)
    {
        return true;
    }
    return false;
}

bool edge::operator>(const edge &rhs) const
{
    return !(operator<(rhs)) && !(operator==(rhs));
}

void edge::print()
{
    printf("(%i, %i)%i ", start, end, weight);
}

void print(set<edge> s)
{
    for (auto elem : s)
    {
        elem.print();
    }
    printf("\n");
}

void print(std::vector<edge> s)
{
    for (auto elem : s)
    {
        elem.print();
    }
    printf("\n");
}

void print(list<adj_edge> s)
{
    for (auto elem : s)
    {
        printf("%i)%i, ", elem.end, elem.weight);
    }
    printf("\n");
}
void print(list<adj_edge> * s, int V)
{
    for (int i=0; i<V; i++) {
        printf("%i ->", i);
        print(s[i]);
    }
    printf("\n");
}


void set_to_vector()
{
}

bool adj_edge::operator==(const adj_edge &rhs) const
{
    if (end == rhs.end && weight == rhs.weight)
    {
        return true;
    }
    return false;
}

adj_edge::adj_edge(int v, int p)
{
    end = v;
    weight = p;
}

Graph::Graph(int V, int p_lev)
{
    this->V = V;
    adj = new list<adj_edge>[V];
    p_levels = p_lev;
}

Graph::Graph(int V)
{
    this->V = V;
    adj = new list<adj_edge>[V];
    p_levels = 1;
}

void Graph::addEdge(int v, int w, int p)
{
    adj_edge edge(w, p);
    adj[v].push_back(edge); // Add w to v’s list.
}

void Graph::addEdge(edge e)
{
    adj_edge edge(e.end, e.weight);
    adj[e.start].push_back(edge); // Add w to v’s list.
}

// void Graph::eraseEdge(int u, int v) {
// 	list<adj_edge>::iterator i;
//         for (i = adj[u].begin(); i != adj[u].end(); ++i) {
// 	    if ((*i).end == v) {
// 	         //Node n((*i).end , (*i).priority)
// 	         // adj[u].erase(i);
// 	         adj[u].remove(*i);
// 	    }
// 	}
// 	// adj[u].remove(v);
// }

std::set<edge> *Graph::get_orderings_with_priority()
{
    std::set<edge> *result = new std::set<edge>[p_levels];
    for (int v = 0; v < V; v++)
    {
        for (adj_edge n : adj[v])
        {
            edge e = edge(v, n.end);
            result[n.weight].insert(e);
        }
    }
    return result;
}

std::set<edge> Graph::get_orderings()
{
    std::set<edge> result;
    for (int v = 0; v < V; v++)
    {
        for (adj_edge n : adj[v])
        {
            edge e = edge(v, n.end);
            result.insert(e);
        }
    }
    return result;
}

// This function is a variation of DFSUtil() in https://www.geeksforgeeks.org/archives/18212
// finds 1 or 0 edges
std::vector<edge> Graph::findCyclicUtil(int v, bool visited[], bool *recStack, std::vector<edge> back_edges)
{
    if (visited[v] == false)
    {
        // Mark the current node as visited and part of recursion stack
        visited[v] = true;
        recStack[v] = true;

        // Recur for all the vertices adjacent to this vertex
        list<adj_edge>::iterator i;
        for (i = adj[v].begin(); i != adj[v].end(); ++i)
        {
            if (!visited[(*i).end]) // keep looking at neighbours
            {
                back_edges = findCyclicUtil((*i).end, visited, recStack, back_edges);
            }
            else if (recStack[(*i).end]) // found  a back edge
            {
                // printf("recStack, cycle found at %i %i, has weight %i \n", v, (*i).end, (*i).weight);
                edge e(v, (*i).end, (*i).weight);
                back_edges.push_back(e);
            }
        }
    }
    recStack[v] = false; // remove the vertex from recursion stack
    return back_edges;
}

// Finds all back_edges for graph reachable from intial_task
// if initial_task <0, searches whole graph
std::vector<edge> Graph::findAllCycles(int initial_task)
{
    // Mark all the vertices as not visited and not part of recursion stack
    bool *visited = new bool[V];
    bool *recStack = new bool[V];

    for (int i = 0; i < V; i++)
    {
        visited[i] = false;
        recStack[i] = false;
    }

    std::vector<edge> back_edges;
    if (initial_task < 0)
    {
        for (int i = 0; i < V; i++)
        {
            if (visited[i] == false)
            {
                back_edges = findCyclicUtil(i, visited, recStack, back_edges);
            }
        }
    }
    else
    {
        back_edges = findCyclicUtil(initial_task, visited, recStack, back_edges);
    }
    return back_edges;
}

int Graph::findGraphHeight(int root)
{
    bool *visited = new bool[V]{false};
    return findGraphHeightUtil(root, 0, visited);
}

int Graph::findGraphHeightUtil(int node, int height, bool *visited)
{
    if (!(visited[node]))
    {
        visited[node] = true;
        height++;
        int interim_height = height;
        for (adj_edge child : adj[node])
        {
            // printf("height %i  node %i, child%i\n", interim_height, node, child.end);
            interim_height = max(interim_height, findGraphHeightUtil(child.end, height, visited));
        }
        height = max(height, interim_height);
    }
    return height;
}

// A recursive function used by topologicalSort
void Graph::topologicalSortUtil(int v, bool visited[],
                                stack<int> &Stack)
{
    // Mark the current node as visited.
    visited[v] = true;

    // Recur for all the vertices
    // adjacent to this vertex
    list<adj_edge>::iterator i;
    for (i = adj[v].begin(); i != adj[v].end(); ++i)
        if (!visited[(*i).end])
            topologicalSortUtil((*i).end, visited, Stack);

    // Push current vertex to stack
    // which stores result
    Stack.push(v);
}

//  Uses recursive topologicalSortUtil()
stack<int> Graph::topologicalSort()
{
    stack<int> Stack;

    // Mark all the vertices as not visited
    bool *visited = new bool[V];
    for (int i = 0; i < V; i++)
        visited[i] = false;

    // Call the recursive helper function to store Topological
    // Sort starting from all vertices one by one
    for (int i = 0; i < V; i++)
        if (visited[i] == false)
            topologicalSortUtil(i, visited, Stack);
    return Stack;
}

// Prints shortest paths from src to all other vertices
int *Graph::shortestPath(int src, int end)
{
    // Create a priority queue to store vertices that
    // are being preprocessed. This is weird syntax in C++.
    // Refer below link for details of this syntax
    // https://www.geeksforgeeks.org/implement-min-heap-using-stl/
    priority_queue<iPair, vector<iPair>, greater<iPair>> pq;

    // Create a vector for distances and initialize all
    // distances as infinite (INF)
    // int INF = 9999999999;
    vector<int> dist(V, 99999);
    int *prev = (int *)malloc(V * sizeof(int)); // int prev[V] = {-1};  // previous node, possibly none if no path
    for (int i = 0; i < V; i++)
    {
        prev[i] = -1;
    }

    // Insert source itself in priority queue and initialize
    // its distance as 0.
    pq.push(make_pair(0, src));
    dist[src] = 0;

    vector<bool> f(V, false);

    /* Looping till priority queue becomes empty (or all
    distances are not finalized) */
    while (!pq.empty())
    {
        // The first vertex in pair is the minimum distance vertex, extract it from priority queue.
        // vertex label is stored in second of pair (to keep the vertices sorted by distance,
        // distance must be first item in pair)
        int u = pq.top().second;
        pq.pop();
        f[u] = true;

        // if we've found any path to the end, return
        if (u == end)
        {
            return prev;
        }

        // 'i' is used to get all adjacent vertices of a vertex
        list<adj_edge>::iterator i;
        for (i = adj[u].begin(); i != adj[u].end(); ++i)
        {
            // Get vertex label and weight of current adjacent of u.
            int v = (*i).end;
            int weight = (*i).weight;

            // If there is shorted path to v through u.
            if (f[v] == false && dist[v] > dist[u] + weight)
            {
                // record that shortest path to v is from neighbour u
                prev[v] = u;
                // Updating distance of v
                dist[v] = dist[u] + weight;
                pq.push(make_pair(dist[v], v));
            }
        }
    }

    // Print shortest distances stored in dist[]
    //	printf("Vertex Distance from Source\n");
    //	for (int i = 0; i < V; ++i)
    //		printf("%d \t\t %d\n", i, dist[i]);

    return prev;
}

std::set<edge> Graph::find_path(int *prev, int src, int dest, std::set<edge> edges)
{
    int neighbour = dest;
    vector<int> path;
    // at least one path
 
    while (neighbour != src)
    {    
        path.push_back(neighbour);
        neighbour = prev[neighbour];
        if (neighbour == -1)
        {
            std::set<edge> no_path;
            return no_path;
        }
    }
    path.push_back(src); // path from dest to src

    // edges connecting src to dest
    for (int i = path.size() - 2; i >= 0; i--)
    {
        int start = path[i + 1];
        int end = path[i];
        // TODO: find priority of edge
        for (adj_edge e1 : adj[start])
        {
            if (e1.end == end)
            {                
                edge e = edge(start, end, e1.weight);                
                edges.insert(e);
            }
        }
    }
    return edges;
}

std::set<edge> delete_edge(std::set<edge> edges, edge e)
{
    std::set<edge>::iterator iter = edges.find(e);
    if (iter != edges.end())
    {
        edges.erase(iter);
    }
    //     std::set<edge>::iterator place_to_delete;
    // for (std::set<edge>::iterator iter = edges.begin(); iter != edges.end(); ++iter)
    // {
    //     if (*iter == e)
    //     {
    //         place_to_delete = iter;
    //     }
    // }
    // edges.erase(place_to_delete);
    return edges;
}

// V is number of nodes
// REQUIRES A WELL-FORMED SET OF EDGES, (E.G., NO REPEATS WITH DIFFERING PRIORITY)
std::set<edge> break_cycle(std::set<edge> edges, int V)
{
    // for each back edge
    //   1) delete back edge between the 2 nodes OR
    //   2) delete other path between the 2 nodes
    // repeat until no more cycles can be found
    std::vector<edge> back_edges = {edge(-1, -1, -1)};
    do
    {
        //  make (or re-make) graph out of remaining edges
        Graph gr(V);
        for (edge e : edges)
            gr.addEdge(e);

        // finds all back edges that leads back to a previously seen node
        back_edges = gr.findAllCycles(-1);
        for (edge back_edge : back_edges)
        {
            // printf("back edge found: (%i, %i) weight %i\n", back_edge.start, back_edge.end, back_edge.weight);
            // deletes back_edge from edges (if edge is not required) 
            if (back_edge.weight != 0)
            {
                edges = delete_edge(edges, back_edge);
            }
            // else find the rest of the cycle, and delete one of their edges
            else
            {
                // find other edges of the cycle
                int *prev = gr.shortestPath(back_edge.end, back_edge.start);

                std::set<edge> back_path;  // back_path is not being discovered correctly
                back_path = gr.find_path(prev, back_edge.end, back_edge.start, back_path);
                
                // select a non-required edge from the cycle and delete it
                if (back_path.size() > 0)
                {
                    // find all the non-required edges
                    std::vector<edge> non_req_edges;
                    for (std::set<edge>::iterator iter = back_path.begin(); iter != back_path.end(); ++iter)
                    {
                        if ((*iter).weight != 0)
                        {
                            non_req_edges.push_back(*iter);
                        }
                    }

                    if (non_req_edges.size() > 0)
                    {
                        // pick a random non-required edge
                        int rand_idx = std::rand() % non_req_edges.size();
                        std::vector<edge> non_req_edges_vec = std::vector<edge>(non_req_edges.begin(), non_req_edges.end());
                        edge rand_edge = non_req_edges_vec[rand_idx];

                        //  and delete it
                        edges = delete_edge(edges, rand_edge);
                    }
                    else
                    {
                        printf("other edges in cycle");
                        print(back_path); 
                        
                        printf("all edges in graph/method");                    
                        print(edges);
                        printf("\n");
                        printf("The required edges form a cycle - it is impossible to linearize this method effectively\n");
                    }
                } else {
                    printf("No back path - are you sure you found a cycle?");
                }
                // printf("random edge deleted (%i, %i)\n", rand_edge.start, rand_edge.end);
            }
        }
    } while (back_edges.size() > 0);
    return edges;
}

int main____()
{
    std::set<edge> test_edges_1;
    // test_edges_1.insert(edge(0, 1, 1));
    // test_edges_1.insert(edge(0, 2, 0));
    // test_edges_1.insert(edge(1, 3, 0));
    // test_edges_1.insert(edge(2, 3, 0));

    test_edges_1.insert(edge(0, 1, 0));
    test_edges_1.insert(edge(1, 2, 1));
    test_edges_1.insert(edge(2, 3, 1));

    test_edges_1.insert(edge(3, 0, 0));
    test_edges_1.insert(edge(1, 5, 1));
    test_edges_1.insert(edge(5, 3, 1));
    // test_edges_1.insert(edge(3, 4, 1));
    // test_edges_1.insert(edge(4, 5, 0));
    // test_edges_1.insert(edge(5, 3, 0));

    // test_edges_1.insert(edge(0, 1, 0));
    // test_edges_1.insert(edge(1, 2, 1)); // delete
    // test_edges_1.insert(edge(2, 0, 0));

    // test_edges_1.insert(edge(1, 3, 1)); // alt path
    // test_edges_1.insert(edge(3, 2, 1));
    Graph g(6);
    for (edge e : test_edges_1)
    {
        g.addEdge(e);
    }
  
   std::vector<edge> back_edges = g.findAllCycles(-1); //
   print(back_edges);
   printf("\n");
    std::set<edge> new_edges = break_cycle(test_edges_1, 6);
    print(new_edges);


    Graph g2(6);
    for (edge e : new_edges)
    {
       g2.addEdge(e);
    }
    
    stack<int> Stack = g2.topologicalSort();

       // return topological ordering in adj matrix format
       while (Stack.empty() == false)
       {
              int node = Stack.top();
              printf("%i ", node);
              Stack.pop();
       } 
    // int height = g.findGraphHeight(0);
    // printf("graph heigth %i\n", height);

    // std::vector<edge> back_edges = g.findAllCycles(-1); //
    // printf("back edges in new graph: ");
    // print(back_edges);
    return 0;
}

int main__()
{
    // intialize graph edges
    std::set<edge> test_edges_1;
    test_edges_1.insert(edge(0, 1, 1));
    test_edges_1.insert(edge(1, 2, 0));
    test_edges_1.insert(edge(2, 3, 0));
    test_edges_1.insert(edge(3, 4, 0));
    test_edges_1.insert(edge(2, 1, 0));
    test_edges_1.insert(edge(1, 5, 0));
    Graph g(7);
    for (edge e : test_edges_1)
    {
        g.addEdge(e);
    }
    int height = g.findGraphHeight(0);
    printf("graph heigth %i\n", height);

    // std::set<edge> new_edges = break_cycle(test_edges_1, 6);
    // printf("edges in new graph: ");
    // print(new_edges); //
    return 0;
}

// int main_()
// {
//     for (int ii = 0; ii < 2; ii++)
//     {
//         if (ii == 0)
//         {
//             // intialize graph edges
//             std::set<edge> test_edges_1;
//             test_edges_1.insert(edge(0, 1, 0)); // perma
//             test_edges_1.insert(edge(1, 0, 1)); // perma
//             test_edges_1.insert(edge(0, 1, 1)); // not added

//             std::set<edge> new_edges = break_cycle(test_edges_1, 6);
//             printf("edges in new graph: ");
//             print(new_edges);
//         }
//         else
//         {
//             // intialize graph edges
//             std::set<edge> test_edges_1;
//             test_edges_1.insert(edge(1, 0, 0));
//             test_edges_1.insert(edge(0, 1, 1));
//             test_edges_1.insert(edge(1, 0, 1)); // not added

//             std::set<edge> new_edges = break_cycle(test_edges_1, 6);
//             printf("edges in new graph: part 2 ");
//             print(new_edges);
//         }
//     }

//     return 0;
// }
