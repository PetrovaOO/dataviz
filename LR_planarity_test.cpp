#define _CRT_SECURE_NO_WARNINGS

#include <iostream>
#include <string>
#include <fstream>
#include <algorithm>
#include <vector>
#include <stack>
#define mp make_pair

using namespace std;

int INF = 1e9;

struct edge {
  int u, v; // u ~ 'from', v ~ 'to'
  int prev, next; // prev (next) - index of previous (next) edge in adjacency list for vertex u 

  edge(int u_, int v_, int prev_ = -1, int next_ = -1) :
    u(u_), v(v_), prev(prev_), next(next_) {}

  edge() {}
};

struct interval {
  int high_edge_ind, low_edge_ind;

  interval(int high_edge_ind_ = -1, int low_edge_ind_ = -1) :
    high_edge_ind(high_edge_ind_), low_edge_ind(low_edge_ind_) {}

  bool empty() {
    return high_edge_ind == -1 && low_edge_ind == -1;
  }
};

struct conflict {
  interval L, R;

  conflict(interval L_ = interval(), interval R_ = interval()) :
    L(L_), R(R_) {}

  bool empty() {
    return L.empty() && R.empty();
  }
};

bool operator==(const interval& I1, const interval& I2) {
  return I1.high_edge_ind == I2.high_edge_ind && I1.low_edge_ind == I2.low_edge_ind;
}

bool operator==(const conflict& P, const conflict& Q) {
  return P.L == Q.L && P.R == Q.R;
}


vector <edge> E; // List of all orient edges
vector <int> g_roots; // Index (in E) of the first edge exiting vertex (-1 if adjacency list of vertex is empty)

vector <int> height;
vector <int> parent;

vector <int> lowpt;
vector <int> lowpt2;
vector <int> nesting_depth;

vector <int> ref_edge;
vector <int> side;

void orient(int e_ind) {
  int v = E[e_ind].v;
  if (E[e_ind ^ 1].prev != -1) {
    E[E[e_ind ^ 1].prev].next = E[e_ind ^ 1].next;
  }
  else {
    g_roots[v] = E[e_ind ^ 1].next;
  }
  if (E[e_ind ^ 1].next != -1) {
    E[E[e_ind ^ 1].next].prev = E[e_ind ^ 1].prev;
  }
}

void DFS1(int u) {
  int e_ind = parent[u];
  int cur_e_ind = g_roots[u];
  while (cur_e_ind != -1) {
    orient(cur_e_ind);
    lowpt[cur_e_ind] = height[u];
    int v = E[cur_e_ind].v;
    if (height[v] == INF) {
      parent[v] = cur_e_ind;
      height[v] = height[u] + 1;
      DFS1(v);
    }
    else {
      lowpt[cur_e_ind] = height[v];
    }

    nesting_depth[cur_e_ind] = 2 * lowpt[cur_e_ind];
    if (lowpt[cur_e_ind] < height[u]) {
      nesting_depth[cur_e_ind] += 1;
    }

    if (e_ind != -1) {
      if (lowpt[cur_e_ind] < lowpt[e_ind]) {
        lowpt2[e_ind] = min(lowpt[e_ind], lowpt2[cur_e_ind]);
        lowpt[e_ind] = lowpt[cur_e_ind];
      }
      else if (lowpt[cur_e_ind] > lowpt[e_ind]) {
        lowpt2[e_ind] = min(lowpt2[e_ind], lowpt[cur_e_ind]);
      }
      else {
        lowpt2[e_ind] = min(lowpt2[e_ind], lowpt2[cur_e_ind]);
      }
    }

    cur_e_ind = E[cur_e_ind].next;
  }
}

stack < conflict > S;
vector < conflict > stack_bottom;
vector <int> lowpt_edge;

void rebuildEdges(int u, int n) { // Ordering outgoing edges of vertex u according to non-decreasing nesting depth. ~'Counting sort' is used.
  int cur_e_ind = g_roots[u];
  vector <vector <int> > nesting_depth_vals(4 * (n + 1));
  while (cur_e_ind != -1) {
    nesting_depth_vals[nesting_depth[cur_e_ind] + 2 * (n + 1)].push_back(cur_e_ind);
    cur_e_ind = E[cur_e_ind].next;
  }
  int prev_e_ind = -1;
  for (int i = 0; i < nesting_depth_vals.size(); ++i) {
    for (int j = 0; j < nesting_depth_vals[i].size(); ++j) {
      cur_e_ind = nesting_depth_vals[i][j];
      if (prev_e_ind == -1) {
        g_roots[u] = cur_e_ind;
        
      }
      else {
        E[prev_e_ind].next = cur_e_ind;
      }
      E[cur_e_ind].prev = prev_e_ind;
      prev_e_ind = cur_e_ind;
    }
  }
  if (prev_e_ind != -1) {
    E[prev_e_ind].next = -1;
  }

}

bool conflicting(interval I, int edge_id) {
  return !I.empty() && lowpt[I.high_edge_ind] > lowpt[edge_id];
}

bool addConstraints(int edge_id, int parent_edge_id) {
  conflict P;
  while(!S.empty() && !(S.top() == stack_bottom[edge_id])) {
    conflict Q = S.top();
    S.pop();
    if (!Q.L.empty()) {
      swap(Q.L, Q.R);
    }
    if (!Q.L.empty()) {
      return false;
    }
    if (lowpt[Q.R.low_edge_ind] > lowpt[parent_edge_id]) {
      if (P.R.empty()) {
        P.R.high_edge_ind = Q.R.high_edge_ind;
      }else {
        ref_edge[P.R.low_edge_ind] = Q.R.high_edge_ind;
      }
      P.R.low_edge_ind = Q.R.low_edge_ind;
    }
    else {
      ref_edge[Q.R.low_edge_ind] = lowpt_edge[parent_edge_id];
    }
  }

  while (conflicting(S.top().L, edge_id) || conflicting(S.top().R, edge_id)) {
    conflict Q = S.top();
    S.pop();
    if (conflicting(Q.R, edge_id)) {
      swap(Q.L, Q.R);
    }
    if (conflicting(Q.R, edge_id)) {
      return false;
    }
    ref_edge[P.R.low_edge_ind] = Q.R.high_edge_ind;
    if (Q.R.low_edge_ind != -1) {
      P.R.low_edge_ind = Q.R.low_edge_ind;
    }
    if (P.L.empty()) {
      P.L.high_edge_ind = Q.L.high_edge_ind;
    }
    else {
      ref_edge[P.L.high_edge_ind] = Q.L.high_edge_ind;
    }
    P.L.low_edge_ind = Q.L.low_edge_ind;
  }

  if (!P.empty()) {
    S.push(P);
  }
  return true;
}

int lowest(conflict& P) {
  if (P.L.empty()) {
    return lowpt[P.R.low_edge_ind];
  }
  if (P.R.empty()) {
    return lowpt[P.L.low_edge_ind];
  }
  return min(lowpt[P.L.low_edge_ind], lowpt[P.R.low_edge_ind]);
}

void Trim(int u) {
  while (!S.empty() && lowest(S.top()) == height[u]) {
    conflict P = S.top();
    S.pop();
    if (P.L.low_edge_ind != -1) {
      side[P.L.low_edge_ind] = -1;
    }
  }
  if(!S.empty()){
    conflict P = S.top();
    S.pop();
    while (P.L.high_edge_ind != -1 && E[P.L.high_edge_ind].v == u) {
      P.L.high_edge_ind = ref_edge[P.L.high_edge_ind];
    }
    if (P.L.high_edge_ind == -1 && P.L.low_edge_ind != -1) {
      ref_edge[P.L.low_edge_ind] = P.R.low_edge_ind;
      side[P.L.low_edge_ind] = -1;
      P.L.low_edge_ind = -1;
    }

    while (P.R.high_edge_ind != -1 && E[P.R.high_edge_ind].v == u) {
      P.R.high_edge_ind = ref_edge[P.R.high_edge_ind];
    }
    if (P.R.high_edge_ind == -1 && P.R.low_edge_ind != -1) {
      ref_edge[P.R.low_edge_ind] = P.L.low_edge_ind;
      side[P.R.low_edge_ind] = -1;
      P.R.low_edge_ind = -1;
    }

    S.push(P);
  }
}

bool DFS2(int u) {
  int parent_e_ind = parent[u];
  int cur_e_ind = g_roots[u];
  while (cur_e_ind != -1) {
    if (!S.empty()) {
      stack_bottom[cur_e_ind] = S.top();
    }
    int v = E[cur_e_ind].v;
    if (parent[v] == cur_e_ind) {
      if (!DFS2(v)) {
        return false;
      }
    }
    else {
      lowpt_edge[cur_e_ind] = cur_e_ind;
      S.push(conflict(interval(-1, -1), interval(cur_e_ind, cur_e_ind)));
    }

    if (lowpt[cur_e_ind] < height[u]) {
      if (cur_e_ind == g_roots[u]) {
        lowpt_edge[parent_e_ind] = lowpt_edge[cur_e_ind];
      }
      else {
        if (!addConstraints(cur_e_ind, parent_e_ind)) {
          return false;
        }
      }
    }
    cur_e_ind = E[cur_e_ind].next;
  }

  if (parent_e_ind != -1) {
    int w = E[parent_e_ind].u;
    Trim(w);

    if (lowpt[parent_e_ind] < height[w]) {
      int h_left_ind = S.top().L.high_edge_ind, h_right_ind = S.top().R.high_edge_ind;
      if (h_left_ind != -1 && 
          (h_right_ind == -1 || lowpt[h_left_ind] > lowpt[h_right_ind])) {
        ref_edge[parent_e_ind] = h_left_ind;
      }
      else {
        ref_edge[parent_e_ind] = h_right_ind;
      }
    }
  }

  return true;
}

int sign(int e_ind) {
  if (ref_edge[e_ind] != -1) {
    side[e_ind] = side[e_ind] * sign(ref_edge[e_ind]);
    ref_edge[e_ind] = -1;
  }
  return side[e_ind];
}

vector <int> leftRef, rightRef;

void addEdgeBefor(int e_ind, int next_e_ind) { // Add edge #(e_ind) befor edge #(next_e_ind) in adjacency list of vertex #(E[next_e_ind].u)
  if (next_e_ind == -1) { // Adjacency list of vertex #(E[e_ind].u) is empty, required to make edge #(e_ind) first
    g_roots[E[e_ind].u] = e_ind;
    return;
  }

  E[e_ind].next = next_e_ind;
  E[e_ind].prev = E[next_e_ind].prev;
  if (E[next_e_ind].prev != -1) {
    E[E[next_e_ind].prev].next = e_ind;
  }
  else { // Edge #(next_e_ind) was a root for vertex #(E[next_e_ind].u)
    g_roots[E[next_e_ind].u] = e_ind;
  }
  E[next_e_ind].prev = e_ind;
}

void addEdgeAfter(int e_ind, int prev_e_ind) { // Add edge #(e_ind) after edge #(prev_e_ind) in adjacency list of vertex #(E[prev_e_ind].u)
  if (prev_e_ind == -1) { // Adjacency list of vertex #(E[e_ind].u) is empty, required to make edge #(e_ind) first
    g_roots[E[e_ind].u] = e_ind;
    return;
  }

  E[e_ind].prev = prev_e_ind;
  E[e_ind].next = E[prev_e_ind].next;
  if (E[prev_e_ind].next != -1) {
    E[E[prev_e_ind].next].prev = e_ind;
  }
  E[prev_e_ind].next = e_ind;
}

vector <bool> ignor_edges;

void DFS3(int u) {
  int cur_e_ind = g_roots[u];
  while (cur_e_ind != -1) {
    if (!ignor_edges[cur_e_ind]) { // Edge #(cur_e_ind) is not freshly added in previous steps
      int v = E[cur_e_ind].v;
      if (cur_e_ind == parent[v]) {
        addEdgeBefor((cur_e_ind ^ 1), g_roots[v]);
        ignor_edges[(cur_e_ind ^ 1)] = true;
        leftRef[u] = rightRef[u] = cur_e_ind;
        DFS3(v);
      }
      else {
        if (side[cur_e_ind] == 1) {
          addEdgeAfter((cur_e_ind ^ 1), rightRef[v]);
          ignor_edges[(cur_e_ind ^ 1)] = true;
        }
        else {
          addEdgeBefor((cur_e_ind ^ 1), leftRef[v]);
          ignor_edges[(cur_e_ind ^ 1)] = true;
          leftRef[v] = (cur_e_ind ^ 1);
        }
      }
    }
    cur_e_ind = E[cur_e_ind].next;
  }
}


void readEdges(int n, int m) {
  g_roots.resize(n, -1);
  E.resize(2 * m);
  int a, b;
  for (int i = 0; i < m; ++i) {
    cin >> a >> b;

    E[2 * i] = edge(a, b, -1, g_roots[a]);
    if (g_roots[a] == -1) {
      g_roots[a] = 2 * i;
    }
    else {
      E[g_roots[a]].prev = 2 * i;
      g_roots[a] = 2 * i;
    }
    
    E[2 * i + 1] = edge(b, a, -1, g_roots[b]);
    if (g_roots[b] == -1) {
      g_roots[b] = 2 * i + 1;
    }
    else {
      E[g_roots[b]].prev = 2 * i + 1;
      g_roots[b] = 2 * i + 1;
    }
  }
}

void printResult(int n) {
  for (int i = 0; i < n; ++i) {
    cout << i << ": ";
    int cur_ind = g_roots[i];
    while (cur_ind != -1) {
      cout << E[cur_ind].v << " ";
      cur_ind = E[cur_ind].next;
    }
    cout << "\n";
  }
}

int main(int argc, char* argv[]) {
  freopen(argv[1], "r", stdin);
  freopen(argv[2], "w", stdout);

  int n, m;
  cin >> n >> m;

  if (n > 2 && m > 3 * n - 6) {
    cout << "Not planar.\n";
    return 0;
  }

  readEdges(n, m);

  lowpt.resize(2 * m, -1);
  lowpt2.resize(2 * m, -1);
  height.resize(n, INF);
  parent.resize(n, -1);
  nesting_depth.resize(2 * m, -1);

  ref_edge.resize(2 * m, -1);
  side.resize(2 * m, 1);
  stack_bottom.resize(2 * m);
  lowpt_edge.resize(2 * m, -1);

  vector <int> roots;

  // orientation
  for (int u = 0; u < n; ++u) {
    if (height[u] == INF) {
      roots.push_back(u);
      height[u] = 0;
      DFS1(u);
    }
  }

  // testing
  for (int u = 0; u < n; ++u) {
    rebuildEdges(u, n);
  }
  for (int u : roots) {
    if (!DFS2(u)) {
      cout << "Not planar.\n";
      return 0;
    }
  }
  
  // embedding
  for (int e_ind = 0; e_ind < E.size(); ++e_ind) {
    nesting_depth[e_ind] = sign(e_ind) * nesting_depth[e_ind];
  }
  for (int u = 0; u < n; ++u) {
    rebuildEdges(u, n);
  }

  leftRef.resize(n);
  rightRef.resize(n);
  ignor_edges.resize(2 * m, false);
  for (int u : roots) {
    DFS3(u);
  }

  printResult(n);

  return 0;
}
