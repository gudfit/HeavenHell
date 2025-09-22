#include <iostream>
#include <vector>
#include <string>
#include <numeric>
#include <algorithm>
#include <random>
#include <map>

// Simulation parameters
const int NUM_VERTICES = 50;    // Total number of services (V)
const int HUB_NODE = 0;         // The control plane node (g)
const double EDGE_PROBABILITY = 0.1; // Chance of a dependency between any two non-hub services
const int MAX_NON_HUB_WEIGHT = 10; // Max w(u,v) for u != g
const int SWEEP_W_MAX = 150;     // Max hub broadcast weight (W) to test
const int ASYNC_TRIALS = 100;   // Number of random schedules to average for async success

// As per the Coq definitions: Inductive State := Glory | Gnash.
enum class State {
    Glory,
    Gnash
};

std::string to_string(State s) {
    return (s == State::Glory) ? "Glory" : "Gnash";
}

// Represents the graph V and weights w
struct Graph {
    int num_vertices;
    std::vector<std::vector<int>> weights;

    Graph(int n) : num_vertices(n), weights(n, std::vector<int>(n, 0)) {}
};

// Definition sum_all (f:V->nat) := ...
// (Helper, not directly used in main logic but concept is here)

// Definition statef := V -> State.
using StateF = std::vector<State>;

// Definition score (s:statef) (x:State) (v:V) : nat :=
//   sum_all (fun u => w u v * ind (state_eqb (s u) x)).
int score(const StateF& s, State x, int v, const Graph& graph) {
    int total_score = 0;
    for (int u = 0; u < graph.num_vertices; ++u) {
        total_score += graph.weights[u][v] * ((s[u] == x) ? 1 : 0);
    }
    return total_score;
}

// Definition force_g (s:statef) : statef := fun u => if dec u g then Glory else s u.
StateF force_g(const StateF& s, int g_node) {
    StateF s_prime = s;
    s_prime[g_node] = State::Glory;
    return s_prime;
}

// Definition next_heaven (s:statef) (v:V) : State := ...
State next_heaven(const StateF& s, int v, const Graph& graph, int g_node) {
    if (v == g_node) {
        return State::Glory;
    }
    // let s' := force_g s
    StateF s_prime = force_g(s, g_node);
    // let SG := score s' Glory v
    int score_glory = score(s_prime, State::Glory, v, graph);
    // let SN := score s' Gnash v
    int score_gnash = score(s_prime, State::Gnash, v, graph);
    // if Nat.ltb SG SN then Gnash else Glory
    return (score_glory < score_gnash) ? State::Gnash : State::Glory;
}

// Definition rest_weight (v:V) : nat := sum_all (fun u => if dec u g then 0 else w u v).
int rest_weight(int v, const Graph& graph, int g_node) {
    int total_weight = 0;
    for (int u = 0; u < graph.num_vertices; ++u) {
        if (u == g_node) continue;
        total_weight += graph.weights[u][v];
    }
    return total_weight;
}

// Definition hub_weight (v:V) : nat := w g v.
int hub_weight(int v, const Graph& graph, int g_node) {
    return graph.weights[g_node][v];
}

// --- Demo Implementation ---

Graph generate_random_graph(int n, int g_node, double p, int max_w) {
    Graph graph(n);
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_real_distribution<> dis(0.0, 1.0);
    std::uniform_int_distribution<> weight_dist(1, max_w);

    for (int u = 0; u < n; ++u) {
        if (u == g_node) continue;
        for (int v = 0; v < n; ++v) {
            if (v == g_node) continue;
            if (u == v) continue;
            if (dis(gen) < p) {
                graph.weights[u][v] = weight_dist(gen);
            }
        }
    }
    return graph;
}

int main() {
    // 1. Build a random dependency graph
    Graph graph = generate_random_graph(NUM_VERTICES, HUB_NODE, EDGE_PROBABILITY, MAX_NON_HUB_WEIGHT);

    // Calculate max_rest for this graph topology. This is a fixed property of the graph.
    // Definition max_rest : nat := list_max (map rest_weight nonhubs).
    int max_rest = 0;
    for (int v = 0; v < NUM_VERTICES; ++v) {
        if (v == HUB_NODE) continue;
        int rw = rest_weight(v, graph, HUB_NODE);
        if (rw > max_rest) {
            max_rest = rw;
        }
    }

    // Print CSV header
    std::cout << "W,max_rest,percent_glory_sync,success_prob_async" << std::endl;

    // 2. Sweep hub weight W and show the phase transition
    for (int W = 0; W <= SWEEP_W_MAX; ++W) {
        // Set uniform hub weight: forall v, v <> g -> hub_weight v = W
        for (int v = 0; v < NUM_VERTICES; ++v) {
            if (v != HUB_NODE) {
                graph.weights[HUB_NODE][v] = W;
            }
        }

        // --- Sync update simulation ---
        // Start with all non-hubs in Gnash state
        StateF initial_state(NUM_VERTICES, State::Gnash);
        initial_state[HUB_NODE] = State::Glory;

        StateF next_sync_state = initial_state;
        int glory_count = 0;
        for (int v = 0; v < NUM_VERTICES; ++v) {
            if (v == HUB_NODE) continue;
            next_sync_state[v] = next_heaven(initial_state, v, graph, HUB_NODE);
            if (next_sync_state[v] == State::Glory) {
                glory_count++;
            }
        }
        double percent_glory_sync = (double)glory_count / (NUM_VERTICES - 1);

        // --- Async update simulation ---
        // Corresponds to: async_one_pass_all_G_nonhub
        int successful_trials = 0;
        std::vector<int> non_hubs;
        for(int i = 0; i < NUM_VERTICES; ++i) {
            if (i != HUB_NODE) non_hubs.push_back(i);
        }

        std::random_device rd;
        std::mt19937 g(rd());

        for (int i = 0; i < ASYNC_TRIALS; ++i) {
            StateF async_state = initial_state;
            std::shuffle(non_hubs.begin(), non_hubs.end(), g); // Random update order

            for (int v : non_hubs) {
                async_state[v] = next_heaven(async_state, v, graph, HUB_NODE);
            }

            bool all_glory = true;
            for (int v : non_hubs) {
                if (async_state[v] != State::Glory) {
                    all_glory = false;
                    break;
                }
            }
            if (all_glory) {
                successful_trials++;
            }
        }
        double success_prob_async = (double)successful_trials / ASYNC_TRIALS;

        // Print results for this W
        std::cout << W << "," << max_rest << "," << percent_glory_sync << "," << success_prob_async << std::endl;
    }

    return 0;
}
