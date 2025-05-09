#include <iostream>
#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <algorithm>
#include <random>
#include <chrono>
#include <memory>
#include <fstream>
#include <future>
#include <sstream>
#include <iomanip>
#include <limits>

using namespace std;
using namespace std::chrono;

// Literal representation: positive integers for variables, negative for their negations
using Literal = int;
using Clause = unordered_set<Literal>;
using CNF = vector<Clause>;

// Statistics structure
struct Stats {
    size_t decisions = 0;
    size_t unit_propagations = 0;
    size_t pure_eliminations = 0;
    size_t conflicts = 0;
    size_t clauses_learned = 0;
    size_t max_depth = 0;
    size_t memory_usage = 0;
    duration<double> runtime{0};

    void reset() {
        decisions = 0;
        unit_propagations = 0;
        pure_eliminations = 0;
        conflicts = 0;
        clauses_learned = 0;
        max_depth = 0;
        memory_usage = 0;
        runtime = duration<double>(0);
    }

    void print() const {
        cout << "Decisions: " << decisions << "\n";
        cout << "Unit propagations: " << unit_propagations << "\n";
        cout << "Pure eliminations: " << pure_eliminations << "\n";
        cout << "Conflicts: " << conflicts << "\n";
        cout << "Clauses learned: " << clauses_learned << "\n";
        cout << "Max depth: " << max_depth << "\n";
        cout << "Memory usage: ~" << memory_usage / 1024 << " KB\n";
        cout << "Runtime: " << runtime.count() << " seconds\n";
    }
};

// Base SAT solver class
class SATSolver {
protected:
    Stats stats;
    CNF cnf;
    unordered_map<Literal, bool> assignment;
    vector<Literal> decision_stack;

    virtual bool solve_impl() = 0;

    bool is_unit_clause(const Clause& clause) const {
        return clause.size() == 1;
    }

    bool is_empty_clause(const Clause& clause) const {
        return clause.empty();
    }

    bool is_satisfied(const Clause& clause) const {
        for (Literal lit : clause) {
            if (assignment.count(abs(lit)) && (assignment.at(abs(lit)) == (lit > 0))) {
                return true;
            }
        }
        return false;
    }

    bool is_conflicting(const Clause& clause) const {
        for (Literal lit : clause) {
            if (!assignment.count(abs(lit)) || (assignment.at(abs(lit)) != (lit > 0))) {
                return false;
            }
        }
        return true;
    }

    void simplify_cnf() {
        bool changed = true;
        while (changed) {
            changed = false;

            for (auto it = cnf.begin(); it != cnf.end(); ) {
                Clause simplified_clause;
                Literal unit_lit = 0;
                bool all_false = true;
                for (Literal lit : *it) {
                    if (assignment.count(abs(lit))) {
                        if (assignment.at(abs(lit)) == (lit > 0)) {
                            it = cnf.erase(it);
                            changed = true;
                            goto next_clause_simplify;
                        }
                    } else {
                        all_false = false;
                        simplified_clause.insert(lit);
                        if (simplified_clause.size() == 1) {
                            unit_lit = *simplified_clause.begin();
                        }
                    }
                }

                if (all_false && !it->empty()) {
                    it = cnf.erase(it);
                    changed = true;
                    goto next_clause_simplify;
                } else if (simplified_clause.empty() && !it->empty()) {
                    it = cnf.erase(it);
                    changed = true;
                    goto next_clause_simplify;
                } else if (unit_lit != 0 && simplified_clause.size() == 1) {
                    assign_literal(unit_lit, false);
                    it = cnf.erase(it);
                    stats.unit_propagations++;
                    changed = true;
                    goto next_clause_simplify;
                } else {
                    *it = simplified_clause;
                    ++it;
                }
                next_clause_simplify:;
            }

            // Pure literal elimination
            unordered_map<Literal, bool> polarity;
            unordered_set<Literal> unassigned_vars;
            for (const Clause& clause : cnf) {
                for (Literal lit : clause) {
                    if (!assignment.count(abs(lit))) {
                        unassigned_vars.insert(abs(lit));
                        if (polarity.find(abs(lit)) == polarity.end()) {
                            polarity[abs(lit)] = (lit > 0);
                        } else if (polarity[abs(lit)] != (lit > 0)) {
                            polarity[abs(lit)] = true;
                        }
                    }
                }
            }

            for (Literal var : unassigned_vars) {
                if (polarity.count(var)) {
                    bool pure_positive = true;
                    bool pure_negative = true;
                    for (const Clause& clause : cnf) {
                        if (clause.count(var)) pure_negative = false;
                        if (clause.count(-var)) pure_positive = false;
                    }

                    if (pure_positive) {
                        assign_literal(var, false);
                        stats.pure_eliminations++;
                        changed = true;
                    } else if (pure_negative) {
                        assign_literal(-var, false);
                        stats.pure_eliminations++;
                        changed = true;
                    }
                }
            }

        }
    }

    void assign_literal(Literal lit, bool is_decision) {
        bool value = lit > 0;
        assignment[abs(lit)] = value;
        if (is_decision) {
            decision_stack.push_back(lit);
            stats.max_depth = max(stats.max_depth, decision_stack.size());
        }
    }

    void unassign_literal(Literal lit) {
        assignment.erase(abs(lit));
        for (auto it = decision_stack.rbegin(); it != decision_stack.rend(); ++it) {
            if (abs(*it) == abs(lit)) {
                decision_stack.erase(next(it).base());
                break;
            }
        }
    }

    void backtrack() {
        if (!decision_stack.empty()) {
            Literal last_decision = decision_stack.back();
            unassign_literal(last_decision);
            assign_literal(-last_decision, true);
        }
    }

public:
    bool solve(const CNF& input_cnf) {
        auto start = high_resolution_clock::now();
        stats.reset();
        cnf = input_cnf;
        assignment.clear();
        decision_stack.clear();

        bool result = solve_impl();

        auto end = high_resolution_clock::now();
        stats.runtime = end - start;

        stats.memory_usage = sizeof(*this) +
                            cnf.size() * sizeof(Clause) +
                            assignment.size() * sizeof(pair<Literal, bool>) +
                            decision_stack.size() * sizeof(Literal);

        return result;
    }

    const Stats& get_stats() const { return stats; }
    const unordered_map<Literal, bool>& get_assignment() const { return assignment; }
};

// Resolution-based solver
class ResolutionSolver : public SATSolver {
protected:
    bool solve_impl() override {
        size_t last_size = 0;
        const size_t max_iterations = 2000;
        size_t iterations = 0;

        while (iterations++ < max_iterations) {
            simplify_cnf();

            if (cnf.empty()) return true;

            bool has_empty = any_of(cnf.begin(), cnf.end(),
                [](const Clause& c) { return c.empty(); });
            if (has_empty) return false;

            if (cnf.size() == last_size) return true;
            last_size = cnf.size();

            bool resolution_applied = false;
            size_t current_size = cnf.size();
            for (size_t i = 0; i < current_size; ++i) {
                for (size_t j = i + 1; j < current_size; ++j) {
                    Clause resolvent = resolve(cnf[i], cnf[j]);
                    if (!resolvent.empty()) {
                        bool exists = false;
                        for (const Clause& c : cnf) {
                            if (c == resolvent) {
                                exists = true;
                                break;
                            }
                        }
                        if (!exists) {
                            cnf.push_back(resolvent);
                            resolution_applied = true;
                            stats.clauses_learned++;
                            if (resolvent.empty()) return false;
                        }
                    }
                }
            }
            if (!resolution_applied) return true;
        }
        return false;
    }

    Clause resolve(const Clause& c1, const Clause& c2) {
        Clause resolvent;
        Literal complementary = 0;
        size_t complementary_count = 0;

        for (Literal lit : c1) {
            if (c2.count(-lit)) {
                complementary = lit;
                complementary_count++;
                if (complementary_count > 1) return {};
            }
        }

        if (complementary_count != 1) return {};

        for (Literal lit : c1) if (lit != complementary) resolvent.insert(lit);
        for (Literal lit : c2) if (lit != -complementary) resolvent.insert(lit);

        return resolvent;
    }
};

// DP (Davis-Putnam) solver
class DPSolver : public SATSolver {
protected:
    bool solve_impl() override {
        simplify_cnf();

        if (cnf.empty()) return true;
        for (const Clause& clause : cnf) {
            if (clause.empty()) {
                stats.conflicts++;
                return false;
            }
        }

        Literal var = select_variable();
        if (var == 0) return true;

        stats.decisions++;

        CNF new_cnf_pos = cnf;
        new_cnf_pos.push_back({var});
        DPSolver solver_pos;
        if (solver_pos.solve(new_cnf_pos)) {
            assignment.insert(solver_pos.get_assignment().begin(), solver_pos.get_assignment().end());
            return true;
        }

        CNF new_cnf_neg = cnf;
        new_cnf_neg.push_back({-var});
        DPSolver solver_neg;
        if (solver_neg.solve(new_cnf_neg)) {
            assignment.insert(solver_neg.get_assignment().begin(), solver_neg.get_assignment().end());
            return true;
        }

        return false;
    }

    Literal select_variable() const {
        unordered_set<Literal> assigned;
        for (const auto& [var, _] : assignment) {
            assigned.insert(var);
        }

        unordered_map<Literal, size_t> freq;
        for (const Clause& clause : cnf) {
            for (Literal lit : clause) {
                Literal var = abs(lit);
                if (!assigned.count(var)) {
                    freq[var]++;
                }
            }
        }

        if (freq.empty()) return 0;

        return max_element(freq.begin(), freq.end(),
                           [](const auto& a, const auto& b) { return a.second < b.second; })->first;
    }
};

// DPLL (Davis-Putnam-Logemann-Loveland) solver
class DPLLSolver : public SATSolver {
protected:
    bool solve_impl() override {
        stats.max_depth = max(stats.max_depth, decision_stack.size());
        simplify_cnf();

        if (cnf.empty()) {
            return true;
        }
        for (const Clause& clause : cnf) {
            if (clause.empty()) {
                stats.conflicts++;
                return false;
            }
        }

        Literal decision_lit = select_literal();
        if (decision_lit == 0) {
            return true;
        }
        stats.decisions++;

        assign_literal(decision_lit, true);
        if (solve_impl()) {
            return true;
        }
        unassign_literal(decision_lit);

        assign_literal(-decision_lit, true);
        if (solve_impl()) {
            return true;
        }
        unassign_literal(-decision_lit);

        return false;
    }

    Literal select_literal() const {
        unordered_set<Literal> assigned_vars;
        for (const auto& [var, _] : assignment) {
            assigned_vars.insert(var);
        }

        if (cnf.empty()) return 0;

        size_t min_size = numeric_limits<size_t>::max();
        for (const Clause& clause : cnf) {
            size_t unassigned_count = 0;
            for (Literal lit : clause) {
                if (!assigned_vars.count(abs(lit))) {
                    unassigned_count++;
                }
            }
            if (unassigned_count > 0 && unassigned_count < min_size) {
                min_size = unassigned_count;
            }
        }

        unordered_map<Literal, size_t> counts;
        for (const Clause& clause : cnf) {
            size_t unassigned_count = 0;
            for (Literal lit : clause) {
                if (!assigned_vars.count(abs(lit))) {
                    counts[lit]++;
                }
            }
            if (unassigned_count == min_size) {
                for (Literal lit : clause) {
                    if (!assigned_vars.count(abs(lit))) {
                        counts[lit]++;
                    }
                }
            }
        }

        if (!counts.empty()) {
            auto it = max_element(counts.begin(), counts.end(),
                                 [](const auto& a, const auto& b) { return a.second < b.second; });
            if (it != counts.end()) {
                return it->first;
            }
        }

        for (const Clause& clause : cnf) {
            for (Literal lit : clause) {
                if (!assigned_vars.count(abs(lit))) {
                    return lit;
                }
            }
        }

        return 0;
    }
};

// Test case generator
class TestGenerator {
public:
    static CNF generate_random_k_sat(size_t num_vars, size_t num_clauses, size_t k, double neg_prob = 0.5) {
        CNF cnf;
        random_device rd;
        mt19937 gen(rd());
        uniform_int_distribution<size_t> var_dist(1, num_vars);
        bernoulli_distribution neg_dist(neg_prob);

        for (size_t i = 0; i < num_clauses; ++i) {
            Clause clause;
            while (clause.size() < k) {
                Literal var = var_dist(gen);
                Literal lit = neg_dist(gen) ? -var : var;
                clause.insert(lit);
            }
            cnf.push_back(clause);
        }

        return cnf;
    }

    static CNF generate_unsatisfiable_problem(size_t num_vars) {
        CNF cnf;
        vector<Literal> vars;
        for (size_t i = 1; i <= num_vars; ++i) {
            vars.push_back(i);
        }

        // Generate all possible 2^num_vars clauses
        for (size_t mask = 0; mask < (1 << num_vars); ++mask) {
            Clause clause;
            for (size_t i = 0; i < num_vars; ++i) {
                if (mask & (1 << i)) {
                    clause.insert(vars[i]);
                } else {
                    clause.insert(-vars[i]);
                }
            }
            cnf.push_back(clause);
        }

        return cnf;
    }

    static CNF load_from_file(const string& filename) {
        CNF cnf;
        ifstream file(filename);
        string line;

        while (getline(file, line)) {
            if (line.empty() || line[0] == 'c' || line[0] == 'p') continue;

            istringstream iss(line);
            Clause clause;
            Literal lit;
            while (iss >> lit && lit != 0) {
                clause.insert(lit);
            }
            if (!clause.empty()) {
                cnf.push_back(clause);
            }
        }

        return cnf;
    }

    static void save_to_file(const CNF& cnf, const string& filename) {
        ofstream file(filename);
        file << "p cnf " << count_variables(cnf) << " " << cnf.size() << "\n";
        for (const Clause& clause : cnf) {
            for (Literal lit : clause) {
                file << lit << " ";
            }
            file << "0\n";
        }
    }

    static size_t count_variables(const CNF& cnf) {
        unordered_set<Literal> vars;
        for (const Clause& clause : cnf) {
            for (Literal lit : clause) {
                vars.insert(abs(lit));
            }
        }
        return vars.size();
    }
};

void print_cnf(const CNF& cnf) {
    for (const Clause& clause : cnf) {
        cout << "(";
        bool first = true;
        for (Literal lit : clause) {
            if (!first) cout << " v ";
            first = false;
            if (lit < 0) cout << "!";
            cout << abs(lit);
        }
        cout << ")";
        if (&clause != &cnf.back()) cout << " ^ ";
    }
    cout << endl;
}

void compare_solvers(const CNF& cnf) {
    cout << "Solving CNF with " << cnf.size() << " clauses and "
         << TestGenerator::count_variables(cnf) << " variables\n";

    vector<unique_ptr<SATSolver>> solvers;
    solvers.push_back(make_unique<ResolutionSolver>());
    solvers.push_back(make_unique<DPSolver>());
    solvers.push_back(make_unique<DPLLSolver>());

    vector<string> names = {"Resolution", "DP", "DPLL"};

    for (size_t i = 0; i < solvers.size(); ++i) {
        cout << "\n=== " << names[i] << " Solver ===\n";
        try {
            auto start = high_resolution_clock::now();

            future<bool> result = async(launch::async, [&]{
                return solvers[i]->solve(cnf);
            });

            if (result.wait_for(chrono::seconds(5)) != future_status::ready) {
                cout << "TIMEOUT after 5 seconds\n";
            }

            bool sat_result = result.get();
            auto end = high_resolution_clock::now();

            cout << "Result: " << (sat_result ? "SATISFIABLE" : "UNSATISFIABLE") << "\n";
            if (sat_result) {
                cout << "Assignment: ";
                for (const auto& [var, val] : solvers[i]->get_assignment()) {
                    cout << var << "=" << (val ? "T" : "F") << " ";
                }
                cout << "\n";
            }

            solvers[i]->get_stats().print();
            cout << "Total time: " << duration_cast<milliseconds>(end - start).count() << " ms\n";

        } catch (const exception& e) {
            cout << "Error: " << e.what() << "\n";
        } catch (...) {
            cout << "Unknown error occurred\n";
        }
    }
}

int main() {


    cout << "\nRandom Test Case\n";
    CNF random_cnf = TestGenerator::generate_random_k_sat(10, 20, 3);
    print_cnf(random_cnf);
    compare_solvers(random_cnf);

/*
    cout << "\n=== Harder 3-SAT Test Case ===\n";
    CNF hard_cnf = TestGenerator::generate_random_k_sat(20, 100, 3);
    compare_solvers(hard_cnf);

    cout << "\n=== Small Unsatisfiable Problem ===\n";
    CNF unsat_cnf = TestGenerator::generate_unsatisfiable_problem(3);
    compare_solvers(unsat_cnf);
*/
    return 0;
}





