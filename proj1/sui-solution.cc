#include "search-strategies.h"
#include "memusage.h"
#include <queue>
#include <stack>
#include <set>
#include <algorithm>
#include <tuple>
#include <array>
#include <chrono>
#include <utility>

using namespace std::chrono;

bool enough_memory(size_t mem_limit_){
    size_t mem_usage_size = 0;
    size_t remaining_memory = 5000000;
    mem_usage_size = getCurrentRSS();
    return (mem_usage_size + remaining_memory < mem_limit_);
}

struct Node {
    double f = 0;
    int depth = 0;
    std::shared_ptr<SearchState> state;
    std::vector<SearchAction> actions = {};
    Node(double f, int depth, std::vector<SearchAction> actions, std::shared_ptr<SearchState> state)  {
        this->f=f;
        this->depth=depth;
        this->state=std::move(state);
        this->actions=std::move(actions);
    }
};

bool operator==(const SearchState &a, const SearchState &b) {
    return a.state_.stacks == b.state_.stacks && a.state_.homes == b.state_.homes;
}

Node find_in_tuple_vector(const std::vector<Node>& s, SearchState state){
    auto it = std::find_if(s.begin(), s.end(), [&state](const Node& e) {return *e.state == state;});
    if( it != s.end() ) {
        return *it;
    }
    else {
        Node return_node(-1, 0, {}, std::make_shared<SearchState>(state));
        return return_node;
    }
}

std::vector<SearchAction> BreadthFirstSearch::solve(const SearchState &init_state) {
    std::vector<SearchAction> solution;
    std::vector<SearchAction> solution2;
    SearchState working_state(init_state);
    std::deque<std::tuple<SearchState, std::vector<SearchAction>>> state_queue = {};
    SearchState child = working_state;
    std::map<SearchState, std::vector<SearchAction>> visited;

    visited.insert(std::make_pair(working_state, solution));
    state_queue.push_back(std::make_tuple(working_state, solution));

    while(!state_queue.empty()) {
        if (!enough_memory(mem_limit_)) {
            return {};
        }
        std::tuple<SearchState, std::vector<SearchAction>> node = state_queue.front();
        SearchState parent = std::get<0>(node);
        solution = std::get<1>(node);
        state_queue.pop_front();

        auto actions = parent.actions();
        for(auto & action : actions){

            child = action.execute(parent);

            if (child.isFinal()) {
                solution.push_back(action);
                return solution;
            }

            auto it = std::find_if(state_queue.begin(), state_queue.end(), [&](const std::tuple<SearchState, std::vector<SearchAction>> &e) {return std::get<0>(e) == child;});
            if( it != state_queue.end() ) {
                continue;
            }

            try {
                solution2 = visited.at(child);
                continue;
            }catch (const std::out_of_range &e){
                solution2 = solution;
                solution2.push_back(action);
                state_queue.push_back(std::make_tuple(child, solution2));
            }
        }
        visited.insert(std::make_pair(parent, solution));
    }

    return {};
}

std::vector<SearchAction> DepthFirstSearch::solve(const SearchState &init_state) {
    SearchState working_state(init_state);
    std::stack<std::tuple<SearchState, int>> open;
    std::vector<SearchAction> solution = {};
    std::vector<SearchAction> solution_tmp = {};
    SearchState child = working_state;

    std::map<SearchState, std::vector<SearchAction>> visited;

    visited.insert(std::make_pair(child, solution));
    open.push(std::make_tuple(child, 0));

    while (!open.empty()) {
        if (!enough_memory(mem_limit_)) {
            return {};
        }
        SearchState parent = std::get<0>(open.top());
        int current_depth = std::get<1>(open.top());
        open.pop();
        solution = visited[parent];
        current_depth = current_depth + 1;

        if (current_depth > depth_limit_)
            continue;

        for (auto & action: parent.actions()) {
            child = action.execute(parent);

            if (child.isFinal()) {
                solution.push_back(action);
                return solution;
            }

            try {
                solution_tmp = visited.at(child);
            }catch (const std::out_of_range &e){
                solution_tmp = solution;
                solution_tmp.push_back(action);
                open.push(std::make_tuple(child, current_depth));
                visited.insert(std::make_pair(child, solution_tmp));
            }
        }
    }
    return {};
}

bool canSitOn(const Card &base, const Card &candidate) {
    bool oppposing_render_color = render_color_map.at(candidate.color) != render_color_map.at(base.color);
    bool one_less = candidate.value == base.value - 1;
    return oppposing_render_color && one_less;
}

double StudentHeuristic::distanceLowerBound(const GameState &state) const {
    std::map<Card, int> home_top_cards = {};
    int free_cells = state.free_cells.size();
    double cards_out_of_home = king_value * colors_list.size()  ;

    for (const auto &home : state.homes) {
        auto opt_top = home.topCard();
        if (opt_top.has_value()) {
            cards_out_of_home -= opt_top->value;
            home_top_cards.insert(std::make_pair(*std::move(opt_top),0));
        }
    }

    int found_cards = 0;

    std::vector<Card> top_cards = topCards(state);
    for (auto stack: state.stacks) {
        int can_sit_on = 0;
        if (found_cards == 4) {
            break;
        }

        for (int i = 0; i <= 4 - free_cells; i++) {
            if (i == stack.storage().size()) {
                break;
            }
            if (found_cards == 4) {
                break;
            }
            Card top_card = stack.storage().at(i);
            try{
                Card card_on_top = stack.storage().at(i + 1);
                if (canSitOn( top_card, card_on_top))
                {
                    can_sit_on++;
                    cards_out_of_home -= can_sit_on;
                }
                else
                    can_sit_on = 0;
            }
            catch (std::out_of_range){}

            if (top_card.value != 1) {
                Card card_tmp = Card(top_card.color, top_card.value - 1);

                auto it = home_top_cards.find(card_tmp);
                if (it == home_top_cards.end())
                    continue;
            }

            cards_out_of_home += i;

            found_cards++;
        }
    }

    return cards_out_of_home;

}

template<typename Base, typename T>
inline bool instanceof(const T *ptr) {
    return dynamic_cast<const Base*>(ptr) != nullptr;
}

std::vector<SearchAction> AStarSearch::solve(const SearchState &init_state) {
    auto start = high_resolution_clock::now();
    bool isStudentHeuristic = instanceof<StudentHeuristic>(heuristic_.get());
    SearchState working_state(init_state);
    std::vector<Node> open;
    SearchState child = working_state;
    std::vector<SearchAction> solution = {};
    std::vector<SearchAction> solution2 = {};
    double f = 0;
    int depth = 0; // g
    Node node(f, depth, solution, std::make_shared<SearchState>(working_state));
    Node child_node(f, depth, solution, std::make_shared<SearchState>(working_state));
    std::map<SearchState, Node> visited;


    open.insert(open.begin(), node);

    while(!open.empty()) {
        if (!enough_memory(mem_limit_)) {
            return {};
        }
        if (isStudentHeuristic && duration_cast<microseconds>(high_resolution_clock::now() - start) > seconds(10)) {
            return {};
        }

        // sort vector
        std::sort(begin(open), end(open), [](auto const &t1, auto const &t2) {
            return t1.f < t2.f;
        });

        Node parent_node = open.front();
        SearchState parent = *parent_node.state;

        solution = parent_node.actions;

        open.erase(open.begin());

        // increment depth for children
        int child_depth = node.depth + 1;

        auto actions = parent.actions();
        for(auto & action : actions){

            child = action.execute(parent);

            if (child.isFinal()) {
                solution.push_back(action);
                return solution;
            }

            // compute g and h
            double child_heuristic = compute_heuristic(child, *heuristic_);
            // compute f = g + h
            double child_f = child_depth + child_heuristic;

            // if child in open list and open.f < child.f continue
            Node found_tuple = find_in_tuple_vector(open, child);
            if (found_tuple.f != -1 && found_tuple.f <= child_f) {
                continue;
            }

            try {
                // if child in visited and visited.f < child.f continue
                Node visited_node = visited.at(child);
                if(visited_node.f <= child_f)
                    continue;
            }catch (const std::out_of_range &e){
            }

            solution2 = solution;
            solution2.push_back(action);

            child_node.f = child_f;
            child_node.depth = child_depth;
            child_node.state = std::make_shared<SearchState>(child);
            child_node.actions = solution2;

            open.insert(open.end(), child_node);
        }

        // push q in visited or rewrite the already visited with better f
        try {
            Node visited_node = visited.at((*parent_node.state));
            if (visited_node.f >= parent_node.f)
                visited.at(parent) = parent_node;
        }catch (const std::out_of_range &e){
            visited.insert(std::make_pair((parent), parent_node));
        }
    }
    return {};
}