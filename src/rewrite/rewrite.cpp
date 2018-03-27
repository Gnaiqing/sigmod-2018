#include "rewrite.h"
#include "../database.h"
#include "../stats.h"

#include <algorithm>
#include <unordered_set>

static std::vector<Filter> getFilters(const std::vector<Filter>& filters, const Selection& selection)
{
    std::vector<Filter> selected;
    for (auto& f: filters)
    {
        if (f.selection == selection) selected.push_back(f);
    }
    return selected;
}
static bool containsFilter(const std::vector<Filter>& filters, const Filter& filter)
{
    return std::find_if(filters.begin(), filters.end(), [&filter](const Filter& f) {
        return f == filter;
    }) != filters.end();
}

static bool hasOtherColumn(const Query& query, Selection selection,
                           const std::unordered_set<SelectionId>& skippable)
{
    for (auto& join: query.joins)
    {
        for (auto& pred: join)
        {
            for (auto& sel: pred.selections)
            {
                if (sel.binding == selection.binding && sel.column != selection.column
                    && skippable.find(sel.getId()) == skippable.end())
                {
                    return true;
                }
            }
        }
    }

    for (auto& filter: query.filters)
    {
        auto& sel = filter.selection;
        if (sel.binding == selection.binding && sel.column != selection.column
            && skippable.find(sel.getId()) == skippable.end()) return true;
    }

    for (auto& sel: query.selections)
    {
        if (sel.binding == selection.binding && sel.column != selection.column)
        {
            if (skippable.find(sel.getId()) == skippable.end())
            {
                return true;
            }
        }
    }

    return false;
}
static bool hasOtherColumnNonUnique(const Query& query, Selection selection)
{
    for (auto& join: query.joins)
    {
        for (auto& pred: join)
        {
            for (auto& sel: pred.selections)
            {
                if (sel.binding == selection.binding && sel.column != selection.column
                    && !sel.isUnique())
                {
                    return true;
                }
            }
        }
    }

    for (auto& filter: query.filters)
    {
        auto& sel = filter.selection;
        if (sel.binding == selection.binding && sel.column != selection.column && !sel.isUnique()) return true;
    }

    for (auto& sel: query.selections)
    {
        if (sel.binding == selection.binding && sel.column != selection.column && !sel.isUnique())
        {
            return true;
        }
    }

    return false;
}
static void rewriteSelection(Query& query, Selection before, Selection after)
{
    for (auto& join: query.joins)
    {
        for (auto& pred: join)
        {
            for (auto& sel: pred.selections)
            {
                if (sel == before) sel = after;
            }
        }
    }

    for (auto& filter: query.filters)
    {
        auto& sel = filter.selection;
        if (sel == before) sel = after;
    }

    for (auto& sel: query.selections)
    {
        if (sel == before) sel = after;
    }
}

static void rewriteFks(Query& query)
{
    std::unordered_set<SelectionId> skippableSelections;

    // remove PK-FK joins
    for (int j = 0; j < static_cast<int32_t>(query.joins.size()); j++)
    {
        auto& join = query.joins[j];
        if (join.size() == 1)
        {
            for (int s = 0; s < 2; s++)
            {
                if (join[0].selections[s].isUnique() && !hasOtherColumnNonUnique(query, join[0].selections[s]))
                {
                    if (database.isPkFk(join[0].selections[s], join[0].selections[1 - s]))
                    {
                        skippableSelections.insert(join[0].selections[s].getId());
                    }
                }
            }
        }
    }

    for (int j = 0; j < static_cast<int32_t>(query.joins.size()); j++)
    {
        auto& join = query.joins[j];
        if (join.size() == 1)
        {
            for (int s = 0; s < 2; s++)
            {
                if (join[0].selections[s].isUnique())
                {
                    if (skippableSelections.find(join[0].selections[s].getId()) != skippableSelections.end() &&
                        !hasOtherColumn(query, join[0].selections[s], skippableSelections))
                    {
                        skippableFK++;

                        rewriteSelection(query, join[0].selections[s], join[0].selections[1 - s]);
                        query.joins.erase(query.joins.begin() + j);
                        j--;
                        break;
                    }
                }
            }
        }
    }

    // TODO: join joins with same bindings into one
}

void rewriteQuery(Query& query)
{
#ifdef REWRITE_FKS
    rewriteFks(query);
#endif

    std::unordered_map<uint32_t, std::unique_ptr<UnionFind>> components;
    for (auto& join: query.joins)
    {
        for (auto& pred: join)
        {
            auto left = components.find(pred.selections[0].getId());
            if (left == components.end())
            {
                left = components.insert(std::make_pair(pred.selections[0].getId(),
                                                        std::make_unique<UnionFind>(pred.selections[0]))).first;
            }
            auto right = components.find(pred.selections[1].getId());
            if (right == components.end())
            {
                right = components.insert(std::make_pair(pred.selections[1].getId(),
                                                         std::make_unique<UnionFind>(pred.selections[1]))).first;
            }

            left->second->join(right->second.get());
        }
    }


    std::unordered_map<UnionFind*, std::vector<Selection>> groups; // components of join graph
    for (auto& kv: components)
    {
        auto parent = kv.second->findParent();
        auto it = groups.find(parent);
        if (it == groups.end())
        {
            it = groups.insert({ parent, {} }).first;
        }
        it->second.push_back(kv.second->selection);
    }

    // iterate every component
    for (auto& kv: groups)
    {
        std::unordered_map<uint32_t, std::vector<Selection>> byBinding;
        for (auto& sel: kv.second)
        {
            auto it = byBinding.find(sel.binding);
            if (it == byBinding.end())
            {
                it = byBinding.insert({ sel.binding, {} }).first;
            }
            it->second.push_back(sel);
        }

        for (auto& bind: byBinding)
        {
            if (bind.second.size() > 1)
            {
                for (auto& s: bind.second)
                {
                    auto& v = query.selfJoins[bind.first];
                    if (std::find(v.begin(), v.end(), s) == v.end())
                    {
                        v.push_back(s);
                    }
                }
            }
        }

#ifdef EXPAND_FILTERS
        std::vector<Filter> componentFilters;
        for (auto& sel: kv.second)
        {
            auto filters = getFilters(query.filters, sel);
            for (auto& f: filters)
            {
                if (!containsFilter(componentFilters, f))
                {
                    componentFilters.push_back(f);
                }
            }
        }

        if (componentFilters.empty()) continue;

        bool impossible = false;
        std::unordered_set<uint64_t> equals;

        uint64_t minValue = 0;
        uint64_t maxValue = std::numeric_limits<uint64_t>::max();

        for (auto& f: componentFilters)
        {
            if (f.oper == '=')
            {
                equals.insert(f.value);
                minValue = f.value;
                maxValue = f.value;
                if (equals.size() > 1)
                {
                    impossible = true;
                    break;
                }
            }
            else if (f.oper == '<')
            {
                maxValue = std::min(f.value, maxValue);
            }
            else minValue = std::max(f.value, minValue);
        }

        if (minValue == maxValue)
        {
            componentFilters = {
                    Filter(Selection(0, 0, 0), minValue, nullptr, '=')
            };
        }
        else if (minValue > 0 && maxValue < std::numeric_limits<uint64_t>::max())
        {
            componentFilters = {
                    Filter(Selection(0, 0, 0), minValue, nullptr, '>'),
                    Filter(Selection(0, 0, 0), maxValue, nullptr, '<')
            };
        }

        query.impossible = impossible;

        for (auto& sel: kv.second)
        {
            for (auto& filter: componentFilters)
            {
                auto assigned = filter;
                assigned.selection = sel;
                if (!containsFilter(query.filters, assigned))
                {
                    query.filters.push_back(assigned);
                }
            }
        }
#endif
    }

    // rewrite sum selections
    std::vector<Selection> usedSelections;
    for (int i = 0; i < static_cast<int32_t>(query.selections.size()); i++)
    {
        auto& sel = query.selections[i];
        for (auto& used: usedSelections)
        {
            auto usedIt = components.find(used.getId());
            auto selIt = components.find(sel.getId());
            if (usedIt != components.end() && selIt != components.end())
            {
                if (usedIt->second->findParent() == selIt->second->findParent())
                {
                    query.selections[i] = used;
                    break;
                }
            }
        }
        usedSelections.push_back(query.selections[i]);
    }
}