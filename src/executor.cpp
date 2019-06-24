#include "executor.h"

#include <unordered_set>
#include <algorithm>
#include <iostream>

#include "relation/filter-iterator.h"
#include "join/hash-joiner.h"
#include "aggregation/aggregator.h"
#include "settings.h"
#include "join/nested-joiner.h"
#include "relation/hash-filter-iterator.h"
#include "relation/sort-index-iterator.h"
#include "relation/primary-index-iterator.h"
#include "join/self-join.h"
#include "timer.h"
#include "join/index-joiner.h"
#include "join/merge-sort-joiner.h"
#include "aggregation/aggregated-iterator.h"
#include "aggregation/indexed-aggregated-iterator.h"
#include "stats.h"

void Executor::buildPlan(Database& database, int split)
{
    bool aggregable;
    this->createViews(database, this->query, this->views, this->container, aggregable);
    auto root = this->createRootView(database, this->query, this->views, this->container, aggregable);
    this->prepareRoots(database, this->query, root, aggregable, split);
}

void Executor::createViews(Database& database, const Query& query, std::unordered_map<uint32_t, Iterator*>& views,
                           std::vector<std::unique_ptr<Iterator>>& container, bool& aggregable)
{
    std::unordered_map<uint32_t, std::vector<Filter>> filtersByBindings;

    // group filters by binding
    for (auto& filter: query.filters)
    {
        filtersByBindings[filter.selection.binding].push_back(filter);
    }

    // assign a filter iterator for filtered bindings
    for (auto& filterGroup: filtersByBindings)
    {
        std::sort(filterGroup.second.begin(), filterGroup.second.end());

#ifdef USE_HASH_INDEX
        int equalsIndex = -1;
        for (int i = 0; i < static_cast<int32_t>(filterGroup.second.size()); i++)
        {
            if (filterGroup.second[i].oper == '=')
            {
                equalsIndex = i;
                break;
            }
        }
#endif

        auto binding = filterGroup.first;
#ifdef USE_HASH_INDEX
        std::unique_ptr<FilterIterator> filter;
        if (equalsIndex != -1)
        {
            TODO: add check for created index
            filter = std::make_unique<HashFilterIterator>(relation,
                                                          binding,
                                                          filterGroup.second,
                                                          equalsIndex);
        }
        else filter = database.createFilteredIterator(filterGroup.second[0].selection, filterGroup.second);
#else
        auto filter = database.createFilteredIterator(filterGroup.second[0].selection, filterGroup.second);
#endif
        views.insert({ binding, filter.get() });
        container.push_back(std::move(filter));
    }

    // assign a simple relation iterator for bindings without a filter
    uint32_t binding = 0;
    for (auto& relation: query.relations)
    {
        auto it = views.find(binding);
        if (it == views.end())
        {
            container.push_back(std::make_unique<ColumnRelationIterator>(
                    &database.relations[relation],
                    binding
            ));
            views.insert({ binding, container.back().get() });
        }
        binding++;
    }

    if (query.isAggregable())
    {
        aggregable = true;
        this->createAggregatedViews(query, views, container);
    }
    else aggregable = false;

#ifdef USE_SELF_JOIN
    // assign self-joins
    for (auto& kv: query.selfJoins)
    {
        auto it = views.find(kv.first);
        container.push_back(std::make_unique<SelfJoin>(
                it->second,
                kv.second
        ));
        views[kv.first] = container.back().get();
    }
#endif
}

template <template<bool> typename T>
void createTemplatedJoin(Iterator* left,
                                Iterator* right,
                                uint32_t leftIndex,
                                Join* join,
                                std::vector<std::unique_ptr<Iterator>>& container)
{
    if (join->size() > 1)
    {
        container.push_back(std::make_unique<T<true>>(
                left,
                right,
                leftIndex,
                *join
        ));
    }
    else
    {
        container.push_back(std::make_unique<T<false>>(
                left,
                right,
                leftIndex,
                *join
        ));
    }
}

static void createHashJoin(Iterator* left,
                    Iterator* right,
                    uint32_t leftIndex,
                    std::vector<std::unique_ptr<Iterator>>& container,
                    Join* join,
                    bool last)
{
    if (last && database.hasIndexedIterator((*join)[0].selections[1 - leftIndex]))
    {
        container.push_back(right->createIndexedIterator(container, (*join)[0].selections[1 - leftIndex]));
        right = container.back().get();
    }
    else last = false;

    if (join->size() > 1)
    {
        container.push_back(std::make_unique<HashJoiner<true>>(
                left,
                right,
                leftIndex,
                *join,
                last
        ));
    }
    else
    {
        container.push_back(std::make_unique<HashJoiner<false>>(
                left,
                right,
                leftIndex,
                *join,
                last
        ));
    }
}
static void createIndexJoin(Iterator* left,
                    Iterator* right,
                    uint32_t leftIndex,
                    std::vector<std::unique_ptr<Iterator>>& container,
                    Join* join,
                    bool hasLeftIndex)
{
    if (hasLeftIndex && !left->isJoin())
    {
        container.push_back(left->createIndexedIterator(container, (*join)[0].selections[leftIndex]));
        left = container.back().get();
    }
    else hasLeftIndex = false;

    container.push_back(right->createIndexedIterator(container, (*join)[0].selections[1 - leftIndex]));
    right = container.back().get();

    if (join->size() > 1)
    {
        container.push_back(std::make_unique<IndexJoiner<true>>(
                left,
                right,
                leftIndex,
                *join,
                hasLeftIndex
        ));
    }
    else
    {
        container.push_back(std::make_unique<IndexJoiner<false>>(
                left,
                right,
                leftIndex,
                *join,
                hasLeftIndex
        ));
    }
}
static void createMergesortJoin(Iterator* left,
                                Iterator* right,
                                uint32_t leftIndex,
                                std::vector<std::unique_ptr<Iterator>>& container,
                                Join* join,
                                bool leftSorted)
{
    if (!left->isJoin() && !leftSorted)
    {
        container.push_back(left->createIndexedIterator(container, (*join)[0].selections[leftIndex]));
        left = container.back().get();
    }

    container.push_back(right->createIndexedIterator(container, (*join)[0].selections[1 - leftIndex]));

    createTemplatedJoin<MergeSortJoiner>(left, container.back().get(), leftIndex, join, container);
}

static void createJoin(Iterator* left,
                       Iterator* right,
                       uint32_t leftIndex,
                       std::vector<std::unique_ptr<Iterator>>& container,
                       Join* join,
                       const Query& query,
                       bool first,
                       bool last,
                       bool aggregable)
{
    int index = 0;
    for (; index < static_cast<int32_t>(join->size()); index++)
    {
        if (left->isSortedOn((*join)[index].selections[leftIndex]))
        {
            break;
        }
    }

    if (index < static_cast<int32_t>(join->size()))
    {
        std::swap((*join)[0], (*join)[index]);
    }

    bool hasLeftIndex = database.hasIndexedIterator((*join)[0].selections[leftIndex]);
    bool hasRightIndex = database.hasIndexedIterator((*join)[0].selections[1 - leftIndex]);
    bool leftSorted = left->isSortedOn((*join)[0].selections[leftIndex]);
    bool leftSortable = leftSorted || (hasLeftIndex && !left->isJoin());

    if (leftSortable && hasRightIndex && (first || leftSorted))
    {
        createMergesortJoin(left, right, leftIndex, container, join, leftSorted);
    }
    else
    {
        if (hasRightIndex)
        {
            createIndexJoin(left, right, leftIndex, container, join, hasLeftIndex);
        }
        else createHashJoin(left, right, leftIndex, container, join, last);
    }
}
static uint64_t getJoinRange(const JoinPredicate& predicate)
{
    auto left = predicate.selections[0];
    auto right = predicate.selections[1];

    auto leftMin = database.getMinValue(left.relation, left.column);
    auto leftMax = database.getMaxValue(left.relation, left.column);
    auto rightMin = database.getMinValue(right.relation, right.column);
    auto rightMax = database.getMaxValue(right.relation, right.column);

    auto start = std::max(leftMin, rightMin);
    auto end = std::min(leftMax, rightMax);

    if (start >= end) return 0;
    return end - start;
}

static uint32_t estimateJoinSize(Query& query, double * selectRate,
                                uint32_t * leftSize,uint32_t *rightSize,
                                uint32_t prevJoins, uint32_t prevSize,
                                uint32_t nextJoin)
{
    int joinNum = query.joins.size();
    auto left = query.joins[nextJoin][0].selections[0];
    auto right = query.joins[nextJoin][0].selections[1];
    auto leftBinding = left.binding;
    auto rightBinding = right.binding;
    bool usedLeftBinding  = false;
    bool usedRightBinding = false;
    for (int i = 0;i < joinNum; i++)
        if(((1<<i) & prevJoins) > 0)
        {
            auto binding1 = query.joins[i][0].selections[0].binding;
            auto binding2 = query.joins[i][0].selections[1].binding;
            if (binding1 == leftBinding || binding2 == leftBinding)
                usedLeftBinding = true;
            if (binding1 == rightBinding || binding2 == rightBinding)
                usedRightBinding = true;
        }
    double tmp = prevSize * selectRate[nextJoin];  
    if (!usedLeftBinding)
        tmp = tmp * leftSize[nextJoin];
    if (!usedRightBinding)
        tmp = tmp * rightSize[nextJoin];
    uint32_t estimateSize = (uint32_t)tmp;
    return estimateSize;
}
Iterator* Executor::createRootView(Database& database, Query& query,
                                   std::unordered_map<uint32_t, Iterator*>& views,
                                   std::vector<std::unique_ptr<Iterator>>& container,
                                   bool aggregable)
{
    if (query.joins.empty())
    {
        std::vector<uint32_t> bindings;
        query.fillBindings(bindings);
        if (bindings.size() > 1)
        {
#ifdef STATISTICS
            std::cerr << query.input << std::endl;
            query.dump(std::cerr);
#endif
            throw "EXC";
        }

        return views[bindings[0]];
    }

    std::sort(query.joins.begin(), query.joins.end(), [](const Join& a, const Join& b) {
        return a.size() > b.size();
    });

#ifdef SORT_JOINS_BY_SIZE
    std::sort(query.joins.begin(), query.joins.end(), [&database, &views](const Join& a, const Join& b) {
        return getJoinRange(a[0]) < getJoinRange(b[0]);

        /*auto& aLeft = views[a[0].selections[0].binding];
        auto& aRight = views[a[0].selections[1].binding];
        auto& bLeft = views[b[0].selections[0].binding];
        auto& bRight = views[b[0].selections[1].binding];
        return (aLeft->predictSize() * aRight->predictSize()) < (bLeft->predictSize() * bRight->predictSize());*/
    });
#endif

#ifdef SORT_JOINS_BY_DP
    int n = static_cast<int>(query.joins.size());
    int m = 1 << n;

    uint32_t * left_size = new uint32_t[n];
    uint32_t * right_size = new uint32_t[n];
    double * select_rate = new double[n];
    uint64_t * tot_cost = new uint64_t[m];
    uint32_t * mid_size = new uint32_t[m];
    int * select = new int[m];
    for (int i = 0;i < n;i++)
    {
        auto left = query.joins[i][0].selections[0];
        auto right = query.joins[i][0].selections[1];
        auto leftBinding = left.binding;
        auto rightBinding = right.binding;    
        auto& leftView = views[leftBinding];
        auto& rightView = views[rightBinding];
        left_size[i] = leftView->predictSize();
        right_size[i] = rightView->predictSize();
        int filteredLeftMin = 1e9;
        int filteredLeftMax = 0;
        int filteredRightMin = 1e9;
        int filteredRightMax = 0;
    #ifdef GET_ACCURATE_RANGE
        leftView->save();
        while (leftView->getNext())
        {
            int value = leftView->getValue(left);
            filteredLeftMin = std::min(filteredLeftMin,value);
            filteredLeftMax = std::max(filteredLeftMax,value);
        }            
        leftView->restore();
        rightView->save();
        while (rightView->getNext())
        {
            int value = rightView->getValue(right);
            filteredRightMin = std::min(filteredRightMin,value);
            filteredRightMax = std::max(filteredRightMax,value);
        }            
        rightView->restore();
    #else
        filteredLeftMin = database.getMinValue(left.relation,left.column);
        filteredLeftMax = database.getMaxValue(left.relation,left.column);
        filteredRightMin = database.getMinValue(right.relation,right.column);
        filteredRightMax = database.getMaxValue(right.relation,right.column);
    #endif   
        int start = std::max(filteredLeftMin,filteredRightMin);
        int end = std::min(filteredLeftMax,filteredRightMax);
        if (end < start)
            select_rate[i] = 0.0f;
        else
            select_rate[i] = (double)(end + 1 - start) / (filteredLeftMax + 1 - filteredLeftMin) / (filteredRightMax + 1 - filteredRightMin);

    #ifdef CHECK_SIZE
        /*
        std::cerr << i << ": " << std::endl;
        std::cerr << "left size:" << left_size[i] << std::endl;
        std::cerr << "right size:" << right_size[i] << std::endl;
        std::cerr << "left Range:" << filteredLeftMin << " - " << filteredLeftMax << std::endl;
        std::cerr << "right Range:" << filteredRightMin << " - " << filteredRightMax << std::endl;
        std::cerr << "select rate" << select_rate[i] << std::endl;
        */
    #endif
    }


    for (int i = 0;i < m;i++)

    {
        tot_cost[i] = 1e9;
        mid_size[i] = 1e9;
    }
    tot_cost[0] = 0;
    mid_size[0] = 1;
    for (int prevJoins = 0;prevJoins < m;prevJoins++)
        for (int nextJoin = 0;nextJoin < n;nextJoin++)
            if (((1 << nextJoin) & prevJoins) == 0)
            {
                int newJoins = prevJoins | (1 << nextJoin);
                uint32_t estimateSize = estimateJoinSize(query,select_rate,
                                                left_size,right_size,
                                                prevJoins,mid_size[prevJoins],
                                                nextJoin);
                if (estimateSize < mid_size[newJoins])
                      mid_size[newJoins] = estimateSize;
                if (estimateSize + tot_cost[prevJoins] < tot_cost[newJoins])
                {
                    tot_cost[newJoins] = estimateSize + tot_cost[prevJoins];
                    select[newJoins] = nextJoin;
                }
            }

#ifdef STATISTICS
    /*
    std::cerr << "result for DP:" << std::endl;
    for (int i = 0;i < m;i ++)
        std::cerr << i << " tot_cost:" <<  tot_cost[i] << " mid_size:" << mid_size[i] << std::endl;
        */
#endif

    auto tmpJoins = query.joins;
    m = (1 << n) - 1;
    std::cerr << "join order: ";
    for (int i = n-1;i >= 0;i--)
    {
        int curJoin = select[m];
        std::cerr<< curJoin << " "; 
        query.joins[i] = tmpJoins[curJoin];
        m = m - (1 << curJoin);
    }
    std::cerr << std::endl;
    delete[] select_rate;
    delete[] left_size;
    delete[] right_size;
    delete[] tot_cost;
    delete[] mid_size;
    delete[] select;        
#endif

#ifdef CHECK_SIZE
    /*
    for (int i = 0;i < static_cast<int32_t>(query.joins.size());i++)
    {
        auto* join = &query.joins[i];
        auto left = (*join)[0].selections[0];
        auto right = (*join)[0].selections[1];
        auto& leftView = views[left.binding];
        auto& rightView = views[right.binding];

        leftView->save();
        uint32_t filteredLeftMin = 1e9;
        uint32_t filteredLeftMax = 0;
        while (leftView->getNext())
        {
            uint32_t value = leftView->getValue(left);
            filteredLeftMin = std::min(filteredLeftMin,value);
            filteredLeftMax = std::max(filteredLeftMax,value);
        }            
        leftView->restore();
        
        rightView->save();
        uint32_t filteredRightMin = 1e9;
        uint32_t filteredRightMax = 0;
        while (rightView->getNext())
        {
            uint32_t value = rightView->getValue(right);
            filteredRightMin = std::min(filteredRightMin,value);
            filteredRightMax = std::max(filteredRightMax,value);
        }            
        rightView->restore();

        auto leftMin = database.getMinValue(left.relation,left.column);
        auto leftMax = database.getMaxValue(left.relation,left.column);
        auto rightMin = database.getMinValue(right.relation,right.column);
        auto rightMax = database.getMaxValue(right.relation,right.column);
        std::cerr << "left(binding,relation,column) : " <<left.binding << " " << left.relation << " " << left.column << std::endl;
        std::cerr << "left predict size: " << leftView->predictSize() << std::endl;
        std::cerr << "left range: "<< leftMin << " - " << leftMax << std::endl;        
        std::cerr << "filtered left range: "<< filteredLeftMin << " - " << filteredLeftMax << std::endl;
        std::cerr << "right(binding,relation,column) : " << right.binding << " " << right.relation << " " << right.column << std::endl;
        std::cerr << "right predict size: " << rightView->predictSize() << std::endl;
        std::cerr << "right range: "<< rightMin << " - " << rightMax << std::endl;
        std::cerr << "filtered right range: "<< filteredRightMin << " - " << filteredRightMax << std::endl;
    }
    */
#endif

    auto* join = &query.joins[0];

    auto leftBinding = (*join)[0].selections[0].binding;
    auto rightBinding = (*join)[0].selections[1].binding;

    createJoin(views[leftBinding], views[rightBinding], 0, container, join,
               query, true, query.joins.size() == 1, aggregable);

    std::unordered_set<uint32_t> usedBindings = { leftBinding, rightBinding };
    Iterator* root = container.back().get();
    for (int i = 1; i < static_cast<int32_t>(query.joins.size()); i++)
    {
        join = &query.joins[i];
        leftBinding = (*join)[0].selections[0].binding;
        rightBinding = (*join)[0].selections[1].binding;

        auto usedLeft = usedBindings.find(leftBinding) != usedBindings.end();
        auto usedRight = usedBindings.find(rightBinding) != usedBindings.end();
        Iterator* left = root;
        Iterator* right;
        uint32_t leftIndex = 0;

        if (usedLeft)
        {
            right = views[rightBinding];
            usedBindings.insert(rightBinding);
        }
        else if (usedRight)
        {
            right = views[leftBinding];
            usedBindings.insert(leftBinding);
            leftIndex = 1;
        }
        else
        {
            query.joins.push_back(*join);
            continue;
        }

        createJoin(left, right, leftIndex, container, join, query,
                   false, i == (static_cast<int32_t>(query.joins.size()) - 1), aggregable);
        root = container.back().get();
    }

    if (aggregable)
    {
        container.push_back(std::make_unique<Aggregator>(root, query));
        root = container.back().get();
    }

    return root;
}

template <template<bool> typename T, bool GROUPBY_SUM>
static void createTemplatedAggregate(const Selection& groupBy,
                                     const std::vector<Selection>& sumSelections,
                                     std::vector<std::unique_ptr<Iterator>>& container)
{
    container.push_back(std::make_unique<T<GROUPBY_SUM>>(container.back().get(), groupBy, sumSelections));
}
void Executor::createAggregatedViews(const Query& query, std::unordered_map<uint32_t, Iterator*>& views,
                                     std::vector<std::unique_ptr<Iterator>>& container)
{
    for (auto& kv: views)
    {
        Selection groupBy{};
        for (auto& join: query.joins)
        {
            for (auto selection : join[0].selections)
            {
                if (selection.binding == kv.first)
                {
                    groupBy = selection;
                    break;
                }
            }
        }

        bool joinSummed = false;
        std::vector<Selection> sumSelections;
        for (auto& sel: query.selections)
        {
            if (sel.binding == kv.first)
            {
                sumSelections.push_back(sel);
            }
            if (sel == groupBy) joinSummed = true;
        }

        container.push_back(kv.second->createIndexedIterator(container, groupBy));

#ifdef USE_AGGREGATE_INDEX
        bool canUseIndex = true;
        for (auto& filter: query.filters)
        {
            if (filter.selection.binding == kv.first)
            {
                canUseIndex = false;
                break;
            }
        }


        if (canUseIndex)
        {
            if (joinSummed)
            {
                createTemplatedAggregate<IndexedAggregatedIterator, true>(groupBy, sumSelections, container);
            }
            else createTemplatedAggregate<IndexedAggregatedIterator, false>(groupBy, sumSelections, container);
        }
        else
#endif
        {
            if (joinSummed)
            {
                createTemplatedAggregate<AggregatedIterator, true>(groupBy, sumSelections, container);
            }
            else createTemplatedAggregate<AggregatedIterator, false>(groupBy, sumSelections, container);
        }
        kv.second = container.back().get();
    }
}

void Executor::prepareRoots(Database& database, Query& query, Iterator* root, bool aggregable, int split)
{
    for (auto& sel: query.selections)
    {
        this->selectionMap[sel.getId()] = sel;
    }

    if (aggregable)
    {
        auto map = selectionMap;
        std::vector<uint32_t> bindings;
        root->fillBindings(bindings);

        for (auto binding: bindings)
        {
            Selection sel = Selection::aggregatedCount(binding);
            map[sel.getId()] = sel;
        }

        root->requireSelections(map);
    }
    else root->requireSelections(this->selectionMap);

    std::vector<Iterator*> groups;

#ifdef STATISTICS
    this->query.predicted = static_cast<uint64_t>(root->predictSize());
#endif

    if (root->isImpossible())
    {
        this->query.fillImpossible();
#ifdef STATISTICS
        plansSkipped++;
#endif
    }
    else
    {
        root->split(this->container, groups, static_cast<size_t>(split));
        for (int i = 0; i < static_cast<int32_t>(groups.size()); i++)
        {
            auto iter = std::make_unique<MultiWrapperIterator>(groups, i);
            this->roots.push_back(iter.get());
            this->container.push_back(std::move(iter));
        }
    }

    if (!this->roots.empty())
    {
        root = this->roots.back();
    }

    root->requireSelections(this->selectionMap);

    for (auto& sel: this->selectionMap)
    {
        this->backMap[sel.second.getId()] = static_cast<unsigned int>(columnIds.size());
        this->columnIds.push_back(root->getColumnForSelection(sel.second));
        this->selections.push_back(sel.second);
    }

    for (auto& root: this->roots)
    {
        root->setSelections(this->columnIds, this->selections);
    }
}

void Executor::finalizeQuery()
{
    size_t count = 0;
    std::vector<uint64_t> results(static_cast<size_t>(this->selectionMap.size()));

    if (!this->roots.empty())
    {
        for (auto& iter: this->roots)
        {
            size_t localCount = 0;
            iter->sumRows(results, this->columnIds, this->selections, localCount);
            count += localCount;
        }

#ifdef STATISTICS
        std::stringstream planStream;
        this->roots[0]->dumpPlan(planStream);
        this->query.plan = planStream.str();

        double time = 0;
        for (auto& root: this->roots)
        {
            time += ((MultiWrapperIterator*)root)->time;
        }

        this->query.time = time / this->roots.size();
#endif

#ifdef COLLECT_JOIN_SIZE
        this->roots[0]->assignJoinSize(database);
#endif
    }

    std::stringstream ss;
    for (auto& sel: this->query.selections)
    {
        if (count == 0)
        {
            ss << "NULL ";
        }
        else
        {
            uint64_t result = results[this->backMap[sel.getId()]];
            ss << std::to_string(result) << ' ';
        }
    }

    this->query.result = ss.str();
    this->query.result[this->query.result.size() - 1] = '\n';
}
