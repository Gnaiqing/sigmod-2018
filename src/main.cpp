#include <iostream>
#include <cstring>
#include <cstddef>
#include <unordered_set>
#include <limits>
#include <unordered_map>
#include <memory>
#include <sstream>
#include <algorithm>

#include "settings.h"
#include "database.h"
#include "executor.h"
#include "io.h"
#include "stats.h"
#include "timer.h"
#include "join/hash-joiner.h"

Database database;

int main(int argc, char** argv)
{
    std::ios::sync_with_stdio(false);

#ifdef LOAD_FROM_FILE
    freopen(LOAD_FROM_FILE, "r", stdin);
#else
    if (getenv("VTUNE") != nullptr)
    {
        freopen(INPUT_FILE, "r", stdin);
    }
#endif

#ifdef STATISTICS
    Timer loadTimer;
#endif
    loadDatabase(database);
#ifdef STATISTICS
    std::cerr << "Relation load time: " << loadTimer.get() << std::endl;
#endif

#ifndef REAL_RUN
    std::cout << "Ready" << std::endl;
#endif

#ifdef STATISTICS
    Timer queryLoadTimer;
    std::vector<Query> allQueries;
    std::unordered_map<std::string, uint32_t> cachedJoins;
    size_t joinsFilteredByMinMax = 0;
#endif

    Executor executor;
    std::string line;
    std::vector<Query> queries;
    while (std::getline(std::cin, line))
    {
        if (NOEXPECT(line[0] == 'F'))
        {
            auto queryCount = static_cast<int32_t>(queries.size());
            auto numThreads = std::min(QUERY_NUM_THREADS, queryCount);

#ifdef USE_THREADS
            #pragma omp parallel for num_threads(numThreads)
            for (int i = 0; i < queryCount; i++)
#else
            for (int i = 0; i < queryCount; i++)
#endif
            {
                executor.executeQuery(database, queries[i]);
            }
            for (auto& q: queries)
            {
                std::cout << q.result;
            }

#ifdef STATISTICS
            batchCount++;
            allQueries.insert(allQueries.end(), queries.begin(), queries.end());
#endif

            std::cout << std::flush;
            queries.clear();
        }
        else
        {
#ifdef STATISTICS
            queryLoadTimer.reset();
#endif
            queries.emplace_back();
            loadQuery(queries.back(), line);

#ifdef STATISTICS
            queryLoadTime += queryLoadTimer.get();

            auto& query = queries.back();
            queryCount++;
            joinCount += query.joins.size();
            filterCount += query.filters.size();

            for (auto& join : query.joins)
            {
                columnsPerJoin += join.size();
                if (join.size() > 1)
                {
                    multipleColumnsPerRelJoins++;
                }

                if (join[0].selections[0].column == 0 || join[0].selections[1].column == 0)
                {
                    joinsOnFirstColumn++;
                }

                bool cacheable = true;
                for (auto& predicate : join)
                {
                    for (auto& filter : query.filters)
                    {
                        if (filter.selection == predicate.selections[0] ||
                            filter.selection == predicate.selections[1])
                        {
                            cacheable = false;
                            break;
                        }
                    }

#ifdef USE_SORT_INDEX
                    auto& l = predicate.selections[0];
                    auto& r = predicate.selections[1];
                    auto li = database.getSortIndex(l.relation, l.column);
                    auto ri = database.getSortIndex(r.relation, r.column);

                    if (li->maxValue <= ri->minValue || ri->maxValue <= li->minValue)
                    {
                        joinsFilteredByMinMax++;
                    }
#endif
                }

                if (cacheable)
                {
                    cachedJoins[database.createJoinKey(join)]++;
                }
            }

            selfJoinCount += query.selfJoins.size();

            for (auto& filter: query.filters)
            {
                if (filter.selection.column == 0)
                {
                    filtersOnFirstColumn++;
                }
                if (filter.oper == '=')
                {
                    filterEqualsCount++;
                }
                if (filter.isSkippable())
                {
                    filtersSkippedByHistogram++;
                }
            }
#endif
        }
    }

#ifdef STATISTICS
    std::cerr << "Empty hash table count: " << emptyHashTableCount << std::endl;
    std::cerr << "Avg rows in hash: " << averageRowsInHash / (std::max(1UL, averageRowsInHashCount.load()))
              << std::endl;

    std::sort(allQueries.begin(), allQueries.end(), [](const Query& a, const Query& b) {
        return a.time > b.time;
    });

    for (int i = 0; i < std::min(static_cast<int32_t>(allQueries.size()), 5); i++)
    {
        std::cerr << allQueries[i].time << "ms, " << allQueries[i].input << ' ' << allQueries[i].plan << std::endl;
    }

    /*std::vector<std::pair<std::string, uint32_t>> cachedList;
    for (auto& kv: cachedJoins)
    {
        cachedList.emplace_back(kv.first, kv.second);
    }

    std::sort(cachedList.begin(), cachedList.end(), [](auto& a, auto& b) {
        return a.second > b.second;
    });
    for (auto& kv: cachedList)
    {
        std::cerr << kv.first << ' ' << kv.second << "x";

        auto key = kv.first;
        auto size = database.joinSizeMap.find(key);
        if (size != database.joinSizeMap.end())
        {
            std::cerr << " (" << size->second << ")";
        }
        std::cerr << std::endl;
    }*/

    /*size_t relationCount = database.relations.size();
    std::cerr << "Query load time: " << queryLoadTime << std::endl;
    std::cerr << "ColumnRelation count: " << relationCount << std::endl;
    std::cerr << "Min tuple count: " << minTuples << std::endl;
    std::cerr << "Max tuple count: " << maxTuples << std::endl;
    std::cerr << "Avg tuple count: " << tupleCount / (double) relationCount << std::endl;
    std::cerr << "Min column count: " << minColumns << std::endl;
    std::cerr << "Max column count: " << maxColumns << std::endl;
    std::cerr << "Avg column count: " << columnCount / (double) relationCount << std::endl;
    std::cerr << "Query count: " << queryCount << std::endl;
    std::cerr << "Join count: " << joinCount << std::endl;
    std::cerr << "Filter count: " << filterCount << std::endl;
    std::cerr << "Equals filter count: " << filterEqualsCount << std::endl;
    std::cerr << "Batch count: " << batchCount << std::endl;
    std::cerr << "Multiple-columns for joins: " << multipleColumnsPerRelJoins << std::endl;
    std::cerr << "Avg columns for join: " << columnsPerJoin / (double) joinCount << std::endl;
    std::cerr << "Sorted on first column: " << sortedOnFirstColumn << std::endl;
    std::cerr << "Joins on first column: " << joinsOnFirstColumn << std::endl;
    std::cerr << "Filters on first column: " << filtersOnFirstColumn << std::endl;
    std::cerr << "Self-join count: " << selfJoinCount << std::endl;
    std::cerr << std::endl;*/

    std::cerr << std::flush;
#endif

    std::quick_exit(0);
}
