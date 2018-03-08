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
    Database database;
    loadDatabase(database);
#ifdef STATISTICS
    std::cerr << "Relation load time: " << loadTimer.get() << std::endl;
#endif

#ifndef REAL_RUN
    std::cout << "Ready" << std::endl;
#endif

#ifdef STATISTICS
    Timer queryLoadTimer;
#endif

    Executor executor;
    std::string line;
    std::vector<Query> queries;
    while (std::getline(std::cin, line))
    {
        if (line[0] == 'F')
        {
            auto queryCount = static_cast<int32_t>(queries.size());
            auto numThreads = std::min(QUERY_NUM_THREADS, queryCount);

            #pragma omp parallel for num_threads(numThreads)
            for (int i = 0; i < queryCount; i++)
            {
                executor.executeQuery(database, queries[i]);
            }
            for (int i = 0; i < queryCount; i++)
            {
                std::cout << queries[i].result;
            }

#ifdef STATISTICS
            for (auto& q: queries)
            {
                queryRowsMax = std::max(queryRowsMax, q.count);
                queryRowsCount += q.count;
            }
            batchCount++;
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

            std::unordered_set<std::string> pairs;
            std::unordered_set<int> joinedRelations;
            size_t multipleColumns = 1;

            for (auto& join : query.joins)
            {
                auto smaller = std::min(join[0].selections[0].relation, join[0].selections[1].relation);
                auto larger = std::max(join[0].selections[0].relation, join[0].selections[1].relation);
                auto key = std::to_string(smaller) + "." + std::to_string(larger);
                if (pairs.find(key) != pairs.end())
                {
                    multipleColumns++;
                }
                pairs.insert(key);

                joinedRelations.insert(smaller);
                joinedRelations.insert(larger);

                if (join[0].selections[0].column == 0 || join[0].selections[1].column == 0)
                {
                    joinsOnFirstColumn++;
                }
            }

            for (auto& filter: query.filters)
            {
                if (filter.selection.column == 0)
                {
                    filtersOnFirstColumn++;
                }
            }

            columnsPerJoin += multipleColumns;
            if (multipleColumns > 1)
            {
                multipleColumnsPerRelJoins++;
            }
#endif
        }
    }

#ifdef STATISTICS
    size_t relationCount = database.relations.size();
    std::cerr << "Query load time: " << queryLoadTime << std::endl;
    std::cerr << "ColumnRelation count: " << relationCount << std::endl;
    std::cerr << "Min tuple count: " << minTuples << std::endl;
    std::cerr << "Max tuple count: " << maxTuples << std::endl;
    std::cerr << "Avg tuple count: " << tupleCount / (double) relationCount << std::endl;
    std::cerr << "Min column count: " << minColumns << std::endl;
    std::cerr << "Max column count: " << maxColumns << std::endl;
    std::cerr << "Avg column count: " << columnCount / (double) relationCount << std::endl;
    std::cerr << "Query count: " << queryCount << std::endl;
    std::cerr << "Max result rows: " << queryRowsMax << std::endl;
    std::cerr << "Avg result rows: " << (size_t) (queryRowsCount / (double) queryCount) << std::endl;
    std::cerr << "Join count: " << joinCount << std::endl;
    std::cerr << "Filter count: " << filterCount << std::endl;
    std::cerr << "Batch count: " << batchCount << std::endl;
    std::cerr << "Multiple-columns for joins: " << multipleColumnsPerRelJoins << std::endl;
    std::cerr << "Avg columns for join: " << columnsPerJoin / (double) queryCount << std::endl;
    std::cerr << "Sorted on first column: " << sortedOnFirstColumn << std::endl;
    std::cerr << "Joins on first column: " << joinsOnFirstColumn << std::endl;
    std::cerr << "Filters on first column: " << filtersOnFirstColumn << std::endl;
    std::cerr << std::endl;
#endif

    std::quick_exit(0);
}
