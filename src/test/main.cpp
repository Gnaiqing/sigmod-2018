#include <iostream>
#include <memory>
#include "../relation/column-relation.h"
#include "../io.h"
#include "../join/hash-joiner.h"
#include "../executor.h"
#include "../emit/filter-compiler.h"

static ColumnRelation createRelation(int tupleCount, int columnCount, int offset = 0)
{
    ColumnRelation relation{};
    relation.tupleCount = static_cast<uint64_t>(tupleCount);
    relation.columnCount = static_cast<uint32_t>(columnCount);
    relation.data = new uint64_t[relation.tupleCount * relation.columnCount];
    for (int i = 0; i < (int) (relation.tupleCount * relation.columnCount); i++)
    {
        relation.data[i] = static_cast<uint64_t>(i) + offset;
    }
    return relation;
}
static void setRelation(ColumnRelation& relation, const std::vector<uint64_t>& data)
{
    uint64_t cols = relation.columnCount;

    for (int i = 0; i < (int) data.size(); i++)
    {
        uint64_t row = i / cols;
        uint64_t col = i % cols;

        relation.getValueMutable(row, col) = data[i];
    }
}

Database database;

int main()
{
    std::vector<Filter> filters = {
        Filter(Selection(0, 0, 0), '>', nullptr, 13),
        Filter(Selection(0, 0, 0), '<', nullptr, 28)
    };

    FilterCompiler compiler;
    auto fn = compiler.compile(filters);
    std::cerr << fn(25600000000) << std::endl;
    std::cerr << fn(0) << std::endl;
    std::cerr << fn(13) << std::endl;
    std::cerr << fn(28) << std::endl;
    std::cerr << fn(14) << std::endl;

    Query query;
    std::string line = "0 1 2|0.1=1.0&1.1=2.0|0.2 1.1 2.0";
    //std::string line = "2 2|0.0=1.1|1.2";
    loadQuery(query, line);

    database.relations.push_back(createRelation(3, 3));
    database.relations.back().cumulativeColumnId = 0;
    database.relations.push_back(createRelation(3, 3));
    database.relations.back().cumulativeColumnId = 3;
    database.relations.push_back(createRelation(3, 3));
    database.relations.back().cumulativeColumnId = 6;

    setRelation(database.relations[0], {
            1, 2, 3,
            4, 2, 6,
            3, 4, 2
    });
    setRelation(database.relations[1], {
            2, 1, 0,
            4, 4, 2,
            3, 8, 4
    });
    setRelation(database.relations[2], {
            1, 2, 1,
            4, 4, 8,
            4, 8, 3
    });

    database.hashIndices.resize(9);
    database.sortIndices.resize(9);
    for (int i = 0; i < 3; i++)
    {
        for (int j = 0; j < 3; j++)
        {
            database.hashIndices[i * 3 + j] = std::make_unique<HashIndex>(database.relations[i], j);
            database.hashIndices[i * 3 + j]->build();
            database.sortIndices[i * 3 + j] = std::make_unique<SortIndex>(database.relations[i], j);
            database.sortIndices[i * 3 + j]->build();
        }
    }

    Executor executor;
    executor.executeQuery(database, query);
    std::cout << query.result << std::flush;

    return 0;
}
