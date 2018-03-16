#pragma once

#include <atomic>
#include "../util.h"

class ColumnRelation;

class Index
{
public:
    Index(ColumnRelation& relation, uint32_t column);
    DISABLE_COPY(Index);

    virtual ~Index() = default;

    virtual void build() = 0;

    std::atomic_flag buildStarted = ATOMIC_FLAG_INIT;
    std::atomic<bool> buildCompleted { false };

    ColumnRelation& relation;
    uint32_t column;
};